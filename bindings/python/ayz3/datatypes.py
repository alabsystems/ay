# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# z3py-shaped algebraic datatypes (B-6): Datatype / EnumSort / TupleSort.
#
# z3py term programs use algebraic datatypes heavily (enumerations, tuples,
# records, recursive lists/trees). This module wires z3py's datatype surface
# onto AY's Z3-shaped C API (Z3_mk_constructor / Z3_mk_datatype /
# Z3_query_constructor / Z3_del_constructor), which routes each
# constructor / recognizer / accessor application through AY's verified
# datatype theory (the same terms `declare-datatypes` elaborates to).
#
#   # Enumeration
#   Color, (red, green, blue) = EnumSort('Color', ['red', 'green', 'blue'])
#
#   # Tuple / record
#   Pair, mk_pair, (first, second) = TupleSort('Pair', [IntSort(), IntSort()])
#
#   # General (possibly self-recursive) datatype
#   List = Datatype('List')
#   List.declare('cons', ('car', IntSort()), ('cdr', List))
#   List.declare('nil')
#   List = List.create()
#   # -> List.cons, List.nil (constructors), List.car, List.cdr (accessors),
#   #    List.is_cons, List.is_nil (recognizers)
#
# SOUNDNESS / HONESTY
# -------------------
# Every constructor/recognizer/accessor is a REAL datatype op in AY's theory;
# nothing here fabricates a value. Model values are read back through
# `Z3_model_get_const_interp` (the constructor term, e.g. `blue` / `(mk-pair 3
# 5)`), and datatype field values through AST introspection on that concrete
# value (`m[p].arg(0)`), both of which reflect AY's actual model.
#
# MUTUAL RECURSION: AY's C ABI does not yet support mutually recursive datatypes
# (`Z3_mk_datatypes` with cross-datatype sort references). `CreateDatatypes` for
# more than one datatype that reference each other raises an honest
# NotImplementedError rather than mis-encoding the reference.

import ctypes

from . import _lib

lib = _lib.lib

# Filled in by install(mod): references to the package internals we build on.
_M = None
# A FuncDeclRef subclass (built in install(), once the package's FuncDeclRef
# exists) whose nullary applications register themselves as named datatype
# constants so they survive cross-context rebuild.
_ConstructorFuncDecl = None


# A sentinel marking a constructor field whose sort is the datatype under
# construction (a self-reference, e.g. `List.cdr : List`).
class _SelfRef:
    __slots__ = ("builder",)

    def __init__(self, builder):
        self.builder = builder


# ---------------------------------------------------------------------------
# Declaration recipes (context-independent), so a datatype can be re-declared
# in any context (needed for ayz3's per-Solver context model / cross-context
# rebuild). A recipe records exactly what is needed to replay the declaration.
# ---------------------------------------------------------------------------

class _CtorRecipe:
    __slots__ = ("name", "recognizer", "fields")

    def __init__(self, name, recognizer, fields):
        self.name = name
        # fields: list of (field_name, field_sort) where field_sort is a
        # SortRef, or the string "self" for a self-reference.
        self.fields = fields
        self.recognizer = recognizer


class _DatatypeRecipe:
    __slots__ = ("name", "ctors")

    def __init__(self, name, ctors):
        self.name = name
        self.ctors = ctors


def _mk_sym(ctx, name):
    return lib.Z3_mk_string_symbol(ctx.ref, name.encode())


def _declare_in_ctx(recipe, ctx):
    """Build (or reuse) the datatype described by `recipe` in `ctx`.

    Idempotent: a datatype already declared in `ctx` (by name) is returned from
    the context's registry so the constructor/accessor/recognizer func_decls are
    shared and hash-consed applications line up.
    """
    existing = ctx._datatype_sorts.get(recipe.name)
    if existing is not None:
        return existing

    SortRef = _M.SortRef
    FuncDeclRef = _M.FuncDeclRef

    # Reject a field that references another datatype BUILDER that has not been
    # created yet (only meaningful for mutual recursion, which AY does not
    # support) — a clear error rather than an opaque failure deep in ctypes.
    for cr in recipe.ctors:
        for _fn, fs in cr.fields:
            if fs != "self" and isinstance(fs, Datatype):
                raise NotImplementedError(
                    f"datatype field {_fn!r} of constructor {cr.name!r} references "
                    f"the un-created datatype {fs.name!r}; AY does not support "
                    "mutually recursive datatypes. Reference an already-created "
                    "DatatypeSortRef, or use a single self-recursive datatype."
                )

    c_handles = []
    # Keep ctypes field-name/sort/ref arrays alive until after Z3_mk_datatype.
    keepalive = []
    for cr in recipe.ctors:
        nf = len(cr.fields)
        if nf:
            fname_arr = (_lib.Z3_symbol * nf)(
                *[_mk_sym(ctx, fn) for fn, _ in cr.fields]
            )
            sorts_arr = (_lib.Z3_sort * nf)()
            refs_arr = (ctypes.c_uint * nf)()
            for k, (_fn, fs) in enumerate(cr.fields):
                if fs == "self":
                    # Null sort + ref index 0 => the datatype under construction.
                    sorts_arr[k] = None
                    refs_arr[k] = 0
                else:
                    dsort = fs if fs.ctx is ctx else _rebuild_field_sort(fs, ctx)
                    sorts_arr[k] = dsort.handle
                    refs_arr[k] = 0
            keepalive.extend([fname_arr, sorts_arr, refs_arr])
            ch = lib.Z3_mk_constructor(
                ctx.ref, _mk_sym(ctx, cr.name), _mk_sym(ctx, cr.recognizer),
                nf, fname_arr, sorts_arr, refs_arr,
            )
        else:
            ch = lib.Z3_mk_constructor(
                ctx.ref, _mk_sym(ctx, cr.name), _mk_sym(ctx, cr.recognizer),
                0, None, None, None,
            )
        if not ch:
            raise _M.AyZ3Exception(
                f"Z3_mk_constructor returned null for {cr.name!r}"
            )
        c_handles.append(ch)

    arr = (_lib.Z3_constructor * len(c_handles))(*c_handles)
    dt_handle = lib.Z3_mk_datatype(
        ctx.ref, _mk_sym(ctx, recipe.name), len(c_handles), arr
    )
    if not dt_handle:
        ctx.check_error("Z3_mk_datatype")
        raise _M.AyZ3Exception(
            f"Z3_mk_datatype returned null for datatype {recipe.name!r} "
            "(mutually recursive datatypes are not supported)"
        )

    dsortref = DatatypeSortRef(dt_handle, ctx, recipe)
    # Register BEFORE querying so a self-referential field's datatype sort is
    # resolvable and re-entrant declaration is a no-op.
    ctx._datatype_sorts[recipe.name] = dsortref

    for i, (ch, cr) in enumerate(zip(c_handles, recipe.ctors)):
        nf = len(cr.fields)
        cdecl = _lib.Z3_func_decl()
        tdecl = _lib.Z3_func_decl()
        accs = (_lib.Z3_func_decl * nf)() if nf else None
        lib.Z3_query_constructor(
            ctx.ref, ch, nf, ctypes.byref(cdecl), ctypes.byref(tdecl), accs
        )

        # Constructor domain = field sorts (self-ref -> the datatype sort).
        domain = []
        for _fn, fs in cr.fields:
            domain.append(dsortref if fs == "self"
                          else (fs if fs.ctx is ctx else _rebuild_field_sort(fs, ctx)))
        ctor_fd = _ConstructorFuncDecl(cdecl, cr.name, domain, dsortref, ctx)
        recog_fd = FuncDeclRef(tdecl, cr.recognizer, [dsortref],
                               _M._bool_sort(ctx), ctx)
        accessor_fds = []
        for j, (fn, fs) in enumerate(cr.fields):
            fsort = dsortref if fs == "self" else (
                fs if fs.ctx is ctx else _rebuild_field_sort(fs, ctx))
            accessor_fds.append(FuncDeclRef(accs[j], fn, [dsortref], fsort, ctx))

        entry = _CtorRefs(cr.name, cr.recognizer, ctor_fd, recog_fd, accessor_fds,
                          [fn for fn, _ in cr.fields])
        dsortref._constructors.append(entry)

        # Register the datatype ops by the decl name AY reports for a built
        # application, so a cross-context rebuild can re-route them (constructor,
        # recognizer, each accessor). See _rebuild_datatype_app.
        ctx._datatype_ops[cr.name] = ("ctor", recipe.name, i)
        ctx._datatype_ops[cr.recognizer] = ("recog", recipe.name, i)
        for j, (fn, _fs) in enumerate(cr.fields):
            ctx._datatype_ops[fn] = ("accessor", recipe.name, i, j)

        # The constructor descriptor is consumed once; free it (its func_decls
        # live in the context arena and stay valid).
        lib.Z3_del_constructor(ctx.ref, ch)

    keepalive.append(arr)
    return dsortref


def _rebuild_field_sort(sort, ctx):
    """Rebuild a field SortRef in `ctx` (primitive sorts, or another datatype)."""
    if isinstance(sort, DatatypeSortRef):
        return _declare_in_ctx(sort.recipe, ctx)
    return _M._rebuild_sort_in_ctx(sort, ctx)


class _CtorRefs:
    """Bundle of a single constructor's func_decls in one context."""

    __slots__ = ("name", "recognizer", "ctor_decl", "recog_decl",
                 "accessor_decls", "field_names")

    def __init__(self, name, recognizer, ctor_decl, recog_decl,
                 accessor_decls, field_names):
        self.name = name
        self.recognizer = recognizer
        self.ctor_decl = ctor_decl
        self.recog_decl = recog_decl
        self.accessor_decls = accessor_decls
        self.field_names = field_names


# ---------------------------------------------------------------------------
# Public sort / expression wrappers
# ---------------------------------------------------------------------------

class DatatypeSortRef:
    """An algebraic-datatype sort (z3py DatatypeSortRef).

    Exposes z3py's `num_constructors()/constructor(i)/recognizer(i)/
    accessor(i,j)` and, after creation, attribute access for each constructor
    (`List.cons`), recognizer (`List.is_cons`) and accessor (`List.car`).
    """

    kind = "Datatype"

    def __init__(self, handle, ctx, recipe):
        self.handle = handle
        self.ctx = ctx
        self.recipe = recipe
        self.bv_size = 0
        self.domain_sort = None
        self.range_sort = None
        self._constructors = []  # list[_CtorRefs]

    def name(self):
        return self.recipe.name

    def num_constructors(self):
        return len(self._constructors)

    def constructor(self, i):
        return self._constructors[i].ctor_decl

    def recognizer(self, i):
        return self._constructors[i].recog_decl

    def accessor(self, i, j):
        return self._constructors[i].accessor_decls[j]

    def __repr__(self):
        return self.recipe.name

    def __eq__(self, other):
        return (isinstance(other, DatatypeSortRef)
                and other.ctx is self.ctx
                and other.recipe.name == self.recipe.name)

    def __hash__(self):
        return hash((id(self.ctx), self.recipe.name))

    def _attach_attrs(self):
        """z3py convenience: expose ctor/recognizer/accessor decls as attributes.

        Matches z3py's `Datatype.create()`: a NULLARY constructor is exposed as
        its already-applied constant value (a DatatypeRef, so `List.nil` is a
        term), an n-ary constructor as its FuncDeclRef (`List.cons`); recognizers
        as `is_<ctor>` and accessors by field name.
        """
        for c in self._constructors:
            if c.ctor_decl.arity() == 0:
                setattr(self, c.name, c.ctor_decl())
            else:
                setattr(self, c.name, c.ctor_decl)
            setattr(self, "is_" + c.name, c.recog_decl)
            for fname, acc in zip(c.field_names, c.accessor_decls):
                setattr(self, fname, acc)


def _register_datatype_sortref(ds):
    """Also register the sort under the module's SortRef hierarchy conceptually.

    DatatypeSortRef is intentionally NOT a SortRef subclass (SortRef's __init__
    signature is positional); instead it duck-types the SortRef surface the rest
    of ayz3 reads (`.handle/.kind/.ctx/.bv_size/.domain_sort/.range_sort`).
    """
    return ds


# ---------------------------------------------------------------------------
# Datatype builder (z3py Datatype)
# ---------------------------------------------------------------------------

class Datatype:
    """z3py Datatype builder: declare constructors, then `.create()`."""

    def __init__(self, name, ctx=None):
        self.name = name
        self.ctx = ctx
        self._ctors = []  # list[(ctor_name, [(field_name, field_sort_or_"self")])]

    def declare(self, name, *fields):
        """Declare a constructor `name` with the given `(field_name, sort)` args.

        A field sort may be this same `Datatype` builder (a self-reference) or
        an already-created `DatatypeSortRef`.
        """
        parsed = []
        for f in fields:
            if not (isinstance(f, tuple) and len(f) == 2):
                raise _M.AyZ3Exception(
                    "Datatype.declare fields must be (name, sort) pairs"
                )
            fname, fsort = f
            if fsort is self:
                parsed.append((fname, "self"))
            else:
                parsed.append((fname, fsort))
        self._ctors.append((name, parsed))
        return self

    def create(self):
        """Create the datatype sort (z3py Datatype.create())."""
        if not self._ctors:
            raise _M.AyZ3Exception(
                f"datatype {self.name!r} has no constructors; call declare(...)"
            )
        ctx = self.ctx or _M._current_ctx()
        recipe = _DatatypeRecipe(
            self.name,
            [_CtorRecipe(cn, "is-" + cn, flds) for cn, flds in self._ctors],
        )
        ds = _declare_in_ctx(recipe, ctx)
        ds._attach_attrs()
        return ds


def CreateDatatypes(*datatypes):
    """z3py CreateDatatypes: create several datatypes at once.

    A single datatype (including a self-recursive one) is supported. Several
    datatypes that reference EACH OTHER (mutual recursion) are not supported by
    AY's core yet — rather than mis-encode the cross-datatype references, this
    raises an honest NotImplementedError.
    """
    if len(datatypes) == 1:
        return (datatypes[0].create(),)
    # Detect cross-datatype references among the batch.
    names = {d.name for d in datatypes}
    for d in datatypes:
        for _cn, flds in d._ctors:
            for _fn, fs in flds:
                # A field referencing another builder in this batch by identity.
                if isinstance(fs, Datatype) and fs is not d and fs.name in names:
                    raise NotImplementedError(
                        "mutually recursive datatypes are not supported by AY's "
                        f"core (datatype {d.name!r} references {fs.name!r}); "
                        "declare a single (optionally self-recursive) datatype"
                    )
    return tuple(d.create() for d in datatypes)


# ---------------------------------------------------------------------------
# EnumSort / TupleSort (z3py helpers over Datatype)
# ---------------------------------------------------------------------------

def EnumSort(name, values, ctx=None):
    """z3py EnumSort: an enumeration datatype.

    Returns `(sort, consts)` where `sort` is the DatatypeSortRef and `consts`
    are the enumeration constants (one nullary-constructor value each), matching
    z3py's `Color, (red, green, blue) = EnumSort('Color', ['red','green','blue'])`.
    """
    ctx = ctx or _M._current_ctx()
    recipe = _DatatypeRecipe(
        name, [_CtorRecipe(v, "is-" + v, []) for v in values]
    )
    ds = _declare_in_ctx(recipe, ctx)
    # z3py's EnumSort does NOT attach constructor/recognizer attributes to the
    # sort (it returns the constants separately); match that and only return the
    # sort + constant list.
    consts = [ds._constructors[i].ctor_decl() for i in range(len(values))]
    return ds, consts


def TupleSort(name, sorts, ctx=None):
    """z3py TupleSort: a single-constructor record datatype.

    Returns `(tuple_sort, constructor, [projections])`, matching z3py exactly:
    the single constructor is named `name` (the same symbol as the sort) and the
    projections `project0, project1, ...`.
    """
    ctx = ctx or _M._current_ctx()
    fields = [(f"project{i}", s) for i, s in enumerate(sorts)]
    recipe = _DatatypeRecipe(
        name, [_CtorRecipe(name, "is-" + name, fields)]
    )
    ds = _declare_in_ctx(recipe, ctx)
    ds._attach_attrs()
    ctor = ds._constructors[0].ctor_decl
    projections = list(ds._constructors[0].accessor_decls)
    return ds, ctor, projections


# ---------------------------------------------------------------------------
# Cross-context rebuild hooks (called from ayz3.__init__'s rebuild machinery)
# ---------------------------------------------------------------------------

def _rebuild_datatype_sort(sort, dctx):
    """Re-declare a DatatypeSortRef in dctx (idempotent) and return it."""
    return _declare_in_ctx(sort.recipe, dctx)


def _rebuild_datatype_app(name, src_ctx, dctx, arg_handles):
    """If `name` is a datatype op, rebuild its application in dctx; else None.

    Ensures the owning datatype is declared in dctx (replaying its recipe) so the
    constructor/recognizer/accessor func_decl exists, then applies it to the
    already-rebuilt argument handles.
    """
    op = src_ctx._datatype_ops.get(name)
    if op is None:
        return None
    dt_name = op[1]
    # Ensure the datatype is declared in dctx (replay from the src recipe).
    src_ds = src_ctx._datatype_sorts.get(dt_name)
    if src_ds is None:
        return None
    dds = _declare_in_ctx(src_ds.recipe, dctx)
    ctor_refs = dds._constructors[op[2]]
    if op[0] == "ctor":
        decl = ctor_refs.ctor_decl
    elif op[0] == "recog":
        decl = ctor_refs.recog_decl
    else:  # accessor
        decl = ctor_refs.accessor_decls[op[3]]
    n = len(arg_handles)
    arr = (_lib.Z3_ast * n)(*arg_handles) if n else (_lib.Z3_ast * 0)()
    return lib.Z3_mk_app(dctx.ref, decl.handle, n, arr)


# ---------------------------------------------------------------------------
# Installation onto the ayz3 package
# ---------------------------------------------------------------------------

_EXPORTS = [
    "Datatype", "DatatypeSortRef", "EnumSort", "TupleSort", "CreateDatatypes",
]


def install(mod):
    """Attach the datatype surface onto the top-level `ayz3` module."""
    global _M, _ConstructorFuncDecl
    _M = mod

    class _ConstructorFuncDeclImpl(mod.FuncDeclRef):
        """A datatype constructor. A nullary application (an enum literal) is a
        VAR node in AY's C ABI; record its name + datatype sort so the
        cross-context rebuild machinery (which recovers a const by its recorded
        name) can rebuild it — a plain FuncDeclRef would leave it unrecoverable.
        """

        def __call__(self, *args):
            expr = mod.FuncDeclRef.__call__(self, *args)
            if not args:
                expr.decl_name = self._name
                mod._register_const(expr, self._name)
            return expr

    _ConstructorFuncDecl = _ConstructorFuncDeclImpl

    for nm in _EXPORTS:
        setattr(mod, nm, globals()[nm])
    # Expose the rebuild hooks so __init__'s rebuild machinery can call them.
    mod._rebuild_datatype_sort = _rebuild_datatype_sort
    mod._rebuild_datatype_app = _rebuild_datatype_app

    if hasattr(mod, "__all__"):
        for nm in _EXPORTS:
            if nm not in mod.__all__:
                mod.__all__.append(nm)
