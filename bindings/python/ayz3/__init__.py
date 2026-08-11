# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# ayz3: a z3py-shaped Python binding over AY's Z3-shaped C API (libay_ffi).
#
# This is a CORE SLICE, not a complete z3py. It deliberately mirrors z3py's
# names and behavior closely enough that a typical small z3py snippet runs
# unchanged:
#
#     from ayz3 import Int, Solver, sat
#     x = Int('x')
#     s = Solver()
#     s.add(x > 0, x < 10)
#     assert s.check() == sat
#     m = s.model()
#     assert 0 < m[x].as_long() < 10
#
# CORRECTNESS BOUNDARY: this binding contains no substitute solver; AY computes
# verdicts and models for requests sent through the C ABI. Correctness also
# depends on this module's term encoding, ctypes signatures, context handling,
# and result mapping. Operations without an implemented C-ABI route raise
# NotImplementedError naming the gap.
#
# FEATURES (Phase 4): besides the Int/Bool/Real/BitVec core, this slice wires
# Arrays (Array/ArraySort/Select/Store/K), uninterpreted Functions (Function ->
# FuncDeclRef applied via Z3_mk_app), Quantifiers (ForAll/Exists over declared
# app-const bound variables), and Strings (String/StringVal/Concat/Length/
# Contains/PrefixOf/SuffixOf/IndexOf/SubString=Extract/Replace). All four were
# cross-checked verdict- and value-for-value against real z3py 4.15.4.
#
# DOCUMENTED DIVERGENCES:
#   * String `Distinct` over length-constrained strings: AY may return
#     `unknown` where z3 decides `sat`.
#   * `SeqRef.as_string()` returns the raw literal/model bytes; AY does not
#     parse SMT-LIB escape sequences, so non-ASCII/escaped content may differ
#     from z3py (ASCII content matches exactly).
#   * Algebraic datatypes (`Datatype`/`EnumSort`/`TupleSort`, wired in
#     ayz3/datatypes.py with model readout) support single self-recursive
#     datatypes, but MUTUALLY RECURSIVE datatype groups are unsupported:
#     `CreateDatatypes` raises an honest NotImplementedError rather than
#     mis-encoding the cross-references.
#   * Exact z3py 5.0 has Python naming bugs in its finite-set `SetAdd`,
#     `SetDel`, `IsMember`, and `IsSubset` dispatch branches (each raises
#     NameError). AY intentionally implements the operations those branches
#     were meant to call instead of reproducing those wrapper-only failures.
#
# CONTEXT MODEL (important divergence from a naive single-context binding):
#   In AY's C ABI every `Z3_solver` owns its OWN assertion stack (independent
#   per handle, matching Z3 — the multi-solver fix), but a `Z3_optimize` still
#   aliases the context's single `ay_dpll::api::Solver` engine state. ayz3
#   keeps its ONE-Z3_context-PER-Solver/Optimize design: it isolates Optimize
#   objects and keeps each solver's term arena self-contained. Terms (`Z3_ast`)
#   are arena-interned PER CONTEXT, so an expression is bound to the context it
#   was built in.
#
#   To keep the z3py idiom "build vars first, then make a Solver" working, ayz3
#   uses a CURRENT-CONTEXT model: bare constructors (Int, Bool, And, ...) build
#   in the current context; `Solver()`/`Optimize()` create and *activate* a new
#   context for their lifetime. Mixing expressions across contexts raises a
#   clear error rather than silently misbehaving. For the common single-solver
#   script this is invisible and matches z3py.
#
# REFERENCE COUNTING: we use the non-RC context (Z3_mk_context). AY's terms are
# arena-interned and never individually freed; inc_ref/dec_ref are
# bookkeeping-only. So this slice never touches reference counting.

import ctypes
import numbers
import re
import threading

from . import _lib
from ._lib import lib


class AyZ3Exception(Exception):
    """Raised when the underlying AY C API reports an error."""


# ---------------------------------------------------------------------------
# Context
# ---------------------------------------------------------------------------

class Context:
    """Wraps a Z3_context. Each Solver/Optimize gets its own."""

    def __init__(self):
        cfg = lib.Z3_mk_config()
        try:
            self.ref = lib.Z3_mk_context(cfg)
        finally:
            # The C side reads the config only DURING Z3_mk_context (it copies
            # the params and never stores the config pointer), so the config is
            # freed eagerly here — it must not wait for __del__ (z3py's
            # Context.__init__ does the same).
            lib.Z3_del_config(cfg)
        self.cfg = None
        # Cross-context-rebuild bookkeeping, stored ON the Context so its
        # lifetime is exactly the context's (Python `id()` is reused after a
        # context is GC'd, so id-keyed global dicts can return DANGLING handles
        # from a freed context — a crash hazard. Holding the maps here avoids
        # that entirely.).
        #   _const_meta:    ast_handle -> (name, SortRef)   for declared consts
        #   _const_sorts:   const_name -> sort SIGNATURE     sort-collision guard
        #   _funcdecl_meta: func_name  -> FuncDeclRef       for Function() decls
        #   _rebuild_cache: src_Context -> (src_epoch, {src_ast: dst_ast})
        #     rebuild memo; the epoch drops the memo when a rec definition
        #     over src_Context is replaced (see _rebuild_cache_for)
        self._const_meta = {}
        self._const_sorts = {}
        self._funcdecl_meta = {}
        self._rebuild_cache = {}
        # Array-combinator registries for the cross-context rebuild (keyed by
        # ast handle; AY hash-conses, so handles are stable within a context):
        #   _map_meta:      map_ast     -> (FuncDeclRef f, (ArrayRef, ...) args)
        #   _ext_meta:      witness_ast -> (ArrayRef a, ArrayRef b)
        #   _as_array_meta: array_ast   -> FuncDeclRef f
        # SOUNDNESS: a Map/Ext term must NEVER be rebuilt through the generic
        # const/UF paths (registering the Ext witness in _const_meta would
        # rebuild it as a bare const and DROP the extensionality background
        # axiom; registering map[f] in _funcdecl_meta would rebuild it as a
        # plain UF and DROP the eager select rewrite — both REAL wrong-verdict
        # channels). `_rebuild_ast` consults these registries FIRST and
        # re-invokes Z3_mk_map / Z3_mk_array_ext in the destination context on
        # the recursively rebuilt f/args, so the destination derives its OWN
        # witness + background axiom.
        self._map_meta = {}
        self._ext_meta = {}
        self._as_array_meta = {}
        # Algebraic-datatype registries (B-6), keyed by name so a datatype is
        # declared once per context and re-declared on demand when an expression
        # is rebuilt into another context:
        #   _datatype_sorts: datatype name -> DatatypeSortRef (in THIS context)
        #   _datatype_ops:   op decl name  -> (kind, dt_name, ctor_i[, field_j])
        #                    for constructor / recognizer / accessor routing.
        self._datatype_sorts = {}
        self._datatype_ops = {}
        # Quantifier metadata the core does not persist / cannot read back through
        # the C ABI, recorded at construction keyed by the quantifier AST handle:
        #   _quantifier_weight:   ast -> int weight  (AY's core ignores weights;
        #                         z3py's default is 1, so weight() defaults to 1)
        #   _quantifier_patterns: ast -> [PatternRef] trigger patterns supplied
        self._quantifier_weight = {}
        self._quantifier_patterns = {}

    def __del__(self):
        # Free the native context (a full solver engine + term arenas) once no
        # wrapper can reach it. Every handle wrapper (AstRef/SortRef/Solver/
        # Optimize/ModelRef/Statistics/...) holds a strong reference to its
        # Context, so under CPython refcounting this fires only after every
        # object holding a handle into this context is already gone — the
        # Context is the sole OWNER of the native allocation. `self.ref` is
        # nulled BEFORE the C call so a double-invocation (e.g. object
        # resurrection) can never double-free. The try/except guards
        # interpreter shutdown, where module globals (`lib`) may already be
        # torn down / set to None — then we simply leak into process exit,
        # which is safe.
        try:
            ref = getattr(self, "ref", None)
            if ref and lib is not None:
                self.ref = None
                lib.Z3_del_context(ref)
        except Exception:
            pass

    def check_error(self, where):
        code = lib.Z3_get_error_code(self.ref)
        if code != 0:
            msg = lib.Z3_get_error_msg(self.ref, code)
            msg = msg.decode() if msg else "<no message>"
            raise AyZ3Exception(f"{where}: AY error {code}: {msg}")


# A default/main context for bare expression building outside any Solver, plus
# a thread-local "current context" that Solver()/Optimize() temporarily install.
_main_ctx = Context()
_tls = threading.local()


def _reset_default_context():
    """TEST SUPPORT: replace the shared default context with a fresh one.

    The module-level default context interns constants BY NAME for the life of
    the process, and `_mk_const`'s sort-collision soundness guard (see
    `_mk_const`) rightly rejects re-declaring a name at a different sort within
    one context. Independent test files that reuse a short name at different
    sorts (e.g. `Int('a')` in one file, `Bool('a')` in another) would therefore
    fail purely due to suite ordering. This swaps in a pristine default context
    (fresh name registry) and clears any leaked thread-local scoped context.

    It does NOT weaken the guard and does NOT invalidate existing objects:
    every expression/solver holds a strong reference to its own Context, so
    previously built terms stay alive and correct — they simply no longer share
    name interning with terms built after the reset.

    Not part of the z3py-compatible public surface; intended for test harnesses
    (see bindings/python/conftest.py).
    """
    global _main_ctx
    _main_ctx = Context()
    _tls.ctx = None


# ---------------------------------------------------------------------------
# Cross-context introspection registries
# ---------------------------------------------------------------------------
#
# AY's C ABI cannot read back the NAME of a declared constant from its AST
# handle (Z3_to_app/Z3_get_app_decl return null for a Var node, and
# Z3_ast_to_string prints an opaque `(ast N : Int)` handle). To rebuild an
# expression in a different context we therefore record, at construction time,
# the metadata we cannot otherwise recover: a declared const's name+sort, and a
# Function's declaration. These maps live ON each Context (see Context.__init__)
# so their lifetime matches the context's. AY hash-conses terms, so a given
# const always has the same handle within its context — including when it
# reappears as a sub-term reached via Z3_get_app_arg.
#
# The funcdecl registry is keyed by NAME because an application's decl is
# recovered from Z3_get_app_decl (a fresh synthetic handle each call), not from
# a stable AST handle; the name + recovered domain/range identify it uniquely.


def _register_const(expr, name):
    expr.ctx._const_meta[expr.ast] = (name, expr.sort_ref)


def _register_funcdecl(fd):
    fd.ctx._funcdecl_meta[fd._name] = fd


def _current_ctx():
    return getattr(_tls, "ctx", None) or _main_ctx


def _solver_ctx(ctx):
    """Pick the Context a new Solver/Optimize should bind to.

    Priority:
      1. An explicitly passed Context (caller controls isolation themselves).
      2. A scoped context active via `with ctx_scope/using():` — adopt it, so
         the established "build vars and solver in one scope" idiom builds the
         solver over that scope's term arena (no cross-context rebuild). Each
         solver still has its own independent assertion stack at the C level.
      3. Otherwise (top level): a FRESH Context per Solver/Optimize. This is
         what makes several top-level solvers genuinely independent the way
         z3py's are — constraints built over top-level vars (in `_main_ctx`)
         are transparently rebuilt into each solver's own context on `add`.
    """
    if ctx is not None:
        return ctx
    scoped = getattr(_tls, "ctx", None)
    if scoped is not None:
        return scoped
    return Context()


class _ctx_scope:
    def __init__(self, ctx):
        self.ctx = ctx

    def __enter__(self):
        self.prev = getattr(_tls, "ctx", None)
        _tls.ctx = self.ctx
        return self.ctx

    def __exit__(self, *exc):
        _tls.ctx = self.prev


# ---------------------------------------------------------------------------
# lbool result objects (mirror z3py's sat / unsat / unknown singletons)
# ---------------------------------------------------------------------------

class CheckSatResult:
    def __init__(self, r):
        self._r = r

    def __eq__(self, other):
        return isinstance(other, CheckSatResult) and self._r == other._r

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self._r)

    def __repr__(self):
        return {1: "sat", -1: "unsat", 0: "unknown"}[self._r]


sat = CheckSatResult(_lib.Z3_L_TRUE)
unsat = CheckSatResult(_lib.Z3_L_FALSE)
unknown = CheckSatResult(_lib.Z3_L_UNDEF)


def _lbool_to_result(v):
    if v == _lib.Z3_L_TRUE:
        return sat
    if v == _lib.Z3_L_FALSE:
        return unsat
    return unknown


# ---------------------------------------------------------------------------
# Sorts
# ---------------------------------------------------------------------------

class SortRef:
    def __init__(self, handle, kind, ctx, bv_size=0, domain=None, range=None,
                 basis=None):
        self.handle = handle      # Z3_sort (c_void_p value)
        # "Bool" | "Int" | "Real" | "BitVec" | "Array" | "String" | "Seq" | ...
        self.kind = kind
        self.ctx = ctx
        self.bv_size = bv_size
        # Array sorts carry their domain/range SortRefs.
        self.domain_sort = domain
        self.range_sort = range
        # Sequence sorts (z3py SeqSortRef) carry their element ("basis") SortRef.
        self.basis_sort = basis

    def __repr__(self):
        if self.kind == "BitVec":
            return f"BitVec({self.bv_size})"
        if self.kind == "Array":
            return f"Array({self.domain_sort}, {self.range_sort})"
        if self.kind == "Seq":
            # z3py renders SeqSort(Int) as `Seq(Int)`.
            return f"Seq({self.basis_sort})"
        if self.kind == "FiniteSet":
            return f"FiniteSet({self.basis_sort})"
        return self.kind

    def name(self):
        """The sort's constructor name (z3py SortRef.name())."""
        if self.kind == "Seq":
            return "Seq"
        if self.kind == "FiniteSet":
            return "FiniteSet"
        return self.kind

    def sexpr(self):
        """The SMT-LIB s-expression for this sort (z3py SortRef.sexpr()).

        A sequence sort renders `(Seq <elem>)`; other sorts defer to AY's
        `Z3_sort_to_string`, matching z3py's rendering for the primitive sorts
        (`Int`, `Real`, `Bool`, `String`, `(_ BitVec n)`, ...).
        """
        if self.kind == "Seq" and self.basis_sort is not None:
            return f"(Seq {self.basis_sort.sexpr()})"
        s = lib.Z3_sort_to_string(self.ctx.ref, self.handle)
        return s.decode().strip() if s else repr(self)

    def basis(self):
        """The element sort of a sequence sort (z3py SeqSortRef.basis())."""
        if self.kind != "Seq" or self.basis_sort is None:
            raise AyZ3Exception(
                f"basis() is only defined on a sequence sort, not {self.kind}")
        return self.basis_sort

    def size(self):
        """The bit width of a bitvector sort (z3py BitVecSortRef.size())."""
        if self.kind != "BitVec":
            raise AyZ3Exception(f"size() is only defined on a BitVec sort, not {self.kind}")
        return self.bv_size


def _bool_sort(ctx=None):
    ctx = ctx or _current_ctx()
    return SortRef(lib.Z3_mk_bool_sort(ctx.ref), "Bool", ctx)


def _int_sort(ctx=None):
    ctx = ctx or _current_ctx()
    return SortRef(lib.Z3_mk_int_sort(ctx.ref), "Int", ctx)


def _real_sort(ctx=None):
    ctx = ctx or _current_ctx()
    return SortRef(lib.Z3_mk_real_sort(ctx.ref), "Real", ctx)


def _bv_sort(bits, ctx=None):
    ctx = ctx or _current_ctx()
    return SortRef(lib.Z3_mk_bv_sort(ctx.ref, bits), "BitVec", ctx, bits)


def BoolSort():
    return _bool_sort()


def IntSort():
    return _int_sort()


def RealSort():
    return _real_sort()


def BitVecSort(bits):
    return _bv_sort(bits)


def _array_sort(dom, rng, ctx=None):
    ctx = ctx or _current_ctx()
    handle = lib.Z3_mk_array_sort(ctx.ref, dom.handle, rng.handle)
    return SortRef(handle, "Array", ctx, domain=dom, range=rng)


def _string_sort(ctx=None):
    ctx = ctx or _current_ctx()
    return SortRef(lib.Z3_mk_string_sort(ctx.ref), "String", ctx)


def _re_sort(basis=None, ctx=None):
    """Build the regular-expression sort (RegLan).

    AY's regex sort is monomorphic (every AY regex is over strings), so the
    optional `basis` sequence/string sort is accepted for z3py fidelity but does
    not parameterize the result.
    """
    ctx = ctx or (basis.ctx if isinstance(basis, SortRef) else _current_ctx())
    basis = basis if isinstance(basis, SortRef) else _string_sort(ctx)
    return SortRef(lib.Z3_mk_re_sort(ctx.ref, basis.handle), "RegLan", ctx)


def ArraySort(dom, rng):
    return _array_sort(dom, rng)


def StringSort():
    return _string_sort()


def _char_sort(ctx=None):
    """The character sort (z3py CharSort; SMT `Char`).

    AY models a Char as a bounded-Int code point; the sort handle reports kind
    `Z3_CHAR_SORT` (13) exactly like Z3.
    """
    ctx = ctx or _current_ctx()
    return SortRef(lib.Z3_mk_char_sort(ctx.ref), "Char", ctx)


def SeqSort(elem):
    """The sequence sort `(Seq elem)` over element sort `elem` (z3py `SeqSort`).

    Returns a `SortRef` (AY has no distinct `SeqSortRef`) whose `kind` is `Seq`,
    whose `basis()` is `elem`, and whose `sexpr()` is `(Seq <elem>)` — matching
    z3py's observable behavior (`repr` `Seq(Int)`, `name()` `Seq`, `kind()`
    `Z3_SEQ_SORT`). AY builds the genuine sequence sort, so two consts of it
    decide equality soundly.
    """
    if not isinstance(elem, SortRef):
        raise AyZ3Exception(
            "SeqSort expects an element SortRef, e.g. SeqSort(IntSort())")
    ctx = elem.ctx
    handle = lib.Z3_mk_seq_sort(ctx.ref, elem.handle)
    return SortRef(handle, "Seq", ctx, basis=elem)


def ReSort(basis=None):
    """The regular-expression sort over `basis` (z3py `ReSort(StringSort())`).

    AY's RegLan is string-monomorphic; `basis` defaults to the String sort.
    """
    return _re_sort(basis)


class FiniteSetSortRef(SortRef):
    """Z3 5.0.0's distinct finite-set sort."""

    def __init__(self, handle, elem_sort, ctx):
        super().__init__(handle, "FiniteSet", ctx, basis=elem_sort)

    def element_sort(self):
        return self.basis_sort

    def cast(self, value):
        if isinstance(value, FiniteSetRef):
            if _sorts_equal(self, value.sort_ref):
                return value
            raise AyZ3Exception("Cannot cast between different finite-set sorts")
        if isinstance(value, set):
            result = FiniteSetEmpty(self)
            for element in value:
                result = FiniteSetUnion(
                    result, Singleton(_coerce(element, self.basis_sort, self.ctx))
                )
            return result
        raise AyZ3Exception(f"Cannot cast {value!r} to {self}")


def FiniteSetSort(elem_sort):
    """Create the distinct Z3 5.0.0 finite-set sort over `elem_sort`."""
    if not isinstance(elem_sort, SortRef):
        raise AyZ3Exception("FiniteSetSort expects an element SortRef")
    handle = lib.Z3_mk_finite_set_sort(elem_sort.ctx.ref, elem_sort.handle)
    if not handle:
        elem_sort.ctx.check_error("FiniteSetSort")
    return FiniteSetSortRef(handle, elem_sort, elem_sort.ctx)


# ---------------------------------------------------------------------------
# AST nodes
# ---------------------------------------------------------------------------

def _same_ctx(*exprs):
    ctxs = {e.ctx for e in exprs}
    if len(ctxs) > 1:
        raise AyZ3Exception(
            "expressions from different contexts mixed; build all sub-expressions "
            "for a given Solver in the same scope"
        )
    return next(iter(ctxs))


def _as_ast_array(asts):
    n = len(asts)
    arr = (_lib.Z3_ast * n)(*[a.ast for a in asts])
    return n, arr


_SMT2_SIMPLE_SYMBOL_RE = re.compile(
    r"[A-Za-z~!@$%^&*_\-+=<>.?/][A-Za-z0-9~!@$%^&*_\-+=<>.?/]*\Z"
)


def _smt2_symbol(name):
    """Render a string symbol the way Z3's SMT-LIB printer does."""
    if not name:
        # Z3's empty string symbol is printed as the conventional `null`.
        return "null"
    if _SMT2_SIMPLE_SYMBOL_RE.fullmatch(name):
        return name
    escaped = name.replace("\\", "\\\\").replace("|", "\\|")
    return f"|{escaped}|"


def _canonicalize_as_array_text(text, ctx):
    """Replace AY-private as-array identities with their public Z3 spelling."""
    for ast, fd in ctx._as_array_meta.items():
        raw = lib.Z3_ast_to_string(ctx.ref, ast)
        if raw:
            text = text.replace(
                raw.decode(), f"(_ as-array {_smt2_symbol(fd._name)})"
            )
    return text


class AstRef:
    """Base class for all expressions. Holds a Z3_ast handle (u64), a SortRef
    and the Context it was built in."""

    def __init__(self, ast, sort, ctx):
        self.ast = int(ast)   # the u64 handle
        self.sort_ref = sort
        self.ctx = ctx
        # Set for 0-arity constants so model lookup can match by name. None for
        # compound expressions / literals.
        self.decl_name = None
        # True for values produced by a model (m[x] / m.eval(...)). AY's
        # Z3_ast_to_string renders a model value as an opaque `(ast N : Int)`
        # handle, whereas z3py prints the CONCRETE value (e.g. `7`). When this
        # flag is set, __repr__ renders the concrete content instead.
        self._is_model_value = False

    def sort(self):
        return self.sort_ref

    def translate(self, target_ctx):
        """Copy this AST into `target_ctx` (z3py AstRef.translate).

        Returns an equivalent term in the target context — the same term AY
        would build natively there — via the cross-context rebuild machinery
        (`_adopt`, the same path `Solver.add` uses to accept a foreign-context
        constraint). Returns self unchanged when `target_ctx` is already this
        term's context. Declared-constant name metadata is preserved so model
        lookups on the translated term keep working.
        """
        if not isinstance(target_ctx, Context):
            raise NotImplementedError("AstRef.translate expects a Context")
        return _adopt(self, target_ctx)

    def sexpr(self):
        """The SMT-LIB s-expression for this term (z3py AstRef.sexpr()).

        Returns AY's `Z3_ast_to_string` rendering — the same text z3py's
        `sexpr()` produces for a term (e.g. `(+ 3 y)`, `(to_real x)`). A value
        produced by a model renders its concrete content (numeral / Bool /
        quoted string), matching how z3py prints a model value, rather than
        AY's internal opaque handle form.
        """
        if self._is_model_value:
            return _canonicalize_as_array_text(_render_model_value(self), self.ctx)
        s = lib.Z3_ast_to_string(self.ctx.ref, self.ast)
        if not s:
            return f"<ast {self.ast}>"
        return _canonicalize_as_array_text(s.decode(), self.ctx)

    def __repr__(self):
        if self._is_model_value:
            return _canonicalize_as_array_text(_render_model_value(self), self.ctx)
        s = lib.Z3_ast_to_string(self.ctx.ref, self.ast)
        if not s:
            return f"<ast {self.ast}>"
        return _canonicalize_as_array_text(s.decode(), self.ctx)

    def __eq__(self, other):
        other = _coerce(other, self.sort_ref, self.ctx)
        if (
            self.sort_ref.kind == "FiniteSet"
            or other.sort_ref.kind == "FiniteSet"
        ) and not _sorts_equal(self.sort_ref, other.sort_ref):
            raise AyZ3Exception(
                f"sort mismatch: cannot compare {self.sort_ref} and {other.sort_ref}"
            )
        ctx = _same_ctx(self, other)
        lhs, rhs = _promote_arith(self, other, ctx)
        return BoolRef(
            lib.Z3_mk_eq(ctx.ref, lhs.ast, rhs.ast), _bool_sort(ctx), ctx
        )

    def __ne__(self, other):
        other = _coerce(other, self.sort_ref, self.ctx)
        if (
            self.sort_ref.kind == "FiniteSet"
            or other.sort_ref.kind == "FiniteSet"
        ) and not _sorts_equal(self.sort_ref, other.sort_ref):
            raise AyZ3Exception(
                f"sort mismatch: cannot compare {self.sort_ref} and {other.sort_ref}"
            )
        ctx = _same_ctx(self, other)
        lhs, rhs = _promote_arith(self, other, ctx)
        n, arr = _as_ast_array([lhs, rhs])
        return BoolRef(
            lib.Z3_mk_distinct(ctx.ref, n, arr), _bool_sort(ctx), ctx
        )

    def __hash__(self):
        return hash((id(self.ctx), self.ast, self.sort_ref.kind))


def _wrap(ast, sort, ctx):
    if ast == 0:
        ctx.check_error("expression construction")
        raise AyZ3Exception("AY returned the null AST (0) for an expression")
    if sort.kind == "Bool":
        return BoolRef(ast, sort, ctx)
    if sort.kind == "BitVec":
        return BitVecRef(ast, sort, ctx)
    if sort.kind == "Array":
        return ArrayRef(ast, sort, ctx)
    if sort.kind == "FiniteSet":
        return FiniteSetRef(ast, sort, ctx)
    if sort.kind == "String":
        return SeqRef(ast, sort, ctx)
    if sort.kind == "RegLan":
        return ReRef(ast, sort, ctx)
    if sort.kind == "Datatype":
        return DatatypeRef(ast, sort, ctx)
    if sort.kind == "FloatingPoint":
        from .fp import FPRef
        return FPRef(ast, sort, ctx)
    if sort.kind == "RoundingMode":
        from .fp import FPRMRef
        return FPRMRef(ast, sort, ctx)
    return ArithRef(ast, sort, ctx)


# --- arithmetic-flavored class (Int / Real) --------------------------------

class ArithRef(AstRef):
    """Integer or Real expression."""

    def _bin(self, other, mk_nary):
        other = _coerce(other, self.sort_ref, self.ctx)
        ctx = _same_ctx(self, other)
        sort = _result_arith_sort(self.sort_ref, other.sort_ref, ctx)
        lhs, rhs = _promote_arith(self, other, ctx)
        n, arr = _as_ast_array([lhs, rhs])
        return _wrap(mk_nary(ctx.ref, n, arr), sort, ctx)

    def __add__(self, other):
        return self._bin(other, lib.Z3_mk_add)

    def __radd__(self, other):
        return _coerce(other, self.sort_ref, self.ctx)._bin(self, lib.Z3_mk_add)

    def __sub__(self, other):
        return self._bin(other, lib.Z3_mk_sub)

    def __rsub__(self, other):
        return _coerce(other, self.sort_ref, self.ctx)._bin(self, lib.Z3_mk_sub)

    def __mul__(self, other):
        return self._bin(other, lib.Z3_mk_mul)

    def __rmul__(self, other):
        return _coerce(other, self.sort_ref, self.ctx)._bin(self, lib.Z3_mk_mul)

    def __neg__(self):
        return _wrap(lib.Z3_mk_unary_minus(self.ctx.ref, self.ast), self.sort_ref, self.ctx)

    def __truediv__(self, other):
        other = _coerce(other, self.sort_ref, self.ctx)
        ctx = _same_ctx(self, other)
        sort = _result_arith_sort(self.sort_ref, other.sort_ref, ctx)
        lhs, rhs = _promote_arith(self, other, ctx)
        return _wrap(lib.Z3_mk_div(ctx.ref, lhs.ast, rhs.ast), sort, ctx)

    def __mod__(self, other):
        # z3py mod is Int-only; a Real operand is a type error, so we do not
        # promote here (a mixed Int/Real mod has no z3py meaning).
        other = _coerce(other, self.sort_ref, self.ctx)
        ctx = _same_ctx(self, other)
        return _wrap(lib.Z3_mk_mod(ctx.ref, self.ast, other.ast), _int_sort(ctx), ctx)

    def _cmp(self, other, mk):
        other = _coerce(other, self.sort_ref, self.ctx)
        ctx = _same_ctx(self, other)
        lhs, rhs = _promote_arith(self, other, ctx)
        return BoolRef(mk(ctx.ref, lhs.ast, rhs.ast), _bool_sort(ctx), ctx)

    def __lt__(self, other):
        return self._cmp(other, lib.Z3_mk_lt)

    def __le__(self, other):
        return self._cmp(other, lib.Z3_mk_le)

    def __gt__(self, other):
        return self._cmp(other, lib.Z3_mk_gt)

    def __ge__(self, other):
        return self._cmp(other, lib.Z3_mk_ge)

    def as_long(self):
        """Return the value as a Python int (Int sorts; whole Reals)."""
        text = self._numeral_string("as_long")
        if "/" in text:
            num, den = text.split("/")
            q, r = divmod(int(num), int(den))
            if r != 0:
                raise AyZ3Exception(f"as_long() on non-integer rational {text}")
            return q
        return int(text)

    def as_fraction(self):
        """Return the value as a Python Fraction (Real sorts)."""
        from fractions import Fraction
        text = self._numeral_string("as_fraction")
        if "/" in text:
            num, den = text.split("/")
            return Fraction(int(num), int(den))
        return Fraction(int(text))

    def as_string(self):
        s = lib.Z3_get_numeral_string(self.ctx.ref, self.ast)
        return s.decode() if s else None

    def _numeral_string(self, who):
        s = lib.Z3_get_numeral_string(self.ctx.ref, self.ast)
        if not s:
            raise AyZ3Exception(f"not a numeral; {who}() needs a model value")
        return s.decode()


class _SizeInt(int):
    """An int that is ALSO callable, returning itself.

    z3py's `BitVec(...).size()` is a METHOD returning the bit width, but ayz3's
    internals read `.size` as a plain int (`a.size + n`). This int subclass makes
    a single value serve both: `bv.size` behaves as the int width everywhere it
    is used arithmetically, and `bv.size()` calls through to return the same int —
    so `BitVec('a', 8).size() == 8` works exactly like z3py while every existing
    `.size`-as-int use keeps functioning.
    """

    def __call__(self):
        return int(self)


class BitVecRef(AstRef):
    """Fixed-width bitvector expression."""

    @property
    def size(self):
        return _SizeInt(self.sort_ref.bv_size)

    def _bv_bin(self, other, mk):
        other = _coerce(other, self.sort_ref, self.ctx)
        ctx = _same_ctx(self, other)
        return _wrap(mk(ctx.ref, self.ast, other.ast), self.sort_ref, ctx)

    def __add__(self, other):
        return self._bv_bin(other, lib.Z3_mk_bvadd)

    def __radd__(self, other):
        return _coerce(other, self.sort_ref, self.ctx)._bv_bin(self, lib.Z3_mk_bvadd)

    def __sub__(self, other):
        return self._bv_bin(other, lib.Z3_mk_bvsub)

    def __mul__(self, other):
        return self._bv_bin(other, lib.Z3_mk_bvmul)

    def __and__(self, other):
        return self._bv_bin(other, lib.Z3_mk_bvand)

    def __or__(self, other):
        return self._bv_bin(other, lib.Z3_mk_bvor)

    def __xor__(self, other):
        return self._bv_bin(other, lib.Z3_mk_bvxor)

    def __invert__(self):
        return _wrap(lib.Z3_mk_bvnot(self.ctx.ref, self.ast), self.sort_ref, self.ctx)

    def __neg__(self):
        return _wrap(lib.Z3_mk_bvneg(self.ctx.ref, self.ast), self.sort_ref, self.ctx)

    # z3py default comparisons on BitVec are SIGNED (bvslt/bvsle/bvsgt/bvsge).
    # Use the free functions ULT/ULE/UGT/UGE for unsigned comparison.
    def _bv_cmp(self, other, mk):
        other = _coerce(other, self.sort_ref, self.ctx)
        ctx = _same_ctx(self, other)
        return BoolRef(mk(ctx.ref, self.ast, other.ast), _bool_sort(ctx), ctx)

    def __lt__(self, other):
        return self._bv_cmp(other, lib.Z3_mk_bvslt)

    def __le__(self, other):
        return self._bv_cmp(other, lib.Z3_mk_bvsle)

    def __gt__(self, other):
        return self._bv_cmp(other, lib.Z3_mk_bvsgt)

    def __ge__(self, other):
        return self._bv_cmp(other, lib.Z3_mk_bvsge)

    # z3py maps the Python arithmetic/shift operators on BitVec to the SIGNED bv
    # operations (exactly matching z3py's BitVecRef): `x / y` -> bvsdiv,
    # `x % y` -> bvsmod, `x >> y` -> bvashr (arithmetic), `x << y` -> bvshl.
    # The unsigned / signed-remainder variants are the free functions
    # UDiv / URem / SRem / SMod / LShR / AShR.
    def _bv_bin_r(self, other, mk):
        return _coerce(other, self.sort_ref, self.ctx)._bv_bin(self, mk)

    def __mod__(self, other):
        return self._bv_bin(other, lib.Z3_mk_bvsmod)

    def __rmod__(self, other):
        return self._bv_bin_r(other, lib.Z3_mk_bvsmod)

    def __truediv__(self, other):
        return self._bv_bin(other, lib.Z3_mk_bvsdiv)

    def __rtruediv__(self, other):
        return self._bv_bin_r(other, lib.Z3_mk_bvsdiv)

    # z3py keeps the legacy __div__/__rdiv__ names as aliases of true division.
    __div__ = __truediv__
    __rdiv__ = __rtruediv__

    def __rshift__(self, other):
        return self._bv_bin(other, lib.Z3_mk_bvashr)

    def __rrshift__(self, other):
        return self._bv_bin_r(other, lib.Z3_mk_bvashr)

    def __lshift__(self, other):
        return self._bv_bin(other, lib.Z3_mk_bvshl)

    def __rlshift__(self, other):
        return self._bv_bin_r(other, lib.Z3_mk_bvshl)

    def as_long(self):
        s = lib.Z3_get_numeral_string(self.ctx.ref, self.ast)
        if not s:
            raise AyZ3Exception("not a numeral; as_long() needs a model value")
        return int(s.decode())


# ---------------------------------------------------------------------------
# Numeral value subtypes (z3py IntNumRef / RatNumRef / BitVecNumRef)
# ---------------------------------------------------------------------------
#
# z3py returns these NUMERAL subtypes for concrete values — model values
# (`m[x]`) and literals (`IntVal`/`RealVal`/`BitVecVal`) — so an isinstance
# check (`isinstance(m[x], IntNumRef)`) and value accessors (`.as_long()`,
# `.numerator_as_long()`, `.as_signed_long()`) work. A NON-value expression
# (`Int('x')`, `x + 1`) stays a plain ArithRef/BitVecRef, exactly as in z3py.

class IntNumRef(ArithRef):
    """A concrete Int value (z3py IntNumRef). `as_long()` is the Python int."""

    def as_binary_string(self):
        """The value as a base-2 string (z3py IntNumRef.as_binary_string())."""
        return format(self.as_long(), "b")


class RatNumRef(ArithRef):
    """A concrete Real (rational) value (z3py RatNumRef)."""

    def numerator_as_long(self):
        return self.as_fraction().numerator

    def denominator_as_long(self):
        return self.as_fraction().denominator

    def numerator(self):
        """The numerator as an IntNumRef (z3py RatNumRef.numerator())."""
        return IntVal(self.numerator_as_long(), self.ctx)

    def denominator(self):
        """The denominator as an IntNumRef (z3py RatNumRef.denominator())."""
        return IntVal(self.denominator_as_long(), self.ctx)

    def is_int_value(self):
        """True iff this rational is a whole number (z3py RatNumRef.is_int_value())."""
        return self.denominator_as_long() == 1

    def as_decimal(self, prec):
        """Decimal string with `prec` fractional digits (z3py RatNumRef.as_decimal()).

        Truncated (not rounded) toward zero; a trailing `?` marks an expansion
        that did not terminate within `prec` digits, matching z3py exactly.
        """
        fr = self.as_fraction()
        sign = "-" if fr < 0 else ""
        fr = -fr if fr < 0 else fr
        int_part = fr.numerator // fr.denominator
        rem = fr - int_part
        if rem == 0:
            return f"{sign}{int_part}"
        digits = []
        for _ in range(prec):
            rem *= 10
            d = rem.numerator // rem.denominator
            digits.append(str(d))
            rem -= d
            if rem == 0:
                break
        out = f"{sign}{int_part}." + "".join(digits)
        if rem != 0:
            out += "?"
        return out


class BitVecNumRef(BitVecRef):
    """A concrete bitvector value (z3py BitVecNumRef)."""

    def as_signed_long(self):
        """The two's-complement signed value (z3py BitVecNumRef.as_signed_long())."""
        sz = self.sort_ref.bv_size
        val = self.as_long()
        if sz > 0 and val >= (1 << (sz - 1)):
            val -= (1 << sz)
        return val

    def as_string(self):
        return str(self.as_long())

    def as_binary_string(self):
        """The value as a base-2 string (z3py BitVecNumRef.as_binary_string())."""
        return format(self.as_long(), "b")


def _as_numref(val):
    """Return `val` as the z3py numeral subtype when it is a concrete numeral.

    Rewraps a concrete Int/Real/BitVec value into IntNumRef / RatNumRef /
    BitVecNumRef (preserving the handle, sort, context and model-value flag) so
    `isinstance(...)` and the numeral accessors match z3py. A non-numeral or a
    sort without a numeral subtype is returned unchanged (never fabricated).
    """
    if not isinstance(val, AstRef):
        return val
    k = val.sort_ref.kind
    if k == "FloatingPoint":
        from .fp import FPNumRef, _fp_ref_fields
        if isinstance(val, FPNumRef) or _fp_ref_fields(val) is None:
            return val
        cls = FPNumRef
        out = cls(val.ast, val.sort_ref, val.ctx)
        out._is_model_value = val._is_model_value
        out.decl_name = val.decl_name
        return out
    cls = {"Int": IntNumRef, "Real": RatNumRef, "BitVec": BitVecNumRef}.get(k)
    if cls is None or isinstance(val, cls):
        return val
    out = cls(val.ast, val.sort_ref, val.ctx)
    out._is_model_value = val._is_model_value
    out.decl_name = val.decl_name
    return out


class BoolRef(AstRef):
    """Boolean expression."""

    def __invert__(self):
        return Not(self)

    # z3py overloads &/|/^ on Bool to And/Or/Xor (a Python bool operand is
    # coerced through the same path as And/Or/Xor themselves).
    def __and__(self, other):
        return And(self, other)

    def __rand__(self, other):
        return And(other, self)

    def __or__(self, other):
        return Or(self, other)

    def __ror__(self, other):
        return Or(other, self)

    def __xor__(self, other):
        return Xor(self, other)

    def __rxor__(self, other):
        return Xor(other, self)

    def as_bool(self):
        v = lib.Z3_get_bool_value(self.ctx.ref, self.ast)
        if v == _lib.Z3_L_TRUE:
            return True
        if v == _lib.Z3_L_FALSE:
            return False
        return None


class ArrayRef(AstRef):
    """Array expression (sort `Array(domain, range)`)."""

    def domain(self):
        return self.sort_ref.domain_sort

    def range(self):
        return self.sort_ref.range_sort

    def __getitem__(self, index):
        """a[i] is sugar for Select(a, i)."""
        return Select(self, index)


class SeqRef(AstRef):
    """Sequence/String expression.

    AY models a String as a first-class String sort (Z3 reports it as a
    sequence sort). Concatenation uses Python `+` to mirror z3py.
    """

    def __add__(self, other):
        return Concat(self, other)

    def __radd__(self, other):
        return Concat(other, self)

    def at(self, i):
        """The length-1 subsequence at index `i` (z3py `SeqRef.at`, SMT `seq.at`).

        Returns a String/sequence (NOT the element): `s.at(0)` is the one-char
        string at position 0, or the empty string when `i` is out of range —
        matching z3py exactly.
        """
        ctx = self.ctx
        idx = _coerce(i, _int_sort(ctx), ctx)
        return _wrap(lib.Z3_mk_seq_at(ctx.ref, self.ast, idx.ast),
                     self.sort_ref, ctx)

    def __getitem__(self, i):
        """z3py `s[i]` — the ELEMENT at index `i` (SMT `seq.nth`).

        DIVERGENCE (documented, never faked): AY's sequence theory does not
        implement `seq.nth` (element extraction), so this raises
        NotImplementedError. Use `s.at(i)` for the length-1 SUBSEQUENCE at `i`
        (which AY backs and z3py also provides).
        """
        raise NotImplementedError(
            "SeqRef indexing s[i] (seq.nth element extraction) is not implemented "
            "by AY's sequence theory. Use s.at(i) for the length-1 subsequence at i."
        )

    def as_string(self):
        """Return the string content of a literal / model value as a Python str.

        NOTE: AY treats the bytes of a string literal as the literal content
        and does not parse SMT-LIB escape sequences, so non-ASCII / escaped
        content may differ from z3py. ASCII content matches z3py exactly.
        """
        s = lib.Z3_get_numeral_string(self.ctx.ref, self.ast)
        if s is None:
            raise AyZ3Exception(
                "not a string value; as_string() needs a literal or model value"
            )
        return s.decode()


class ReRef(AstRef):
    """A regular-expression expression (z3py ReRef), of sort RegLan.

    Built by `Re`/`to_re`, `Star`, `Plus`, `Option`, `Complement`, `Union`,
    `Intersect`, `Concat` (over regexes), `Range`, `Loop`, `Full`, `Empty`, and
    `AllChar`. Membership is tested with `InRe(seq, re)`. Each maps onto AY's
    native `re.*` theory operations, whose sat/unsat verdicts match Z3's (or,
    where AY's regex/sequence decision procedure is incomplete, a sound
    `unknown` — never a wrong answer).
    """

    def __add__(self, other):
        # z3py: `re1 + re2` is regex union (matches Z3's ReRef.__add__). z3py
        # deliberately does NOT overload `*`/`|` on regexes, so neither do we.
        return Union(self, other)


class FiniteSetRef(AstRef):
    """An expression in Z3 5.0.0's distinct finite-set theory."""

    def __or__(self, other):
        return FiniteSetUnion(self, other)

    def __and__(self, other):
        return FiniteSetIntersect(self, other)

    def __sub__(self, other):
        return FiniteSetDifference(self, other)


class DatatypeRef(AstRef):
    """An algebraic-datatype expression (z3py DatatypeRef).

    A datatype value in a model is a constructor application (e.g. `blue` or
    `(mk_pair 3 5)`); its constructor and field values are read through the AST
    introspection surface shared by all AstRefs — `decl()` (the constructor
    func_decl), `num_args()`, `arg(i)` and `children()`. That mirrors z3py's
    `m[p].arg(0)` for reading a field of a concrete datatype value.
    """


# ---------------------------------------------------------------------------
# Sort helpers for arithmetic mixing (Int + Real -> Real, like z3py)
# ---------------------------------------------------------------------------

def _result_arith_sort(a, b, ctx):
    if a.kind == "Real" or b.kind == "Real":
        return _real_sort(ctx)
    if a.kind == "Int" and b.kind == "Int":
        return _int_sort(ctx)
    if a.kind == b.kind:
        return a
    raise NotImplementedError(
        f"mixed-sort arithmetic between {a} and {b} is not supported in this slice"
    )


def _to_real(expr, ctx):
    """Wrap an Int-sorted expression in ToReal (Z3_mk_int2real)."""
    ast = lib.Z3_mk_int2real(ctx.ref, expr.ast)
    if ast == 0:
        ctx.check_error("int2real coercion")
        raise AyZ3Exception("AY returned the null AST for an int2real coercion")
    return _wrap(ast, _real_sort(ctx), ctx)


def _promote_arith(lhs, rhs, ctx):
    """Apply z3py's Int/Real mixing rule to two already-AstRef operands.

    z3py auto-promotes a mixed Int/Real term by inserting `ToReal` on the Int
    operand, yielding a Real-sorted result (exactly what `Z3_mk_int2real`
    produces). Same-sort pairs (Int/Int, Real/Real, BitVec/BitVec, ...) are
    returned unchanged. Returns the (possibly coerced) (lhs, rhs) pair.
    """
    lk, rk = lhs.sort_ref.kind, rhs.sort_ref.kind
    if lk == rk:
        return lhs, rhs
    if lk == "Int" and rk == "Real":
        return _to_real(lhs, ctx), rhs
    if lk == "Real" and rk == "Int":
        return lhs, _to_real(rhs, ctx)
    return lhs, rhs


def _coerce(value, hint_sort, ctx):
    """Turn a Python literal into an AstRef matching `hint_sort` where possible."""
    if isinstance(value, AstRef):
        return value
    if isinstance(value, bool):
        return BoolVal(value, ctx)
    if isinstance(value, numbers.Integral):
        if hint_sort.kind == "BitVec":
            return BitVecVal(int(value), hint_sort.bv_size, ctx)
        if hint_sort.kind == "Real":
            return RealVal(int(value), ctx)
        if hint_sort.kind == "FloatingPoint":
            from .fp import FPVal
            return FPVal(int(value), hint_sort, ctx=ctx)
        return IntVal(int(value), ctx)
    if isinstance(value, float):
        if hint_sort.kind == "FloatingPoint":
            from .fp import FPVal
            return FPVal(value, hint_sort, ctx=ctx)
        return RealVal(value, ctx)
    import decimal as _decimal
    if isinstance(value, (numbers.Rational, _decimal.Decimal)):
        # A non-integer exact rational (Fraction(1, 3), Decimal("2.5")). z3py
        # coerces these into a Real; AY builds the exact numeral via RealVal.
        # Into Int/BitVec there is no exact value, so error (matching z3, and
        # never a silently-truncated wrong value).
        if hint_sort.kind == "Real":
            return RealVal(value, ctx)
        if hint_sort.kind == "FloatingPoint":
            from .fp import FPVal
            return FPVal(float(value), hint_sort, ctx=ctx)
        raise NotImplementedError(
            f"cannot coerce non-integer {value!r} into sort {hint_sort}"
        )
    if isinstance(value, str):
        if hint_sort.kind == "String":
            return StringVal(value, ctx)
        if hint_sort.kind in ("Int", "Real"):
            return (
                RealVal(value, ctx)
                if hint_sort.kind == "Real"
                else IntVal(int(value), ctx)
            )
    raise NotImplementedError(
        f"cannot coerce Python value {value!r} into sort {hint_sort}"
    )


# ---------------------------------------------------------------------------
# Constants / variables
# ---------------------------------------------------------------------------

def _sort_signature(sort):
    """A hashable signature of a SortRef for collision detection.

    Two consts of the same name must agree on this signature; AY hash-conses a
    const purely by NAME, so re-declaring `x` with a different sort silently
    returns the FIRST sort's handle -- a type-confusion hazard that crashes the
    Rust core when the mis-sorted handle is later used in an `=`.
    """
    if sort.kind == "BitVec":
        return ("BitVec", sort.bv_size)
    if sort.kind == "Array":
        return ("Array", _sort_signature(sort.domain_sort),
                _sort_signature(sort.range_sort))
    if sort.kind == "FiniteSet":
        return ("FiniteSet", _sort_signature(sort.basis_sort))
    if sort.kind == "Datatype":
        # Distinguish datatypes by name: two different datatypes are different
        # sorts even though both report kind "Datatype".
        name = getattr(sort, "recipe", None)
        name = name.name if name is not None else getattr(sort, "_dt_name", "")
        return ("Datatype", name)
    if sort.kind == "FloatingPoint":
        return ("FloatingPoint", sort.ebits(), sort.sbits())
    return (sort.kind,)


def _mk_const(name, sort, ctx):
    # SOUNDNESS GUARD: AY interns a const by name within a context, so asking for
    # the same name at a DIFFERENT sort hands back the original (wrong-sorted)
    # handle. Using that handle in a comparison then panics inside the Rust core
    # (it survives only via FFI catch-unwind, returning a null AST). Fail CLOSED
    # to a clear Python error instead of returning a type-confused expression.
    sig = _sort_signature(sort)
    prev = ctx._const_sorts.get(name)
    if prev is not None and prev != sig:
        raise AyZ3Exception(
            f"constant {name!r} was already declared with sort {prev} in this "
            f"context; cannot redeclare it with sort {sig}. AY interns a const "
            f"by name, so a same-name/different-sort redeclaration would alias "
            f"the original sort's handle. Use a distinct name or a fresh Context."
        )
    sym = lib.Z3_mk_string_symbol(ctx.ref, name.encode())
    ast = lib.Z3_mk_const(ctx.ref, sym, sort.handle)
    expr = _wrap(ast, sort, ctx)
    expr.decl_name = name
    ctx._const_sorts[name] = sig
    # Record name+sort so this const can be rebuilt by name in another context
    # (its AST handle does not carry its name through AY's C ABI).
    _register_const(expr, name)
    return expr


def Int(name, ctx=None):
    ctx = ctx or _current_ctx()
    return _mk_const(name, _int_sort(ctx), ctx)


def Real(name, ctx=None):
    ctx = ctx or _current_ctx()
    return _mk_const(name, _real_sort(ctx), ctx)


def Bool(name, ctx=None):
    ctx = ctx or _current_ctx()
    return _mk_const(name, _bool_sort(ctx), ctx)


def BitVec(name, bits, ctx=None):
    ctx = ctx or _current_ctx()
    return _mk_const(name, _bv_sort(bits, ctx), ctx)


def Const(name, sort):
    """A constant of an arbitrary SortRef (z3py's Const)."""
    return _mk_const(name, sort, sort.ctx)


def Array(name, dom, rng, ctx=None):
    """Declare an array constant of sort Array(dom, rng)."""
    ctx = ctx or _current_ctx()
    return _mk_const(name, _array_sort(dom, rng, ctx), ctx)


def String(name, ctx=None):
    """Declare a string constant."""
    ctx = ctx or _current_ctx()
    return _mk_const(name, _string_sort(ctx), ctx)


# ---------------------------------------------------------------------------
# Plural constructors (z3py Ints/Bools/Reals/BitVecs/Consts/Strings)
# ---------------------------------------------------------------------------
#
# Each takes a `names` argument that is either a whitespace-separated string
# (`Ints('x y z')`) or an iterable of names, and returns a LIST of constants —
# exactly like z3py, so `x, y = Ints('x y')` unpacks. These are the line-one
# idiom of most z3 tutorials.

def _split_names(names):
    """z3py name-list handling: split a string on whitespace; else pass through."""
    if isinstance(names, str):
        return names.split()
    return list(names)


def Ints(names, ctx=None):
    """Declare several Int constants at once (z3py Ints)."""
    ctx = ctx or _current_ctx()
    return [Int(name, ctx) for name in _split_names(names)]


def Reals(names, ctx=None):
    """Declare several Real constants at once (z3py Reals)."""
    ctx = ctx or _current_ctx()
    return [Real(name, ctx) for name in _split_names(names)]


def Bools(names, ctx=None):
    """Declare several Bool constants at once (z3py Bools)."""
    ctx = ctx or _current_ctx()
    return [Bool(name, ctx) for name in _split_names(names)]


def BitVecs(names, bv, ctx=None):
    """Declare several BitVec constants of width `bv` at once (z3py BitVecs)."""
    ctx = ctx or _current_ctx()
    return [BitVec(name, bv, ctx) for name in _split_names(names)]


def Consts(names, sort):
    """Declare several constants of an arbitrary sort at once (z3py Consts)."""
    return [Const(name, sort) for name in _split_names(names)]


def Strings(names, ctx=None):
    """Declare several String constants at once (z3py Strings)."""
    ctx = ctx or _current_ctx()
    return [String(name, ctx) for name in _split_names(names)]


# ---------------------------------------------------------------------------
# Version (z3py get_version / get_version_string)
# ---------------------------------------------------------------------------

def get_version():
    """The engine's Z3-compatibility version as `(major, minor, build, revision)`.

    Reads the REAL `Z3_get_version` the FFI reports (AY's Z3 API-compatibility
    version) — never a fabricated tuple. Mirrors z3py's `get_version()`.
    """
    major = ctypes.c_uint(0)
    minor = ctypes.c_uint(0)
    build = ctypes.c_uint(0)
    revision = ctypes.c_uint(0)
    lib.Z3_get_version(
        ctypes.byref(major), ctypes.byref(minor),
        ctypes.byref(build), ctypes.byref(revision),
    )
    return (major.value, minor.value, build.value, revision.value)


def get_version_string():
    """The engine's Z3-compatibility version as `"major.minor.build"` (z3py shape)."""
    major, minor, build, _revision = get_version()
    return f"{major}.{minor}.{build}"


# ---------------------------------------------------------------------------
# Literals
# ---------------------------------------------------------------------------

def IntVal(v, ctx=None):
    ctx = ctx or _current_ctx()
    sort = _int_sort(ctx)
    # A non-integer exact rational (Fraction(1, 3)) has no Int value; z3 raises
    # rather than accepting it. Match that instead of `str(int(v))`, which
    # SILENTLY truncated Fraction(1, 3) to 0 (a wrong value). Floats still
    # truncate (IntVal(2.9) -> 2), matching z3py.
    if (
        isinstance(v, numbers.Rational)
        and not isinstance(v, numbers.Integral)
        and v.denominator != 1
    ):
        raise NotImplementedError(
            f"IntVal: {v!r} is not an integer (use RealVal for a rational value)"
        )
    ast = lib.Z3_mk_numeral(ctx.ref, str(int(v)).encode(), sort.handle)
    return _as_numref(_wrap(ast, sort, ctx))


def RealVal(v, ctx=None):
    ctx = ctx or _current_ctx()
    sort = _real_sort(ctx)
    if isinstance(v, str):
        # AY's Z3_mk_numeral accepts integer and `n/d` rational text but REJECTS
        # decimal / scientific spellings ("2.5", "-0.5", "1e2") that z3py's
        # RealVal takes. Normalize any string Fraction can parse to exact `n/d`
        # (strings are exact, so no limit_denominator); fall back to the raw
        # text for forms Fraction can't handle (Z3_mk_numeral then accepts or
        # rejects them exactly as before).
        from fractions import Fraction
        try:
            fr = Fraction(v)
            text = f"{fr.numerator}/{fr.denominator}"
        except (ValueError, ZeroDivisionError):
            text = v
    elif isinstance(v, float):
        from fractions import Fraction
        # Match z3py's semantics: z3py stringifies the float (repr) and Z3
        # parses it as a DECIMAL numeral, so RealVal(0.1) is exactly 1/10.
        # Fraction(repr(v)) reproduces that exactly (it parses decimal and
        # scientific notation, e.g. 1e-13 -> 1/10**13) and, unlike the old
        # limit_denominator(10**12) approximation, never silently collapses a
        # small-magnitude float to a wrong value (1e-13 used to become 0).
        fr = Fraction(repr(v))
        text = f"{fr.numerator}/{fr.denominator}"
    elif isinstance(v, numbers.Integral):
        text = str(int(v))
    else:
        # Fraction / Decimal / any exact rational. Previously this hit
        # `str(int(v))`, which SILENTLY truncated Fraction(1, 3) to 0 (a wrong
        # value). Convert supported numeric types to an exact n/d. Do not fall
        # back to `int(v)`: an object with only `__int__` could otherwise be
        # silently truncated and accepted as a different real value.
        from fractions import Fraction
        try:
            fr = Fraction(v)
            text = f"{fr.numerator}/{fr.denominator}"
        except (ValueError, TypeError, ZeroDivisionError) as exc:
            raise AyZ3Exception(f"RealVal: unsupported numeric value {v!r}") from exc
    ast = lib.Z3_mk_numeral(ctx.ref, text.encode(), sort.handle)
    return _as_numref(_wrap(ast, sort, ctx))


def BoolVal(b, ctx=None):
    ctx = ctx or _current_ctx()
    sort = _bool_sort(ctx)
    ast = lib.Z3_mk_true(ctx.ref) if b else lib.Z3_mk_false(ctx.ref)
    return _wrap(ast, sort, ctx)


def BitVecVal(v, bits, ctx=None):
    ctx = ctx or _current_ctx()
    sort = _bv_sort(bits, ctx)
    ast = lib.Z3_mk_numeral(ctx.ref, str(int(v)).encode(), sort.handle)
    return _as_numref(_wrap(ast, sort, ctx))


def StringVal(s, ctx=None):
    """A string literal.

    AY treats the given bytes as the literal content (no SMT-LIB escape
    parsing). For ASCII content this matches z3py exactly.
    """
    ctx = ctx or _current_ctx()
    sort = _string_sort(ctx)
    ast = lib.Z3_mk_string(ctx.ref, str(s).encode())
    return _wrap(ast, sort, ctx)


# ---------------------------------------------------------------------------
# Boolean connectives
# ---------------------------------------------------------------------------

def _bool_args(args, ctx):
    coerced = []
    for a in args:
        if isinstance(a, bool):
            coerced.append(BoolVal(a, ctx))
        elif isinstance(a, BoolRef):
            coerced.append(a)
        else:
            raise NotImplementedError(f"expected Bool argument, got {a!r}")
    return coerced


def _flatten(args):
    if len(args) == 1 and isinstance(args[0], (list, tuple)):
        return tuple(args[0])
    return args


def _ctx_of(args, fallback=None):
    for a in args:
        if isinstance(a, AstRef):
            return a.ctx
    return fallback or _current_ctx()


def And(*args):
    args = _flatten(args)
    ctx = _ctx_of(args)
    coerced = _bool_args(args, ctx)
    if coerced:
        _same_ctx(*coerced)
    n, arr = _as_ast_array(coerced)
    return BoolRef(lib.Z3_mk_and(ctx.ref, n, arr), _bool_sort(ctx), ctx)


def Or(*args):
    args = _flatten(args)
    ctx = _ctx_of(args)
    coerced = _bool_args(args, ctx)
    if coerced:
        _same_ctx(*coerced)
    n, arr = _as_ast_array(coerced)
    return BoolRef(lib.Z3_mk_or(ctx.ref, n, arr), _bool_sort(ctx), ctx)


def Not(a):
    ctx = _ctx_of([a])
    a = _bool_args([a], ctx)[0]
    return BoolRef(lib.Z3_mk_not(ctx.ref, a.ast), _bool_sort(ctx), ctx)


def Implies(a, b):
    ctx = _ctx_of([a, b])
    a, b = _bool_args([a, b], ctx)
    _same_ctx(a, b)
    return BoolRef(lib.Z3_mk_implies(ctx.ref, a.ast, b.ast), _bool_sort(ctx), ctx)


def Xor(a, b):
    ctx = _ctx_of([a, b])
    a, b = _bool_args([a, b], ctx)
    _same_ctx(a, b)
    return BoolRef(lib.Z3_mk_xor(ctx.ref, a.ast, b.ast), _bool_sort(ctx), ctx)


# ---------------------------------------------------------------------------
# Pseudo-boolean / cardinality constraints (z3py AtMost/AtLeast/PbLe/PbGe/PbEq)
# ---------------------------------------------------------------------------


def _pb_split_bound(args, k):
    """Split cardinality arguments into (literals, integer-bound).

    z3py takes the bound as the trailing positional argument
    (``AtMost(a, b, c, 2)``); we additionally accept an explicit ``k=`` keyword
    (``AtMost(a, b, c, k=2)``) — a harmless superset of the z3py surface.
    """
    items = list(_flatten(args))
    if k is None:
        if not items:
            raise AyZ3Exception(
                "AtMost/AtLeast requires a bound k as the last argument"
            )
        k = items.pop()
    if isinstance(k, bool) or not isinstance(k, numbers.Integral):
        raise AyZ3Exception(f"cardinality bound k must be an integer, got {k!r}")
    k = int(k)
    # The C ABI takes the bound as an UNSIGNED 32-bit int; an out-of-range
    # Python int would silently wrap in ctypes (e.g. -1 -> 4294967295, turning
    # AtMost(..., -1) into a trivially-true constraint). Fail loudly instead.
    if not 0 <= k < 2**32:
        raise AyZ3Exception(
            f"cardinality bound k must fit in an unsigned 32-bit int "
            f"(0 <= k < 2**32), got {k}"
        )
    return items, k


def AtMost(*args, k=None):
    """At-most Pseudo-Boolean constraint: at most ``k`` of the Bool arguments hold.

    >>> a, b, c = Bools('a b c')
    >>> f = AtMost(a, b, c, 2)   # z3py form: bound is the last positional arg
    """
    lits, bound = _pb_split_bound(args, k)
    ctx = _ctx_of(lits)
    coerced = _bool_args(lits, ctx)
    if coerced:
        _same_ctx(*coerced)
    n, arr = _as_ast_array(coerced)
    return BoolRef(lib.Z3_mk_atmost(ctx.ref, n, arr, bound), _bool_sort(ctx), ctx)


def AtLeast(*args, k=None):
    """At-least Pseudo-Boolean constraint: at least ``k`` of the Bool arguments hold.

    >>> a, b, c = Bools('a b c')
    >>> f = AtLeast(a, b, c, 2)
    """
    lits, bound = _pb_split_bound(args, k)
    ctx = _ctx_of(lits)
    coerced = _bool_args(lits, ctx)
    if coerced:
        _same_ctx(*coerced)
    n, arr = _as_ast_array(coerced)
    return BoolRef(lib.Z3_mk_atleast(ctx.ref, n, arr, bound), _bool_sort(ctx), ctx)


def _mk_pb(fn, arg_coeffs, k):
    """Build a weighted pseudo-boolean constraint ``Σ cᵢ·litᵢ  (⋈)  k``.

    ``arg_coeffs`` is a sequence of ``(Bool, integer-coefficient)`` pairs and
    ``k`` is the integer threshold (matches z3py's ``PbLe(((a,1),(b,3)), 3)``).
    """
    lits = []
    coeffs = []
    for pair in arg_coeffs:
        try:
            lit, coeff = pair
        except (TypeError, ValueError):
            raise AyZ3Exception(
                f"PB argument must be a (literal, coefficient) pair, got {pair!r}"
            )
        if isinstance(coeff, bool) or not isinstance(coeff, numbers.Integral):
            raise AyZ3Exception(f"PB coefficient must be an integer, got {coeff!r}")
        coeff = int(coeff)
        # The C ABI takes coefficients as SIGNED 32-bit ints; an out-of-range
        # value would silently wrap in ctypes (e.g. 2**31 -> -2**31), building
        # a DIFFERENT constraint than the user wrote. Fail loudly instead.
        if not -(2**31) <= coeff < 2**31:
            raise AyZ3Exception(
                f"PB coefficient must fit in a signed 32-bit int "
                f"(-2**31 <= c < 2**31), got {coeff}"
            )
        lits.append(lit)
        coeffs.append(coeff)
    if isinstance(k, bool) or not isinstance(k, numbers.Integral):
        raise AyZ3Exception(f"PB threshold k must be an integer, got {k!r}")
    k = int(k)
    if not -(2**31) <= k < 2**31:
        raise AyZ3Exception(
            f"PB threshold k must fit in a signed 32-bit int "
            f"(-2**31 <= k < 2**31), got {k}"
        )
    ctx = _ctx_of(lits)
    coerced = _bool_args(lits, ctx)
    if coerced:
        _same_ctx(*coerced)
    n, arr = _as_ast_array(coerced)
    carr = (ctypes.c_int * n)(*coeffs)
    return BoolRef(fn(ctx.ref, n, arr, carr, int(k)), _bool_sort(ctx), ctx)


def PbLe(args, k):
    """Weighted pseudo-boolean ``<= k`` constraint.

    >>> a, b, c = Bools('a b c')
    >>> f = PbLe(((a, 1), (b, 3), (c, 2)), 3)
    """
    return _mk_pb(lib.Z3_mk_pble, args, k)


def PbGe(args, k):
    """Weighted pseudo-boolean ``>= k`` constraint.

    >>> a, b, c = Bools('a b c')
    >>> f = PbGe(((a, 1), (b, 3), (c, 2)), 3)
    """
    return _mk_pb(lib.Z3_mk_pbge, args, k)


def PbEq(args, k, ctx=None):
    """Weighted pseudo-boolean ``= k`` constraint.

    >>> a, b, c = Bools('a b c')
    >>> f = PbEq(((a, 1), (b, 3), (c, 2)), 3)
    """
    return _mk_pb(lib.Z3_mk_pbeq, args, k)


def If(cond, t, e):
    ctx = _ctx_of([cond, t, e])
    cond = _bool_args([cond], ctx)[0]
    if not isinstance(t, AstRef):
        hint = e.sort_ref if isinstance(e, AstRef) else _int_sort(ctx)
        t = _coerce(t, hint, ctx)
    if not isinstance(e, AstRef):
        e = _coerce(e, t.sort_ref, ctx)
    _same_ctx(cond, t, e)
    # z3py promotes a mixed Int/Real ite: the Int branch is wrapped in ToReal
    # and the result is Real-sorted.
    t, e = _promote_arith(t, e, ctx)
    return _wrap(lib.Z3_mk_ite(ctx.ref, cond.ast, t.ast, e.ast), t.sort_ref, ctx)


def Distinct(*args):
    args = _flatten(args)
    ctx = _ctx_of(args)
    items = list(args)
    if items:
        _same_ctx(*[x for x in items if isinstance(x, AstRef)])
    n, arr = _as_ast_array(items)
    result = BoolRef(lib.Z3_mk_distinct(ctx.ref, n, arr), _bool_sort(ctx), ctx)
    # AY's core EAGER-EXPANDS distinct into a pairwise `(and (not (= ...)) ...)`,
    # so the built node's decl kind is `and`, not `distinct`. z3py keeps a real
    # distinct node whose `decl().name() == 'distinct'`, `is_distinct(...)` is
    # True and whose children are the arguments. We record the arguments on the
    # wrapper (a faithful reconstruction of what the user built, NOT a fabricated
    # value) so the introspection surface (decl/is_distinct/num_args/arg/children)
    # matches z3py; the underlying assertion is the logically-equivalent expansion.
    result._distinct_args = [x for x in items if isinstance(x, AstRef)]
    return result


# ---------------------------------------------------------------------------
# Arithmetic aggregates (z3py Sum / Product over a list of terms)
# ---------------------------------------------------------------------------

def Sum(*args):
    """Sum a list (or varargs) of arithmetic/bitvector terms (z3py Sum).

    `Sum([a, b, c])` and `Sum(a, b, c)` both work, mirroring z3py. Python int
    literals are coerced against the first AstRef's sort.
    """
    args = _flatten(args)
    items = list(args)
    if not items:
        raise AyZ3Exception("Sum needs at least one argument")
    ctx = _ctx_of(items)
    hint = next((a.sort_ref for a in items if isinstance(a, AstRef)), _int_sort(ctx))
    acc = _coerce(items[0], hint, ctx)
    for x in items[1:]:
        acc = acc + x
    return acc


def Product(*args):
    """Multiply a list (or varargs) of arithmetic/bitvector terms (z3py Product)."""
    args = _flatten(args)
    items = list(args)
    if not items:
        raise AyZ3Exception("Product needs at least one argument")
    ctx = _ctx_of(items)
    hint = next((a.sort_ref for a in items if isinstance(a, AstRef)), _int_sort(ctx))
    acc = _coerce(items[0], hint, ctx)
    for x in items[1:]:
        acc = acc * x
    return acc


# ---------------------------------------------------------------------------
# Unsigned bitvector comparisons (z3py free functions)
# ---------------------------------------------------------------------------

def _bv_ucmp(a, b, mk):
    if not isinstance(a, BitVecRef):
        raise NotImplementedError("unsigned BV comparison needs a BitVec lhs")
    b = _coerce(b, a.sort_ref, a.ctx)
    ctx = _same_ctx(a, b)
    return BoolRef(mk(ctx.ref, a.ast, b.ast), _bool_sort(ctx), ctx)


def ULT(a, b):
    return _bv_ucmp(a, b, lib.Z3_mk_bvult)


def ULE(a, b):
    return _bv_ucmp(a, b, lib.Z3_mk_bvule)


def UGT(a, b):
    return _bv_ucmp(a, b, lib.Z3_mk_bvugt)


def UGE(a, b):
    return _bv_ucmp(a, b, lib.Z3_mk_bvuge)


# ---------------------------------------------------------------------------
# Bitvector operations exposed as z3py free functions (B-10)
# ---------------------------------------------------------------------------

def _bv_coerce_pair(a, b, name):
    """Coerce (a, b) to a common BitVec sort inferred from whichever is a BV.

    Mirrors z3py's `_coerce_exprs` for bitvectors: at least one operand must be
    a BitVecRef so the width is known; a Python int / same-width value on the
    other side is coerced to that sort. Returns (a, b, ctx).
    """
    bv = a if isinstance(a, BitVecRef) else (b if isinstance(b, BitVecRef) else None)
    if bv is None:
        raise NotImplementedError(f"{name} needs at least one BitVec operand")
    ctx = bv.ctx
    a = _coerce(a, bv.sort_ref, ctx)
    b = _coerce(b, bv.sort_ref, ctx)
    _same_ctx(a, b)
    return a, b, ctx


def _bv_free_bin(a, b, mk, name):
    a, b, ctx = _bv_coerce_pair(a, b, name)
    return _wrap(mk(ctx.ref, a.ast, b.ast), a.sort_ref, ctx)


def UDiv(a, b):
    """Unsigned bitvector division (z3py UDiv -> bvudiv)."""
    return _bv_free_bin(a, b, lib.Z3_mk_bvudiv, "UDiv")


def URem(a, b):
    """Unsigned bitvector remainder (z3py URem -> bvurem)."""
    return _bv_free_bin(a, b, lib.Z3_mk_bvurem, "URem")


def SRem(a, b):
    """Signed bitvector remainder, sign follows the dividend (z3py SRem -> bvsrem)."""
    return _bv_free_bin(a, b, lib.Z3_mk_bvsrem, "SRem")


def LShR(a, b):
    """Logical (unsigned) shift right (z3py LShR -> bvlshr)."""
    return _bv_free_bin(a, b, lib.Z3_mk_bvlshr, "LShR")


# z3py reaches signed division / signed mod / arithmetic shift right through the
# operators `x / y` (bvsdiv), `x % y` (bvsmod) and `x >> y` (bvashr) — which this
# binding wires on BitVecRef exactly as z3py does. SMod / SDiv / AShR are offered
# additionally as explicitly-named free functions (same builders, no divergence)
# so the full signed/unsigned BV family is reachable by name as well.
def SMod(a, b):
    """Signed bitvector modulo, sign follows the divisor (bvsmod). Same as `a % b`."""
    return _bv_free_bin(a, b, lib.Z3_mk_bvsmod, "SMod")


def SDiv(a, b):
    """Signed bitvector division (bvsdiv). Same as `a / b`."""
    return _bv_free_bin(a, b, lib.Z3_mk_bvsdiv, "SDiv")


def AShR(a, b):
    """Arithmetic (signed) shift right (bvashr). Same as `a >> b`."""
    return _bv_free_bin(a, b, lib.Z3_mk_bvashr, "AShR")


def _as_bv(a, name):
    if not isinstance(a, BitVecRef):
        raise NotImplementedError(f"{name} needs a BitVec argument")
    return a


def SignExt(n, a):
    """Sign-extend `a` by `n` bits (z3py SignExt -> (_ sign_extend n))."""
    a = _as_bv(a, "SignExt")
    ctx = a.ctx
    return _wrap(lib.Z3_mk_sign_ext(ctx.ref, int(n), a.ast),
                 _bv_sort(a.size + int(n), ctx), ctx)


def ZeroExt(n, a):
    """Zero-extend `a` by `n` bits (z3py ZeroExt -> (_ zero_extend n))."""
    a = _as_bv(a, "ZeroExt")
    ctx = a.ctx
    return _wrap(lib.Z3_mk_zero_ext(ctx.ref, int(n), a.ast),
                 _bv_sort(a.size + int(n), ctx), ctx)


def RepeatBitVec(n, a):
    """Concatenate `n` copies of `a` (z3py RepeatBitVec -> (_ repeat n))."""
    a = _as_bv(a, "RepeatBitVec")
    ctx = a.ctx
    return _wrap(lib.Z3_mk_repeat(ctx.ref, int(n), a.ast),
                 _bv_sort(a.size * int(n), ctx), ctx)


def _rotate_amount(b, name):
    """A constant rotation amount from a Python int or a concrete BV numeral.

    AY's core provides only constant-amount bit rotation, so a symbolic rotation
    amount is genuinely unsupported (honest NotImplementedError rather than a
    fabricated encoding).
    """
    if isinstance(b, bool):
        return int(b)
    if isinstance(b, numbers.Integral):
        return int(b)
    if isinstance(b, BitVecRef):
        try:
            return b.as_long()
        except AyZ3Exception:
            pass
    raise NotImplementedError(
        f"{name} with a symbolic (non-constant) rotation amount is not supported: "
        "AY's core provides only constant-amount bit rotation")


def RotateLeft(a, b):
    """Rotate `a` left by `b` bits (z3py RotateLeft).

    z3py always builds `ext_rotate_left`; AY emits the (semantically identical)
    parametric `(_ rotate_left k)` for a constant amount `k` — a documented,
    sound printing divergence. `b` must be a constant (see `_rotate_amount`).
    """
    a = _as_bv(a, "RotateLeft")
    ctx = a.ctx
    return _wrap(lib.Z3_mk_rotate_left(ctx.ref, _rotate_amount(b, "RotateLeft"), a.ast),
                 a.sort_ref, ctx)


def RotateRight(a, b):
    """Rotate `a` right by `b` bits (z3py RotateRight). See `RotateLeft`."""
    a = _as_bv(a, "RotateRight")
    ctx = a.ctx
    return _wrap(lib.Z3_mk_rotate_right(ctx.ref, _rotate_amount(b, "RotateRight"), a.ast),
                 a.sort_ref, ctx)


def BV2Int(a, is_signed=False):
    """Convert a bitvector to an Int (z3py BV2Int; unsigned unless is_signed)."""
    a = _as_bv(a, "BV2Int")
    ctx = a.ctx
    return _wrap(lib.Z3_mk_bv2int(ctx.ref, a.ast, bool(is_signed)),
                 _int_sort(ctx), ctx)


def Int2BV(a, num_bits):
    """Convert an Int expression to a `num_bits`-wide bitvector (z3py Int2BV)."""
    ctx = a.ctx if isinstance(a, AstRef) else _current_ctx()
    a = _coerce(a, _int_sort(ctx), ctx)
    return _wrap(lib.Z3_mk_int2bv(ctx.ref, int(num_bits), a.ast),
                 _bv_sort(int(num_bits), ctx), ctx)


def BVRedAnd(a):
    """AND-reduce a bitvector to a 1-bit result (z3py BVRedAnd -> bvredand)."""
    a = _as_bv(a, "BVRedAnd")
    ctx = a.ctx
    return _wrap(lib.Z3_mk_bvredand(ctx.ref, a.ast), _bv_sort(1, ctx), ctx)


def BVRedOr(a):
    """OR-reduce a bitvector to a 1-bit result (z3py BVRedOr -> bvredor)."""
    a = _as_bv(a, "BVRedOr")
    ctx = a.ctx
    return _wrap(lib.Z3_mk_bvredor(ctx.ref, a.ast), _bv_sort(1, ctx), ctx)


# --- overflow / underflow predicates (Bool-sorted; signatures match z3py) ---

def BVAddNoOverflow(a, b, signed):
    """No-overflow predicate for bitvector addition (z3py BVAddNoOverflow)."""
    a, b, ctx = _bv_coerce_pair(a, b, "BVAddNoOverflow")
    return BoolRef(lib.Z3_mk_bvadd_no_overflow(ctx.ref, a.ast, b.ast, bool(signed)),
                   _bool_sort(ctx), ctx)


def BVAddNoUnderflow(a, b):
    """No-underflow predicate for signed bitvector addition (z3py BVAddNoUnderflow)."""
    a, b, ctx = _bv_coerce_pair(a, b, "BVAddNoUnderflow")
    return BoolRef(lib.Z3_mk_bvadd_no_underflow(ctx.ref, a.ast, b.ast),
                   _bool_sort(ctx), ctx)


def BVSubNoOverflow(a, b):
    """No-overflow predicate for signed bitvector subtraction (z3py BVSubNoOverflow)."""
    a, b, ctx = _bv_coerce_pair(a, b, "BVSubNoOverflow")
    return BoolRef(lib.Z3_mk_bvsub_no_overflow(ctx.ref, a.ast, b.ast),
                   _bool_sort(ctx), ctx)


def BVSubNoUnderflow(a, b, signed):
    """No-underflow predicate for bitvector subtraction (z3py BVSubNoUnderflow)."""
    a, b, ctx = _bv_coerce_pair(a, b, "BVSubNoUnderflow")
    return BoolRef(lib.Z3_mk_bvsub_no_underflow(ctx.ref, a.ast, b.ast, bool(signed)),
                   _bool_sort(ctx), ctx)


def BVMulNoOverflow(a, b, signed):
    """No-overflow predicate for bitvector multiplication (z3py BVMulNoOverflow)."""
    a, b, ctx = _bv_coerce_pair(a, b, "BVMulNoOverflow")
    return BoolRef(lib.Z3_mk_bvmul_no_overflow(ctx.ref, a.ast, b.ast, bool(signed)),
                   _bool_sort(ctx), ctx)


def BVMulNoUnderflow(a, b):
    """No-underflow predicate for signed bitvector multiplication (z3py BVMulNoUnderflow)."""
    a, b, ctx = _bv_coerce_pair(a, b, "BVMulNoUnderflow")
    return BoolRef(lib.Z3_mk_bvmul_no_underflow(ctx.ref, a.ast, b.ast),
                   _bool_sort(ctx), ctx)


def BVSDivNoOverflow(a, b):
    """No-overflow predicate for signed bitvector division (z3py BVSDivNoOverflow)."""
    a, b, ctx = _bv_coerce_pair(a, b, "BVSDivNoOverflow")
    return BoolRef(lib.Z3_mk_bvsdiv_no_overflow(ctx.ref, a.ast, b.ast),
                   _bool_sort(ctx), ctx)


# ---------------------------------------------------------------------------
# Arrays  (Select / Store / K, backed by Z3_mk_select/store/const_array)
# ---------------------------------------------------------------------------

def Select(a, i):
    """Read the value of array `a` at index `i` (z3py Select; also a[i])."""
    if isinstance(a, FiniteSetRef):
        raise AyZ3Exception(
            "sort mismatch: Select expects a legacy Array, not a FiniteSet"
        )
    if not isinstance(a, ArrayRef):
        raise NotImplementedError("Select expects an Array as its first argument")
    i = _coerce(i, a.sort_ref.domain_sort, a.ctx)
    ctx = _same_ctx(a, i)
    ast = lib.Z3_mk_select(ctx.ref, a.ast, i.ast)
    return _wrap(ast, a.sort_ref.range_sort, ctx)


def Store(a, i, v):
    """Return array `a` with index `i` updated to value `v`."""
    if not isinstance(a, ArrayRef):
        raise NotImplementedError("Store expects an Array as its first argument")
    i = _coerce(i, a.sort_ref.domain_sort, a.ctx)
    v = _coerce(v, a.sort_ref.range_sort, a.ctx)
    ctx = _same_ctx(a, i, v)
    ast = lib.Z3_mk_store(ctx.ref, a.ast, i.ast, v.ast)
    return _wrap(ast, a.sort_ref, ctx)


def K(dom, v):
    """The constant array over domain sort `dom` mapping everything to `v`."""
    if not isinstance(dom, SortRef):
        raise NotImplementedError("K expects a SortRef domain")
    ctx = dom.ctx
    v = _coerce(v, _value_hint_sort(v, ctx), ctx)
    if v.ctx is not ctx:
        raise AyZ3Exception("K value and domain sort are from different contexts")
    rng = v.sort_ref
    ast = lib.Z3_mk_const_array(ctx.ref, dom.handle, v.ast)
    return _wrap(ast, _array_sort(dom, rng, ctx), ctx)


def _value_hint_sort(v, ctx):
    """Best-effort sort hint for a Python value used as an array's K value."""
    if isinstance(v, AstRef):
        return v.sort_ref
    if isinstance(v, bool):
        return _bool_sort(ctx)
    if isinstance(v, numbers.Integral):
        return _int_sort(ctx)
    if isinstance(v, float):
        return _real_sort(ctx)
    if isinstance(v, str):
        return _string_sort(ctx)
    raise NotImplementedError(f"cannot infer a sort for K value {v!r}")


def Update(a, *args):
    """Return array `a` with an index updated to a value (z3py `Update`).

    `Update(a, i, v)` is `Store(a, i, v)`. For a MULTI-dimensional array (domain
    a tuple of sorts) z3py accepts `Update(a, i0, i1, ..., v)`; AY's arrays are
    single-domain, so only the 1-index form is supported (a genuinely
    multi-dimensional update raises honestly).
    """
    if not isinstance(a, ArrayRef):
        raise NotImplementedError("Update expects an Array as its first argument")
    if len(args) == 1 and isinstance(args[0], (list, tuple)):
        args = tuple(args[0])
    if len(args) != 2:
        raise NotImplementedError(
            "Update(a, i, v) is supported for single-domain arrays; AY does not "
            f"model multi-dimensional array update (got {len(args)} index/value args)"
        )
    return Store(a, args[0], args[1])


def _sorts_equal(s1, s2):
    """Structural SortRef equality (context-independent)."""
    if s1 is s2:
        return True
    if s1 is None or s2 is None:
        return False
    if s1.kind != s2.kind:
        return False
    if s1.kind == "BitVec":
        return s1.bv_size == s2.bv_size
    if s1.kind == "Array":
        return _sorts_equal(s1.domain_sort, s2.domain_sort) and _sorts_equal(
            s1.range_sort, s2.range_sort
        )
    if s1.kind == "Seq":
        return _sorts_equal(s1.basis_sort, s2.basis_sort)
    if s1.kind == "FiniteSet":
        return _sorts_equal(s1.basis_sort, s2.basis_sort)
    # Same-kind scalar sorts (Bool/Int/Real/String/...) are equal; named sorts
    # (Datatype/Uninterpreted subclasses) compare by name when available.
    n1, n2 = getattr(s1, "_name", None), getattr(s2, "_name", None)
    return n1 == n2


def Map(f, *args):
    """Return the array `map(f)(a0, a1, ...)` (z3py `Map`).

    Backed by AY's real `Z3_mk_map`: the term is `((_ map f) a0 ...)` with the
    eager select rewrite `Select(Map(f, a), i) == f(Select(a, i))`; selects
    over the map DECIDE; unsupported un-selected map-array equalities return
    `unknown`. All argument
    sorts are checked here (the binding is the sort gate): `f` must be a
    FuncDeclRef of arity `len(args) >= 1`, every arg an Array over one common
    index sort, and `args[i]`'s element sort must equal `f.domain(i)`.
    """
    if not isinstance(f, FuncDeclRef):
        raise NotImplementedError("Map expects a function declaration as its first argument")
    if getattr(f, "_is_rec", False):
        # A rec function's applications are decided by definition expansion;
        # AY's map term captures `f` by name as a plain UF symbol, which would
        # bypass the definition. Fail closed, honestly.
        raise NotImplementedError("Map over a recursive function is not supported by AY")
    if len(args) < 1:
        raise NotImplementedError("Map needs at least one array argument")
    if f.arity() != len(args):
        raise NotImplementedError(
            f"Map: function {f.name()} has arity {f.arity()}, got {len(args)} array(s)"
        )
    ctx = f.ctx
    # Cross-context guard: adopt every array into f's context BEFORE touching
    # the FFI — passing another context's u64 handle into Z3_mk_map would be
    # decoded against f.ctx's arena and silently alias a DIFFERENT term (a
    # wrong-verdict channel).
    args = tuple(_adopt(a, ctx) for a in args)
    idx_sort = None
    for i, a in enumerate(args):
        if not isinstance(a, ArrayRef):
            raise NotImplementedError("Map arguments must be arrays")
        if idx_sort is None:
            idx_sort = a.sort_ref.domain_sort
        elif not _sorts_equal(idx_sort, a.sort_ref.domain_sort):
            raise NotImplementedError(
                "Map: all arrays must share one index sort "
                f"({idx_sort} vs {a.sort_ref.domain_sort})"
            )
        if not _sorts_equal(a.sort_ref.range_sort, f.domain_sorts[i]):
            raise NotImplementedError(
                f"Map: array {i} has element sort {a.sort_ref.range_sort} but "
                f"{f.name()} expects {f.domain_sorts[i]}"
            )
    n, arr = _as_ast_array(args)
    ast = lib.Z3_mk_map(ctx.ref, f.handle, n, arr)
    ctx.check_error("Map")
    out = _wrap(ast, _array_sort(idx_sort, f.range_sort, ctx), ctx)
    # Register for the cross-context rebuild (see Context.__init__: the term
    # must be re-derived via Z3_mk_map in the destination, never rebuilt as a
    # plain UF application).
    ctx._map_meta[out.ast] = (f, args)
    return out


def Ext(a, b):
    """Return the extensionality index for arrays `a` and `b` (z3py `Ext`).

    Backed by AY's real `Z3_mk_array_ext`: a cached witness index `k` plus the
    background axiom `a != b => Select(a, k) != Select(b, k)` (re-asserted at
    every solve site), giving z3's extensionality semantics:
    `Select(a, Ext(a, b)) == Select(b, Ext(a, b))` implies `a == b`.
    Both arguments must be arrays of the same sort.
    """
    if not isinstance(a, ArrayRef) or not isinstance(b, ArrayRef):
        raise NotImplementedError("Ext expects two arrays")
    ctx = a.ctx
    # Cross-context guard (same aliasing hazard as Map).
    b = _adopt(b, ctx)
    if not _sorts_equal(a.sort_ref, b.sort_ref):
        raise NotImplementedError(
            f"Ext: array sorts differ ({a.sort_ref} vs {b.sort_ref})"
        )
    ast = lib.Z3_mk_array_ext(ctx.ref, a.ast, b.ast)
    ctx.check_error("Ext")
    out = _wrap(ast, a.sort_ref.domain_sort, ctx)
    # Register for the cross-context rebuild (see Context.__init__: the
    # witness must be RE-DERIVED via Z3_mk_array_ext in the destination so it
    # carries its own background axiom — never rebuilt as a bare const).
    ctx._ext_meta[out.ast] = (a, b)
    return out


def Unit(a):
    """Create a singleton sequence containing element `a` (z3py `Unit`).

    DIVERGENCE (documented, never faked): AY models the character/element sort of
    a String as `Int`, so `Z3_mk_seq_unit` yields a `(Seq Int)` whose reported
    sort conflates with `String` and triggers an engine-level sort-mismatch when
    compared with a real `String` term. Because that is unsafe (it can crash the
    engine rather than return a value), `Unit` raises NotImplementedError. Build a
    singleton string with `StringVal(...)` and concatenate with `Concat` instead.
    """
    raise NotImplementedError(
        "Unit(a) (singleton-sequence construction) is not safely supported: AY's "
        "String element sort is modeled as Int and the resulting (Seq Int) sort "
        "conflates with String, causing engine sort mismatches. Use StringVal / "
        "Concat for string construction."
    )


# ---------------------------------------------------------------------------
# Uninterpreted functions  (Function -> FuncDeclRef, applied via Z3_mk_app)
# ---------------------------------------------------------------------------

class FuncDeclRef:
    """A function declaration. Calling it builds an application term.

        f = Function('f', IntSort(), IntSort())
        f(x)          # -> an Int application term
    """

    def __init__(self, handle, name, domain_sorts, range_sort, ctx, kind=None):
        self.handle = handle               # Z3_func_decl (c_void_p)
        self._name = name
        self.domain_sorts = list(domain_sorts)
        self.range_sort = range_sort
        self.ctx = ctx
        # z3py FuncDeclRef.kind(). Declared functions (Function()) and model
        # constant decls are uninterpreted; a decl recovered from a built-in
        # application via AstRef.decl() carries the real Z3_get_decl_kind.
        self._kind = _lib.Z3_OP_UNINTERPRETED if kind is None else kind

    def name(self):
        """The declaration's name as a Python str (z3py FuncDeclRef.name())."""
        return self._name

    def arity(self):
        return len(self.domain_sorts)

    def __call__(self, *args):
        if len(args) != len(self.domain_sorts):
            raise AyZ3Exception(
                f"{self._name} expects {len(self.domain_sorts)} args, got {len(args)}"
            )
        coerced = [
            _coerce(a, self.domain_sorts[k], self.ctx) for k, a in enumerate(args)
        ]
        if coerced:
            _same_ctx(*coerced)
        n, arr = _as_ast_array(coerced)
        ast = lib.Z3_mk_app(self.ctx.ref, self.handle, n, arr)
        return _wrap(ast, self.range_sort, self.ctx)

    def __repr__(self):
        # z3py renders a FuncDeclRef as just its name (e.g. `f`).
        return self._name


def Function(name, *sig):
    """Declare an uninterpreted function.

    `sig` is domain_sort..., range_sort (z3py order), e.g.
        Function('f', IntSort(), IntSort())        # Int -> Int
        Function('g', IntSort(), IntSort(), BoolSort())  # Int,Int -> Bool
    """
    if len(sig) < 1:
        raise AyZ3Exception("Function needs at least a range sort")
    *domain, rng = sig
    if not all(isinstance(s, SortRef) for s in sig):
        raise NotImplementedError("Function signature must be SortRefs")
    ctx = rng.ctx
    for s in domain:
        if s.ctx is not ctx:
            raise AyZ3Exception("Function signature sorts span multiple contexts")
    sym = lib.Z3_mk_string_symbol(ctx.ref, name.encode())
    n = len(domain)
    dom_arr = (_lib.Z3_sort * n)(*[s.handle for s in domain]) if n else None
    handle = lib.Z3_mk_func_decl(ctx.ref, sym, n, dom_arr, rng.handle)
    if not handle:
        ctx.check_error("Function declaration")
        raise AyZ3Exception("AY returned a null func_decl")
    fd = FuncDeclRef(handle, name, domain, rng, ctx)
    # Record so applications of this UF can be rebuilt in another context.
    _register_funcdecl(fd)
    return fd


def AsArray(f):
    """Convert a unary function declaration to its array representation."""
    if not isinstance(f, FuncDeclRef) or len(f.domain_sorts) != 1:
        raise AyZ3Exception("AsArray expects a unary FuncDeclRef")
    sort = _array_sort(f.domain_sorts[0], f.range_sort, f.ctx)
    out = _wrap(lib.Z3_mk_as_array(f.ctx.ref, f.handle), sort, f.ctx)
    # AY's AST inspection surface cannot recover the function declaration from
    # an as-array term. Retain it explicitly so translating a finite-set
    # map/filter rebuilds `(as-array f)` with the corresponding declaration in
    # the destination context instead of treating it as an opaque nullary UF.
    f.ctx._as_array_meta[out.ast] = f
    return out


def RecFunction(name, *sig):
    """Declare a recursive function symbol (z3py RecFunction).

    `sig` is domain_sort..., range_sort (z3py order), exactly like `Function`.
    Until `RecAddDefinition` supplies the body the symbol is uninterpreted
    (matching z3's semantics for a rec decl whose definition has not arrived
    yet). A rec decl is never silently rebuilt as a plain uninterpreted
    function in another context: without a stored definition, a cross-context
    rebuild raises instead (fail-closed — a plain-UF rebuild would drop the
    recursive semantics and could certify a wrong `sat`).
    """
    if len(sig) < 1:
        raise AyZ3Exception("RecFunction needs at least a range sort")
    *domain, rng = sig
    if not all(isinstance(s, SortRef) for s in sig):
        raise NotImplementedError("RecFunction signature must be SortRefs")
    ctx = rng.ctx
    for s in domain:
        if s.ctx is not ctx:
            raise AyZ3Exception("RecFunction signature sorts span multiple contexts")
    sym = lib.Z3_mk_string_symbol(ctx.ref, name.encode())
    n = len(domain)
    dom_arr = (_lib.Z3_sort * n)(*[s.handle for s in domain]) if n else None
    handle = lib.Z3_mk_rec_func_decl(ctx.ref, sym, n, dom_arr, rng.handle)
    if not handle:
        ctx.check_error("RecFunction declaration")
        raise AyZ3Exception("AY returned a null func_decl")
    fd = FuncDeclRef(handle, name, domain, rng, ctx)
    # Rec markers consumed by the cross-context rebuild: `_is_rec` forbids a
    # plain-UF rebuild; `_rec_def` (set by RecAddDefinition) is the replayable
    # definition (args, body); `_rec_version` counts RecAddDefinition calls so
    # a context that replayed an OLD definition is refreshed, never stale.
    fd._is_rec = True
    fd._rec_def = None
    fd._rec_version = 0
    _register_funcdecl(fd)
    return fd


def RecAddDefinition(f, args, body):
    """Attach the recursive definition `f(args...) == body` (z3py
    RecAddDefinition).

    `args` are the declared constants standing for the parameters (e.g.
    `Int('x')`); `body` is an expression over exactly those constants (and may
    apply `f` itself, or other RecFunctions for mutual recursion). AY registers
    the definition for check-time bounded expansion: fully-expanded goals
    decide (fact(5) == 120 is sat), while any goal whose rec applications
    cannot be fully expanded fails closed — engine `sat` is demoted to
    `unknown`, never certified over an unexpanded recursive function.

    Re-defining an already-defined function is REJECTED (z3 parity:
    "function ... has already been given a definition"), as is a definition
    whose name AY matches structurally as a builtin operator (`+`, `and`,
    `ite`, …) — splicing a body into builtin nodes would rewrite builtin
    semantics (a wrong-verdict class). Errors reported by AY (including
    those, and args that are not declared constants) raise — the definition
    is never silently dropped or silently applied.
    """
    if not isinstance(f, FuncDeclRef):
        raise AyZ3Exception(
            "RecAddDefinition expects a FuncDeclRef (from RecFunction)")
    if isinstance(args, AstRef):
        args = [args]
    args = list(args)
    if len(args) != len(f.domain_sorts):
        raise AyZ3Exception(
            f"RecAddDefinition: {f.name()} expects {len(f.domain_sorts)} "
            f"argument(s), got {len(args)}")
    ctx = f.ctx
    cargs = []
    for a in args:
        if not isinstance(a, AstRef):
            raise AyZ3Exception(
                "RecAddDefinition arguments must be declared constants")
        cargs.append(_adopt(a, ctx))
    body = _adopt(_coerce(body, f.range_sort, ctx), ctx)
    n = len(cargs)
    arr = (_lib.Z3_ast * n)(*[a.ast for a in cargs]) if n else None
    lib.Z3_add_rec_def(ctx.ref, f.handle, n, arr, body.ast)
    ctx.check_error("RecAddDefinition")
    # Mark rec and store the replayable definition ONLY after AY accepted it:
    # a failed definition leaves `_rec_def is None`, so a cross-context rebuild
    # of this decl still fails closed rather than replaying garbage. (The
    # version stamp is retained for the rebuild machinery even though the
    # C level now rejects redefinition — the registry is add-only, so a
    # replayed context can never hold a stale definition.)
    f._is_rec = True
    f._rec_def = (cargs, body)
    f._rec_version = getattr(f, "_rec_version", 0) + 1
    # Invalidate every rebuild memo keyed on this source context: a memoized
    # dst ast embedding an application of `f` would otherwise bypass the
    # decl-level refresh and keep deciding with the REPLACED definition.
    ctx._rebuild_epoch = getattr(ctx, "_rebuild_epoch", 0) + 1


# ---------------------------------------------------------------------------
# Quantifiers  (constant style: bound vars are ordinary app-consts)
# ---------------------------------------------------------------------------

class PatternRef:
    """A quantifier trigger pattern (z3py PatternRef).

    Holds the pattern's term(s). AY's core stores triggers for e-matching, but
    its C ABI has no pattern->AST reader, so the pattern's terms are tracked here
    (they are exactly the terms supplied at construction). `sexpr()` renders the
    z3py multi-pattern shape `(t1 t2 ...)`; the terms print in AY's constant
    style (a bound var appears as its declared name rather than z3py's de Bruijn
    `(:var i)`) — the same documented, sound divergence as a quantifier body.
    """

    def __init__(self, terms, ctx):
        self.terms = list(terms)
        self.ctx = ctx

    def sexpr(self):
        return "(" + " ".join(t.sexpr() for t in self.terms) + ")"

    def __repr__(self):
        return self.sexpr()


def MultiPattern(*args):
    """A multi-term trigger pattern (z3py MultiPattern)."""
    args = _flatten(args)
    if not args:
        raise AyZ3Exception("MultiPattern needs at least one term")
    for a in args:
        if not isinstance(a, AstRef):
            raise NotImplementedError("MultiPattern terms must be expressions")
    ctx = _same_ctx(*args)
    return PatternRef(args, ctx)


def is_pattern(a):
    """z3py is_pattern: whether `a` is a trigger PatternRef."""
    return isinstance(a, PatternRef)


def _mk_pattern_handle(pat, ctx):
    n = len(pat.terms)
    arr = (_lib.Z3_ast * n)(*[t.ast for t in pat.terms])
    return lib.Z3_mk_pattern(ctx.ref, n, arr)


def _norm_patterns(patterns, ctx):
    """Normalize a z3py `patterns=` list into PatternRefs.

    Each entry is either a PatternRef (from MultiPattern) or a bare expression,
    which z3py wraps as a single-term pattern.
    """
    out = []
    for p in patterns or []:
        if isinstance(p, PatternRef):
            out.append(p)
        elif isinstance(p, AstRef):
            out.append(PatternRef([p], ctx))
        else:
            raise NotImplementedError(
                "patterns must be PatternRef (MultiPattern) or expressions")
    return out


def _mk_quant(mk, vs, body, weight=1, patterns=None):
    if isinstance(vs, AstRef):
        vs = [vs]
    vs = list(vs)
    if not vs:
        raise AyZ3Exception("quantifier needs at least one bound variable")
    for v in vs:
        if v.decl_name is None:
            raise NotImplementedError(
                "quantifier bound variables must be declared constants "
                "(e.g. Int('x')), not compound expressions"
            )
    body = _coerce(body, _bool_sort(vs[0].ctx), vs[0].ctx)
    ctx = _same_ctx(*(vs + [body]))
    pat_objs = _norm_patterns(patterns, ctx)
    n = len(vs)
    bound = (_lib.Z3_ast * n)(*[v.ast for v in vs])
    if pat_objs:
        np = len(pat_objs)
        handles = (_lib.Z3_pattern * np)(
            *[_mk_pattern_handle(p, ctx) for p in pat_objs])
        ast = mk(ctx.ref, int(weight), n, bound, np, handles, body.ast)
    else:
        ast = mk(ctx.ref, int(weight), n, bound, 0, None, body.ast)
    if ast == 0:
        ctx.check_error("quantifier construction")
        raise AyZ3Exception("AY returned the null AST for a quantifier")
    # Record the weight (default 1, matching z3py; AY's core does not persist it)
    # and the trigger patterns (AY's C ABI cannot read a pattern back to an AST),
    # keyed by the quantifier AST so the introspection accessors can report them.
    ctx._quantifier_weight[ast] = int(weight)
    if pat_objs:
        ctx._quantifier_patterns[ast] = pat_objs
    return BoolRef(ast, _bool_sort(ctx), ctx)


def ForAll(vs, body, weight=1, qid="", skid="", patterns=None, no_patterns=None):
    """Universal quantifier. `vs` is a declared const or list of them.

    Accepts z3py's `weight` and `patterns` (list of MultiPattern / expressions).
    `qid`/`skid`/`no_patterns` are accepted for signature compatibility; AY does
    not track a quantifier id/skolem-id and has no no-pattern facility.
    """
    return _mk_quant(lib.Z3_mk_forall_const, vs, body, weight, patterns)


def Exists(vs, body, weight=1, qid="", skid="", patterns=None, no_patterns=None):
    """Existential quantifier. See `ForAll` for the keyword arguments."""
    return _mk_quant(lib.Z3_mk_exists_const, vs, body, weight, patterns)


def Lambda(vs, body):
    """z3py Lambda([vars], body) — an array-valued lambda term.

    AY's core has no lambda / array-comprehension term, so this capability is
    genuinely absent. Raising `NotImplementedError` keeps the binding honest
    rather than fabricating an unsound encoding; use `ForAll`/`Exists` for
    quantified assertions and `Array`/`Store`/`K` for array values.
    """
    raise NotImplementedError(
        "Lambda is not supported: AY's core has no lambda (array-comprehension) "
        "term. Use ForAll/Exists for quantified assertions.")


# ---------------------------------------------------------------------------
# Strings / sequences
# ---------------------------------------------------------------------------

def _as_seq(value, ctx):
    """Coerce a Python str or SeqRef to a string-sorted AstRef."""
    if isinstance(value, SeqRef):
        return value
    if isinstance(value, str):
        return StringVal(value, ctx)
    if isinstance(value, AstRef) and value.sort_ref.kind == "String":
        return value
    raise NotImplementedError(
        f"expected a String expression or Python str, got {value!r}"
    )


def _seq_ctx(args):
    for a in args:
        if isinstance(a, AstRef):
            return a.ctx
    return _current_ctx()


def Concat(*args):
    """Concatenate bitvectors, strings/sequences, or regexes (z3py Concat).

    Like z3py, dispatches on argument sort: bitvector operands concatenate with
    `bvconcat` (`concat`, most-significant first, widths summed); a regular
    expression operand gives the regex concatenation `re.++`; otherwise it is
    the string/sequence concatenation `str.++`.
    """
    args = _flatten(args)
    if len(args) < 2:
        raise AyZ3Exception("Concat needs at least two arguments")
    ctx = _seq_ctx(args)
    # Bitvector concatenation when the first operand is a bitvector (matches
    # z3py, which dispatches on is_bv(args[0])). Folds left, summing widths.
    if isinstance(args[0], BitVecRef):
        acc = args[0]
        for nxt in args[1:]:
            if not isinstance(nxt, BitVecRef):
                raise NotImplementedError(
                    "Concat: cannot mix bitvector and non-bitvector operands")
            c2 = _same_ctx(acc, nxt)
            acc = _wrap(lib.Z3_mk_concat(c2.ref, acc.ast, nxt.ast),
                        _bv_sort(acc.size + nxt.size, c2), c2)
        return acc
    # Regex concatenation when any operand is a regular expression.
    if any(isinstance(a, ReRef) for a in args):
        res = [_as_re(a, ctx) for a in args]
        _same_ctx(*res)
        n, arr = _as_ast_array(res)
        return _wrap(lib.Z3_mk_re_concat(ctx.ref, n, arr), _re_sort(ctx=ctx), ctx)
    items = [_as_seq(a, ctx) for a in args]
    _same_ctx(*items)
    n, arr = _as_ast_array(items)
    ast = lib.Z3_mk_seq_concat(ctx.ref, n, arr)
    return _wrap(ast, items[0].sort_ref, ctx)


def Length(s):
    """Length of a string/sequence (returns an Int)."""
    ctx = _seq_ctx([s])
    s = _as_seq(s, ctx)
    return _wrap(lib.Z3_mk_seq_length(ctx.ref, s.ast), _int_sort(ctx), ctx)


def Contains(s, sub):
    """Whether `s` contains `sub` as a contiguous subsequence."""
    ctx = _seq_ctx([s, sub])
    s = _as_seq(s, ctx)
    sub = _as_seq(sub, ctx)
    _same_ctx(s, sub)
    return BoolRef(lib.Z3_mk_seq_contains(ctx.ref, s.ast, sub.ast), _bool_sort(ctx), ctx)


def PrefixOf(pre, s):
    """Whether `pre` is a prefix of `s`."""
    ctx = _seq_ctx([pre, s])
    pre = _as_seq(pre, ctx)
    s = _as_seq(s, ctx)
    _same_ctx(pre, s)
    return BoolRef(lib.Z3_mk_seq_prefix(ctx.ref, pre.ast, s.ast), _bool_sort(ctx), ctx)


def SuffixOf(suf, s):
    """Whether `suf` is a suffix of `s`."""
    ctx = _seq_ctx([suf, s])
    suf = _as_seq(suf, ctx)
    s = _as_seq(s, ctx)
    _same_ctx(suf, s)
    return BoolRef(lib.Z3_mk_seq_suffix(ctx.ref, suf.ast, s.ast), _bool_sort(ctx), ctx)


def IndexOf(s, sub, offset=0):
    """Index of the first occurrence of `sub` in `s` at or after `offset`."""
    ctx = _seq_ctx([s, sub, offset])
    s = _as_seq(s, ctx)
    sub = _as_seq(sub, ctx)
    off = _coerce(offset, _int_sort(ctx), ctx)
    _same_ctx(s, sub, off)
    return _wrap(lib.Z3_mk_seq_index(ctx.ref, s.ast, sub.ast, off.ast),
                 _int_sort(ctx), ctx)


# NOTE: z3py's `LastIndexOf` (SMT `seq.last_indexof`) is deliberately NOT exposed.
# AY builds the correct term, but its decision procedure leaves the result
# UNCONSTRAINED on ground inputs — e.g. `LastIndexOf("abcb","b") == 1` (and
# `== 999`, `== 0`) are all wrongly `sat` where z3 proves `unsat` (the true last
# index is 3). Emitting it would yield wrong verdicts, so it is omitted (honest
# absence) rather than misrepresent the op.


def SubString(s, offset, length):
    """The substring of `s` starting at `offset` of the given `length`."""
    ctx = _seq_ctx([s, offset, length])
    s = _as_seq(s, ctx)
    off = _coerce(offset, _int_sort(ctx), ctx)
    ln = _coerce(length, _int_sort(ctx), ctx)
    _same_ctx(s, off, ln)
    return _wrap(lib.Z3_mk_seq_extract(ctx.ref, s.ast, off.ast, ln.ast),
                 s.sort_ref, ctx)


def SubSeq(s, offset, length):
    """The subsequence of `s` at `offset` of the given `length` (z3py `SubSeq`).

    A convenience alias for `SubString` / `Extract(s, offset, length)` (SMT
    `str.substr`), matching z3py exactly.
    """
    return SubString(s, offset, length)


# z3py's `Extract` is overloaded on operand type: a bitvector bit-slice
# `Extract(high, low, bv)` or a string substring `Extract(s, offset, length)`
# (== SubString / str.substr). Dispatch exactly as z3py does.
def Extract(a, b, c):
    """Bitvector bit-slice `Extract(high, low, bv)` or string substring
    `Extract(s, offset, length)` (z3py Extract, overloaded on argument type)."""
    if isinstance(a, (SeqRef, str)):
        return SubString(a, b, c)
    if isinstance(c, BitVecRef):
        ctx = c.ctx
        hi, lo = int(a), int(b)
        return _wrap(lib.Z3_mk_extract(ctx.ref, hi, lo, c.ast),
                     _bv_sort(hi - lo + 1, ctx), ctx)
    raise NotImplementedError(
        "Extract expects Extract(high:int, low:int, bv) for bitvectors, or "
        "Extract(s, offset, length) for strings")


def Replace(s, src, dst):
    """`s` with the first occurrence of `src` replaced by `dst`."""
    ctx = _seq_ctx([s, src, dst])
    s = _as_seq(s, ctx)
    src = _as_seq(src, ctx)
    dst = _as_seq(dst, ctx)
    _same_ctx(s, src, dst)
    return _wrap(lib.Z3_mk_seq_replace(ctx.ref, s.ast, src.ast, dst.ast),
                 s.sort_ref, ctx)


# ---------------------------------------------------------------------------
# Regular expressions (RegLan) — z3py's regex surface over AY's `re.*` theory
# ---------------------------------------------------------------------------
#
# Each constructor below maps to a native AY regex operation. The wrapper's
# per-constructor encoding and AY's regex/sequence implementation are both in
# the correctness boundary; incomplete queries may return `unknown`.
# Representative `sexpr()` shapes are cross-checked against z3py.

def _as_re(value, ctx):
    """Coerce to a RegLan-sorted `ReRef`.

    A `ReRef` (or any RegLan-sorted expr) passes through; a Python `str` or a
    String-sorted expr is lifted to the singleton regex via `Re` (z3py accepts
    this coercion for regex builders).
    """
    if isinstance(value, ReRef):
        return value
    if isinstance(value, AstRef) and value.sort_ref.kind == "RegLan":
        return value
    if isinstance(value, str) or (
        isinstance(value, AstRef) and value.sort_ref.kind == "String"
    ):
        return Re(value, ctx)
    raise NotImplementedError(
        f"expected a regular expression (or String) argument, got {value!r}"
    )


def Re(s, ctx=None):
    """The regex matching exactly the string/sequence `s` (SMT `str.to_re`)."""
    if isinstance(s, ReRef):
        return s
    ctx = ctx or _seq_ctx([s])
    s = _as_seq(s, ctx)
    return _wrap(lib.Z3_mk_seq_to_re(ctx.ref, s.ast), _re_sort(ctx=ctx), ctx)


# z3py spells the singleton-regex constructor `Re`; `to_re` is a convenience
# alias matching the SMT-LIB operator name.
to_re = Re


def InRe(s, re):
    """Whether string/sequence `s` is a member of regex `re` (SMT `str.in_re`)."""
    ctx = _seq_ctx([s, re])
    s = _as_seq(s, ctx)
    re = _as_re(re, ctx)
    _same_ctx(s, re)
    return BoolRef(lib.Z3_mk_seq_in_re(ctx.ref, s.ast, re.ast), _bool_sort(ctx), ctx)


def Star(re):
    """Kleene star `re.*` — zero or more repetitions of `re`."""
    ctx = _seq_ctx([re])
    re = _as_re(re, ctx)
    return _wrap(lib.Z3_mk_re_star(ctx.ref, re.ast), _re_sort(ctx=ctx), ctx)


def Plus(re):
    """Kleene plus `re.+` — one or more repetitions of `re`."""
    ctx = _seq_ctx([re])
    re = _as_re(re, ctx)
    return _wrap(lib.Z3_mk_re_plus(ctx.ref, re.ast), _re_sort(ctx=ctx), ctx)


def Option(re):
    """Optional `re.opt` — the empty string or `re`."""
    ctx = _seq_ctx([re])
    re = _as_re(re, ctx)
    return _wrap(lib.Z3_mk_re_option(ctx.ref, re.ast), _re_sort(ctx=ctx), ctx)


def Complement(re):
    """Complement `re.comp` — every string `re` does not match."""
    ctx = _seq_ctx([re])
    re = _as_re(re, ctx)
    return _wrap(lib.Z3_mk_re_complement(ctx.ref, re.ast), _re_sort(ctx=ctx), ctx)


def Union(*args):
    """Union of regexes `re.union` (n-ary; z3py returns a lone argument as-is)."""
    args = _flatten(args)
    if len(args) == 0:
        raise AyZ3Exception("Union needs at least one argument")
    ctx = _seq_ctx(args)
    res = [_as_re(a, ctx) for a in args]
    if len(res) == 1:
        return res[0]
    _same_ctx(*res)
    n, arr = _as_ast_array(res)
    return _wrap(lib.Z3_mk_re_union(ctx.ref, n, arr), _re_sort(ctx=ctx), ctx)


def Intersect(*args):
    """Intersection of regexes `re.inter` (n-ary; a lone argument as-is)."""
    args = _flatten(args)
    if len(args) == 0:
        raise AyZ3Exception("Intersect needs at least one argument")
    ctx = _seq_ctx(args)
    res = [_as_re(a, ctx) for a in args]
    if len(res) == 1:
        return res[0]
    _same_ctx(*res)
    n, arr = _as_ast_array(res)
    return _wrap(lib.Z3_mk_re_intersect(ctx.ref, n, arr), _re_sort(ctx=ctx), ctx)


def Range(lo, hi, ctx=None):
    """Character-range regex `re.range` over single-character strings `lo`, `hi`."""
    ctx = ctx or _seq_ctx([lo, hi])
    lo = _as_seq(lo, ctx)
    hi = _as_seq(hi, ctx)
    _same_ctx(lo, hi)
    return _wrap(lib.Z3_mk_re_range(ctx.ref, lo.ast, hi.ast), _re_sort(ctx=ctx), ctx)


def Loop(re, lo, hi=0):
    """Bounded repetition `(_ re.loop lo hi) re` — between `lo` and `hi` copies."""
    ctx = _seq_ctx([re])
    re = _as_re(re, ctx)
    return _wrap(
        lib.Z3_mk_re_loop(ctx.ref, re.ast, int(lo), int(hi)), _re_sort(ctx=ctx), ctx
    )


def Full(s):
    """The universal regex `re.all` of the given regex sort (z3py `Full`)."""
    if not (isinstance(s, SortRef) and s.kind == "RegLan"):
        raise AyZ3Exception(
            "Full expects a regex sort, e.g. Full(ReSort(StringSort()))"
        )
    ctx = s.ctx
    return _wrap(lib.Z3_mk_re_full(ctx.ref, s.handle), _re_sort(ctx=ctx), ctx)


def Empty(s):
    """The empty regex `re.none`, or the empty string for a String sort.

    Matches z3py: `Empty(ReSort(StringSort()))` is `re.none`; `Empty(StringSort())`
    is the empty string `""`.
    """
    if isinstance(s, SortRef) and s.kind == "RegLan":
        ctx = s.ctx
        return _wrap(lib.Z3_mk_re_empty(ctx.ref, s.handle), _re_sort(ctx=ctx), ctx)
    if isinstance(s, SortRef) and s.kind == "String":
        return StringVal("", s.ctx)
    raise AyZ3Exception(
        "Empty expects a regex sort (ReSort(...)) or the String sort"
    )


def AllChar(regex_sort, ctx=None):
    """The any-single-character regex `re.allchar` of the given regex sort."""
    if not (isinstance(regex_sort, SortRef) and regex_sort.kind == "RegLan"):
        raise AyZ3Exception(
            "AllChar expects a regex sort, e.g. AllChar(ReSort(StringSort()))"
        )
    ctx = regex_sort.ctx
    return _wrap(
        lib.Z3_mk_re_allchar(ctx.ref, regex_sort.handle), _re_sort(ctx=ctx), ctx
    )


# ---------------------------------------------------------------------------
# Model
# ---------------------------------------------------------------------------

def _sort_from_handle(sh, ctx):
    """Build a SortRef from a raw Z3_sort handle, recursing into arrays."""
    if lib.Z3_is_finite_set_sort(ctx.ref, sh):
        basis = lib.Z3_get_finite_set_sort_basis(ctx.ref, sh)
        return FiniteSetSortRef(sh, _sort_from_handle(basis, ctx), ctx)
    kind = lib.Z3_get_sort_kind(ctx.ref, sh)
    if kind == _lib.Z3_BOOL_SORT:
        return SortRef(sh, "Bool", ctx)
    if kind == _lib.Z3_INT_SORT:
        return SortRef(sh, "Int", ctx)
    if kind == _lib.Z3_REAL_SORT:
        return SortRef(sh, "Real", ctx)
    if kind == _lib.Z3_BV_SORT:
        size = lib.Z3_get_bv_sort_size(ctx.ref, sh)
        return SortRef(sh, "BitVec", ctx, size)
    if kind == _lib.Z3_ARRAY_SORT:
        dh = lib.Z3_get_array_sort_domain(ctx.ref, sh)
        rh = lib.Z3_get_array_sort_range(ctx.ref, sh)
        return SortRef(
            sh, "Array", ctx,
            domain=_sort_from_handle(dh, ctx),
            range=_sort_from_handle(rh, ctx),
        )
    if kind == _lib.Z3_SEQ_SORT:
        return SortRef(sh, "String", ctx)
    if kind == _lib.Z3_DATATYPE_SORT:
        return _datatype_sort_from_handle(sh, ctx)
    # FP sorts report an out-of-enum kind through AY's C ABI and the
    # RoundingMode sort reports UNINTERPRETED; both are recovered from the
    # sort NAME ("(_ FloatingPoint E S)" / "RoundingMode").
    sym = lib.Z3_get_sort_name(ctx.ref, sh)
    nm = lib.Z3_get_symbol_string(ctx.ref, sym) if sym else None
    nm = nm.decode() if nm else ""
    m = re.match(r"^\(_ FloatingPoint (\d+) (\d+)\)$", nm)
    if m:
        from .fp import FPSortRef
        return FPSortRef(sh, int(m.group(1)), int(m.group(2)), ctx)
    if nm == "RoundingMode":
        from .fp import FPRMSortRef
        return FPRMSortRef(sh, ctx)
    return SortRef(sh, "Int", ctx)  # defensive fallback


def _datatype_sort_from_handle(sh, ctx):
    """Recover a DatatypeSortRef for a datatype sort handle.

    The datatype's constructor structure is not readable back from a bare sort
    handle through AY's C ABI, so we resolve the full DatatypeSortRef from the
    context's registry by name (populated when the datatype was declared /
    rebuilt in this context). If the name is not registered (a datatype sort
    that did not originate from this ayz3 session), fall back to a minimal
    name-only sort wrapper so a model value still renders honestly.
    """
    sym = lib.Z3_get_sort_name(ctx.ref, sh)
    name = lib.Z3_get_symbol_string(ctx.ref, sym) if sym else None
    name = name.decode() if name else ""
    ds = ctx._datatype_sorts.get(name)
    if ds is not None:
        return ds
    # Unknown datatype: a lightweight sort object that duck-types SortRef enough
    # for wrapping/rendering a value (kind + ctx + handle), without constructors.
    stub = SortRef(sh, "Datatype", ctx)
    stub._dt_name = name
    return stub


def _value_sort_from_ast(ast, ctx):
    """Recover a SortRef for a model-value AST via Z3_get_sort."""
    sh = lib.Z3_get_sort(ctx.ref, ast)
    return _sort_from_handle(sh, ctx)


def _wrap_from_ast(ast, ctx):
    """Wrap a bare Z3_ast handle into the right AstRef, recovering its sort."""
    sh = lib.Z3_get_sort(ctx.ref, ast)
    kind = lib.Z3_get_sort_kind(ctx.ref, sh) if sh else _lib.Z3_UNKNOWN_AST
    if kind == _lib.Z3_UNKNOWN_AST:
        # A value sub-term pulled out of a datatype constructor via
        # Z3_get_app_arg (e.g. `m[p].arg(i)` for a `Pair(9, True)` field) can
        # carry no recorded sort in AY's C ABI, so Z3_get_sort yields UNKNOWN and
        # _sort_from_handle would fall back to Int — mis-sorting a Boolean field
        # as an ArithRef that prints `true`. Recover a DETERMINED Boolean here so
        # `.arg(i)` is a BoolRef that prints `True`/`False`, matching z3py.
        bv = lib.Z3_get_bool_value(ctx.ref, ast)
        if bv in (_lib.Z3_L_TRUE, _lib.Z3_L_FALSE):
            return _wrap(ast, _bool_sort(ctx), ctx)
    sort = _sort_from_handle(sh, ctx)
    return _wrap(ast, sort, ctx)


# ---------------------------------------------------------------------------
# Cross-context expression rebuild
# ---------------------------------------------------------------------------
#
# z3py lets you build an expression once and use it in many independent
# Solver/Optimize objects. ayz3 gives every top-level Solver/Optimize its own
# Context (Z3_optimize still aliases per-context engine state, and per-solver
# contexts keep term arenas self-contained). The cost is that an expression
# built in context A cannot be asserted into a Solver in context B directly
# (AY rejects cross-context terms).
#
# We close that gap by rebuilding the expression in the destination context:
# recursively walk the source AST via the term-introspection C API and
# reconstruct each node with the matching builder. The walk is intended to
# preserve the stored structure, including AY's eager normalization (for
# example, `x > 0` is stored as `0 < x`). Declared constants with the same name
# and sort rebuild to the same B-term through AY's hash-consing. Correctness
# depends on the per-node builder mappings below; unsupported node kinds raise
# NotImplementedError rather than being silently dropped.

# Operator-name -> builder. Each builder takes (dst_ctx, [rebuilt-arg asts],
# src_ast for any extra metadata) and returns a destination Z3_ast handle.
# AY reports the canonical operator name via Z3_get_decl_name; we route on it.
# n-ary ops (+ * and or) accept any arity; binary ops take exactly 2.


def _nary_builder(mk):
    def build(dctx, args, _src):
        n = len(args)
        arr = (_lib.Z3_ast * n)(*args)
        return mk(dctx.ref, n, arr)
    return build


def _binary_builder(mk):
    def build(dctx, args, _src):
        return mk(dctx.ref, args[0], args[1])
    return build


def _unary_builder(mk):
    def build(dctx, args, _src):
        return mk(dctx.ref, args[0])
    return build


def _ternary_builder(mk):
    def build(dctx, args, _src):
        return mk(dctx.ref, args[0], args[1], args[2])
    return build


def _re_const_builder(mk):
    """Nullary regex constants (re.all / re.none / re.allchar) take a RegLan sort
    rather than argument asts; rebuild the (monomorphic) regex sort in dctx."""
    def build(dctx, _args, _src):
        return mk(dctx.ref, _re_sort(ctx=dctx).handle)
    return build


# Built-in operators whose name (from Z3_get_decl_name) maps to a single AY
# builder. Everything here is sort-agnostic at the C ABI level (AY infers result
# sorts from the operand terms), so we just forward the rebuilt argument asts.
_REBUILD_OPS = {
    # Boolean
    "=": _binary_builder(lambda c, a, b: lib.Z3_mk_eq(c, a, b)),
    "and": _nary_builder(lib.Z3_mk_and),
    "or": _nary_builder(lib.Z3_mk_or),
    "not": _unary_builder(lib.Z3_mk_not),
    "xor": _binary_builder(lib.Z3_mk_xor),
    "iff": _binary_builder(lib.Z3_mk_iff),
    "=>": _binary_builder(lib.Z3_mk_implies),
    "implies": _binary_builder(lib.Z3_mk_implies),
    # AY's decl-name for if-then-else is "if" (z3py's canonical name); older/raw
    # "ite" spellings are accepted too so any core-named term still rebuilds.
    "if": _ternary_builder(lambda c, a, b, d: lib.Z3_mk_ite(c, a, b, d)),
    "ite": _ternary_builder(lambda c, a, b, d: lib.Z3_mk_ite(c, a, b, d)),
    "distinct": _nary_builder(lib.Z3_mk_distinct),
    # Arithmetic
    "+": _nary_builder(lib.Z3_mk_add),
    "*": _nary_builder(lib.Z3_mk_mul),
    # AY normalizes subtraction to (+ a (- b)); a top-level "-" therefore only
    # appears as UNARY minus. We still accept an n-ary "-" defensively.
    "-": (lambda dctx, args, _src:
          lib.Z3_mk_unary_minus(dctx.ref, args[0]) if len(args) == 1
          else lib.Z3_mk_sub(dctx.ref, len(args), (_lib.Z3_ast * len(args))(*args))),
    "neg": _unary_builder(lib.Z3_mk_unary_minus),
    "div": _binary_builder(lambda c, a, b: lib.Z3_mk_div(c, a, b)),
    "/": _binary_builder(lambda c, a, b: lib.Z3_mk_div(c, a, b)),
    "mod": _binary_builder(lambda c, a, b: lib.Z3_mk_mod(c, a, b)),
    "<": _binary_builder(lambda c, a, b: lib.Z3_mk_lt(c, a, b)),
    "<=": _binary_builder(lambda c, a, b: lib.Z3_mk_le(c, a, b)),
    ">": _binary_builder(lambda c, a, b: lib.Z3_mk_gt(c, a, b)),
    ">=": _binary_builder(lambda c, a, b: lib.Z3_mk_ge(c, a, b)),
    "to_real": _unary_builder(lib.Z3_mk_int2real),
    "to_int": _unary_builder(lib.Z3_mk_real2int),
    "is_int": _unary_builder(lib.Z3_mk_is_int),
    # Real exponentiation `base ^ exp` (z3py Sqrt/Cbrt build over this).
    "^": _binary_builder(lambda c, a, b: lib.Z3_mk_power(c, a, b)),
    # Bitvectors
    "bvadd": _binary_builder(lambda c, a, b: lib.Z3_mk_bvadd(c, a, b)),
    "bvsub": _binary_builder(lambda c, a, b: lib.Z3_mk_bvsub(c, a, b)),
    "bvmul": _binary_builder(lambda c, a, b: lib.Z3_mk_bvmul(c, a, b)),
    "bvand": _binary_builder(lambda c, a, b: lib.Z3_mk_bvand(c, a, b)),
    "bvor": _binary_builder(lambda c, a, b: lib.Z3_mk_bvor(c, a, b)),
    "bvxor": _binary_builder(lambda c, a, b: lib.Z3_mk_bvxor(c, a, b)),
    "bvnot": _unary_builder(lib.Z3_mk_bvnot),
    "bvneg": _unary_builder(lib.Z3_mk_bvneg),
    "bvult": _binary_builder(lambda c, a, b: lib.Z3_mk_bvult(c, a, b)),
    "bvule": _binary_builder(lambda c, a, b: lib.Z3_mk_bvule(c, a, b)),
    "bvugt": _binary_builder(lambda c, a, b: lib.Z3_mk_bvugt(c, a, b)),
    "bvuge": _binary_builder(lambda c, a, b: lib.Z3_mk_bvuge(c, a, b)),
    "bvslt": _binary_builder(lambda c, a, b: lib.Z3_mk_bvslt(c, a, b)),
    "bvsle": _binary_builder(lambda c, a, b: lib.Z3_mk_bvsle(c, a, b)),
    "bvsgt": _binary_builder(lambda c, a, b: lib.Z3_mk_bvsgt(c, a, b)),
    "bvsge": _binary_builder(lambda c, a, b: lib.Z3_mk_bvsge(c, a, b)),
    # BV division / remainder / mod / shifts / concat (B-10). The width-changing
    # indexed ops (extract/sign_extend/zero_extend/repeat/rotate_left/
    # rotate_right/int2bv) carry their sizes as decl parameters and are handled
    # specially in `_rebuild_app`. bvredand/bvredor and the overflow predicates
    # are stored EXPANDED (ite / or / and / bvslt / ...), so they rebuild through
    # those existing entries with no dedicated builder.
    "bvudiv": _binary_builder(lambda c, a, b: lib.Z3_mk_bvudiv(c, a, b)),
    "bvsdiv": _binary_builder(lambda c, a, b: lib.Z3_mk_bvsdiv(c, a, b)),
    "bvurem": _binary_builder(lambda c, a, b: lib.Z3_mk_bvurem(c, a, b)),
    "bvsrem": _binary_builder(lambda c, a, b: lib.Z3_mk_bvsrem(c, a, b)),
    "bvsmod": _binary_builder(lambda c, a, b: lib.Z3_mk_bvsmod(c, a, b)),
    "bvshl": _binary_builder(lambda c, a, b: lib.Z3_mk_bvshl(c, a, b)),
    "bvlshr": _binary_builder(lambda c, a, b: lib.Z3_mk_bvlshr(c, a, b)),
    "bvashr": _binary_builder(lambda c, a, b: lib.Z3_mk_bvashr(c, a, b)),
    "concat": _binary_builder(lambda c, a, b: lib.Z3_mk_concat(c, a, b)),
    # BV -> Int (unsigned). AY's decl-name for the unsigned conversion is
    # "bv2nat"; the signed BV2Int is stored as an ite over it, so only the
    # unsigned node needs a builder here.
    "bv2nat": (lambda dctx, args, _src: lib.Z3_mk_bv2int(dctx.ref, args[0], False)),
    # Arrays
    "select": _binary_builder(lambda c, a, b: lib.Z3_mk_select(c, a, b)),
    "store": _ternary_builder(lambda c, a, b, d: lib.Z3_mk_store(c, a, b, d)),
    # Strings / sequences
    "str.++": _nary_builder(lib.Z3_mk_seq_concat),
    "str.len": _unary_builder(lib.Z3_mk_seq_length),
    "str.contains": _binary_builder(lambda c, a, b: lib.Z3_mk_seq_contains(c, a, b)),
    "str.prefixof": _binary_builder(lambda c, a, b: lib.Z3_mk_seq_prefix(c, a, b)),
    "str.suffixof": _binary_builder(lambda c, a, b: lib.Z3_mk_seq_suffix(c, a, b)),
    "str.at": _binary_builder(lambda c, a, b: lib.Z3_mk_seq_at(c, a, b)),
    "str.indexof": _ternary_builder(lambda c, a, b, d: lib.Z3_mk_seq_index(c, a, b, d)),
    "str.substr": _ternary_builder(lambda c, a, b, d: lib.Z3_mk_seq_extract(c, a, b, d)),
    "str.replace": _ternary_builder(lambda c, a, b, d: lib.Z3_mk_seq_replace(c, a, b, d)),
    "str.from_int": _unary_builder(lib.Z3_mk_int_to_str),
    "str.to_int": _unary_builder(lib.Z3_mk_str_to_int),
    "str.to_code": _unary_builder(lib.Z3_mk_string_to_code),
    "str.from_code": _unary_builder(lib.Z3_mk_string_from_code),
    # Regular expressions (RegLan) — B-9. `re.loop` is indexed (its bounds are
    # decl parameters, not args) and is handled specially in `_rebuild_app`.
    "str.in_re": _binary_builder(lambda c, a, b: lib.Z3_mk_seq_in_re(c, a, b)),
    "str.to_re": _unary_builder(lib.Z3_mk_seq_to_re),
    "re.*": _unary_builder(lib.Z3_mk_re_star),
    "re.+": _unary_builder(lib.Z3_mk_re_plus),
    "re.opt": _unary_builder(lib.Z3_mk_re_option),
    "re.comp": _unary_builder(lib.Z3_mk_re_complement),
    "re.union": _nary_builder(lib.Z3_mk_re_union),
    "re.inter": _nary_builder(lib.Z3_mk_re_intersect),
    "re.++": _nary_builder(lib.Z3_mk_re_concat),
    "re.range": _binary_builder(lambda c, a, b: lib.Z3_mk_re_range(c, a, b)),
    "re.all": _re_const_builder(lib.Z3_mk_re_full),
    "re.none": _re_const_builder(lib.Z3_mk_re_empty),
    "re.allchar": _re_const_builder(lib.Z3_mk_re_allchar),
    # Floating-point operators (sort-agnostic at the C ABI level; AY infers
    # the FP sort from the operand terms). Decl names verified against AY:
    # rm-first arithmetic is (rm, a, b) / fma is (rm, a, b, c).
    "fp.add": _ternary_builder(lambda c, r, a, b: lib.Z3_mk_fpa_add(c, r, a, b)),
    "fp.sub": _ternary_builder(lambda c, r, a, b: lib.Z3_mk_fpa_sub(c, r, a, b)),
    "fp.mul": _ternary_builder(lambda c, r, a, b: lib.Z3_mk_fpa_mul(c, r, a, b)),
    "fp.div": _ternary_builder(lambda c, r, a, b: lib.Z3_mk_fpa_div(c, r, a, b)),
    "fp.fma": (lambda dctx, args, _src:
               lib.Z3_mk_fpa_fma(dctx.ref, args[0], args[1], args[2], args[3])),
    "fp.sqrt": _binary_builder(lambda c, r, a: lib.Z3_mk_fpa_sqrt(c, r, a)),
    "fp.roundToIntegral": _binary_builder(
        lambda c, r, a: lib.Z3_mk_fpa_round_to_integral(c, r, a)),
    "fp.rem": _binary_builder(lambda c, a, b: lib.Z3_mk_fpa_rem(c, a, b)),
    "fp.min": _binary_builder(lambda c, a, b: lib.Z3_mk_fpa_min(c, a, b)),
    "fp.max": _binary_builder(lambda c, a, b: lib.Z3_mk_fpa_max(c, a, b)),
    "fp.abs": _unary_builder(lib.Z3_mk_fpa_abs),
    "fp.neg": _unary_builder(lib.Z3_mk_fpa_neg),
    "fp.eq": _binary_builder(lambda c, a, b: lib.Z3_mk_fpa_eq(c, a, b)),
    "fp.lt": _binary_builder(lambda c, a, b: lib.Z3_mk_fpa_lt(c, a, b)),
    "fp.leq": _binary_builder(lambda c, a, b: lib.Z3_mk_fpa_leq(c, a, b)),
    "fp.gt": _binary_builder(lambda c, a, b: lib.Z3_mk_fpa_gt(c, a, b)),
    "fp.geq": _binary_builder(lambda c, a, b: lib.Z3_mk_fpa_geq(c, a, b)),
    "fp.isNaN": _unary_builder(lib.Z3_mk_fpa_is_nan),
    "fp.isInfinite": _unary_builder(lib.Z3_mk_fpa_is_infinite),
    "fp.isZero": _unary_builder(lib.Z3_mk_fpa_is_zero),
    "fp.isNormal": _unary_builder(lib.Z3_mk_fpa_is_normal),
    "fp.isSubnormal": _unary_builder(lib.Z3_mk_fpa_is_subnormal),
    "fp.isNegative": _unary_builder(lib.Z3_mk_fpa_is_negative),
    "fp.isPositive": _unary_builder(lib.Z3_mk_fpa_is_positive),
}


# Indexed BV operators: name -> (dctx, single_arg_ast, [int params]) -> Z3_ast.
# Their sizes come from the source decl's integer parameters (see _rebuild_app).
_REBUILD_INDEXED_BV = {
    "extract": (lambda dctx, a, p:
                lib.Z3_mk_extract(dctx.ref, int(p[0]), int(p[1]), a)),
    "sign_extend": (lambda dctx, a, p:
                    lib.Z3_mk_sign_ext(dctx.ref, int(p[0]), a)),
    "zero_extend": (lambda dctx, a, p:
                    lib.Z3_mk_zero_ext(dctx.ref, int(p[0]), a)),
    "repeat": (lambda dctx, a, p: lib.Z3_mk_repeat(dctx.ref, int(p[0]), a)),
    "rotate_left": (lambda dctx, a, p:
                    lib.Z3_mk_rotate_left(dctx.ref, int(p[0]), a)),
    "rotate_right": (lambda dctx, a, p:
                     lib.Z3_mk_rotate_right(dctx.ref, int(p[0]), a)),
    "int2bv": (lambda dctx, a, p: lib.Z3_mk_int2bv(dctx.ref, int(p[0]), a)),
}


def _rebuild_sort_in_ctx(sort, dctx):
    """Rebuild a SortRef in dctx (sorts are cheap to recreate by kind)."""
    k = sort.kind
    if k == "Bool":
        return _bool_sort(dctx)
    if k == "Int":
        return _int_sort(dctx)
    if k == "Real":
        return _real_sort(dctx)
    if k == "BitVec":
        return _bv_sort(sort.bv_size, dctx)
    if k == "Array":
        return _array_sort(
            _rebuild_sort_in_ctx(sort.domain_sort, dctx),
            _rebuild_sort_in_ctx(sort.range_sort, dctx),
            dctx,
        )
    if k == "FiniteSet":
        return FiniteSetSort(_rebuild_sort_in_ctx(sort.basis_sort, dctx))
    if k == "String":
        return _string_sort(dctx)
    if k == "Datatype":
        # Re-declare the datatype in dctx (idempotent) and return its sort there.
        return _rebuild_datatype_sort(sort, dctx)
    if k == "FloatingPoint":
        from .fp import FPSort
        return FPSort(sort.ebits(), sort.sbits(), dctx)
    if k == "RoundingMode":
        from .fp import _fprm_sort
        return _fprm_sort(dctx)
    raise NotImplementedError(
        f"cross-context rebuild does not support sort kind {k!r}"
    )


def _rebuild_const(src_ast, src_ctx, dctx):
    """Rebuild a declared 0-arity constant (Var node) in dctx by name+sort.

    The name is recovered from the per-context registry populated at
    construction (AY's C ABI cannot read a const's name back from its handle).
    """
    meta = src_ctx._const_meta.get(src_ast)
    if meta is None:
        raise NotImplementedError(
            "cross-context rebuild encountered a constant with no recorded name "
            "(handle {}); only constants declared via Int/Real/Bool/BitVec/"
            "Const/Array/String/Function can be rebuilt".format(src_ast)
        )
    name, sort = meta
    dsort = _rebuild_sort_in_ctx(sort, dctx)
    sym = lib.Z3_mk_string_symbol(dctx.ref, name.encode())
    dast = lib.Z3_mk_const(dctx.ref, sym, dsort.handle)
    # Register the rebuilt const so it is itself recoverable if later rebuilt
    # again (e.g. it appears as a quantifier bound var in B).
    dctx._const_meta[dast] = (name, dsort)
    return dast


def _rebuild_numeral(src_ast, src_ctx, dctx):
    """Rebuild a numeral / literal constant in dctx from its concrete value."""
    sort = _value_sort_from_ast(src_ast, src_ctx)
    k = sort.kind
    if k == "Bool":
        v = lib.Z3_get_bool_value(src_ctx.ref, src_ast)
        if v == _lib.Z3_L_TRUE:
            return lib.Z3_mk_true(dctx.ref)
        if v == _lib.Z3_L_FALSE:
            return lib.Z3_mk_false(dctx.ref)
        raise NotImplementedError(
            "cross-context rebuild: Bool constant with no determinate value"
        )
    text = lib.Z3_get_numeral_string(src_ctx.ref, src_ast)
    if k == "String":
        # A string literal's "value" is its characters; the EMPTY string ("") is
        # a perfectly valid value for which Z3_get_numeral_string returns "".
        # Do not treat that as "unreadable".
        sval = text.decode() if text else ""
        return lib.Z3_mk_string(dctx.ref, sval.encode())
    if not text:
        raise NotImplementedError(
            f"cross-context rebuild: numeral of sort {k} has no readable value"
        )
    text = text.decode()
    dsort = _rebuild_sort_in_ctx(sort, dctx)
    return lib.Z3_mk_numeral(dctx.ref, text.encode(), dsort.handle)


def _rebuild_app(src_ast, src_ctx, dctx, cache):
    """Rebuild an application/operator node in dctx, recursing into args."""
    # A DECLARED 0-arity constant reports Z3_APP_AST (the stock-z3 shape the C
    # ABI now matches; only a `__db` de-Bruijn bound var is Z3_VAR_AST). Route
    # it through the per-context constant registry FIRST — by handle, exactly
    # as the old Z3_VAR_AST path did — so a user const whose NAME collides with
    # a builtin operator (e.g. Bool("and")) can never be misread as that op.
    if src_ast in src_ctx._const_meta:
        return _rebuild_const(src_ast, src_ctx, dctx)
    decl = lib.Z3_get_app_decl(src_ctx.ref, src_ast)
    if not decl:
        raise NotImplementedError(
            "cross-context rebuild: application node has no decl (handle "
            f"{src_ast})"
        )
    sym = lib.Z3_get_decl_name(src_ctx.ref, decl)
    name = lib.Z3_get_symbol_string(src_ctx.ref, sym)
    name = name.decode() if name else ""
    decl_kind = lib.Z3_get_decl_kind(src_ctx.ref, decl)
    # DEFENSE IN DEPTH: an array-combinator term (map application / Ext
    # witness) that somehow missed its registry must fail closed here — the
    # generic paths below would rebuild it as a plain UF / bare const,
    # silently dropping the select rewrite resp. the extensionality axiom (a
    # wrong-verdict channel). Registered terms never reach this point
    # (`_rebuild_ast` consults the registries first).
    if (
        name.startswith("map[")
        or name.startswith("!ay.array-ext!")
        or name.startswith("as-array[")
    ):
        raise NotImplementedError(
            f"cross-context rebuild: internal array-combinator term {name!r} "
            "is not in this context's Map/Ext registry; rebuilding it "
            "generically would drop its semantics"
        )
    nargs = lib.Z3_get_app_num_args(src_ctx.ref, src_ast)
    args = [
        _rebuild_ast(lib.Z3_get_app_arg(src_ctx.ref, src_ast, i), src_ctx, dctx, cache)
        for i in range(nargs)
    ]
    if decl_kind == _lib.Z3_OP_FINITE_SET_EMPTY:
        src_sort = _value_sort_from_ast(src_ast, src_ctx)
        dst_sort = _rebuild_sort_in_ctx(src_sort, dctx)
        return lib.Z3_mk_finite_set_empty(dctx.ref, dst_sort.handle)
    finite_set_builders = {
        _lib.Z3_OP_FINITE_SET_SINGLETON: lambda: lib.Z3_mk_finite_set_singleton(
            dctx.ref, args[0]
        ),
        _lib.Z3_OP_FINITE_SET_UNION: lambda: lib.Z3_mk_finite_set_union(
            dctx.ref, args[0], args[1]
        ),
        _lib.Z3_OP_FINITE_SET_INTERSECT: lambda: lib.Z3_mk_finite_set_intersect(
            dctx.ref, args[0], args[1]
        ),
        _lib.Z3_OP_FINITE_SET_DIFFERENCE: lambda: lib.Z3_mk_finite_set_difference(
            dctx.ref, args[0], args[1]
        ),
        _lib.Z3_OP_FINITE_SET_IN: lambda: lib.Z3_mk_finite_set_member(
            dctx.ref, args[0], args[1]
        ),
        _lib.Z3_OP_FINITE_SET_SIZE: lambda: lib.Z3_mk_finite_set_size(
            dctx.ref, args[0]
        ),
        _lib.Z3_OP_FINITE_SET_SUBSET: lambda: lib.Z3_mk_finite_set_subset(
            dctx.ref, args[0], args[1]
        ),
        _lib.Z3_OP_FINITE_SET_MAP: lambda: lib.Z3_mk_finite_set_map(
            dctx.ref, args[0], args[1]
        ),
        _lib.Z3_OP_FINITE_SET_FILTER: lambda: lib.Z3_mk_finite_set_filter(
            dctx.ref, args[0], args[1]
        ),
        _lib.Z3_OP_FINITE_SET_RANGE: lambda: lib.Z3_mk_finite_set_range(
            dctx.ref, args[0], args[1]
        ),
    }
    finite_set_builder = finite_set_builders.get(decl_kind)
    if finite_set_builder is not None:
        return finite_set_builder()
    # re.loop is an indexed operator: its repetition bounds live in the decl's
    # integer parameters, not the argument list. Recover them from the source
    # decl and rebuild via the indexed builder in dctx.
    if name == "re.loop":
        nparams = lib.Z3_get_decl_num_parameters(src_ctx.ref, decl)
        lo = lib.Z3_get_decl_int_parameter(src_ctx.ref, decl, 0) if nparams >= 1 else 0
        hi = lib.Z3_get_decl_int_parameter(src_ctx.ref, decl, 1) if nparams >= 2 else lo
        return lib.Z3_mk_re_loop(dctx.ref, args[0], int(lo), int(hi))
    # Indexed bitvector operators (B-10) carry their sizes as decl integer
    # parameters rather than argument asts; recover them and rebuild via the
    # matching parametric FFI builder in dctx.
    ip = _REBUILD_INDEXED_BV.get(name)
    if ip is not None:
        nparams = lib.Z3_get_decl_num_parameters(src_ctx.ref, decl)
        params = [lib.Z3_get_decl_int_parameter(src_ctx.ref, decl, i)
                  for i in range(nparams)]
        return ip(dctx, args[0], params)
    # const-array (K): the array's DOMAIN sort is implicit in the RESULT sort,
    # not in the argument list, so recover it from the source term's sort and
    # rebuild the const array (all-cells-equal-to-value) in dctx.
    if name == "const-array":
        src_sort = _value_sort_from_ast(src_ast, src_ctx)
        dom = _rebuild_sort_in_ctx(src_sort.domain_sort, dctx)
        return lib.Z3_mk_const_array(dctx.ref, dom.handle, args[0])
    # A USER-declared function whose NAME collides with a builtin operator
    # (e.g. `Function("is_int", RealSort(), BoolSort())`, or `to_real` — the
    # operators SMT-LIB/AY leave user-declarable) must rebuild as its
    # UNINTERPRETED application, never through the builtin builder in
    # `_REBUILD_OPS`. AY's C ABI reports the same decl kind (528) for the UF and
    # the builtin `is_int`, so the only reliable signal is the source context's
    # user func-decl registry: a name present there was `declare`d by the user
    # and denotes their free function. Rebuilding it via the builtin builder
    # (`Z3_mk_is_int`) forged the integrality predicate, which the `is_int`
    # quantifier eliminator then decided `unsat` where z3 exhibits a model
    # (`is_int ≡ λx.true`) — a wrong verdict. Mirrors the const-registry-first
    # discipline above (a declared const never misread as a builtin op).
    # (#isint-shadow)
    if name not in src_ctx._funcdecl_meta:
        builder = _REBUILD_OPS.get(name)
        if builder is not None:
            return builder(dctx, args, src_ast)
    # FP nodes that need the SOURCE term's sort (NaN/±oo/±zero specials, FP
    # numerals and `to_fp` conversions) plus the rounding-mode values; the
    # sort-agnostic fp.* operators rebuild through _REBUILD_OPS above.
    from .fp import _rebuild_fp_app
    fp_ast = _rebuild_fp_app(name, decl, src_ast, src_ctx, dctx, args)
    if fp_ast is not None:
        return fp_ast
    # Datatype constructor / recognizer / accessor application: re-route through
    # the datatype's op in dctx (re-declaring the datatype there if needed), so
    # the rebuilt term stays a real datatype op rather than an opaque UF.
    dt_app = _rebuild_datatype_app(name, src_ctx, dctx, args)
    if dt_app is not None:
        return dt_app
    # A nullary uninterpreted application is a declared CONSTANT, not a
    # function: since the Z3_VAR_AST fix, declared consts are nullary
    # Z3_APP_AST (not VAR), so they never reach _rebuild_const and are absent
    # from _funcdecl_meta. Rebuild by name+sort exactly as _rebuild_const does.
    # This is what makes the single most canonical z3py idiom
    #   x = Int('x'); s = Solver(); s.add(x > 0)
    # work when the fresh Solver owns a different context. Guard on
    # Z3_OP_UNINTERPRETED so a builtin nullary (pi, seq.empty, re.none, …) is
    # never misread as a fresh uninterpreted const — that would be a WRONG term.
    if nargs == 0 and decl_kind == _lib.Z3_OP_UNINTERPRETED:
        # A 0-ary RECURSIVE function's application (RecFunction with no
        # parameters) is exactly the nullary-app shape the declared-constant
        # path below would capture — which would rebuild it as a plain const
        # and silently DROP its definition in dctx (a wrong-`sat` source).
        # Route it through the rec-aware funcdecl rebuild instead: the
        # definition is replayed into dctx, or the rebuild fails closed.
        rfd = src_ctx._funcdecl_meta.get(name)
        if rfd is not None and getattr(rfd, "_is_rec", False) \
                and not rfd.domain_sorts:
            dfd = _rebuild_funcdecl_in_ctx(rfd, dctx)
            return lib.Z3_mk_app(dctx.ref, dfd.handle, 0, None)
        meta = src_ctx._const_meta.get(src_ast)
        if meta is not None:
            cname, csort = meta
        else:
            cname, csort = name, _value_sort_from_ast(src_ast, src_ctx)
        dsort = _rebuild_sort_in_ctx(csort, dctx)
        sym0 = lib.Z3_mk_string_symbol(dctx.ref, cname.encode())
        dconst = lib.Z3_mk_const(dctx.ref, sym0, dsort.handle)
        dctx._const_meta[dconst] = (cname, dsort)
        return dconst
    # Not a built-in operator: treat as an uninterpreted-function application.
    # Recover the declaration from the per-context registry (by name) so the
    # rebuilt application uses a func_decl with the right domain/range in dctx.
    fd = src_ctx._funcdecl_meta.get(name)
    if fd is None:
        raise NotImplementedError(
            f"cross-context rebuild: unsupported operator/function {name!r} "
            f"(arity {nargs})"
        )
    dfd = _rebuild_funcdecl_in_ctx(fd, dctx)
    arr = (_lib.Z3_ast * nargs)(*args)
    return lib.Z3_mk_app(dctx.ref, dfd.handle, nargs, arr)


def _rebuild_cache_for(dctx, src_ctx):
    """The src_ctx -> dst ast rebuild memo held by `dctx`, epoch-checked.

    `src_ctx._rebuild_epoch` is bumped whenever a recursive definition over
    src_ctx is REPLACED (RecAddDefinition again): a memoized dst ast may embed
    an application of the redefined function, and serving it from the memo
    would bypass `_rebuild_app` — and with it the decl-level definition
    refresh — leaving `dctx` deciding goals with the STALE definition (a wrong
    verdict). A stale epoch therefore drops the memo and refreshes the rebuilt
    declaration and body.
    """
    epoch = getattr(src_ctx, "_rebuild_epoch", 0)
    entry = dctx._rebuild_cache.get(src_ctx)
    if entry is None or entry[0] != epoch:
        entry = (epoch, {})
        dctx._rebuild_cache[src_ctx] = entry
    return entry[1]


def _replay_rec_def_in_ctx(fd, dfd, dctx):
    """Replay `fd`'s recursive definition (args, body) onto `dfd`, a rec decl
    living in dctx: rebuild the stored args/body into dctx and Z3_add_rec_def
    them there (Z3_add_rec_def is transactional and REJECTS a name dctx has
    already defined — on error dctx keeps its consistent definition and the
    caller's rollback path raises rather than silently proceeding).

    The caller must have registered `dfd` in `dctx._funcdecl_meta` and stamped
    `dfd._rec_src_version` BEFORE calling, so self/mutual occurrences inside
    the body resolve to `dfd` as current instead of recursing forever."""
    src_args, src_body = fd._rec_def
    n = len(fd.domain_sorts)
    cache = _rebuild_cache_for(dctx, fd.ctx)
    dargs = [
        _wrap(_rebuild_ast(a.ast, fd.ctx, dctx, cache),
              _rebuild_sort_in_ctx(a.sort_ref, dctx), dctx)
        for a in src_args
    ]
    dbody = _wrap(_rebuild_ast(src_body.ast, fd.ctx, dctx, cache),
                  _rebuild_sort_in_ctx(src_body.sort_ref, dctx), dctx)
    arr = (_lib.Z3_ast * n)(*[a.ast for a in dargs]) if n else None
    lib.Z3_add_rec_def(dctx.ref, dfd.handle, n, arr, dbody.ast)
    dctx.check_error("cross-context RecAddDefinition replay")
    dfd._rec_def = (dargs, dbody)


def _rebuild_funcdecl_in_ctx(fd, dctx):
    """Rebuild a FuncDeclRef in dctx (cached by name in the dctx registry).

    A RECURSIVE decl (`RecFunction`) is NEVER rebuilt as a plain uninterpreted
    function — that would silently drop its definition in dctx and could
    certify a wrong `sat` there. With a stored definition, the decl AND the
    definition are replayed into dctx (the decl is registered in
    `dctx._funcdecl_meta` BEFORE the body is rebuilt, which memo-terminates
    self- and mutual recursion); without one, the rebuild fails closed by
    raising.
    """
    existing = dctx._funcdecl_meta.get(fd._name)
    if existing is not None:
        if getattr(fd, "_is_rec", False):
            if not getattr(existing, "_is_rec", False):
                # The name exists in dctx as a PLAIN uninterpreted function
                # (declared before the source decl became recursive). Returning
                # it would apply the rec decl's uses as a plain UF there — a
                # dropped-definition wrong-`sat` source. Fail closed.
                raise NotImplementedError(
                    f"cross-context rebuild: {fd._name!r} is recursive in its "
                    "source context but already exists as a plain "
                    "uninterpreted function in the target context"
                )
            if fd._rec_def is not None and (
                getattr(existing, "_rec_src_version", None)
                != getattr(fd, "_rec_version", None)
            ):
                # The source definition was REPLACED (RecAddDefinition again)
                # after dctx replayed an earlier version. Re-replay the current
                # one (AY's Z3_add_rec_def replaces): a STALE definition must
                # never decide a goal in dctx. The version is stamped BEFORE
                # the body replay so self/mutual occurrences inside the body
                # resolve to `existing` as current instead of recursing; on
                # failure it is rolled back (Z3_add_rec_def is transactional,
                # so dctx still holds the old, consistent definition).
                old_ver = getattr(existing, "_rec_src_version", None)
                old_def = getattr(existing, "_rec_def", None)
                existing._rec_src_version = fd._rec_version
                try:
                    _replay_rec_def_in_ctx(fd, existing, dctx)
                except BaseException:
                    existing._rec_src_version = old_ver
                    existing._rec_def = old_def
                    raise
        return existing
    domain = [_rebuild_sort_in_ctx(s, dctx) for s in fd.domain_sorts]
    rng = _rebuild_sort_in_ctx(fd.range_sort, dctx)
    sym = lib.Z3_mk_string_symbol(dctx.ref, fd._name.encode())
    n = len(domain)
    dom_arr = (_lib.Z3_sort * n)(*[s.handle for s in domain]) if n else None
    if getattr(fd, "_is_rec", False):
        if getattr(fd, "_rec_def", None) is None:
            raise NotImplementedError(
                f"cross-context rebuild: recursive function {fd._name!r} has "
                "no definition yet (RecAddDefinition was not called); "
                "rebuilding it as a plain uninterpreted function would drop "
                "its recursive semantics — define it before asserting across "
                "contexts"
            )
        handle = lib.Z3_mk_rec_func_decl(dctx.ref, sym, n, dom_arr, rng.handle)
        if not handle:
            dctx.check_error("cross-context rec func_decl rebuild")
            raise NotImplementedError(
                "cross-context rebuild: could not redeclare recursive "
                f"function {fd._name!r}"
            )
        dfd = FuncDeclRef(handle, fd._name, domain, rng, dctx)
        dfd._is_rec = True
        dfd._rec_def = None
        # Stamp the replayed version BEFORE the body replay: a recursive
        # occurrence of this name inside the body (self- or mutual recursion)
        # hits the `existing` fast path above and must be seen as CURRENT
        # (same version), not re-replayed into an infinite regress.
        dfd._rec_src_version = getattr(fd, "_rec_version", 0)
        # Register BEFORE replaying the body: a recursive occurrence of this
        # name inside the body (self- or mutual recursion) then resolves to
        # `dfd` via the `existing` fast path above instead of recursing
        # forever.
        _register_funcdecl(dfd)
        try:
            _replay_rec_def_in_ctx(fd, dfd, dctx)
        except BaseException:
            # Never leave a half-built rec decl behind: a definition-less rec
            # entry in `dctx._funcdecl_meta` would satisfy the `existing` fast
            # path on the NEXT rebuild and let the function be used in dctx
            # with its definition silently missing (an unsound window). Roll
            # the registration back and re-raise — the failed assert reaches
            # the caller loudly and nothing half-defined persists.
            if dctx._funcdecl_meta.get(fd._name) is dfd:
                del dctx._funcdecl_meta[fd._name]
            raise
        return dfd
    handle = lib.Z3_mk_func_decl(dctx.ref, sym, n, dom_arr, rng.handle)
    if not handle:
        dctx.check_error("cross-context func_decl rebuild")
        raise NotImplementedError(
            f"cross-context rebuild: could not redeclare function {fd._name!r}"
        )
    dfd = FuncDeclRef(handle, fd._name, domain, rng, dctx)
    _register_funcdecl(dfd)
    return dfd


def _rebuild_quantifier(src_ast, src_ctx, dctx, cache):
    """Rebuild a forall/exists in dctx, reconstructing its bound consts."""
    nbound = lib.Z3_get_quantifier_num_bound(src_ctx.ref, src_ast)
    if nbound == 0:
        raise NotImplementedError(
            "cross-context rebuild: quantifier with no bound variables"
        )
    bound_asts = []
    for i in range(nbound):
        bn = lib.Z3_get_quantifier_bound_name(src_ctx.ref, src_ast, i)
        name = lib.Z3_get_symbol_string(src_ctx.ref, bn)
        name = name.decode() if name else None
        if not name:
            raise NotImplementedError(
                "cross-context rebuild: quantifier bound var without a name"
            )
        bs = lib.Z3_get_quantifier_bound_sort(src_ctx.ref, src_ast, i)
        sort = _sort_from_handle(bs, src_ctx)
        dsort = _rebuild_sort_in_ctx(sort, dctx)
        sym = lib.Z3_mk_string_symbol(dctx.ref, name.encode())
        dconst = lib.Z3_mk_const(dctx.ref, sym, dsort.handle)
        dctx._const_meta[dconst] = (name, dsort)
        bound_asts.append(dconst)
        # The body in the SOURCE context references the same hash-consed const
        # for this bound var; register a cache entry so the body's references
        # rebuild to this exact destination const.
        src_const = lib.Z3_mk_const(
            src_ctx.ref, lib.Z3_mk_string_symbol(src_ctx.ref, name.encode()),
            sort.handle,
        )
        cache[src_const] = dconst
    body_src = lib.Z3_get_quantifier_body(src_ctx.ref, src_ast)
    body_dst = _rebuild_ast(body_src, src_ctx, dctx, cache)
    is_forall = lib.Z3_is_quantifier_forall(src_ctx.ref, src_ast)
    mk = lib.Z3_mk_forall_const if is_forall else lib.Z3_mk_exists_const
    arr = (_lib.Z3_ast * nbound)(*bound_asts)
    return mk(dctx.ref, 0, nbound, arr, 0, None, body_dst)


def _rebuild_ast(src_ast, src_ctx, dctx, cache):
    """Recursively rebuild a single source AST handle in dctx.

    `cache` maps a source AST handle -> destination handle, so shared subterms
    are rebuilt once and term identity is preserved (and quantifier bound vars
    resolve to the bound const we created).
    """
    if src_ast == 0:
        raise NotImplementedError("cross-context rebuild: null AST")
    hit = cache.get(src_ast)
    if hit is not None:
        return hit
    # Array-combinator terms rebuild through their DEDICATED FFI builders,
    # never through the generic const/UF paths (see Context.__init__ for why
    # the naive rebuilds are wrong-verdict channels). Checked BEFORE the kind
    # dispatch: the Ext witness reads as a declared const and the Map term as
    # an app, and both generic paths would either raise or — worse — silently
    # drop the combinator's semantics.
    as_array = src_ctx._as_array_meta.get(src_ast)
    if as_array is not None:
        dfd = _rebuild_funcdecl_in_ctx(as_array, dctx)
        dast = lib.Z3_mk_as_array(dctx.ref, dfd.handle)
        dctx.check_error("cross-context AsArray rebuild")
        if dast == 0:
            raise NotImplementedError(
                "cross-context rebuild: AsArray produced a null term"
            )
        # Preserve the declaration metadata across rebuild chains.
        dctx._as_array_meta[dast] = dfd
        cache[src_ast] = dast
        return dast
    ext = src_ctx._ext_meta.get(src_ast)
    if ext is not None:
        ea, eb = ext
        da = _rebuild_ast(ea.ast, src_ctx, dctx, cache)
        db = _rebuild_ast(eb.ast, src_ctx, dctx, cache)
        dast = lib.Z3_mk_array_ext(dctx.ref, da, db)
        dctx.check_error("cross-context Ext rebuild")
        if dast == 0:
            raise NotImplementedError("cross-context rebuild: Ext produced a null term")
        # Register the rebuilt wrappers so a further rebuild out of dctx also
        # re-derives (rebuild chains stay sound).
        dctx._ext_meta[dast] = (
            _wrap(da, _rebuild_sort_in_ctx(ea.sort_ref, dctx), dctx),
            _wrap(db, _rebuild_sort_in_ctx(eb.sort_ref, dctx), dctx),
        )
        cache[src_ast] = dast
        return dast
    mm = src_ctx._map_meta.get(src_ast)
    if mm is not None:
        mf, margs = mm
        dfd = _rebuild_funcdecl_in_ctx(mf, dctx)
        dargs = [_rebuild_ast(a.ast, src_ctx, dctx, cache) for a in margs]
        arr = (_lib.Z3_ast * len(dargs))(*dargs)
        dast = lib.Z3_mk_map(dctx.ref, dfd.handle, len(dargs), arr)
        dctx.check_error("cross-context Map rebuild")
        if dast == 0:
            raise NotImplementedError("cross-context rebuild: Map produced a null term")
        dctx._map_meta[dast] = (
            dfd,
            tuple(
                _wrap(d, _rebuild_sort_in_ctx(a.sort_ref, dctx), dctx)
                for d, a in zip(dargs, margs)
            ),
        )
        cache[src_ast] = dast
        return dast
    kind = lib.Z3_get_ast_kind(src_ctx.ref, src_ast)
    if kind == _lib.Z3_NUMERAL_AST:
        dast = _rebuild_numeral(src_ast, src_ctx, dctx)
    elif kind == _lib.Z3_VAR_AST:
        dast = _rebuild_const(src_ast, src_ctx, dctx)
    elif kind == _lib.Z3_APP_AST:
        dast = _rebuild_app(src_ast, src_ctx, dctx, cache)
    elif kind == _lib.Z3_QUANTIFIER_AST:
        dast = _rebuild_quantifier(src_ast, src_ctx, dctx, cache)
    else:
        raise NotImplementedError(
            f"cross-context rebuild: unsupported AST kind {kind}"
        )
    if dast == 0:
        dctx.check_error("cross-context rebuild")
        raise NotImplementedError(
            "cross-context rebuild produced a null term for AST handle "
            f"{src_ast} (kind {kind})"
        )
    cache[src_ast] = dast
    return dast


def _rebuild_expr(expr, dctx):
    """Rebuild an AstRef in destination context `dctx`, returning a new AstRef.

    Used transparently when a constraint built in one context is asserted into a
    Solver/Optimize in another. The implementation reconstructs AY's stored,
    eagerly normalized structure using the per-node mappings above. It raises
    `NotImplementedError`, naming the offending node, when a kind cannot be
    rebuilt.

    The per-source-context rebuild memo lives on `dctx` (keyed by the source
    Context OBJECT, not its id) so it is reused across calls — preserving
    shared-subterm identity — while never outliving either context.
    """
    if expr.ctx is dctx:
        return expr
    cache = _rebuild_cache_for(dctx, expr.ctx)
    dast = _rebuild_ast(expr.ast, expr.ctx, dctx, cache)
    sort = _rebuild_sort_in_ctx(expr.sort_ref, dctx)
    out = _wrap(dast, sort, dctx)
    # Preserve a declared constant's name on the rebuilt wrapper so model
    # lookups (m[x]) and unsat-core matching keep working across the rebuild.
    if expr.decl_name is not None:
        out.decl_name = expr.decl_name
        dctx._const_meta[dast] = (expr.decl_name, sort)
    return out


def _adopt(expr, dctx):
    """Return `expr` if already in dctx, else its rebuilt copy in dctx."""
    if not isinstance(expr, AstRef):
        return expr
    if expr.ctx is dctx:
        return expr
    return _rebuild_expr(expr, dctx)


def _coerce_soft_weight(weight):
    """Coerce an add_soft `weight` to a non-negative int (AY's weight-exact domain).

    Accepts an int, an integral float (e.g. 3.0), or an integer string ("3").
    A genuinely fractional weight (0.5, "1/2") raises NotImplementedError: AY's
    MaxSMT is exact over non-negative integer weights and cannot represent a
    fractional penalty — an honest error, never a silent rounding.
    """
    if isinstance(weight, bool):
        raise NotImplementedError("add_soft weight must be numeric, not bool")
    if isinstance(weight, numbers.Integral):
        w = int(weight)
    elif isinstance(weight, float):
        if not weight.is_integer():
            raise NotImplementedError(
                f"add_soft fractional weight {weight!r} is unsupported: AY's MaxSMT "
                "is weight-exact over non-negative integer weights only"
            )
        w = int(weight)
    elif isinstance(weight, str):
        try:
            w = int(weight)
        except ValueError:
            raise NotImplementedError(
                f"add_soft weight string {weight!r} is not an integer: AY's MaxSMT "
                "is weight-exact over non-negative integer weights only"
            )
    else:
        raise NotImplementedError(
            f"add_soft weight must be an int, integral float, or integer string, "
            f"got {weight!r}"
        )
    if w < 0:
        raise NotImplementedError(f"add_soft weight must be non-negative, got {w}")
    return w


def _ast_vector_to_list(vec, ctx):
    """Materialize a Z3_ast_vector handle into a Python list of AstRef."""
    if not vec:
        return []
    n = lib.Z3_ast_vector_size(ctx.ref, vec)
    out = []
    for i in range(n):
        a = lib.Z3_ast_vector_get(ctx.ref, vec, i)
        if a == 0:
            continue
        out.append(_wrap_from_ast(a, ctx))
    return out


def _bool_ast_vector_to_list(vec, ctx):
    """Materialize a Z3_ast_vector KNOWN to hold boolean formulas into BoolRefs.

    Used for the solver-introspection getters (units / non_units / trail /
    consequences) whose elements are boolean literals/clauses/implications by
    definition. We wrap each with the Bool sort directly rather than inferring it
    via Z3_get_sort: AY's C ABI can mis-report the sort of a normalized clause
    pulled from an internal vector (e.g. an `Or(...)` consequence reads back as
    Int), which would wrongly wrap it as an ArithRef. Forcing the definitionally-
    correct Bool sort keeps `Not(e)`/boolean composition on these results sound.
    """
    if not vec:
        return []
    bsort = _bool_sort(ctx)
    n = lib.Z3_ast_vector_size(ctx.ref, vec)
    out = []
    for i in range(n):
        a = lib.Z3_ast_vector_get(ctx.ref, vec, i)
        if a == 0:
            continue
        out.append(_wrap(a, bsort, ctx))
    return out


def _raw_ast_string(val):
    """AY's raw textual form for an AST (the opaque `(ast N : Int)` fallback)."""
    s = lib.Z3_ast_to_string(val.ctx.ref, val.ast)
    return s.decode() if s else f"<ast {val.ast}>"


def _render_model_value(val):
    """Render an AstRef model value the way z3py prints it inside a model.

    z3py prints `[x = 4, b = True, r = 1/2, st = "hi"]`: numbers bare, Bool as
    Python True/False, strings double-quoted. AY's own `Z3_ast_to_string` on a
    model value yields an opaque `(ast N : Int)` handle string, so we render the
    value honestly from its concrete content instead.

    NOTE: never delegates to `repr(val)` for the fallback — a model value's
    __repr__ routes back here, so we use the raw AST string directly to avoid
    recursion.
    """
    if val is None:
        return "None"
    kind = val.sort_ref.kind
    if kind == "Bool":
        b = val.as_bool()
        # An undetermined Bool (no concrete value) falls back to the AST repr.
        return {True: "True", False: "False"}.get(b, _raw_ast_string(val))
    if kind == "String":
        try:
            return '"' + val.as_string() + '"'
        except AyZ3Exception:
            return _raw_ast_string(val)
    if kind in ("Int", "Real", "BitVec"):
        text = lib.Z3_get_numeral_string(val.ctx.ref, val.ast)
        if not text:
            return _raw_ast_string(val)
        text = text.decode()
        # z3py renders a whole-number Real as `2`, not `2/1`; match it.
        if kind == "Real" and text.endswith("/1"):
            text = text[:-2]
        return text
    if kind == "Datatype":
        return _render_datatype_value(val)
    if kind == "FloatingPoint":
        from .fp import _fp_ref_fields, _fp_value_str
        fields = _fp_ref_fields(val)
        if fields is not None:
            return _fp_value_str(*fields, val.sort_ref.ebits(), val.sort_ref.sbits())
        return _raw_ast_string(val)
    # Arrays and any other sort: fall back to AY's textual form (honest, even if
    # it is not byte-identical to z3py's array lambda printing).
    return _raw_ast_string(val)


def _render_datatype_value(val):
    """Render a datatype model value in z3py's `ctor(a, b, ...)` form.

    A nullary constructor (enum literal) renders as the bare constructor name
    (`blue`, `none`); an n-ary constructor as `ctor(arg0, arg1, ...)` with each
    argument rendered as its own concrete model value (recursively, so nested
    datatypes print z3py-identically, e.g. `some(cons(1, nil))`). AY's own text
    for the same value is the SMT-LIB prefix form `(ctor a b)`; this reshapes it
    to z3py's surface form without changing the value.
    """
    ctx = val.ctx
    is_app = lib.Z3_is_app(ctx.ref, val.ast)
    nargs = lib.Z3_get_app_num_args(ctx.ref, val.ast) if is_app else 0
    if nargs == 0:
        # Nullary constructor (a VAR node): its raw text IS the constructor name.
        return _raw_ast_string(val)
    decl = lib.Z3_get_app_decl(ctx.ref, val.ast)
    cname = ""
    if decl:
        sym = lib.Z3_get_decl_name(ctx.ref, decl)
        raw = lib.Z3_get_symbol_string(ctx.ref, sym) if sym else None
        cname = raw.decode() if raw else ""
    if not cname:
        return _raw_ast_string(val)
    parts = []
    for i in range(nargs):
        arg = lib.Z3_get_app_arg(ctx.ref, val.ast, i)
        parts.append(_render_datatype_field(arg, ctx))
    return f"{cname}(" + ", ".join(parts) + ")"


def _render_datatype_field(arg, ctx):
    """Render one constructor-argument value inside a datatype model value.

    A field value carried inside a datatype constructor can have its sort
    reported as UNKNOWN by AY's C ABI (a datatype-arg-sort quirk), so we detect
    a Boolean value directly (z3py prints `True`/`False`, not `true`/`false`)
    before delegating to the generic model-value renderer (which handles
    numerals and nested constructor values).
    """
    bv = lib.Z3_get_bool_value(ctx.ref, arg)
    if bv == _lib.Z3_L_TRUE:
        return "True"
    if bv == _lib.Z3_L_FALSE:
        return "False"
    argref = _wrap_from_ast(arg, ctx)
    argref._is_model_value = True
    return _render_model_value(argref)


def _mark_model_value(val):
    """Tag a wrapped AstRef as a model value so it renders concretely."""
    if val is not None:
        val._is_model_value = True
    return val


def _is_concrete_value(val):
    """Whether a model-value AstRef reduced to a concrete (renderable) value.

    A concrete value is a numeral (Int/Real/BitVec), a determined Bool, or a
    String literal. An expression that did NOT reduce (e.g. an unconstrained
    var with model_completion=False) stays an opaque AST; we report that
    honestly rather than pretending it is a value.
    """
    kind = val.sort_ref.kind
    if kind in ("Int", "Real", "BitVec"):
        return bool(lib.Z3_get_numeral_string(val.ctx.ref, val.ast))
    if kind == "Bool":
        return val.as_bool() is not None
    if kind == "String":
        try:
            val.as_string()
            return True
        except AyZ3Exception:
            return False
    if kind == "FloatingPoint":
        from .fp import _fp_ref_fields
        return _fp_ref_fields(val) is not None
    if kind == "RoundingMode":
        from .fp import is_fprm_value
        return is_fprm_value(val)
    # Arrays / other compound sorts: AY has no concrete readout, so treat as
    # non-concrete (honest); the value is still returned, just not claimed
    # concrete.
    return False


class ModelRef:
    def __init__(self, handle, ctx, hidden_prefixes=None):
        self.handle = handle
        self.ctx = ctx
        # Name prefixes whose constants are HIDDEN from decls()/len()/iteration
        # (but still eval-able). Used by Optimize.model() to suppress the
        # engine's internal MaxSMT relaxation vars (`__maxsmt_…`), which z3's
        # own Optimize.model() never surfaces. Empty for Solver models — their
        # enumeration is unchanged.
        self._hidden_prefixes = tuple(hidden_prefixes) if hidden_prefixes else ()

    def _is_hidden_name(self, name):
        return any(name.startswith(p) for p in self._hidden_prefixes)

    def eval(self, expr, model_completion=False):
        """Evaluate `expr` in this model, returning a concrete value where
        possible (z3py ModelRef.eval / m[expr]).

        Uses Z3_model_eval (with `model_completion` to fill unconstrained
        variables). The returned AstRef renders its CONCRETE content (numeral /
        Bool / string), matching z3py. If AY cannot reduce the expression to a
        value (e.g. completion off and the term mentions an unconstrained var),
        the honest, unreduced AST is returned rather than a fabricated value.
        """
        # Allow evaluating an expr built in another context (e.g. a top-level
        # shared var) against this model by rebuilding it in the model's ctx.
        expr = _adopt(expr, self.ctx)
        out = _lib.Z3_ast()
        ok = lib.Z3_model_eval(
            self.ctx.ref, self.handle, expr.ast, model_completion, ctypes.byref(out)
        )
        if not ok or out.value == 0:
            raise AyZ3Exception(
                "Z3_model_eval failed (expression not interpretable in model)"
            )
        sort = _value_sort_from_ast(out.value, self.ctx)
        val = _wrap(out.value, sort, self.ctx)
        # Only render as a concrete value if it genuinely reduced to one; a
        # concrete numeral is additionally returned as its z3py NumRef subtype.
        if _is_concrete_value(val):
            val = _as_numref(val)
            _mark_model_value(val)
        return val

    # z3py exposes the same operation under the name `evaluate`.
    def evaluate(self, expr, model_completion=False):
        return self.eval(expr, model_completion=model_completion)

    # --- z3py-style iteration over constant declarations -------------------

    def _const_decl_at(self, i):
        """Build a 0-arity FuncDeclRef for the i-th constant in the model."""
        d = lib.Z3_model_get_const_decl(self.ctx.ref, self.handle, i)
        sym = lib.Z3_get_decl_name(self.ctx.ref, d)
        name = lib.Z3_get_symbol_string(self.ctx.ref, sym)
        name = name.decode() if name else ""
        rng_h = lib.Z3_get_range(self.ctx.ref, d)
        rng = _sort_from_handle(rng_h, self.ctx) if rng_h else _int_sort(self.ctx)
        return FuncDeclRef(d, name, [], rng, self.ctx)

    def decls(self):
        """The constant declarations interpreted by this model (z3py decls())."""
        n = lib.Z3_model_get_num_consts(self.ctx.ref, self.handle)
        out = [self._const_decl_at(i) for i in range(n)]
        if self._hidden_prefixes:
            out = [d for d in out if not self._is_hidden_name(d._name)]
        return out

    def __len__(self):
        if self._hidden_prefixes:
            return len(self.decls())
        return lib.Z3_model_get_num_consts(self.ctx.ref, self.handle)

    def __iter__(self):
        """Iterate over the model's constant declarations (z3py `for d in m`)."""
        return iter(self.decls())

    def _interp_of_decl(self, decl):
        """Read a FuncDeclRef's constant interpretation as a value AstRef."""
        val = lib.Z3_model_get_const_interp(self.ctx.ref, self.handle, decl.handle)
        if val == 0:
            return None
        sort = _value_sort_from_ast(val, self.ctx)
        return _mark_model_value(_as_numref(_wrap(val, sort, self.ctx)))

    def _interp_by_name(self, name):
        n = lib.Z3_model_get_num_consts(self.ctx.ref, self.handle)
        for i in range(n):
            d = lib.Z3_model_get_const_decl(self.ctx.ref, self.handle, i)
            sym = lib.Z3_get_decl_name(self.ctx.ref, d)
            dname = lib.Z3_get_symbol_string(self.ctx.ref, sym)
            dname = dname.decode() if dname else ""
            if dname == name:
                val = lib.Z3_model_get_const_interp(self.ctx.ref, self.handle, d)
                if val == 0:
                    return None
                sort = _value_sort_from_ast(val, self.ctx)
                return _mark_model_value(_as_numref(_wrap(val, sort, self.ctx)))
        return None

    def __getitem__(self, decl):
        """Look up a value: `m[x]` (a const ref) or `m[d]` (a FuncDeclRef)."""
        if isinstance(decl, FuncDeclRef):
            if decl.arity() != 0:
                raise NotImplementedError(
                    "model indexing only supports 0-arity (constant) declarations"
                )
            return self._interp_of_decl(decl)
        if not isinstance(decl, AstRef):
            raise NotImplementedError(
                "model indexing expects an ayz3 constant expression or FuncDeclRef"
            )
        if decl.decl_name is None:
            raise NotImplementedError(
                "model indexing only supports declared constants "
                "(Int/Bool/Real/BitVec(name, ...)), not compound expressions; "
                "use model.eval(expr) instead"
            )
        return self._interp_by_name(decl.decl_name)

    def __repr__(self):
        """z3py-style `[x = 4, y = 6]`, in a stable (name-sorted) order.

        z3py prints values bare (numbers), Bool as True/False and strings
        quoted. We sort by declaration name for a deterministic repr (z3py's own
        order is engine-internal); the set of name=value pairs matches z3py.
        """
        entries = []
        for d in self.decls():
            val = self._interp_of_decl(d)
            entries.append((d.name(), _render_model_value(val)))
        entries.sort(key=lambda kv: kv[0])
        return "[" + ", ".join(f"{k} = {v}" for k, v in entries) + "]"

    def sexpr(self):
        """AY's raw SMT-LIB model text (z3py ModelRef.sexpr())."""
        s = lib.Z3_model_to_string(self.ctx.ref, self.handle)
        return s.decode() if s else ""


# ---------------------------------------------------------------------------
# Statistics
# ---------------------------------------------------------------------------

class Statistics:
    """z3py-shaped view over AY's REAL solver statistics (Solver.statistics()).

    Wraps a `Z3_stats` snapshot captured from a `check()`. Matches z3py's core
    surface: `len()`, `keys()`, `stats[int]` -> `(key, value)` pair,
    `get_key_value(key)`, attribute access (`stats.max_memory`), and a z3py-style
    `(:key val ...)` repr.

    ERGONOMIC SUPERSET (documented divergence, never breaks a z3py program):
    `stats[key]` also accepts a STRING key and returns the value directly, and
    `key in stats` / `.get(key)` are key-membership helpers. z3py raises on a
    string subscript and (having no `__contains__`) iterates `(key, value)`
    pairs for `in`, so these string-key forms only ADD behavior where z3py has
    none — no valid z3py usage changes meaning.

    HONESTY: every value is an ACTUAL AY solve counter (conflicts, decisions,
    propagations, memory, per-theory activity, ...). AY's counter SET differs
    from z3's — AY has counters z3 lacks (e.g. `nelson-oppen rounds`) and lacks
    some z3 has (e.g. `mk bool var`) — so the KEY NAMES are AY's honest counters,
    not a fabricated z3 key set. Values read as `int` (uint stats) or `float`
    (double stats).
    """

    def __init__(self, handle, ctx):
        self.handle = handle
        self.ctx = ctx
        lib.Z3_stats_inc_ref(ctx.ref, handle)

    def __del__(self):
        # Best-effort: at interpreter shutdown the lib/context may already be
        # torn down. The handle is arena-owned by the context anyway (dec_ref is
        # a bookkeeping no-op), so a failure here leaks nothing.
        try:
            lib.Z3_stats_dec_ref(self.ctx.ref, self.handle)
        except Exception:
            pass

    def __len__(self):
        return int(lib.Z3_stats_size(self.ctx.ref, self.handle))

    def key(self, idx):
        """Name of the statistic at position `idx`."""
        s = lib.Z3_stats_get_key(self.ctx.ref, self.handle, idx)
        return s.decode() if s else ""

    def keys(self):
        """List of statistic names (z3py Statistics.keys())."""
        return [self.key(i) for i in range(len(self))]

    def get_key_value(self, key):
        """Value of `key` as int (uint stat) or float (double stat).

        Raises AyZ3Exception for an unknown key (matches z3py).
        """
        for i in range(len(self)):
            if self.key(i) == key:
                if lib.Z3_stats_is_uint(self.ctx.ref, self.handle, i):
                    return int(lib.Z3_stats_get_uint_value(self.ctx.ref, self.handle, i))
                return float(lib.Z3_stats_get_double_value(self.ctx.ref, self.handle, i))
        raise AyZ3Exception(f"unknown statistics key: {key!r}")

    def __getitem__(self, key):
        """z3py: an INTEGER index returns a `(key, value)` pair.

        ayz3 also accepts a STRING key and returns just the value — an ergonomic
        superset. z3py raises `TypeError` for a string subscript, so no valid
        z3py program's behavior changes; int indexing keeps z3py's exact
        `(key, value)`-tuple semantics.
        """
        if isinstance(key, str):
            return self.get_key_value(key)
        idx = int(key)
        if idx < 0 or idx >= len(self):
            raise IndexError(f"statistics index out of range: {idx}")
        k = self.key(idx)
        if lib.Z3_stats_is_uint(self.ctx.ref, self.handle, idx):
            return (k, int(lib.Z3_stats_get_uint_value(self.ctx.ref, self.handle, idx)))
        return (k, float(lib.Z3_stats_get_double_value(self.ctx.ref, self.handle, idx)))

    def __contains__(self, key):
        return key in self.keys()

    def get(self, key, default=None):
        """Value of `key`, or `default` if absent (dict-style convenience)."""
        try:
            return self.get_key_value(key)
        except AyZ3Exception:
            return default

    def __getattr__(self, name):
        # z3py exposes stats as attributes with '_' standing in for spaces
        # (e.g. `stats.max_memory` -> the `max memory` key), and coerces an
        # integral float to int. Mirror that, then also try the raw name (AY's
        # dotted extra counters, e.g. `phase.solver_dispatch.seconds`).
        if name.startswith("_") or name in ("handle", "ctx"):
            raise AttributeError(name)
        for candidate in (name.replace("_", " "), name):
            try:
                val = self.get_key_value(candidate)
            except AyZ3Exception:
                continue
            if isinstance(val, float) and val.is_integer():
                return int(val)
            return val
        raise AttributeError(name)

    def __repr__(self):
        s = lib.Z3_stats_to_string(self.ctx.ref, self.handle)
        return s.decode() if s else "(:statistics)"


# ---------------------------------------------------------------------------
# Parameters (Params / ParamDescrs) and symbol helpers
# ---------------------------------------------------------------------------

def _to_symbol(name, ctx):
    """A Z3_symbol for `name`.

    z3py accepts a str or an int parameter/const name. AY's C ABI only exposes a
    string-symbol maker, so an int name is routed through its decimal string
    form (parameter names are strings in practice; this keeps the surface total).
    """
    if isinstance(name, numbers.Integral) and not isinstance(name, bool):
        return lib.Z3_mk_string_symbol(ctx.ref, str(int(name)).encode())
    return lib.Z3_mk_string_symbol(ctx.ref, str(name).encode())


def _symbol2py(ctx, sym):
    """Convert a Z3_symbol back to a Python str (string symbol) or int (int symbol)."""
    kind = lib.Z3_get_symbol_kind(ctx.ref, sym)
    if kind == _lib.Z3_INT_SYMBOL:
        return int(lib.Z3_get_symbol_int(ctx.ref, sym))
    s = lib.Z3_get_symbol_string(ctx.ref, sym)
    return s.decode() if s else ""


def _param_val_str(v):
    """Render a param value the way an SMT `(params ...)` block prints it."""
    if isinstance(v, bool):
        return "true" if v else "false"
    return str(v)


class ParamDescrsRef:
    """A queryable parameter-descriptor set (z3py `ParamDescrsRef`).

    Wraps a REAL `Z3_param_descrs` handle produced by `Tactic.param_descrs()` /
    `Optimize.param_descrs()`. Supports z3py's surface: `len()`, `get_name(i)`,
    `get_kind(name)`, `get_documentation(name)`, `pd[i]` (name) / `pd[name]`
    (kind), and a whole-set repr.

    HONESTY: every descriptor comes from AY's engine. A `Tactic`'s set is
    HONEST-EMPTY (size 0) — its tactics are equivalence-preserving with no tunable
    that changes the produced goal. An `Optimize`'s set lists the params AY
    genuinely accepts (e.g. `timeout`, `produce_proofs`, `priority`). AY's param
    SET differs from z3's, so the names are AY's real accepted params, never a
    fabricated z3 parameter list.
    """

    def __init__(self, descr, ctx):
        self.descr = descr
        self.ctx = ctx
        lib.Z3_param_descrs_inc_ref(ctx.ref, descr)

    def __del__(self):
        try:
            lib.Z3_param_descrs_dec_ref(self.ctx.ref, self.descr)
        except Exception:
            pass

    def size(self):
        """Number of parameters described (z3py ParamDescrsRef.size())."""
        return int(lib.Z3_param_descrs_size(self.ctx.ref, self.descr))

    def __len__(self):
        return self.size()

    def get_name(self, i):
        """Name of the parameter at position `i`."""
        if i < 0 or i >= self.size():
            raise IndexError(f"param-descr index out of range: {i}")
        sym = lib.Z3_param_descrs_get_name(self.ctx.ref, self.descr, ctypes.c_uint(i))
        return _symbol2py(self.ctx, sym)

    def get_kind(self, n):
        """Z3_param_kind (int) of the parameter named `n`."""
        sym = _to_symbol(n, self.ctx)
        return int(lib.Z3_param_descrs_get_kind(self.ctx.ref, self.descr, sym))

    def get_documentation(self, n):
        """Documentation string of the parameter named `n` (may be empty)."""
        sym = _to_symbol(n, self.ctx)
        s = lib.Z3_param_descrs_get_documentation(self.ctx.ref, self.descr, sym)
        return s.decode() if s else ""

    def __getitem__(self, arg):
        # z3py: an int index returns the NAME; a string returns the KIND.
        if isinstance(arg, numbers.Integral) and not isinstance(arg, bool):
            return self.get_name(int(arg))
        return self.get_kind(arg)

    def __repr__(self):
        s = lib.Z3_param_descrs_to_string(self.ctx.ref, self.descr)
        return s.decode() if s else "(param_descrs)"


# Alias so `ayz3.ParamDescrs` resolves like z3py's low-level name (both refer to
# the same descriptor-set wrapper here).
ParamDescrs = ParamDescrsRef


class ParamsRef:
    """A parameter set (z3py `ParamsRef`; construct via `Params()`).

    Backs a REAL `Z3_params` object. `set(name, val)` dispatches on the Python
    value type exactly like z3py — bool -> set_bool, int -> set_uint,
    float -> set_double, str -> set_symbol — and the object can be handed to
    `Solver.set(params)`, `Tactic.__call__(..., params)` etc.

    DIVERGENCE (documented, never faked): AY's C ABI has no `Z3_params_to_string`,
    so `__repr__` renders from a Python-side mirror of the values set on THIS
    object (exactly the values forwarded to the engine). It never invents engine
    state it cannot read back.
    """

    def __init__(self, ctx=None, params=None):
        self.ctx = ctx or _current_ctx()
        self.params = (
            params if params is not None else lib.Z3_mk_params(self.ctx.ref)
        )
        lib.Z3_params_inc_ref(self.ctx.ref, self.params)
        # Read-back / repr mirror of what was set (the ABI cannot enumerate a
        # Z3_params object's contents).
        self._mirror = {}

    def __del__(self):
        try:
            lib.Z3_params_dec_ref(self.ctx.ref, self.params)
        except Exception:
            pass

    def set(self, name, val):
        """Set parameter `name` to `val` (z3py ParamsRef.set)."""
        key = str(name)
        sym = _to_symbol(key, self.ctx)
        if isinstance(val, bool):
            lib.Z3_params_set_bool(self.ctx.ref, self.params, sym, ctypes.c_bool(val))
        elif isinstance(val, numbers.Integral):
            lib.Z3_params_set_uint(self.ctx.ref, self.params, sym, ctypes.c_uint(int(val)))
        elif isinstance(val, numbers.Real):
            lib.Z3_params_set_double(
                self.ctx.ref, self.params, sym, ctypes.c_double(float(val))
            )
        elif isinstance(val, str):
            lib.Z3_params_set_symbol(
                self.ctx.ref, self.params, sym, _to_symbol(val, self.ctx)
            )
        else:
            raise NotImplementedError(
                f"Params value for {name!r} must be bool/int/float/str, got {val!r}"
            )
        self._mirror[key] = val
        return self

    def __setitem__(self, name, val):
        self.set(name, val)

    def validate(self, ds):
        """Accept a ParamDescrsRef for signature parity (z3py ParamsRef.validate).

        DIVERGENCE (documented): AY has no `Z3_params_validate` and accepts any
        parameter name permissively, so this is a no-op that never rejects an
        unknown name. It still type-checks its argument like z3py.
        """
        if not isinstance(ds, ParamDescrsRef):
            raise TypeError("validate expects a ParamDescrsRef")

    def __repr__(self):
        body = " ".join(f"{k} {_param_val_str(v)}" for k, v in self._mirror.items())
        return f"(params{(' ' + body) if body else ''})"


def Params(ctx=None):
    """A fresh, empty parameter set (z3py `Params()`)."""
    return ParamsRef(ctx)


def args2params(arguments, keywords, ctx=None):
    """Build a `ParamsRef` from a flat ('k1', v1, 'k2', v2, ...) tuple plus
    keyword params (z3py `args2params`). Positional args must pair up."""
    if len(arguments) % 2 != 0:
        raise NotImplementedError(
            "args2params: positional arguments must be ('key', value) pairs"
        )
    r = ParamsRef(ctx)
    prev = None
    for a in arguments:
        if prev is None:
            prev = a
        else:
            r.set(prev, a)
            prev = None
    for k, v in keywords.items():
        r.set(k, v)
    return r


# ---------------------------------------------------------------------------
# Solver
# ---------------------------------------------------------------------------

_QUANTIFIED_ARRAY_REASON = (
    "quantified array reasoning is outside ayz3's soundly supported solver path"
)


def _contains_quantified_array(exprs, ctx):
    """Whether a formula quantifies over, or quantifies around, an array term.

    The native FFI route is not sound for this combination. Detect it at the
    wrapper boundary and return `unknown` instead of forwarding a query that
    could produce a wrong definitive verdict.
    """
    stack = [(expr.ast, False) for expr in exprs]
    seen = set()
    while stack:
        node, under_quantifier = stack.pop()
        key = (node, under_quantifier)
        if key in seen:
            continue
        seen.add(key)
        kind = lib.Z3_get_ast_kind(ctx.ref, node)
        if kind == _lib.Z3_QUANTIFIER_AST:
            for i in range(lib.Z3_get_quantifier_num_bound(ctx.ref, node)):
                sort = lib.Z3_get_quantifier_bound_sort(ctx.ref, node, i)
                if sort and lib.Z3_get_sort_kind(ctx.ref, sort) == _lib.Z3_ARRAY_SORT:
                    return True
            stack.append((lib.Z3_get_quantifier_body(ctx.ref, node), True))
            continue
        if kind != _lib.Z3_APP_AST:
            continue
        if under_quantifier:
            sort = lib.Z3_get_sort(ctx.ref, node)
            if sort and lib.Z3_get_sort_kind(ctx.ref, sort) == _lib.Z3_ARRAY_SORT:
                return True
        for i in range(lib.Z3_get_app_num_args(ctx.ref, node)):
            stack.append((lib.Z3_get_app_arg(ctx.ref, node, i), under_quantifier))
    return False


class Solver:
    # NOTE on isolation: every AY Z3_solver owns its own assertion stack at the
    # C level (independent per handle, matching Z3 — the multi-solver fix), so
    # Solvers are independent even when they share one Context. ayz3 still
    # binds each Solver to a Context for term-arena scoping (see `_solver_ctx`):
    #   * explicit ctx arg -> used as-is;
    #   * inside `with ctx_scope/using():` -> that scope's context (so the
    #     "build vars and solver in one scope" idiom needs no rebuild);
    #   * otherwise (top level) -> a FRESH Context per Solver.
    # Top-level Solvers are GENUINELY INDEPENDENT, like z3py:
    # `x=Int('x'); s1=Solver(); s2=Solver(); s1.add(x>0); s2.add(x<0)`
    # gives two independent sat solvers. A constraint built over a top-level var
    # (in `_main_ctx`) is TRANSPARENTLY REBUILT into the solver's own context on
    # `add` (see `_rebuild_expr`) — the rebuilt term is the same term AY would
    # build natively there. Two Solvers sharing ONE explicit Context are ALSO
    # independent now (each has its own C-level assertion stack).
    def __init__(self, ctx=None, _tactic_handle=None):
        self.ctx = _solver_ctx(ctx)
        # When built via Tactic.solver(), use Z3_mk_solver_from_tactic so the
        # (equivalence-preserving) tactic is applied to the goal before each
        # check. The verdict/model are identical to a plain solver's. Otherwise
        # a plain solver.
        if _tactic_handle is not None:
            self.handle = lib.Z3_mk_solver_from_tactic(self.ctx.ref, _tactic_handle)
            self.ctx.check_error("Solver.from_tactic")
            if not self.handle:
                raise AyZ3Exception("Z3_mk_solver_from_tactic returned null")
        else:
            self.handle = lib.Z3_mk_solver(self.ctx.ref)
        # Tracking literals registered via assert_and_track; their conjunction
        # forms the assumption set used to compute an unsat core.
        self._tracked = []
        # Auto-generated tracking-literal counter for assert_and_track(c) with a
        # string/auto name.
        self._track_counter = 0
        self._fail_closed_reason = None
        # Apply any process-wide defaults set via set_param (z3py semantics:
        # global params seed solvers created afterwards).
        if _global_params:
            self.set(**_global_params)

    def add(self, *args):
        for a in args:
            if isinstance(a, (list, tuple)):
                self.add(*a)
                continue
            if isinstance(a, bool):
                a = BoolVal(a, self.ctx)
            # FP constraints (fpEQ/fpLT/fpIsNaN/...) are ordinary native
            # BoolRefs over Z3_mk_fpa_* handles, so they flow through the
            # standard assert path below exactly like z3py.
            if not isinstance(a, BoolRef):
                raise NotImplementedError(
                    f"Solver.add expects Bool constraints, got {a!r}"
                )
            # Transparently rebuild a constraint built in another context into
            # this Solver's context, so a formula built once can be added to
            # multiple independent solvers (matches z3py).
            a = _adopt(a, self.ctx)
            lib.Z3_solver_assert(self.ctx.ref, self.handle, a.ast)

    def assert_exprs(self, *args):
        self.add(*args)

    # z3py aliases for add(): append / insert take one-or-more constraints and
    # add them to the assertion stack (identical semantics to add()).
    def append(self, *args):
        self.add(*args)

    def insert(self, *args):
        self.add(*args)

    def num_scopes(self):
        """Number of `push`es not yet `pop`ped (z3py Solver.num_scopes())."""
        return int(lib.Z3_solver_get_num_scopes(self.ctx.ref, self.handle))

    def using(self):
        """Context manager that makes this Solver's context the current one, so
        bare constructors (Int, Bool, ...) build expressions in it."""
        return _ctx_scope(self.ctx)

    def push(self):
        lib.Z3_solver_push(self.ctx.ref, self.handle)

    def pop(self, n=1):
        lib.Z3_solver_pop(self.ctx.ref, self.handle, n)

    def reset(self):
        lib.Z3_solver_reset(self.ctx.ref, self.handle)
        self._fail_closed_reason = None

    def assert_and_track(self, constraint, tracker):
        """Assert `constraint`, tracked by a boolean literal `tracker`.

        Mirrors z3py: the tracker (a Bool const, or a name string) is added to
        the set of literals over which an unsat core is computed. If a later
        `check()` is UNSAT, `unsat_core()` returns the trackers that the solver
        used. Implemented over AY's assumption mechanism: we assert
        `Implies(tracker, constraint)` and treat `tracker` as an assumption at
        check time (the same encoding z3py uses internally).
        """
        if isinstance(tracker, str):
            tracker = Bool(tracker, self.ctx)
        if not isinstance(tracker, BoolRef):
            raise NotImplementedError(
                "assert_and_track tracker must be a Bool const or a name string"
            )
        if isinstance(constraint, bool):
            constraint = BoolVal(constraint, self.ctx)
        if not isinstance(constraint, BoolRef):
            raise NotImplementedError(
                f"assert_and_track expects a Bool constraint, got {constraint!r}"
            )
        # Rebuild either operand into this Solver's context if needed.
        tracker = _adopt(tracker, self.ctx)
        constraint = _adopt(constraint, self.ctx)
        self.add(Implies(tracker, constraint))
        # Record the tracker (dedup by AST handle, preserving order).
        if all(t.ast != tracker.ast for t in self._tracked):
            self._tracked.append(tracker)

    def _check_assuming(self, assumptions):
        n = len(assumptions)
        if n == 0:
            r = lib.Z3_solver_check(self.ctx.ref, self.handle)
        else:
            arr = (_lib.Z3_ast * n)(*[a.ast for a in assumptions])
            r = lib.Z3_solver_check_assumptions(self.ctx.ref, self.handle, n, arr)
        self.ctx.check_error("solver.check")
        return _lbool_to_result(r)

    def check(self, *assumptions):
        """Check satisfiability, optionally under `assumptions`.

        With no arguments this is a plain check-sat. With assumption Bool
        expressions (z3py `s.check(a, b, ...)`), AY checks under those literals
        via `Z3_solver_check_assumptions`. If any tracking literals were
        registered with `assert_and_track`, they are used as the assumption set
        automatically when no explicit assumptions are given.
        """
        assumptions = _flatten(assumptions)
        self._fail_closed_reason = None
        if assumptions:
            coerced = _bool_args(list(assumptions), self.ctx)
            # Rebuild assumptions from another context into this Solver's.
            coerced = [_adopt(a, self.ctx) for a in coerced]
            if coerced:
                _same_ctx(*coerced)
            if _contains_quantified_array([*self.assertions(), *coerced], self.ctx):
                self._fail_closed_reason = _QUANTIFIED_ARRAY_REASON
                return unknown
            return self._check_assuming(coerced)
        if _contains_quantified_array(self.assertions(), self.ctx):
            self._fail_closed_reason = _QUANTIFIED_ARRAY_REASON
            return unknown
        if self._tracked:
            return self._check_assuming(self._tracked)
        r = lib.Z3_solver_check(self.ctx.ref, self.handle)
        self.ctx.check_error("solver.check")
        return _lbool_to_result(r)

    def unsat_core(self):
        """Return a sound, best-effort deletion-minimized unsat core.

        Valid only after a `check(...)` that returned `unsat`. The result is a
        sound unsat core whose conjunction (with the asserted constraints) is
        unsatisfiable. An element is dropped only when the remainder is still
        UNSAT. SAT and UNKNOWN deletion checks both keep the element, so an
        UNKNOWN result preserves soundness but prevents a minimality claim.

        Algorithm (deletion-based minimization, a.k.a. the destructive / Junker
        QuickXplain-style baseline): start from the subset the solver reports as
        the core, then iterate over its tracking literals trying to drop each
        one — re-check the solver under the remaining trackers (as assumptions)
        and, if it is still UNSAT, drop the candidate permanently. Repeat to a
        fixpoint. Because every `assert_and_track(c, p)` is encoded as the hard
        clause `Implies(p, c)`, checking under a *subset* of trackers leaves the
        omitted constraints vacuously satisfied (their tracker is unconstrained),
        so a check under a subset of trackers is exactly a check of that subset's
        constraints — re-check is the authority on whether an element is needed.

        SOUNDNESS: every removal is authorized by an UNSAT re-check, so the
        returned set remains a real unsat core. A kept element may be necessary
        (its removal returned SAT) or unresolved (its removal returned UNKNOWN).
        Re-checks reuse this Solver's single context (no rebuild) via
        `Z3_solver_check_assumptions`.

        COST: deletion minimization issues O(k) incremental check-assumptions
        calls per pass (k = size of the solver-reported core), iterated to a
        fixpoint. For pathological instances this is more solving than a single
        check; it is bounded by the number of trackers.
        """
        vec = lib.Z3_solver_get_unsat_core(self.ctx.ref, self.handle)
        if not vec:
            return []
        # Prefer returning the caller's original tracker objects (which carry
        # decl_name) when the core AST matches one — same AST handle is the same
        # literal. Fall back to a freshly wrapped AST otherwise.
        by_ast = {t.ast: t for t in self._tracked}
        n = lib.Z3_ast_vector_size(self.ctx.ref, vec)
        core = []
        seen = set()
        for i in range(n):
            a = lib.Z3_ast_vector_get(self.ctx.ref, vec, i)
            if a == 0 or a in seen:
                continue
            seen.add(a)
            core.append(by_ast.get(a) or _wrap_from_ast(a, self.ctx))
        if not core:
            return core
        return self._minimize_core(core)

    def _minimize_core(self, core):
        """Deletion-based minimization of an unsat `core` (list of tracker
        literals) to a deletion-minimal core, iterating passes to a fixpoint.

        Re-checks the solver under subsets of the trackers as assumptions; an
        element is dropped permanently iff the set WITHOUT it is still UNSAT.
        """
        kept = list(core)
        changed = True
        while changed and kept:
            changed = False
            i = 0
            while i < len(kept):
                # Tentatively drop kept[i] and re-check under the rest. An empty
                # `trial` checks just the hard (untracked) asserts; if THAT is
                # UNSAT the conflict needs no tracked assumption, so the
                # deletion-minimal core is empty (matches z3py) — re-check is the
                # authority on whether an element is required.
                trial = kept[:i] + kept[i + 1:]
                if self._check_assuming(trial) == unsat:
                    # kept[i] is not required: drop it permanently.
                    kept = trial
                    changed = True
                    # Do not advance i; the element now at index i is new.
                else:
                    i += 1
        # The last trial we ran may have been SAT, leaving the solver's cached
        # verdict/unsat-core inconsistent with the UNSAT problem the caller saw.
        # Restore an UNSAT state by re-checking under the minimal core (which is
        # UNSAT by construction), so a subsequent unsat_core()/check() stays sane.
        if kept:
            self._check_assuming(kept)
        return kept

    def assertions(self):
        """Return the solver's current assertions as a list of expressions."""
        vec = lib.Z3_solver_get_assertions(self.ctx.ref, self.handle)
        return _ast_vector_to_list(vec, self.ctx)

    def translate(self, target_ctx):
        """Copy this solver into `target_ctx` (z3py Solver.translate).

        Returns a fresh Solver in `target_ctx` holding this solver's current
        assertions, each rebuilt into the target context via the cross-context
        machinery. Note (documented divergence): only the flat assertion set is
        copied — open push/pop scopes and assumption trackers are not carried
        over (z3py copies the full stack); assert into the returned solver or
        re-push as needed.
        """
        if not isinstance(target_ctx, Context):
            raise NotImplementedError("Solver.translate expects a Context")
        out = Solver(ctx=target_ctx)
        for a in self.assertions():
            out.add(_adopt(a, target_ctx))
        return out

    def set(self, *args, **kwargs):
        """Set solver parameters (z3py surface).

        Accepts, exactly like z3py:
          * keyword params:            ``s.set(timeout=1000, unsat_core=True)``
          * a single ('key', value):   ``s.set('timeout', 1000)``
          * a prebuilt Params object:  ``s.set(p)`` where ``p = Params(); ...``

        AY honors `timeout` (milliseconds) and the named `proof` toggle at the
        engine level; other parameters are accepted (for API compatibility, and
        forwarded to the engine via `Z3_solver_set_params`) but may be ignored
        by the core. Value types dispatch like z3py: bool/int/float/str.
        """
        # z3py: s.set(params_obj) applies a prebuilt Params directly.
        if len(args) == 1 and isinstance(args[0], ParamsRef) and not kwargs:
            p = args[0]
            if p._mirror.get("proof") is not None:
                lib.Z3_solver_set_proof_production(
                    self.ctx.ref, self.handle, bool(p._mirror["proof"])
                )
            lib.Z3_solver_set_params(self.ctx.ref, self.handle, p.params)
            return
        opts = dict(kwargs)
        # Positional ('key', value) pairs, like z3py.
        if len(args) == 2 and isinstance(args[0], str):
            opts[args[0]] = args[1]
        elif args:
            raise NotImplementedError(
                "Solver.set positional args must be a single ('key', value) pair "
                "or a single Params object"
            )
        if not opts:
            return
        # Proof production is a named toggle (Z3's global `proof` param): route
        # it to the dedicated C setter so Solver.proof() has a real Alethe proof
        # to return. Enable it before the check whose proof you want.
        if "proof" in opts:
            enable = bool(opts.pop("proof"))
            lib.Z3_solver_set_proof_production(self.ctx.ref, self.handle, enable)
        if not opts:
            return
        params = lib.Z3_mk_params(self.ctx.ref)
        for key, value in opts.items():
            sym = lib.Z3_mk_string_symbol(self.ctx.ref, str(key).encode())
            if isinstance(value, bool):
                lib.Z3_params_set_bool(self.ctx.ref, params, sym, ctypes.c_bool(value))
            elif isinstance(value, numbers.Integral):
                lib.Z3_params_set_uint(self.ctx.ref, params, sym, ctypes.c_uint(int(value)))
            elif isinstance(value, numbers.Real):
                lib.Z3_params_set_double(
                    self.ctx.ref, params, sym, ctypes.c_double(float(value))
                )
            elif isinstance(value, str):
                lib.Z3_params_set_symbol(
                    self.ctx.ref, params, sym, _to_symbol(value, self.ctx)
                )
            else:
                raise NotImplementedError(
                    f"Solver.set value for {key!r} must be bool/int/float/str, "
                    f"got {value!r}"
                )
        lib.Z3_solver_set_params(self.ctx.ref, self.handle, params)

    def param_descrs(self):
        """Parameter descriptors this solver accepts (z3py Solver.param_descrs()).

        DIVERGENCE (documented, never faked): AY's C ABI does not export
        `Z3_solver_get_param_descrs`, so ayz3 cannot enumerate the engine's
        solver-parameter descriptors. Rather than fabricate a descriptor set, it
        raises honestly. (Params still WORK — `set('timeout', ...)` etc. are
        honored; only the reflective descriptor enumeration is absent.)
        """
        raise NotImplementedError(
            "Solver.param_descrs(): AY's C ABI has no Z3_solver_get_param_descrs "
            "(solver-parameter descriptor enumeration is absent); parameters "
            "themselves are still accepted via Solver.set(...)"
        )

    def reason_unknown(self):
        """Explanation string for the last `unknown` result (may be empty)."""
        if self._fail_closed_reason is not None:
            return self._fail_closed_reason
        s = lib.Z3_solver_get_reason_unknown(self.ctx.ref, self.handle)
        return s.decode() if s else ""

    def from_string(self, smt2):
        """Parse SMT-LIB2 text and assert its formulas into this solver."""
        for f in parse_smtlib2_string(smt2, ctx=self.ctx):
            self.add(f)

    def from_file(self, path):
        """Parse an SMT-LIB2 FILE and assert its formulas into this solver
        (z3py Solver.from_file()).

        Reads the file text and routes it through `from_string` (AY has no
        distinct `Z3_parse_smtlib2_file`, but a file is just its contents — the
        asserted formula set is identical).
        """
        with open(path, "r") as fh:
            self.from_string(fh.read())

    def units(self):
        """Currently-implied unit literals as a list of Bool expressions
        (z3py Solver.units())."""
        vec = lib.Z3_solver_get_units(self.ctx.ref, self.handle)
        return _bool_ast_vector_to_list(vec, self.ctx)

    def non_units(self):
        """Non-unit assertions/clauses as a list of Bool expressions
        (z3py Solver.non_units())."""
        vec = lib.Z3_solver_get_non_units(self.ctx.ref, self.handle)
        return _bool_ast_vector_to_list(vec, self.ctx)

    def trail(self):
        """The current assignment trail as a list of Bool literal expressions
        (z3py Solver.trail())."""
        vec = lib.Z3_solver_get_trail(self.ctx.ref, self.handle)
        return _bool_ast_vector_to_list(vec, self.ctx)

    def consequences(self, assumptions, variables):
        """Forward-implied consequences of `variables` under `assumptions`
        (z3py Solver.consequences()).

        Returns a `(CheckSatResult, [consequence exprs])` tuple. Each consequence
        expresses "the asserted constraints AND the assumptions IMPLY this fact
        about a query variable". `assumptions`/`variables` may be Python lists of
        Bool expressions (z3py also accepts an AstVector; ayz3 accepts lists).

        DIVERGENCE (documented, sound): z3py renders each consequence as
        `Implies(premise, literal)`; AY's engine returns the LOGICALLY EQUIVALENT
        Or/Not normal form (e.g. `Or(x, Not(p))` for `Implies(p, x)`, or a bare
        `lit` when the premise is trivially true). The boolean function is
        identical — a sound canonicalization difference, never a changed result.
        The verdict (sat/unsat/unknown) and the set of forced facts match z3py.
        """
        asm_list = list(assumptions)
        var_list = list(variables)
        # Coerce + rebuild into this solver's context (matches add()/check()).
        asm_list = [_adopt(a, self.ctx) for a in _bool_args(asm_list, self.ctx)]
        var_list = [_adopt(v, self.ctx) for v in _bool_args(var_list, self.ctx)]
        cref = self.ctx.ref
        asm_vec = lib.Z3_mk_ast_vector(cref)
        lib.Z3_ast_vector_inc_ref(cref, asm_vec)
        var_vec = lib.Z3_mk_ast_vector(cref)
        lib.Z3_ast_vector_inc_ref(cref, var_vec)
        con_vec = lib.Z3_mk_ast_vector(cref)
        lib.Z3_ast_vector_inc_ref(cref, con_vec)
        try:
            for a in asm_list:
                lib.Z3_ast_vector_push(cref, asm_vec, a.ast)
            for v in var_list:
                lib.Z3_ast_vector_push(cref, var_vec, v.ast)
            r = lib.Z3_solver_get_consequences(
                cref, self.handle, asm_vec, var_vec, con_vec
            )
            self.ctx.check_error("solver.consequences")
            cons = _bool_ast_vector_to_list(con_vec, self.ctx)
        finally:
            lib.Z3_ast_vector_dec_ref(cref, asm_vec)
            lib.Z3_ast_vector_dec_ref(cref, var_vec)
            lib.Z3_ast_vector_dec_ref(cref, con_vec)
        return _lbool_to_result(r), cons

    def model(self):
        h = lib.Z3_solver_get_model(self.ctx.ref, self.handle)
        if not h:
            raise AyZ3Exception("no model available (last check was not sat)")
        return ModelRef(h, self.ctx)

    def statistics(self):
        """Return solver statistics from the last `check()` (z3py Solver.statistics()).

        The result is a `Statistics` object mapping AY's REAL solve counters
        (conflicts, decisions, propagations, memory, ...). AY's counter SET
        differs from z3's, so the KEY NAMES are AY's honest counters, not a
        fabricated z3 key set (see `Statistics`). Before any check has run the
        counters are all zero.
        """
        h = lib.Z3_solver_get_statistics(self.ctx.ref, self.handle)
        self.ctx.check_error("solver.statistics")
        if not h:
            raise AyZ3Exception("no statistics available")
        return Statistics(h, self.ctx)

    def sexpr(self):
        """SMT-LIB2 form of this solver's assertions (z3py Solver.sexpr()).

        Renders `(declare-fun ...)` + `(assert ...)` for the current assertion
        stack. Reparses (via `parse_smtlib2_string` / `Solver.from_string`) to
        an equisatisfiable solver.
        """
        s = lib.Z3_solver_to_string(self.ctx.ref, self.handle)
        return _canonicalize_as_array_text(s.decode(), self.ctx) if s else ""

    def to_smt2(self):
        """Self-contained SMT-LIB2 script for this solver (z3py Solver.to_smt2()).

        Emits the assertion set (declarations + `(assert ...)`, from `sexpr()`)
        followed by `(check-sat)`.

        DIVERGENCE: unlike z3's `Z3_benchmark_to_smtlib_string`, AY has no
        benchmark serializer, so this omits `set-logic`/`set-info` headers. The
        body is the REAL assertion set and reparses to an equisatisfiable solver.
        """
        body = self.sexpr()
        if body and not body.endswith("\n"):
            body += "\n"
        return body + "(check-sat)\n"

    def proof(self):
        """Return the proof of the last UNSAT `check()` as Alethe proof text.

        DIVERGENCE (documented, never faked): AY produces ALETHE proofs, not
        z3's proof-term AST. Where z3py returns an `AstRef` of z3 proof terms,
        ayz3 returns the real Alethe proof TEXT as a `str`.

        Requires proof production to have been enabled BEFORE the check
        (`s.set(proof=True)` or `set_param('proof', True)`) and the last result
        to have been `unsat`. Otherwise raises honestly — a proof is never
        fabricated for a sat/unknown result or when production was off.
        """
        if not lib.Z3_solver_get_proof_production(self.ctx.ref, self.handle):
            raise AyZ3Exception(
                "no proof available: enable proof production first "
                "(s.set(proof=True) or set_param('proof', True)) before check()"
            )
        s = lib.Z3_solver_get_proof_string(self.ctx.ref, self.handle)
        if not s:
            # The C getter set an honest error on the not-available path; clear
            # it (a successful get_statistics resets the context error to OK) so
            # it cannot poison a later check_error(), then raise.
            lib.Z3_solver_get_statistics(self.ctx.ref, self.handle)
            raise AyZ3Exception(
                "no proof available: last check was not unsat "
                "(AY emits Alethe proofs only for UNSAT with production enabled)"
            )
        return s.decode()

    def __repr__(self):
        s = lib.Z3_solver_to_string(self.ctx.ref, self.handle)
        return (
            _canonicalize_as_array_text(s.decode(), self.ctx)
            if s
            else "<solver>"
        )


# ---------------------------------------------------------------------------
# Optimize
# ---------------------------------------------------------------------------

class _Objective:
    """A handle to one optimization objective (z3py `OptimizeObjective`).

    Returned by `Optimize.maximize` / `minimize` / `add_soft`. After a `check()`
    it exposes the optimum via `value()`, and the bounds the engine has proven so
    far via `lower()` / `upper()`. Matching z3py, `value()` returns the *upper*
    bound for a maximize objective and the *lower* bound for a minimize (and for
    a soft objective, which minimizes total unsatisfied soft weight). When the
    objective is fully determined the two coincide.

    `lower_values()` / `upper_values()` return the REAL bound-as-vector contents
    that the engine reports (z3's extended-rational triple encoding). ayz3
    returns them as a plain Python list of `AstRef` rather than z3py's `AstVector`
    — a list is iterable/indexable/`len`-able exactly where z3py programs use the
    vector, and the ELEMENTS are the same terms (documented ergonomic divergence,
    never a fabricated value).
    """

    def __init__(self, opt, idx, is_max, soft_group=None):
        self._opt = opt
        self._idx = idx
        self._is_max = is_max
        # For a soft (add_soft) objective, the group label whose optimal total
        # penalty this handle reports; None for a hard maximize/minimize.
        self._soft_group = soft_group

    def _soft_penalty(self):
        """The optimal total penalty of this soft objective's group, computed
        from AY's optimal model.

        AY's MaxSMT engine does not expose a soft group's penalty via
        `Z3_optimize_get_lower/upper` (those return null for soft objectives), so
        we evaluate it on the OPTIMAL MODEL AY returned: sum the weights of the
        group's soft constraints that the model VIOLATES. This is the true
        objective value of the returned optimum (never a fabricated number — if
        AY's model were suboptimal this would honestly report the higher penalty),
        and it matches z3py's `OptimizeObjective.value()` whenever the models
        agree. Returns None when no model is available (last check not sat).
        """
        opt = self._opt
        h = lib.Z3_optimize_get_model(opt.ctx.ref, opt.handle)
        if not h:
            return None
        model = ModelRef(h, opt.ctx)
        total = 0
        for term, weight, group in opt._softs:
            if group != self._soft_group:
                continue
            # A soft constraint is VIOLATED when its term is false in the model.
            v = model.eval(term, model_completion=True)
            if is_false(v):
                total += weight
        return IntVal(total, opt.ctx)

    def _bound(self, getter):
        if self._soft_group is not None:
            return self._soft_penalty()
        ctx = self._opt.ctx
        ast = getter(ctx.ref, self._opt.handle, self._idx)
        if not ast:
            return None  # unbounded/unavailable; AY never fabricates a value
        sort = _value_sort_from_ast(ast, ctx)
        return _wrap(ast, sort, ctx)

    def lower(self):
        """The lower bound the engine has proven for this objective (or None if
        unbounded/unavailable — e.g. -oo, which AY does not represent). For a soft
        objective this is its group's optimal total penalty."""
        return self._bound(lib.Z3_optimize_get_lower)

    def upper(self):
        """The upper bound the engine has proven for this objective (or None if
        unbounded/unavailable — e.g. +oo, which AY does not represent). For a soft
        objective this is its group's optimal total penalty."""
        return self._bound(lib.Z3_optimize_get_upper)

    def value(self):
        """The optimum: `upper()` for a maximize, `lower()` for a minimize/soft
        objective (mirrors z3py). Equal to both bounds once fully determined."""
        return self.upper() if self._is_max else self.lower()

    def lower_values(self):
        """The lower bound as the engine's bound-vector, as a list of AstRef."""
        vec = lib.Z3_optimize_get_lower_as_vector(
            self._opt.ctx.ref, self._opt.handle, self._idx)
        return _ast_vector_to_list(vec, self._opt.ctx)

    def upper_values(self):
        """The upper bound as the engine's bound-vector, as a list of AstRef."""
        vec = lib.Z3_optimize_get_upper_as_vector(
            self._opt.ctx.ref, self._opt.handle, self._idx)
        return _ast_vector_to_list(vec, self._opt.ctx)


class Optimize:
    # Like Solver: explicit ctx wins; else adopt an active scope; else a fresh
    # Context (so a top-level Optimize and Solver are independent). See Solver.
    def __init__(self, ctx=None):
        self.ctx = _solver_ctx(ctx)
        self.handle = lib.Z3_mk_optimize(self.ctx.ref)
        self._n_obj = 0
        # Tracking literals registered via assert_and_track, so unsat_core() can
        # return the caller's original tracker objects (which carry decl_name).
        self._tracked = []
        # Soft constraints registered via add_soft, as (term, weight_int, group)
        # tuples, so a soft objective handle can report its group's optimal
        # penalty from the model (AY does not expose it via get_lower/upper).
        self._softs = []
        self._fail_closed_reason = None

    def using(self):
        return _ctx_scope(self.ctx)

    def add(self, *args):
        for a in args:
            if isinstance(a, (list, tuple)):
                self.add(*a)
                continue
            if isinstance(a, bool):
                a = BoolVal(a, self.ctx)
            if not isinstance(a, BoolRef):
                raise NotImplementedError(
                    f"Optimize.add expects Bool constraints, got {a!r}"
                )
            # Transparently rebuild a constraint from another context (so the
            # same vars can feed a Solver AND an Optimize — matches z3py).
            a = _adopt(a, self.ctx)
            lib.Z3_optimize_assert(self.ctx.ref, self.handle, a.ast)

    # z3py alias.
    assert_exprs = add

    def add_soft(self, arg, weight=1, id=None):
        """Assert a SOFT constraint with a penalty `weight` (weighted MaxSMT).

        Mirrors z3py `Optimize.add_soft(f, weight, id)`: the engine minimizes the
        total weight of unsatisfied soft constraints, grouped by `id`. `weight`
        may be an int, float, or numeric string (z3py's own coercion); `id` names
        the soft group (default: the anonymous group). Returns an objective handle
        whose `value()`/`lower()`/`upper()` report that group's optimal penalty
        (a minimize objective, so `value()` == `lower()`).
        """
        if isinstance(arg, bool):
            arg = BoolVal(arg, self.ctx)
        if not isinstance(arg, BoolRef):
            raise NotImplementedError(
                f"Optimize.add_soft expects a Bool constraint, got {arg!r}"
            )
        arg = _adopt(arg, self.ctx)
        # z3py coerces weight to a string; AY's MaxSMT is weight-exact over
        # NON-NEGATIVE INTEGER weights (Z3_optimize_assert_soft rejects a
        # fractional weight). Accept int / integral-float / integer-string; a
        # genuinely fractional weight raises honestly (AY cannot represent it).
        weight_int = _coerce_soft_weight(weight)
        gid = "" if id is None else str(id)
        sym = lib.Z3_mk_string_symbol(self.ctx.ref, gid.encode())
        idx = lib.Z3_optimize_assert_soft(
            self.ctx.ref, self.handle, arg.ast, ("%d" % weight_int).encode(), sym)
        self.ctx.check_error("optimize.add_soft")
        self._n_obj += 1
        # Record for model-based penalty readout (see _Objective._soft_penalty).
        self._softs.append((arg, weight_int, gid))
        # A soft objective minimizes total unsatisfied weight (is_max=False); its
        # value is its group's optimal penalty, computed from the model.
        return _Objective(self, idx, is_max=False, soft_group=gid)

    def assert_and_track(self, constraint, tracker):
        """Assert `constraint`, tracked by a Boolean literal `tracker`.

        On a subsequent UNSAT `check()`, `unsat_core()` returns the trackers the
        engine used. Mirrors z3py: `tracker` is a Bool const or a name string.
        """
        if isinstance(tracker, str):
            tracker = Bool(tracker, self.ctx)
        if not isinstance(tracker, BoolRef):
            raise NotImplementedError(
                "assert_and_track tracker must be a Bool const or a name string"
            )
        if isinstance(constraint, bool):
            constraint = BoolVal(constraint, self.ctx)
        if not isinstance(constraint, BoolRef):
            raise NotImplementedError(
                f"assert_and_track expects a Bool constraint, got {constraint!r}"
            )
        tracker = _adopt(tracker, self.ctx)
        constraint = _adopt(constraint, self.ctx)
        lib.Z3_optimize_assert_and_track(
            self.ctx.ref, self.handle, constraint.ast, tracker.ast)
        self.ctx.check_error("optimize.assert_and_track")
        if all(t.ast != tracker.ast for t in self._tracked):
            self._tracked.append(tracker)

    def maximize(self, expr):
        expr = _adopt(expr, self.ctx)
        idx = lib.Z3_optimize_maximize(self.ctx.ref, self.handle, expr.ast)
        self._n_obj += 1
        return _Objective(self, idx, is_max=True)

    def minimize(self, expr):
        expr = _adopt(expr, self.ctx)
        idx = lib.Z3_optimize_minimize(self.ctx.ref, self.handle, expr.ast)
        self._n_obj += 1
        return _Objective(self, idx, is_max=False)

    def push(self):
        """Create a backtracking point (z3py Optimize.push())."""
        lib.Z3_optimize_push(self.ctx.ref, self.handle)

    def pop(self, n=1):
        """Backtrack `n` scopes (z3py Optimize.pop() pops one at a time)."""
        for _ in range(int(n)):
            lib.Z3_optimize_pop(self.ctx.ref, self.handle)

    def check(self, *assumptions):
        """Check for an optimal model (z3py Optimize.check()).

        Optimizes the asserted constraints and objectives, returning `sat`,
        `unsat`, or `unknown`. On `sat`, `model()` realizes the optima and each
        objective handle's `value()` is the optimum.

        DIVERGENCE (documented, never faked): AY's optimization loop does not
        thread CHECK-TIME ASSUMPTIONS through the MaxSMT/objective search, so
        `check(a, b, ...)` with assumptions is not supported and raises
        `NotImplementedError` (the C layer rejects a non-zero assumption count
        rather than return a possibly-wrong optimum). Encode assumption toggles as
        hard `Implies(p, c)` constraints instead.
        """
        assumptions = _flatten(assumptions)
        self._fail_closed_reason = None
        if assumptions:
            raise NotImplementedError(
                "Optimize.check(*assumptions) is not supported: AY's optimization "
                "path does not thread check-time assumptions through the MaxSMT / "
                "objective search (a documented divergence — see Z3_optimize_check). "
                "Encode toggles as hard Implies(p, c) constraints and use plain "
                "check(), or use a Solver for assumption-based checking."
            )
        formulas = [*self.assertions(), *(term for term, _, _ in self._softs)]
        if _contains_quantified_array(formulas, self.ctx):
            self._fail_closed_reason = _QUANTIFIED_ARRAY_REASON
            return unknown
        r = lib.Z3_optimize_check(self.ctx.ref, self.handle, 0, None)
        self.ctx.check_error("optimize.check")
        return _lbool_to_result(r)

    def model(self):
        h = lib.Z3_optimize_get_model(self.ctx.ref, self.handle)
        if not h:
            raise AyZ3Exception("no model available (last optimize check not sat)")
        # Hide the engine's internal MaxSMT relaxation constants
        # (`__maxsmt_r…`/`__maxsmt_wc…`/`__maxsmt_c…`, minted in
        # api/solving/maxsmt.rs) from decls()/len()/iteration, matching z3's
        # Optimize.model() which never surfaces them (the SMT-LIB (get-model)
        # path already filters them). They stay eval-able by explicit handle.
        return ModelRef(h, self.ctx, hidden_prefixes=("__maxsmt_",))

    def lower(self, objective):
        """The lower bound the engine proved for `objective` (z3py Optimize.lower(h))."""
        return objective.lower()

    def upper(self, objective):
        """The upper bound the engine proved for `objective` (z3py Optimize.upper(h))."""
        return objective.upper()

    def value(self, objective):
        """The optimum of `objective`: upper() for maximize, lower() for
        minimize/soft (z3py Optimize.value(h))."""
        return objective.value()

    def param_descrs(self):
        """Parameter descriptors the optimizer accepts (z3py Optimize.param_descrs()).

        Returns a real, queryable `ParamDescrsRef` listing the params AY's
        optimizer genuinely accepts (e.g. `timeout` (uint), `produce_proofs`
        (bool), `priority` (string)), each with its real kind + documentation.
        AY's accepted-param SET differs from z3's — these are AY's honest params,
        never a fabricated z3 list.
        """
        descr = lib.Z3_optimize_get_param_descrs(self.ctx.ref, self.handle)
        self.ctx.check_error("Optimize.param_descrs")
        if not descr:
            raise AyZ3Exception("Z3_optimize_get_param_descrs returned null")
        return ParamDescrsRef(descr, self.ctx)
    def objectives(self):
        """The optimization objectives as a list of expressions (z3py
        Optimize.objectives()). Each is the engine's normalized objective term."""
        vec = lib.Z3_optimize_get_objectives(self.ctx.ref, self.handle)
        return _ast_vector_to_list(vec, self.ctx)

    def assertions(self):
        """The hard assertions as a list of expressions (z3py Optimize.assertions())."""
        vec = lib.Z3_optimize_get_assertions(self.ctx.ref, self.handle)
        return _ast_vector_to_list(vec, self.ctx)

    def unsat_core(self):
        """The unsat core over `assert_and_track` trackers (z3py Optimize.unsat_core()).

        Valid only after a `check()` that returned `unsat`. Returns the tracker
        literals the engine reports; the caller's original tracker objects are
        returned where the AST matches (preserving `decl_name`).

        DIVERGENCE (documented, never faked): AY's Optimize engine cannot extract
        a PARTICIPATING core — its optimization loop does not thread check-time
        assumptions, and tracked constraints are asserted unconditionally, so it
        has no sound way to identify which trackers actually caused the conflict.
        Rather than return a possibly-wrong over-approximate set, it yields no
        core; when that happens this raises `NotImplementedError`. Use a
        `Solver` with `assert_and_track` / `unsat_core` for participating cores.
        """
        vec = lib.Z3_optimize_get_unsat_core(self.ctx.ref, self.handle)
        by_ast = {t.ast: t for t in self._tracked}
        out = []
        seen = set()
        if vec:
            n = lib.Z3_ast_vector_size(self.ctx.ref, vec)
            for i in range(n):
                a = lib.Z3_ast_vector_get(self.ctx.ref, vec, i)
                if a == 0 or a in seen:
                    continue
                seen.add(a)
                out.append(by_ast.get(a) or _wrap_from_ast(a, self.ctx))
        if not out:
            raise NotImplementedError(
                "Optimize.unsat_core() is unavailable: AY's optimization engine "
                "cannot extract a participating unsat core (documented divergence "
                "— see Z3_optimize_get_unsat_core). Use a Solver with "
                "assert_and_track / unsat_core for participating cores."
            )
        return out

    def statistics(self):
        """Statistics from the last `check()` as a `Statistics` object (z3py
        Optimize.statistics()). Keys are AY's honest solve counters."""
        h = lib.Z3_optimize_get_statistics(self.ctx.ref, self.handle)
        self.ctx.check_error("optimize.statistics")
        if not h:
            raise AyZ3Exception("no statistics available")
        return Statistics(h, self.ctx)

    def reason_unknown(self):
        """Explanation string for the last `unknown` result (may be empty)."""
        if self._fail_closed_reason is not None:
            return self._fail_closed_reason
        s = lib.Z3_optimize_get_reason_unknown(self.ctx.ref, self.handle)
        return s.decode() if s else ""

    def set(self, *args, **kwargs):
        """Set optimize parameters (z3py `o.set('timeout', 1000)` / `o.set(k=v)`).

        Parameters are forwarded via `Z3_mk_params` + `Z3_optimize_set_params`.
        """
        opts = dict(kwargs)
        if len(args) == 2 and isinstance(args[0], str):
            opts[args[0]] = args[1]
        elif args:
            raise NotImplementedError(
                "Optimize.set positional args must be a single ('key', value) pair"
            )
        if not opts:
            return
        params = lib.Z3_mk_params(self.ctx.ref)
        for key, value in opts.items():
            sym = lib.Z3_mk_string_symbol(self.ctx.ref, str(key).encode())
            if isinstance(value, bool):
                lib.Z3_params_set_bool(
                    self.ctx.ref, params, sym, ctypes.c_bool(value)
                )
            elif isinstance(value, numbers.Integral):
                lib.Z3_params_set_uint(
                    self.ctx.ref, params, sym, ctypes.c_uint(int(value))
                )
            elif isinstance(value, numbers.Real):
                # Float-valued params (e.g. numeric tolerances) — our audit
                # added this; upstream's variant only covered int/bool/str.
                lib.Z3_params_set_double(
                    self.ctx.ref, params, sym, ctypes.c_double(float(value))
                )
            elif isinstance(value, str):
                # Symbol-valued params, notably `priority` ('lex'|'box'|
                # 'pareto') — the standard z3py Optimize idiom
                # `o.set(priority='pareto')`. AY's engine honors pareto/box via
                # the same path the SMT-LIB `:opt.priority` option drives
                # (repeated check() enumerates the pareto front).
                lib.Z3_params_set_symbol(
                    self.ctx.ref, params, sym, _to_symbol(value, self.ctx)
                )
            else:
                raise NotImplementedError(
                    f"Optimize.set value for {key!r} must be bool/int/float/str, "
                    f"got {value!r}"
                )
        lib.Z3_optimize_set_params(self.ctx.ref, self.handle, params)

    def from_string(self, s):
        """Parse an SMT-LIB2 optimization script and load it into this Optimize.

        Unlike `Solver.from_string`, this honors `(maximize ...)`,
        `(minimize ...)` and `(assert-soft ...)` directives (via
        `Z3_optimize_from_string`), so a full optimization benchmark round-trips.
        """
        lib.Z3_optimize_from_string(self.ctx.ref, self.handle, s.encode())
        self.ctx.check_error("optimize.from_string")

    def from_file(self, path):
        """Parse an SMT-LIB2 optimization script from `path` (z3py
        Optimize.from_file())."""
        lib.Z3_optimize_from_file(self.ctx.ref, self.handle, str(path).encode())
        self.ctx.check_error("optimize.from_file")

    def help(self):
        """Return the optimize engine's parameter help string (z3py Optimize.help())."""
        s = lib.Z3_optimize_get_help(self.ctx.ref, self.handle)
        return s.decode() if s else ""

    def sexpr(self):
        """SMT-LIB2 form of this Optimize's assertions + objectives (z3py
        Optimize.sexpr())."""
        s = lib.Z3_optimize_to_string(self.ctx.ref, self.handle)
        return _canonicalize_as_array_text(s.decode(), self.ctx) if s else ""

    def __repr__(self):
        s = lib.Z3_optimize_to_string(self.ctx.ref, self.handle)
        return (
            _canonicalize_as_array_text(s.decode(), self.ctx)
            if s
            else "<optimize>"
        )


# ---------------------------------------------------------------------------
# Tactics (goal-to-goal transformations), z3py-shaped.
# ---------------------------------------------------------------------------
#
# A Tactic is a recipe for an equivalence-preserving goal transformation. It is
# stored as a lazy spec tree (a name, or a then/or-else of sub-tactics) and is
# materialized into a concrete C handle ON DEMAND, in whatever Context it is
# applied to. Keeping the recipe context-free (rather than holding a single C
# handle) means Then(...)/OrElse(...) compose freely and Tactic.solver() can
# build the handle in a FRESH Context per solver — matching how Solver() gives
# each top-level solver its own context.
#
# SOUNDNESS: AY only exposes equivalence-preserving tactics, so solving via
# Tactic.solver() yields the SAME sat/unsat verdict and a valid model as a plain
# Solver. Unknown tactic names are rejected by the C layer (Z3_mk_tactic returns
# NULL + Z3_INVALID_ARG); Tactic(name) raises AyZ3Exception rather than
# pretending the tactic exists.

class Tactic:
    """A goal-to-goal transformation (z3py-compatible surface).

    `Tactic('<name>')` names a built-in tactic; `Then(t1, t2, ...)` and
    `OrElse(t1, t2, ...)` compose tactics. `Tactic.solver()` returns a `Solver`
    that applies the tactic to its goal before solving.

    Supported names (validated by the C layer against the single shared registry,
    never an allowlist that can drift) — all real z3 tactic names, each backed by
    a real equivalence-preserving pass:
      * 'skip'             - identity.
      * 'simplify'         - simplify each formula, split top-level conjunctions.
      * 'solve-eqs'        - solve variable equalities and eliminate them.
      * 'propagate-values' - propagate ground `(= expr const)` equalities.
      * 'elim-and'         - z3's and-elimination: (and (and a b) c) => {a, b, c}.
      * 'qe-light'         - eliminate in-fragment `(exists ((x Int)) phi)` via
                             Cooper LIA quantifier elimination; out-of-fragment
                             quantifiers are left intact.

    Only equivalence-preserving tactics are supported, so the result of solving
    through a tactic-solver is identical to solving the original goal. An unknown
    tactic name (including z3-nonexistent names like 'flatten-and') raises
    `AyZ3Exception` exactly as z3py does — never silently treated as a no-op.
    """

    __slots__ = ("_spec",)

    def __init__(self, name, ctx=None):
        # `ctx` is accepted for z3py signature compatibility but the recipe is
        # context-free; the handle is built lazily per target context.
        if not isinstance(name, str):
            raise TypeError(f"Tactic name must be a string, got {name!r}")
        # Validate eagerly so an unknown name fails at construction (z3py raises
        # a Z3Exception on an unknown tactic too). Build-and-discard in a fresh
        # context.
        probe_ctx = Context()
        h = lib.Z3_mk_tactic(probe_ctx.ref, name.encode())
        if not h:
            # Surface the C error honestly.
            code = lib.Z3_get_error_code(probe_ctx.ref)
            msg = lib.Z3_get_error_msg(probe_ctx.ref, code)
            msg = msg.decode() if msg else "<no message>"
            raise AyZ3Exception(f"unknown/unsupported tactic {name!r}: {msg}")
        self._spec = ("name", name)

    @classmethod
    def _from_spec(cls, spec):
        obj = cls.__new__(cls)
        obj._spec = spec
        return obj

    def _build_in(self, ctx):
        """Materialize this recipe into a concrete C tactic handle in `ctx`."""
        kind = self._spec[0]
        if kind == "name":
            h = lib.Z3_mk_tactic(ctx.ref, self._spec[1].encode())
            ctx.check_error("Z3_mk_tactic")
            if not h:
                raise AyZ3Exception(f"unknown/unsupported tactic {self._spec[1]!r}")
            return h
        if kind == "repeat":
            # ("repeat", (sub-Tactic, max)).
            sub, max_iters = self._spec[1]
            inner = sub._build_in(ctx)
            h = lib.Z3_tactic_repeat(ctx.ref, inner, ctypes.c_uint(max_iters))
            ctx.check_error("Z3_tactic_repeat")
            if not h:
                raise AyZ3Exception("Z3_tactic_repeat returned null")
            return h
        if kind == "with":
            # ("with", (sub-Tactic, {param: value, ...})).
            sub, params = self._spec[1]
            inner = sub._build_in(ctx)
            p = lib.Z3_mk_params(ctx.ref)
            for key, value in params.items():
                sym = lib.Z3_mk_string_symbol(ctx.ref, key.encode())
                if isinstance(value, bool):
                    lib.Z3_params_set_bool(ctx.ref, p, sym, ctypes.c_bool(value))
                elif isinstance(value, int):
                    lib.Z3_params_set_uint(ctx.ref, p, sym, ctypes.c_uint(value))
                # Other value kinds are recorded on the recipe (repr) but AY always
                # applies the equivalence-preserving transform, so they do not
                # change the result.
            h = lib.Z3_tactic_using_params(ctx.ref, inner, p)
            ctx.check_error("Z3_tactic_using_params")
            if not h:
                raise AyZ3Exception("Z3_tactic_using_params returned null")
            return h
        # Composition: (op, [sub-Tactic, ...]). Fold left, mirroring z3py's
        # left-associative Then/OrElse. `kind` is "then" or "or-else".
        subs = self._spec[1]
        mk = lib.Z3_tactic_and_then if kind == "then" else lib.Z3_tactic_or_else
        acc = subs[0]._build_in(ctx)
        for sub in subs[1:]:
            nxt = sub._build_in(ctx)
            acc = mk(ctx.ref, acc, nxt)
            ctx.check_error("Z3_tactic_and_then/or_else")
            if not acc:
                raise AyZ3Exception("tactic composition returned null")
        return acc

    def then(self, *others):
        """Sequential composition: apply self, then each `other` in turn."""
        return Then(self, *others)

    def __call__(self, goal, *args, **kwargs):
        """Apply this tactic to `goal`, returning an `ApplyResult` (z3py `Tactic(goal)`).

        `goal` may be a `Goal`, a single Boolean expression, or a list of them.
        Any trailing positional/keyword args (z3py passes tactic parameters here)
        are accepted for signature compatibility; AY always applies the
        equivalence-preserving transform, so they never change the subgoal set.
        """
        return self.apply(goal, *args, **kwargs)

    def apply(self, goal, *args, **kwargs):
        """Apply this tactic to `goal`, returning an `ApplyResult` (z3py `Tactic.apply`).

        Routes through the shared AY apply engine (`Z3_tactic_apply`), so the
        produced subgoals are the tactic's REAL output. An HONEST tactic failure
        (e.g. `bit-blast` on an out-of-fragment BV goal, `split-clause` on a
        clause-free goal) raises `AyZ3Exception` with the engine's diagnostic —
        never a fabricated subgoal.
        """
        g = goal if isinstance(goal, Goal) else _goal_from(goal)
        handle = lib.Z3_tactic_apply(g.ctx.ref, self._build_in(g.ctx), g.handle)
        if not handle:
            code = lib.Z3_get_error_code(g.ctx.ref)
            msg = lib.Z3_get_error_msg(g.ctx.ref, code)
            msg = msg.decode() if msg else "<no message>"
            raise AyZ3Exception(f"tactic apply failed: {msg}")
        return ApplyResult(handle, g.ctx)

    def __repr__(self):
        kind = self._spec[0]
        if kind == "name":
            return f"Tactic({self._spec[1]!r})"
        if kind == "repeat":
            sub, max_iters = self._spec[1]
            return f"Repeat({sub!r}, {max_iters})"
        if kind == "with":
            sub, params = self._spec[1]
            kw = "".join(f", {k}={v!r}" for k, v in params.items())
            return f"With({sub!r}{kw})"
        label = {"then": "Then", "or-else": "OrElse"}.get(kind, kind.capitalize())
        return f"{label}({', '.join(repr(s) for s in self._spec[1])})"

    def solver(self, ctx=None):
        """Return a `Solver` that applies this tactic to its goal before solving.

        The verdict and model are identical to a plain `Solver` on the same goal
        (every supported tactic is equivalence-preserving).
        """
        sctx = ctx if ctx is not None else Context()
        handle = self._build_in(sctx)
        return Solver(ctx=sctx, _tactic_handle=handle)

    def param_descrs(self):
        """Parameter descriptors this tactic accepts (z3py Tactic.param_descrs()).

        Returns a real, queryable `ParamDescrsRef`. AY's tactics are
        equivalence-preserving and expose no per-tactic tunable that changes the
        produced goal's model set, so the descriptor set is HONEST-EMPTY (size 0)
        — a genuine, queryable empty set, never a fabricated parameter list.
        """
        ctx = Context()
        handle = self._build_in(ctx)
        descr = lib.Z3_tactic_get_param_descrs(ctx.ref, handle)
        ctx.check_error("Tactic.param_descrs")
        if not descr:
            raise AyZ3Exception("Z3_tactic_get_param_descrs returned null")
        return ParamDescrsRef(descr, ctx)


def _compose_tactics(op, tactics):
    if not tactics:
        raise ValueError(f"{op} requires at least one tactic")
    subs = []
    for t in tactics:
        if isinstance(t, str):
            t = Tactic(t)
        if not isinstance(t, Tactic):
            raise TypeError(f"expected Tactic or str, got {t!r}")
        subs.append(t)
    if len(subs) == 1:
        return subs[0]
    return Tactic._from_spec((op, subs))


def Then(*tactics):
    """Sequential composition of tactics (z3py-compatible).

    `Then(t1, t2, ...)` applies t1, then t2 on its result, and so on. Each
    argument may be a `Tactic` or a tactic-name string.
    """
    return _compose_tactics("then", tactics)


def OrElse(*tactics):
    """Alternative composition of tactics (z3py-compatible).

    `OrElse(t1, t2, ...)` applies t1; if it FAILS, applies t2 on the original
    goal, and so on (Z3's or-else falls through on failure, not on a mere lack of
    progress). Each argument may be a `Tactic` or a name string.
    """
    return _compose_tactics("or-else", tactics)


def _as_tactic(t):
    if isinstance(t, str):
        t = Tactic(t)
    if not isinstance(t, Tactic):
        raise TypeError(f"expected Tactic or str, got {t!r}")
    return t


def Repeat(t, max=4294967295):
    """Repeat a tactic to a fixpoint, or at most `max` iterations (z3py `Repeat`).

    `t` may be a `Tactic` or a tactic-name string. AY's `repeat` stops as soon as
    the body makes no progress, so the default (effectively unbounded) `max` still
    terminates at the fixpoint.
    """
    return Tactic._from_spec(("repeat", (_as_tactic(t), int(max))))


def With(t, *args, **kwargs):
    """Attach parameters to a tactic (z3py `With` / `Using`).

    `With(t, k1=v1, k2=v2, ...)` records tactic parameters. AY always applies the
    equivalence-preserving transform, so parameters that would only affect output
    SHAPE (not the model set) are accepted and do not change the result — the
    verdict of a `With(...).solver()` is identical to the base tactic's.
    """
    params = dict(kwargs)
    # z3py also accepts a single positional params-like mapping.
    for a in args:
        if isinstance(a, dict):
            params.update(a)
    return Tactic._from_spec(("with", (_as_tactic(t), params)))


# ---------------------------------------------------------------------------
# Goal + ApplyResult (z3py's Goal and the result of a callable Tactic)
# ---------------------------------------------------------------------------

class Goal:
    """A z3py-compatible Goal: a set of assertion formulas over one Context.

    `g = Goal(); g.add(x > 0); r = Tactic('simplify')(g)` mirrors z3py exactly.
    Like z3py, `add` FLATTENS a top-level conjunction into separate formulas, so
    `Goal().add(And(a, b))` has `len == 2`.
    """

    def __init__(self, models=True, unsat_cores=False, proofs=False, ctx=None, _handle=None):
        self.ctx = ctx or _current_ctx()
        if _handle is not None:
            # Wrapping an existing engine goal (e.g. a tactic subgoal).
            self.handle = _handle
        else:
            self.handle = lib.Z3_mk_goal(
                self.ctx.ref, bool(models), bool(unsat_cores), bool(proofs)
            )
            self.ctx.check_error("Z3_mk_goal")
            if not self.handle:
                raise AyZ3Exception("Z3_mk_goal returned null")

    def add(self, *args):
        """Assert one or more Boolean formulas into the goal (z3py Goal.add).

        A top-level conjunction is flattened into its conjuncts, matching z3py.
        """
        for a in _flatten(args):
            self._assert_one(a)

    # z3py aliases.
    append = add
    insert = add
    assert_exprs = add

    def _assert_one(self, a):
        if isinstance(a, bool):
            a = BoolVal(a, self.ctx)
        if not isinstance(a, AstRef):
            raise AyZ3Exception(f"Goal.add expects a Boolean expression, got {a!r}")
        a = _adopt(a, self.ctx)
        # z3py's Goal splits a top-level `and` into separate formulas.
        if is_and(a):
            for child in a.children():
                self._assert_one(child)
            return
        # z3py drops a trivially-true formula (the identity of conjunction), so
        # `Goal().add(True)` has size 0 — match it. `False` is kept.
        if is_true(a):
            return
        lib.Z3_goal_assert(self.ctx.ref, self.handle, a.ast)
        self.ctx.check_error("Z3_goal_assert")

    def __len__(self):
        return lib.Z3_goal_size(self.ctx.ref, self.handle)

    def size(self):
        """The number of formulas in the goal (z3py Goal.size())."""
        return len(self)

    def __getitem__(self, i):
        n = len(self)
        idx = i + n if i < 0 else i
        if not (0 <= idx < n):
            raise IndexError(f"goal formula index {i} out of range (size={n})")
        ast = lib.Z3_goal_formula(self.ctx.ref, self.handle, idx)
        if not ast:
            raise AyZ3Exception("Z3_goal_formula returned null")
        return _wrap_from_ast(ast, self.ctx)

    def get(self, i):
        """The i-th formula (z3py Goal.get())."""
        return self[i]

    def __iter__(self):
        for i in range(len(self)):
            yield self[i]

    def assertions(self):
        """The goal's formulas as a list (z3py Goal.assertions())."""
        return [self[i] for i in range(len(self))]

    def as_expr(self):
        """The goal as a single expression (z3py Goal.as_expr()).

        Empty -> True, one formula -> that formula, otherwise their conjunction.
        """
        n = len(self)
        if n == 0:
            return BoolVal(True, self.ctx)
        if n == 1:
            return self[0]
        return And(*[self[i] for i in range(n)])

    def sexpr(self):
        """z3py-style `(goal f1 f2 ...)` s-expression."""
        formulas = [self[i].sexpr() for i in range(len(self))]
        if not formulas:
            return "(goal)"
        return "(goal\n  " + "\n  ".join(formulas) + ")"

    def __repr__(self):
        return "[" + ", ".join(repr(self[i]) for i in range(len(self))) + "]"


def _goal_from(spec):
    """Build a `Goal` from a bare expression or a list of expressions."""
    if isinstance(spec, (list, tuple)):
        ctx = _ctx_of([x for x in spec if isinstance(x, AstRef)])
        g = Goal(ctx=ctx)
        g.add(*spec)
        return g
    ctx = spec.ctx if isinstance(spec, AstRef) else _current_ctx()
    g = Goal(ctx=ctx)
    g.add(spec)
    return g


class ApplyResult:
    """The subgoals a `Tactic` produced (z3py ApplyResult).

    `len(r)` is the number of subgoals; `r[i]` is the i-th subgoal as a `Goal`.
    The disjunction of the subgoals is equivalent to the input goal (a normal
    tactic yields one subgoal; a case-splitting tactic yields several).
    """

    def __init__(self, handle, ctx):
        self.handle = handle
        self.ctx = ctx

    def __len__(self):
        return lib.Z3_apply_result_get_num_subgoals(self.ctx.ref, self.handle)

    def __getitem__(self, i):
        n = len(self)
        idx = i + n if i < 0 else i
        if not (0 <= idx < n):
            raise IndexError(f"subgoal index {i} out of range (num_subgoals={n})")
        gh = lib.Z3_apply_result_get_subgoal(self.ctx.ref, self.handle, idx)
        if not gh:
            raise AyZ3Exception("Z3_apply_result_get_subgoal returned null")
        return Goal(ctx=self.ctx, _handle=gh)

    def __iter__(self):
        for i in range(len(self)):
            yield self[i]

    def as_expr(self):
        """Combine the subgoals into one expression (z3py ApplyResult.as_expr()).

        No subgoals -> False, one -> its `as_expr()`, otherwise their disjunction.
        """
        n = len(self)
        if n == 0:
            return BoolVal(False, self.ctx)
        if n == 1:
            return self[0].as_expr()
        return Or(*[self[i].as_expr() for i in range(n)])

    def __repr__(self):
        return repr([self[i] for i in range(len(self))])


# ---------------------------------------------------------------------------
# Misc helpers mirroring z3py
# ---------------------------------------------------------------------------

def is_true(expr):
    return isinstance(expr, BoolRef) and expr.as_bool() is True


def is_false(expr):
    return isinstance(expr, BoolRef) and expr.as_bool() is False


def simplify(expr, *args, **kwargs):
    """Simplify an expression (z3py `simplify`).

    Returns a logically EQUIVALENT, simplified expression. `Z3_simplify`
    rebuilds the term bottom-up through AY's simplifying constructors, folding
    the obvious constant/identity cases z3 folds: closed arithmetic to a
    numeral (`simplify(2 + 3) == 5`), `And`/`Or` with `True`/`False`
    (`simplify(And(True, p)) == p`), `x + 0 == x`, `x * 1 == x`,
    `If(True, a, b) == a`, `Select(Store(a, i, v), i) == v`, etc.

    AY also simplifies eagerly during term construction, so a term built
    entirely through this binding's constructors is already a fixpoint and
    `simplify` returns it unchanged — that is expected, not a bug. AY never
    returns a non-equivalent term. Any z3py simplify tactic params
    (`args`/`kwargs`) are accepted for API compatibility but ignored.
    """
    if not isinstance(expr, AstRef):
        raise NotImplementedError("simplify expects an ayz3 expression")
    ast = lib.Z3_simplify(expr.ctx.ref, expr.ast)
    if ast == 0:
        return expr
    return _wrap(ast, expr.sort_ref, expr.ctx)


# ---------------------------------------------------------------------------
# Expression kind predicates (z3py module-level is_* helpers)
# ---------------------------------------------------------------------------

def is_expr(a):
    """True iff `a` is an ayz3 expression (z3py `is_expr`)."""
    return isinstance(a, AstRef)


def is_bool(a):
    """True iff `a` is a Bool-sorted expression (z3py `is_bool`)."""
    return isinstance(a, AstRef) and a.sort_ref.kind == "Bool"


def is_int(a):
    """True iff `a` is an Int-sorted expression (z3py `is_int`)."""
    return isinstance(a, AstRef) and a.sort_ref.kind == "Int"


def is_real(a):
    """True iff `a` is a Real-sorted expression (z3py `is_real`)."""
    return isinstance(a, AstRef) and a.sort_ref.kind == "Real"


def is_string(a):
    """True iff `a` is a String-sorted expression (z3py `is_string`)."""
    return isinstance(a, AstRef) and a.sort_ref.kind == "String"


# ---------------------------------------------------------------------------
# z3py tutorial/module helper functions (solve / prove / substitute / casts)
# ---------------------------------------------------------------------------
#
# These mirror z3py's top-level convenience functions. `solve` / `prove` build a
# throwaway Solver and PRINT a result line exactly like z3py's demo helpers.
# The value-producing helpers (ToReal / ToInt / IsInt / IntToStr / StrToInt /
# Sqrt / Cbrt / substitute / Fresh*) are thin Python over C primitives that
# already exist in AY's ABI, so they need no Rust rebuild.
#
# NOTE on rendering divergences (all SOUND, documented per the standing law):
#   * AY canonicalizes a commutative `+`/`*` with the numeral operand LAST, so
#     `substitute(x + y, (x, IntVal(3)))` prints `(+ y 3)` where z3py prints
#     `(+ 3 y)` — the same term, different operand order.
#   * AY renders a rational literal as `(/ 1 2)` where z3py prints `(/ 1.0 2.0)`
#     — the same value, so `Sqrt`/`Cbrt`/`Q` differ only in that rendering.
#   * A Fresh* constant's unique-name suffix is AY-internal (e.g. `x!18`) and
#     need not equal z3py's counter; only the freshness/uniqueness is contractual.


def _print_assertions(s):
    """Print a solver's assertions as a bracketed list, z3py's `[c1, c2]` shape.

    z3py's `solve(show=True)` prints `str(Solver)`, which for z3py is the
    bracketed list `[x > 0, x < 10]`. AY's `str(Solver)` is instead the full
    SMT-LIB script (`(declare-fun ...) (assert ...)`), so we render the
    bracketed list ourselves from `s.assertions()`. Since B-4 each element uses
    the z3py-style infix pretty-printer, so the list is z3py-shaped down to the
    element level (`[0 < x, x < 10]`); it differs from z3py only where AY's term
    is canonicalized (here `x > 0` is stored `0 < x`), the same documented,
    sound rendering divergence that applies to every expression in this binding.
    """
    print("[" + ", ".join(str(a) for a in s.assertions()) + "]")


def Abs(x):
    """Absolute value of an arithmetic expression (z3py `Abs`).

    Returns `If(x > 0, x, -x)` — byte-identical to z3py's expansion (at x==0
    both branches are 0, so the strict `>` is exact).
    """
    return If(x > 0, x, -x)


def eq(a, b):
    """True iff `a` and `b` are the SAME AST (z3py `eq` — structural identity,
    not semantic equality).

    AY hash-conses terms, so two structurally-identical terms in one context
    share a handle; `eq` compares handles (and contexts). NOTE: AY normalizes
    eagerly at construction (`x + 0` -> `x`, `a > 5` -> `5 < a`), so `eq` can
    report True for terms z3 considers distinct before simplification — a
    documented consequence of eager normalization, never a wrong result. For a
    boolean SMT equality atom use `a == b` instead.
    """
    if not isinstance(a, AstRef) or not isinstance(b, AstRef):
        return a is b
    return a.ctx is b.ctx and a.ast == b.ast


def SolverFor(logic, ctx=None):
    """A `Solver` specialized for `logic` (z3py `SolverFor('QF_LIA')`).

    Creates a Solver and records the logic. AY dispatches internally by the
    theories it detects regardless of the logic hint, so the hint is accepted
    for compatibility and to steer any logic-specific setup; the verdict is
    unaffected.
    """
    s = Solver(ctx=ctx)
    s.set(logic=logic)
    return s


def tactics(ctx=None):
    """The list of tactic names AY supports on its `(apply ...)` surface
    (z3py `tactics()`).

    Enumerated from the real C registry (`Z3_get_num_tactics`/`_name`) — AY's
    HONEST supported set, not z3's full ~116-name list.
    """
    c = ctx if isinstance(ctx, Context) else Context()
    n = lib.Z3_get_num_tactics(c.ref)
    out = []
    for i in range(n):
        name = lib.Z3_get_tactic_name(c.ref, i)
        if name:
            out.append(name.decode())
    return out


def describe_tactics(ctx=None):
    """Print each supported tactic name with its description (z3py
    `describe_tactics()`)."""
    c = ctx if isinstance(ctx, Context) else Context()
    for name in tactics(c):
        descr = lib.Z3_tactic_get_descr(c.ref, name.encode())
        print("%s : %s" % (name, descr.decode() if descr else ""))


def solve(*args, **keywords):
    """Solve the constraints `*args`, printing a model line (z3py `solve`).

    Builds a throwaway Solver, applies any keyword params (e.g. `timeout=...`),
    asserts the constraints and checks. Prints the satisfying model as z3py does
    (`[x = 3]`), or `no solution` when UNSAT, or `failed to solve` (plus any
    partial model) when the result is unknown. `show=True` first prints the
    asserted constraints as a bracketed list like z3py's `[c1, c2, ...]` (each
    constraint in the z3py-style infix form since B-4, e.g. `0 < x`, differing
    from z3py only where AY canonicalizes the term).
    """
    show = keywords.pop("show", False)
    s = Solver()
    if keywords:
        s.set(**keywords)
    s.add(*args)
    if show:
        _print_assertions(s)
    r = s.check()
    if r == unsat:
        print("no solution")
    elif r == unknown:
        print("failed to solve")
        try:
            print(s.model())
        except AyZ3Exception:
            return
    else:
        print(s.model())


def prove(claim, show=False, **keywords):
    """Try to prove `claim` by refuting its negation (z3py `prove`).

    Asserts `Not(claim)`; prints `proved` when that is UNSAT, `counterexample`
    plus a falsifying model when it is SAT, or `failed to prove` (plus any
    model) when unknown. `claim` must be a Bool expression. `show=True` first
    prints the asserted `Not(claim)` as a bracketed list like z3py's
    `[c1, ...]` (each constraint in AY's SMT-LIB prefix form).
    """
    if not is_bool(claim):
        raise AyZ3Exception("prove expects a Bool claim (Z3 Boolean expression expected)")
    s = Solver()
    if keywords:
        s.set(**keywords)
    s.add(Not(claim))
    if show:
        _print_assertions(s)
    r = s.check()
    if r == unsat:
        print("proved")
    elif r == unknown:
        print("failed to prove")
        print(s.model())
    else:
        print("counterexample")
        print(s.model())


# --- AC substitution: what AY can and CANNOT reproduce from z3py ------------
#
# z3py's `substitute` is a purely STRUCTURAL operation on the term's BUILD TREE.
# A `+`/`*` in z3py is a binary, left-associative, order-preserving node that is
# only pretty-printed flat: `a+b+b+c` is the tree `(+ (+ (+ a b) b) c)` (which
# prints as `(+ a b b c)`), and `substitute(from=(a+b), to=10)` replaces the
# literal `(+ a b)` sub-node -> `(+ 10 b c)`. Whether a `+`/`*` `from` matches
# therefore depends entirely on the source expression's associativity and its
# operand ORDER.
#
# AY does NOT keep that build tree. It FLATTENS and COLLECTS like terms at
# construction and SORTS the operands, so `a+b+b+c` is stored as the single node
# `(+ a (* b 2) c)`. That canonicalization is MANY-TO-ONE and irreversible: many
# distinct z3py source trees collapse to one AY node, and z3py's `substitute`
# answer DIFFERS across those sources. Verified against real z3py 4.15.4:
#
#     source                  z3py substitute(x+y->10)  AY stored node
#     x+y+x  =(+ (+ x y) x)  ->  (+ 10 x)                 (+ (* x 2) y)
#     x+x+y  =(+ (+ x x) y)  ->  (+ x x y)   UNCHANGED    (+ (* x 2) y)     <- same!
#     x+y+x+y               ->  (+ 10 x y)               (+ (* x 2)(* y 2))
#     x+x+y+y               ->  (+ x x y y) UNCHANGED    (+ (* x 2)(* y 2)) <- same!
#     a+b+b+c               ->  (+ 10 b c)               (+ a (* b 2) c)
#     a+(b+b)+c             ->  (+ a b b c) UNCHANGED    (+ a (* b 2) c)    <- same!
#     (x+y)+w =(+ (+ x y) w)->  (+ 10 w)                 (+ x y w)
#     x+(y+w) =(+ x (+ y w))->  (+ x y w)   UNCHANGED    (+ x y w)          <- same!
#
# So for a `from` that is a PROPER sub-multiset of a flattened `+`/`*` node (it
# shares operands with the node but is not the whole node), z3py's result is not
# a function of the AY node alone -- the information it needs was destroyed at
# construction. A "coefficient-multiset splice" (target_ms - from_ms + {to}) can
# reproduce ONE of those sources but is then a WRONG VALUE for the others (e.g.
# it turns `x+x+y+y` into `x+y+10`, disagreeing with z3py's unchanged `2x+2y`),
# which would propagate to a wrong solve()/model. Per the standing law -- no
# wrong values, ever -- ayz3 therefore does NOT guess: it raises a clear,
# limitation-naming error for these unrecoverable AC sub-multiset `from`s.
#
# What IS sound and IS supported (byte-exact via AY's structural Z3_substitute):
#   * every non-AC `from`   (a leaf var, `f(x)`, a comparison, etc.);
#   * an EXACT WHOLE-NODE `+`/`*` match, where `from` equals a `+`/`*` node in
#     `t` (`substitute(x+y, (x+y,10)) -> 10`, `substitute(f(x+y),(x+y,10)) ->
#     f(10)`) -- here AY's canonical node IS the from, with no lost sub-structure;
#   * a genuinely-absent `from` (returns `t` unchanged, matching z3py).
# AY hash-conses, so operand identity below is a plain handle comparison.


def _op_name(ast, ctx):
    """The operator name of an APP node (e.g. '+', '*', '<', 'f'); else None."""
    if lib.Z3_get_ast_kind(ctx.ref, ast) != _lib.Z3_APP_AST:
        return None
    decl = lib.Z3_get_app_decl(ctx.ref, ast)
    if not decl:
        return None
    sym = lib.Z3_get_decl_name(ctx.ref, decl)
    name = lib.Z3_get_symbol_string(ctx.ref, sym)
    return name.decode() if name else None


def _app_arg_handles(ast, ctx):
    """The operand AST handles of an APP node, in order."""
    n = lib.Z3_get_app_num_args(ctx.ref, ast)
    return [lib.Z3_get_app_arg(ctx.ref, ast, i) for i in range(n)]


def _is_ac_from(frm):
    """True iff `frm` is a flattened `+`/`*` application (an AC 'from' term)."""
    if _op_name(frm.ast, frm.ctx) not in ("+", "*"):
        return False
    return lib.Z3_get_app_num_args(frm.ctx.ref, frm.ast) >= 2


def _numeral_value(ast, ctx):
    """The exact value of a numeral AST as a `Fraction`, else None.

    Used to read the collected coefficient `k` out of a `+`-context like-term
    `(* v k)` (and any rational literal). Handles integer (`"2"`), rational
    (`"1/2"`) and decimal (`"2.0"`) renderings AY may emit.
    """
    from fractions import Fraction
    if not lib.Z3_is_numeral_ast(ctx.ref, ast):
        return None
    raw = lib.Z3_get_numeral_string(ctx.ref, ast)
    if not raw:
        return None
    s = raw.decode()
    try:
        return Fraction(s)
    except (ValueError, ZeroDivisionError):
        pass
    try:
        from decimal import Decimal
        return Fraction(Decimal(s))
    except Exception:
        return None


def _plus_term_key_coeff(operand, ctx):
    """Decompose a `+`-node operand into `(base_key, coeff)`.

    A like term `(* v k)` (AY collects `x+x` -> `(* x 2)`, numeral operand in
    any position) contributes base `v` with coefficient `k`; a bare operand
    contributes itself with coefficient 1. `base_key` is a sorted tuple of the
    NON-numeral factor handles, so equal (hash-consed) subterms compare equal.
    Anything not cleanly a numeral-scaled product is left opaque (coeff 1).
    """
    from fractions import Fraction
    if _op_name(operand, ctx) == "*":
        coeff = Fraction(1)
        bases = []
        for f in _app_arg_handles(operand, ctx):
            v = _numeral_value(f, ctx)
            if v is not None:
                coeff *= v
            else:
                bases.append(f)
        if bases:
            return tuple(sorted(bases)), coeff
        # A pure numeric product (constant): treat the whole node as opaque.
        return (operand,), Fraction(1)
    return (operand,), Fraction(1)


def _ac_node_multiset(node_ast, op_name, ctx):
    """The coefficient/multiplicity multiset of a flattened `+`/`*` node.

    For `+`: base -> summed coefficient (seeing through `(* v k)` like terms).
    For `*`: base -> repeated-factor multiplicity (`(* a b b c)` -> b:2). Keys
    are handle tuples; counts are `Fraction`s. This mirrors how AY collects like
    terms, so a `from`'s multiset can be tested for containment in a node.
    """
    from fractions import Fraction
    m = {}
    for operand in _app_arg_handles(node_ast, ctx):
        if op_name == "+":
            key, cnt = _plus_term_key_coeff(operand, ctx)
        else:  # "*": each operand is one factor
            key, cnt = (operand,), Fraction(1)
        m[key] = m.get(key, Fraction(0)) + cnt
    return m


def _is_proper_submultiset(sub, sup):
    """True iff multiset `sub` is contained in `sup` but is NOT equal to it.

    `sub`/`sup` are base_key -> count dicts. Equality (an exact whole-node
    match) returns False — that case is handled soundly by Z3_substitute and
    must NOT raise. A strict containment (a shared-operand sub-multiset that AY
    flattened) returns True — the unrecoverable case."""
    for k, c in sub.items():
        if sup.get(k, 0) < c:
            return False  # not contained at all
    # Contained. Proper iff sup has an extra key or a strictly larger count.
    if len(sub) != len(sup):
        return True
    return any(sub.get(k, 0) != c for k, c in sup.items())


def _unrecoverable_ac_from(t_ast, ctx, from_specs):
    """Return the first AC `from` whose operands survive only as a flattened
    PROPER sub-multiset of some `+`/`*` node in `t` (the case z3py answers from
    build-tree structure AY discarded), else None.

    `from_specs` is a list of `(op_name, from_multiset, from_astref)`.
    """
    stack = [t_ast]
    seen = set()
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        kind = lib.Z3_get_ast_kind(ctx.ref, node)
        if kind == _lib.Z3_QUANTIFIER_AST:
            stack.append(lib.Z3_get_quantifier_body(ctx.ref, node))
            continue
        if kind != _lib.Z3_APP_AST:
            continue
        name = _op_name(node, ctx)
        if name in ("+", "*"):
            node_ms = _ac_node_multiset(node, name, ctx)
            for op_name, from_ms, frm in from_specs:
                if op_name == name and _is_proper_submultiset(from_ms, node_ms):
                    return frm
        for child in _app_arg_handles(node, ctx):
            stack.append(child)
    return None


def substitute(t, *m):
    """Simultaneously replace each `from` with `to` in `t` (z3py `substitute`).

    `m` is a sequence of `(from, to)` expression pairs (or a single list of such
    pairs). Every occurrence of a `from` term in `t` is replaced by the paired
    `to`; the substitution is SIMULTANEOUS (all `from`s are matched against the
    original `t`, so `substitute(x - y, (x, y), (y, x))` swaps them). Each pair's
    `from`/`to` must share a sort.

    z3py matches STRUCTURAL subterms of the build tree. AY's structural
    `Z3_substitute` reproduces that EXACTLY for every non-AC `from` (a leaf var,
    `f(x)`, a comparison, ...) and for an EXACT WHOLE-NODE `+`/`*` match
    (`substitute(x+y, (x+y,10)) -> 10`, `substitute(f(x+y),(x+y,10)) -> f(10)`).

    What it CANNOT reproduce is an associative-commutative `+`/`*` `from` that
    survives in `t` only as a PROPER flattened sub-multiset (it shares operands
    with a `+`/`*` node but is not the whole node, e.g. `(x+y)` inside `x+y+w`).
    AY flattens, collects like terms and sorts at construction, discarding the
    build-tree associativity and operand order that z3py's answer depends on --
    and that loss is many-to-one (see the module comment above): `x+y+x+y` and
    `x+x+y+y` become the same AY node yet z3py substitutes them differently. No
    single value can be right for both, so rather than guess (and risk a wrong
    value that would poison a later solve/model), ayz3 raises a clear error
    naming the limitation. Exact whole-node and non-AC substitutions are exact.
    """
    if not isinstance(t, AstRef):
        raise NotImplementedError("substitute expects an ayz3 expression")
    # Accept substitute(t, [(a, b), (c, d)]) as well as varargs of pairs.
    if len(m) == 1 and isinstance(m[0], (list, tuple)) and m[0] \
            and all(isinstance(p, tuple) for p in m[0]):
        m = tuple(m[0])
    pairs = []
    for p in m:
        if not (isinstance(p, tuple) and len(p) == 2):
            raise NotImplementedError(
                "substitute pairs must be (from, to) tuples"
            )
        frm, to = p
        if not isinstance(frm, AstRef) or not isinstance(to, AstRef):
            raise NotImplementedError(
                "substitute (from, to) must both be ayz3 expressions"
            )
        if _sort_signature(frm.sort_ref) != _sort_signature(to.sort_ref):
            raise AyZ3Exception(
                "substitute: 'from' and 'to' must have the same sort "
                f"(got {frm.sort_ref} and {to.sort_ref})"
            )
        pairs.append((_adopt(frm, t.ctx), _adopt(to, t.ctx)))
    num = len(pairs)
    from_arr = (_lib.Z3_ast * num)(*[a.ast for a, _ in pairs])
    to_arr = (_lib.Z3_ast * num)(*[b.ast for _, b in pairs])

    # Any AC `from` (a `+`/`*` term) that survives in `t` only as a PROPER
    # flattened sub-multiset is unrecoverable -- z3py answers it from build-tree
    # structure AY threw away. Refuse with an honest error instead of guessing a
    # value that could be wrong (and poison a later solve/model). This checks the
    # ORIGINAL `t`; whole-node and non-AC matches are NOT proper sub-multisets,
    # so they never trip it and flow through the sound Z3_substitute below.
    from_specs = [
        (_op_name(frm.ast, t.ctx),
         _ac_node_multiset(frm.ast, _op_name(frm.ast, t.ctx), t.ctx),
         frm)
        for frm, _ in pairs if _is_ac_from(frm)
    ]
    if from_specs:
        bad = _unrecoverable_ac_from(t.ast, t.ctx, from_specs)
        if bad is not None:
            raise AyZ3Exception(
                "substitute: the associative-commutative `from` term "
                f"`{bad.sexpr()}` occurs in `{t.sexpr()}` only as a flattened "
                "sub-multiset of a larger `+`/`*` node. AY collects like terms "
                "and drops operand order/associativity at construction, so the "
                "build-tree structure z3py's structural substitute needs was "
                "destroyed -- distinct source terms that z3py substitutes "
                "differently (e.g. `x+y+x+y` vs `x+x+y+y`) collapse to this same "
                "node. ayz3 refuses to emit a possibly-wrong value here. "
                "Supported: non-AC `from`s and exact whole-node `+`/`*` matches "
                "(e.g. substitute(x+y, (x+y, 10)))."
            )

    # Sound path: AY's structural Z3_substitute is byte-exact for every case
    # that reaches here (leaf/app/comparison `from`s and exact whole `+`/`*`
    # nodes), and correctly leaves a genuinely-absent `from` unchanged.
    ast = lib.Z3_substitute(t.ctx.ref, t.ast, num, from_arr, to_arr)
    if ast == 0:
        t.ctx.check_error("substitute")
        raise AyZ3Exception("AY returned the null AST for a substitute")
    # Substitution is sort-preserving: the result has t's top-level sort.
    return _wrap(ast, t.sort_ref, t.ctx)


def ToReal(a):
    """Coerce an Int (or Bool) expression to Real (z3py `ToReal`).

    On an Int expression this builds `(to_real a)` via `Z3_mk_int2real`. As in
    z3py, a Bool argument becomes `If(a, 1, 0)` as a Real. Any other sort is a
    type error.
    """
    if not isinstance(a, AstRef):
        raise NotImplementedError("ToReal expects an ayz3 expression")
    ctx = a.ctx
    if isinstance(a, BoolRef):
        return If(a, RealVal(1, ctx), RealVal(0, ctx))
    if a.sort_ref.kind != "Int":
        raise AyZ3Exception("ToReal: Z3 integer expression expected")
    ast = lib.Z3_mk_int2real(ctx.ref, a.ast)
    if ast == 0:
        ctx.check_error("ToReal")
        raise AyZ3Exception("AY returned the null AST for ToReal")
    return _wrap(ast, _real_sort(ctx), ctx)


def ToInt(a):
    """Coerce a Real expression to Int via floor (z3py `ToInt`).

    Builds `(to_int a)` via `Z3_mk_real2int`. The argument must be Real.
    """
    if not isinstance(a, AstRef):
        raise NotImplementedError("ToInt expects an ayz3 expression")
    if a.sort_ref.kind != "Real":
        raise AyZ3Exception("ToInt: Z3 real expression expected")
    ctx = a.ctx
    ast = lib.Z3_mk_real2int(ctx.ref, a.ast)
    if ast == 0:
        ctx.check_error("ToInt")
        raise AyZ3Exception("AY returned the null AST for ToInt")
    return _wrap(ast, _int_sort(ctx), ctx)


def IsInt(a):
    """The Bool predicate `a is an integer` for a Real `a` (z3py `IsInt`).

    Builds `(is_int a)` via `Z3_mk_is_int`. The argument must be Real.
    """
    if not isinstance(a, AstRef):
        raise NotImplementedError("IsInt expects an ayz3 expression")
    if a.sort_ref.kind != "Real":
        raise AyZ3Exception("IsInt: Z3 real expression expected")
    ctx = a.ctx
    ast = lib.Z3_mk_is_int(ctx.ref, a.ast)
    if ast == 0:
        ctx.check_error("IsInt")
        raise AyZ3Exception("AY returned the null AST for IsInt")
    return BoolRef(ast, _bool_sort(ctx), ctx)


def IntToStr(s):
    """The decimal string of an Int expression (z3py `IntToStr`).

    Builds `(str.from_int s)` via `Z3_mk_int_to_str`. A Python int is lifted to
    an Int literal first. The result is a String-sorted sequence.
    """
    if not isinstance(s, AstRef):
        s = IntVal(s)
    if s.sort_ref.kind != "Int":
        raise AyZ3Exception("IntToStr: Z3 integer expression expected")
    ctx = s.ctx
    ast = lib.Z3_mk_int_to_str(ctx.ref, s.ast)
    if ast == 0:
        ctx.check_error("IntToStr")
        raise AyZ3Exception("AY returned the null AST for IntToStr")
    return SeqRef(ast, _string_sort(ctx), ctx)


def StrToInt(s):
    """The Int value of a numeric String expression (z3py `StrToInt`).

    Builds `(str.to_int s)` via `Z3_mk_str_to_int`. A Python str is lifted to a
    String literal first. The result is Int-sorted.
    """
    if not isinstance(s, AstRef):
        s = StringVal(s)
    if s.sort_ref.kind != "String":
        raise AyZ3Exception("StrToInt: Z3 string expression expected")
    ctx = s.ctx
    ast = lib.Z3_mk_str_to_int(ctx.ref, s.ast)
    if ast == 0:
        ctx.check_error("StrToInt")
        raise AyZ3Exception("AY returned the null AST for StrToInt")
    return _wrap(ast, _int_sort(ctx), ctx)


def StrToCode(s):
    """The Unicode code point of a length-1 String (z3py `StrToCode`).

    Builds `(str.to_code s)` via `Z3_mk_string_to_code`, an Int — the code point
    of `s` if `s` has length 1, else `-1`. A Python `str` is lifted to a String
    literal first. The result is Int-sorted. Same term z3py's `StrToCode` builds.
    """
    if not isinstance(s, AstRef):
        s = StringVal(s)
    if s.sort_ref.kind != "String":
        raise AyZ3Exception("StrToCode: Z3 string expression expected")
    ctx = s.ctx
    ast = lib.Z3_mk_string_to_code(ctx.ref, s.ast)
    if ast == 0:
        ctx.check_error("StrToCode")
        raise AyZ3Exception("AY returned the null AST for StrToCode")
    return _wrap(ast, _int_sort(ctx), ctx)


def StrFromCode(c):
    """The single-character String for a code-point Int (z3py `StrFromCode`).

    Builds `(str.from_code c)` via `Z3_mk_string_from_code`, a String — the
    length-1 string whose only character is code point `c` (the empty string for
    an out-of-range `c`). A Python int is lifted to an Int literal first. Same
    term z3py's `StrFromCode` builds.
    """
    if not isinstance(c, AstRef):
        c = IntVal(c)
    if c.sort_ref.kind != "Int":
        raise AyZ3Exception("StrFromCode: Z3 integer expression expected")
    ctx = c.ctx
    ast = lib.Z3_mk_string_from_code(ctx.ref, c.ast)
    if ast == 0:
        ctx.check_error("StrFromCode")
        raise AyZ3Exception("AY returned the null AST for StrFromCode")
    return SeqRef(ast, _string_sort(ctx), ctx)


# ---------------------------------------------------------------------------
# Character theory  (z3py CharVal / CharToInt / CharToBv / CharIsDigit)
# ---------------------------------------------------------------------------
#
# AY models a Char as a bounded-Int code point in `[0, 196607]` (Z3's max_char).
# The C builders below carry that model faithfully:
#   * `CharVal(n)` folds to the code-point literal (sort Char, kind 13);
#   * `CharToInt` is the identity onto Int (a Char IS its code point);
#   * `CharToBv` is `int2bv(code, 18)` — an exact, lossless BV18 encoding;
#   * `CharIsDigit` is `48 <= code <= 57`, agreeing with `str.is_digit`.
# Because a `CharVal` is always a literal (AY exposes no symbolic Char const),
# these character operations fold to concrete numerals.
# The eager fold means the `sexpr()` is the normalized value (`65`, `false`,
# `#x00041`) rather than z3py's un-normalized `(char.* (_ Char 65))`, but the OP
# semantics — and thus every sat/unsat verdict — are identical.

_AY_MAX_CHAR = 196607  # Z3's max_char (matches Z3_mk_char's range check)


def CharVal(ch, ctx=None):
    """The character with code point `ch` (z3py `CharVal`; SMT `(_ Char ch)`).

    `ch` is an `int` code point or a length-1 `str` (its ordinal is used), like
    z3py. Builds a Char-sorted literal via `Z3_mk_char`.
    """
    ctx = ctx or _current_ctx()
    if isinstance(ch, str):
        if len(ch) != 1:
            raise AyZ3Exception(
                "CharVal expects a single-character string or an int code point")
        ch = ord(ch)
    if not isinstance(ch, numbers.Integral):
        raise AyZ3Exception("CharVal: character value should be an ordinal (int)")
    ch = int(ch)
    if not (0 <= ch <= _AY_MAX_CHAR):
        raise AyZ3Exception(
            f"CharVal: code point {ch} out of range [0, {_AY_MAX_CHAR}]")
    ast = lib.Z3_mk_char(ctx.ref, ch)
    if ast == 0:
        ctx.check_error("CharVal")
        raise AyZ3Exception("AY returned the null AST for CharVal")
    return _wrap(ast, _char_sort(ctx), ctx)


def _coerce_char(ch, ctx=None):
    """Coerce to a Char-sorted expression (z3py `_coerce_char`).

    A length-1 `str` is lifted via `CharVal`; an existing expression passes
    through; anything else is rejected — matching z3py.
    """
    if isinstance(ch, str):
        return CharVal(ch, ctx)
    if isinstance(ch, AstRef):
        return ch
    raise AyZ3Exception("Character expression expected")


def CharToInt(ch, ctx=None):
    """The Int code point of a character (z3py `CharToInt`; SMT `char.to_int`)."""
    ch = _coerce_char(ch, ctx)
    ctx = ch.ctx
    ast = lib.Z3_mk_char_to_int(ctx.ref, ch.ast)
    if ast == 0:
        ctx.check_error("CharToInt")
        raise AyZ3Exception("AY returned the null AST for CharToInt")
    return _wrap(ast, _int_sort(ctx), ctx)


def CharToBv(ch, ctx=None):
    """The 18-bit-vector code of a character (z3py `CharToBv`; SMT `char.to_bv`).

    The width is Z3's internal char bit-width (18); a code point is `<= 196607 <
    2**18`, so the conversion is lossless.
    """
    ch = _coerce_char(ch, ctx)
    ctx = ch.ctx
    ast = lib.Z3_mk_char_to_bv(ctx.ref, ch.ast)
    if ast == 0:
        ctx.check_error("CharToBv")
        raise AyZ3Exception("AY returned the null AST for CharToBv")
    return _wrap(ast, _bv_sort(18, ctx), ctx)


def CharIsDigit(ch, ctx=None):
    """Whether a character is an ASCII digit (z3py `CharIsDigit`;
    SMT `char.is_digit` == `48 <= code <= 57`)."""
    ch = _coerce_char(ch, ctx)
    ctx = ch.ctx
    ast = lib.Z3_mk_char_is_digit(ctx.ref, ch.ast)
    if ast == 0:
        ctx.check_error("CharIsDigit")
        raise AyZ3Exception("AY returned the null AST for CharIsDigit")
    return _wrap(ast, _bool_sort(ctx), ctx)


def _fresh_const(prefix, sort, ctx):
    """Build a uniquely-named constant of `sort` via `Z3_mk_fresh_const`.

    The generated name is recovered from the app decl so the const can be looked
    up in a model (its name/sort are registered like a declared const).
    """
    ast = lib.Z3_mk_fresh_const(ctx.ref, prefix.encode(), sort.handle)
    if ast == 0:
        ctx.check_error("fresh const")
        raise AyZ3Exception("AY returned the null AST for a fresh constant")
    expr = _wrap(ast, sort, ctx)
    # Recover the generated name so this const can be looked up in a model and
    # rebuilt into another context (like a declared const). AY reports a bare
    # declared constant as a VAR node (not an app), so `Z3_get_app_decl` does
    # not apply; the node's printed form IS its unique name (e.g. `x!33`).
    name = None
    if lib.Z3_is_app(ctx.ref, ast):
        decl = lib.Z3_get_app_decl(ctx.ref, ast)
        sym = lib.Z3_get_decl_name(ctx.ref, decl)
        nm = lib.Z3_get_symbol_string(ctx.ref, sym) if sym else None
        name = nm.decode() if nm else None
    if not name:
        nm = lib.Z3_ast_to_string(ctx.ref, ast)
        name = nm.decode().strip() if nm else None
    if name:
        expr.decl_name = name
        _register_const(expr, name)
    return expr


def FreshInt(prefix="x", ctx=None):
    """A fresh (uniquely named) Int constant (z3py `FreshInt`)."""
    ctx = ctx or _current_ctx()
    return _fresh_const(prefix, _int_sort(ctx), ctx)


def FreshReal(prefix="x", ctx=None):
    """A fresh (uniquely named) Real constant (z3py `FreshReal`)."""
    ctx = ctx or _current_ctx()
    return _fresh_const(prefix, _real_sort(ctx), ctx)


def FreshBool(prefix="b", ctx=None):
    """A fresh (uniquely named) Bool constant (z3py `FreshBool`)."""
    ctx = ctx or _current_ctx()
    return _fresh_const(prefix, _bool_sort(ctx), ctx)


def FreshConst(sort, prefix="c"):
    """A fresh (uniquely named) constant of an arbitrary sort (z3py `FreshConst`)."""
    if not isinstance(sort, SortRef):
        raise NotImplementedError("FreshConst expects an ayz3 SortRef")
    return _fresh_const(prefix, sort, sort.ctx)


def _real_pow(base, exp_text, ctx):
    """Real exponentiation `base ^ RealVal(exp_text)` via `Z3_mk_power`."""
    exp = RealVal(exp_text, ctx)
    ast = lib.Z3_mk_power(ctx.ref, base.ast, exp.ast)
    if ast == 0:
        ctx.check_error("power")
        raise AyZ3Exception("AY returned the null AST for exponentiation")
    return _wrap(ast, _real_sort(ctx), ctx)


def Sqrt(a, ctx=None):
    """The square root of `a` as `a ** (1/2)` over the reals (z3py `Sqrt`).

    A non-expression `a` is lifted to a Real literal. Like z3py, `Sqrt` is a
    real operation: it accepts a Real (or numeric literal) base. An Int-sorted
    expression is rejected (z3py itself errors on `IntRef ** '1/2'`); coerce it
    with `ToReal` first.
    """
    if not isinstance(a, AstRef):
        ctx = ctx or _current_ctx()
        a = RealVal(a, ctx)
    if a.sort_ref.kind != "Real":
        raise AyZ3Exception(
            "Sqrt: Z3 real expression expected (wrap an Int base in ToReal)"
        )
    return _real_pow(a, "1/2", a.ctx)


def Cbrt(a, ctx=None):
    """The cube root of `a` as `a ** (1/3)` over the reals (z3py `Cbrt`).

    A non-expression `a` is lifted to a Real literal; an Int-sorted expression
    is rejected as for `Sqrt` (wrap it in `ToReal`).
    """
    if not isinstance(a, AstRef):
        ctx = ctx or _current_ctx()
        a = RealVal(a, ctx)
    if a.sort_ref.kind != "Real":
        raise AyZ3Exception(
            "Cbrt: Z3 real expression expected (wrap an Int base in ToReal)"
        )
    return _real_pow(a, "1/3", a.ctx)


def Q(a, b, ctx=None):
    """The rational `a/b` as a Real value (z3py `Q`).

    Equivalent to `simplify(RealVal(a) / RealVal(b))`. AY renders a rational as
    `(/ 1 3)` where z3py prints `(/ 1.0 3.0)`; the value is identical.
    """
    ctx = ctx or _current_ctx()
    return simplify(RealVal(a, ctx) / RealVal(b, ctx))


# ---------------------------------------------------------------------------
# Global parameters
# ---------------------------------------------------------------------------

# Process-wide default parameters, applied to Solvers/Optimizers created after
# they are set (z3py's global `set_param`). AY honors `timeout` (ms); other keys
# are recorded for API compatibility but ignored by the engine.
_global_params = {}


def set_param(*args, **kwargs):
    """Set a global parameter (z3py `set_param('timeout', 1000)`).

    Accepts flat ('k1', v1, 'k2', v2, ...) positional pairs, a single dict, and
    keyword params — like z3py. `timeout` (milliseconds) is HONORED at the engine
    level: it is stashed and forwarded to every Solver/Optimize created AFTERWARD
    (verified — a global timeout flips a hard check to `unknown`). Other keys are
    accepted for compatibility. Use `Solver.set(...)` to target one solver.
    """
    if len(args) == 1 and isinstance(args[0], dict):
        kwargs = {**args[0], **kwargs}
        args = ()
    if len(args) % 2 != 0:
        raise NotImplementedError(
            "set_param positional args must be ('key', value, ...) pairs"
        )
    for i in range(0, len(args), 2):
        kwargs[args[i]] = args[i + 1]
    _global_params.update(kwargs)


# z3py exposes `set_option` as an alias of `set_param`.
def set_option(*args, **kwargs):
    """Alias of `set_param` (z3py `set_option`)."""
    return set_param(*args, **kwargs)


def get_param(name):
    """Return a previously-set global parameter value, or None (z3py `get_param`).

    DIVERGENCE (documented): AY's C ABI has no `Z3_global_param_get`, so this
    reads back the Python-side mirror of values set via `set_param`/`set_option`
    (the values actually forwarded to solvers). A key never set through ayz3
    returns None rather than the engine's built-in default.
    """
    return _global_params.get(name)


def reset_params():
    """Clear all global parameters set via `set_param` (z3py `reset_params`).

    Resets ayz3's global-param mirror AND the engine's process-wide global config
    (`Z3_global_param_reset_all`). Solvers created after this see no ayz3-set
    global defaults.
    """
    _global_params.clear()
    try:
        lib.Z3_global_param_reset_all()
    except Exception:
        pass


# ---------------------------------------------------------------------------
# Z3 5.0.0 finite sets (distinct FiniteSet theory)
# ---------------------------------------------------------------------------


def is_finite_set(value):
    return isinstance(value, FiniteSetRef)


def is_finite_set_sort(value):
    return isinstance(value, FiniteSetSortRef)


def FiniteSetEmpty(set_sort):
    if not isinstance(set_sort, FiniteSetSortRef):
        raise AyZ3Exception("FiniteSetEmpty expects a FiniteSetSort")
    ast = lib.Z3_mk_finite_set_empty(set_sort.ctx.ref, set_sort.handle)
    return _wrap(ast, set_sort, set_sort.ctx)


def Singleton(elem):
    if not isinstance(elem, AstRef):
        raise AyZ3Exception("Singleton expects an expression")
    sort = FiniteSetSort(elem.sort_ref)
    return _wrap(
        lib.Z3_mk_finite_set_singleton(elem.ctx.ref, elem.ast), sort, elem.ctx
    )


def _finite_set_pair(s1, s2, operation):
    if not isinstance(s1, FiniteSetRef) or not isinstance(s2, FiniteSetRef):
        raise AyZ3Exception(f"{operation} expects two finite-set expressions")
    if s1.ctx is not s2.ctx or not _sorts_equal(s1.sort_ref, s2.sort_ref):
        raise AyZ3Exception(f"{operation} expects equal finite-set sorts in one context")
    return s1.ctx


def FiniteSetUnion(s1, s2):
    ctx = _finite_set_pair(s1, s2, "FiniteSetUnion")
    return _wrap(
        lib.Z3_mk_finite_set_union(ctx.ref, s1.ast, s2.ast), s1.sort_ref, ctx
    )


def FiniteSetIntersect(s1, s2):
    ctx = _finite_set_pair(s1, s2, "FiniteSetIntersect")
    return _wrap(
        lib.Z3_mk_finite_set_intersect(ctx.ref, s1.ast, s2.ast),
        s1.sort_ref,
        ctx,
    )


def FiniteSetDifference(s1, s2):
    ctx = _finite_set_pair(s1, s2, "FiniteSetDifference")
    return _wrap(
        lib.Z3_mk_finite_set_difference(ctx.ref, s1.ast, s2.ast),
        s1.sort_ref,
        ctx,
    )


def FiniteSetMember(elem, finite_set):
    if not isinstance(finite_set, FiniteSetRef):
        raise AyZ3Exception("FiniteSetMember expects a finite-set expression")
    elem = _coerce(elem, finite_set.sort_ref.element_sort(), finite_set.ctx)
    _same_ctx(elem, finite_set)
    return BoolRef(
        lib.Z3_mk_finite_set_member(finite_set.ctx.ref, elem.ast, finite_set.ast),
        _bool_sort(finite_set.ctx),
        finite_set.ctx,
    )


def In(elem, finite_set):
    """Alias for `FiniteSetMember`, matching z3py 5.0.0."""
    return FiniteSetMember(elem, finite_set)


def FiniteSetSize(finite_set):
    if not isinstance(finite_set, FiniteSetRef):
        raise AyZ3Exception("FiniteSetSize expects a finite-set expression")
    return _wrap(
        lib.Z3_mk_finite_set_size(finite_set.ctx.ref, finite_set.ast),
        _int_sort(finite_set.ctx),
        finite_set.ctx,
    )


def FiniteSetSubset(s1, s2):
    ctx = _finite_set_pair(s1, s2, "FiniteSetSubset")
    return BoolRef(
        lib.Z3_mk_finite_set_subset(ctx.ref, s1.ast, s2.ast),
        _bool_sort(ctx),
        ctx,
    )


def FiniteSetMap(f, finite_set):
    if isinstance(f, FuncDeclRef):
        f = AsArray(f)
    if not isinstance(f, ArrayRef) or not isinstance(finite_set, FiniteSetRef):
        raise AyZ3Exception("FiniteSetMap expects an array/function and a finite set")
    if not _sorts_equal(f.sort_ref.domain_sort, finite_set.sort_ref.element_sort()):
        raise AyZ3Exception("FiniteSetMap function domain differs from set element sort")
    _same_ctx(f, finite_set)
    output_sort = FiniteSetSort(f.sort_ref.range_sort)
    return _wrap(
        lib.Z3_mk_finite_set_map(f.ctx.ref, f.ast, finite_set.ast),
        output_sort,
        f.ctx,
    )


def FiniteSetFilter(predicate, finite_set):
    if isinstance(predicate, FuncDeclRef):
        predicate = AsArray(predicate)
    if not isinstance(predicate, ArrayRef) or not isinstance(finite_set, FiniteSetRef):
        raise AyZ3Exception(
            "FiniteSetFilter expects a predicate array/function and a finite set"
        )
    if predicate.sort_ref.range_sort.kind != "Bool" or not _sorts_equal(
        predicate.sort_ref.domain_sort, finite_set.sort_ref.element_sort()
    ):
        raise AyZ3Exception("FiniteSetFilter expects an element-to-Bool predicate")
    _same_ctx(predicate, finite_set)
    return _wrap(
        lib.Z3_mk_finite_set_filter(
            predicate.ctx.ref, predicate.ast, finite_set.ast
        ),
        finite_set.sort_ref,
        predicate.ctx,
    )


def FiniteSetRange(low, high):
    ctx = _ctx_of([low, high])
    low = _coerce(low, _int_sort(ctx), ctx)
    high = _coerce(high, _int_sort(ctx), ctx)
    _same_ctx(low, high)
    output_sort = FiniteSetSort(_int_sort(ctx))
    return _wrap(
        lib.Z3_mk_finite_set_range(ctx.ref, low.ast, high.ast), output_sort, ctx
    )


# ---------------------------------------------------------------------------
# Legacy sets (sets-as-arrays)
# ---------------------------------------------------------------------------
#
# z3py models a Set over element sort E as `Array(E, Bool)` (SetSort), with
# EmptySet = K(E, False), FullSet = K(E, True), SetAdd = Store(s, e, True),
# IsMember(e, s) = s[e]. AY's C ABI has no native Z3_mk_set_* functions, but it
# DOES expose the full array theory (Z3_mk_array_sort / select / store /
# const_array), which is definitionally identical to z3py's set encoding. We
# therefore back sets on the NATIVE handle path (no SMT-LIB parse needed),
# matching z3py's exact semantics.
#
# EmptySet / FullSet / SetAdd / SetDel produce real ArrayRef-backed sets, so
# they interoperate with Array/Select/Store and appear in models.
#
# SetUnion / SetIntersect / SetDifference / SetComplement need a POINTWISE
# combination of two arrays into a new array. AY has no array-map / pointwise
# array op at the C ABI, so these are represented as LAZY SetRef nodes whose
# `IsMember(e, op)` reduces pointwise to And/Or/Not of element memberships — a
# SOUND, quantifier-free reduction (verified vs z3py). The lazy set itself is
# only usable via membership (its primary use); building it as a concrete array
# value would need the missing native op.
#
# IsSubset is DEFERRED: it requires quantified array reasoning
# (forall x. a[x] => b[x]), which AY does not soundly decide — it returns
# `unknown` via the SMT path, and the FFI quantifier path can yield an UNSOUND
# `unsat`. Rather than risk an unsound verdict, IsSubset raises
# NotImplementedError naming the gap.


def SetSort(elem):
    """The sort of sets over element sort `elem` (z3py: Array(elem, Bool))."""
    if not isinstance(elem, SortRef):
        raise NotImplementedError("SetSort expects an element SortRef")
    return _array_sort(elem, _bool_sort(elem.ctx), elem.ctx)


class SetRef:
    """A lazy set expression for the pointwise algebra ops (union / intersect /
    difference / complement). It records the operator and operand sets; the only
    sound reduction AY backs is membership, so `IsMember(e, setref)` expands to
    a quantifier-free And/Or/Not of the operands' memberships."""

    def __init__(self, op, operands, elem_sort, ctx):
        self.op = op                # "union" | "intersect" | "difference" | "complement"
        self.operands = operands    # list of ArrayRef | SetRef
        self.elem_sort = elem_sort
        self.ctx = ctx

    def member(self, e):
        """The Bool: `e` is a member of this lazy set (pointwise expansion)."""
        e = _coerce(e, self.elem_sort, self.ctx)
        parts = [_set_member_bool(op, e, self.ctx) for op in self.operands]
        if self.op == "union":
            return Or(*parts)
        if self.op == "intersect":
            return And(*parts)
        if self.op == "difference":
            return And(parts[0], Not(parts[1]))
        if self.op == "complement":
            return Not(parts[0])
        raise NotImplementedError(f"unknown set op {self.op!r}")

    def __repr__(self):
        return f"Set[{self.op}]({', '.join(map(repr, self.operands))})"


def _elem_sort_of(s):
    """The element sort of a set (ArrayRef -> its domain; SetRef -> its elem)."""
    if isinstance(s, ArrayRef):
        return s.sort_ref.domain_sort
    if isinstance(s, SetRef):
        return s.elem_sort
    raise NotImplementedError(
        "expected a set (ArrayRef from SetSort, or a SetRef), got " + repr(s)
    )


def _set_member_bool(s, e, ctx):
    """Membership Bool for `e` in set `s`, handling both backed array sets and
    lazy SetRef nodes (pointwise)."""
    if isinstance(s, SetRef):
        return s.member(e)
    if isinstance(s, ArrayRef):
        e = _coerce(e, s.sort_ref.domain_sort, ctx)
        return Select(s, e)
    raise NotImplementedError("expected a set, got " + repr(s))


def EmptySet(elem):
    """Create an empty legacy set, or an empty distinct finite set.

    Z3 5.0 dispatches ``EmptySet(FiniteSetSort(E))`` to the finite-set
    constructor; other element sorts retain z3py's array-backed set encoding.
    """
    if not isinstance(elem, SortRef):
        raise NotImplementedError("EmptySet expects an element SortRef")
    if isinstance(elem, FiniteSetSortRef):
        return FiniteSetEmpty(elem)
    return K(elem, BoolVal(False, elem.ctx))


def FullSet(elem):
    """The universal set over element sort `elem` (z3py: K(elem, True))."""
    if not isinstance(elem, SortRef):
        raise NotImplementedError("FullSet expects an element SortRef")
    return K(elem, BoolVal(True, elem.ctx))


def SetAdd(s, e):
    """Add element `e` to set `s` (z3py: Store(s, e, True))."""
    if isinstance(s, FiniteSetRef):
        e = _coerce(e, s.sort_ref.element_sort(), s.ctx)
        return FiniteSetUnion(Singleton(e), s)
    if not isinstance(s, ArrayRef):
        raise NotImplementedError(
            "SetAdd requires a backed array-set (from EmptySet/FullSet/SetAdd/"
            "a SetSort const), not a lazy union/intersect/difference SetRef"
        )
    return Store(s, e, BoolVal(True, s.ctx))


def SetDel(s, e):
    """Remove element `e` from set `s` (z3py: Store(s, e, False))."""
    if isinstance(s, FiniteSetRef):
        e = _coerce(e, s.sort_ref.element_sort(), s.ctx)
        return FiniteSetDifference(s, Singleton(e))
    if not isinstance(s, ArrayRef):
        raise NotImplementedError(
            "SetDel requires a backed array-set (from EmptySet/FullSet/SetAdd/"
            "a SetSort const), not a lazy union/intersect/difference SetRef"
        )
    return Store(s, e, BoolVal(False, s.ctx))


def IsMember(e, s):
    """Whether element `e` is a member of set `s` (z3py: s[e]).

    Works for both backed array-sets (Select) and lazy algebra SetRefs
    (pointwise And/Or/Not expansion)."""
    if isinstance(s, FiniteSetRef):
        return FiniteSetMember(e, s)
    ctx = s.ctx if isinstance(s, (ArrayRef, SetRef)) else _current_ctx()
    return _set_member_bool(s, e, ctx)


def SetUnion(*args):
    """Union of sets (lazy; membership-reducible). z3py SetUnion(a, b, ...)."""
    args = _flatten(args)
    if not args:
        raise NotImplementedError("SetUnion needs at least one set")
    if isinstance(args[0], FiniteSetRef):
        result = args[0]
        for arg in args[1:]:
            result = FiniteSetUnion(result, arg)
        return result
    elem = _elem_sort_of(args[0])
    ctx = args[0].ctx
    return SetRef("union", list(args), elem, ctx)


def SetIntersect(*args):
    """Intersection of sets (lazy; membership-reducible)."""
    args = _flatten(args)
    if not args:
        raise NotImplementedError("SetIntersect needs at least one set")
    if isinstance(args[0], FiniteSetRef):
        result = args[0]
        for arg in args[1:]:
            result = FiniteSetIntersect(result, arg)
        return result
    elem = _elem_sort_of(args[0])
    ctx = args[0].ctx
    return SetRef("intersect", list(args), elem, ctx)


def SetDifference(a, b):
    """Set difference a \\ b (lazy; membership-reducible)."""
    if isinstance(a, FiniteSetRef):
        return FiniteSetDifference(a, b)
    elem = _elem_sort_of(a)
    return SetRef("difference", [a, b], elem, a.ctx)


def SetComplement(s):
    """Set complement (lazy; membership-reducible)."""
    elem = _elem_sort_of(s)
    return SetRef("complement", [s], elem, s.ctx)


def IsSubset(a, b):
    """DEFERRED: subset needs quantified array reasoning (forall x. a[x]=>b[x]),
    which AY does not soundly decide (returns unknown; the FFI quantifier path
    can yield an UNSOUND unsat). Raises rather than risk an unsound result."""
    if isinstance(a, FiniteSetRef):
        return FiniteSetSubset(a, b)
    raise NotImplementedError(
        "IsSubset is not soundly backed by AY: it requires quantified array "
        "reasoning (forall x. a[x] => b[x]); AY returns `unknown` via the SMT "
        "path and the FFI quantifier path is unsound for arrays. Encode subset "
        "explicitly per-element if your element domain is finite/bounded."
    )


# ---------------------------------------------------------------------------
# SMT-LIB2 parsing
# ---------------------------------------------------------------------------

def parse_smtlib2_string(s, sorts=None, decls=None, ctx=None):
    """Parse an SMT-LIB2 string; return its assertions as a list of expressions.

    Mirrors z3py's `parse_smtlib2_string` (which returns an AstVector); ayz3
    returns a plain Python list of BoolRef/AstRef. The `sorts`/`decls`
    pre-declaration maps are accepted for API compatibility but ignored — every
    sort and function used must be declared inside the string itself (AY's C ABI
    parses a self-contained SMT-LIB2 fragment). Query commands (`check-sat`,
    `get-model`, ...) in the string are ignored; only assertions are returned.
    """
    if sorts:
        raise NotImplementedError(
            "parse_smtlib2_string: pre-declared `sorts` are not supported by AY's "
            "C ABI; declare all sorts inside the SMT-LIB2 string"
        )
    if decls:
        raise NotImplementedError(
            "parse_smtlib2_string: pre-declared `decls` are not supported by AY's "
            "C ABI; declare all functions inside the SMT-LIB2 string"
        )
    ctx = ctx or _current_ctx()
    vec = lib.Z3_parse_smtlib2_string(
        ctx.ref, str(s).encode(), 0, None, None, 0, None, None
    )
    ctx.check_error("parse_smtlib2_string")
    # Each returned element is the argument of a top-level SMT-LIB `(assert ...)`,
    # which the SMT-LIB standard requires to be Bool-sorted. AY's FFI does not
    # track sorts for parsed terms (Z3_get_sort returns null for them), so we
    # wrap them as BoolRef according to that parser contract.
    if not vec:
        return []
    bool_sort = _bool_sort(ctx)
    n = lib.Z3_ast_vector_size(ctx.ref, vec)
    out = []
    for i in range(n):
        a = lib.Z3_ast_vector_get(ctx.ref, vec, i)
        if a == 0:
            continue
        out.append(BoolRef(a, bool_sort, ctx))
    return out


def parse_smtlib2_file(path, sorts=None, decls=None, ctx=None):
    """Parse an SMT-LIB2 file; return its assertions as a list of expressions.

    AY's C ABI has no file-parsing entry point, so ayz3 reads the file and
    delegates to `parse_smtlib2_string` (functionally identical to z3py's
    `parse_smtlib2_file`).
    """
    with open(path, "r", encoding="utf-8") as fh:
        text = fh.read()
    return parse_smtlib2_string(text, sorts=sorts, decls=decls, ctx=ctx)


def parse_smt2_string(s, sorts=None, decls=None, ctx=None):
    """Parse an SMT-LIB2 string; return its assertions (z3py's public name).

    Stock z3py exposes the SMT-LIB2 parse entry point as `parse_smt2_string`
    (the C symbol it calls is `Z3_parse_smtlib2_string`). This is the drop-in
    name z3py programs use; it delegates to `parse_smtlib2_string`. z3py returns
    an `AstVector`; ayz3 returns a plain Python list of BoolRef (ayz3's uniform
    convention for every vector-returning API — `len()`, iteration, and
    `Solver.add(*result)` all behave identically). The `sorts`/`decls`
    pre-declaration maps are accepted for API compatibility; a non-empty map
    raises `NotImplementedError` (AY's C ABI parses a self-contained fragment,
    so declare every sort/function inside the string) rather than silently
    ignoring an injected binding and mis-parsing.

    >>> from ayz3 import parse_smt2_string
    >>> parse_smt2_string('(declare-const x Int) (assert (> x 0)) (assert (< x 10))')
    [0 < x, x < 10]
    """
    return parse_smtlib2_string(s, sorts=sorts, decls=decls, ctx=ctx)


def parse_smt2_file(f, sorts=None, decls=None, ctx=None):
    """Parse an SMT-LIB2 file; return its assertions (z3py's public name).

    Mirror of stock z3py's `parse_smt2_file`; delegates to
    `parse_smtlib2_file`. See `parse_smt2_string` for the return-type and
    `sorts`/`decls` handling notes.
    """
    return parse_smtlib2_file(f, sorts=sorts, decls=decls, ctx=ctx)


__all__ = [
    "sat", "unsat", "unknown", "CheckSatResult",
    "Context",
    "Int", "Real", "Bool", "BitVec", "Const",
    "Ints", "Reals", "Bools", "BitVecs", "Consts", "Strings",
    "IntVal", "RealVal", "BoolVal", "BitVecVal",
    "IntNumRef", "RatNumRef", "BitVecNumRef",
    "IntSort", "RealSort", "BoolSort", "BitVecSort",
    "And", "Or", "Not", "Implies", "Xor", "If", "Distinct",
    # Pseudo-boolean / cardinality constraints
    "AtMost", "AtLeast", "PbLe", "PbGe", "PbEq",
    "Sum", "Product",
    "ULT", "ULE", "UGT", "UGE",
    # Bitvector operations (B-10)
    "UDiv", "URem", "SRem", "SMod", "SDiv", "LShR", "AShR",
    "SignExt", "ZeroExt", "RepeatBitVec", "RotateLeft", "RotateRight",
    "BV2Int", "Int2BV", "BVRedAnd", "BVRedOr",
    "BVAddNoOverflow", "BVAddNoUnderflow", "BVSubNoOverflow",
    "BVSubNoUnderflow", "BVMulNoOverflow", "BVMulNoUnderflow",
    "BVSDivNoOverflow",
    # Arrays
    "Array", "ArraySort", "Select", "Store", "K", "Update", "Map", "Ext",
    "ArrayRef", "AsArray",
    # Uninterpreted functions
    "Function", "FuncDeclRef", "RecFunction", "RecAddDefinition",
    # Quantifiers
    "ForAll", "Exists", "Lambda", "MultiPattern", "PatternRef", "is_pattern",
    # Strings / sequences
    "String", "StringVal", "StringSort", "SeqSort", "SeqRef",
    "Concat", "Length", "Contains", "PrefixOf", "SuffixOf",
    "IndexOf", "SubString", "SubSeq", "Extract", "Replace", "Unit",
    "StrToCode", "StrFromCode",
    # Character theory
    "CharVal", "CharToInt", "CharToBv", "CharIsDigit",
    # Regular expressions (RegLan)
    "ReSort", "ReRef", "Re", "to_re", "InRe",
    "Star", "Plus", "Option", "Complement",
    "Union", "Intersect", "Range", "Loop",
    "Full", "Empty", "AllChar",
    "Solver", "Optimize", "ModelRef", "Statistics",
    # Parameters / parameter-descriptor sets
    "Params", "ParamsRef", "ParamDescrs", "ParamDescrsRef", "args2params",
    # Tactics (goal-to-goal transformations)
    "Tactic", "Then", "OrElse", "Repeat", "With", "Goal", "ApplyResult",
    # Version
    "get_version_string", "get_version",
    "AstRef", "ArithRef", "BoolRef", "BitVecRef", "SortRef", "DatatypeRef",
    "AyZ3Exception", "is_true", "is_false", "simplify",
    # Expression kind predicates
    "is_expr", "is_bool", "is_int", "is_real", "is_string",
    # z3py tutorial/module helpers
    "solve",
    "describe_tactics",
    "tactics",
    "SolverFor",
    "eq",
    "Abs", "prove", "substitute",
    "ToReal", "ToInt", "IsInt", "IntToStr", "StrToInt",
    "FreshInt", "FreshReal", "FreshBool", "FreshConst",
    "Sqrt", "Cbrt", "Q",
    # Phase-4 solver surface
    "parse_smtlib2_string", "parse_smtlib2_file",
    "parse_smt2_string", "parse_smt2_file",
    "set_param", "get_param", "set_option", "reset_params",
    # Phase-4 sets (sets-as-arrays; native handle path)
    "SetSort", "EmptySet", "FullSet", "SetAdd", "SetDel", "IsMember",
    "SetUnion", "SetIntersect", "SetDifference", "SetComplement",
    "IsSubset", "SetRef",
    # Z3 5.0.0 distinct finite-set theory
    "FiniteSetSort", "FiniteSetSortRef", "FiniteSetRef", "FiniteSetEmpty",
    "Singleton", "FiniteSetUnion", "FiniteSetIntersect", "FiniteSetDifference",
    "FiniteSetMember", "In", "FiniteSetSize", "FiniteSetSubset", "FiniteSetMap",
    "FiniteSetFilter", "FiniteSetRange", "is_finite_set", "is_finite_set_sort",
    # Floating point (native Z3_mk_fpa_* handles; re-exported from ayz3.fp)
    "FPSort", "Float16", "FloatHalf", "Float32", "FloatSingle",
    "Float64", "FloatDouble", "Float128", "FloatQuadruple",
    "RoundNearestTiesToEven", "RNE", "RoundNearestTiesToAway", "RNA",
    "RoundTowardPositive", "RTP", "RoundTowardNegative", "RTN",
    "RoundTowardZero", "RTZ",
    "get_default_rounding_mode", "set_default_rounding_mode",
    "get_default_fp_sort", "set_default_fp_sort",
    "FP", "FPs", "FPVal",
    "fpNaN", "fpPlusInfinity", "fpMinusInfinity", "fpInfinity",
    "fpPlusZero", "fpMinusZero", "fpZero",
    "fpAdd", "fpSub", "fpMul", "fpDiv", "fpNeg", "fpAbs",
    "fpSqrt", "fpFMA", "fpRem", "fpRoundToIntegral", "fpMin", "fpMax",
    "fpEQ", "fpNEQ", "fpLT", "fpLEQ", "fpGT", "fpGEQ",
    "fpIsNaN", "fpIsInf", "fpIsInfinite", "fpIsZero",
    "fpIsNegative", "fpIsPositive", "fpIsNormal", "fpIsSubnormal",
    "fpToFP", "fpFPToFP", "fpSignedToFP",
    "is_fp", "is_fp_value", "is_fprm", "is_fprm_value",
    "is_fp_sort", "is_fprm_sort",
    "FPRef", "FPNumRef", "FPSortRef", "FPRMSortRef", "FPRMRef",
    # FP conversions (native Z3_mk_fpa_* exports; see fpa_ext.rs /
    # fpa_introspect.rs on the Rust side)
    "fpRealToFP", "fpUnsignedToFP", "fpBVToFP",
    "fpToSBV", "fpToUBV", "fpToReal", "fpToIEEEBV", "fpFP",
    # Back-compat aliases from the old fragment-based FP layer
    "FpAnd", "FpOr", "FpNot", "FpImplies",
    "FPSolver", "FPBoolRef", "FPModelRef",
    # Fixedpoint / CHC (re-exported from ayz3.fixedpoint)
    "Fixedpoint",
]


# ---------------------------------------------------------------------------
# Floating point: re-export the ayz3.fp module surface.
#
# FP terms are NATIVE Z3_mk_fpa_* handles (the dylib exports the full fpa
# term-constructor surface — verified via nm), so FP constraints are ordinary
# BoolRefs solved by the regular Solver and read back via the regular
# ModelRef, matching z3py. See ayz3/fp.py for the backed/absent split.
# ---------------------------------------------------------------------------

from .fp import (  # noqa: E402
    FPSort, Float16, FloatHalf, Float32, FloatSingle,
    Float64, FloatDouble, Float128, FloatQuadruple,
    RoundNearestTiesToEven, RNE, RoundNearestTiesToAway, RNA,
    RoundTowardPositive, RTP, RoundTowardNegative, RTN,
    RoundTowardZero, RTZ,
    get_default_rounding_mode, set_default_rounding_mode,
    get_default_fp_sort, set_default_fp_sort,
    FP, FPs, FPVal,
    fpNaN, fpPlusInfinity, fpMinusInfinity, fpInfinity,
    fpPlusZero, fpMinusZero, fpZero,
    fpAdd, fpSub, fpMul, fpDiv, fpNeg, fpAbs,
    fpSqrt, fpFMA, fpRem, fpRoundToIntegral, fpMin, fpMax,
    fpEQ, fpNEQ, fpLT, fpLEQ, fpGT, fpGEQ,
    fpIsNaN, fpIsInf, fpIsInfinite, fpIsZero,
    fpIsNegative, fpIsPositive, fpIsNormal, fpIsSubnormal,
    fpToFP, fpFPToFP, fpSignedToFP,
    fpRealToFP, fpUnsignedToFP, fpBVToFP,
    fpToSBV, fpToUBV, fpToReal, fpToIEEEBV, fpFP,
    is_fp, is_fp_value, is_fprm, is_fprm_value, is_fp_sort, is_fprm_sort,
    FPRef, FPNumRef, FPSortRef, FPRMSortRef, FPRMRef,
    FpAnd, FpOr, FpNot, FpImplies,
)

# Back-compat aliases for the pre-native ayz3 FP layer: FP constraints are now
# ordinary BoolRefs solved by the ordinary Solver / read via the ordinary
# ModelRef, so the old dedicated FP types alias the general ones.
FPSolver = Solver
FPBoolRef = BoolRef
FPModelRef = ModelRef

# ---------------------------------------------------------------------------
# Fixedpoint (CHC / Horn clauses): re-export the ayz3.fixedpoint surface,
# backed by ay-chc through the dylib's 8 Z3_fixedpoint_* C entry points.
# See ayz3/fixedpoint.py for the backed/unbacked breakdown.
# ---------------------------------------------------------------------------

from .fixedpoint import Fixedpoint  # noqa: E402


# ---------------------------------------------------------------------------
# AST introspection (B-3): z3py-shaped module predicates (is_add/is_and/...) and
# AstRef/FuncDeclRef accessors (.decl()/.children()/.arg(i)/... and FuncDeclRef
# .domain(i)/.range()/.kind()/.params()), attached over the now-correct C ABI.
# Attaching happens here — after AstRef, FuncDeclRef and __all__ are defined — so
# the mixins land on the real classes and the predicates join the public surface.
# ---------------------------------------------------------------------------

import sys as _sys  # noqa: E402
from . import introspect as _introspect  # noqa: E402

_public_ast_sexpr = AstRef.sexpr
_introspect.install(_sys.modules[__name__])
# Introspection supplies a generic raw-AST `sexpr`; retain the public rendering
# above so as-array terms never expose AY's private function identities.
AstRef.sexpr = _public_ast_sexpr


# ---------------------------------------------------------------------------
# z3py-style infix pretty-printer (B-4): rebinds AstRef.__repr__/__str__ so an
# expression prints its z3py infix surface form (`x + 2*y`, `x <= y`,
# `And(p, q)`, `a[i]`, `ForAll(x, ...)`) instead of the raw s-expression. Walks
# the B-3 introspection API installed just above, so it must run AFTER it.
# ---------------------------------------------------------------------------

from . import printer as _printer  # noqa: E402

_printer.install(_sys.modules[__name__])
_infix_ast_repr = AstRef.__repr__


def _as_array_aware_ast_repr(self):
    """Keep the infix printer except where it would leak a private as-array."""
    if not getattr(self, "_is_model_value", False):
        raw = lib.Z3_ast_to_string(self.ctx.ref, self.ast)
        if raw:
            text = raw.decode()
            public = _canonicalize_as_array_text(text, self.ctx)
            if public != text:
                return public
    return _infix_ast_repr(self)


AstRef.__repr__ = _as_array_aware_ast_repr
AstRef.__str__ = _as_array_aware_ast_repr


# ---------------------------------------------------------------------------
# Algebraic datatypes (B-6): Datatype / EnumSort / TupleSort, wired onto AY's
# datatype C ABI. Installed here — after the AstRef/SortRef/FuncDeclRef surface
# and __all__ exist, and after the cross-context rebuild machinery it hooks into
# is defined — so DatatypeRef model values and cross-context rebuild both work.
# ---------------------------------------------------------------------------

from . import datatypes as _datatypes  # noqa: E402

_datatypes.install(_sys.modules[__name__])
