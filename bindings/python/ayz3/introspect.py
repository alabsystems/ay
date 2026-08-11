# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# z3py-shaped AST introspection layer (B-3).
#
# z3py term programs inspect an expression's shape through a family of module
# predicates (is_add / is_and / is_const / ...) and AstRef/FuncDeclRef accessors
# (.decl(), .children(), .num_args(), .arg(i), .sexpr(), and FuncDeclRef
# .name()/.arity()/.domain(i)/.range()/.kind()/.params()). This module builds
# those on top of AY's now-correct C ABI (Z3_get_ast_kind / Z3_get_app_decl /
# Z3_get_decl_kind / Z3_get_app_num_args / Z3_get_app_arg / Z3_get_decl_name).
#
# EVERY predicate reflects the REAL, AY-stored term — never a guess. AY normalizes
# eagerly at construction (a documented, sound canonicalization), so a handful of
# operators are stored in an equivalent normal form rather than the surface form
# z3py keeps:
#
#   * comparisons are oriented `<`/`<=` : `x > y` is stored as `(< y x)`, so
#     is_gt/is_ge report False and is_lt/is_le report True on that term;
#   * subtraction folds into addition : `x - y` is stored as `(+ x (- y))`, so
#     is_sub reports False and is_add True;
#   * `x != y` / binary Distinct fold to `(not (= x y))` (is_not, not
#     is_distinct); Implies folds to `(or q (not p))` (is_or, not is_implies).
#
# These are the SAME sound normalizations documented for B-1's printing path.
# The predicates report AY's actual term honestly; the divergences are covered by
# regression tests that assert the honest ayz3 answer alongside z3py's.
#
# The C ABI represents a declared constant (Int('x')) as a Z3_VAR_AST whose
# Z3_get_app_decl is NULL, and a literal as a Z3_NUMERAL_AST (also NULL decl), so
# `.decl()` for those recovers the name/kind from the wrapper's construction-time
# metadata instead of the (unavailable) app decl. AY uses constant-style
# quantifiers, so a bound variable is an ordinary declared constant and no raw
# de-Bruijn variable is ever surfaced; hence is_var is always False (matching how
# z3py classifies a declared constant: an app, not a var).

from . import _lib

lib = _lib.lib

# ---------------------------------------------------------------------------
# Z3_ast_kind (Z3_get_ast_kind). Byte-for-byte upstream Z3 (verified 4.15.4).
# ---------------------------------------------------------------------------
Z3_NUMERAL_AST = 0
Z3_APP_AST = 1
Z3_VAR_AST = 2
Z3_QUANTIFIER_AST = 3

# ---------------------------------------------------------------------------
# Z3_decl_kind subset (Z3_get_decl_kind). Byte-for-byte upstream Z3 (verified
# against AY's actual returns and z3py 4.15.4).
# ---------------------------------------------------------------------------
Z3_OP_TRUE = 256
Z3_OP_FALSE = 257
Z3_OP_EQ = 258
Z3_OP_DISTINCT = 259
Z3_OP_ITE = 260
Z3_OP_AND = 261
Z3_OP_OR = 262
Z3_OP_IFF = 263
Z3_OP_XOR = 264
Z3_OP_NOT = 265
Z3_OP_IMPLIES = 266

Z3_OP_ANUM = 512
Z3_OP_LE = 514
Z3_OP_GE = 515
Z3_OP_LT = 516
Z3_OP_GT = 517
Z3_OP_ADD = 518
Z3_OP_SUB = 519
Z3_OP_UMINUS = 520
Z3_OP_MUL = 521
Z3_OP_DIV = 522
Z3_OP_IDIV = 523
Z3_OP_MOD = 525
Z3_OP_TO_REAL = 526
Z3_OP_TO_INT = 527

Z3_OP_STORE = 768
Z3_OP_SELECT = 769

Z3_OP_BNUM = 1024
Z3_OP_BADD = 1028

Z3_OP_FINITE_SET_EMPTY = 49152
Z3_OP_FINITE_SET_SINGLETON = 49153
Z3_OP_FINITE_SET_UNION = 49154
Z3_OP_FINITE_SET_INTERSECT = 49155
Z3_OP_FINITE_SET_DIFFERENCE = 49156
Z3_OP_FINITE_SET_IN = 49157
Z3_OP_FINITE_SET_SIZE = 49158
Z3_OP_FINITE_SET_SUBSET = 49159
Z3_OP_FINITE_SET_MAP = 49160
Z3_OP_FINITE_SET_FILTER = 49161
Z3_OP_FINITE_SET_RANGE = 49162
Z3_OP_FINITE_SET_EXT = 49163
Z3_OP_FINITE_SET_MAP_INVERSE = 49164
Z3_OP_INTERNAL = 49165
Z3_OP_RECURSIVE = 49166
Z3_OP_UNINTERPRETED = 49167

Z3_PARAMETER_INT = 0
Z3_PARAMETER_SORT = 4

# Sequence/string value decl kind (z3py reports StringVal(...).decl().kind()).
Z3_OP_SEQ_VALUE = 45100

# The parent `ayz3` module, wired by install().
_M = None


# ---------------------------------------------------------------------------
# Low-level accessors over the C ABI
# ---------------------------------------------------------------------------

def _is_ast(a):
    return _M is not None and isinstance(a, _M.AstRef)


def _ast_kind(a):
    return lib.Z3_get_ast_kind(a.ctx.ref, a.ast)


def _decl_name_of(ctx, decl):
    sym = lib.Z3_get_decl_name(ctx.ref, decl)
    nm = lib.Z3_get_symbol_string(ctx.ref, sym)
    return nm.decode() if nm else ""


def _decl_kind(a):
    """The Z3_get_decl_kind of an application node, or None for non-apps.

    A declared constant (VAR) and a literal (NUMERAL) have a NULL app decl in
    AY's C ABI, so they are not routed here — their decl kind is synthesized in
    `_expr_decl` from the wrapper's construction-time metadata.
    """
    if _ast_kind(a) != Z3_APP_AST:
        return None
    decl = lib.Z3_get_app_decl(a.ctx.ref, a.ast)
    if not decl:
        return None
    return lib.Z3_get_decl_kind(a.ctx.ref, decl)


def _num_args(a):
    """Number of arguments of an app / 0 for a const-or-literal.

    Raises for a quantifier (as z3py's Z3_get_app_num_args does), so callers
    that reach it have already excluded quantifiers via is_app.
    """
    k = _ast_kind(a)
    if k == Z3_APP_AST:
        return lib.Z3_get_app_num_args(a.ctx.ref, a.ast)
    if k in (Z3_NUMERAL_AST, Z3_VAR_AST):
        return 0
    raise _M.AyZ3Exception("num_args() is not defined on a quantifier")


# ---------------------------------------------------------------------------
# Module predicates (dispatch on the real ast_kind / decl_kind)
# ---------------------------------------------------------------------------

def is_expr(a):
    """True for any ayz3 expression (z3py is_expr)."""
    return _is_ast(a)


def _sorted(a, kind):
    return _is_ast(a) and a.sort_ref.kind == kind


def is_int(a):
    """Int-sorted arithmetic expression (z3py is_int)."""
    return _sorted(a, "Int")


def is_real(a):
    """Real-sorted arithmetic expression (z3py is_real)."""
    return _sorted(a, "Real")


def is_bool(a):
    """Bool-sorted expression (z3py is_bool)."""
    return _sorted(a, "Bool")


def is_bv(a):
    """Bitvector-sorted expression (z3py is_bv)."""
    return _sorted(a, "BitVec")


def is_array(a):
    """Array-sorted expression (z3py is_array)."""
    return _sorted(a, "Array")


def is_string(a):
    """String-sorted (sequence) expression (z3py is_string)."""
    return _sorted(a, "String")


def is_seq(a):
    """Sequence-sorted expression (z3py is_seq); AY models String as a seq."""
    return _sorted(a, "String")


def is_app(a):
    """z3py is_app: True for an application or a literal.

    AY stores a declared constant as a Z3_VAR_AST; z3py classifies a declared
    constant as a 0-arity application, so VAR maps to app here. AY never exposes
    a raw de-Bruijn variable (constant-style quantifiers), so this is exact.
    """
    if not _is_ast(a):
        return False
    return _ast_kind(a) in (Z3_NUMERAL_AST, Z3_APP_AST, Z3_VAR_AST)


def is_const(a):
    """z3py is_const: an application (or literal) with no arguments."""
    return is_app(a) and _num_args(a) == 0


def is_var(a):
    """z3py is_var: a de-Bruijn bound variable.

    AY uses constant-style quantifiers, so a bound variable is an ordinary
    declared constant (which z3py — and this layer — classify as an app, not a
    var). AY therefore never surfaces a raw bound variable, so this is False for
    every ayz3 term.
    """
    return False


def is_quantifier(a):
    """z3py is_quantifier: a ForAll/Exists node."""
    return _is_ast(a) and _ast_kind(a) == Z3_QUANTIFIER_AST


def is_app_of(a, k):
    """z3py is_app_of: an application whose declaration kind is `k`."""
    return _is_ast(a) and _decl_kind(a) == k


# --- operator predicates (route on the real decl kind) ---------------------

def is_and(a):
    # A term built by ayz3.Distinct is STORED as an eager-expanded `and`, but its
    # z3py identity is `distinct` (see is_distinct/decl). Present it consistently:
    # a distinct node is NOT an `and`, exactly as in z3py.
    if _is_ast(a) and getattr(a, "_distinct_args", None) is not None:
        return False
    return is_app_of(a, Z3_OP_AND)


def is_or(a):
    return is_app_of(a, Z3_OP_OR)


def is_not(a):
    return is_app_of(a, Z3_OP_NOT)


def is_implies(a):
    return is_app_of(a, Z3_OP_IMPLIES)


def is_eq(a):
    return is_app_of(a, Z3_OP_EQ)


def is_distinct(a):
    # A term built by ayz3.Distinct carries a `_distinct_args` marker even though
    # AY's core eager-expands it to `(and (not (= ...)) ...)`; honor that marker
    # so the z3py-observable `is_distinct` is True (matching z3py, which keeps a
    # real distinct node). Fall back to the decl-kind check for any other term.
    return (_is_ast(a) and getattr(a, "_distinct_args", None) is not None) or is_app_of(
        a, Z3_OP_DISTINCT
    )


def is_add(a):
    return is_app_of(a, Z3_OP_ADD)


def is_mul(a):
    return is_app_of(a, Z3_OP_MUL)


def is_sub(a):
    # A binary subtraction. AY normalizes `x - y` to `(+ x (- y))`, so no binary
    # SUB node is ever stored; this honestly reports False on such a term (and
    # is_add reports True). The arity guard also keeps AY's unary `-` (which
    # shares the SUB decl kind) from being misreported as a subtraction.
    return is_app_of(a, Z3_OP_SUB) and _num_args(a) == 2


def is_div(a):
    # z3py's is_div is DIV-only (real division, Z3_OP_DIV). Integer division is
    # is_idiv (Z3_OP_IDIV). `x / y` for Real x,y is a DIV; for Int x,y it is an
    # IDIV, so is_div reports False on it (matching z3py).
    return is_app_of(a, Z3_OP_DIV)


def is_idiv(a):
    # z3py's is_idiv: the SMT-LIB integer-division operator (Z3_OP_IDIV). `x / y`
    # for Int x,y is an IDIV (decl name 'div', kind 523).
    return is_app_of(a, Z3_OP_IDIV)


def is_mod(a):
    return is_app_of(a, Z3_OP_MOD)


def is_le(a):
    return is_app_of(a, Z3_OP_LE)


def is_lt(a):
    return is_app_of(a, Z3_OP_LT)


def is_ge(a):
    return is_app_of(a, Z3_OP_GE)


def is_gt(a):
    return is_app_of(a, Z3_OP_GT)


def is_select(a):
    return is_app_of(a, Z3_OP_SELECT)


def is_store(a):
    return is_app_of(a, Z3_OP_STORE)


# --- value predicates ------------------------------------------------------

def is_numeral(a):
    """z3py is_int_value/is_bv_value-style base: a literal AST."""
    return _is_ast(a) and _ast_kind(a) == Z3_NUMERAL_AST


def is_int_value(a):
    """z3py is_int_value: an Int-sorted integer literal."""
    return is_numeral(a) and a.sort_ref.kind == "Int"


def is_rational_value(a):
    """z3py is_rational_value: a Real-sorted rational literal."""
    return is_numeral(a) and a.sort_ref.kind == "Real"


def is_bv_value(a):
    """z3py is_bv_value: a bitvector literal."""
    return is_numeral(a) and a.sort_ref.kind == "BitVec"


def is_string_value(a):
    """z3py is_string_value: a String literal."""
    return is_numeral(a) and a.sort_ref.kind == "String"


# ---------------------------------------------------------------------------
# AstRef accessor methods (attached to AstRef by install())
# ---------------------------------------------------------------------------

def _sexpr(self):
    """The SMT-LIB s-expression for this term (z3py AstRef.sexpr())."""
    s = lib.Z3_ast_to_string(self.ctx.ref, self.ast)
    return s.decode() if s else f"<ast {self.ast}>"


def _num_args_method(self):
    """Number of arguments (z3py AstRef.num_args())."""
    dargs = getattr(self, "_distinct_args", None)
    if dargs is not None:
        return len(dargs)
    return _num_args(self)


def _arg(self, i):
    """The i-th argument as an AstRef (z3py AstRef.arg(i))."""
    # A Distinct term reports its recorded arguments (its stored form is an
    # eager-expanded `and`, whose args are the pairwise disequalities).
    dargs = getattr(self, "_distinct_args", None)
    if dargs is not None:
        if not (0 <= i < len(dargs)):
            raise IndexError(f"arg index {i} out of range (num_args={len(dargs)})")
        return dargs[i]
    if _ast_kind(self) != Z3_APP_AST:
        raise IndexError("expression has no arguments")
    n = lib.Z3_get_app_num_args(self.ctx.ref, self.ast)
    if not (0 <= i < n):
        raise IndexError(f"arg index {i} out of range (num_args={n})")
    ca = lib.Z3_get_app_arg(self.ctx.ref, self.ast, i)
    return _M._wrap_from_ast(ca, self.ctx)


def _children(self):
    """The immediate sub-expressions (z3py AstRef.children()).

    An application's children are its arguments; a quantifier's single child is
    its body; a constant or literal has none.
    """
    dargs = getattr(self, "_distinct_args", None)
    if dargs is not None:
        return list(dargs)
    k = _ast_kind(self)
    if k == Z3_APP_AST:
        n = lib.Z3_get_app_num_args(self.ctx.ref, self.ast)
        return [self.arg(i) for i in range(n)]
    if k == Z3_QUANTIFIER_AST:
        return [self.body()]
    return []


def _decl(self):
    """The function declaration of this application (z3py AstRef.decl())."""
    return _expr_decl(self)


# --- quantifier accessors (defined on a quantifier term) -------------------

def _quant_guard(self, who):
    if _ast_kind(self) != Z3_QUANTIFIER_AST:
        raise _M.AyZ3Exception(f"{who}() is only defined on a quantifier")


def _body(self):
    """The body of a quantifier (z3py QuantifierRef.body())."""
    _quant_guard(self, "body")
    b = lib.Z3_get_quantifier_body(self.ctx.ref, self.ast)
    return _M._wrap_from_ast(b, self.ctx)


def _num_vars(self):
    """The number of bound variables (z3py QuantifierRef.num_vars())."""
    _quant_guard(self, "num_vars")
    return lib.Z3_get_quantifier_num_bound(self.ctx.ref, self.ast)


def _var_name(self, i):
    """The name of the i-th bound variable (z3py QuantifierRef.var_name(i))."""
    _quant_guard(self, "var_name")
    sym = lib.Z3_get_quantifier_bound_name(self.ctx.ref, self.ast, i)
    nm = lib.Z3_get_symbol_string(self.ctx.ref, sym)
    return nm.decode() if nm else ""


def _var_sort(self, i):
    """The sort of the i-th bound variable (z3py QuantifierRef.var_sort(i))."""
    _quant_guard(self, "var_sort")
    sh = lib.Z3_get_quantifier_bound_sort(self.ctx.ref, self.ast, i)
    return _M._sort_from_handle(sh, self.ctx)


def _is_forall(self):
    """True for a universal quantifier (z3py QuantifierRef.is_forall())."""
    _quant_guard(self, "is_forall")
    return bool(lib.Z3_is_quantifier_forall(self.ctx.ref, self.ast))


def _is_exists(self):
    """True for an existential quantifier (z3py QuantifierRef.is_exists())."""
    _quant_guard(self, "is_exists")
    return bool(lib.Z3_is_quantifier_exists(self.ctx.ref, self.ast))


def _is_lambda(self):
    """True for a lambda (z3py QuantifierRef.is_lambda()).

    AY's core has no lambda term (see ayz3.Lambda), so a quantifier is never a
    lambda — this is honestly False for every ayz3 quantifier.
    """
    _quant_guard(self, "is_lambda")
    return False


def _weight(self):
    """The quantifier's weight hint (z3py QuantifierRef.weight()).

    AY's core does not persist a quantifier's weight, so this returns the value
    supplied at construction (z3py's default is 1). It has no effect on the
    sat/unsat verdict.
    """
    _quant_guard(self, "weight")
    return self.ctx._quantifier_weight.get(self.ast, 1)


def _num_patterns(self):
    """The number of trigger patterns (z3py QuantifierRef.num_patterns())."""
    _quant_guard(self, "num_patterns")
    pats = self.ctx._quantifier_patterns.get(self.ast)
    return len(pats) if pats else 0


def _pattern(self, i):
    """The i-th trigger pattern as a PatternRef (z3py QuantifierRef.pattern(i))."""
    _quant_guard(self, "pattern")
    pats = self.ctx._quantifier_patterns.get(self.ast)
    if not pats or i < 0 or i >= len(pats):
        raise _M.AyZ3Exception(f"pattern index {i} out of range")
    return pats[i]


# ---------------------------------------------------------------------------
# Declaration recovery
# ---------------------------------------------------------------------------

def _expr_decl(a):
    """Return a FuncDeclRef for an expression, honoring AY's representation.

    * An application (APP): the real declaration from the C ABI. For an
      uninterpreted-function application we return the registered FuncDeclRef so
      its declared domain/range are exact; for a built-in operator we synthesize
      a FuncDeclRef whose domain is the argument sorts and range is the result.
    * A declared constant (VAR): a 0-arity uninterpreted declaration whose name
      is recovered from the construction-time registry (the C ABI cannot read a
      const's name back from its handle).
    * A literal (NUMERAL): the value declaration z3py reports (Int/Real/bv/
      true/false/String) with its matching decl kind.
    """
    ctx = a.ctx
    # A term built by ayz3.Distinct is stored as an eager-expanded `and`, but its
    # z3py-visible declaration is `distinct` (kind Z3_OP_DISTINCT). Synthesize
    # that declaration from the recorded arguments so `decl().name() == 'distinct'`
    # matches z3py, rather than reporting the expansion's `and`.
    dargs = getattr(a, "_distinct_args", None)
    if dargs is not None:
        domain = [x.sort() for x in dargs]
        return _M.FuncDeclRef(None, "distinct", domain, a.sort_ref, ctx,
                              kind=Z3_OP_DISTINCT)
    k = _ast_kind(a)
    if k == Z3_APP_AST:
        decl = lib.Z3_get_app_decl(ctx.ref, a.ast)
        if decl:
            name = _decl_name_of(ctx, decl)
            dkind = lib.Z3_get_decl_kind(ctx.ref, decl)
            reg = ctx._funcdecl_meta.get(name)
            if reg is not None and dkind == Z3_OP_UNINTERPRETED:
                return reg
            n = lib.Z3_get_app_num_args(ctx.ref, a.ast)
            domain = [a.arg(i).sort() for i in range(n)]
            return _M.FuncDeclRef(decl, name, domain, a.sort_ref, ctx, kind=dkind)
        raise _M.AyZ3Exception(
            f"application node has no declaration (handle {a.ast})"
        )
    if k == Z3_VAR_AST:
        name = a.decl_name
        if name is None:
            meta = ctx._const_meta.get(a.ast)
            name = meta[0] if meta else None
        if name is None:
            raise _M.AyZ3Exception(
                f"cannot recover the declaration name for constant {a.ast}"
            )
        return _M.FuncDeclRef(None, name, [], a.sort_ref, ctx,
                              kind=Z3_OP_UNINTERPRETED)
    if k == Z3_NUMERAL_AST:
        name, kind = _numeral_decl(a)
        return _M.FuncDeclRef(None, name, [], a.sort_ref, ctx, kind=kind)
    raise _M.AyZ3Exception("decl() is not defined on a quantifier")


def _numeral_decl(a):
    """(name, decl_kind) for a literal, matching z3py's value declarations."""
    sk = a.sort_ref.kind
    if sk == "Bool":
        b = a.as_bool()
        if b is True:
            return ("true", Z3_OP_TRUE)
        if b is False:
            return ("false", Z3_OP_FALSE)
        return ("Bool", Z3_OP_ANUM)
    if sk == "Int":
        return ("Int", Z3_OP_ANUM)
    if sk == "Real":
        return ("Real", Z3_OP_ANUM)
    if sk == "BitVec":
        return ("bv", Z3_OP_BNUM)
    if sk == "String":
        return ("String", Z3_OP_SEQ_VALUE)
    return (sk, Z3_OP_ANUM)


# ---------------------------------------------------------------------------
# FuncDeclRef accessor methods (attached to FuncDeclRef by install())
# ---------------------------------------------------------------------------

def _fd_domain(self, i):
    """The i-th domain sort of the declaration (z3py FuncDeclRef.domain(i))."""
    return self.domain_sorts[i]


def _fd_range(self):
    """The range (result) sort of the declaration (z3py FuncDeclRef.range())."""
    return self.range_sort


def _fd_kind(self):
    """The declaration kind (z3py FuncDeclRef.kind())."""
    return self._kind


def _fd_params(self):
    """Typed declaration parameters (z3py FuncDeclRef.params())."""
    if not self.handle:
        return []
    n = lib.Z3_get_decl_num_parameters(self.ctx.ref, self.handle)
    result = []
    for i in range(n):
        kind = lib.Z3_get_decl_parameter_kind(self.ctx.ref, self.handle, i)
        if kind == Z3_PARAMETER_INT:
            result.append(lib.Z3_get_decl_int_parameter(self.ctx.ref, self.handle, i))
        elif kind == Z3_PARAMETER_SORT:
            sort = lib.Z3_get_decl_sort_parameter(self.ctx.ref, self.handle, i)
            if not sort:
                self.ctx.check_error("FuncDeclRef.params")
                raise _M.AyZ3Exception("AY returned a null sort declaration parameter")
            result.append(_M._sort_from_handle(sort, self.ctx))
        else:
            raise _M.AyZ3Exception(
                f"unsupported declaration parameter kind {kind} at index {i}"
            )
    return result


# ---------------------------------------------------------------------------
# Installation
# ---------------------------------------------------------------------------

# Predicates exported into the ayz3 namespace and __all__. is_true / is_false
# are already defined in ayz3 (BoolRef value check) and intentionally NOT
# redefined here, so install() leaves them intact.
_PREDICATES = [
    "is_expr", "is_app", "is_const", "is_var", "is_quantifier", "is_app_of",
    "is_int", "is_real", "is_bool", "is_bv", "is_array", "is_string", "is_seq",
    "is_and", "is_or", "is_not", "is_implies",
    "is_eq", "is_distinct",
    "is_add", "is_mul", "is_sub", "is_div", "is_idiv", "is_mod",
    "is_le", "is_lt", "is_ge", "is_gt",
    "is_select", "is_store",
    "is_numeral", "is_int_value", "is_rational_value", "is_bv_value",
    "is_string_value",
]

_AST_METHODS = {
    "decl": _decl,
    "sexpr": _sexpr,
    "num_args": _num_args_method,
    "arg": _arg,
    "children": _children,
    "body": _body,
    "num_vars": _num_vars,
    "var_name": _var_name,
    "var_sort": _var_sort,
    "is_forall": _is_forall,
    "is_exists": _is_exists,
    "is_lambda": _is_lambda,
    "weight": _weight,
    "num_patterns": _num_patterns,
    "pattern": _pattern,
}

_FUNCDECL_METHODS = {
    "domain": _fd_domain,
    "range": _fd_range,
    "kind": _fd_kind,
    "params": _fd_params,
}

_FINITE_SET_DECL_CONSTANTS = [
    "Z3_OP_FINITE_SET_EMPTY",
    "Z3_OP_FINITE_SET_SINGLETON",
    "Z3_OP_FINITE_SET_UNION",
    "Z3_OP_FINITE_SET_INTERSECT",
    "Z3_OP_FINITE_SET_DIFFERENCE",
    "Z3_OP_FINITE_SET_IN",
    "Z3_OP_FINITE_SET_SIZE",
    "Z3_OP_FINITE_SET_SUBSET",
    "Z3_OP_FINITE_SET_MAP",
    "Z3_OP_FINITE_SET_FILTER",
    "Z3_OP_FINITE_SET_RANGE",
    "Z3_OP_FINITE_SET_EXT",
    "Z3_OP_FINITE_SET_MAP_INVERSE",
    "Z3_OP_INTERNAL",
    "Z3_OP_RECURSIVE",
    "Z3_OP_UNINTERPRETED",
]


def install(mod):
    """Attach the introspection predicates and accessor methods onto `mod`.

    `mod` is the top-level `ayz3` package module. Predicates become module-level
    functions (and are added to `mod.__all__`); the AstRef/FuncDeclRef accessor
    methods are attached to those classes.
    """
    global _M
    _M = mod

    for name, fn in _AST_METHODS.items():
        setattr(mod.AstRef, name, fn)
    for name, fn in _FUNCDECL_METHODS.items():
        setattr(mod.FuncDeclRef, name, fn)

    exported = []
    for name in _PREDICATES:
        setattr(mod, name, globals()[name])
        exported.append(name)
    for name in _FINITE_SET_DECL_CONSTANTS:
        setattr(mod, name, globals()[name])
        exported.append(name)

    if hasattr(mod, "__all__"):
        for name in exported:
            if name not in mod.__all__:
                mod.__all__.append(name)
