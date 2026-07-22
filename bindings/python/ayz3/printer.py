# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# z3py-style infix pretty-printer for AstRef.str()/repr() (B-4).
#
# Wave-1 (B-1) made an ayz3 expression's repr() emit the real SMT-LIB
# s-expression (e.g. `(+ x (* y 2))`) via Z3_ast_to_string. z3py, by contrast,
# renders an INFIX surface syntax (`x + 2*y`, `x <= y`, `And(p, q)`, `a[i]`,
# `ForAll(x, ...)`). This module reproduces z3py's pretty-printer by walking the
# B-3 introspection API (decl().kind()/name(), num_args(), arg(i), children(),
# is_quantifier/var_name/body/is_forall, and the module value predicates) and
# rendering z3py-style infix with z3py's exact precedence, associativity, operator
# spellings and spacing. The algorithm is a faithful transcription of upstream
# z3printer.py 4.15.4 (pp_app / pp_infix / infix_args_core / pp_unary / pp_select
# / pp_quantifier / ...), producing flat single-line text (which is byte-identical
# to z3py's own str() for any expression that fits on one line).
#
# HONESTY (the load-bearing property): this printer renders the term AY ACTUALLY
# STORED. AY applies a family of SOUND canonicalizations at construction — the
# same ones documented for B-1's printing path and B-3's introspection:
#
#   * comparisons orient to `<` / `<=`  : `x > y` is stored `(< y x)`, so it
#     prints `y < x` (z3py prints `x > y`);
#   * subtraction folds to addition-of-negation : `x - y` is stored `(+ x (- y))`,
#     so it prints `x + -y` (z3py prints `x - y`) — note upstream z3py renders the
#     SAME structure `x + (-y)` as `x + -y`, so we match z3py on AY's structure;
#   * `x != y` folds to `(not (= x y))` -> `Not(x == y)`; binary/n-ary Distinct
#     folds to and/not; Implies folds to `(or q (not p))` -> `Or(q, Not(p))`;
#   * commutative operands may be reordered (`2*y` stored `(* y 2)` -> `y*2`),
#     and n-ary and/or/+ are flattened;
#   * seq/string operations are stored as uninterpreted functions carrying their
#     SMT-LIB names (`str.++`, `str.len`, `str.contains`), so they print with
#     those names rather than z3py's `Concat` / `Length` / `Contains`.
#
# For every one of these the printer prints AY's REAL term (never z3py's surface
# form re-synthesized by un-canonicalizing — that would be a fabrication). Where
# AY's stored structure coincides with z3py's, the output is byte-identical
# (`x <= y`, `x < y`, `And(p, q)`, `x*y + z`, `a[i]`, `Store(a, i, v)`,
# `ForAll(x, x < 10)`, `f(x)`, ...). The divergences are covered by regression
# tests that assert AY's honest output AND cross-check it against z3py's rendering
# of the equivalent canonical structure, so each divergence stays intentional.
#
# Anything the printer cannot classify (an exotic/unsupported decl kind, or any
# internal error) falls back to AY's real s-expression via sexpr() — an honest
# degradation, never an invented value. A model value (m[x]) keeps its concrete
# rendering through the existing _render_model_value path.

# ---------------------------------------------------------------------------
# Z3_decl_kind integer constants (Z3 enum, verified against z3.z3consts 4.15.4
# and AY's actual Z3_get_decl_kind returns). Keyed by the same integers AY
# reports, so the maps below behave exactly as upstream z3printer's do.
# ---------------------------------------------------------------------------
OP_TRUE = 256
OP_FALSE = 257
OP_EQ = 258
OP_DISTINCT = 259
OP_ITE = 260
OP_AND = 261
OP_OR = 262
OP_IFF = 263
OP_XOR = 264
OP_NOT = 265
OP_IMPLIES = 266

OP_ANUM = 512
OP_LE = 514
OP_GE = 515
OP_LT = 516
OP_GT = 517
OP_ADD = 518
OP_SUB = 519
OP_UMINUS = 520
OP_MUL = 521
OP_DIV = 522
OP_IDIV = 523
OP_REM = 524
OP_MOD = 525
OP_TO_REAL = 526
OP_TO_INT = 527
OP_IS_INT = 528
OP_POWER = 529

OP_STORE = 768
OP_SELECT = 769
OP_CONST_ARRAY = 770
OP_ARRAY_MAP = 771

OP_BNUM = 1024
OP_BNEG = 1027
OP_BADD = 1028
OP_BSUB = 1029
OP_BMUL = 1030
OP_BSDIV = 1031
OP_BUDIV = 1032
OP_BSREM = 1033
OP_BUREM = 1034
OP_BSMOD = 1035
OP_ULEQ = 1041
OP_SLEQ = 1042
OP_UGEQ = 1043
OP_SGEQ = 1044
OP_ULT = 1045
OP_SLT = 1046
OP_UGT = 1047
OP_SGT = 1048
OP_BAND = 1049
OP_BOR = 1050
OP_BNOT = 1051
OP_BXOR = 1052
OP_CONCAT = 1056
OP_SIGN_EXT = 1057
OP_ZERO_EXT = 1058
OP_EXTRACT = 1059
OP_REPEAT = 1060
OP_BSHL = 1064
OP_BLSHR = 1065
OP_BASHR = 1066

# ---------------------------------------------------------------------------
# Operator surface spellings. This is upstream z3printer._z3_op_to_str RESTRICTED
# to the keys z3py actually lists (so `_op_name` falls back to decl.name() for
# ADD/SUB/MUL/DIV/LE/LT/GE/GT/UMINUS exactly as z3py does — and AY's decl names
# for those already match z3py's operator glyphs). Keys z3py DOES override
# (IDIV -> "/", MOD -> "%", all the BV ops, the boolean connectives, ...) are
# reproduced here verbatim.
# ---------------------------------------------------------------------------
_OP_TO_STR = {
    OP_TRUE: "True",
    OP_FALSE: "False",
    OP_EQ: "==",
    OP_DISTINCT: "Distinct",
    OP_ITE: "If",
    OP_AND: "And",
    OP_OR: "Or",
    OP_IFF: "==",
    OP_XOR: "Xor",
    OP_NOT: "Not",
    OP_IMPLIES: "Implies",

    OP_IDIV: "/",
    OP_MOD: "%",
    OP_TO_REAL: "ToReal",
    OP_TO_INT: "ToInt",
    OP_POWER: "**",
    OP_IS_INT: "IsInt",

    OP_BADD: "+",
    OP_BSUB: "-",
    OP_BMUL: "*",
    OP_BOR: "|",
    OP_BAND: "&",
    OP_BNOT: "~",
    OP_BXOR: "^",
    OP_BNEG: "-",
    OP_BUDIV: "UDiv",
    OP_BSDIV: "/",
    OP_BSMOD: "%",
    OP_BSREM: "SRem",
    OP_BUREM: "URem",

    OP_SLEQ: "<=",
    OP_SLT: "<",
    OP_SGEQ: ">=",
    OP_SGT: ">",

    OP_ULEQ: "ULE",
    OP_ULT: "ULT",
    OP_UGEQ: "UGE",
    OP_UGT: "UGT",

    OP_BASHR: ">>",
    OP_BSHL: "<<",
    OP_BLSHR: "LShR",

    OP_CONCAT: "Concat",
    OP_EXTRACT: "Extract",
    OP_SIGN_EXT: "SignExt",
    OP_ZERO_EXT: "ZeroExt",
    OP_REPEAT: "RepeatBitVec",

    OP_SELECT: "Select",
    OP_STORE: "Store",
    OP_CONST_ARRAY: "K",
    OP_ARRAY_MAP: "Map",
}

# Operators rendered infix (upstream _z3_infix).
_INFIX = frozenset({
    OP_EQ, OP_IFF, OP_ADD, OP_SUB, OP_MUL, OP_DIV, OP_IDIV, OP_MOD, OP_POWER,
    OP_LE, OP_LT, OP_GE, OP_GT, OP_BADD, OP_BSUB, OP_BMUL, OP_BSDIV, OP_BSMOD,
    OP_BOR, OP_BAND, OP_BXOR, OP_SLEQ, OP_SLT, OP_SGEQ, OP_SGT, OP_BASHR, OP_BSHL,
})

# Prefix unary operators (upstream _z3_unary).
_UNARY = frozenset({OP_UMINUS, OP_BNOT, OP_BNEG})

# Infix operators printed with NO surrounding spaces (upstream _z3_infix_compact).
_COMPACT = frozenset({
    OP_MUL, OP_BMUL, OP_POWER, OP_DIV, OP_IDIV, OP_MOD, OP_BSDIV, OP_BSMOD,
})

# Precedence (lower binds tighter); upstream _z3_precedence. Default 100000.
_PREC = {
    OP_POWER: 0,
    OP_UMINUS: 1, OP_BNEG: 1, OP_BNOT: 1,
    OP_MUL: 2, OP_DIV: 2, OP_IDIV: 2, OP_MOD: 2, OP_BMUL: 2, OP_BSDIV: 2, OP_BSMOD: 2,
    OP_ADD: 3, OP_SUB: 3, OP_BADD: 3, OP_BSUB: 3,
    OP_BASHR: 4, OP_BSHL: 4,
    OP_BAND: 5,
    OP_BXOR: 6,
    OP_BOR: 7,
    OP_LE: 8, OP_LT: 8, OP_GE: 8, OP_GT: 8, OP_EQ: 8,
    OP_SLEQ: 8, OP_SLT: 8, OP_SGEQ: 8, OP_SGT: 8, OP_IFF: 8,
}

# Fully-associative operators (flatten nested same-kind children on both sides).
_ASSOC = frozenset({OP_BOR, OP_BXOR, OP_BAND, OP_ADD, OP_BADD, OP_MUL, OP_BMUL})
# Left-associative operators (flatten only the leftmost same-kind child).
_LEFT_ASSOC = _ASSOC | {OP_SUB, OP_BSUB}

# The parent `ayz3` module, wired by install(); gives access to the value/shape
# predicates and the model-value renderer.
_M = None


def _prec(k):
    return _PREC.get(k, 100000)


def _is_infix_unary(k):
    return k in _INFIX or k in _UNARY


def _is_add(k):
    return k == OP_ADD or k == OP_BADD


def _is_sub(k):
    return k == OP_SUB or k == OP_BSUB


def _eff_kind(a):
    """The effective decl kind used for classification/precedence.

    AY stores integer/real UNARY MINUS as a 1-argument `SUB` (kind 519), where
    z3py uses a distinct `UMINUS` (520). To render AY's real term the way z3py
    renders that same structure, a 1-arg SUB is classified as UMINUS everywhere
    (unary spelling `-x`, precedence 1). A genuine 2-arg SUB — should AY ever
    emit one — stays an infix `-`. (BV negation is already its own BNEG kind.)
    """
    k = a.decl().kind()
    if k == OP_SUB and a.num_args() == 1:
        return OP_UMINUS
    return k


def _kind(a):
    """The effective decl kind of an application/const/value; None for a
    quantifier.

    Mirrors upstream's `child_k = child.decl().kind() if is_app(child) else None`
    (with AY's 1-arg-SUB-as-unary-minus normalization). AY classifies a declared
    constant as an app (0-arity), so its kind is the uninterpreted kind — not
    infix/unary, exactly what z3py sees.
    """
    if not _M.is_app(a):
        return None
    return _eff_kind(a)


def _op_name(a):
    """Upstream `_op_name`: the override glyph if listed, else the decl name."""
    d = a.decl()
    s = _OP_TO_STR.get(d.kind())
    return s if s is not None else d.name()


def _paren(s):
    return "(" + s + ")"


# ---------------------------------------------------------------------------
# Core recursive renderer (transcription of z3printer.Formatter.pp_* to flat
# strings). Flat text is byte-identical to z3py's own str() whenever z3py does
# not line-wrap, i.e. for any expression that fits on one line.
# ---------------------------------------------------------------------------

def pp(a):
    """Render an ayz3 AstRef as z3py-style infix text (its str()/repr())."""
    return _pp_expr(a)


def _pp_expr(a):
    if _M.is_quantifier(a):
        return _pp_quantifier(a)
    if _M.is_app(a):
        return _pp_app(a)
    # Not an app or quantifier (should not arise for AY terms): honest s-expr.
    return a.sexpr()


def _pp_app(a):
    # Value nodes first (upstream pp_app order), then a 0-arity const, then the
    # decl-kind dispatch. The value checks precede is_const because a literal is
    # also 0-arity.
    if _M.is_int_value(a):
        return a.as_string()
    if _M.is_rational_value(a):
        return _pp_rational(a)
    if _M.is_bv_value(a):
        # z3py's pp_bv prints the decimal (unsigned) value; AY's numeral string
        # for a bitvector is exactly that decimal (e.g. BitVecVal(-1, 8) -> 255).
        s = _M.lib.Z3_get_numeral_string(a.ctx.ref, a.ast)
        return s.decode() if s else a.sexpr()
    if _M.is_string_value(a):
        return '"' + a.as_string() + '"'
    if _M.is_const(a):
        return _op_name(a)

    k = _eff_kind(a)
    if k == OP_POWER:
        return _pp_power(a)
    if k == OP_DISTINCT:
        return _pp_distinct(a)
    if k == OP_SELECT:
        return _pp_select(a)
    if k in (OP_SIGN_EXT, OP_ZERO_EXT, OP_REPEAT):
        return _pp_unary_param(a)
    if k == OP_EXTRACT:
        return _pp_extract(a)
    if k in _INFIX:
        return _pp_infix(a)
    if k in _UNARY:
        return _pp_unary(a)
    return _pp_prefix(a)


def _pp_rational(a):
    """A Real literal: `num/den`, or bare `num` when den == 1 (z3py's form).

    AY's numeral string spells a whole rational `2/1`; z3py prints `2`.
    """
    s = a.as_string()
    if s is None:
        return a.sexpr()
    if "/" in s:
        num, den = s.split("/", 1)
        if den == "1":
            return num
    return s


def _pp_prefix(a):
    head = _op_name(a)
    args = ", ".join(_pp_expr(c) for c in a.children())
    return head + "(" + args + ")"


def _pp_infix(a):
    k = _eff_kind(a)
    op = _op_name(a)
    args = _infix_args(a)
    if k in _COMPACT:
        return op.join(args)
    return (" " + op + " ").join(args)


def _infix_args(a):
    r = []
    _infix_args_core(a, r)
    return r


def _infix_args_core(a, r):
    """Upstream infix_args_core: flatten associative chains and parenthesize a
    child only when its (looser) precedence would otherwise misgroup it."""
    k = _eff_kind(a)
    p = _prec(k)
    first = True
    for child in a.children():
        child_pp = _pp_expr(child)
        child_k = _kind(child)
        if k == child_k and (k in _ASSOC or (first and k in _LEFT_ASSOC)):
            _infix_args_core(child, r)
        elif _is_infix_unary(child_k):
            child_p = _prec(child_k)
            if (p > child_p
                    or (_is_add(k) and _is_sub(child_k))
                    or (_is_sub(k) and first and _is_add(child_k))):
                r.append(child_pp)
            else:
                r.append(_paren(child_pp))
        elif _M.is_quantifier(child):
            r.append(_paren(child_pp))
        else:
            r.append(child_pp)
        first = False


def _pp_unary(a):
    """Upstream pp_unary for `-`/`~`/bvneg: parenthesize a looser-or-equal child."""
    k = _eff_kind(a)
    p = _prec(k)
    child = a.children()[0]
    child_k = _kind(child)
    child_pp = _pp_expr(child)
    if k != child_k and _is_infix_unary(child_k):
        if p <= _prec(child_k):
            child_pp = _paren(child_pp)
    if _M.is_quantifier(child):
        child_pp = _paren(child_pp)
    return _op_name(a) + child_pp


def _pp_power(a):
    return _pp_power_arg(a.arg(0)) + "**" + _pp_power_arg(a.arg(1))


def _pp_power_arg(arg):
    r = _pp_expr(arg)
    k = _kind(arg)
    if _is_infix_unary(k):
        return _paren(r)
    if _M.is_rational_value(arg):
        try:
            if arg.as_fraction().denominator != 1:
                return _paren(r)
        except Exception:
            pass
    return r


def _pp_select(a):
    if a.num_args() != 2:
        return _pp_prefix(a)
    return _pp_expr(a.arg(0)) + "[" + _pp_expr(a.arg(1)) + "]"


def _pp_distinct(a):
    # AY folds Distinct into and/not, so a real DISTINCT decl never reaches here;
    # kept for parity with z3py (a 2-arg distinct renders `x != y`).
    if a.num_args() == 2:
        return " != ".join(_infix_args(a))
    return _pp_prefix(a)


def _pp_unary_param(a):
    params = a.decl().params()
    if not params:
        return _pp_prefix(a)
    return _op_name(a) + "(" + str(params[0]) + ", " + _pp_expr(a.arg(0)) + ")"


def _pp_extract(a):
    params = a.decl().params()
    if len(params) < 2:
        return _pp_prefix(a)
    high, low = params[0], params[1]
    return (_op_name(a) + "(" + str(high) + ", " + str(low) + ", "
            + _pp_expr(a.arg(0)) + ")")


def _pp_quantifier(a):
    names = [a.var_name(i) for i in range(a.num_vars())]
    body_pp = _pp_expr(a.body())
    if len(names) == 1:
        vs = names[0]
    else:
        vs = "[" + ", ".join(names) + "]"
    header = "ForAll" if a.is_forall() else "Exists"
    return header + "(" + vs + ", " + body_pp + ")"


# ---------------------------------------------------------------------------
# Installation: rebind AstRef.__repr__/__str__ to the pretty-printer.
# ---------------------------------------------------------------------------

def _ast_repr(self):
    # A model value (m[x] / m.eval(...)) keeps its concrete rendering, exactly as
    # the pre-B-4 __repr__ did: AY's Z3_ast_to_string yields an opaque handle for
    # a model value, so it is rendered from its concrete content instead.
    if getattr(self, "_is_model_value", False):
        return _M._render_model_value(self)
    try:
        return pp(self)
    except Exception:
        # A repr must never raise: fall back to AY's real s-expression (honest,
        # never fabricated) for any shape the pretty-printer cannot classify.
        try:
            return self.sexpr()
        except Exception:
            return object.__repr__(self)


def install(mod):
    """Rebind ayz3.AstRef.__repr__/__str__ to the z3py-style pretty-printer.

    Must run AFTER introspect.install(mod) so the decl/children/quantifier
    accessors and value predicates the printer walks are already attached.
    """
    global _M
    _M = mod
    mod.AstRef.__repr__ = _ast_repr
    mod.AstRef.__str__ = _ast_repr
