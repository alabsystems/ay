# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Floating-point (IEEE-754) support for the z3py-compatible ayz3 binding.
#
# ============================================================================
# NATIVE FP: first-class Z3_mk_fpa_* handles (z3py-parity surface)
# ============================================================================
#
# libay_ffi exports the Z3_mk_fpa_* term-constructor surface (verified via
# `nm`): FP sorts, rounding modes, values (NaN/inf/zero/numeral_double/
# numeral_int), the full arithmetic set (add/sub/mul/div/fma/sqrt/
# roundToIntegral/rem/min/max/abs/neg), the IEEE comparison set (fp.eq/lt/leq/
# gt/geq), the classification predicates (isNaN/isInfinite/isZero/isNormal/
# isSubnormal/isNegative/isPositive), and the conversion set (to_fp from
# FP/signed BV/unsigned BV/IEEE bits/Real, fp.to_sbv/to_ubv/to_real,
# to_ieee_bv, and per-field `fp` construction).
#
# So an ayz3 FP expression is an ORDINARY AstRef over a native handle: FP
# constraints are plain BoolRefs, they go into the regular Solver next to
# Int/BV/Bool constraints, and model values come back through the regular
# ModelRef (as FPNumRef), exactly like z3py.
#
# The FPA C API (crates/ay-ffi/src/z3_compat/fpa.rs, fpa_ext.rs and
# fpa_introspect.rs) exports the full conversion set as well, so the
# following are ALL native:
#   - Z3_mk_fpa_to_fp_bv        -> fpBVToFP / fpToFP(bv, sort)   (IEEE BV->FP)
#   - Z3_mk_fpa_to_fp_real      -> fpRealToFP                    (Real->FP)
#   - Z3_mk_fpa_to_fp_unsigned  -> fpUnsignedToFP                (uBV->FP)
#   - Z3_mk_fpa_to_ubv/to_sbv   -> fpToUBV / fpToSBV             (FP->BV)
#   - Z3_mk_fpa_to_real         -> fpToReal                      (FP->Real)
#   - Z3_mk_fpa_to_ieee_bv      -> fpToIEEEBV                    (FP->IEEE BV)
#   - Z3_mk_fpa_fp              -> fpFP                          (fields->FP)
# and FPNumRef field accessors go through the native Z3_fpa_get_numeral_* /
# Z3_fpa_is_numeral_* accessors (the textual parser in _parse_fp_value is
# kept as the reference implementation and as the fallback for formats whose
# fields exceed the int64/uint64 accessor widths, e.g. Float128).
#
# SEMANTICS (cross-checked against real z3py 4.15.4):
#   - `x == y` on FP terms is SMT `=` (object equality: NaN = NaN is true,
#     +0 = -0 is false) — matching z3py's ExprRef.__eq__. IEEE equality is
#     fpEQ (fp.eq: NaN never equal, +0 == -0 true).
#   - Python operators +,-,*,/ on FPRef round with the DEFAULT rounding mode
#     (RNE unless changed via set_default_rounding_mode), matching z3py.
#   - FPVal computes the correctly-rounded target value in exact bignum
#     arithmetic and lands it through Z3_mk_fpa_numeral_double (every
#     half/single/double value is exactly a double, so no double-rounding).

import ctypes
import re as _re
from fractions import Fraction

from . import _lib
from ._lib import lib

# fp.py is imported at the END of ayz3/__init__.py, so the package module is
# fully populated with everything below by the time this executes.
from . import (  # noqa: E402
    AstRef,
    SortRef,
    BoolRef,
    AyZ3Exception,
    _current_ctx,
    _mk_const,
    _bool_sort,
)


def _pkg():
    """The fully-initialized ayz3 package module (late import helper)."""
    import ayz3
    return ayz3


# ---------------------------------------------------------------------------
# FP sorts
# ---------------------------------------------------------------------------


class FPSortRef(SortRef):
    """A floating-point sort `(_ FloatingPoint eb sb)` (z3py FPSortRef).

    `ebits()` is the exponent width; `sbits()` the significand width INCLUDING
    the hidden bit — exactly z3py's FPSort(ebits, sbits).
    """

    def __init__(self, handle, ebits, sbits, ctx):
        SortRef.__init__(self, handle, "FloatingPoint", ctx)
        self._ebits = int(ebits)
        self._sbits = int(sbits)

    def ebits(self):
        return self._ebits

    def sbits(self):
        return self._sbits

    def cast(self, val):
        """Coerce a Python value into this FP sort (z3py FPSortRef.cast)."""
        if isinstance(val, FPRef):
            return val
        return FPVal(val, self, ctx=self.ctx)

    def __eq__(self, other):
        return (
            isinstance(other, FPSortRef)
            and self._ebits == other._ebits
            and self._sbits == other._sbits
        )

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(("FPSort", self._ebits, self._sbits))

    def __repr__(self):
        return f"FPSort({self._ebits}, {self._sbits})"


class FPRMSortRef(SortRef):
    """The RoundingMode sort (z3py FPRMSortRef)."""

    def __init__(self, handle, ctx):
        SortRef.__init__(self, handle, "RoundingMode", ctx)

    def __eq__(self, other):
        return isinstance(other, FPRMSortRef)

    def __ne__(self, other):
        return not isinstance(other, FPRMSortRef)

    def __hash__(self):
        return hash("RoundingMode")

    def __repr__(self):
        return "RoundingMode"


def FPSort(ebits, sbits, ctx=None):
    """z3py FPSort(ebits, sbits)."""
    ctx = ctx or _current_ctx()
    h = lib.Z3_mk_fpa_sort(ctx.ref, int(ebits), int(sbits))
    return FPSortRef(h, ebits, sbits, ctx)


def Float16(ctx=None):
    return FPSort(5, 11, ctx)


def FloatHalf(ctx=None):
    return FPSort(5, 11, ctx)


def Float32(ctx=None):
    return FPSort(8, 24, ctx)


def FloatSingle(ctx=None):
    return FPSort(8, 24, ctx)


def Float64(ctx=None):
    return FPSort(11, 53, ctx)


def FloatDouble(ctx=None):
    return FPSort(11, 53, ctx)


def Float128(ctx=None):
    return FPSort(15, 113, ctx)


def FloatQuadruple(ctx=None):
    return FPSort(15, 113, ctx)


def _fprm_sort(ctx=None):
    ctx = ctx or _current_ctx()
    return FPRMSortRef(lib.Z3_mk_fpa_rounding_mode_sort(ctx.ref), ctx)


def is_fp_sort(s):
    """Whether `s` is an FP sort (z3py is_fp_sort)."""
    return isinstance(s, FPSortRef)


def is_fprm_sort(s):
    """Whether `s` is the RoundingMode sort (z3py is_fprm_sort)."""
    return isinstance(s, FPRMSortRef)


# ---------------------------------------------------------------------------
# Rounding modes
# ---------------------------------------------------------------------------


class FPRMRef(AstRef):
    """A rounding-mode expression (z3py FPRMRef)."""

    def __repr__(self):
        s = lib.Z3_ast_to_string(self.ctx.ref, self.ast)
        s = s.decode() if s else f"<ast {self.ast}>"
        # z3py prints the five RM values as their constructor calls.
        if s in ("RNE", "RNA", "RTP", "RTN", "RTZ"):
            return s + "()"
        return s

    def as_string(self):
        return repr(self)


def _mk_rm(mk, ctx):
    ctx = ctx or _current_ctx()
    return FPRMRef(mk(ctx.ref), _fprm_sort(ctx), ctx)


def RoundNearestTiesToEven(ctx=None):
    return _mk_rm(lib.Z3_mk_fpa_round_nearest_ties_to_even, ctx)


def RNE(ctx=None):
    return _mk_rm(lib.Z3_mk_fpa_rne, ctx)


def RoundNearestTiesToAway(ctx=None):
    return _mk_rm(lib.Z3_mk_fpa_round_nearest_ties_to_away, ctx)


def RNA(ctx=None):
    return _mk_rm(lib.Z3_mk_fpa_rna, ctx)


def RoundTowardPositive(ctx=None):
    return _mk_rm(lib.Z3_mk_fpa_round_toward_positive, ctx)


def RTP(ctx=None):
    return _mk_rm(lib.Z3_mk_fpa_rtp, ctx)


def RoundTowardNegative(ctx=None):
    return _mk_rm(lib.Z3_mk_fpa_round_toward_negative, ctx)


def RTN(ctx=None):
    return _mk_rm(lib.Z3_mk_fpa_rtn, ctx)


def RoundTowardZero(ctx=None):
    return _mk_rm(lib.Z3_mk_fpa_round_toward_zero, ctx)


def RTZ(ctx=None):
    return _mk_rm(lib.Z3_mk_fpa_rtz, ctx)


def is_fprm(a):
    """Whether `a` is a rounding-mode expression (z3py is_fprm)."""
    return isinstance(a, FPRMRef)


def is_fprm_value(a):
    """Whether `a` is one of the five concrete rounding-mode values."""
    if not isinstance(a, FPRMRef):
        return False
    s = lib.Z3_ast_to_string(a.ctx.ref, a.ast)
    return bool(s) and s.decode() in ("RNE", "RNA", "RTP", "RTN", "RTZ")


# --- default rounding mode / default FP sort (z3py globals) ----------------

_dflt_rm_name = ["RNE"]
_dflt_fp_sort = [(11, 53)]

_RM_BUILDERS = {
    "RNE": lambda ctx: RNE(ctx),
    "RNA": lambda ctx: RNA(ctx),
    "RTP": lambda ctx: RTP(ctx),
    "RTN": lambda ctx: RTN(ctx),
    "RTZ": lambda ctx: RTZ(ctx),
}


def get_default_rounding_mode(ctx=None):
    """The rounding mode used by the FP Python operators (z3py parity: RNE
    unless changed with set_default_rounding_mode)."""
    return _RM_BUILDERS[_dflt_rm_name[0]](ctx)


def set_default_rounding_mode(rm, ctx=None):
    if isinstance(rm, str):
        if rm not in _RM_BUILDERS:
            raise AyZ3Exception(f"unknown rounding mode {rm!r}")
        _dflt_rm_name[0] = rm
        return
    if not is_fprm_value(rm):
        raise AyZ3Exception(
            "set_default_rounding_mode expects one of RNE()/RNA()/RTP()/RTN()/RTZ()"
        )
    _dflt_rm_name[0] = lib.Z3_ast_to_string(rm.ctx.ref, rm.ast).decode()


def get_default_fp_sort(ctx=None):
    eb, sb = _dflt_fp_sort[0]
    return FPSort(eb, sb, ctx)


def set_default_fp_sort(ebits, sbits, ctx=None):
    _dflt_fp_sort[0] = (int(ebits), int(sbits))


# ---------------------------------------------------------------------------
# FP expressions
# ---------------------------------------------------------------------------


class FPRef(AstRef):
    """A floating-point-sorted expression (z3py FPRef).

    `==`/`!=` are SMT `=`/distinct (object equality, like z3py's ExprRef);
    the IEEE comparisons are fpEQ/fpLT/... and the `<`,`<=`,`>`,`>=`
    operators. Arithmetic operators round with the default rounding mode.
    """

    def ebits(self):
        return self.sort_ref.ebits()

    def sbits(self):
        return self.sort_ref.sbits()

    # --- arithmetic (default rounding mode, like z3py) ---------------------
    def __add__(self, other):
        return fpAdd(get_default_rounding_mode(self.ctx), self, other)

    def __radd__(self, other):
        return fpAdd(get_default_rounding_mode(self.ctx), other, self)

    def __sub__(self, other):
        return fpSub(get_default_rounding_mode(self.ctx), self, other)

    def __rsub__(self, other):
        return fpSub(get_default_rounding_mode(self.ctx), other, self)

    def __mul__(self, other):
        return fpMul(get_default_rounding_mode(self.ctx), self, other)

    def __rmul__(self, other):
        return fpMul(get_default_rounding_mode(self.ctx), other, self)

    def __truediv__(self, other):
        return fpDiv(get_default_rounding_mode(self.ctx), self, other)

    def __rtruediv__(self, other):
        return fpDiv(get_default_rounding_mode(self.ctx), other, self)

    def __mod__(self, other):
        return fpRem(self, other)

    def __rmod__(self, other):
        return fpRem(other, self)

    def __neg__(self):
        return fpNeg(self)

    def __pos__(self):
        return self

    # --- IEEE ordering comparisons (z3py FPRef operators) ------------------
    def __lt__(self, other):
        return fpLT(self, other)

    def __le__(self, other):
        return fpLEQ(self, other)

    def __gt__(self, other):
        return fpGT(self, other)

    def __ge__(self, other):
        return fpGEQ(self, other)

    def __hash__(self):
        return AstRef.__hash__(self)


# ---------------------------------------------------------------------------
# FP numerals (concrete values) — field parsing + z3py-style rendering
# ---------------------------------------------------------------------------

_FP_TOFP_LIT_RE = _re.compile(
    r"^\(\(_ to_fp (\d+) (\d+)\) #([xb])([0-9a-fA-F]+)\)$"
)
_FP_FIELDS_RE = _re.compile(
    r"^\(fp #([xb])([0-9a-fA-F]+) #([xb])([0-9a-fA-F]+) #([xb])([0-9a-fA-F]+)\)$"
)
_FP_SPECIAL_RE = _re.compile(r"^\(_ (NaN|\+oo|-oo|\+zero|-zero) (\d+) (\d+)\)$")


def _parse_fp_value(text, eb, sb):
    """Parse AY's textual FP value forms into (sign, biased_exp, mantissa)
    integer fields, or None if `text` is not a concrete FP value.

    Handles all three forms AY prints:
      `((_ to_fp E S) #xBITS)`  — constructed numerals (whole IEEE pattern)
      `(fp #x.. #x.. #x..)`     — model values (per-field, hex or binary)
      `(_ NaN/±oo/±zero E S)`   — specials
    """
    mb = sb - 1
    text = text.strip()
    m = _FP_SPECIAL_RE.match(text)
    if m:
        kind = m.group(1)
        all1 = (1 << eb) - 1
        return {
            "NaN": (0, all1, 1 << (mb - 1)),
            "+oo": (0, all1, 0),
            "-oo": (1, all1, 0),
            "+zero": (0, 0, 0),
            "-zero": (1, 0, 0),
        }[kind]
    m = _FP_TOFP_LIT_RE.match(text)
    if m:
        base = 16 if m.group(3) == "x" else 2
        bits = int(m.group(4), base)
        return (bits >> (eb + mb)) & 1, (bits >> mb) & ((1 << eb) - 1), bits & ((1 << mb) - 1)
    m = _FP_FIELDS_RE.match(text)
    if m:
        def fld(prefix, digits):
            return int(digits, 16 if prefix == "x" else 2)
        return (
            fld(m.group(1), m.group(2)),
            fld(m.group(3), m.group(4)),
            fld(m.group(5), m.group(6)),
        )
    return None


def _fp_ref_fields(ref):
    """(sign, biased_exp, mantissa) of a concrete FP AstRef, or None."""
    s = lib.Z3_ast_to_string(ref.ctx.ref, ref.ast)
    if not s:
        return None
    sort = ref.sort_ref
    return _parse_fp_value(s.decode(), sort.ebits(), sort.sbits())


def _exact_decimal(n, mb):
    """The EXACT decimal string of n / 2**mb (n, mb ints; denominator is a
    power of two so the expansion terminates)."""
    ip, rem = divmod(n, 1 << mb)
    if rem == 0:
        return str(ip)
    frac_digits = str(rem * 5**mb).rjust(mb, "0").rstrip("0")
    return f"{ip}.{frac_digits}"


def _fp_value_str(sign, exp, mant, eb, sb):
    """Render FP fields exactly the way z3py prints an FPNumRef.

    z3py: NaN -> "NaN"; infinities -> "+oo"/"-oo"; zeros -> "+0.0"/"-0.0";
    otherwise "<sig>*(2**<unbiased-exp>)" with the "*(2**0)" suffix omitted,
    where <sig> is the EXACT decimal of the significand (1.f, or 0.f for a
    subnormal) and the exponent is unbiased (1-bias for subnormals).
    """
    mb = sb - 1
    all1 = (1 << eb) - 1
    bias = (1 << (eb - 1)) - 1
    if exp == all1:
        if mant:
            return "NaN"
        return "-oo" if sign else "+oo"
    if exp == 0 and mant == 0:
        return "-0.0" if sign else "+0.0"
    if exp == 0:
        sig = _exact_decimal(mant, mb)          # 0.f (subnormal)
        e = 1 - bias
    else:
        sig = _exact_decimal((1 << mb) + mant, mb)  # 1.f
        e = exp - bias
    s = "-" if sign else ""
    if e == 0:
        return s + sig
    return f"{s}{sig}*(2**{e})"


# Formats whose FPVal numerals land through Z3_mk_fpa_numeral_double, i.e.
# in the `((_ to_fp E S) #x..)` / special shapes the NATIVE numeral accessors
# recognize. Other formats land through Z3_mk_fpa_fp (see FPVal), whose
# fp-constructor application the C accessors reject exactly like libz3.
_NATIVE_NUMERAL_FORMATS = ((5, 11), (8, 24), (11, 53))


class FPNumRef(FPRef):
    """A concrete FP value (z3py FPNumRef): field accessors + z3py rendering."""

    def _fields(self):
        """(sign, biased_exp, mantissa) via the NATIVE Z3_fpa_get_numeral_* /
        Z3_fpa_is_numeral_* accessors.

        Field triples are normalized to exactly what the textual reference
        parser (_parse_fp_value) produced: NaN canonicalized to the quiet
        positive pattern, infinities to all-ones-exponent/zero-mantissa.
        Formats whose exponent/trailing-significand fields exceed the
        int64/uint64 accessor widths (e.g. Float128, mb=112) fall back to the
        textual reference parser, which is exact at any width.
        """
        c, a = self.ctx.ref, self.ast
        eb, sb = self.ebits(), self.sbits()
        all1 = (1 << eb) - 1
        if self._is_model_value or (eb, sb) not in _NATIVE_NUMERAL_FORMATS:
            # `(fp <bv> <bv> <bv>)` field-constructor shapes — model values,
            # and FPVal numerals of the non-double-backed formats — are
            # numerals to ayz3 but NOT to the C accessors (which match libz3
            # in rejecting fp-constructor applications), so they read through
            # the textual reference parser (exact at any width).
            f = _fp_ref_fields(self)
            if f is None:
                raise AyZ3Exception("FP value fields are not available for this term")
            return f
        if lib.Z3_fpa_is_numeral_nan(c, a):
            return 0, all1, 1 << (sb - 2)
        if lib.Z3_fpa_is_numeral_inf(c, a):
            return int(bool(lib.Z3_fpa_is_numeral_negative(c, a))), all1, 0
        sgn = ctypes.c_int(0)
        exp = ctypes.c_int64(0)
        mant = ctypes.c_uint64(0)
        ok = (
            lib.Z3_fpa_get_numeral_sign(c, a, ctypes.byref(sgn))
            and lib.Z3_fpa_get_numeral_exponent_int64(c, a, ctypes.byref(exp), True)
            and lib.Z3_fpa_get_numeral_significand_uint64(c, a, ctypes.byref(mant))
        )
        if not ok:
            raise AyZ3Exception("FP value fields are not available for this term")
        return (1 if sgn.value else 0), int(exp.value), int(mant.value)

    def sign(self):
        """The sign bit as a Python bool (z3py FPNumRef.sign)."""
        return bool(self._fields()[0])

    def significand(self):
        """The significand as an exact decimal string (z3py .significand())."""
        _, exp, mant = self._fields()
        mb = self.sbits() - 1
        n = mant if exp == 0 else (1 << mb) + mant
        return _exact_decimal(n, mb)

    def significand_as_long(self):
        """The trailing-significand FIELD as an int (z3py semantics)."""
        return self._fields()[2]

    def exponent(self, biased=True):
        """The exponent as a decimal string (z3py .exponent())."""
        return str(self.exponent_as_long(biased))

    def exponent_as_long(self, biased=True):
        sign, exp, mant = self._fields()
        if biased:
            return exp
        bias = (1 << (self.ebits() - 1)) - 1
        # Unbiased: subnormals (and zeros) report emin = 1 - bias, matching
        # z3py's Z3_fpa_get_numeral_exponent_int64(..., biased=false).
        if exp == 0:
            return 1 - bias
        return exp - bias

    def isNaN(self):
        sign, exp, mant = self._fields()
        return exp == (1 << self.ebits()) - 1 and mant != 0

    def isInf(self):
        sign, exp, mant = self._fields()
        return exp == (1 << self.ebits()) - 1 and mant == 0

    def isZero(self):
        sign, exp, mant = self._fields()
        return exp == 0 and mant == 0

    def isNormal(self):
        sign, exp, mant = self._fields()
        return 0 < exp < (1 << self.ebits()) - 1

    def isSubnormal(self):
        sign, exp, mant = self._fields()
        return exp == 0 and mant != 0

    def isNegative(self):
        sign, exp, mant = self._fields()
        return bool(sign) and not self.isNaN()

    def isPositive(self):
        sign, exp, mant = self._fields()
        return not sign and not self.isNaN()

    def as_fraction(self):
        """The exact rational value of this (finite) FP value as a Fraction."""
        sign, exp, mant = self._fields()
        eb, sb = self.ebits(), self.sbits()
        if exp == (1 << eb) - 1:
            raise AyZ3Exception("NaN/inf has no rational value")
        mb = sb - 1
        bias = (1 << (eb - 1)) - 1
        if exp == 0:
            v = Fraction(mant, 1 << mb) * Fraction(2) ** (1 - bias)
        else:
            v = Fraction((1 << mb) + mant, 1 << mb) * Fraction(2) ** (exp - bias)
        return -v if sign else v

    def __float__(self):
        """The value as a Python float (exact for half/single/double)."""
        sign, exp, mant = self._fields()
        eb = self.ebits()
        if exp == (1 << eb) - 1:
            if mant:
                return float("nan")
            return float("-inf") if sign else float("inf")
        if exp == 0 and mant == 0:
            return -0.0 if sign else 0.0
        return float(self.as_fraction())

    def __repr__(self):
        sign, exp, mant = self._fields()
        return _fp_value_str(sign, exp, mant, self.ebits(), self.sbits())

    def __str__(self):
        return self.__repr__()

    def as_string(self):
        return repr(self)


def is_fp(a):
    """Whether `a` is a floating-point expression (z3py is_fp)."""
    return isinstance(a, FPRef)


def is_fp_value(a):
    """Whether `a` is a CONCRETE floating-point value (z3py is_fp_value)."""
    return isinstance(a, FPRef) and _fp_ref_fields(a) is not None


# ---------------------------------------------------------------------------
# FP constants and values
# ---------------------------------------------------------------------------


def FP(name, fpsort, ctx=None):
    """Declare an FP constant `name` of sort `fpsort` (z3py FP)."""
    if not isinstance(fpsort, FPSortRef):
        raise AyZ3Exception("FP(name, sort) requires an FPSort")
    ctx = ctx or fpsort.ctx
    if fpsort.ctx is not ctx:
        fpsort = FPSort(fpsort.ebits(), fpsort.sbits(), ctx)
    return _mk_const(name, fpsort, ctx)


def FPs(names, fpsort, ctx=None):
    """Declare several FP constants (z3py FPs)."""
    if isinstance(names, str):
        names = names.split()
    return [FP(n, fpsort, ctx) for n in names]


def _wrap_fp(ast, sort, ctx, numeral=False):
    if ast == 0:
        ctx.check_error("FP expression construction")
        raise AyZ3Exception("AY returned the null AST (0) for an FP expression")
    cls = FPNumRef if numeral else FPRef
    return cls(ast, sort, ctx)


def _target_fields_exact(value, eb, sb):
    """Round `value` (an exact Fraction) into (sign, biased_exp, mantissa)
    fields of the (eb, sb) format with round-to-nearest-ties-to-even, in exact
    bignum arithmetic (no double rounding)."""
    mb = sb - 1
    bias = (1 << (eb - 1)) - 1
    emax = bias
    sign = 1 if value < 0 else 0
    v = -value if value < 0 else value
    if v == 0:
        return sign, 0, 0
    # Find E with 2**E <= v < 2**(E+1).
    E = v.numerator.bit_length() - v.denominator.bit_length()
    if Fraction(2) ** E > v:
        E -= 1
    if Fraction(2) ** (E + 1) <= v:
        E += 1

    def round_half_even(x):
        ip = x.numerator // x.denominator
        rem = x - ip
        if rem > Fraction(1, 2) or (rem == Fraction(1, 2) and ip % 2 == 1):
            ip += 1
        return ip

    if E < 1 - bias:
        # Subnormal range.
        scaled = v / (Fraction(2) ** (1 - bias - mb))
        mant = round_half_even(scaled)
        if mant >= (1 << mb):
            return sign, 1, 0  # rounded up into the smallest normal
        return sign, 0, mant
    scaled = v / (Fraction(2) ** E) * (1 << mb)  # in [2**mb, 2**(mb+1))
    n = round_half_even(scaled)
    if n >= (1 << (mb + 1)):
        n >>= 1
        E += 1
    exp = E + bias
    if E > emax:
        return sign, (1 << eb) - 1, 0  # overflow -> infinity
    return sign, exp, n - (1 << mb)


def _fields_to_double(sign, exp, mant, eb, sb):
    """The Python float equal EXACTLY to the FP value with these fields, or
    None if the value is not representable as a double (only possible for
    formats wider than double, e.g. Float128 beyond double precision)."""
    mb = sb - 1
    all1 = (1 << eb) - 1
    if exp == all1:
        if mant:
            return float("nan")
        return float("-inf") if sign else float("inf")
    if exp == 0 and mant == 0:
        return -0.0 if sign else 0.0
    bias = (1 << (eb - 1)) - 1
    if exp == 0:
        frac = Fraction(mant, 1 << mb) * Fraction(2) ** (1 - bias)
    else:
        frac = Fraction((1 << mb) + mant, 1 << mb) * Fraction(2) ** (exp - bias)
    if sign:
        frac = -frac
    d = float(frac)
    if Fraction(d) != frac:
        return None
    return d


_FPVAL_SPECIALS = {
    "nan": "nan",
    "+oo": "+inf", "oo": "+inf", "inf": "+inf", "+inf": "+inf",
    "plusinfinity": "+inf",
    "-oo": "-inf", "-inf": "-inf", "minusinfinity": "-inf",
    "+zero": "+0", "+0": "+0", "+0.0": "+0",
    "-zero": "-0", "-0": "-0", "-0.0": "-0",
}


def FPVal(val, exp=None, fps=None, ctx=None):
    """A floating-point value (z3py FPVal).

    Accepts z3py's flexible call shapes: FPVal(v), FPVal(v, fpsort),
    FPVal(v, exp, fpsort). `v` may be a Python float/int/Fraction, a decimal
    string ("1.5", "-2.5e3"), a rational string ("15/4"), or one of the
    special strings "NaN"/"+oo"/"-oo"/"+zero"/"-zero"/"inf"/"-inf".

    The value is rounded to the target format with RNE in EXACT bignum
    arithmetic (identical to z3py/SMT-LIB semantics; no double rounding).
    """
    # z3py argument juggling: the sort may arrive via `exp` or `fps`.
    if fps is None and isinstance(exp, FPSortRef):
        fps, exp = exp, None
    if fps is None:
        fps = get_default_fp_sort(ctx)
    if not isinstance(fps, FPSortRef):
        raise AyZ3Exception("FPVal requires an FP sort")
    ctx = ctx or fps.ctx
    if fps.ctx is not ctx:
        fps = FPSort(fps.ebits(), fps.sbits(), ctx)
    if exp is None:
        exp = 0

    # Specials (strings and non-finite floats).
    if isinstance(val, str):
        key = val.strip().lower()
        special = _FPVAL_SPECIALS.get(key)
        if special == "nan":
            return fpNaN(fps)
        if special == "+inf":
            return fpPlusInfinity(fps)
        if special == "-inf":
            return fpMinusInfinity(fps)
        if special == "+0":
            return fpPlusZero(fps)
        if special == "-0":
            return fpMinusZero(fps)
        try:
            frac = Fraction(val)  # exact: decimal or rational string
        except ValueError:
            raise AyZ3Exception(f"cannot build an FP value from string {val!r}")
    elif isinstance(val, float):
        if val != val:  # NaN
            return fpNaN(fps)
        if val == float("inf"):
            return fpPlusInfinity(fps)
        if val == float("-inf"):
            return fpMinusInfinity(fps)
        if val == 0.0:
            import math
            return fpMinusZero(fps) if math.copysign(1.0, val) < 0 else fpPlusZero(fps)
        frac = Fraction(val)  # exact value of the double
    elif isinstance(val, (int, Fraction)):
        frac = Fraction(val)
    elif isinstance(val, FPNumRef):
        return val
    else:
        raise AyZ3Exception(f"cannot build an FP value from {val!r}")

    frac = frac * Fraction(2) ** int(exp)
    sign, e, m = _target_fields_exact(frac, fps.ebits(), fps.sbits())
    if e == 0 and m == 0:
        return fpMinusZero(fps) if sign else fpPlusZero(fps)
    if e == (1 << fps.ebits()) - 1:
        return fpMinusInfinity(fps) if sign else fpPlusInfinity(fps)
    if (fps.ebits(), fps.sbits()) in ((5, 11), (8, 24), (11, 53)):
        d = _fields_to_double(sign, e, m, fps.ebits(), fps.sbits())
        ast = lib.Z3_mk_fpa_numeral_double(ctx.ref, d, fps.handle)
        return _wrap_fp(ast, fps, ctx, numeral=True)
    # Other formats (e.g. Float128): land the EXACT already-rounded fields
    # through the per-field constructor Z3_mk_fpa_fp — no precision loss.
    ayz3 = _pkg()
    sgn_bv = ayz3.BitVecVal(sign, 1, ctx)
    exp_bv = ayz3.BitVecVal(e, fps.ebits(), ctx)
    sig_bv = ayz3.BitVecVal(m, fps.sbits() - 1, ctx)
    ast = lib.Z3_mk_fpa_fp(ctx.ref, sgn_bv.ast, exp_bv.ast, sig_bv.ast)
    return _wrap_fp(ast, fps, ctx, numeral=True)


def fpNaN(s):
    """NaN of FP sort `s` (z3py fpNaN)."""
    return _wrap_fp(lib.Z3_mk_fpa_nan(s.ctx.ref, s.handle), s, s.ctx, numeral=True)


def fpInfinity(s, negative):
    """±infinity of FP sort `s` (z3py fpInfinity)."""
    ast = lib.Z3_mk_fpa_inf(s.ctx.ref, s.handle, bool(negative))
    return _wrap_fp(ast, s, s.ctx, numeral=True)


def fpPlusInfinity(s):
    return fpInfinity(s, False)


def fpMinusInfinity(s):
    return fpInfinity(s, True)


def fpZero(s, negative):
    """±0 of FP sort `s` (z3py fpZero)."""
    ast = lib.Z3_mk_fpa_zero(s.ctx.ref, s.handle, bool(negative))
    return _wrap_fp(ast, s, s.ctx, numeral=True)


def fpPlusZero(s):
    return fpZero(s, False)


def fpMinusZero(s):
    return fpZero(s, True)


# ---------------------------------------------------------------------------
# Operand coercion
# ---------------------------------------------------------------------------


def _coerce_fp(x, sort_hint=None, ctx=None):
    if isinstance(x, FPRef):
        return x
    if isinstance(x, (int, float, str, Fraction)):
        sort = sort_hint if isinstance(sort_hint, FPSortRef) else get_default_fp_sort(ctx)
        return FPVal(x, sort, ctx=ctx or sort.ctx)
    raise AyZ3Exception(
        f"cannot use {x!r} as a floating-point operand; build an FP value with "
        f"FPVal(x, sort) or an FP const with FP(name, sort)"
    )


def _fp_pair(a, b, name):
    """Coerce (a, b) into same-sorted FPRefs in one context (z3py's _coerce_fp_pair)."""
    if not isinstance(a, FPRef) and not isinstance(b, FPRef):
        raise AyZ3Exception(f"{name}: at least one operand must be an FP expression")
    if isinstance(a, FPRef):
        b = _coerce_fp(b, a.sort_ref, a.ctx)
    else:
        a = _coerce_fp(a, b.sort_ref, b.ctx)
    ayz3 = _pkg()
    ctx = ayz3._same_ctx(a, b)
    a = ayz3._adopt(a, ctx)
    b = ayz3._adopt(b, ctx)
    if a.sort_ref != b.sort_ref:
        raise AyZ3Exception(
            f"{name}: operands must share an FP sort "
            f"({a.sort_ref} vs {b.sort_ref})"
        )
    return a, b, ctx


def _rm_in_ctx(rm, ctx, name):
    if not isinstance(rm, FPRMRef):
        raise AyZ3Exception(f"{name}: first argument must be a rounding mode "
                            f"(RNE()/RNA()/RTP()/RTN()/RTZ()), got {rm!r}")
    return _pkg()._adopt(rm, ctx)


# ---------------------------------------------------------------------------
# FP arithmetic
# ---------------------------------------------------------------------------


def _fp_rm_binop(mk, name, rm, a, b, ctx=None):
    a, b, ctx = _fp_pair(a, b, name)
    rm = _rm_in_ctx(rm, ctx, name)
    return _wrap_fp(mk(ctx.ref, rm.ast, a.ast, b.ast), a.sort_ref, ctx)


def fpAdd(rm, a, b, ctx=None):
    return _fp_rm_binop(lib.Z3_mk_fpa_add, "fpAdd", rm, a, b, ctx)


def fpSub(rm, a, b, ctx=None):
    return _fp_rm_binop(lib.Z3_mk_fpa_sub, "fpSub", rm, a, b, ctx)


def fpMul(rm, a, b, ctx=None):
    return _fp_rm_binop(lib.Z3_mk_fpa_mul, "fpMul", rm, a, b, ctx)


def fpDiv(rm, a, b, ctx=None):
    return _fp_rm_binop(lib.Z3_mk_fpa_div, "fpDiv", rm, a, b, ctx)


def fpFMA(rm, a, b, c, ctx=None):
    """fused multiply-add: round(a*b + c) with one rounding (z3py fpFMA)."""
    a, b, ctx2 = _fp_pair(a, b, "fpFMA")
    c = _coerce_fp(c, a.sort_ref, ctx2)
    c = _pkg()._adopt(c, ctx2)
    if c.sort_ref != a.sort_ref:
        raise AyZ3Exception("fpFMA: operands must share an FP sort")
    rm = _rm_in_ctx(rm, ctx2, "fpFMA")
    ast = lib.Z3_mk_fpa_fma(ctx2.ref, rm.ast, a.ast, b.ast, c.ast)
    return _wrap_fp(ast, a.sort_ref, ctx2)


def fpSqrt(rm, a, ctx=None):
    a = _coerce_fp(a, None, ctx)
    rm = _rm_in_ctx(rm, a.ctx, "fpSqrt")
    return _wrap_fp(lib.Z3_mk_fpa_sqrt(a.ctx.ref, rm.ast, a.ast), a.sort_ref, a.ctx)


def fpRoundToIntegral(rm, a, ctx=None):
    a = _coerce_fp(a, None, ctx)
    rm = _rm_in_ctx(rm, a.ctx, "fpRoundToIntegral")
    ast = lib.Z3_mk_fpa_round_to_integral(a.ctx.ref, rm.ast, a.ast)
    return _wrap_fp(ast, a.sort_ref, a.ctx)


def fpAbs(a, ctx=None):
    a = _coerce_fp(a, None, ctx)
    return _wrap_fp(lib.Z3_mk_fpa_abs(a.ctx.ref, a.ast), a.sort_ref, a.ctx)


def fpNeg(a, ctx=None):
    a = _coerce_fp(a, None, ctx)
    return _wrap_fp(lib.Z3_mk_fpa_neg(a.ctx.ref, a.ast), a.sort_ref, a.ctx)


def fpRem(a, b, ctx=None):
    a, b, ctx = _fp_pair(a, b, "fpRem")
    return _wrap_fp(lib.Z3_mk_fpa_rem(ctx.ref, a.ast, b.ast), a.sort_ref, ctx)


def fpMin(a, b, ctx=None):
    a, b, ctx = _fp_pair(a, b, "fpMin")
    return _wrap_fp(lib.Z3_mk_fpa_min(ctx.ref, a.ast, b.ast), a.sort_ref, ctx)


def fpMax(a, b, ctx=None):
    a, b, ctx = _fp_pair(a, b, "fpMax")
    return _wrap_fp(lib.Z3_mk_fpa_max(ctx.ref, a.ast, b.ast), a.sort_ref, ctx)


# ---------------------------------------------------------------------------
# FP comparisons / classification predicates (-> BoolRef)
# ---------------------------------------------------------------------------


def _fp_cmp(mk, name, a, b):
    a, b, ctx = _fp_pair(a, b, name)
    return BoolRef(mk(ctx.ref, a.ast, b.ast), _bool_sort(ctx), ctx)


def fpEQ(a, b, ctx=None):
    """IEEE equality `fp.eq` (NaN != NaN; +0 == -0) — z3py fpEQ."""
    return _fp_cmp(lib.Z3_mk_fpa_eq, "fpEQ", a, b)


def fpNEQ(a, b, ctx=None):
    """Not(fpEQ(a, b)) — z3py fpNEQ."""
    return _pkg().Not(fpEQ(a, b))


def fpLT(a, b, ctx=None):
    return _fp_cmp(lib.Z3_mk_fpa_lt, "fpLT", a, b)


def fpLEQ(a, b, ctx=None):
    return _fp_cmp(lib.Z3_mk_fpa_leq, "fpLEQ", a, b)


def fpGT(a, b, ctx=None):
    return _fp_cmp(lib.Z3_mk_fpa_gt, "fpGT", a, b)


def fpGEQ(a, b, ctx=None):
    return _fp_cmp(lib.Z3_mk_fpa_geq, "fpGEQ", a, b)


def _fp_pred(mk, name, a, ctx=None):
    a = _coerce_fp(a, None, ctx)
    return BoolRef(mk(a.ctx.ref, a.ast), _bool_sort(a.ctx), a.ctx)


def fpIsNaN(a, ctx=None):
    return _fp_pred(lib.Z3_mk_fpa_is_nan, "fpIsNaN", a, ctx)


def fpIsInf(a, ctx=None):
    return _fp_pred(lib.Z3_mk_fpa_is_infinite, "fpIsInf", a, ctx)


def fpIsInfinite(a, ctx=None):
    return fpIsInf(a, ctx)


def fpIsZero(a, ctx=None):
    return _fp_pred(lib.Z3_mk_fpa_is_zero, "fpIsZero", a, ctx)


def fpIsNormal(a, ctx=None):
    return _fp_pred(lib.Z3_mk_fpa_is_normal, "fpIsNormal", a, ctx)


def fpIsSubnormal(a, ctx=None):
    return _fp_pred(lib.Z3_mk_fpa_is_subnormal, "fpIsSubnormal", a, ctx)


def fpIsNegative(a, ctx=None):
    return _fp_pred(lib.Z3_mk_fpa_is_negative, "fpIsNegative", a, ctx)


def fpIsPositive(a, ctx=None):
    return _fp_pred(lib.Z3_mk_fpa_is_positive, "fpIsPositive", a, ctx)


# ---------------------------------------------------------------------------
# Conversions
# ---------------------------------------------------------------------------


def _to_fp_sort_in_ctx(sort, ctx):
    if not isinstance(sort, FPSortRef):
        raise AyZ3Exception("conversion target must be an FP sort")
    if sort.ctx is not ctx:
        sort = FPSort(sort.ebits(), sort.sbits(), ctx)
    return sort


def fpFPToFP(rm, v, sort, ctx=None):
    """Convert an FP term to another FP sort, rounding with `rm` (z3py fpFPToFP)."""
    if not isinstance(v, FPRef):
        raise AyZ3Exception("fpFPToFP expects an FP expression")
    rm = _rm_in_ctx(rm, v.ctx, "fpFPToFP")
    sort = _to_fp_sort_in_ctx(sort, v.ctx)
    ast = lib.Z3_mk_fpa_to_fp_float(v.ctx.ref, rm.ast, v.ast, sort.handle)
    return _wrap_fp(ast, sort, v.ctx)


def fpSignedToFP(rm, v, sort, ctx=None):
    """Convert a signed (2's-complement) BV to FP (z3py fpSignedToFP)."""
    ayz3 = _pkg()
    if not isinstance(v, ayz3.BitVecRef):
        raise AyZ3Exception("fpSignedToFP expects a bit-vector expression")
    rm = _rm_in_ctx(rm, v.ctx, "fpSignedToFP")
    sort = _to_fp_sort_in_ctx(sort, v.ctx)
    ast = lib.Z3_mk_fpa_to_fp_signed(v.ctx.ref, rm.ast, v.ast, sort.handle)
    return _wrap_fp(ast, sort, v.ctx)


def fpToFP(a1, a2=None, a3=None, ctx=None):
    """z3py fpToFP dispatch (exactly z3py 4.15.4's accepted shapes):
      fpToFP(BitVecRef, FPSort)      -> IEEE-bits BV -> FP (Z3_mk_fpa_to_fp_bv)
      fpToFP(rm, FPRef, FPSort)      -> FP -> FP        (Z3_mk_fpa_to_fp_float)
      fpToFP(rm, RealRef, FPSort)    -> Real -> FP      (Z3_mk_fpa_to_fp_real)
      fpToFP(rm, BitVecRef, FPSort)  -> signed BV -> FP (Z3_mk_fpa_to_fp_signed)
    Anything else (including a bare Python float, which z3py 4.15.4 also
    rejects) raises the same "Unsupported combination" error as z3py.
    """
    ayz3 = _pkg()
    if isinstance(a1, ayz3.BitVecRef) and isinstance(a2, FPSortRef):
        return fpBVToFP(a1, a2, ctx)
    if isinstance(a1, FPRMRef):
        rm, v, sort = a1, a2, a3
        if isinstance(v, FPRef) and isinstance(sort, FPSortRef):
            return fpFPToFP(rm, v, sort, ctx)
        if isinstance(v, ayz3.ArithRef) and v.sort_ref.kind == "Real" \
                and isinstance(sort, FPSortRef):
            return fpRealToFP(rm, v, sort, ctx)
        if isinstance(v, ayz3.BitVecRef) and isinstance(sort, FPSortRef):
            return fpSignedToFP(rm, v, sort, ctx)
    raise AyZ3Exception(
        "Unsupported combination of arguments for conversion to floating-point term."
    )


def fpBVToFP(v, sort, ctx=None):
    """Reinterpret a BV term as the IEEE-754 bit pattern of an FP value
    (z3py fpBVToFP; the BV width must equal ebits+sbits)."""
    ayz3 = _pkg()
    if not isinstance(v, ayz3.BitVecRef):
        raise AyZ3Exception("fpBVToFP expects a bit-vector expression")
    sort = _to_fp_sort_in_ctx(sort, v.ctx)
    ast = lib.Z3_mk_fpa_to_fp_bv(v.ctx.ref, v.ast, sort.handle)
    return _wrap_fp(ast, sort, v.ctx)


def fpRealToFP(rm, v, sort, ctx=None):
    """Convert a Real term to FP, rounding with `rm` (z3py fpRealToFP)."""
    ayz3 = _pkg()
    if not (isinstance(v, ayz3.ArithRef) and v.sort_ref.kind == "Real"):
        raise AyZ3Exception("fpRealToFP expects a real expression")
    rm = _rm_in_ctx(rm, v.ctx, "fpRealToFP")
    sort = _to_fp_sort_in_ctx(sort, v.ctx)
    ast = lib.Z3_mk_fpa_to_fp_real(v.ctx.ref, rm.ast, v.ast, sort.handle)
    return _wrap_fp(ast, sort, v.ctx)


def fpUnsignedToFP(rm, v, sort, ctx=None):
    """Convert an unsigned BV to FP, rounding with `rm` (z3py fpUnsignedToFP)."""
    ayz3 = _pkg()
    if not isinstance(v, ayz3.BitVecRef):
        raise AyZ3Exception("fpUnsignedToFP expects a bit-vector expression")
    rm = _rm_in_ctx(rm, v.ctx, "fpUnsignedToFP")
    sort = _to_fp_sort_in_ctx(sort, v.ctx)
    ast = lib.Z3_mk_fpa_to_fp_unsigned(v.ctx.ref, rm.ast, v.ast, sort.handle)
    return _wrap_fp(ast, sort, v.ctx)


def _fp_to_bv(cfn, pyname, rm, v, sort, signed):
    ayz3 = _pkg()
    if not isinstance(v, FPRef):
        raise AyZ3Exception(f"{pyname} expects an FP expression")
    if not (isinstance(sort, ayz3.SortRef) and sort.kind == "BitVec"):
        raise AyZ3Exception(f"{pyname} expects a bit-vector target sort")
    rm = _rm_in_ctx(rm, v.ctx, pyname)
    ast = cfn(v.ctx.ref, rm.ast, v.ast, sort.size())
    if ast == 0:
        v.ctx.check_error(pyname)
        raise AyZ3Exception(f"AY returned the null AST (0) for {pyname}")
    return ayz3.BitVecRef(ast, ayz3._bv_sort(sort.size(), v.ctx), v.ctx)


def fpToSBV(rm, v, sort, ctx=None):
    """Convert an FP term to a signed BV, rounding with `rm` (z3py fpToSBV)."""
    return _fp_to_bv(lib.Z3_mk_fpa_to_sbv, "fpToSBV", rm, v, sort, True)


def fpToUBV(rm, v, sort, ctx=None):
    """Convert an FP term to an unsigned BV, rounding with `rm` (z3py fpToUBV)."""
    return _fp_to_bv(lib.Z3_mk_fpa_to_ubv, "fpToUBV", rm, v, sort, False)


def fpToReal(v, ctx=None):
    """Convert an FP term to its exact Real value (z3py fpToReal)."""
    ayz3 = _pkg()
    if not isinstance(v, FPRef):
        raise AyZ3Exception("fpToReal expects an FP expression")
    ast = lib.Z3_mk_fpa_to_real(v.ctx.ref, v.ast)
    if ast == 0:
        v.ctx.check_error("fpToReal")
        raise AyZ3Exception("AY returned the null AST (0) for fpToReal")
    return ayz3.ArithRef(ast, ayz3._real_sort(v.ctx), v.ctx)


def fpToIEEEBV(v, ctx=None):
    """The IEEE-754 bit pattern of an FP term as a BV of width ebits+sbits
    (z3py fpToIEEEBV; NaN's bit pattern is underspecified, as in z3)."""
    ayz3 = _pkg()
    if not isinstance(v, FPRef):
        raise AyZ3Exception("fpToIEEEBV expects an FP expression")
    ast = lib.Z3_mk_fpa_to_ieee_bv(v.ctx.ref, v.ast)
    if ast == 0:
        v.ctx.check_error("fpToIEEEBV")
        raise AyZ3Exception("AY returned the null AST (0) for fpToIEEEBV")
    width = v.sort_ref.ebits() + v.sort_ref.sbits()
    return ayz3.BitVecRef(ast, ayz3._bv_sort(width, v.ctx), v.ctx)


def fpFP(sgn, exp, sig, ctx=None):
    """Construct an FP term from sign/exponent/significand BV terms
    (z3py fpFP: sgn is a BV of size 1; the result sort is
    FPSort(exp.size(), sig.size()+1))."""
    ayz3 = _pkg()
    if not (isinstance(sgn, ayz3.BitVecRef) and isinstance(exp, ayz3.BitVecRef)
            and isinstance(sig, ayz3.BitVecRef)):
        raise AyZ3Exception("fpFP expects three bit-vector expressions")
    if sgn.sort_ref.size() != 1:
        raise AyZ3Exception("sort mismatch: the sign bit-vector must have size 1")
    if not (sgn.ctx is exp.ctx is sig.ctx):
        raise AyZ3Exception("fpFP arguments must share a context")
    ast = lib.Z3_mk_fpa_fp(sgn.ctx.ref, sgn.ast, exp.ast, sig.ast)
    sort = FPSort(exp.sort_ref.size(), sig.sort_ref.size() + 1, sgn.ctx)
    return _wrap_fp(ast, sort, sgn.ctx)


# ---------------------------------------------------------------------------
# Cross-context rebuild support (called from ayz3._rebuild_app)
# ---------------------------------------------------------------------------

_FP_SPECIAL_DECLS = ("NaN", "+oo", "-oo", "+zero", "-zero")
_FP_RM_DECLS = {
    "RNE": lambda c: lib.Z3_mk_fpa_rne(c),
    "RNA": lambda c: lib.Z3_mk_fpa_rna(c),
    "RTP": lambda c: lib.Z3_mk_fpa_rtp(c),
    "RTN": lambda c: lib.Z3_mk_fpa_rtn(c),
    "RTZ": lambda c: lib.Z3_mk_fpa_rtz(c),
}

_FP_SORT_NAME_RE = _re.compile(r"^\(_ FloatingPoint (\d+) (\d+)\)$")


def _fp_sort_dims_of_ast(src_ast, src_ctx):
    """(ebits, sbits) of an FP-sorted source AST, from its sort name."""
    sh = lib.Z3_get_sort(src_ctx.ref, src_ast)
    sym = lib.Z3_get_sort_name(src_ctx.ref, sh) if sh else None
    nm = lib.Z3_get_symbol_string(src_ctx.ref, sym) if sym else None
    m = _FP_SORT_NAME_RE.match(nm.decode()) if nm else None
    if not m:
        raise AyZ3Exception("could not recover the FP sort of a term during rebuild")
    return int(m.group(1)), int(m.group(2))


def _rebuild_fp_app(name, decl, src_ast, src_ctx, dctx, args):
    """Rebuild the FP application nodes that need source-sort context
    (specials and `to_fp`); returns the dst AST or None if `name` is not one
    of them. The sort-agnostic fp.* operators rebuild via _REBUILD_OPS."""
    if name in _FP_RM_DECLS:
        return _FP_RM_DECLS[name](dctx.ref)
    if name in _FP_SPECIAL_DECLS:
        eb, sb = _fp_sort_dims_of_ast(src_ast, src_ctx)
        dsort = lib.Z3_mk_fpa_sort(dctx.ref, eb, sb)
        if name == "NaN":
            return lib.Z3_mk_fpa_nan(dctx.ref, dsort)
        if name in ("+oo", "-oo"):
            return lib.Z3_mk_fpa_inf(dctx.ref, dsort, name == "-oo")
        return lib.Z3_mk_fpa_zero(dctx.ref, dsort, name == "-zero")
    if name == "to_fp":
        eb, sb = _fp_sort_dims_of_ast(src_ast, src_ctx)
        dsort = lib.Z3_mk_fpa_sort(dctx.ref, eb, sb)
        if len(args) == 1:
            # An FP NUMERAL: `((_ to_fp E S) #xBITS)`. Decode the IEEE bit
            # pattern from the source text and re-land it via numeral_double
            # (exact for any format up to double precision).
            s = lib.Z3_ast_to_string(src_ctx.ref, src_ast)
            fields = _parse_fp_value(s.decode(), eb, sb) if s else None
            if fields is not None:
                d = _fields_to_double(*fields, eb, sb)
                if d is not None:
                    return lib.Z3_mk_fpa_numeral_double(dctx.ref, d, dsort)
            # Not a numeral in a recognized textual form (or beyond double
            # precision): `((_ to_fp E S) bv)` is the IEEE reinterpretation,
            # which Z3_mk_fpa_to_fp_bv re-lands EXACTLY from the rebuilt arg.
            return lib.Z3_mk_fpa_to_fp_bv(dctx.ref, args[0], dsort)
        if len(args) == 2:
            # `((_ to_fp E S) rm arg)`: FP->FP, signed-BV->FP or Real->FP
            # depending on the SOURCE argument's sort.
            src_arg = lib.Z3_get_app_arg(src_ctx.ref, src_ast, 1)
            ash = lib.Z3_get_sort(src_ctx.ref, src_arg)
            akind = lib.Z3_get_sort_kind(src_ctx.ref, ash) if ash else None
            if akind == _lib.Z3_BV_SORT:
                return lib.Z3_mk_fpa_to_fp_signed(dctx.ref, args[0], args[1], dsort)
            if akind == _lib.Z3_REAL_SORT:
                return lib.Z3_mk_fpa_to_fp_real(dctx.ref, args[0], args[1], dsort)
            return lib.Z3_mk_fpa_to_fp_float(dctx.ref, args[0], args[1], dsort)
    if name == "to_fp_unsigned":
        eb, sb = _fp_sort_dims_of_ast(src_ast, src_ctx)
        dsort = lib.Z3_mk_fpa_sort(dctx.ref, eb, sb)
        return lib.Z3_mk_fpa_to_fp_unsigned(dctx.ref, args[0], args[1], dsort)
    if name in ("fp.to_sbv", "fp.to_ubv"):
        # The target width is the RESULT sort's BV width.
        sh = lib.Z3_get_sort(src_ctx.ref, src_ast)
        sz = lib.Z3_get_bv_sort_size(src_ctx.ref, sh) if sh else 0
        mk = lib.Z3_mk_fpa_to_sbv if name == "fp.to_sbv" else lib.Z3_mk_fpa_to_ubv
        return mk(dctx.ref, args[0], args[1], sz)
    if name == "fp.to_real":
        return lib.Z3_mk_fpa_to_real(dctx.ref, args[0])
    if name == "fp.to_ieee_bv":
        return lib.Z3_mk_fpa_to_ieee_bv(dctx.ref, args[0])
    if name == "fp" and len(args) == 3:
        return lib.Z3_mk_fpa_fp(dctx.ref, args[0], args[1], args[2])
    return None


# ---------------------------------------------------------------------------
# Back-compat combinators from the old (fragment-based) ayz3 FP layer.
# FP constraints are now ordinary BoolRefs, so these are the ordinary Boolean
# connectives; kept so existing ayz3 user code keeps working.
# ---------------------------------------------------------------------------


def FpAnd(*args):
    return _pkg().And(*args)


def FpOr(*args):
    return _pkg().Or(*args)


def FpNot(a):
    return _pkg().Not(a)


def FpImplies(a, b):
    return _pkg().Implies(a, b)
