// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point numeral introspection and Real/Int -> FP construction.
//!
//! Backs the Z3-compatible `Z3_fpa_is_numeral*` / `Z3_fpa_get_numeral_*`
//! accessors and the `Z3_mk_fpa_to_fp_real` / `Z3_mk_fpa_to_fp_int_real`
//! constructors (see `crates/ay-ffi/src/z3_compat/fpa_introspect.rs`).
//!
//! # The three canonical FP-numeral term shapes
//!
//! AY has no dedicated FP `Constant` variant — a floating-point numeral is an
//! *application*, so [`Solver::numeral_string`](Self::numeral_string) returns
//! `None` for it and a dedicated decoder is required.
//! [`fp_numeral_decode`](Solver::fp_numeral_decode) recognizes exactly the shapes
//! AY's own FP builders (`floating_point.rs`, `floating_point_conv.rs`) and the
//! FFI numeral constructors (`fpa.rs`, `fpa_ext.rs`) produce:
//!
//! 1. **Nullary indexed special-value apps** — `(_ +oo eb sb)`, `(_ -oo eb sb)`,
//!    `(_ NaN eb sb)`, `(_ +zero eb sb)`, `(_ -zero eb sb)` (built by
//!    `try_fp_plus_infinity` / `try_fp_nan` / ...). The canonical IEEE-754
//!    bit-fields are synthesized from the value's category.
//! 2. **1-arg `(_ to_fp eb sb) bv`** whose child is a concrete BitVec `Const` of
//!    width `eb + sb` (built by `try_bv_to_fp_reinterpret`, the path
//!    `try_fp_const_from_bits_bigint` / `Z3_mk_fpa_numeral_double` take). The
//!    child's bits are split into `sign | exponent | trailing-significand`.
//! 3. **3-arg `(fp sgn exp sig)`** over three concrete BitVec `Const`s (built by
//!    `try_fp_from_bvs` / `Z3_mk_fpa_fp`).
//!
//! Any operand that is not a concrete `Const` (e.g. a `to_fp` over a *rounding
//! mode + symbolic BV*, an `fp` over symbolic components, or a plain FP variable)
//! yields `None`: these are symbolic terms, not numerals, and the decoder never
//! fabricates a value for them.
//!
//! # Field semantics (soundness)
//!
//! [`FpNumeral`] carries the raw IEEE-754 encoding fields: the 1-bit `sign`, the
//! `eb`-bit biased `exp_field`, and the `(sb-1)`-bit trailing `sig_field`. The
//! `category` is the IEEE class derived from those fields (or fixed directly for
//! the special-value apps). Every accessor reads these fields directly — nothing
//! is invented. NaN carries no meaningful sign/significand/exponent, so the FFI
//! value accessors decline it (matching Z3, which raises an error for NaN).

use super::types::{SolverError, Term};
use super::Solver;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigUint;
use num_traits::Zero;

/// IEEE-754 value category of a decoded floating-point numeral.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpCategory {
    /// Not-a-Number: `exp_field` all ones and `sig_field != 0`.
    NaN,
    /// +/-infinity: `exp_field` all ones and `sig_field == 0`.
    Inf,
    /// +/-zero: `exp_field == 0` and `sig_field == 0`.
    Zero,
    /// Normal (with implicit leading `1`): `0 < exp_field < all-ones`.
    Normal,
    /// Subnormal (denormal): `exp_field == 0` and `sig_field != 0`.
    Subnormal,
}

/// The decoded IEEE-754 encoding fields of an AY floating-point numeral term.
///
/// Produced by [`Solver::fp_numeral_decode`]. All fields are exact and read
/// straight off the term; see the module docs for the recognized term shapes.
#[derive(Debug, Clone)]
pub struct FpNumeral {
    /// The sign bit (`true` = negative). AY's canonical NaN reports `false`.
    pub sign: bool,
    /// The biased exponent field (`eb` bits, unsigned).
    pub exp_field: BigUint,
    /// The trailing-significand field (`sb - 1` bits, unsigned; excludes the
    /// implicit leading bit).
    pub sig_field: BigUint,
    /// Exponent width in bits.
    pub eb: u32,
    /// Significand width in bits INCLUDING the implicit leading bit (so the
    /// stored trailing field is `sb - 1` bits wide).
    pub sb: u32,
    /// The IEEE-754 value category.
    pub category: FpCategory,
}

impl FpNumeral {
    /// `true` iff the value is NaN.
    #[must_use]
    pub fn is_nan(&self) -> bool {
        matches!(self.category, FpCategory::NaN)
    }

    /// `true` iff the value is +/-infinity.
    #[must_use]
    pub fn is_inf(&self) -> bool {
        matches!(self.category, FpCategory::Inf)
    }

    /// `true` iff the value is +/-zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        matches!(self.category, FpCategory::Zero)
    }

    /// `true` iff the value is a normal (implicit-leading-`1`) number.
    #[must_use]
    pub fn is_normal(&self) -> bool {
        matches!(self.category, FpCategory::Normal)
    }

    /// `true` iff the value is subnormal (denormal).
    #[must_use]
    pub fn is_subnormal(&self) -> bool {
        matches!(self.category, FpCategory::Subnormal)
    }

    /// Classify an `(exp_field, sig_field)` pair per IEEE-754.
    #[must_use]
    fn category_from_fields(exp_field: &BigUint, sig_field: &BigUint, eb: u32) -> FpCategory {
        let all_ones = (BigUint::from(1u8) << (eb as usize)) - BigUint::from(1u8);
        if *exp_field == all_ones {
            if sig_field.is_zero() {
                FpCategory::Inf
            } else {
                FpCategory::NaN
            }
        } else if exp_field.is_zero() {
            if sig_field.is_zero() {
                FpCategory::Zero
            } else {
                FpCategory::Subnormal
            }
        } else {
            FpCategory::Normal
        }
    }

    /// Decode the full IEEE-754 bit pattern `bits` (width `eb + sb`) into fields.
    #[must_use]
    fn from_bits(bits: &BigUint, eb: u32, sb: u32) -> Self {
        let sb1 = (sb - 1) as usize;
        let total_bits = u64::from(eb) + u64::from(sb);
        let sign = bits.bit(total_bits - 1);
        let exp_mask = (BigUint::from(1u8) << (eb as usize)) - BigUint::from(1u8);
        let sig_mask = (BigUint::from(1u8) << sb1) - BigUint::from(1u8);
        let shifted = bits.clone() >> sb1;
        let exp_field = &shifted & &exp_mask;
        let sig_field = bits & &sig_mask;
        let category = Self::category_from_fields(&exp_field, &sig_field, eb);
        Self {
            sign,
            exp_field,
            sig_field,
            eb,
            sb,
            category,
        }
    }

    /// Synthesize the canonical IEEE-754 fields for a nullary special-value app.
    #[must_use]
    fn special(name: &str, eb: u32, sb: u32) -> Option<Self> {
        let all_ones = (BigUint::from(1u8) << (eb as usize)) - BigUint::from(1u8);
        let zero = BigUint::from(0u8);
        let (sign, exp_field, sig_field, category) = match name {
            "+oo" => (false, all_ones, zero, FpCategory::Inf),
            "-oo" => (true, all_ones, zero, FpCategory::Inf),
            "+zero" => (false, zero.clone(), zero, FpCategory::Zero),
            "-zero" => (true, zero.clone(), zero, FpCategory::Zero),
            "NaN" => {
                // Canonical quiet NaN: MSB of the trailing-significand field set.
                // (Never actually read — the FFI value accessors decline NaN — so
                // the exact payload only needs to be nonzero for the category.)
                let sig = if sb >= 2 {
                    BigUint::from(1u8) << ((sb - 2) as usize)
                } else {
                    BigUint::from(1u8)
                };
                (false, all_ones, sig, FpCategory::NaN)
            }
            _ => return None,
        };
        Some(Self {
            sign,
            exp_field,
            sig_field,
            eb,
            sb,
            category,
        })
    }
}

impl Solver {
    /// Decode `t` into its IEEE-754 [`FpNumeral`] fields, or `None` if `t` is not
    /// a concrete FP numeral (i.e. it is symbolic, or not FP-sorted).
    ///
    /// Recognizes the three canonical AY FP-numeral term shapes documented at the
    /// module level. Returns `None` for any FP term whose components are not
    /// concrete `Const`s, so a symbolic FP term is never mistaken for a value.
    ///
    /// This backs `Z3_fpa_is_numeral` (`= decode(t).is_some()`) and every
    /// `Z3_fpa_get_numeral_*` / `Z3_fpa_is_numeral_*` accessor.
    #[must_use]
    pub fn fp_numeral_decode(&self, t: Term) -> Option<FpNumeral> {
        let t_id = self.resolve_term("fp_numeral_decode", t).ok()?;
        let (eb, sb) = match self.terms().sort(t_id).clone() {
            Sort::FloatingPoint(eb, sb) => (eb, sb),
            _ => return None,
        };
        // Degenerate widths cannot form an IEEE encoding; decline rather than
        // underflow `sb - 1` / `eb` shifts.
        if eb == 0 || sb == 0 {
            return None;
        }
        // Clone the node so the immutable borrow of the term store is released
        // before the per-child `Const` lookups below.
        let node = self.terms().get(t_id).clone();
        match node {
            // (a) nullary special-value app: (_ +oo eb sb), (_ NaN eb sb), ...
            TermData::App(Symbol::Indexed(name, _indices), args) if args.is_empty() => {
                FpNumeral::special(&name, eb, sb)
            }
            // (b) 1-arg reinterpret: ((_ to_fp eb sb) bv-const)
            TermData::App(Symbol::Indexed(name, _indices), args)
                if name == "to_fp" && args.len() == 1 =>
            {
                let (bits, width) = self.fp_bv_const_value(args[0])?;
                let total = eb.checked_add(sb)?;
                if width != total {
                    return None;
                }
                Some(FpNumeral::from_bits(&bits, eb, sb))
            }
            // (c) 3-arg component form: (fp sgn-const exp-const sig-const)
            TermData::App(Symbol::Named(name), args) if name == "fp" && args.len() == 3 => {
                let (sign_v, sign_w) = self.fp_bv_const_value(args[0])?;
                let (exp_v, exp_w) = self.fp_bv_const_value(args[1])?;
                let (sig_v, sig_w) = self.fp_bv_const_value(args[2])?;
                if sign_w != 1 || exp_w != eb || sig_w != sb.checked_sub(1)? {
                    return None;
                }
                let sign = !sign_v.is_zero();
                let category = FpNumeral::category_from_fields(&exp_v, &sig_v, eb);
                Some(FpNumeral {
                    sign,
                    exp_field: exp_v,
                    sig_field: sig_v,
                    eb,
                    sb,
                    category,
                })
            }
            _ => None,
        }
    }

    /// Read a term's value as an unsigned BitVec constant `(value, width)`, or
    /// `None` if it is not a concrete BitVec `Const`.
    ///
    /// BitVec constants are stored normalized to a non-negative value in
    /// `[0, 2^width)` (see `TermStore::mk_bitvec`), so `to_biguint` never loses a
    /// sign.
    fn fp_bv_const_value(&self, id: TermId) -> Option<(BigUint, u32)> {
        match self.terms().get(id) {
            TermData::Const(Constant::BitVec { value, width, .. }) => {
                value.to_biguint().map(|v| (v, *width))
            }
            _ => None,
        }
    }

    /// Convert a Real to FP: `((_ to_fp eb sb) rm real)`.
    ///
    /// The exact Real analog of [`try_bv_to_fp`](Self::try_bv_to_fp) /
    /// [`try_fp_to_fp`](Self::try_fp_to_fp): validates `real` is Real-sorted and
    /// builds the well-typed indexed `to_fp` application. Construction is sound
    /// (the term is well-formed); the IEEE meaning (`round(real)` under `rm`) is
    /// the FP theory's. Because AY's FP solver bit-blasts, a symbolic Real
    /// operand may return `unknown` at solve time — orthogonal to sound
    /// construction, exactly as for existing `fp.to_real` terms.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `real` is not Real, or
    /// [`SolverError::InvalidArgument`] if `eb`/`sb` is zero or `eb + sb`
    /// overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_real_to_fp(
        &mut self,
        rm: Term,
        real: Term,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        let rm_id = self.resolve_term("to_fp (real)", rm)?;
        let real_id = self.resolve_term("to_fp (real)", real)?;
        self.expect_real("to_fp (real)", real)?;
        self.checked_fp_total_width("to_fp", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        let result = self.terms_mut().mk_app(
            Symbol::indexed("to_fp", vec![eb, sb]),
            vec![rm_id, real_id],
            sort,
        );
        Ok(self.wrap_term(result))
    }

    /// Convert an `(Int exponent, Real significand)` pair to FP:
    /// `((_ to_fp eb sb) rm exp sig)` — Z3's real+int `to_fp` form.
    ///
    /// The FP value is `round(sig * 2^exp)`. Validates `exp` is Int-sorted and
    /// `sig` is Real-sorted, then builds the three-operand indexed `to_fp`
    /// application. Same soundness/completeness characterization as
    /// [`try_real_to_fp`](Self::try_real_to_fp): construction is sound; the
    /// decision may be `unknown`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `exp` is not Int or `sig` is not
    /// Real, or [`SolverError::InvalidArgument`] if `eb`/`sb` is zero or
    /// `eb + sb` overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_int_real_to_fp(
        &mut self,
        rm: Term,
        exp: Term,
        sig: Term,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        let rm_id = self.resolve_term("to_fp (int real)", rm)?;
        let exp_id = self.resolve_term("to_fp (int real)", exp)?;
        let sig_id = self.resolve_term("to_fp (int real)", sig)?;
        self.expect_int("to_fp (exponent)", exp)?;
        self.expect_real("to_fp (significand)", sig)?;
        self.checked_fp_total_width("to_fp", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        let result = self.terms_mut().mk_app(
            Symbol::indexed("to_fp", vec![eb, sb]),
            vec![rm_id, exp_id, sig_id],
            sort,
        );
        Ok(self.wrap_term(result))
    }
}
