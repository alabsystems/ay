// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Local validity tests for the div/mod purification recognizer.
//!
//! Only the LOCAL half lives here: is the atom valid once `q := D` and
//! `r := M`? Freshness, one definiens per symbol and independence are
//! whole-proof properties tested through `ay-proof`'s `FreshDefRegistry`.
//!
//! Every rejected atom names the dividend at which it is FALSE under the SMT-LIB
//! definition, so a future loosening cannot be argued to be harmless.

use num_bigint::BigInt;

use super::divmod_def::{recognize_divmod_def, DivModDefShapeError};
use crate::{Sort, TermId, TermStore};

struct Fx {
    terms: TermStore,
    x: TermId,
    q: TermId,
    r: TermId,
}

fn fx() -> Fx {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x".to_string(), Sort::Int);
    let q = terms.mk_var("_divmod_q_1".to_string(), Sort::Int);
    let r = terms.mk_var("_divmod_r_2".to_string(), Sort::Int);
    Fx { terms, x, q, r }
}

impl Fx {
    fn int(&mut self, value: i64) -> TermId {
        self.terms.mk_int(BigInt::from(value))
    }

    /// The `(q D r M)` arguments for `(div dividend k)` / `(mod dividend k)`,
    /// built with the FOLDING constructors `mk_intdiv`/`mk_mod`. For a
    /// symbolic dividend that is the very term the executor lane builds; for a
    /// literal dividend (folded to the Euclidean literals) it is checker-only
    /// coverage, since the lane never folds (see [`Self::raw_args`]).
    fn args(&mut self, dividend: TermId, k: i64) -> Vec<TermId> {
        let k = self.int(k);
        let d = self.terms.mk_intdiv(dividend, k);
        let m = self.terms.mk_mod(dividend, k);
        vec![self.q, d, self.r, m]
    }

    /// The `(q D r M)` arguments exactly as the executor lane builds them: RAW
    /// `div`/`mod` applications (`mk_app`), never folded.
    fn raw_args(&mut self, dividend: TermId, k: i64) -> Vec<TermId> {
        let k = self.int(k);
        let operands = [dividend, k];
        let d = self
            .terms
            .mk_app(crate::term::Symbol::named("div"), operands, Sort::Int);
        let m = self
            .terms
            .mk_app(crate::term::Symbol::named("mod"), operands, Sort::Int);
        vec![self.q, d, self.r, m]
    }

    /// `dividend = k*q + r`, built as `mod_div_elim` builds it.
    fn equation(&mut self, dividend: TermId, k: i64) -> TermId {
        let k = self.int(k);
        let kq = self.terms.mk_mul(vec![k, self.q]);
        let sum = self.terms.mk_add(vec![kq, self.r]);
        self.terms.mk_eq(dividend, sum)
    }

    fn lower(&mut self) -> TermId {
        let zero = self.int(0);
        self.terms.mk_ge(self.r, zero)
    }

    fn upper(&mut self, bound: i64) -> TermId {
        let bound = self.int(bound);
        self.terms.mk_lt(self.r, bound)
    }

    fn check(&self, atom: TermId, args: &[TermId]) -> Result<(), DivModDefShapeError> {
        recognize_divmod_def(&self.terms, &[atom], 0, args).map(|_| ())
    }
}

#[test]
fn accepts_the_three_atoms_of_a_symbolic_purification() {
    let mut f = fx();
    let args = f.args(f.x, 2);
    let atoms = [f.equation(f.x, 2), f.lower(), f.upper(2)];
    for atom in atoms {
        f.check(atom, &args)
            .unwrap_or_else(|e| panic!("{atom:?} is the SMT-LIB definition: {e}"));
    }
}

#[test]
fn accepts_a_negative_divisor_and_a_compound_dividend() {
    // `(div (+ x 1) (- 3))`: the remainder still ranges over `[0, |k| - 1]`.
    let mut f = fx();
    let one = f.int(1);
    let dividend = f.terms.mk_add(vec![f.x, one]);
    let args = f.args(dividend, -3);
    let atoms = [f.equation(dividend, -3), f.lower(), f.upper(3)];
    for atom in atoms {
        f.check(atom, &args)
            .unwrap_or_else(|e| panic!("{atom:?} holds for a negative divisor: {e}"));
    }
}

#[test]
fn accepts_a_literal_dividend_through_the_folded_definientia() {
    // `mk_intdiv(-7, 2)` folds to `-4` and `mk_mod(-7, 2)` to `1`, so the
    // substituted atoms are closed arithmetic: `-7 = 2*(-4) + 1`, `0 <= 1 < 2`.
    let mut f = fx();
    for dividend in [-7, -1, 0, 1, 7, 200] {
        let x = f.int(dividend);
        let args = f.args(x, 2);
        let atoms = [f.equation(x, 2), f.lower(), f.upper(2)];
        for atom in atoms {
            f.check(atom, &args)
                .unwrap_or_else(|e| panic!("dividend {dividend}: {atom:?}: {e}"));
        }
    }
}

#[test]
fn reads_the_raw_definientia_the_lane_builds() {
    // The lane's `(div 7 2)` / `(mod 7 2)` stay opaque applications: the
    // triple is accepted through the SMT-LIB definition, and `r < 1` is still
    // refused (FALSE: `(mod 7 2) = 1`), now at the remainder's range end.
    let mut f = fx();
    for dividend in [-7, 0, 7] {
        let x = f.int(dividend);
        let args = f.raw_args(x, 2);
        let atoms = [f.equation(x, 2), f.lower(), f.upper(2)];
        for atom in atoms {
            f.check(atom, &args)
                .unwrap_or_else(|e| panic!("dividend {dividend}: {atom:?}: {e}"));
        }
    }
    let seven = f.int(7);
    let args = f.raw_args(seven, 2);
    let wrong = f.upper(1);
    assert_eq!(f.check(wrong, &args), Err(DivModDefShapeError::NotValid));
    let args = f.raw_args(f.x, -3);
    let atoms = [f.equation(f.x, -3), f.lower(), f.upper(3)];
    for atom in atoms {
        f.check(atom, &args)
            .unwrap_or_else(|e| panic!("{atom:?} holds for a negative divisor: {e}"));
    }
}

#[test]
fn accepts_a_weaker_but_still_valid_bound() {
    // `r <= 5` is implied by `r <= 1`; validity, not syntax, is the criterion.
    let mut f = fx();
    let args = f.args(f.x, 2);
    let five = f.int(5);
    let weaker = f.terms.mk_le(f.r, five);
    f.check(weaker, &args)
        .expect("a valid consequence of the range");
}

#[test]
fn rejects_an_upper_bound_that_excludes_an_attainable_remainder() {
    // NEGATIVE TWIN. `r < 1` with `k = 2`: FALSE at `x = 1`, where
    // `(mod 1 2) = 1`.
    let mut f = fx();
    let args = f.args(f.x, 2);
    let wrong = f.upper(1);
    assert_eq!(f.check(wrong, &args), Err(DivModDefShapeError::NotValid));
}

#[test]
fn rejects_a_lower_bound_that_excludes_zero() {
    // `1 <= r`: FALSE at `x = 0`, where `(mod 0 2) = 0`.
    let mut f = fx();
    let args = f.args(f.x, 2);
    let one = f.int(1);
    let wrong = f.terms.mk_le(one, f.r);
    assert_eq!(f.check(wrong, &args), Err(DivModDefShapeError::NotValid));
}

#[test]
fn rejects_an_equation_with_the_wrong_multiplier() {
    // `x = 3*q + r` against `q := (div x 2)`: FALSE at `x = 2` (`2 != 3*1+0`).
    let mut f = fx();
    let args = f.args(f.x, 2);
    let wrong = f.equation(f.x, 3);
    assert_eq!(f.check(wrong, &args), Err(DivModDefShapeError::NotValid));
}

#[test]
fn rejects_definientia_over_different_dividends() {
    // `q := (div x 2)` with `r := (mod y 2)`: `x = 2*q + r` is FALSE at
    // `x = 1, y = 0` (`1 != 2*0 + 0`).
    let mut f = fx();
    let y = f.terms.mk_var("y".to_string(), Sort::Int);
    let two = f.int(2);
    let d = f.terms.mk_intdiv(f.x, two);
    let m = f.terms.mk_mod(y, two);
    let args = vec![f.q, d, f.r, m];
    let equation = f.equation(f.x, 2);
    assert_eq!(f.check(equation, &args), Err(DivModDefShapeError::NotValid));
    let lower = f.lower();
    assert_eq!(f.check(lower, &args), Err(DivModDefShapeError::NotValid));
}

#[test]
fn rejects_a_range_claim_about_the_quotient() {
    // `0 <= q`: FALSE at `x = -1`, where `(div -1 2) = -1`.
    let mut f = fx();
    let args = f.args(f.x, 2);
    let zero = f.int(0);
    let wrong = f.terms.mk_le(zero, f.q);
    assert_eq!(f.check(wrong, &args), Err(DivModDefShapeError::NotValid));
}

#[test]
fn rejects_a_wrong_literal_definiens() {
    // `q := 4` for the dividend `7`: `7 = 2*4 + 1` is false.
    let mut f = fx();
    let seven = f.int(7);
    let four = f.int(4);
    let one = f.int(1);
    let args = vec![f.q, four, f.r, one];
    let equation = f.equation(seven, 2);
    assert_eq!(f.check(equation, &args), Err(DivModDefShapeError::NotValid));
}

#[test]
fn rejects_a_zero_or_symbolic_divisor() {
    // `(mod x 0)` is UNCONSTRAINED in SMT-LIB, so `0 <= r` is FALSE for a
    // model choosing `(mod 5 0) = -1`; a symbolic divisor has no range at all.
    let mut f = fx();
    let zero = f.int(0);
    let d = f.terms.mk_intdiv(f.x, zero);
    let m = f.terms.mk_mod(f.x, zero);
    let lower = f.lower();
    assert_eq!(
        f.check(lower, &[f.q, d, f.r, m]),
        Err(DivModDefShapeError::NotValid)
    );
    let y = f.terms.mk_var("y".to_string(), Sort::Int);
    let d = f.terms.mk_intdiv(f.x, y);
    let m = f.terms.mk_mod(f.x, y);
    assert_eq!(
        f.check(lower, &[f.q, d, f.r, m]),
        Err(DivModDefShapeError::NotValid)
    );
}

#[test]
fn rejects_malformed_steps() {
    let mut f = fx();
    let args = f.args(f.x, 2);
    let atom = f.lower();
    assert_eq!(
        recognize_divmod_def(&f.terms, &[atom], 1, &args).map(|_| ()),
        Err(DivModDefShapeError::HasPremises)
    );
    assert_eq!(
        recognize_divmod_def(&f.terms, &[atom], 0, &args[..3]).map(|_| ()),
        Err(DivModDefShapeError::ArgArity(3))
    );
    assert_eq!(
        recognize_divmod_def(&f.terms, &[atom, atom], 0, &args).map(|_| ()),
        Err(DivModDefShapeError::ClauseArity(2))
    );
    let same = vec![f.r, args[1], f.r, args[3]];
    assert_eq!(
        f.check(atom, &same),
        Err(DivModDefShapeError::NotTwoIntSymbols)
    );
    let one = f.int(1);
    let compound = f.terms.mk_add(vec![f.q, one]);
    let not_symbol = vec![compound, args[1], f.r, args[3]];
    assert_eq!(
        f.check(atom, &not_symbol),
        Err(DivModDefShapeError::NotTwoIntSymbols)
    );
    let zero = f.int(0);
    let unrelated = f.terms.mk_le(zero, f.x);
    assert_eq!(
        f.check(unrelated, &args),
        Err(DivModDefShapeError::MentionsNeitherSymbol)
    );
}

// ---- Reviewer witnesses: each pins a guard no test above exercises. ----

fn raw(terms: &mut TermStore, op: &str, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(crate::term::Symbol::named(op), [lhs, rhs], Sort::Bool)
}

#[test]
fn rejects_the_euclidean_reading_of_a_zero_divisor() {
    // `(mod x 0)` is unconstrained: `x = 0*q + r` (i.e. `x = r`) and `r <= 0`
    // are both FALSE in a model choosing `(mod 3 0) = 5`.
    let mut f = fx();
    let (x, q, r) = (f.x, f.q, f.r);
    let zero = f.int(0);
    let d = f.terms.mk_intdiv(x, zero);
    let m = f.terms.mk_mod(x, zero);
    let args = [q, d, r, m];
    let x_is_r = raw(&mut f.terms, "=", x, r);
    assert_eq!(f.check(x_is_r, &args), Err(DivModDefShapeError::NotValid));
    let r_le_0 = raw(&mut f.terms, "<=", r, zero);
    assert_eq!(f.check(r_le_0, &args), Err(DivModDefShapeError::NotValid));
}

#[test]
fn reads_the_greater_than_heads_with_their_own_strictness_and_orientation() {
    // `(> r 0)` is FALSE at `x = 0`; `(>= 0 r)` is FALSE at `x = 1`. Both
    // heads survive raw construction (`mk_gt`/`mk_ge` would normalize them).
    let mut f = fx();
    let (x, r) = (f.x, f.r);
    let args = f.args(x, 2);
    let zero = f.int(0);
    let two = f.int(2);
    let gt = raw(&mut f.terms, ">", r, zero);
    assert_eq!(f.check(gt, &args), Err(DivModDefShapeError::NotValid));
    let ge = raw(&mut f.terms, ">=", zero, r);
    assert_eq!(f.check(ge, &args), Err(DivModDefShapeError::NotValid));
    let ge_ok = raw(&mut f.terms, ">=", r, zero);
    f.check(ge_ok, &args).expect("`r >= 0` is the range");
    let gt_ok = raw(&mut f.terms, ">", two, r);
    f.check(gt_ok, &args).expect("`2 > r` is the range");
}

#[test]
fn rejects_a_false_closed_comparison_after_substitution() {
    // Folded literal definientia for dividend 7, k = 2: `r := 1`, so `r < 1`
    // is the closed FALSE `1 < 1`.
    let mut f = fx();
    let seven = f.int(7);
    let args = f.args(seven, 2);
    let wrong = f.upper(1);
    assert_eq!(f.check(wrong, &args), Err(DivModDefShapeError::NotValid));
}

#[test]
fn rejects_a_definiens_of_another_sort() {
    // `q := 1/2` (Real) would make `2*q = 1` an "identity" for an Int `q`.
    let mut f = fx();
    let (x, q, r) = (f.x, f.q, f.r);
    let half = f.terms.mk_rational(num_rational::BigRational::new(
        BigInt::from(1),
        BigInt::from(2),
    ));
    let two = f.int(2);
    let one = f.int(1);
    let m = f.terms.mk_mod(x, two);
    let scaled = f.terms.mk_mul(vec![two, q]);
    let atom = raw(&mut f.terms, "=", scaled, one);
    assert_eq!(
        f.check(atom, &[q, half, r, m]),
        Err(DivModDefShapeError::DefiniensSort)
    );
}
