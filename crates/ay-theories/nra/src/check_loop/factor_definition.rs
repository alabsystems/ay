// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact definitions for compound linear terms used as monomial factors.

use super::*;

/// `floor(log2(|value|))` of a non-zero rational, from bit lengths plus one
/// shifted comparison.
fn floor_log2_abs(value: &BigRational) -> i64 {
    let numer = value.numer().magnitude();
    let denom = value.denom().magnitude();
    let e0 = numer.bits() as i64 - denom.bits() as i64;
    let below = if e0 >= 0 {
        numer < &(denom << (e0 as u64))
    } else {
        &(numer << ((-e0) as u64)) < denom
    };
    if below {
        e0 - 1
    } else {
        e0
    }
}

/// Whether `aux == coeff * product(values)`, decided exactly but without a
/// gcd reduction per multiply. Sign and magnitude screens reject most
/// mismatches from bit lengths alone; survivors compare cross-multiplied
/// numerator/denominator products, which agree with the reduced comparison
/// because rational equality is representation-independent. Forming the
/// reduced product instead spends nearly all of its time in binary gcd when
/// model values carry thousand-digit numerators (measured on `40f50`, where
/// this check was ~99% of solver samples inside `Ratio::reduce`).
pub(super) fn scaled_product_equals(
    aux: &BigRational,
    coeff: &BigRational,
    values: &[BigRational],
) -> bool {
    use num_bigint::Sign;
    use num_traits::Zero;
    if coeff.is_zero() || values.iter().any(|value| value.is_zero()) {
        return aux.is_zero();
    }
    if aux.is_zero() {
        return false;
    }
    let mut negative = coeff.numer().sign() == Sign::Minus;
    let mut log_sum = floor_log2_abs(coeff);
    for value in values {
        negative ^= value.numer().sign() == Sign::Minus;
        log_sum += floor_log2_abs(value);
    }
    if (aux.numer().sign() == Sign::Minus) != negative {
        return false;
    }
    let aux_log = floor_log2_abs(aux);
    let terms = values.len() as i64 + 1;
    if aux_log < log_sum || aux_log >= log_sum + terms {
        return false;
    }
    let mut numer = coeff.numer().clone();
    let mut denom = coeff.denom().clone();
    for value in values {
        numer *= value.numer();
        denom *= value.denom();
    }
    aux.numer() * &denom == &numer * aux.denom()
}

impl NraSolver<'_> {
    /// Check `aux == coeff * product(factors)` under a fully available model.
    /// Missing values are unavailable evidence and therefore inconsistent for
    /// every gate that could authorize a theory-level `Sat`.
    ///
    /// # Why the strong resolver and the strict residual belong together
    ///
    /// This is the only thing tying the LINEAR abstraction back to nonlinear
    /// reality on a `nra_check_loop` Sat exit: every product is a free opaque
    /// LRA column, and nothing else forces that column to equal what it denotes.
    /// So the predicate has two independent halves, and each was once wrong on
    /// its own:
    ///
    /// 1. HOW A FACTOR IS RESOLVED. Resolving with `var_value` alone answers
    ///    only for terms the tableau carries. MetiTarski emits Taylor
    ///    polynomials in HORNER form, so every product nests a compound `+` as
    ///    its last factor — a linear combination, not a column — and
    ///    `var_value` returns `None` for it. Measured on
    ///    `sqrt-1mcosq-7-chunk-0170`: ALL 30 monomials were unresolvable that
    ///    way. Factors therefore resolve through
    ///    [`NraSolver::monomial_factor_value`], which asks the tableau FIRST and
    ///    only then evaluates structurally. That order is load-bearing: a nested
    ///    product aux term must contribute the OPAQUE value the abstraction
    ///    assigned it, because recomputing it structurally would make the
    ///    monomial agree with itself and the check could never fail.
    ///
    /// 2. WHAT AN UNRESOLVABLE FACTOR MEANS. Fail-OPEN — treating "no value" as
    ///    "consistent" — lets an unchecked monomial authorize `Sat`, which is
    ///    exactly the vacuous-pass defect above. So the residual is fail-CLOSED.
    ///
    /// Fail-closing was previously argued to cost solves, and it did: on top of
    /// resolver (1)'s blind spot, nearly every Horner monomial fell into the
    /// residual, so closing it rejected models that were genuinely `Sat`. With
    /// the strong resolver in front, "unresolvable" is rare and means what it
    /// says — no evidence — and closing it is both sound and cheap. The two
    /// halves are only safe as a pair.
    ///
    /// The aux side stays on `var_value` deliberately: it is the opaque column
    /// under test, and must never be recomputed through the structural path.
    ///
    /// [`emit_factor_definitions`](Self::emit_factor_definitions) and
    /// [`has_undefined_compound_factors`](Self::has_undefined_compound_factors)
    /// remain the independent cross-check, so a compound factor must ALSO agree
    /// with its exact linear definition.
    pub(super) fn check_monomial_consistency(
        &self,
        monomial: &crate::monomial::Monomial,
        memo: &std::cell::RefCell<ValueMemo>,
    ) -> bool {
        let Some(aux) = self.memo_var_value(monomial.aux_var, memo) else {
            return false;
        };
        let mut values = Vec::with_capacity(monomial.vars.len());
        for &factor in &monomial.vars {
            let Some(value) = self.monomial_factor_value(factor, memo) else {
                return false;
            };
            values.push(value);
        }
        scaled_product_equals(&aux, &monomial.coeff, &values)
    }

    /// Check every exact nonlinear relation before authorizing `Sat`.
    /// One value memo serves the whole read-only pass, so the LRA
    /// materialisation δ is scanned at most once however many factor
    /// occurrences the pass evaluates.
    pub(crate) fn has_inconsistent_monomials(&self) -> bool {
        let memo = std::cell::RefCell::new(ValueMemo::default());
        self.products()
            .any(|monomial| !self.check_monomial_consistency(monomial, &memo))
            || self.has_undefined_compound_factors(&memo)
    }

    /// Expand a term as `sum(coeff_i * atom_i) + constant` within the same
    /// linear fragment accepted by LRA. Nonlinear or otherwise opaque children
    /// remain atoms; the resulting identity is still exact.
    pub(crate) fn linear_definition_of(
        &self,
        term: TermId,
        multiplier: &BigRational,
        depth: usize,
        atoms: &mut Vec<(TermId, BigRational)>,
        constant: &mut BigRational,
    ) -> bool {
        if depth > crate::LINEAR_DEFINITION_MAX_DEPTH {
            return false;
        }
        let Some(child_depth) = depth.checked_add(1) else {
            return false;
        };
        if let Some(value) = crate::constant_value_of(self.terms, term) {
            *constant += multiplier * value;
            return true;
        }
        match self.terms.get(term) {
            TermData::App(ay_core::term::Symbol::Named(name), args) => match name.as_str() {
                "+" => args.iter().all(|&arg| {
                    self.linear_definition_of(arg, multiplier, child_depth, atoms, constant)
                }),
                "-" if args.len() == 1 => {
                    let negated = -multiplier.clone();
                    self.linear_definition_of(args[0], &negated, child_depth, atoms, constant)
                }
                "-" if args.len() >= 2 => {
                    if !self.linear_definition_of(args[0], multiplier, child_depth, atoms, constant)
                    {
                        return false;
                    }
                    let negated = -multiplier.clone();
                    args[1..].iter().all(|&arg| {
                        self.linear_definition_of(arg, &negated, child_depth, atoms, constant)
                    })
                }
                "*" => {
                    let mut scale = BigRational::one();
                    let mut symbolic = None;
                    for &arg in args {
                        match crate::constant_value_of(self.terms, arg) {
                            Some(value) => scale *= value,
                            None if symbolic.is_none() => symbolic = Some(arg),
                            None => {
                                atoms.push((term, multiplier.clone()));
                                return true;
                            }
                        }
                    }
                    let scaled = multiplier * scale;
                    if let Some(inner) = symbolic {
                        self.linear_definition_of(inner, &scaled, child_depth, atoms, constant)
                    } else {
                        *constant += scaled;
                        true
                    }
                }
                "/" if args.len() == 2 => {
                    if let Some(divisor) = crate::constant_value_of(self.terms, args[1]) {
                        if !divisor.is_zero() {
                            let scaled = multiplier / divisor;
                            return self.linear_definition_of(
                                args[0],
                                &scaled,
                                child_depth,
                                atoms,
                                constant,
                            );
                        }
                    }
                    atoms.push((term, multiplier.clone()));
                    true
                }
                _ => {
                    atoms.push((term, multiplier.clone()));
                    true
                }
            },
            _ => {
                atoms.push((term, multiplier.clone()));
                true
            }
        }
    }

    /// Whether a compound factor is absent from the candidate model, cannot be
    /// expanded within the bounded exact fragment, or disagrees with its exact
    /// linear definition. Every uncertainty blocks a theory-level `Sat`.
    pub(crate) fn has_undefined_compound_factors(
        &self,
        memo: &std::cell::RefCell<ValueMemo>,
    ) -> bool {
        for &factor in &self.compound_factors {
            let Some(factor_value) = self.memo_var_value(factor, memo) else {
                return true;
            };
            let mut atoms = Vec::new();
            let mut constant = BigRational::zero();
            if !self.linear_definition_of(factor, &BigRational::one(), 0, &mut atoms, &mut constant)
            {
                return true;
            }
            let mut total = constant;
            for (atom, coefficient) in atoms {
                let Some(value) = self.memo_var_value(atom, memo) else {
                    return true;
                };
                total += coefficient * value;
            }
            if total != factor_value {
                return true;
            }
        }
        false
    }

    /// Emit every compound factor's exact two-sided linear definition.
    pub(crate) fn emit_factor_definitions(&mut self) -> usize {
        use ay_lra::GomoryCut;

        let factors = std::mem::take(&mut self.compound_factors);
        let mut added: usize = 0;
        for &factor in &factors {
            if self.compound_defs_emitted.contains(&factor) {
                continue;
            }
            let mut atoms = Vec::new();
            let mut constant = BigRational::zero();
            if !self.linear_definition_of(factor, &BigRational::one(), 0, &mut atoms, &mut constant)
            {
                continue;
            }
            if atoms.len() == 1 && atoms[0].0 == factor {
                continue;
            }
            let factor_var = self.lra.ensure_var_registered(factor);
            let mut coefficients = vec![(factor_var, BigRational::one())];
            for (atom, coefficient) in atoms {
                let atom_var = self.lra.ensure_var_registered(atom);
                coefficients.push((atom_var, -coefficient));
            }
            for is_lower in [true, false] {
                self.lra.add_gomory_cut(
                    &GomoryCut {
                        coeffs: coefficients.clone(),
                        bound: constant.clone(),
                        is_lower,
                        reasons: Vec::new(),
                        source_term: None,
                    },
                    factor,
                );
            }
            added = added.saturating_add(2);
            self.compound_defs_emitted.insert(factor);
        }
        self.compound_factors = factors;
        added
    }
}

#[cfg(test)]
mod product_eq_tests {
    use super::scaled_product_equals;
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use num_traits::One;

    fn q(n: i64, d: i64) -> BigRational {
        BigRational::new(n.into(), d.into())
    }

    fn naive(aux: &BigRational, coeff: &BigRational, values: &[BigRational]) -> bool {
        let mut product = coeff.clone();
        for value in values {
            product *= value;
        }
        *aux == product
    }

    #[test]
    fn scaled_product_equals_matches_naive_reduced_product() {
        let cases: Vec<(BigRational, BigRational, Vec<BigRational>)> = vec![
            (q(6, 1), q(1, 1), vec![q(2, 1), q(3, 1)]),
            (q(7, 1), q(1, 1), vec![q(2, 1), q(3, 1)]),
            (q(-6, 1), q(1, 1), vec![q(2, 1), q(3, 1)]),
            (q(0, 1), q(5, 1), vec![q(0, 1), q(9, 1)]),
            (q(1, 1), q(5, 1), vec![q(0, 1), q(9, 1)]),
            (q(0, 1), q(5, 1), vec![q(2, 1), q(9, 1)]),
            (q(3, 2), q(3, 1), vec![q(1, 2)]),
            (q(1, 1), q(1, 1), vec![]),
            (q(2, 1), q(1, 1), vec![]),
            (q(-4, 1), q(-2, 1), vec![q(2, 1)]),
            (q(1, 8), q(1, 1), vec![q(1, 2), q(1, 4)]),
            (q(1_000_000, 1), q(1, 1), vec![q(1, 2), q(1, 4)]),
            (q(5, 3), q(0, 1), vec![q(7, 1)]),
            (q(0, 1), q(0, 1), vec![q(7, 1)]),
        ];
        for (aux, coeff, values) in &cases {
            assert_eq!(
                scaled_product_equals(aux, coeff, values),
                naive(aux, coeff, values),
                "aux={aux} coeff={coeff} values={values:?}"
            );
        }
    }

    #[test]
    fn scaled_product_equals_handles_huge_cancelling_operands() {
        // (2^4000 / 3^700) * (3^700 / 2^4000) == 1, with operands far larger
        // than any single gcd a per-multiply reduction would want to run.
        let mut pow3 = BigInt::from(1);
        for _ in 0..700 {
            pow3 *= 3;
        }
        let pow2 = BigInt::from(1i64) << 4000u32;
        let a = BigRational::new(pow2.clone(), pow3.clone());
        let b = BigRational::new(pow3, pow2);
        let one = BigRational::one();
        assert!(scaled_product_equals(&one, &one, &[a.clone(), b.clone()]));
        assert!(!scaled_product_equals(&q(3, 1), &one, &[a, b]));
    }
}
