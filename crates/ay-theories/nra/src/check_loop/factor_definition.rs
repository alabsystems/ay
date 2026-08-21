// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact definitions for compound linear terms used as monomial factors.

use super::*;

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
    pub(super) fn check_monomial_consistency(&self, monomial: &crate::monomial::Monomial) -> bool {
        let mut product = BigRational::one();
        for &factor in &monomial.vars {
            let Some(value) = self.monomial_factor_value(factor) else {
                return false;
            };
            product *= value;
        }
        self.var_value(monomial.aux_var)
            .is_some_and(|value| value == monomial.aux_from_product(&product))
    }

    /// Check every exact nonlinear relation before authorizing `Sat`.
    pub(crate) fn has_inconsistent_monomials(&self) -> bool {
        self.products()
            .any(|monomial| !self.check_monomial_consistency(monomial))
            || self.has_undefined_compound_factors()
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
        if let Some(value) = crate::constant_value_of(self.terms, term) {
            *constant += multiplier * value;
            return true;
        }
        match self.terms.get(term) {
            TermData::App(ay_core::term::Symbol::Named(name), args) => match name.as_str() {
                "+" => args.iter().all(|&arg| {
                    self.linear_definition_of(arg, multiplier, depth + 1, atoms, constant)
                }),
                "-" if args.len() == 1 => {
                    let negated = -multiplier.clone();
                    self.linear_definition_of(args[0], &negated, depth + 1, atoms, constant)
                }
                "-" if args.len() >= 2 => {
                    if !self.linear_definition_of(args[0], multiplier, depth + 1, atoms, constant) {
                        return false;
                    }
                    let negated = -multiplier.clone();
                    args[1..].iter().all(|&arg| {
                        self.linear_definition_of(arg, &negated, depth + 1, atoms, constant)
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
                        self.linear_definition_of(inner, &scaled, depth + 1, atoms, constant)
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
                                depth + 1,
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
    pub(crate) fn has_undefined_compound_factors(&self) -> bool {
        for &factor in &self.compound_factors {
            let Some(factor_value) = self.var_value(factor) else {
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
                let Some(value) = self.var_value(atom) else {
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
        let mut added = 0;
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
            added += 2;
            self.compound_defs_emitted.insert(factor);
        }
        self.compound_factors = factors;
        added
    }
}
