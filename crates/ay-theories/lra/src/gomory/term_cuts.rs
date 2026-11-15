// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gomory cuts in TERM space, for a caller that adds each cut to its search
//! as a guarded lemma over a new atom (the CDCL(T) kernel, `ay-cdclt`,
//! design §3.5) instead of as an internal, scope-bound tableau row.
//!
//! A guarded cut `¬r₁ ∨ … ∨ ¬rₖ ∨ (Σ aᵢ·tᵢ ≥ b)` outlives the scope it was
//! derived in, so its guard must be the COMPLETE justification of every bound
//! the cut used. That is why this entry takes the reasons from
//! [`crate::Bound::complete_reason_pairs`] (the provenance chain), refuses a
//! cut that leans on a bound with a sentinel (reasonless) premise, and
//! refuses one whose columns cannot all be written over terms.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::Sort;

use super::*;

/// `Σ coeff·term ≥ bound` over Int terms with integer coefficients, valid in
/// every integer model of `reasons`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TermCut {
    /// Integer coefficients over arithmetic terms (no zeros, no repeats).
    pub coeffs: Vec<(TermId, BigInt)>,
    /// The right-hand side.
    pub bound: BigInt,
    /// The asserted literals that justify the cut, completely.
    pub reasons: Vec<(TermId, bool)>,
}

impl LraSolver {
    /// Up to `max` Gomory mixed-integer cuts of the current (feasible) LP
    /// vertex, in term space (see the module docs). Integer mode only; every
    /// term of Int sort is an integer column.
    pub fn gomory_term_cuts(&mut self, max: usize) -> Vec<TermCut> {
        let int_terms: HashSet<TermId> = self
            .var_to_term
            .values()
            .copied()
            .filter(|&t| *self.terms().sort(t) == Sort::Int)
            .collect();
        let int_var_ids: HashSet<u32> = int_terms
            .iter()
            .filter_map(|t| self.term_to_var.get(t).copied())
            .collect();
        let mut candidates: Vec<(BigRational, usize)> = Vec::new();
        for (row_idx, row) in self.rows.iter().enumerate() {
            let basic = row.basic_var;
            if !self.is_integer_var(basic, &int_terms, &int_var_ids) {
                continue;
            }
            let value = self.vars[basic as usize].value.rational();
            if value.is_integer()
                || !self.is_gomory_cut_target(row, basic, &int_terms, &int_var_ids)
            {
                continue;
            }
            candidates.push((Self::gomory_score(&value), row_idx));
        }
        candidates.sort();
        let slack_defs: HashMap<u32, (Vec<(u32, Rational)>, Rational)> = self
            .expr_to_slack
            .iter()
            .map(|(key, (slack, constant))| (*slack, (key.clone(), constant.clone())))
            .collect();
        let mut cuts = Vec::new();
        for (_, row_idx) in candidates {
            if cuts.len() >= max {
                break;
            }
            let row = &self.rows[row_idx];
            let basic = row.basic_var;
            let value = self.vars[basic as usize].value.rational();
            let Some(cut) =
                self.build_gomory_cut(row, basic, &value, &int_terms, &int_var_ids, false)
            else {
                continue;
            };
            if !cut.is_small() || !self.current_solution_violates_cut(&cut) {
                continue;
            }
            let Some(reasons) = self.complete_row_reasons(row, basic) else {
                continue;
            };
            if let Some(term_cut) = self.cut_over_terms(&cut, reasons, &slack_defs) {
                cuts.push(term_cut);
            }
        }
        cuts
    }

    /// Complete reasons of every bound a non-basic column of `row` sits at,
    /// or `None` when one of them has a sentinel premise.
    fn complete_row_reasons(&self, row: &TableauRow, basic: u32) -> Option<Vec<(TermId, bool)>> {
        let mut reasons: Vec<(TermId, bool)> = Vec::new();
        for (var, _) in &row.coeffs {
            if *var == basic {
                continue;
            }
            let info = &self.vars[*var as usize];
            for (at, bound) in [
                (Self::is_at_lower_bound(info), info.lower.as_ref()),
                (Self::is_at_upper_bound(info), info.upper.as_ref()),
            ] {
                let (true, Some(bound)) = (at, bound) else {
                    continue;
                };
                if bound.reasons.iter().any(|r| r.is_sentinel()) {
                    return None;
                }
                let pairs = bound.complete_reason_pairs();
                if pairs.is_empty() {
                    return None;
                }
                for pair in pairs {
                    if !reasons.contains(&pair) {
                        reasons.push(pair);
                    }
                }
            }
        }
        Some(reasons)
    }

    /// Rewrite a cut over tableau columns as `Σ aᵢ·tᵢ ≥ b` over Int terms
    /// with integer coefficients (scaled, right-hand side rounded up), or
    /// `None` when a column is neither a term nor a registered slack
    /// expression, or a term is not Int.
    fn cut_over_terms(
        &self,
        cut: &GomoryCut,
        reasons: Vec<(TermId, bool)>,
        slack_defs: &HashMap<u32, (Vec<(u32, Rational)>, Rational)>,
    ) -> Option<TermCut> {
        let mut coeffs: Vec<(TermId, BigRational)> = Vec::new();
        let mut rhs = cut.bound.clone();
        let mut add =
            |term: TermId, c: BigRational| match coeffs.iter_mut().find(|(t, _)| *t == term) {
                Some((_, slot)) => *slot += c,
                None => coeffs.push((term, c)),
            };
        for (var, g) in &cut.coeffs {
            if let Some(&term) = self.var_to_term.get(var) {
                add(term, g.clone());
                continue;
            }
            // A slack column: `s = Σ cᵢ·xᵢ + k` over term columns.
            let (expr, constant) = slack_defs.get(var)?;
            for (x, c) in expr {
                let term = *self.var_to_term.get(x)?;
                add(term, g * c.to_big());
            }
            rhs -= g * constant.to_big();
        }
        coeffs.retain(|(_, c)| !c.is_zero());
        if coeffs.is_empty()
            || coeffs
                .iter()
                .any(|(t, _)| *self.terms().sort(*t) != Sort::Int)
        {
            return None;
        }
        let lcm = coeffs.iter().fold(BigInt::one(), |acc, (_, c)| {
            num_integer::Integer::lcm(&acc, c.denom())
        });
        let scale = BigRational::from_integer(lcm);
        let coeffs: Vec<(TermId, BigInt)> = coeffs
            .into_iter()
            .map(|(t, c)| (t, (c * &scale).to_integer()))
            .collect();
        let bound = (rhs * &scale).ceil().to_integer();
        Some(TermCut {
            coeffs,
            bound,
            reasons,
        })
    }
}

impl LraSolver {
    /// The tableau GCD test (z3's `int_gcd_test`) over the current vertex:
    /// a row `b = Σ aⱼ·vⱼ + c` whose basic column is an Int term with a
    /// fractional value, whose non-fixed columns are all Int terms, and
    /// whose fixed columns fold into the constant, has no integer solution
    /// when the gcd of its scaled non-fixed coefficients (the basic column's
    /// included) does not divide the scaled constant. Returns the COMPLETE
    /// reasons of the fixed columns' bounds — the row itself is an identity
    /// of the slack definitions — or `None` when no row refutes.
    pub fn gcd_test_term_conflict(&self) -> Option<Vec<(TermId, bool)>> {
        let is_int_term = |var: u32| {
            self.var_to_term
                .get(&var)
                .is_some_and(|&t| *self.terms().sort(t) == Sort::Int)
        };
        'rows: for row in &self.rows {
            let basic = row.basic_var;
            if !is_int_term(basic) || self.vars[basic as usize].value.rational().is_integer() {
                continue;
            }
            let lcm = row
                .coeffs
                .iter()
                .map(|(_, c)| c.to_big())
                .chain(std::iter::once(row.constant.to_big()))
                .fold(BigInt::one(), |acc, c| {
                    num_integer::Integer::lcm(&acc, c.denom())
                });
            let scale = BigRational::from_integer(lcm.clone());
            let mut gcd = lcm;
            let mut rhs = row.constant.to_big() * &scale;
            let mut reasons: Vec<(TermId, bool)> = Vec::new();
            for (var, coeff) in &row.coeffs {
                if *var == basic {
                    continue;
                }
                let scaled = coeff.to_big() * &scale;
                let info = &self.vars[*var as usize];
                if let (Some(lo), Some(hi)) = (info.lower.as_ref(), info.upper.as_ref()) {
                    if lo.value == hi.value && !lo.strict && !hi.strict {
                        for bound in [lo, hi] {
                            if bound.reasons.iter().any(|r| r.is_sentinel()) {
                                continue 'rows;
                            }
                            let pairs = bound.complete_reason_pairs();
                            if pairs.is_empty() {
                                continue 'rows;
                            }
                            for pair in pairs {
                                if !reasons.contains(&pair) {
                                    reasons.push(pair);
                                }
                            }
                        }
                        rhs += scaled * lo.value.to_big();
                        continue;
                    }
                }
                if !is_int_term(*var) {
                    continue 'rows;
                }
                gcd = num_integer::Integer::gcd(&gcd, &scaled.to_integer());
            }
            // `scale·b − Σ scaled·vⱼ = rhs` over the non-fixed Int columns.
            if gcd.is_zero() {
                continue;
            }
            let quotient = rhs / BigRational::from_integer(gcd);
            if !quotient.is_integer() && !reasons.is_empty() {
                return Some(reasons);
            }
        }
        None
    }
}
