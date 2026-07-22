// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Joint case-split setup for composed Diophantine substitutions.

use super::*;

const SMALL_RANGE_LIMIT: usize = 3;
const MAX_ASSIGNMENTS: usize = 64;

pub(crate) type JointCaseSplitBoundPair = (Option<BigInt>, Option<BigInt>);

#[derive(Clone, Debug)]
pub(crate) struct JointCaseSplitExpr {
    pub(crate) term_id: TermId,
    pub(crate) coeffs: HashMap<TermId, BigInt>,
    pub(crate) constant: BigInt,
}

#[derive(Clone, Debug)]
pub(crate) struct SmallRangeTerm {
    pub(crate) term_id: TermId,
    pub(crate) values: Vec<BigInt>,
}

#[derive(Clone, Debug)]
pub(crate) struct FeasibleValueSet {
    pub(crate) lo: BigInt,
    pub(crate) hi: BigInt,
    pub(crate) modulus: BigInt,
    pub(crate) residue: BigInt,
}

pub(crate) enum ValueSetEval {
    Known(FeasibleValueSet),
    Empty,
    Unknown,
}

impl LiaSolver<'_> {
    pub(crate) fn check_substitution_joint_case_split(&self) -> Option<Vec<TheoryLit>> {
        if self.dioph_cached_substitutions.is_empty() {
            return None;
        }

        let sub_map: SubstitutionMap<'_> = self
            .dioph_cached_substitutions
            .iter()
            .map(|(tid, cs, c)| (*tid, (cs.as_slice(), c)))
            .collect();

        let mut primary_exprs = Vec::new();
        for (term_id, coeffs, constant) in &self.dioph_cached_substitutions {
            let Some((composed_coeffs, composed_constant)) =
                Self::compose_substitution(term_id, coeffs, constant, &sub_map)
            else {
                continue;
            };
            if self.debug_dioph {
                safe_eprintln!(
                    "[DIOPH-JCS] composed {:?} = {} + {:?}",
                    term_id,
                    composed_constant,
                    composed_coeffs
                );
            }
            primary_exprs.push(JointCaseSplitExpr {
                term_id: *term_id,
                coeffs: composed_coeffs,
                constant: composed_constant,
            });
        }
        if primary_exprs.is_empty() {
            return None;
        }

        let (alternate_exprs, alternate_source_lits) =
            self.build_joint_case_split_alternates(&primary_exprs, &sub_map);
        let mut all_exprs = primary_exprs.clone();
        for exprs in alternate_exprs.values() {
            all_exprs.extend(exprs.iter().cloned());
        }

        // SOUNDNESS (seed-236 false UNSAT): collect the justification literals
        // for every bound consulted by the case split. The infeasibility
        // conclusion below depends on these bounds, so the conflict clause
        // must include their reasons — omitting them produced a two-literal
        // conflict from the substitution equalities alone, which is
        // theory-invalid (the equalities by themselves were satisfiable).
        let mut bound_reasons: Vec<TheoryLit> = alternate_source_lits;
        let bounds =
            dioph_joint_case_split_support::build_joint_case_split_bounds(&all_exprs, |term_id| {
                let (pair, lits) = self.get_current_integer_bounds_with_reasons(term_id);
                bound_reasons.extend(lits);
                pair
            });

        match dioph_joint_case_split_support::joint_case_split_proves_infeasible(
            &primary_exprs,
            &alternate_exprs,
            &all_exprs,
            &bounds,
            SMALL_RANGE_LIMIT,
            MAX_ASSIGNMENTS,
            self.debug_dioph,
        ) {
            Some(true) => Some(self.build_sub_bound_conflict_all(&bound_reasons)),
            Some(false) | None => None,
        }
    }

    /// Build alternate substitution expressions from asserted equalities.
    ///
    /// Returns the alternates plus the source equality literals they were
    /// derived from. The infeasibility conclusion in
    /// `check_substitution_joint_case_split` may rely on alternate
    /// expressions, so any conflict built from it must include their source
    /// literals (same under-inclusive-conflict hazard as bound reasons).
    fn build_joint_case_split_alternates(
        &self,
        primary_exprs: &[JointCaseSplitExpr],
        sub_map: &SubstitutionMap<'_>,
    ) -> (HashMap<TermId, Vec<JointCaseSplitExpr>>, Vec<TheoryLit>) {
        let target_terms: HashSet<TermId> = primary_exprs.iter().map(|expr| expr.term_id).collect();
        let mut alternates: HashMap<TermId, Vec<JointCaseSplitExpr>> = HashMap::default();
        let mut source_lits: Vec<TheoryLit> = Vec::new();

        for &literal in &self.assertion_view().positive_equalities {
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }

            let (var_coeffs, constant) = self.parse_linear_expr_with_vars(args[0], args[1]);
            if var_coeffs.len() < 2 {
                continue;
            }

            let candidates: Vec<_> = var_coeffs
                .keys()
                .filter(|term_id| target_terms.contains(*term_id))
                .copied()
                .collect();
            for term_id in candidates {
                let Some(term_coeff) = var_coeffs.get(&term_id) else {
                    continue;
                };
                if term_coeff.abs() != BigInt::one() {
                    continue;
                }

                let mut isolated_coeffs = var_coeffs.clone();
                isolated_coeffs.remove(&term_id);
                for coeff in isolated_coeffs.values_mut() {
                    *coeff = -coeff.clone() * term_coeff;
                }
                isolated_coeffs.retain(|_, coeff| !coeff.is_zero());

                let isolated_constant = &constant * term_coeff;
                let coeff_vec: Vec<_> = isolated_coeffs.into_iter().collect();
                let Some((alt_coeffs, alt_constant)) =
                    Self::compose_substitution(&term_id, &coeff_vec, &isolated_constant, sub_map)
                else {
                    continue;
                };

                let duplicate_primary = primary_exprs.iter().any(|expr| {
                    expr.term_id == term_id
                        && expr.constant == alt_constant
                        && expr.coeffs == alt_coeffs
                });
                let duplicate_alt = alternates.get(&term_id).is_some_and(|exprs| {
                    exprs
                        .iter()
                        .any(|expr| expr.constant == alt_constant && expr.coeffs == alt_coeffs)
                });
                if duplicate_primary || duplicate_alt {
                    continue;
                }

                if self.debug_dioph {
                    safe_eprintln!(
                        "[DIOPH-JCS] alternate {:?} = {} + {:?}",
                        term_id,
                        alt_constant,
                        alt_coeffs
                    );
                }
                let source_lit = TheoryLit::new(literal, true);
                if !source_lits.contains(&source_lit) {
                    source_lits.push(source_lit);
                }
                alternates
                    .entry(term_id)
                    .or_default()
                    .push(JointCaseSplitExpr {
                        term_id,
                        coeffs: alt_coeffs,
                        constant: alt_constant,
                    });
            }
        }

        (alternates, source_lits)
    }
}
