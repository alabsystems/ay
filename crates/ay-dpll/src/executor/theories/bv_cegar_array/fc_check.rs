// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Check array functional consistency against a concrete SAT model.
    ///
    /// For each pair of select terms on the same direct array operand where the
    /// concrete index values are equal but the concrete result values
    /// differ, generate the corresponding FC axiom clauses.
    ///
    /// `already_covered` tracks pairs that have had FC axioms generated
    /// in previous CEGAR iterations to avoid duplicate work.
    pub(in crate::executor) fn check_array_fc_violations(
        &mut self,
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        next_var_offset: usize,
        already_covered: &mut HashSet<(TermId, TermId)>,
    ) -> CegarArrayCheck {
        let Some(select_terms) = self.collect_fc_select_terms(lits.term_bits()) else {
            return CegarArrayCheck::Incomplete;
        };
        if select_terms.is_empty() {
            return CegarArrayCheck::Consistent;
        }

        let selects_by_array = Self::group_fc_selects_by_direct_array(&select_terms);

        let Some(initial_next_var) = next_var_offset.checked_add(1) else {
            return CegarArrayCheck::Incomplete;
        };
        let Ok(next_var) = u32::try_from(initial_next_var) else {
            return CegarArrayCheck::Incomplete;
        };
        let mut build = CegarArrayBuild {
            clauses: Vec::new(),
            next_var,
            new_vars: 0,
            inspected_bits: 0,
            pair_attempts: 0,
            newly_covered: HashSet::default(),
        };

        for (_array_root, selects) in &selects_by_array {
            if selects.len() < 2 {
                continue;
            }

            let Some(concrete_selects) = self.collect_concrete_fc_selects(
                selects,
                sat_model,
                lits,
                &mut build.inspected_bits,
            ) else {
                return CegarArrayCheck::Incomplete;
            };

            // Group by concrete index value, find violations.
            let mut by_index: HashMap<BigInt, Vec<FcConcreteSelect>> = HashMap::default();
            for concrete in concrete_selects {
                by_index
                    .entry(concrete.index_value.clone())
                    .or_default()
                    .push(concrete);
            }

            for group in by_index.values() {
                if group.len() < 2 {
                    continue;
                }
                let first_value = &group[0].value;
                let has_violation = group
                    .iter()
                    .skip(1)
                    .any(|entry| entry.value != *first_value);
                if !has_violation {
                    continue;
                }

                if !self.append_fc_group_refinement(group, already_covered, &mut build) {
                    return CegarArrayCheck::Incomplete;
                }
            }
        }

        if build.clauses.is_empty() {
            return CegarArrayCheck::Consistent;
        }

        already_covered.extend(build.newly_covered);
        CegarArrayCheck::Refinement(CegarArrayResult {
            clauses: build.clauses,
            num_new_vars: build.new_vars,
        })
    }

    fn collect_concrete_fc_selects(
        &mut self,
        selects: &[(TermId, TermId)],
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        inspected_bits: &mut usize,
    ) -> Option<Vec<FcConcreteSelect>> {
        let mut concrete_selects = Vec::new();
        for &(select_term, index_term) in selects {
            // A missing literal view is incomplete only for a sort the
            // bit-level audit owns. Other element sorts are checked by model
            // validation.
            let Some(index_lits) = lits.scalar_lits(&self.ctx.terms, index_term) else {
                if self.fc_audit_owes_bits(index_term) {
                    return None;
                }
                continue;
            };
            let Some(value_lits) = lits.scalar_lits(&self.ctx.terms, select_term) else {
                if self.fc_audit_owes_bits(select_term) {
                    return None;
                }
                continue;
            };
            let index_value =
                self.concrete_value_bounded(sat_model, &index_lits, inspected_bits)?;
            let value = self.concrete_value_bounded(sat_model, &value_lits, inspected_bits)?;
            concrete_selects.push(FcConcreteSelect {
                select: select_term,
                index_lits,
                value_lits,
                index_value,
                value,
            });
        }
        Some(concrete_selects)
    }

    /// Group by the direct array operand, never by a shared store-chain root.
    /// Selects on different arrays may legitimately differ at an equal index;
    /// grouping them together would generate an unsound FC axiom.
    fn group_fc_selects_by_direct_array(
        select_terms: &[(TermId, TermId, TermId)],
    ) -> HashMap<TermId, Vec<(TermId, TermId)>> {
        let mut selects_by_array = HashMap::default();
        for &(select_term, array, index) in select_terms {
            selects_by_array
                .entry(array)
                .or_insert_with(Vec::new)
                .push((select_term, index));
        }
        selects_by_array
    }
}
