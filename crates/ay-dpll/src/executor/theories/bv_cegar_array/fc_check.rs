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
        term_bits: &HashMap<TermId, BvBits>,
        var_offset: i32,
        next_var_offset: usize,
        already_covered: &mut HashSet<(TermId, TermId)>,
    ) -> CegarArrayCheck {
        let Some(select_terms) = self.collect_fc_select_terms(term_bits) else {
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
                term_bits,
                var_offset,
                &mut build.inspected_bits,
            ) else {
                return CegarArrayCheck::Incomplete;
            };

            // Group by concrete index value, find violations.
            let mut by_index: HashMap<BigInt, Vec<(TermId, TermId, BigInt)>> = HashMap::default();
            for (select, index, idx_val, sel_val) in concrete_selects {
                by_index
                    .entry(idx_val)
                    .or_default()
                    .push((select, index, sel_val));
            }

            for group in by_index.values() {
                if group.len() < 2 {
                    continue;
                }
                let first_val = &group[0].2;
                let has_violation = group.iter().skip(1).any(|entry| entry.2 != *first_val);
                if !has_violation {
                    continue;
                }

                if !self.append_fc_group_refinement(
                    group,
                    term_bits,
                    var_offset,
                    already_covered,
                    &mut build,
                ) {
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
        term_bits: &HashMap<TermId, BvBits>,
        var_offset: i32,
        inspected_bits: &mut usize,
    ) -> Option<Vec<(TermId, TermId, BigInt, BigInt)>> {
        let mut concrete_selects = Vec::new();
        for &(select_term, index_term) in selects {
            // Missing bits are incomplete only for a sort the bit-level audit
            // owns. Other element sorts are checked by model validation.
            let Some(idx_bits) = term_bits.get(&index_term) else {
                if self.fc_audit_owes_bits(index_term) {
                    return None;
                }
                continue;
            };
            let Some(sel_bits) = term_bits.get(&select_term) else {
                if self.fc_audit_owes_bits(select_term) {
                    return None;
                }
                continue;
            };
            let idx_value =
                self.concrete_bv_value_bounded(sat_model, idx_bits, var_offset, inspected_bits)?;
            let select_value =
                self.concrete_bv_value_bounded(sat_model, sel_bits, var_offset, inspected_bits)?;
            concrete_selects.push((select_term, index_term, idx_value, select_value));
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
