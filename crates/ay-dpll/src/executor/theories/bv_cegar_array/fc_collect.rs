// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Collect congruence links `(var_a, var_b, eq_term, def_store)`
    /// for each array equality in `assertions` (the ORIGINAL,
    /// pre-substitution assertions when substitution ran), mapping
    /// the equality term through `subst` to the term that was
    /// actually encoded, whose atom is the congruence guard. Two
    /// shapes: var<->var (`def_store = None`) and var<->store-chain
    /// definitions (`def_store = Some(chain)`, `var_b` the chain's
    /// terminal base var; the chain term is substitution-mapped
    /// too, so its store index terms are the encoded ones).
    /// Captured once per solve at the FC call site, where the
    /// originals still exist: after substitution the equality's
    /// var<->var form is gone (both sides become store chains),
    /// and scalar-budgeted partial substitution makes the chains
    /// unmatchable by term identity.
    pub(in crate::executor) fn collect_cross_equality_pairs(
        terms: &mut TermStore,
        assertions: &[TermId],
        subst: Option<&mut crate::preprocess::VariableSubstitution>,
    ) -> Vec<(TermId, TermId, TermId, Option<TermId>)> {
        let mut candidates: Vec<(TermId, TermId, TermId, Option<TermId>)> = Vec::new();
        let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::default();
        let mut seen_defs: HashSet<(TermId, TermId)> = HashSet::default();
        let mut pending: Vec<TermId> = assertions.to_vec();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(term) = pending.pop() {
            if !visited.insert(term) || visited.len() > budget::MAX_TERMS {
                continue;
            }
            match terms.get(term) {
                TermData::App(sym, args) => {
                    if sym.name() == "=" && args.len() == 2 && args[0] != args[1] {
                        if let Some((a, b, def)) =
                            Self::classify_cross_equality(terms, args[0], args[1])
                        {
                            let fresh = match def {
                                None => seen_pairs.insert(if a < b { (a, b) } else { (b, a) }),
                                Some(chain) => seen_defs.insert((a, chain)),
                            };
                            if fresh {
                                candidates.push((a, b, term, def));
                            }
                        }
                    }
                    pending.extend(args.iter().copied());
                }
                TermData::Not(inner) => pending.push(*inner),
                TermData::Ite(cond, then_term, else_term) => {
                    pending.extend([*cond, *then_term, *else_term]);
                }
                _ => {}
            }
        }
        match subst {
            None => candidates,
            Some(subst) => candidates
                .into_iter()
                .map(|(a, b, eq, def)| {
                    let eq = subst.apply_to_term(terms, eq);
                    let def = def.map(|chain| subst.apply_to_term(terms, chain));
                    (a, b, eq, def)
                })
                .collect(),
        }
    }

    /// Classify one `(= x y)` term as a var<->var link `(x, y,
    /// None)` or a var<->store-chain definition link `(var, base,
    /// Some(chain))`, if either shape fits.
    fn classify_cross_equality(
        terms: &TermStore,
        x: TermId,
        y: TermId,
    ) -> Option<(TermId, TermId, Option<TermId>)> {
        let is_array_var = |side: TermId| {
            matches!(terms.get(side), TermData::Var(_, _))
                && matches!(terms.sort(side), Sort::Array(_))
        };
        if is_array_var(x) && is_array_var(y) {
            return Some((x, y, None));
        }
        for (var, chain) in [(x, y), (y, x)] {
            if !is_array_var(var) {
                continue;
            }
            if let Some(base) = Self::fc_store_chain_base_var(terms, chain) {
                return (base != var).then_some((var, base, Some(chain)));
            }
        }
        None
    }

    /// The terminal base of a store chain when it is an array var.
    fn fc_store_chain_base_var(terms: &TermStore, mut term: TermId) -> Option<TermId> {
        for _ in 0..500 {
            match terms.get(term) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    term = args[0];
                }
                TermData::Var(_, _) if matches!(terms.sort(term), Sort::Array(_)) => {
                    return Some(term);
                }
                _ => return None,
            }
        }
        None
    }

    /// `(store_node, index_term, value_term)` per store of a
    /// chain, outermost first.
    pub(super) fn fc_store_chain_entries(
        terms: &TermStore,
        mut term: TermId,
    ) -> Vec<(TermId, TermId, TermId)> {
        let mut entries = Vec::new();
        for _ in 0..500 {
            match terms.get(term) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    entries.push((term, args[1], args[2]));
                    term = args[0];
                }
                _ => break,
            }
        }
        entries
    }

    /// Store index terms of a store chain, outermost first.
    pub(super) fn fc_store_chain_indices(terms: &TermStore, mut term: TermId) -> Vec<TermId> {
        let mut indices = Vec::new();
        for _ in 0..500 {
            match terms.get(term) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    indices.push(args[1]);
                    term = args[0];
                }
                _ => break,
            }
        }
        indices
    }

    /// `(side_a, side_b, guard_lit, def_store)` for each
    /// pre-collected cross-equality pair whose (substituted)
    /// equality atom is true under `sat_model`.
    pub(super) fn model_true_array_equalities(
        &mut self,
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        cross_pairs: &[(TermId, TermId, TermId, Option<TermId>)],
    ) -> Vec<(TermId, TermId, i32, Option<TermId>)> {
        cross_pairs
            .iter()
            .filter_map(|&(a, b, eq, def)| {
                self.true_equality_guard(sat_model, lits, eq)
                    .map(|guard| (a, b, guard, def))
            })
            .collect()
    }

    /// The equality atom's final-numbered literal when the atom is
    /// true under `sat_model`; `None` when unencoded or false.
    fn true_equality_guard(
        &self,
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        eq_term: TermId,
    ) -> Option<i32> {
        let guard_lits = lits.scalar_lits(&self.ctx.terms, eq_term)?;
        let [lit] = guard_lits.as_slice() else {
            return None;
        };
        let var_idx = usize::try_from(lit.unsigned_abs()).ok()?.checked_sub(1)?;
        let sat_val = *sat_model.get(var_idx)?;
        let truth = if *lit > 0 { sat_val } else { !sat_val };
        truth.then_some(*lit)
    }

    pub(super) fn collect_concrete_fc_selects(
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
    pub(super) fn group_fc_selects_by_direct_array(
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
