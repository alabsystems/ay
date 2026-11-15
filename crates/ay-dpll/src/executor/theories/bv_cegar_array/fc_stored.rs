// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Read-over-write across a definition edge: a select at an
    /// index a candidate-true definition STORES to must equal the
    /// stored value, even when the select sits on another array of
    /// the class (connected to the defined var without crossing
    /// that definition edge). Select-vs-select congruence cannot
    /// see this: no select term on the base side need exist at the
    /// stored index, so the candidate sets the read bits and the
    /// stored-value bits independently. The stored value enters
    /// as a pseudo-select (keyed by its store node) into the same
    /// pair machinery, guarded by the path atoms plus
    /// disequalities against every other store on the path and
    /// every outer store of the same chain (shadowing).
    pub(super) fn append_fc_stored_value_refinements(
        &mut self,
        by_index: &HashMap<BigInt, Vec<FcConcreteSelect>>,
        members: &[TermId],
        edges: &[(TermId, TermId, i32, Option<TermId>)],
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        owner_of: &HashMap<TermId, TermId>,
        adjacency: &HashMap<TermId, Vec<(TermId, i32, Option<TermId>)>>,
        already_covered: &HashSet<FcCoverKey>,
        build: &mut CegarArrayBuild,
    ) -> bool {
        let member_set: HashSet<TermId> = members.iter().copied().collect();
        for &(var, base, def_guard, def) in edges {
            let Some(chain) = def else { continue };
            if !member_set.contains(&var) {
                continue;
            }
            let entries = Self::fc_store_chain_entries(&self.ctx.terms, chain);
            for (pos, &(node, idx_term, val_term)) in entries.iter().enumerate() {
                let Some(pseudo) = self.stored_value_pseudo_select(
                    node,
                    idx_term,
                    val_term,
                    sat_model,
                    lits,
                    &mut build.inspected_bits,
                ) else {
                    continue;
                };
                let Some(group) = by_index.get(&pseudo.index_value) else {
                    continue;
                };
                if !self.append_fc_stored_entry_pairs(
                    group,
                    &pseudo,
                    &entries[..pos],
                    (var, base, def_guard, chain),
                    sat_model,
                    lits,
                    owner_of,
                    adjacency,
                    already_covered,
                    build,
                ) {
                    return false;
                }
            }
        }
        true
    }

    /// The pseudo-select for one store entry: its index/value bit
    /// vectors and concrete values, or `None` when either side has
    /// no literal view.
    fn stored_value_pseudo_select(
        &mut self,
        node: TermId,
        idx_term: TermId,
        val_term: TermId,
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        inspected_bits: &mut usize,
    ) -> Option<FcConcreteSelect> {
        let index_lits = lits.scalar_lits(&self.ctx.terms, idx_term)?;
        let value_lits = lits.scalar_lits(&self.ctx.terms, val_term)?;
        let index_value = self.concrete_value_bounded(sat_model, &index_lits, inspected_bits)?;
        let value = self.concrete_value_bounded(sat_model, &value_lits, inspected_bits)?;
        Some(FcConcreteSelect {
            select: node,
            index_lits,
            value_lits,
            index_value,
            value,
        })
    }

    /// Pair every disagreeing select in `group` (the stored
    /// entry's concrete index) with the stored-value pseudo-select.
    fn append_fc_stored_entry_pairs(
        &mut self,
        group: &[FcConcreteSelect],
        pseudo: &FcConcreteSelect,
        outer_entries: &[(TermId, TermId, TermId)],
        def_edge: (TermId, TermId, i32, TermId),
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        owner_of: &HashMap<TermId, TermId>,
        adjacency: &HashMap<TermId, Vec<(TermId, i32, Option<TermId>)>>,
        already_covered: &HashSet<FcCoverKey>,
        build: &mut CegarArrayBuild,
    ) -> bool {
        let (var, base, def_guard, chain) = def_edge;
        for entry in group {
            if entry.value == pseudo.value {
                continue;
            }
            if !self.count_pair_attempt(build) {
                return false;
            }
            let Some(&owner) = owner_of.get(&entry.select) else {
                continue;
            };
            let Some((mut guards, defs)) =
                Self::equality_path_guards(adjacency, owner, var, Some((var, base, Some(chain))))
            else {
                continue;
            };
            guards.push(def_guard);
            let Some(mut stored_bits) = self.def_path_stored_bits(
                sat_model,
                lits,
                &defs,
                &pseudo.index_value,
                entry.index_lits.len(),
                &mut build.inspected_bits,
            ) else {
                continue;
            };
            // Outer stores of the same chain shadow this entry when
            // their index coincides, so they join the disequalities
            // (and a concrete coincidence means this entry is not
            // the effective write for the group at all).
            let mut shadowed = false;
            for &(_, outer_idx, _) in outer_entries {
                let Some(bits) = lits.scalar_lits(&self.ctx.terms, outer_idx) else {
                    shadowed = true;
                    break;
                };
                let Some(v) =
                    self.concrete_value_bounded(sat_model, &bits, &mut build.inspected_bits)
                else {
                    shadowed = true;
                    break;
                };
                if v == pseudo.index_value || bits.len() != entry.index_lits.len() {
                    shadowed = true;
                    break;
                }
                stored_bits.push(bits);
            }
            if shadowed {
                continue;
            }
            if !self.append_fc_pair_refinement(
                entry,
                pseudo,
                &guards,
                &stored_bits,
                already_covered,
                build,
            ) {
                return false;
            }
        }
        true
    }
}
