// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Propagation of candidate read pins from store-defined arrays down
//! to their terminal bases before interpretations are built.
//! Completion only; the complete original-root validation is unchanged.
use super::*;

impl Executor {
    /// #defined-array-read-pins: a read the candidate committed on a
    /// store-defined array at an index its chain does not store to
    /// is, by read-over-write, a read of the chain's base at that
    /// index. The select scan records it on the DEFINED var, but
    /// [`Self::build_store_chain_interp`] inherits only the base's
    /// own entries, so the committed read silently reverted to the
    /// base default — falsifying the very load the candidate
    /// satisfied (QF_ABV dwp mem-version chains: byte loads through
    /// `mem_k = store(mem_{k-1}, …)` generations, where the terminal
    /// base was never itself read at the load indices). Propagate
    /// each defined var's pins down to its terminal base var
    /// (insert-if-absent; a contested index keeps the base's entry
    /// and the gate judges the inconsistency) before building, so
    /// every interpretation built over that base agrees with the
    /// candidate's reads. The completed model is always
    /// gate-validated, so a junk pin can only cost completeness,
    /// never soundness.
    pub(super) fn propagate_defined_array_read_pins(
        terms: &TermStore,
        bv_model: &BvModel,
        store_defs: &[(TermId, TermId, TermId)],
        assertions: &[TermId],
        array_model: &mut ArrayModel,
    ) {
        let plans = Self::read_pin_plans(terms, bv_model, store_defs);
        // Pins also cross candidate-true var<->var equality edges
        // unchanged: a read committed on a non-defined class member
        // must reach the terminal base of a defined member's lineage
        // BEFORE the authoritative builds, or the built member
        // disagrees with the merged class interpretation at that
        // index and the gate falsifies the member's definition
        // (dwp: loads on `mem_35_3751` vs `mem_35_3784 =
        // store*(mem_35_3791)` with `3784 = 3751` candidate-true).
        let equality_pairs = Self::model_true_array_equality_pairs(terms, bv_model, assertions);
        // Candidate-committed (genuine) reads outrank scan pins —
        // a pin may come from a generated cross-select whose bits
        // are unlinked — so seed them into the interpretations
        // (overwriting) and let them force their way down the
        // cascade: a genuine read on a defined var whose value
        // never became a scan pin otherwise loses to junk already
        // seated on the terminal base, and the authoritative build
        // then disagrees with the very load the candidate
        // satisfied. `committed` tracks which cells are genuine as
        // they hop var to var.
        let mut committed = Self::genuine_assertion_select_cells(terms, bv_model, assertions);
        for (var, cells) in &committed {
            if !Self::ensure_array_interp_entry(terms, array_model, *var) {
                continue;
            }
            if let Some(interp) = array_model.array_values.get_mut(var) {
                for (idx, val) in cells {
                    match interp.stores.iter_mut().find(|(k, _)| k == idx) {
                        Some(slot) => slot.1 = val.clone(),
                        None => interp.stores.push((idx.clone(), val.clone())),
                    }
                }
            }
        }
        // Pins cascade generation by generation (m_k -> m_{k-1} ->
        // ...), so repeat until a pass moves nothing. Recording pins
        // on a still-`read_conflicted` base is fine: that set
        // withholds totality, and the build below — which does
        // consult it — still decides whether the base's entries may
        // be inherited.
        loop {
            let mut moved = false;
            for (var_id, base, stored) in &plans {
                moved |= Self::transfer_read_pins(
                    terms,
                    array_model,
                    *var_id,
                    *base,
                    Some(stored),
                    committed.get(var_id),
                );
                moved |= Self::merge_committed(&mut committed, *var_id, *base, Some(stored));
            }
            for &(a, b) in &equality_pairs {
                moved |=
                    Self::transfer_read_pins(terms, array_model, a, b, None, committed.get(&a));
                moved |=
                    Self::transfer_read_pins(terms, array_model, b, a, None, committed.get(&b));
                moved |= Self::merge_committed(&mut committed, a, b, None);
                moved |= Self::merge_committed(&mut committed, b, a, None);
            }
            if !moved {
                break;
            }
        }
    }

    /// Genuine-cell bookkeeping follows the same hops as the pins:
    /// first genuine writer wins a contested index (two genuine
    /// reads in conflict make the candidate uncompletable either
    /// way; the gate judges).
    fn merge_committed(
        committed: &mut HashMap<TermId, HashMap<String, String>>,
        from: TermId,
        to: TermId,
        stored: Option<&HashSet<String>>,
    ) -> bool {
        let Some(src) = committed.get(&from).cloned() else {
            return false;
        };
        let dst = committed.entry(to).or_default();
        let mut moved = false;
        for (idx, val) in src {
            if stored.is_some_and(|s| s.contains(&idx)) || dst.contains_key(&idx) {
                continue;
            }
            dst.insert(idx, val);
            moved = true;
        }
        moved
    }

    /// Synthesize exactly the entry
    /// `resolve_substitution_target_interp` would for a missing
    /// var, so the build below sees a well-formed base.
    fn ensure_array_interp_entry(
        terms: &TermStore,
        array_model: &mut ArrayModel,
        var: TermId,
    ) -> bool {
        if array_model.array_values.contains_key(&var) {
            return true;
        }
        let Sort::Array(sort) = terms.sort(var) else {
            return false;
        };
        let default = match &sort.element_sort {
            Sort::BitVec(elem) => format_bitvec(&BigInt::from(0u8), elem.width),
            Sort::Bool => "false".to_string(),
            _ => return false,
        };
        array_model.array_values.insert(
            var,
            ArrayInterpretation {
                index_sort: Some(sort.index_sort.clone()),
                element_sort: Some(sort.element_sort.clone()),
                default: Some(default),
                stores: Vec::new(),
            },
        );
        true
    }

    /// Insert-if-absent transfer of `from`'s current pins into
    /// `to`'s interpretation, skipping `stored` indices when given
    /// (a definition's own writes). A pin the source is committed
    /// to (a genuine assertion read, tracked in `force`)
    /// overwrites a conflicting target cell instead: the target's
    /// cell can only be an unlinked generated-select pin, because
    /// a genuine read on the target at the same index would make
    /// the candidate uncompletable regardless of which wins.
    fn transfer_read_pins(
        terms: &TermStore,
        array_model: &mut ArrayModel,
        from: TermId,
        to: TermId,
        stored: Option<&HashSet<String>>,
        force: Option<&HashMap<String, String>>,
    ) -> bool {
        let Some(pins) = array_model
            .array_values
            .get(&from)
            .map(|interp| interp.stores.clone())
        else {
            return false;
        };
        if !Self::ensure_array_interp_entry(terms, array_model, to) {
            return false;
        }
        let Some(target) = array_model.array_values.get_mut(&to) else {
            return false;
        };
        let mut moved = false;
        for (idx, val) in pins {
            if stored.is_some_and(|s| s.contains(&idx)) {
                continue;
            }
            match target.stores.iter_mut().find(|(k, _)| k == &idx) {
                Some(slot) => {
                    if slot.1 != val && force.and_then(|f| f.get(&idx)) == Some(&val) {
                        slot.1 = val;
                        moved = true;
                    }
                }
                None => {
                    target.stores.push((idx, val));
                    moved = true;
                }
            }
        }
        moved
    }

    /// Each definition's (defined var, terminal base var, evaluated
    /// store indices). A chain with an unresolved index cannot be
    /// built either, so its pins have no sound home and are skipped.
    fn read_pin_plans(
        terms: &TermStore,
        bv_model: &BvModel,
        store_defs: &[(TermId, TermId, TermId)],
    ) -> Vec<(TermId, TermId, HashSet<String>)> {
        let mut memo = BvEvalMemo::default();
        let mut plans: Vec<(TermId, TermId, HashSet<String>)> = Vec::new();
        for &(var_id, store_term, base) in store_defs {
            if !matches!(terms.get(base), TermData::Var(_, _)) || base == var_id {
                continue;
            }
            let Sort::Array(arr_sort) = terms.sort(store_term) else {
                continue;
            };
            let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
                continue;
            };
            let Some((entries, _)) = Self::collect_store_chain_entries(terms, store_term) else {
                continue;
            };
            let mut stored = HashSet::default();
            let mut resolved = true;
            for (idx_term, _) in &entries {
                match Self::store_chain_operand_value(terms, bv_model, *idx_term, &mut memo) {
                    Some(idx) => {
                        stored.insert(format_bitvec(&idx, idx_bv.width));
                    }
                    None => {
                        resolved = false;
                        break;
                    }
                }
            }
            if resolved {
                plans.push((var_id, base, stored));
            }
        }
        plans
    }
}
