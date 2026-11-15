// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final-assignment reconciliation of the BV-lane witness in the independent
//! BV + LIA lane (#bv-lia-indep-final-assignment-reconcile).
//!
//! `solve_bv_lia_indep` solves ONE assertion set through TWO sequential
//! lanes. The BV lane (`BvSolveConfig::qf_bv()`: `array_axioms: false`, no
//! congruence) bit-blasts the BitVec structure and treats everything else —
//! Bool variables, array reads, arithmetic atoms, array equalities,
//! uninterpreted predicates — as FREE opaque atoms and opaque bit vectors.
//! For a mixed formula such as `(ite (select A #x2) (= n 0) (= n 1))` it
//! commits the `select` atom to whichever branch its SAT search happened to
//! pick. The AUFLIA lane then decides the arithmetic, the arrays and the
//! propositional skeleton together and may take the OTHER branch; ITS
//! assignment of those atoms is the FINAL assignment (decided against the
//! constraints the BV lane could not see), while the BV lane's values for
//! them are stale free choices. The arithmetic graft
//! (`restore_indep_bv_model_with_arith_graft`) used to carry the AUFLIA `n`
//! next to the BV lane's stale atom values; the merged witness falsified the
//! assertion and the independent gate correctly fail-closed a genuine `sat`
//! to `unknown`. deductive-checks's Set/Map encodings (`(Array BV32 Bool)` domains,
//! `__ground_seed_*` Bool anchors, `(Array BV32 BV32)` maps read at a BV
//! key, and Int cardinality counters through `ite(select ..)`) have exactly
//! this shape.
//!
//! Ownership rule (a function of the two lanes' configurations, not of the
//! instance): a term is LANE-OPAQUE — and takes the AUFLIA lane's final
//! value — when the BV lane never bit-blasted it in relation to other bits:
//!
//! * a Bool variable the BV lane's bit-blaster never reached (a Bool reached
//!   inside a BV term, e.g. a mux condition, sits in the BV model's
//!   `bool_overrides` and stays with the BV lane);
//! * an array read (`select`) — Bool-element reads are atoms, BV-element
//!   reads are opaque bit vectors; the lane runs no array axioms, so both
//!   are free there while the AUFLIA array theory decided them;
//! * an array index VARIABLE the BV lane never related to other bits (it
//!   occurs only as a `select` index / `store` key in every BV predicate and
//!   BV term the BV lane valued) whose AUFLIA EUF class is a BitVec literal —
//!   the AUFLIA array reasoning (ROW splits, extensionality) decided the
//!   index identity, and a read is meaningless without it;
//! * an arithmetic atom (`= distinct < <= > >=` over Int/Real operands);
//! * an equality/distinctness over array or uninterpreted operands, and an
//!   uninterpreted Bool predicate (the BV lane runs no congruence here).
//!
//! A BV predicate (`=`/`distinct`/`bv*` comparison over BitVec operands) and
//! every other bit-blasted BV term keep the BV lane's bit-accurate values.
//! Tseitin gate atoms (`and`/`or`/`not`/`=>`/Bool `ite`) are left alone:
//! every evaluator reads compound terms structurally from their leaves.
//!
//! Every re-valued read is then PINNED into the array interpretation: its
//! index is evaluated under the merged model (the BV lane's bits, with the
//! reconciled index variables), its store chain is walked to the base array
//! variable (a read that hits a store key is ROW-forced and left to the
//! validators), and the final read value overwrites the cell everywhere a
//! reader can see it — the BV model's `bool_overrides`/`values`, the SAT
//! assignment, and the interpretation's store entry (a stale entry at that
//! index is dropped first, so the cell map stays single-valued — the #8510
//! discipline; a base the BV lane extracted no interpretation for gets one
//! of the extraction's own shape). Cached BV values computed from superseded
//! bits are purged so they are re-evaluated structurally. Two final reads of
//! one cell that DISAGREE mean the lanes' index identifications are
//! incompatible; the pass then declines to pin (returns without touching the
//! atoms) and the caller falls back.
//!
//! Soundness: only the CANDIDATE model changes, never the search or the
//! verdict authority. The caller keeps a reconciled merge only when no root
//! evaluates to a definite `false` under it AND — since the executor's own
//! evaluator answers `Unknown` for exactly the array reads re-valued here —
//! the ordinary model validation accepts it independently for every root,
//! preferring the previous merge policy's witness when that one is accepted
//! instead (a cross-lane disagreement the reconciliation cannot resolve
//! falls back to the previous merge policy),
//! and every kept witness still faces the unchanged fail-closed validation
//! and the independent model gate, which re-evaluate every assertion. A wrong
//! re-valuation can only keep today's degrade-to-`unknown` outcome, never
//! manufacture an invalid `sat`, and never flips sat/unsat.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::{EvalValue, Executor, Model};

/// Array reads, index identification and cell pins (the value-level half of
/// the reconciliation; see the module docs above).
mod cells;

impl Executor {
    /// Reconcile the BV lane's witness `merged` with the AUFLIA lane's final
    /// assignment `final_assignment` (see module docs). Returns `true` when
    /// the merged model was mutated (the caller must re-check and
    /// re-validate it) and `false` when nothing changed — including the
    /// fail-closed outcome on a cell disagreement.
    pub(in crate::executor) fn reconcile_bv_lane_model_with_final_assignment(
        &self,
        merged: &mut Model,
        final_assignment: &Model,
        roots: &[TermId],
    ) -> bool {
        if merged.bv_model.is_none() {
            return false;
        }
        let atom_updates = self.lane_opaque_atom_updates(merged, final_assignment);
        let reads = self.collect_bv_array_reads(roots);
        // Index identification first: the cell pins below evaluate every
        // read's index under the merged model, so an index variable the
        // final assignment committed to a literal must carry that literal
        // before the reads are resolved.
        let index_updates = self.final_index_literal_updates(merged, final_assignment, roots);
        let mut changed = self.apply_bv_value_updates(merged, &index_updates);
        if changed {
            super::eval_memo_clear();
        }
        // Decide the cell pins BEFORE re-valuing the atoms: the pins read the
        // final assignment and the (now index-reconciled) BV bits, neither of
        // which the atom re-valuation changes, and a cell disagreement must
        // leave the atoms exactly as the BV lane assigned them.
        //
        // The unlocatable reads are collected here, AFTER the index
        // reconciliation, so an index the reconciliation just decided counts
        // as located.
        let unlocatable = self.unlocatable_read_values(merged, &reads);
        let Some(pins) =
            self.pin_cells_from_final_assignment(merged, final_assignment, &reads, &unlocatable)
        else {
            return changed;
        };
        changed |= Self::apply_atom_updates(merged, &atom_updates);
        if !pins.is_empty() {
            changed |= self.apply_cell_pins(merged, &pins, &reads);
        }
        if changed {
            super::eval_memo_clear();
        }
        changed
    }

    /// Whether the BV lane treats `atom` as an opaque Tseitin literal (see
    /// the ownership rule in the module docs).
    fn bv_lane_opaque_atom(&self, merged: &Model, atom: TermId) -> bool {
        if !matches!(self.ctx.terms.sort(atom), Sort::Bool) {
            return false;
        }
        match self.ctx.terms.get(atom) {
            TermData::Var(_, _) => !merged
                .bv_model
                .as_ref()
                .is_some_and(|bv| bv.bool_overrides.contains_key(&atom)),
            TermData::App(sym, args) => {
                let name = sym.name();
                if name == "select" {
                    return true;
                }
                let Some(&first) = args.first() else {
                    return false;
                };
                let operand_sort = self.ctx.terms.sort(first);
                match name {
                    "=" | "distinct" => matches!(
                        operand_sort,
                        Sort::Int | Sort::Real | Sort::Array(_) | Sort::Uninterpreted(_)
                    ),
                    "<" | "<=" | ">" | ">=" => matches!(operand_sort, Sort::Int | Sort::Real),
                    _ => !Self::is_known_theory_symbol(name),
                }
            }
            _ => false,
        }
    }

    /// The final assignment's value for a Bool atom: its SAT assignment
    /// first, then an EUF `true`/`false` term value, then a recovered Bool
    /// override. `None` when the final assignment never valued it (the atom
    /// is then left alone — nothing is fabricated).
    fn final_bool_value(&self, final_assignment: &Model, atom: TermId) -> Option<bool> {
        if let Some(b) = self.term_value(
            &final_assignment.sat_model,
            &final_assignment.term_to_var,
            atom,
        ) {
            return Some(b);
        }
        if let Some(euf) = final_assignment.euf_model.as_ref() {
            match euf.term_values.get(&atom).map(String::as_str) {
                Some("true") => return Some(true),
                Some("false") => return Some(false),
                _ => {}
            }
        }
        final_assignment.bool_overrides.get(&atom).copied()
    }

    /// The final assignment's EUF class value for a BitVec-sorted term when
    /// that class is spelled as a BitVec literal of the term's width.
    fn final_bv_literal(&self, final_assignment: &Model, term: TermId) -> Option<BigInt> {
        let Sort::BitVec(bv) = self.ctx.terms.sort(term) else {
            return None;
        };
        let spelled = final_assignment
            .euf_model
            .as_ref()?
            .term_values
            .get(&term)?;
        match Self::parse_bitvec_string(spelled, bv.width) {
            EvalValue::BitVec { value, .. } => Some(value),
            _ => None,
        }
    }

    /// Lane-opaque atoms the final assignment values, with those values, in
    /// deterministic order: every atom either lane's SAT layer knows —
    /// EXCEPT an array read, which is never re-valued as a free atom.
    ///
    /// A read is re-valued only as a CONSEQUENCE of pinning its cell
    /// (`apply_cell_pins` -> `pinned_read_updates`), so the atom layer and the
    /// array interpretation can never disagree about one read. Taking the
    /// final value here as well re-valued reads this pass could NOT LOCATE —
    /// an index the merged model does not evaluate, so no cell is pinned and
    /// the array layer keeps the BV lane's value — and model COMPLETION then
    /// fixed that index onto a cell carrying the other value, so the strict
    /// model-validation oracle refused a witness the ladder had accepted.
    /// Measured on `isweep/min/m_04_0124.smt2` (reduced from
    /// `gq2/iabvx/iabvx_0104_named.smt2`): `(select S0 (bvadd k0 #x00000002))`
    /// re-valued `false` with the BV lane valuing no `k0`, cell 2 pinned
    /// `true` by `(select S0 #x00000002)`, completion `k0 := 0` — base and z3
    /// answer `sat`, the pass degraded it to `unknown (incomplete)` on
    /// "strict model-validation oracle arrays rejected assertion 3".
    ///
    /// For a read this pass DOES locate the pin path writes exactly the value
    /// this filter drops, into the same layers, so nothing that merged before
    /// stops merging.
    fn lane_opaque_atom_updates(
        &self,
        merged: &Model,
        final_assignment: &Model,
    ) -> Vec<(TermId, bool)> {
        let mut atoms: Vec<TermId> = merged
            .term_to_var
            .keys()
            .chain(final_assignment.term_to_var.keys())
            .copied()
            .collect();
        atoms.sort_unstable();
        atoms.dedup();
        atoms
            .into_iter()
            .filter(|&atom| self.bv_lane_opaque_atom(merged, atom))
            .filter(|&atom| !self.is_array_read(atom))
            .filter_map(|atom| Some((atom, self.final_bool_value(final_assignment, atom)?)))
            .collect()
    }

    /// Whether `term` is a `(select array index)` application.
    fn is_array_read(&self, term: TermId) -> bool {
        matches!(
            self.ctx.terms.get(term),
            TermData::App(sym, args) if sym.name() == "select" && args.len() == 2
        )
    }

    /// Write the re-valued atoms into the merged model's SAT assignment (an
    /// atom the BV lane's SAT layer never saw goes to the model-level Bool
    /// overrides, which `evaluate_var` consults right after the SAT model).
    /// Returns whether anything changed.
    fn apply_atom_updates(merged: &mut Model, updates: &[(TermId, bool)]) -> bool {
        let mut changed = false;
        for &(atom, val) in updates {
            if let Some(&var) = merged.term_to_var.get(&atom) {
                if let Some(slot) = merged.sat_model.get_mut(var as usize) {
                    if *slot != val {
                        *slot = val;
                        changed = true;
                    }
                    continue;
                }
            }
            if merged.bool_overrides.insert(atom, val) != Some(val) {
                changed = true;
            }
        }
        changed
    }

    /// Install BV term values into the BV model and purge every cached
    /// non-leaf BV value that mentions an updated term (other than the
    /// updated terms themselves), so those terms are re-evaluated
    /// structurally from the new values. Returns whether anything changed.
    pub(super) fn apply_bv_value_updates(
        &self,
        merged: &mut Model,
        updates: &[(TermId, BigInt)],
    ) -> bool {
        if updates.is_empty() {
            return false;
        }
        let Some(bv_model) = merged.bv_model.as_mut() else {
            return false;
        };
        let updated: HashSet<TermId> = updates.iter().map(|(t, _)| *t).collect();
        let mut stale: Vec<TermId> = bv_model
            .values
            .keys()
            .copied()
            .filter(|&t| {
                !updated.contains(&t)
                    && !matches!(self.ctx.terms.get(t), TermData::Var(_, _))
                    && self.term_mentions_any_of(t, &updated)
            })
            .collect();
        stale.sort_unstable();
        let mut changed = !stale.is_empty();
        for t in stale {
            bv_model.values.remove(&t);
        }
        for (term, value) in updates {
            if bv_model.values.insert(*term, value.clone()).as_ref() != Some(value) {
                changed = true;
            }
        }
        changed
    }

    /// Whether `term`'s subtree mentions one of `targets` (as any subterm).
    fn term_mentions_any_of(&self, term: TermId, targets: &HashSet<TermId>) -> bool {
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if targets.contains(&t) {
                return true;
            }
            stack.extend(self.ctx.terms.children(t));
        }
        false
    }
}
