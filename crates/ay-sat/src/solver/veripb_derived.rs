// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-veripb-hints` beyond conflict analysis: a clause a simplification
//! derives is written as `rup <C> : <ids> ;` when the technique names the
//! clauses it derived C from.
//!
//! On the VeriPB route every other derived clause is written as
//! `red <C> : <pivot> -> 1 ;` with no antecedents, and the official check
//! elaborates each one by searching the whole database. On
//! aes_equiv_encry_3_rounds such steps outnumber the learned clauses (5.1
//! million against 4.4 million; in the first minute 1.3 million BVE resolvents,
//! 0.8 million factor steps, 0.5 million each from decompose and congruence),
//! and they elaborated at about 78 per second: about 18 hours for one proof.
//!
//! A technique names each antecedent with `veripb_note_antecedent*` right
//! before its `proof_emit_add*` call. The emission funnel looks up their ids by
//! content, states a unit constraint for each of their root-false literals, and
//! checks by unit propagation over exactly those constraints that the negation
//! of C is refuted; only then are the ids written. Anything else (an unknown id,
//! a unit it cannot state, no conflict) writes the step as before. A wrong or
//! stale antecedent therefore costs checking time, never validity.

use super::veripb_hints::VeripbHintState;
use super::*;
use crate::diagnostic_trace::DiagnosticPass;
use crate::kitten::{CoreAntecedent, CoreLemmas};
use crate::watched::entry_blocker_raw;
use std::io;

/// Antecedent literals one derived clause may name before it is written plain
/// (the check is linear in them).
const VERIPB_DERIVED_MAX_LITS: usize = 1 << 14;

#[derive(Clone, Default)]
pub(crate) struct VeripbDerivedState {
    /// Antecedents of the next derived addition, concatenated (internal
    /// literals); `ends[i]` closes antecedent i.
    lits: Vec<Literal>,
    ends: Vec<usize>,
    /// Hint ids of the addition being written, in propagation order.
    ids: Vec<u64>,
    /// Literal-indexed truth of the refutation check, and the entries set.
    truth: Vec<bool>,
    touched: Vec<usize>,
    done: Vec<bool>,
    scratch: Vec<Literal>,
    /// Root-false literals of the antecedent being examined.
    roots: Vec<Literal>,
    /// The conflict clause conflict analysis is resolving from when it asks
    /// OTFS to strengthen a reason (`veripb_note_otfs_conflict`).
    pub(super) otfs_conflict: Option<ClauseRef>,
    /// Hint ids already read for one clause (`veripb_ready_hints`), and that
    /// clause, sorted.
    pub(super) ready: Vec<u64>,
    pub(super) ready_for: Vec<Literal>,
    /// Derived additions written with hints, and written plain although
    /// antecedents were named.
    pub(super) hinted: u64,
    pub(super) plain: u64,
    /// Additions written as `red` (no hints: no antecedents named, or they did
    /// not refute the clause), by diagnostic pass. Each costs the official
    /// check a scan of the database, and the proved kernel cannot compose
    /// through one whose witness touches it.
    pub(super) red_by_pass: [u64; DiagnosticPass::BY_CODE.len()],
}

impl VeripbDerivedState {
    /// Admission for the trace-only root materializer. Pending antecedents
    /// select a real proving walk even when no external writer is attached.
    pub(in crate::solver) fn has_pending_emission(&self) -> bool {
        !self.ready.is_empty() || !self.ends.is_empty()
    }

    fn set_true(&mut self, lit: Literal) {
        let i = lit.index();
        if !self.truth[i] {
            self.truth[i] = true;
            self.touched.push(i);
        }
    }

    fn value(&self, lit: Literal) -> Option<bool> {
        if self.truth[lit.index()] {
            Some(true)
        } else if self.truth[lit.negated().index()] {
            Some(false)
        } else {
            None
        }
    }

    fn reset(&mut self) {
        for &i in &self.touched {
            self.truth[i] = false;
        }
        self.touched.clear();
        self.lits.clear();
        self.ends.clear();
    }
}

impl Solver {
    fn veripb_root_false(&self, lit: Literal) -> bool {
        let v = lit.variable().index();
        v < self.num_vars && self.var_data[v].level == 0 && self.lit_val(lit) < 0
    }

    /// Name clause `lits` (internal literals) as an antecedent of the next
    /// derived proof addition.
    pub(super) fn veripb_note_antecedent(&mut self, lits: &[Literal]) {
        if !self.veripb_hints_active() {
            return;
        }
        let derived = &mut self.cold.veripb_hints.derived;
        if derived.lits.len() + lits.len() > VERIPB_DERIVED_MAX_LITS {
            derived.lits.clear();
            derived.ends.clear();
            return;
        }
        derived.lits.extend_from_slice(lits);
        derived.ends.push(derived.lits.len());
    }

    /// `veripb_note_antecedent` for an arena clause (read even if it is
    /// already marked garbage: its proof copy is looked up by content).
    pub(super) fn veripb_note_antecedent_ref(&mut self, clause: ClauseRef) {
        if !self.veripb_hints_active() {
            return;
        }
        let lits = self.arena.literals_or_deleted(clause.0 as usize);
        let derived = &mut self.cold.veripb_hints.derived;
        if derived.lits.len() + lits.len() > VERIPB_DERIVED_MAX_LITS {
            derived.lits.clear();
            derived.ends.clear();
            return;
        }
        derived.lits.extend_from_slice(lits);
        derived.ends.push(derived.lits.len());
    }

    /// Write derived clause `clause` (internal literals; `proof_clause` is its
    /// proof-surface form) as annotated RUP: with the ids made ready for it,
    /// or over the antecedents named since the last addition. `None` when
    /// neither applies or the antecedents do not refute its negation: the
    /// caller writes the step plain. Both are consumed either way.
    pub(super) fn veripb_emit_derived_hinted(
        &mut self,
        clause: &[Literal],
        proof_clause: &[Literal],
    ) -> Option<io::Result<()>> {
        if !self.cold.veripb_hints.derived.ready.is_empty() {
            let derived = &mut self.cold.veripb_hints.derived;
            derived.scratch.clear();
            derived.scratch.extend_from_slice(clause);
            derived.scratch.sort_unstable_by_key(|lit| lit.0);
            let ready_for_clause = derived.scratch == derived.ready_for;
            let ids = std::mem::take(&mut derived.ready);
            derived.ready_for.clear();
            if ready_for_clause {
                derived.lits.clear();
                derived.ends.clear();
                let result = self
                    .proof_manager
                    .as_mut()
                    .map(|manager| manager.emit_add_veripb_rup(proof_clause, &ids));
                if result.is_some() {
                    self.cold.veripb_hints.derived.hinted += 1;
                }
                return result;
            }
        }
        if self.cold.veripb_hints.derived.ends.is_empty() {
            return None;
        }
        let mut st = std::mem::take(&mut self.cold.veripb_hints);
        let mut derived = std::mem::take(&mut st.derived);
        let refuted = self.veripb_derived_refutation(&mut st, &mut derived, clause);
        derived.reset();
        let result = if refuted {
            self.proof_manager
                .as_mut()
                .map(|manager| manager.emit_add_veripb_rup(proof_clause, &derived.ids))
        } else {
            None
        };
        if result.is_some() {
            derived.hinted += 1;
        } else {
            derived.plain += 1;
        }
        st.derived = derived;
        self.cold.veripb_hints = st;
        result
    }

    /// Decompose: for every literal of an equivalence class, the next literal
    /// on a binary implication path to its representative (`u32::MAX` for a
    /// representative and for a literal in no class). One reverse
    /// breadth-first search per class from its representative, over the
    /// binary watches the classes were found in, restricted to the class:
    /// linear in the classes' binary edges, with two buffers for all of them.
    pub(super) fn veripb_decompose_hops(&mut self, reprs: &[Literal]) -> Option<Vec<u32>> {
        if !self.veripb_hints_active() {
            return None;
        }
        let n = reprs.len();
        let mut next = vec![u32::MAX; n];
        let mut seen = vec![false; n];
        let mut queue: Vec<Literal> = Vec::new();
        for i in 0..n {
            let r = reprs[i];
            if r.index() == i || r.index() >= n || seen[r.index()] {
                continue;
            }
            seen[r.index()] = true;
            queue.clear();
            queue.push(r);
            let mut head = 0;
            while head < queue.len() {
                let v = queue[head];
                head += 1;
                // A binary (v ∨ b) in v's list is the edge ¬b → v.
                for k in 0..self.watches.binary_count_of(v) {
                    let u = Literal(entry_blocker_raw(self.watches.entry_raw(v, k))).negated();
                    let ui = u.index();
                    if ui < n && !seen[ui] && reprs[ui] == r {
                        seen[ui] = true;
                        next[ui] = v.0;
                        queue.push(u);
                    }
                }
            }
        }
        Some(next)
    }

    /// Sweep: for each literal a with an equivalence binary (¬a ∨ b) among
    /// `binaries` (those `emit_sweep_proof_facts` left in the proof), b, one
    /// step toward a's representative; `u32::MAX` elsewhere. The paths
    /// `veripb_note_substitution` follows (`None` when annotated RUP is off).
    pub(super) fn veripb_sweep_hops(&mut self, binaries: &[Vec<Literal>]) -> Option<Vec<u32>> {
        if !self.veripb_hints_active() {
            return None;
        }
        let mut next = vec![u32::MAX; 2 * self.num_vars];
        for binary in binaries {
            if let [x, y] = binary.as_slice() {
                if let Some(slot) = next.get_mut(x.negated().index()) {
                    if *slot == u32::MAX {
                        *slot = y.0;
                    }
                }
            }
        }
        Some(next)
    }

    /// Name the antecedents of a clause decompose or sweep rewrote from `old`:
    /// `old` itself and, for each literal it replaced, the binaries on the path
    /// from that literal to its representative (`veripb_decompose_hops`,
    /// `veripb_sweep_hops`; `None` when annotated RUP is off).
    pub(super) fn veripb_note_substitution(
        &mut self,
        old: &[Literal],
        reprs: &[Literal],
        next: &Option<Vec<u32>>,
    ) {
        let Some(next) = next else {
            return;
        };
        self.veripb_note_antecedent(old);
        for &u in old {
            let Some(&r) = reprs.get(u.index()) else {
                continue;
            };
            let mut w = u;
            let mut steps = 0;
            while w != r && steps < next.len() {
                let v = next[w.index()];
                if v == u32::MAX {
                    break;
                }
                self.veripb_note_antecedent(&[w.negated(), Literal(v)]);
                w = Literal(v);
                steps += 1;
            }
        }
    }

    /// Name the antecedents of factoring's quotient `quot` = (¬x ∨ Q): the
    /// proof-only blocked clause (¬x ∨ ¬f1 ∨ … ∨ ¬fk) and each factored clause
    /// (fi ∨ Q) it replaces.
    pub(super) fn veripb_note_factor_quotient(
        &mut self,
        quot: &[Literal],
        blocked: &[Literal],
        factors: &[Literal],
    ) {
        if quot.is_empty() || !self.veripb_hints_active() {
            return;
        }
        self.veripb_note_antecedent(blocked);
        let mut factored = Vec::with_capacity(quot.len());
        for &f in factors {
            factored.clear();
            factored.push(f);
            factored.extend_from_slice(&quot[1..]);
            self.veripb_note_antecedent(&factored);
        }
    }

    /// Name the antecedents of lemma `k` of a kitten core: an environment
    /// clause by the arena index it was given to kitten as its id, an earlier
    /// lemma by content (it was added to the proof before this one).
    pub(super) fn veripb_note_core_antecedents(&mut self, core: &CoreLemmas, k: usize) {
        if !self.veripb_hints_active() {
            return;
        }
        let Some(antecedents) = core.antecedents.get(k) else {
            return;
        };
        // Kitten records them in analysis order (the conflict first, then each
        // reason in reverse trail order); named in reverse, the refutation
        // check meets each reason after the ones it rests on and needs one pass.
        for &ante in antecedents.iter().rev() {
            match ante {
                CoreAntecedent::Original(id) if (id as usize) < self.arena.len() => {
                    self.veripb_note_antecedent_ref(ClauseRef(id));
                }
                CoreAntecedent::Original(_) => {}
                CoreAntecedent::Lemma(j) => {
                    if let Some(lemma) = core.lemmas.get(j as usize) {
                        let lits: Vec<Literal> = lemma.iter().map(|&l| Literal(l)).collect();
                        self.veripb_note_antecedent(&lits);
                    }
                }
            }
        }
    }

    /// Name every lemma of a kitten core, or its root environment clause when
    /// the core learned nothing: the fact the core certifies is RUP over them
    /// (its failing clause subsumes the fact).
    pub(super) fn veripb_note_core_lemmas(&mut self, core: &CoreLemmas) {
        if !self.veripb_hints_active() {
            return;
        }
        if let Some(id) = core.root_original {
            if (id as usize) < self.arena.len() {
                self.veripb_note_antecedent_ref(ClauseRef(id));
            }
        }
        for lemma in core.lemmas.iter().filter(|lemma| !lemma.is_empty()) {
            let lits: Vec<Literal> = lemma.iter().map(|&l| Literal(l)).collect();
            self.veripb_note_antecedent(&lits);
        }
    }

    /// Name the antecedents of a unit BVE derived from a variable's
    /// definition, or of a lifted core lemma added before it: the variable's
    /// occurrences (arena clauses) and the lemmas `lemmas` already added.
    pub(super) fn veripb_note_occurrences(
        &mut self,
        pos: &[usize],
        neg: &[usize],
        lemmas: &[Vec<Literal>],
    ) {
        if !self.veripb_hints_active() {
            return;
        }
        for &idx in pos.iter().chain(neg) {
            self.veripb_note_antecedent_ref(ClauseRef(idx as u32));
        }
        for lemma in lemmas {
            self.veripb_note_antecedent(lemma);
        }
    }

    /// Drop antecedents named (and ids made ready) for an addition that is not
    /// a derivation.
    pub(super) fn veripb_drop_antecedents(&mut self) {
        let derived = &mut self.cold.veripb_hints.derived;
        derived.lits.clear();
        derived.ends.clear();
        derived.ready.clear();
        derived.ready_for.clear();
    }

    /// Fill `derived.ids` with constraints that refute the negation of
    /// `clause` by unit propagation alone: the named antecedents in the order
    /// they became unit, ending with the one that became false, each preceded
    /// by unit constraints for the root-false literals it relies on (a
    /// root-false literal counts as false; its unit is stated only when an
    /// antecedent that is used needs it). `false` when no such list exists.
    fn veripb_derived_refutation(
        &mut self,
        st: &mut VeripbHintState,
        derived: &mut VeripbDerivedState,
        clause: &[Literal],
    ) -> bool {
        // Factoring writes its steps before its fresh variable is registered,
        // so the literals present can reach past `num_vars`.
        let lits_needed = clause
            .iter()
            .chain(derived.lits.iter())
            .map(|lit| 2 * (lit.variable().index() + 1))
            .fold(2 * self.num_vars, usize::max);
        if derived.truth.len() < lits_needed {
            derived.truth.resize(lits_needed, false);
        }
        derived.ids.clear();
        for &lit in clause {
            if derived.value(lit) == Some(true) {
                return false;
            }
            derived.set_true(lit.negated());
        }
        let n = derived.ends.len();
        derived.done.clear();
        derived.done.resize(n, false);
        loop {
            let mut progress = false;
            for i in 0..n {
                if derived.done[i] {
                    continue;
                }
                let start = if i == 0 { 0 } else { derived.ends[i - 1] };
                let end = derived.ends[i];
                let mut open = None;
                let mut open_count = 0;
                let mut satisfied = false;
                derived.roots.clear();
                for &lit in &derived.lits[start..end] {
                    match derived.value(lit) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None if self.veripb_root_false(lit) => derived.roots.push(lit),
                        None => {
                            open_count += 1;
                            open = Some(lit);
                        }
                    }
                }
                if satisfied {
                    // Stays satisfied: the assignment only grows.
                    derived.done[i] = true;
                    continue;
                }
                if open_count > 1 {
                    continue;
                }
                // Unit constraints only for the root-false literals an
                // antecedent that is used relies on, written before it.
                for r in 0..derived.roots.len() {
                    let lit = derived.roots[r];
                    if derived.value(lit).is_none() {
                        let Some(id) = self.veripb_unit_id(st, lit.negated()) else {
                            return false;
                        };
                        derived.ids.push(id);
                        derived.set_true(lit.negated());
                    }
                }
                derived.scratch.clear();
                derived.scratch.extend_from_slice(&derived.lits[start..end]);
                let Some(id) = self.veripb_constraint_id_of(&mut derived.scratch) else {
                    return false;
                };
                derived.ids.push(id);
                derived.done[i] = true;
                match open {
                    None => return true,
                    Some(lit) => derived.set_true(lit),
                }
                progress = true;
            }
            if !progress {
                return false;
            }
        }
    }
}
