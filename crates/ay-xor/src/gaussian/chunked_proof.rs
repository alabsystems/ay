// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tseitin-chunked DRAT ladders for wide-XOR refutations (task #20 follow-up).
//!
//! The monolithic resolution ladder in `gaussian.rs` costs
//! `2^(result-1) * (2^(cancelled+1) - 1)` clauses per elimination step, which
//! is certifiable only for narrow traces (`MAX_XOR_PROOF_ROW_VARS`,
//! `MAX_XOR_PROOF_TOTAL_CLAUSES`). This module certifies the general case in
//! LINEAR clause count per step by representing every derived row as a
//! sequential parity chain over fresh DRAT extension variables:
//!
//! * A row `y1 ^ ... ^ yw = c` gets aux vars `s_2..s_w` with XOR definitions
//!   `s_2 <-> y1^y2`, `s_i <-> s_{i-1}^y_i` (4 clauses each, RAT on the
//!   fresh variable, which is emitted FIRST in each clause — external DRAT
//!   checkers resolve RAT on the first literal), plus a derived terminal
//!   unit `s_w = c`. Any full wrong-parity assignment of the row's variables
//!   then refutes by unit propagation through the chain, which is exactly
//!   what derived-row conflict and reason clauses need to be RUP.
//! * An ORIGINAL row's terminal unit is derived from its input CNF encoding
//!   by a "rotation" ladder: `R_i = enc(s_i ^ y_{i+1} ^ ... ^ y_w = c)`
//!   walks from `R_1 = enc(row)` (the consumed input clause group) to
//!   `R_w = [s_w = c]`, costing `3 * (2^(w-1) - 1)` clauses. Original rows
//!   are input constraints (width <= `MAX_XOR_PROOF_ROW_VARS` enforced,
//!   tiny in practice) — derived rows are NEVER converted this way.
//! * A DERIVED row `C = A ^ B` derives its terminal unit from its parents'
//!   chains by a position ladder over `U = vars(A) u vars(B)` in ascending
//!   variable order: after each prefix, the lemma
//!   `enc(c_sum ^ a_sum ^ b_sum = 0)` over the three current partial-sum
//!   variables is derived from the previous lemma plus the chain definition
//!   clauses (at most 12 clauses per position: 8 two-way expansions over the
//!   new variable and 4 lemma clauses). The final lemma plus the parents'
//!   terminal units yields C's terminal unit — or the EMPTY clause when C
//!   is the `0 = 1` row.
//!
//! Exhausted intermediates (expansions, superseded lemmas, rotation levels)
//! are deleted with DRAT `d`-lines immediately after use, so the external
//! checker's live set stays near the chain definitions + terminal units.
//! Everything here is emitted PROOF-ONLY (`ExtProofStep`): fresh variables
//! never reach the solver's clause database, search state, or models.
//!
//! The whole scheme was validated end-to-end against `dsr-trim` (rc 0,
//! `s VERIFIED UNSAT`) on a hand-built micro proof before implementation:
//! extension variables, pivot-first RAT XOR definitions, rotation ladders,
//! position ladders, and `d`-lines are all accepted.

use ay_sat::Literal;

use super::{GaussianSolver, MAX_XOR_PROOF_ROW_VARS};
use crate::packed_row::PackedRow;
use crate::VarId;
use ay_sat::{ExtProofStep, Variable};

/// Aggregate addition budget for a chunked trace. Chunked clauses carry at
/// most five literals (vs up to `MAX_XOR_PROOF_ROW_VARS` for monolithic
/// ladder clauses), and intermediates are deleted eagerly, so the budget is
/// sized by proof-file volume rather than checker live-set: 1<<25 additions
/// is roughly 600 MB of text DRAT. The lightsout_sat "direct" family fits
/// (~2e7); its "totalizer" siblings (~5e8+) are rejected and fall through
/// exactly like today.
pub(crate) const MAX_XOR_CHUNKED_PROOF_TOTAL_CLAUSES: u64 = 1 << 25;

/// Provenance of a matrix row: an input constraint or an elimination step.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ParentRef {
    /// `initial_rows[i]` — an original XOR constraint of this component.
    Original(u32),
    /// `elimination_trace[j].result`.
    Step(u32),
}

/// Preflighted chunked-emission plan for one component.
#[derive(Debug)]
pub(crate) struct ChunkedProofPlan {
    /// Per trace step: provenance of `[parent_a, parent_b]`.
    step_parents: Vec<[ParentRef; 2]>,
    /// Per final RREF row: provenance of its content.
    row_source: Vec<ParentRef>,
    /// Exact worst-case addition count (every step + every referenced
    /// original), used for the aggregate budget. Lazy cone emission at
    /// runtime emits a subset of this.
    pub(crate) total_additions: u64,
}

/// A row's emitted parity chain: `first` is the row's smallest variable
/// (partial sum of width 1), `aux[i]` is the fresh sum variable covering the
/// first `i + 2` row variables. Terminal = last aux (or `first` if width 1).
#[derive(Debug, Clone)]
struct ChainRec {
    first: VarId,
    aux: Vec<VarId>,
}

impl ChainRec {
    fn term(&self) -> VarId {
        self.aux.last().copied().unwrap_or(self.first)
    }
}

/// Current partial-sum variable of a chain during the position walk.
///
/// `Aux(uid, count)` names "chain `uid` after `count` variables" WITHOUT
/// resolving the concrete aux variable, so the same walk drives both the
/// counting preflight (no allocation) and real emission (resolved through
/// the chain registry). Equality is exact: aux variables of different chains
/// are always distinct, and width-1 prefixes alias their concrete variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum CurKey {
    Concrete(VarId),
    Aux(u32, u32),
}

/// Sink driven by the shared position walk. `CountSink` computes the exact
/// addition count; `EmitSink` builds the proof script. A debug assertion in
/// the emitter pins the two to the same per-position formula.
trait StepSink {
    /// Result-chain definitions (`4 * (rl - 1)` additions when `rl >= 2`).
    fn begin_step(&mut self, vars_c: &[VarId], uid_c: u32);
    /// One position with a NEW lemma over `m_new` (`(3 or 1) * 2^(|m|-1)`
    /// additions: two-way expansions over `u` unless `u` is in the lemma).
    fn position(&mut self, m_new: &[CurKey], u: VarId, expanded: bool);
    /// The lemma trivialized (cancelled empty): retire the previous one.
    fn drop_lemma(&mut self);
    /// Terminal unit (1 addition; the EMPTY clause for the `0 = 1` row,
    /// nothing for a trivially-zero row).
    fn finish(&mut self, rl: usize, rhs_c: bool);
}

struct CountSink {
    additions: u64,
}

impl StepSink for CountSink {
    fn begin_step(&mut self, vars_c: &[VarId], _uid_c: u32) {
        if vars_c.len() >= 2 {
            self.additions += 4 * (vars_c.len() as u64 - 1);
        }
    }

    fn position(&mut self, m_new: &[CurKey], _u: VarId, expanded: bool) {
        let per_assignment: u64 = if expanded { 3 } else { 1 };
        self.additions += per_assignment << (m_new.len() - 1);
    }

    fn drop_lemma(&mut self) {}

    fn finish(&mut self, rl: usize, rhs_c: bool) {
        if rl > 0 || rhs_c {
            self.additions += 1;
        }
    }
}

/// Blocking literal for the assignment `var = value` (negative literal
/// blocks TRUE, matching the monolithic ladder's convention).
fn blocking_lit(var: VarId, value: bool) -> Literal {
    let v = Variable::new(var);
    if value {
        Literal::negative(v)
    } else {
        Literal::positive(v)
    }
}

struct EmitSink<'a> {
    chains: &'a mut [Option<ChainRec>],
    next_fresh: &'a mut VarId,
    out: &'a mut Vec<ExtProofStep>,
    /// Clauses of the current lemma, retired (deleted) when superseded.
    last_lemma: Vec<Vec<Literal>>,
    uid_c: u32,
    /// Set when a chain reference could not be resolved (a provenance bug).
    /// Further emission for the step is suppressed; the resulting proof is
    /// incomplete, which an external checker REJECTS — it never accepts a
    /// wrong one.
    abandoned: bool,
}

impl EmitSink<'_> {
    /// Resolve a walk key to its concrete variable, or `None` when the
    /// referenced chain is absent — a provenance bug. Emission then STOPS
    /// (`abandoned`) rather than writing scaffolding over the wrong
    /// variables: an incomplete certificate makes the external checker fail
    /// closed, a wrong one would not.
    fn resolve(&mut self, key: CurKey) -> Option<VarId> {
        match key {
            CurKey::Concrete(v) => Some(v),
            CurKey::Aux(uid, count) => {
                let resolved = self.chains[uid as usize]
                    .as_ref()
                    .and_then(|chain| chain.aux.get(count as usize - 2).copied());
                if resolved.is_none() {
                    debug_assert!(false, "walker referenced a chain before its emission");
                    self.abandoned = true;
                }
                resolved
            }
        }
    }

    fn alloc(&mut self) -> VarId {
        let v = *self.next_fresh;
        *self.next_fresh += 1;
        v
    }

    fn delete_last_lemma(&mut self) {
        for clause in std::mem::take(&mut self.last_lemma) {
            self.out.push(ExtProofStep::Delete(clause));
        }
    }

    /// Emit a fresh chain (aux allocation + XOR definition clauses, RAT on
    /// the fresh variable which is FIRST in every definition clause) and
    /// register it under `uid`. No-op emission for widths 0/1.
    fn emit_chain(&mut self, uid: u32, vars: &[VarId]) {
        debug_assert!(self.chains[uid as usize].is_none());
        let Some((&first, rest)) = vars.split_first() else {
            return; // width 0: no chain
        };
        let mut aux = Vec::with_capacity(rest.len());
        let mut prev = first;
        for &v in rest {
            let s = self.alloc();
            // enc(s ^ prev ^ v = 0): block the four assignments with
            // s != prev ^ v. Pivot (the fresh variable) first.
            for bits in 0u8..8 {
                let (sv, pv, vv) = (bits & 1 != 0, bits & 2 != 0, bits & 4 != 0);
                if sv == (pv ^ vv) {
                    continue;
                }
                self.out.push(ExtProofStep::Add(vec![
                    blocking_lit(s, sv),
                    blocking_lit(prev, pv),
                    blocking_lit(v, vv),
                ]));
            }
            aux.push(s);
            prev = s;
        }
        self.chains[uid as usize] = Some(ChainRec { first, aux });
    }
}

impl StepSink for EmitSink<'_> {
    fn begin_step(&mut self, vars_c: &[VarId], uid_c: u32) {
        self.uid_c = uid_c;
        self.emit_chain(uid_c, vars_c);
    }

    fn position(&mut self, m_new: &[CurKey], u: VarId, expanded: bool) {
        if self.abandoned {
            return;
        }
        let mut m_vars: Vec<VarId> = Vec::with_capacity(m_new.len());
        for &key in m_new {
            let Some(var) = self.resolve(key) else {
                return; // `resolve` latched `abandoned`
            };
            m_vars.push(var);
        }
        let n = m_vars.len();
        let mut new_lemma: Vec<Vec<Literal>> = Vec::with_capacity(1 << (n - 1));
        let mut exps: Vec<Vec<Literal>> = Vec::new();
        for assign in 0u32..(1 << n) {
            if assign.count_ones() % 2 == 0 {
                continue; // right parity for enc(sum = 0): not blocked
            }
            let base: Vec<Literal> = m_vars
                .iter()
                .enumerate()
                .map(|(bit, &var)| blocking_lit(var, (assign >> bit) & 1 == 1))
                .collect();
            if expanded {
                for value in [false, true] {
                    let mut exp = base.clone();
                    exp.push(blocking_lit(u, value));
                    self.out.push(ExtProofStep::Add(exp.clone()));
                    exps.push(exp);
                }
            }
            self.out.push(ExtProofStep::Add(base.clone()));
            new_lemma.push(base);
        }
        debug_assert_eq!(
            (new_lemma.len() + exps.len()) as u64,
            (if expanded { 3u64 } else { 1 }) << (n - 1),
            "emission diverged from the counting formula"
        );
        for exp in exps {
            self.out.push(ExtProofStep::Delete(exp));
        }
        self.delete_last_lemma();
        self.last_lemma = new_lemma;
    }

    fn drop_lemma(&mut self) {
        self.delete_last_lemma();
    }

    fn finish(&mut self, rl: usize, rhs_c: bool) {
        if self.abandoned {
            self.delete_last_lemma();
            return;
        }
        if rl == 0 {
            if rhs_c {
                // The 0 = 1 row: the final lemma plus the parents' terminal
                // units derive the EMPTY clause.
                self.out.push(ExtProofStep::Add(Vec::new()));
            }
        } else if let Some(term) = self.chains[self.uid_c as usize]
            .as_ref()
            .map(ChainRec::term)
        {
            self.out
                .push(ExtProofStep::Add(vec![blocking_lit(term, !rhs_c)]));
        } else {
            debug_assert!(false, "nonzero result row must have a chain");
        }
        self.delete_last_lemma();
    }
}

/// Compare two <= 3-element lemma var multisets ignoring order.
fn multiset_eq(a: &[CurKey], b: &[CurKey]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut x: Vec<CurKey> = a.to_vec();
    let mut y: Vec<CurKey> = b.to_vec();
    x.sort_unstable();
    y.sort_unstable();
    x == y
}

struct WalkChain<'a> {
    vars: &'a [VarId],
    uid: u32,
    count: usize,
}

impl WalkChain<'_> {
    fn cur(&self) -> Option<CurKey> {
        match self.count {
            0 => None,
            1 => Some(CurKey::Concrete(self.vars[0])),
            n => Some(CurKey::Aux(self.uid, n as u32)),
        }
    }
}

/// Shared position walk for one derived step `C = A ^ B`.
///
/// `uids = [uid_c, uid_a, uid_b]`. Variable lists are ascending; `vars_c`
/// must be the symmetric difference of `vars_a` and `vars_b`.
fn walk_step<S: StepSink>(
    vars_a: &[VarId],
    vars_b: &[VarId],
    vars_c: &[VarId],
    rhs_c: bool,
    uids: [u32; 3],
    sink: &mut S,
) {
    sink.begin_step(vars_c, uids[0]);
    let mut c = WalkChain {
        vars: vars_c,
        uid: uids[0],
        count: 0,
    };
    let mut a = WalkChain {
        vars: vars_a,
        uid: uids[1],
        count: 0,
    };
    let mut b = WalkChain {
        vars: vars_b,
        uid: uids[2],
        count: 0,
    };
    let mut prev_m: Vec<CurKey> = Vec::new();
    let (mut ia, mut ib) = (0usize, 0usize);
    while ia < vars_a.len() || ib < vars_b.len() {
        let next_a = vars_a.get(ia);
        let next_b = vars_b.get(ib);
        let (u, in_a, in_b) = match (next_a, next_b) {
            (Some(&va), Some(&vb)) if va == vb => (va, true, true),
            (Some(&va), Some(&vb)) if va < vb => (va, true, false),
            (Some(&va), None) => (va, true, false),
            (_, Some(&vb)) => (vb, false, true),
            (None, None) => unreachable!("loop condition"),
        };
        if in_a {
            ia += 1;
            a.count += 1;
        }
        if in_b {
            ib += 1;
            b.count += 1;
        }
        if in_a ^ in_b {
            c.count += 1;
            debug_assert_eq!(vars_c.get(c.count - 1), Some(&u), "vars_c is not A xor B");
        }
        let mut m_new: Vec<CurKey> = Vec::with_capacity(3);
        for key in [c.cur(), a.cur(), b.cur()].into_iter().flatten() {
            // XOR-cancel identical partial sums (shared alias variables).
            if let Some(pos) = m_new.iter().position(|&k| k == key) {
                m_new.remove(pos);
            } else {
                m_new.push(key);
            }
        }
        if multiset_eq(&m_new, &prev_m) {
            continue; // lemma unchanged (e.g. two chains aliasing the same var)
        }
        if m_new.is_empty() {
            sink.drop_lemma();
            prev_m = m_new;
            continue;
        }
        let expanded = !m_new.contains(&CurKey::Concrete(u));
        sink.position(&m_new, u, expanded);
        prev_m = m_new;
    }
    debug_assert_eq!(c.count, vars_c.len(), "vars_c is not A xor B");
    sink.finish(vars_c.len(), rhs_c);
}

/// Sorted variable list of a packed row (column order equals ascending
/// variable-id order by construction of `col_to_var`).
fn row_vars(solver: &GaussianSolver, row: &PackedRow) -> Vec<VarId> {
    row.iter_set_bits().map(|c| solver.col_to_var[c]).collect()
}

fn uid_of(parent: ParentRef, n_orig: usize) -> u32 {
    match parent {
        ParentRef::Original(i) => i,
        ParentRef::Step(j) => n_orig as u32 + j,
    }
}

/// Exact rotation-conversion cost for an original row of width `w`
/// (definitions + ladder), or `None` outside the certified width envelope.
fn rotation_cost(w: usize) -> Option<u64> {
    if w > MAX_XOR_PROOF_ROW_VARS {
        return None;
    }
    if w < 2 {
        return Some(0);
    }
    Some(4 * (w as u64 - 1) + 3 * ((1u64 << (w - 1)) - 1))
}

impl GaussianSolver {
    /// Build the chunked proof plan for this component's elimination trace,
    /// or `None` when the trace cannot be chunk-certified (an original row
    /// wider than the rotation envelope, or the exact worst-case addition
    /// count exceeding `MAX_XOR_CHUNKED_PROOF_TOTAL_CLAUSES`).
    pub(crate) fn build_chunked_proof_plan(&self) -> Option<ChunkedProofPlan> {
        let n_rows = self.rows.len();
        if self.initial_rows.len() != n_rows {
            return None; // eliminate() has not run
        }
        let n_orig = n_rows;

        // Replay recorded pivot swaps to recover exact row provenance.
        let mut prov: Vec<ParentRef> = (0..n_rows).map(|i| ParentRef::Original(i as u32)).collect();
        let mut swaps = self.elimination_swaps.iter().peekable();
        let mut step_parents = Vec::with_capacity(self.elimination_trace.len());
        let mut needed_orig = vec![false; n_rows];
        for (j, step) in self.elimination_trace.iter().enumerate() {
            while let Some(&&(x, y, watermark)) = swaps.peek() {
                if (watermark as usize) <= j {
                    prov.swap(x as usize, y as usize);
                    swaps.next();
                } else {
                    break;
                }
            }
            let pa = prov[step.pivot_pos as usize];
            let pb = prov[step.target_pos as usize];
            for p in [pa, pb] {
                if let ParentRef::Original(i) = p {
                    needed_orig[i as usize] = true;
                }
            }
            step_parents.push([pa, pb]);
            prov[step.target_pos as usize] = ParentRef::Step(j as u32);
        }
        for &(x, y, _) in swaps {
            prov.swap(x as usize, y as usize);
        }
        let row_source = prov;

        // Exact worst-case cost: every referenced original's rotation plus
        // every step's chunked ladder.
        let mut total: u64 = 0;
        for (i, row) in self.initial_rows.iter().enumerate() {
            if !needed_orig[i] {
                continue;
            }
            total = total.checked_add(rotation_cost(row.iter_set_bits().count())?)?;
        }
        for (j, step) in self.elimination_trace.iter().enumerate() {
            let vars_a = row_vars(self, &step.parent_a);
            let vars_b = row_vars(self, &step.parent_b);
            let vars_c = row_vars(self, &step.result);
            let uids = [
                uid_of(ParentRef::Step(j as u32), n_orig),
                uid_of(step_parents[j][0], n_orig),
                uid_of(step_parents[j][1], n_orig),
            ];
            let mut count = CountSink { additions: 0 };
            walk_step(&vars_a, &vars_b, &vars_c, step.result.rhs, uids, &mut count);
            total = total.checked_add(count.additions)?;
            if total > MAX_XOR_CHUNKED_PROOF_TOTAL_CLAUSES {
                return None;
            }
        }

        Some(ChunkedProofPlan {
            step_parents,
            row_source,
            total_additions: total,
        })
    }

    /// Plan plus fresh per-run emission state for chunked proofs.
    pub(crate) fn build_chunked_component_state(&self) -> Option<ChunkedComponentState> {
        let plan = self.build_chunked_proof_plan()?;
        let n_orig = self.initial_rows.len();
        let n_steps = self.elimination_trace.len();
        Some(ChunkedComponentState {
            plan,
            step_emitted: vec![false; n_steps],
            orig_emitted: vec![false; n_orig],
            chains: vec![None; n_orig + n_steps],
            n_orig,
        })
    }
}

/// Mutable chunked-emission state for one component: which trace steps and
/// original rows have had their scaffolding emitted (latched — each row is
/// emitted at most once per run), and the registry of emitted chains.
#[derive(Debug)]
pub(crate) struct ChunkedComponentState {
    plan: ChunkedProofPlan,
    step_emitted: Vec<bool>,
    orig_emitted: Vec<bool>,
    chains: Vec<Option<ChainRec>>,
    n_orig: usize,
}

impl ChunkedComponentState {
    pub(crate) fn total_additions(&self) -> u64 {
        self.plan.total_additions
    }

    /// Emit the not-yet-emitted derivation cone of a final RREF row, so a
    /// conflict or reason clause built from that row is RUP. Original rows
    /// need nothing (their input encodings are present in the CNF).
    pub(crate) fn emit_row_cone(
        &mut self,
        solver: &GaussianSolver,
        local_row: usize,
        next_fresh: &mut VarId,
        out: &mut Vec<ExtProofStep>,
    ) {
        match self.plan.row_source.get(local_row) {
            Some(&ParentRef::Step(j)) => self.emit_step_cone(solver, j as usize, next_fresh, out),
            Some(&ParentRef::Original(_)) | None => {}
        }
    }

    /// Iterative post-order DFS over unemitted ancestor steps.
    fn emit_step_cone(
        &mut self,
        solver: &GaussianSolver,
        root: usize,
        next_fresh: &mut VarId,
        out: &mut Vec<ExtProofStep>,
    ) {
        if self.step_emitted[root] {
            return;
        }
        let mut stack: Vec<(usize, bool)> = vec![(root, false)];
        while let Some((j, parents_done)) = stack.pop() {
            if self.step_emitted[j] {
                continue;
            }
            if parents_done {
                self.emit_one_step(solver, j, next_fresh, out);
                self.step_emitted[j] = true;
                continue;
            }
            stack.push((j, true));
            for parent in self.plan.step_parents[j] {
                match parent {
                    ParentRef::Step(p) => {
                        if !self.step_emitted[p as usize] {
                            stack.push((p as usize, false));
                        }
                    }
                    ParentRef::Original(i) => {
                        self.ensure_original(solver, i as usize, next_fresh, out);
                    }
                }
            }
        }
    }

    /// Emit an original row's chain: definitions plus the rotation ladder
    /// deriving its terminal unit from the consumed input clause group.
    fn ensure_original(
        &mut self,
        solver: &GaussianSolver,
        idx: usize,
        next_fresh: &mut VarId,
        out: &mut Vec<ExtProofStep>,
    ) {
        if self.orig_emitted[idx] {
            return;
        }
        self.orig_emitted[idx] = true;
        let row = &solver.initial_rows[idx];
        let vars = row_vars(solver, row);
        let rhs = row.rhs;
        let uid = idx as u32;
        let mut sink = EmitSink {
            chains: &mut self.chains,
            next_fresh,
            out,
            last_lemma: Vec::new(),
            uid_c: uid,
            abandoned: false,
        };
        sink.emit_chain(uid, &vars);
        let w = vars.len();
        if w < 2 {
            // Width 1: the input unit clause IS the terminal. Width 0: the
            // input already contains the row's encoding (the empty clause).
            return;
        }
        let Some(chain_aux) = sink.chains[uid as usize]
            .as_ref()
            .map(|chain| chain.aux.clone())
        else {
            // `emit_chain` registers every width >= 2 row; a miss is a bug.
            // Emit nothing further — the checker then fails closed.
            debug_assert!(false, "emit_chain must register a width >= 2 chain");
            return;
        };
        // Level 1 is the input clause group (present, never deleted).
        let mut prev_level: Vec<Vec<Literal>> = Vec::new();
        for i in 2..=w {
            let s = chain_aux[i - 2];
            let y = vars[i - 1];
            let suffix = &vars[i..];
            let mut level: Vec<Vec<Literal>> = Vec::with_capacity(1 << suffix.len());
            let mut exps: Vec<Vec<Literal>> = Vec::with_capacity(2 << suffix.len());
            for assign in 0u32..(2 << suffix.len()) {
                let s_val = assign & 1 == 1;
                let mut parity = s_val;
                let suffix_lits: Vec<Literal> = suffix
                    .iter()
                    .enumerate()
                    .map(|(bit, &var)| {
                        let value = (assign >> (bit + 1)) & 1 == 1;
                        parity ^= value;
                        blocking_lit(var, value)
                    })
                    .collect();
                if parity == rhs {
                    continue; // right parity: not blocked
                }
                let mut base = Vec::with_capacity(1 + suffix_lits.len());
                base.push(blocking_lit(s, s_val));
                base.extend_from_slice(&suffix_lits);
                for value in [false, true] {
                    let mut exp = Vec::with_capacity(base.len() + 1);
                    exp.push(base[0]);
                    exp.push(blocking_lit(y, value));
                    exp.extend_from_slice(&base[1..]);
                    sink.out.push(ExtProofStep::Add(exp.clone()));
                    exps.push(exp);
                }
                sink.out.push(ExtProofStep::Add(base.clone()));
                level.push(base);
            }
            for exp in exps {
                sink.out.push(ExtProofStep::Delete(exp));
            }
            for clause in prev_level {
                sink.out.push(ExtProofStep::Delete(clause));
            }
            prev_level = level;
        }
        debug_assert_eq!(prev_level.len(), 1, "terminal level is the unit clause");
    }

    fn emit_one_step(
        &mut self,
        solver: &GaussianSolver,
        j: usize,
        next_fresh: &mut VarId,
        out: &mut Vec<ExtProofStep>,
    ) {
        let step = &solver.elimination_trace[j];
        let vars_a = row_vars(solver, &step.parent_a);
        let vars_b = row_vars(solver, &step.parent_b);
        let vars_c = row_vars(solver, &step.result);
        let [pa, pb] = self.plan.step_parents[j];
        let uids = [
            uid_of(ParentRef::Step(j as u32), self.n_orig),
            uid_of(pa, self.n_orig),
            uid_of(pb, self.n_orig),
        ];
        debug_assert!(
            self.chains[uids[1] as usize]
                .as_ref()
                .is_some_and(|c| c.aux.len() + 1 == vars_a.len()),
            "parent_a chain width mismatch: provenance error"
        );
        debug_assert!(
            self.chains[uids[2] as usize]
                .as_ref()
                .is_some_and(|c| c.aux.len() + 1 == vars_b.len()),
            "parent_b chain width mismatch: provenance error"
        );
        let mut sink = EmitSink {
            chains: &mut self.chains,
            next_fresh,
            out,
            last_lemma: Vec::new(),
            uid_c: uids[0],
            abandoned: false,
        };
        walk_step(&vars_a, &vars_b, &vars_c, step.result.rhs, uids, &mut sink);
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "chunked_proof_tests.rs"]
mod tests;
