// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `--sat-veripb-hints` walk proper: the literals a hint list must
//! explain, swept down the trail (`veripb_hint_drain`), each explained by its
//! reason and that reason's id. `veripb_hints.rs` seeds the walk and writes
//! what it finds.

use super::veripb_hints::{HintFail, VeripbHintState};
use super::*;
use crate::watched::{entry_blocker_raw, entry_is_binary};

/// Trail literals one hint walk may visit before the clause is written
/// without hints (the walk is linear in the implication cone it explains).
const VERIPB_HINT_WALK_BUDGET: usize = 200_000;

/// Progress of one `veripb_hint_drain`: literals visited, marked positions
/// still to explain, and the lowest and highest of those marked.
#[derive(Default)]
pub(super) struct HintSweep {
    visited: usize,
    pending: usize,
    lo: usize,
    hi: usize,
}

/// The rank (`veripb_hint_rank`) of a stamped literal that is not false.
const HINT_RANK_NOT_FALSE: u32 = u32::MAX >> 1;

/// A stamp-array entry: walk `stamp` in the high half, `rank` in the low.
#[inline]
pub(super) fn hint_mark(stamp: u32, rank: u32) -> u64 {
    (u64::from(stamp) << 32) | u64::from(rank)
}

#[inline]
pub(super) fn hint_stamped(mark: u64, stamp: u32) -> bool {
    (mark >> 32) as u32 == stamp
}

impl Solver {
    /// Explain every queued false literal, and every antecedent that brings
    /// in, by a sweep down the trail; then order the ids for the check.
    ///
    /// Each literal to explain marks its trail position in `st.need`, and the
    /// sweep takes the highest marked position next. An antecedent is always
    /// strictly earlier on the trail (or a root unit, named at once), so every
    /// literal is explained once and after every literal that needs it.
    /// VeriPB checks `rup C : ids` by propagating the ids in order, pass after
    /// pass, until a conflict, so the ids go out in trail order: root units,
    /// then reasons from the earliest, then the clause the walk started from.
    /// One pass reaches the conflict. The depth-first walk this replaces
    /// listed each reason before its antecedents and took a pass per step of
    /// the longest implication chain: the same 241 MB proof of ba773277
    /// elaborates in 4.3 s against 9.8 s (CakePB 12 s either way). The sweep
    /// costs 15 percent more walk time than that walk (1.03 s against 0.89 s of
    /// an 18.9 s search there).
    pub(super) fn veripb_hint_drain(
        &mut self,
        st: &mut VeripbHintState,
        stamp: u32,
    ) -> Result<(), HintFail> {
        let words = self.trail.len().div_ceil(64);
        if st.need.len() < words {
            st.need.resize(words, 0);
            st.need_top.resize(words.div_ceil(64), 0);
        }
        st.unit_ids.clear();
        let mut sweep = HintSweep::default();
        let result = self.veripb_hint_sweep(st, stamp, &mut sweep);
        st.drain_visited = sweep.visited as u64;
        if sweep.pending > 0 {
            let (lo, hi) = (sweep.lo / 64, sweep.hi / 64);
            st.need[lo..=hi].fill(0);
            st.need_top[lo / 64..=hi / 64].fill(0);
        }
        result?;
        st.ids.reverse();
        if !st.unit_ids.is_empty() {
            st.ids.splice(0..0, st.unit_ids.drain(..));
        }
        Ok(())
    }

    fn veripb_hint_sweep(
        &mut self,
        st: &mut VeripbHintState,
        stamp: u32,
        sweep: &mut HintSweep,
    ) -> Result<(), HintFail> {
        while let Some(y) = st.stack.pop() {
            self.veripb_hint_need(st, y, stamp, sweep)?;
        }
        let mut w = sweep.hi / 64;
        while sweep.pending > 0 {
            let word = st.need[w];
            if word == 0 {
                w = Self::veripb_hint_next_word(st, w).ok_or(HintFail::TrailPosMismatch)?;
                continue;
            }
            let bit = 63 - word.leading_zeros() as usize;
            let rest = word & !(1u64 << bit);
            st.need[w] = rest;
            if rest == 0 {
                st.need_top[w / 64] &= !(1u64 << (w % 64));
            }
            sweep.pending -= 1;
            let pos = w * 64 + bit;
            self.veripb_hint_explain(st, pos, stamp, sweep)?;
        }
        Ok(())
    }

    /// The highest `need` word below `w` with a position marked, through the
    /// summary bitmap (a bit per word): a cone of a few literals spread over a
    /// long trail, as a hyper-binary resolvent's at probing, costs a word per
    /// 4,096 positions between them rather than one per 64. None when no word
    /// below `w` is marked, though some position is pending.
    fn veripb_hint_next_word(st: &VeripbHintState, w: usize) -> Option<usize> {
        let (mut t, bit) = (w / 64, w % 64);
        let mut summary = st.need_top[t] & ((1u64 << bit) - 1);
        loop {
            if summary != 0 {
                return Some(t * 64 + 63 - summary.leading_zeros() as usize);
            }
            t = t.checked_sub(1)?;
            summary = st.need_top[t];
        }
    }

    /// Queue false literal `y` for explanation, unless its variable is
    /// stamped (assumed false by the check, or already queued): at level 0 by
    /// naming its unit constraint now, above it by marking its trail position.
    #[inline]
    fn veripb_hint_need(
        &mut self,
        st: &mut VeripbHintState,
        y: Literal,
        stamp: u32,
        sweep: &mut HintSweep,
    ) -> Result<(), HintFail> {
        let v = y.variable().index();
        match st.stamp.get(v) {
            None => return Err(HintFail::ConeLitNotFalse),
            Some(&mark) if hint_stamped(mark, stamp) => return Ok(()),
            Some(_) => {}
        }
        st.stamp[v] = hint_mark(stamp, self.veripb_hint_rank(y));
        sweep.visited += 1;
        if sweep.visited > VERIPB_HINT_WALK_BUDGET {
            return Err(HintFail::Budget);
        }
        if self.lit_val(y) >= 0 {
            return Err(HintFail::ConeLitNotFalse);
        }
        let t = y.negated();
        let vd = self.var_data[v];
        if vd.level == 0 {
            let id = self
                .veripb_unit_id(st, t)
                .ok_or(HintFail::Level0UnitMissing)?;
            st.unit_ids.push(id);
            st.drain_units += 1;
            return Ok(());
        }
        let pos = vd.trail_pos as usize;
        if pos >= self.trail.len() || self.trail[pos] != t || pos / 64 >= st.need.len() {
            return Err(HintFail::TrailPosMismatch);
        }
        let w = pos / 64;
        st.need[w] |= 1u64 << (pos % 64);
        st.need_top[w / 64] |= 1u64 << (w % 64);
        if sweep.pending == 0 {
            (sweep.lo, sweep.hi) = (pos, pos);
        } else {
            sweep.lo = sweep.lo.min(pos);
            sweep.hi = sweep.hi.max(pos);
        }
        sweep.pending += 1;
        Ok(())
    }

    /// Explain the true literal at trail position `pos` (above level 0) by its
    /// reason, whose other literals are queued. A reason that on-the-fly
    /// strengthening has shortened by the literal (`otfs_strengthen`, which
    /// writes the shortened clause) is false on earlier literals alone and
    /// explains the conflict outright. Why not, when the explanation is not
    /// certain.
    fn veripb_hint_explain(
        &mut self,
        st: &mut VeripbHintState,
        pos: usize,
        stamp: u32,
        sweep: &mut HintSweep,
    ) -> Result<(), HintFail> {
        let t = self.trail[pos];
        let v = t.variable().index();
        let kind = match (self.var_reason_kind(v), st.decision_reason) {
            (ReasonKind::Decision, Some((dv, reason))) if dv == v => {
                if !self.arena.literals(reason.0 as usize).contains(&t) {
                    return Err(HintFail::DecisionInCone);
                }
                ReasonKind::Clause(reason)
            }
            (kind, _) => kind,
        };
        // The reason's id by its content key, summed while its literals are
        // checked; its unexplained antecedents are queued as they pass.
        let id = match kind {
            ReasonKind::Clause(reason) => {
                let idx = reason.0 as usize;
                let len = self.arena.len_of(idx);
                let mut key = 0u64;
                for i in 0..len {
                    let lit = self.arena.literal(idx, i);
                    key = key.wrapping_add(self.veripb_proof_literal_key(lit));
                    if lit == t {
                        continue;
                    }
                    self.veripb_hint_antecedent(st, lit, pos, stamp, sweep)?;
                }
                self.veripb_id_by_key(key)
                    .ok_or(HintFail::ReasonIdUnknown)?
            }
            ReasonKind::BinaryLiteral(other) => {
                if !self.veripb_hint_stamped_before(st, other, pos, stamp)?
                    && !self.veripb_hint_antecedent_ok(other, pos)
                {
                    return Err(HintFail::AntecedentOrder);
                }
                let key = self
                    .veripb_proof_literal_key(t)
                    .wrapping_add(self.veripb_proof_literal_key(other));
                let (x, id) = match self.veripb_id_by_key(key) {
                    Some(id) => (other, id),
                    None => {
                        let found = self
                            .veripb_jump_antecedent(st, t, other, pos)
                            .ok_or(HintFail::ReasonIdUnknown)?;
                        st.jumps_resolved += 1;
                        found
                    }
                };
                self.veripb_hint_need(st, x, stamp, sweep)?;
                id
            }
            ReasonKind::Decision | ReasonKind::LazyTheory(_) => {
                return Err(HintFail::DecisionInCone);
            }
        };
        st.ids.push(id);
        Ok(())
    }

    /// A literal's term of the VeriPB writer's content key, in the variables
    /// the proof speaks.
    #[inline]
    fn veripb_proof_literal_key(&self, lit: Literal) -> u64 {
        let lit = if self.cold.proof_vars_compacted {
            self.externalize_for_proof(lit)
        } else {
            lit
        };
        crate::proof::veripb_literal_key(lit)
    }

    /// The VeriPB id of the live constraint whose content key is `key`.
    #[inline]
    fn veripb_id_by_key(&self, key: u64) -> Option<u64> {
        self.proof_manager
            .as_ref()?
            .output()
            .veripb_constraint_id_by_key(key)
    }

    /// The real antecedent behind a jump reason. Binary propagation stores for
    /// `t` the reason literal of its antecedent's own binary reason
    /// (`enqueue_binary_reason`, Kissat fastassign.h:12-19), so (t ∨ other) is
    /// a resolvent no proof line holds: on aes_equiv_encry_3_rounds every hint
    /// fallback but 2 percent was one. The clause that propagated `t` is a
    /// binary (t ∨ x) in `t`'s watch list whose `x` is false, earlier on the
    /// trail, and implied by `other`; `(x, its id)`, and `x` is explained next.
    fn veripb_jump_antecedent(
        &mut self,
        st: &mut VeripbHintState,
        t: Literal,
        other: Literal,
        pos: usize,
    ) -> Option<(Literal, u64)> {
        // Binary watches form the binary-first prefix of the list.
        for i in 0..self.watches.binary_count_of(t) {
            let entry = self.watches.entry_raw(t, i);
            debug_assert!(entry_is_binary(entry));
            let x = Literal(entry_blocker_raw(entry));
            if !self.veripb_hint_antecedent_ok(x, pos)
                || !matches!(
                    self.var_reason_kind(x.variable().index()),
                    ReasonKind::BinaryLiteral(r) if r == other
                )
            {
                continue;
            }
            st.scratch2.clear();
            st.scratch2.push(t);
            st.scratch2.push(x);
            if let Some(id) = self.veripb_constraint_id_of(&mut st.scratch2) {
                return Some((x, id));
            }
        }
        None
    }

    /// Check antecedent `lit` of the literal at trail position `pos`
    /// (`veripb_hint_antecedent_ok`) and queue it. A literal the walk has
    /// stamped is checked by its rank alone, one load where the trail check
    /// takes two; cones meet most antecedents many times over (8 percent of
    /// the walk on ba773277).
    #[inline]
    fn veripb_hint_antecedent(
        &mut self,
        st: &mut VeripbHintState,
        lit: Literal,
        pos: usize,
        stamp: u32,
        sweep: &mut HintSweep,
    ) -> Result<(), HintFail> {
        if self.veripb_hint_stamped_before(st, lit, pos, stamp)? {
            return Ok(());
        }
        if !self.veripb_hint_antecedent_ok(lit, pos) {
            return Err(HintFail::AntecedentOrder);
        }
        self.veripb_hint_need(st, lit, stamp, sweep)
    }

    /// Whether this walk has stamped `lit`'s variable, and then that `lit`
    /// passes `veripb_hint_antecedent_ok` at `pos`: the mark keeps the stamped
    /// literal's sign and how it was assigned (the trail does not move during
    /// a walk), so the opposite literal fails as a true one did.
    #[inline]
    fn veripb_hint_stamped_before(
        &self,
        st: &VeripbHintState,
        lit: Literal,
        pos: usize,
        stamp: u32,
    ) -> Result<bool, HintFail> {
        match st.stamp.get(lit.variable().index()) {
            Some(&mark) if hint_stamped(mark, stamp) => {
                let rank = mark as u32;
                if rank >> 31 != u32::from(lit.is_positive())
                    || (rank & HINT_RANK_NOT_FALSE) as usize > pos
                {
                    return Err(HintFail::AntecedentOrder);
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// `lit`'s rank for `veripb_hint_stamped_before`: its sign in the top bit,
    /// below it 0 at level 0, its trail position plus one above, and
    /// `HINT_RANK_NOT_FALSE` when it is not false (a stamped clause literal
    /// left unassigned).
    #[inline]
    pub(super) fn veripb_hint_rank(&self, lit: Literal) -> u32 {
        let sign = u32::from(lit.is_positive()) << 31;
        if self.lit_val(lit) >= 0 {
            return sign | HINT_RANK_NOT_FALSE;
        }
        let vd = self.var_data[lit.variable().index()];
        if vd.level == 0 {
            sign
        } else {
            sign | vd.trail_pos.saturating_add(1).min(HINT_RANK_NOT_FALSE - 1)
        }
    }

    /// An antecedent of the literal at trail position `pos` must be false and,
    /// above level 0, assigned strictly earlier (so the hints replay in order).
    #[inline]
    fn veripb_hint_antecedent_ok(&self, lit: Literal, pos: usize) -> bool {
        if self.lit_val(lit) >= 0 {
            return false;
        }
        let vd = self.var_data[lit.variable().index()];
        vd.level == 0 || (vd.trail_pos as usize) < pos
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn next_marked_word_skips_unmarked_summary_words() {
        let mut st = VeripbHintState::default();
        st.need_top = vec![0; 3];
        // Words 5, 64 and 130 marked.
        for w in [5usize, 64, 130] {
            st.need_top[w / 64] |= 1 << (w % 64);
        }
        assert_eq!(Solver::veripb_hint_next_word(&st, 191), Some(130));
        assert_eq!(Solver::veripb_hint_next_word(&st, 130), Some(64));
        assert_eq!(Solver::veripb_hint_next_word(&st, 64), Some(5));
        assert_eq!(Solver::veripb_hint_next_word(&st, 5), None);
        assert_eq!(Solver::veripb_hint_next_word(&st, 0), None);
    }
}
