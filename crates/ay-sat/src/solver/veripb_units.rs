// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-veripb-hints`: unit constraints for root-level facts. A hint that
//! needs a root-false literal names the unit constraint of its negation: the
//! proof's own, or one written on the spot, itself annotated from the level-0
//! reason (or a given supporting clause) and the units of that clause's other
//! literals. Also the unit `collect_level0_garbage` re-states before deleting
//! the clause that derived it.

use super::veripb_hints::VeripbHintState;
use super::*;

/// Level-0 reasons a missing unit may be derived through before it is written
/// without hints (`veripb_unit_id`).
const VERIPB_UNIT_HINT_DEPTH: u32 = 64;

impl Solver {
    /// The id of a unit constraint for `t`, true at level 0: the proof's own,
    /// or a plain `rup` unit written now (implied by level-0 propagation).
    pub(super) fn veripb_unit_id(&mut self, st: &mut VeripbHintState, t: Literal) -> Option<u64> {
        self.veripb_unit_id_within(st, t, 0, None)
    }

    /// State `lit`, true at level 0, as a unit constraint: the proof's own, or
    /// one written now with hints from `support` (a live clause deriving it at
    /// root, such as one about to be deleted) or else from its reason
    /// (`veripb_unit_id`). `false` when annotated RUP is off or no unit could
    /// be written.
    pub(super) fn veripb_state_root_unit(
        &mut self,
        lit: Literal,
        support: Option<&[Literal]>,
    ) -> bool {
        if !self.veripb_hints_active() {
            return false;
        }
        let mut st = std::mem::take(&mut self.cold.veripb_hints);
        let id = self.veripb_unit_id_within(&mut st, lit, 0, support);
        self.cold.veripb_hints = st;
        id.is_some()
    }

    /// `veripb_unit_id` at `depth` level-0 reasons below the unit asked for.
    /// A unit the proof lacks is written as annotated RUP from `support` or its
    /// level-0 reason and the units of that clause's other literals (earlier
    /// on the trail), themselves written the same way; past
    /// `VERIPB_UNIT_HINT_DEPTH` levels, or without such a clause whose id is
    /// known, it is written plain, and the check searches for it.
    fn veripb_unit_id_within(
        &mut self,
        st: &mut VeripbHintState,
        t: Literal,
        depth: u32,
        support: Option<&[Literal]>,
    ) -> Option<u64> {
        let mut unit = [t];
        if let Some(id) = self.veripb_constraint_id_of(&mut unit) {
            return Some(id);
        }
        let hints = if depth < VERIPB_UNIT_HINT_DEPTH {
            support
                .and_then(|clause| self.veripb_root_clause_hints(st, t, clause.to_vec(), depth))
                .or_else(|| self.veripb_root_reason_hints(st, t, depth))
        } else {
            None
        };
        // A cycle through the reasons may have written it meanwhile.
        let mut unit = [t];
        if let Some(id) = self.veripb_constraint_id_of(&mut unit) {
            return Some(id);
        }
        // `unit` now holds the proof-surface literal.
        self.proof_manager
            .as_mut()?
            .emit_add_veripb_rup(&unit, hints.as_deref().unwrap_or(&[]))
            .ok()?;
        st.units_written += 1;
        self.proof_manager
            .as_mut()?
            .output_mut()
            .veripb_constraint_id(&unit)
    }

    /// Hints for `t`, true at level 0, from its reason (see
    /// `veripb_root_clause_hints`).
    fn veripb_root_reason_hints(
        &mut self,
        st: &mut VeripbHintState,
        t: Literal,
        depth: u32,
    ) -> Option<Vec<u64>> {
        let v = t.variable().index();
        if v >= self.num_vars {
            return None;
        }
        let ReasonKind::Clause(reason) = self.var_reason_kind(v) else {
            return None;
        };
        let lits = self.arena.literals(reason.0 as usize).to_vec();
        self.veripb_root_clause_hints(st, t, lits, depth)
    }

    /// Hints for `t`, true at level 0, from clause `lits` holding `t` with every
    /// other literal root-false: the units of those literals, then the clause.
    /// The clause's id is looked up first, so no unit is written for a clause
    /// the proof does not hold.
    fn veripb_root_clause_hints(
        &mut self,
        st: &mut VeripbHintState,
        t: Literal,
        lits: Vec<Literal>,
        depth: u32,
    ) -> Option<Vec<u64>> {
        let v = t.variable().index();
        if v >= self.num_vars || self.var_data[v].level != 0 || self.lit_val(t) <= 0 {
            return None;
        }
        if !lits.contains(&t) {
            return None;
        }
        for &other in &lits {
            let ov = other.variable().index();
            if other != t
                && (ov >= self.num_vars || self.var_data[ov].level != 0 || self.lit_val(other) >= 0)
            {
                return None;
            }
        }
        let mut content = lits.clone();
        let clause_id = self.veripb_constraint_id_of(&mut content)?;
        let mut hints = Vec::with_capacity(lits.len());
        for &other in &lits {
            if other != t {
                hints.push(self.veripb_unit_id_within(st, other.negated(), depth + 1, None)?);
            }
        }
        hints.push(clause_id);
        Some(hints)
    }
}
