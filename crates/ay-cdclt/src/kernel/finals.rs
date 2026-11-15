// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The final check (KC8 effort levels, H3 combination) and how its effects
//! become ay-sat's continue-or-conflict answer (G2).

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::Effort;
use ay_sat::{ExtCheckResult, ExtContinue, ExtPropagateResult, SolverContext};

use super::Kernel;
use crate::plugin::{Effects, Final, GiveUp, ThId};

/// The same final-check clause set this many times in a row is a plug-in
/// bug, not progress; the check ends `unknown` (fail closed).
const REPEAT_TRIP: u32 = 3;

impl Kernel<'_> {
    pub(super) fn drain_final(
        &mut self,
        sat: &dyn SolverContext,
    ) -> Result<ExtCheckResult, GiveUp> {
        let effects = std::mem::take(&mut self.effects);
        let conflict = match effects.conflict {
            Some(conflict) => Some(self.conflict_clause(conflict, sat)?),
            None => None,
        };
        let mapped = self.map_lemmas(effects.lemmas, sat)?;
        if mapped.redundant.is_empty() && mapped.definitional.is_empty() {
            if let Some(clause) = conflict {
                return Ok(ExtCheckResult::Conflict(clause));
            }
        }
        let mut lemmas = Vec::new();
        lemmas.extend(conflict);
        lemmas.extend(mapped.redundant);
        // At a full assignment a propagation is true already or refutes it;
        // a refutation is a falsified lemma, which G2 handles as a conflict.
        let mut seen = HashSet::default();
        let mut scratch = ExtPropagateResult::none();
        for prop in effects.props {
            self.push_propagation(prop, sat, &mut seen, &mut scratch);
        }
        lemmas.extend(scratch.conflict);
        self.note_preferred(effects.preferred)?;
        self.internalize_minted()?;
        if lemmas.is_empty() && mapped.definitional.is_empty() {
            return Err(GiveUp::new("final check continued without effects"));
        }
        let cont = ExtContinue::new(lemmas, mapped.definitional).with_num_vars(self.next_mint);
        if self.last_final.as_ref() == Some(&cont) {
            self.repeats += 1;
            if self.repeats >= REPEAT_TRIP {
                return Err(GiveUp::new("final check repeated the same lemmas"));
            }
        } else {
            self.repeats = 0;
            self.last_final = Some(cont.clone());
        }
        Ok(ExtCheckResult::Continue(cont))
    }

    pub(super) fn final_check(
        &mut self,
        sat: &dyn SolverContext,
    ) -> Result<ExtCheckResult, GiveUp> {
        // Every variable is assigned at a final check: all preferences are stale.
        self.preferred.clear();
        self.feed(sat)?;
        if self.effects.conflict.is_some()
            || !self.effects.lemmas.is_empty()
            || self.a_propagation_is_refuted(sat)
        {
            return self.drain_final(sat);
        }
        // KC8: levels cheapest first; within a level the plug-ins take fair
        // turns, and the first one with an effect ends the round.
        let count = usize::from(self.plugin_count());
        for effort in Effort::ALL {
            let order: Vec<usize> = self.schedule.order(effort, count).collect();
            for idx in order {
                let id = ThId::try_from(idx).unwrap_or(ThId::MAX);
                let outcome = self.call(id, Some(sat), |p, ctx| p.final_check(ctx, effort));
                match outcome {
                    Some(Ok(Final::Sat))
                        if self.effects.conflict.is_none() && self.effects.lemmas.is_empty() => {}
                    Some(Ok(_)) => {
                        self.schedule.produced(effort, idx, count);
                        return self.drain_final(sat);
                    }
                    Some(Err(give_up)) => return Err(give_up),
                    None => {}
                }
            }
        }
        // Every plug-in accepts at every level: model-based combination
        // decides (H3). Candidate equalities continue the search.
        if self.combine(sat)? {
            return self.drain_final(sat);
        }
        self.effects = Effects::default();
        for id in 0..self.plugin_count() {
            self.call(id, Some(sat), |p, ctx| p.on_sat(ctx));
        }
        self.final_sat = true;
        Ok(ExtCheckResult::Sat)
    }
}
