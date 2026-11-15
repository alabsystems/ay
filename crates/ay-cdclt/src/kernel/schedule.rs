// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The final check's turn order (KC8): levels cheapest first, and a fair,
//! budgeted turn order among the plug-ins within each level.
//!
//! The budget of one final check is one producing plug-in: the round ends at
//! the first plug-in that answers with an effect, and the search continues
//! with that effect. The next final check at the same level starts with the
//! plug-in after the producer, so a plug-in that produces on every round
//! cannot keep the others from being asked: with `n` plug-ins, every one of
//! them is asked within `n` rounds at that level. The design's earlier rule,
//! "restart from the top and stop at the first effect" (§3.6), starved every
//! plug-in behind one that keeps producing (E-matching ahead of MBQI).

use ay_core::Effort;

/// Where the next round of each level starts.
#[derive(Debug, Default)]
pub(super) struct FinalSchedule {
    start: [usize; Effort::ALL.len()],
}

impl FinalSchedule {
    /// The plug-in indices level `effort` asks this round, in turn order.
    pub(super) fn order(&self, effort: Effort, plugins: usize) -> impl Iterator<Item = usize> {
        let start = self.start.get(effort.index()).copied().unwrap_or(0);
        let start = start.checked_rem(plugins).unwrap_or(0);
        (0..plugins).map(move |i| (start + i) % plugins)
    }

    /// `producer` answered level `effort` with an effect: the next round of
    /// that level starts with the plug-in after it.
    pub(super) fn produced(&mut self, effort: Effort, producer: usize, plugins: usize) {
        if let Some(slot) = self.start.get_mut(effort.index()) {
            *slot = (producer + 1).checked_rem(plugins).unwrap_or(0);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Simulate `rounds` final checks at one level, where `produces(i)` says
    /// whether plug-in `i` answers with an effect; return how often each
    /// plug-in was asked.
    fn simulate(plugins: usize, rounds: usize, produces: impl Fn(usize) -> bool) -> Vec<usize> {
        let mut schedule = FinalSchedule::default();
        let mut asked = vec![0; plugins];
        for _ in 0..rounds {
            let order: Vec<usize> = schedule.order(Effort::Standard, plugins).collect();
            for i in order {
                asked[i] += 1;
                if produces(i) {
                    schedule.produced(Effort::Standard, i, plugins);
                    break;
                }
            }
        }
        asked
    }

    #[test]
    fn a_plugin_that_always_produces_does_not_starve_the_others() {
        // Plug-in 0 produces on every round (E-matching); 1 and 2 also have
        // work every time they are asked (MBQI, enumeration).
        let asked = simulate(3, 30, |_| true);
        assert_eq!(asked, vec![10, 10, 10]);
        // Only plug-in 0 ever produces: the others are still asked on every
        // round after it.
        let asked = simulate(3, 30, |i| i == 0);
        assert_eq!(asked, vec![30, 29, 29]);
    }

    #[test]
    fn levels_keep_their_own_turn() {
        let mut schedule = FinalSchedule::default();
        schedule.produced(Effort::Standard, 0, 2);
        assert_eq!(
            schedule.order(Effort::Standard, 2).collect::<Vec<_>>(),
            [1, 0]
        );
        assert_eq!(schedule.order(Effort::Cheap, 2).collect::<Vec<_>>(), [0, 1]);
        assert_eq!(schedule.order(Effort::Model, 0).count(), 0);
    }
}
