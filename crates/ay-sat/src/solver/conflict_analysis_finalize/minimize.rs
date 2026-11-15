// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Solver {
    pub(super) fn finalize_minimize_admitted<P: admitted::Policy>(
        &mut self,
        size: usize,
        p: &P,
    ) -> Result<Option<Vec<Literal>>, P::Error> {
        p.work(8)?;
        let repeated = self.shrink_enabled
            && size > 2
            && self.finalize_repeated_level_admitted(size - 1, p)?;
        if self.shrink_enabled && size > 2 && !repeated {
            p.counter(self.stats.shrink_singleton_fast_path_skips, 1)?;
            self.stats.shrink_singleton_fast_path_skips += 1;
            if self.cold.lrat_enabled {
                p.counter(self.stats.lrat_original_learned_snapshot_singleton_skips, 1)?;
                self.stats.lrat_original_learned_snapshot_singleton_skips += 1;
            }
        }
        let mut removed = if self.should_snapshot_lrat_original_learned(size, repeated) {
            p.removed_snapshot()?;
            let mut values = std::mem::take(&mut self.min.lrat_original_learned_buf);
            values.clear();
            Some(values)
        } else {
            None
        };
        p.counter(self.stats.shrink_lits_deduced, size as u64)?;
        self.stats.shrink_lits_deduced += size as u64;
        if size > 2 {
            if self.shrink_enabled {
                if repeated {
                    shrink::admitted::run(self, size - 1, removed.as_mut(), p)?;
                }
            } else {
                self.minimize_clause_admitted(removed.as_mut(), p)?;
            }
        }
        Ok(removed)
    }

    fn finalize_repeated_level_admitted<P: admitted::Policy>(
        &mut self,
        count: usize,
        p: &P,
    ) -> Result<bool, P::Error> {
        if !self.min.level_seen_flag_valid {
            return self.repeated_level_admitted(count, p);
        }
        let repeated = self.min.level_seen_repeated_non_uip;
        #[cfg(debug_assertions)]
        {
            let prescan = self.repeated_level_admitted(count, p)?;
            debug_assert_eq!(
                prescan, repeated,
                "incremental repeated-level bit diverges from exact prescan"
            );
        }
        Ok(repeated)
    }
}
