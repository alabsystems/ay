// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One absolute wall-clock frame for a native solve attempt.
//!
//! `SolveOpts::time_limit` is caller-owned duration policy. Reading it again in
//! a nested reduction, feasibility probe, or certificate retry would grant a
//! fresh budget. This boundary materializes the duration exactly once; every
//! inner phase receives `time_limit = None` plus the same absolute deadline.

use std::time::Instant;

use crate::opts::SolveOpts;

enum OptionsStorage<'a> {
    Borrowed(&'a SolveOpts),
    Materialized(Box<SolveOpts>),
}

/// Options whose duration, if any, has been pinned at one top-level entry.
pub(super) struct SolveAttemptOptions<'a> {
    storage: OptionsStorage<'a>,
}

impl<'a> SolveAttemptOptions<'a> {
    pub(super) fn at_entry(options: &'a SolveOpts, started: Instant) -> Self {
        let storage = if options.time_limit.is_none() {
            OptionsStorage::Borrowed(options)
        } else {
            let mut materialized = options.clone();
            materialized.deadline = options.effective_deadline(started);
            materialized.time_limit = None;
            OptionsStorage::Materialized(Box::new(materialized))
        };
        Self { storage }
    }

    pub(super) fn options(&self) -> &SolveOpts {
        match &self.storage {
            OptionsStorage::Borrowed(options) => options,
            OptionsStorage::Materialized(options) => options.as_ref(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;

    #[test]
    fn duration_is_fresh_only_at_a_top_level_entry() {
        let first_start = Instant::now();
        let duration = Duration::from_secs(10);
        let caller = SolveOpts::new().with_time_limit(duration);

        let first = SolveAttemptOptions::at_entry(&caller, first_start);
        let first_deadline = first_start + duration;
        assert_eq!(first.options().deadline, Some(first_deadline));
        assert_eq!(first.options().time_limit, None);

        let later = first_start + Duration::from_secs(3);
        let nested = SolveAttemptOptions::at_entry(first.options(), later);
        assert_eq!(nested.options().deadline, Some(first_deadline));
        assert_eq!(nested.options().time_limit, None);

        let repeated = SolveAttemptOptions::at_entry(&caller, later);
        assert_eq!(repeated.options().deadline, Some(later + duration));
        assert_eq!(caller.time_limit, Some(duration));
        assert_eq!(caller.deadline, None);

        let earlier_absolute = first_start + Duration::from_secs(2);
        let capped_caller = caller.clone().with_deadline(earlier_absolute);
        let capped = SolveAttemptOptions::at_entry(&capped_caller, first_start);
        assert_eq!(capped.options().deadline, Some(earlier_absolute));
        assert_eq!(capped.options().time_limit, None);
    }
}
