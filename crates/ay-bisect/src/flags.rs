// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Canonical list of ay feature-disable CLI flags that `ay-bisect` searches over.
//!
//! Each flag maps to a `--no-*` CLI argument accepted by the `ay` binary. A
//! *trial configuration* in bisect terms is a subset of these flags that are
//! passed on the command line; every flag in the subset disables one feature.
//! A bisection trial that sets *all* of them effectively corresponds to the
//! fully-minimal solver; the empty set corresponds to the default solver with
//! every feature enabled.
//!
//! Per project rules (`MEMORY.md: No Env Vars`) we use CLI flags exclusively
//! here; no `AY_NO_*` environment variables are read or written by this crate.

/// The set of ay feature-disable CLI flags that bisect may toggle.
///
/// Scope: SAT preprocessing/inprocessing passes plus a handful of theory-layer
/// disable knobs that are known to have been implicated in soundness bugs.
/// Keeping this list compact (~12 flags) keeps the search space tractable for
/// binary bisection while still covering the most common culprits.
///
/// Ordering is significant: it defines the halves used by the binary search
/// algorithm. SAT-layer flags come first, theory-layer flags last, so that
/// SAT/theory splits fall naturally on the midpoint for even-sized slices.
pub const FLAGS: &[&str] = &[
    // SAT preprocessing / inprocessing
    "--no-preprocess",
    "--no-bve",
    "--no-vivify",
    "--no-probe",
    "--no-subsume",
    "--no-bce",
    "--no-inprocess",
    // Theory layer
    "--no-bound-axioms",
    "--no-theory-propagation",
    "--no-bcp-theory-check",
    "--no-implied-bounds",
    "--no-ite-deferral",
];

/// Coarse classification of each flag, used for the `subsystems` field in the
/// final report. Intentionally a small enum rather than a string so additions
/// are reviewed at the type level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Subsystem {
    /// SAT-layer preprocessing/inprocessing.
    Sat,
    /// Theory layer (arithmetic propagation, DPLL(T) dispatch, etc.).
    Theory,
}

impl Subsystem {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Theory => "theory",
        }
    }
}

/// Classify a single flag into the subsystem it controls.
///
/// Unknown flags default to `Sat`; callers should only pass values from
/// [`FLAGS`], in which case the classification is always accurate.
#[must_use]
pub fn classify(flag: &str) -> Subsystem {
    match flag {
        "--no-bound-axioms"
        | "--no-theory-propagation"
        | "--no-bcp-theory-check"
        | "--no-implied-bounds"
        | "--no-ite-deferral" => Subsystem::Theory,
        _ => Subsystem::Sat,
    }
}

/// Return the set of subsystems touched by a list of flags, sorted and
/// de-duplicated. Used in the final bisect report.
#[must_use]
pub fn subsystems_for(flags: &[String]) -> Vec<String> {
    let mut seen: Vec<Subsystem> = Vec::new();
    for f in flags {
        let s = classify(f);
        if !seen.contains(&s) {
            seen.push(s);
        }
    }
    seen.sort();
    seen.into_iter().map(|s| s.as_str().to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_flags_all_start_with_double_dash() {
        for f in FLAGS {
            assert!(f.starts_with("--no-"), "flag must start with --no-: {f}");
        }
    }

    #[test]
    fn test_flags_are_unique() {
        let mut seen = std::collections::HashSet::new();
        for f in FLAGS {
            assert!(seen.insert(*f), "duplicate flag: {f}");
        }
    }

    #[test]
    fn test_flags_nonempty_and_reasonable_size() {
        assert!(
            FLAGS.len() >= 10 && FLAGS.len() <= 20,
            "got {}",
            FLAGS.len()
        );
    }

    #[test]
    fn test_classify_sat_flags() {
        assert_eq!(classify("--no-bve"), Subsystem::Sat);
        assert_eq!(classify("--no-vivify"), Subsystem::Sat);
        assert_eq!(classify("--no-probe"), Subsystem::Sat);
    }

    #[test]
    fn test_classify_theory_flags() {
        assert_eq!(classify("--no-bound-axioms"), Subsystem::Theory);
        assert_eq!(classify("--no-theory-propagation"), Subsystem::Theory);
        assert_eq!(classify("--no-ite-deferral"), Subsystem::Theory);
    }

    #[test]
    fn test_subsystems_for_mixed() {
        let flags = vec!["--no-bve".to_string(), "--no-bound-axioms".to_string()];
        assert_eq!(subsystems_for(&flags), vec!["sat", "theory"]);
    }

    #[test]
    fn test_subsystems_for_sat_only() {
        let flags = vec!["--no-bve".to_string(), "--no-vivify".to_string()];
        assert_eq!(subsystems_for(&flags), vec!["sat"]);
    }

    #[test]
    fn test_subsystems_for_empty() {
        let out = subsystems_for(&[]);
        assert!(out.is_empty());
    }
}
