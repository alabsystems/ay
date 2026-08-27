// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression gate for the EUF Bool-arg guard's scratch union-find SEEDING.
//!
//! `bool_arg_model_is_congruent` builds a scratch union-find over e-node ids and
//! seeds it with the live EUF classes:
//!
//! ```ignore
//! let mut parent: Vec<u32> = (0..nverts).collect();
//! // Seed with current EUF classes.
//! for v in 0..nverts {
//!     let r = self.enode_find_const(v);
//!     ...
//! }
//! ```
//!
//! If that seed loop is dropped, `parent` stays the IDENTITY permutation. Two
//! consequences, both silent:
//!
//!   * `sfind(parent, arg)` returns the raw term id instead of the argument's
//!     e-class representative, so signature keys no longer identify congruent
//!     applications; and
//!   * the `baseline` snapshot (a compressed copy of `parent`) makes every term
//!     its own class, so the baseline-class suppression — the check that stops
//!     the guard firing on pairs the base solver had ALREADY merged — never
//!     fires.
//!
//! The guard then over-fires and downgrades satisfiable models to `unknown`.
//! That is a COMPLETENESS regression, never a wrong answer, which is exactly why
//! it is dangerous: no soundness canary trips, and the whole 5,423-test ay-dpll
//! library suite passed with the seed loop missing. It was caught only by a
//! division-scale score drop (14060 -> 14011 check-sats on Incremental
//! QF_Equality, 49 answers lost across 15 CLEARSY files).
//!
//! The benchmark is the first three check-sats of SMT-LIB 2025
//! `incremental/QF_UF/20190906-CLEARSY/0000/00302.smt2`, committed in-tree so
//! this gate does not depend on the competition corpus being downloaded.
//! Verified to discriminate: with the seed loop the answers are
//! `sat unsat unsat`; without it, `sat unknown unknown`.

mod common;

// The guard's repair CEGAR must be enabled for this file to reach definite
// answers at all — without it both the fixed and the broken build report
// `sat unknown unknown`, so the flag is what makes the test discriminating.
// B69: the repair arm rides the set-once typed carrier — installed below
// before anything can read it into a `OnceLock` (single-test binary).

const BENCH: &str = "benchmarks/smt/regression/euf_bool_arg_guard_seed/clearsy_00302_prefix3.smt2";

#[test]
fn bool_arg_guard_scratch_union_find_is_seeded_with_euf_classes() {
    ay_core::set_global_misc_cli_flags(ay_core::MiscCliFlags {
        euf_bool_arg_repair: true,
        ..Default::default()
    })
    .expect("first install in this single-test binary");

    let path = common::workspace_path(BENCH);
    assert!(
        path.is_file(),
        "regression asset missing: {} — it is committed in-tree and must not be deleted",
        path.display()
    );
    let smt = std::fs::read_to_string(&path).expect("read regression asset");

    let outputs = common::solve_vec(&smt);

    assert_eq!(
        outputs,
        vec!["sat", "unsat", "unsat"],
        "EUF Bool-arg guard over-fired. The most likely cause is that the \
         `Seed with current EUF classes` loop in `bool_arg_model_is_congruent` \
         (crates/ay-theories/euf/src/bool_atoms.rs) was removed or bypassed, \
         leaving the scratch union-find as the identity permutation. Do not \
         weaken this assertion to accept `unknown` — that is the bug."
    );
}
