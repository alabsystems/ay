// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{run, CommandUnsatAdmission, Executor};
use crate::VerificationLevel;

const ASSERTIONS: &str = "(set-logic QF_UF)
    (declare-const p Bool)
    (declare-const q Bool)
    (assert (or p q))
    (assert (or (not p) q))
    (assert (not q))";

const CHECKED_LEVELS: [VerificationLevel; 2] = [
    VerificationLevel::ProofChecked,
    VerificationLevel::FullyVerified,
];

#[test]
fn verification_level_overrides_shedding_in_either_setter_order() {
    for level in CHECKED_LEVELS {
        let mut certified = Executor::new();
        certified.set_verification_level(level);
        run(&mut certified, ASSERTIONS);
        let expected = run(&mut certified, "(check-sat)");
        assert_eq!(expected, ["unsat"], "noncompetition control must refute");
        assert_eq!(
            certified.last_command_unsat_admission_tag(),
            Some("strict-proof"),
            "the control must actually carry checked proof authority"
        );

        for mode_first in [false, true] {
            let mut executor = Executor::new();
            if mode_first {
                executor.set_competition_mode(true);
                executor.set_verification_level(level);
            } else {
                executor.set_verification_level(level);
                executor.set_competition_mode(true);
            }
            assert!(!executor.competition_shedding_active());
            assert!(!executor.is_producing_proofs());
            run(&mut executor, ASSERTIONS);
            assert_eq!(run(&mut executor, "(check-sat)"), expected);
            assert_eq!(
                executor.last_command_unsat_admission_tag(),
                certified.last_command_unsat_admission_tag(),
                "{level:?}, mode_first={mode_first}: competition cannot weaken authority"
            );
            assert!(executor.last_proof().is_none(), "output was not requested");
            assert_eq!(executor.statistics().get_string("unsat_admission"), None);
        }
    }
}

#[test]
fn verification_level_changes_reconfigure_each_public_solve() {
    let mut executor = Executor::new();
    executor.set_competition_mode(true);
    run(&mut executor, ASSERTIONS);
    for level in [
        VerificationLevel::Trusted,
        VerificationLevel::ProofChecked,
        VerificationLevel::DebugChecked,
        VerificationLevel::FullyVerified,
        VerificationLevel::Trusted,
    ] {
        executor.set_verification_level(level);
        assert_eq!(
            executor.competition_shedding_active(),
            !level.has_proof_checking()
        );
        assert_eq!(run(&mut executor, "(check-sat)"), ["unsat"]);
        let expected = if level.has_proof_checking() {
            "strict-proof"
        } else {
            "competition-raw"
        };
        assert_eq!(executor.last_command_unsat_admission_tag(), Some(expected));
        assert!(!executor.is_producing_proofs());
        assert!(executor.last_proof().is_none());
    }
}

#[test]
fn checked_verification_levels_revoke_unconsumed_raw_tokens() {
    for level in CHECKED_LEVELS {
        let mut executor = Executor::new();
        executor.set_competition_mode(true);
        run(&mut executor, ASSERTIONS);
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let proposed = executor.check_sat().expect("fixed contradiction solves");
        assert!(proposed.is_unsat());
        assert!(executor
            .certify_unsat_for_publication(proposed, &[])
            .is_unsat());
        assert_eq!(
            executor
                .last_unsat_certificate
                .as_ref()
                .expect("anti-vacuity: a raw token was minted")
                .command_admission(),
            CommandUnsatAdmission::CompetitionRaw
        );

        executor.set_verification_level(level);
        assert!(!executor.competition_shedding_active());
        assert!(
            executor.take_unsat_certificate().is_none(),
            "{level:?}: a prior raw token must not satisfy a checked-proof request"
        );
        executor.set_verification_level(VerificationLevel::Trusted);
        assert!(executor.competition_shedding_active());
        assert!(
            executor.take_unsat_certificate().is_none(),
            "re-enabling shedding must not resurrect a consumed token"
        );
    }
}
