// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `cegqi.rs` to preserve the regression test FQN.

/// Why `closed_universal_precheck_in_proof_mode` DEFAULTS OFF, pinned so that
/// fixing it is noticed rather than guessed at.
///
/// The closed-universal precheck can refute `(forall ((x Int)) (> x 0))` with the
/// literal witness `0`. In proof mode it is nevertheless disarmed, because the
/// certificate it produces is still weaker than the one CEGQI already
/// produces for the same file:
///
/// | | steps | hole | instantiation |
/// |---|---|---|---|
/// | CEGQI (default)  | 5 | no  | `(> 0 0)` — the authored surface form |
/// | precheck (armed) | 9 | no | `(< 0 x_0)` — normalized and rebound |
///
/// The precheck formerly mislabeled `(cl (not false))` as Alethe `true`, which
/// made the printer demote the step to `hole`. That defect is fixed and stays
/// pinned below: the armed proof must remain hole-free.
///
/// The remaining orientation defect matters because `607b19b5c9` ("fix(soundness): bind
/// quantified verdicts to exact authority") pins instantiation to the authored
/// surface form. Installing presentation overrides directly is not a valid
/// repair: `promoted_wire_rule` refuses to promote `LiaGeneric` under overrides.
/// The candidate instead needs to enter the ordinary `build_unsat_proof` path.
///
/// So this is a PRE-EMPT weaker than what it displaces — the same error the QE
/// alternation route made. When the orientation assertion fails, delete this
/// test and default the knob on.
#[test]
fn closed_universal_precheck_in_proof_mode_is_still_weaker_than_cegqi() {
    #[derive(Clone, Copy)]
    enum PrecheckMode {
        Default,
        Armed,
    }

    let export = |mode: PrecheckMode| {
        let armed = matches!(mode, PrecheckMode::Armed);
        let input = r#"
            (set-logic QF_LIA)
            (set-option :produce-proofs true)
            (assert (forall ((x Int)) (> x 0)))
            (check-sat)
        "#;
        let commands = parse(input).unwrap();
        let mut exec = Executor::new();
        exec.set_produce_proofs(true);
        exec.set_closed_universal_precheck_in_proof_mode(armed);
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(outputs, vec!["unsat"], "armed={armed}");
        exec.try_export_last_proof_alethe_for_problem_scope()
            .expect("certified UNSAT must retain an exportable proof")
            .expect("Alethe export must succeed")
    };

    let default_proof = export(PrecheckMode::Default);
    assert!(
        !default_proof.contains(":rule hole"),
        "the DEFAULT path must stay hole-free: {default_proof}"
    );
    assert!(
        default_proof.contains("(> 0 0)"),
        "the DEFAULT path must keep the authored surface orientation: {default_proof}"
    );

    let armed_proof = export(PrecheckMode::Armed);
    // The Alethe false-axiom label is now a requirement, not a known defect.
    assert!(
        !armed_proof.contains(":rule hole"),
        "the armed precheck must not emit an unverifiable `hole`: {armed_proof}"
    );
    // Surface orientation is the only remaining blocker.
    assert!(
        !armed_proof.contains("(> 0 0)"),
        "REMOVE THIS TEST AND DEFAULT THE KNOB ON: the armed precheck now keeps \
         the authored surface orientation: {armed_proof}"
    );
}
