// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn control_lifetime_clear_solve_controls_clears_certification_deadline() {
    let mut exec = Executor::new();
    exec.set_solve_controls(
        Some(Arc::new(AtomicBool::new(false))),
        Some(Instant::now() + Duration::from_mins(1)),
    );

    exec.clear_solve_controls();

    assert!(exec.solve_interrupt.is_none());
    assert_eq!(exec.solve_deadline.get(), None);
    assert_eq!(exec.certification_deadline.get(), None);
}

/// Load a small quantified+ground mixed assertion set (no check-sat).
fn load_quantified_mix(exec: &mut Executor) {
    let commands = ay_frontend::parse(
        "(set-logic UFLIA)\
         (declare-fun f (Int) Int)\
         (declare-const a Int)\
         (assert (forall ((x Int)) (>= (f x) 0)))\
         (assert (> a 0))",
    )
    .expect("test input must parse");
    exec.execute_all(&commands)
        .expect("setup commands must run");
}

#[test]
fn control_lifetime_command_publication_preserves_one_nominal_deadline() {
    let mut exec = Executor::new();
    load_quantified_mix(&mut exec);
    // #honest-timeout: the quantified backstop is opt-in now, and this fixture
    // is specifically about the RESTORE of a relaxed deadline, so select it.
    exec.set_quantifier_deadline_backstop(true);
    exec.set_timeout(Some(Duration::from_secs(10)));

    let before_command = exec.install_command_publication_deadline();
    assert_eq!(before_command, (None, None));
    let nominal = exec
        .solve_deadline
        .get()
        .expect("the command scope must install its absolute deadline");
    assert_eq!(exec.certification_deadline.get(), Some(nominal));

    // The nested solve may temporarily relax a quantified deadline, but must
    // restore the exact command value before publication begins.
    let before_solve = exec.install_timeout_deadline_for_call();
    assert_eq!(before_solve, Some(nominal));
    assert!(
        exec.solve_deadline
            .get()
            .is_some_and(|deadline| deadline > nominal),
        "the fixture must exercise quantified deadline relaxation"
    );
    exec.restore_timeout_deadline_after_call(before_solve);
    assert_eq!(
        exec.solve_deadline.get(),
        Some(nominal),
        "certification must inherit the original absolute deadline, not a renewed timeout"
    );

    exec.restore_command_publication_deadline_after_call(before_command);
    assert_eq!(
        exec.solve_deadline.get(),
        None,
        "the complete command scope must restore its predecessor"
    );
    assert_eq!(exec.certification_deadline.get(), None);
}

#[test]
fn control_lifetime_command_publication_uses_tighter_relative_deadline() {
    let mut exec = Executor::new();
    let persistent = Instant::now() + Duration::from_mins(1);
    exec.set_deadline(Some(persistent));
    exec.set_timeout(Some(Duration::from_secs(10)));

    let before_command = exec.install_command_publication_deadline();
    assert_eq!(before_command, (Some(persistent), Some(persistent)));
    let command_deadline = exec
        .solve_deadline
        .get()
        .expect("the command scope must retain a deadline");
    assert!(
        command_deadline < persistent,
        "the relative timeout must tighten the persistent deadline"
    );
    assert_eq!(
        exec.certification_deadline.get(),
        Some(command_deadline),
        "certification must honor the complete command's tighter timeout"
    );

    exec.restore_command_publication_deadline_after_call(before_command);
    assert_eq!(exec.solve_deadline.get(), Some(persistent));
    assert_eq!(exec.certification_deadline.get(), Some(persistent));
}

#[test]
fn control_lifetime_command_publication_restores_deadline_after_elaboration_error() {
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::from_secs(10)));
    let command = ay_frontend::parse("(check-sat-assuming (undeclared_symbol))")
        .expect("the malformed query is syntactically valid")
        .pop()
        .expect("one command must parse");

    assert!(
        exec.execute_authored(&command).is_err(),
        "an undeclared assumption must fail elaboration"
    );
    assert_eq!(
        exec.solve_deadline.get(),
        None,
        "an error path must not leak the command publication deadline"
    );
    assert_eq!(
        exec.certification_deadline.get(),
        None,
        "an error path must not leak the certification deadline"
    );
}
