// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

/// The opt-in backstop is one complete decision envelope: extending search
/// without certification, or restoring nominal time before publication,
/// makes every answer found in the extra time unusable.
#[test]
fn backstop_envelope_search_certification_and_publication_use_one_grant() {
    let mut exec = Executor::new();
    load_quantified_mix(&mut exec);
    exec.set_timeout(Some(Duration::from_secs(10)));
    exec.set_quantifier_deadline_backstop(true);
    let nominal = Instant::now() + Duration::from_secs(10);

    let command = exec.install_command_publication_deadline();
    let call = exec.install_timeout_deadline_for_call();
    let extended = exec.solve_deadline.get().expect("a timed decision");
    assert!(extended > nominal, "the opt-in must grant additional time");
    assert_eq!(
        exec.certification_deadline.get(),
        Some(extended),
        "search time must remain usable for mandatory certification"
    );
    exec.restore_timeout_deadline_after_call(call);
    assert_eq!(
        exec.solve_deadline.get(),
        Some(extended),
        "publication must not reinstall the nominal wall after search"
    );
    assert_eq!(exec.certification_deadline.get(), Some(extended));
    drop(command);
    assert_eq!(exec.solve_deadline.get(), None);
    assert_eq!(exec.certification_deadline.get(), None);
}

#[test]
fn backstop_envelope_preserves_a_tighter_absolute_owner_wall() {
    let mut exec = Executor::new();
    load_quantified_mix(&mut exec);
    exec.set_timeout(Some(Duration::from_secs(10)));
    let now = Instant::now();
    for (backstop, search, certification) in [
        (true, 20, 30),
        (true, 30, 20),
        (false, 20, 5),
        (false, 5, 20),
    ] {
        exec.set_quantifier_deadline_backstop(backstop);
        let search = now + Duration::from_secs(search);
        let certification = now + Duration::from_secs(certification);
        exec.set_solve_controls(None, Some(certification));
        exec.set_search_deadline(Some(search));
        let command = exec.install_command_publication_deadline();
        let owner = Some(search.min(certification));
        assert_eq!(exec.solve_deadline.get(), owner);
        assert_eq!(exec.certification_deadline.get(), owner);
        drop(command);
        assert_eq!(exec.solve_deadline.get(), Some(search));
        assert_eq!(exec.certification_deadline.get(), Some(certification));
    }
}

#[test]
fn backstop_envelope_default_ground_command_preserves_both_inherited_walls() {
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::from_secs(10)));
    assert!(!exec.quantifier_deadline_backstop());
    let now = Instant::now();
    let search = now + Duration::from_secs(20);
    let certification = now + Duration::from_secs(5);
    exec.set_solve_controls(None, Some(certification));
    exec.set_search_deadline(Some(search));
    let command = exec.install_command_publication_deadline();
    assert_eq!(exec.solve_deadline.get(), Some(certification));
    assert_eq!(exec.certification_deadline.get(), Some(certification));
    drop(command);
    assert_eq!(exec.solve_deadline.get(), Some(search));
    assert_eq!(exec.certification_deadline.get(), Some(certification));
}

#[test]
fn backstop_envelope_text_optimization_uses_soft_and_objective_roots() {
    for formula in [
        "(assert-soft (forall ((x Int)) (p x)))",
        "(minimize (ite (forall ((x Int)) (p x)) 0 1))",
    ] {
        let mut exec = Executor::new();
        let commands = ay_frontend::parse(&format!("(declare-fun p (Int) Bool) {formula}"))
            .expect("quantified optimization formula");
        exec.execute_all(&commands).expect("register optimization");
        exec.set_timeout(Some(Duration::from_secs(10)));
        exec.set_quantifier_deadline_backstop(true);
        let now = Instant::now();
        let raw = exec.install_command_publication_deadline();
        assert!(exec.solve_deadline.get().expect("nominal wall") < now + Duration::from_secs(20));
        drop(raw);
        let text = exec.install_text_optimization_publication_deadline();
        assert!(exec.solve_deadline.get().expect("opted-in wall") > now + Duration::from_secs(30));
        assert_eq!(exec.certification_deadline.get(), exec.solve_deadline.get());
        drop(text);
        assert_eq!(exec.solve_deadline.get(), None);
        assert_eq!(exec.certification_deadline.get(), None);
    }
}

#[test]
fn backstop_envelope_cannot_extend_a_nested_search_slice() {
    let mut exec = Executor::new();
    load_quantified_mix(&mut exec);
    exec.set_timeout(Some(Duration::from_secs(10)));
    exec.set_quantifier_deadline_backstop(true);
    let _command = exec.install_command_publication_deadline();
    let granted = exec.solve_deadline.get();
    let slice = Instant::now();
    exec.set_search_deadline(Some(slice));
    let nested = exec.install_timeout_deadline_for_call();
    assert_eq!(exec.solve_deadline.get(), Some(slice));
    assert_eq!(exec.certification_deadline.get(), granted);
    assert!(exec.make_should_stop()());
    exec.restore_timeout_deadline_after_call(nested);
    assert_eq!(exec.solve_deadline.get(), Some(slice));
    assert_eq!(exec.certification_deadline.get(), granted);
}

#[test]
fn backstop_envelope_script_reset_keeps_the_live_command_owner() {
    let mut exec = Executor::new();
    load_quantified_mix(&mut exec);
    exec.set_timeout(Some(Duration::from_secs(10)));
    exec.set_quantifier_deadline_backstop(true);
    let command = exec.install_command_publication_deadline();
    let granted = exec.solve_deadline.get();
    exec.execute(&ay_frontend::Command::Reset)
        .expect("reset the script state");
    assert!(exec.command_deadline.active());
    assert_eq!(exec.solve_deadline.get(), granted);
    assert_eq!(exec.certification_deadline.get(), granted);
    let nested = exec.install_timeout_deadline_for_call();
    assert_eq!(exec.solve_deadline.get(), granted);
    exec.restore_timeout_deadline_after_call(nested);
    drop(command);
    assert!(!exec.command_deadline.active());
    assert_eq!(exec.solve_deadline.get(), None);
    assert_eq!(exec.certification_deadline.get(), None);
}

#[test]
fn backstop_envelope_keeps_the_original_guard_live_under_certification() {
    use ay_core::resource::{ChildSpec, DeadlineSource, Guard, LiveDeadline, NodeLabel};

    let mut exec = Executor::new();
    load_quantified_mix(&mut exec);
    exec.set_timeout(Some(Duration::from_secs(10)));
    exec.set_quantifier_deadline_backstop(true);
    let owner_wall = Instant::now() + Duration::from_secs(3600);
    let live = LiveDeadline::new(Some(owner_wall));
    let owner = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Live(live.clone())),
    );
    let _in_owner = owner.enter();
    let _command = exec.install_command_publication_deadline();
    let allowed = exec.solve_deadline.get().expect("a relative allowance");
    assert!(allowed < owner_wall);
    assert_eq!(
        owner.deadline(),
        Some(owner_wall),
        "the owner was never renewed"
    );

    let certify = exec.proof_assembly_certify_node();
    let _in_certify = certify.enter();
    live.set(Some(Instant::now()));
    assert!(
        ay_core::resource::check_stop_requested(),
        "the original owner remains binding through CancelOnly certification"
    );
    assert!(exec.should_abort_theory_loop());
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::Timeout));
    assert_eq!(
        exec.solve_deadline.get(),
        Some(allowed),
        "no fresh deadline was minted"
    );
}

#[test]
fn backstop_envelope_original_owner_cancellation_still_stops_certification() {
    use ay_core::resource::{ChildSpec, Guard, NodeLabel};

    let mut exec = Executor::new();
    load_quantified_mix(&mut exec);
    exec.set_timeout(Some(Duration::from_secs(10)));
    exec.set_quantifier_deadline_backstop(true);
    let owner = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let _in_owner = owner.enter();
    let _command = exec.install_command_publication_deadline();
    let certify = exec.proof_assembly_certify_node();
    let _in_certify = certify.enter();
    owner.cancel();
    assert!(ay_core::resource::check_stop_requested());
    assert!(exec.should_abort_theory_loop());
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::Interrupted));
}

#[test]
fn backstop_envelope_cannot_replenish_a_spent_counted_owner() {
    use ay_core::resource::{enter_work_grant, work, work_grant_spent};

    let mut exec = Executor::new();
    load_quantified_mix(&mut exec);
    exec.set_timeout(Some(Duration::from_secs(10)));
    exec.set_quantifier_deadline_backstop(true);
    let grant = enter_work_grant(0);
    work().note_round_trip();
    assert!(work_grant_spent());
    let spent = grant.spent_round_trips();
    let command = exec.install_command_publication_deadline();
    let call = exec.install_timeout_deadline_for_call();
    assert!(exec.should_abort_theory_loop());
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::ResourceLimit));
    exec.restore_timeout_deadline_after_call(call);
    drop(command);
    assert!(work_grant_spent());
    assert_eq!(grant.spent_round_trips(), spent);
}

#[test]
fn backstop_envelope_draws_only_the_counted_owners_remaining_allowance() {
    use ay_core::resource::{ChildSpec, Guard, NodeLabel};

    let mut exec = Executor::new();
    load_quantified_mix(&mut exec);
    exec.set_timeout(Some(Duration::from_secs(10)));
    exec.set_quantifier_deadline_backstop(true);
    let owner = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(10)));
    owner.record_ticks(3);
    let _in_owner = owner.enter();
    let _command = exec.install_command_publication_deadline();
    let check = exec.open_check_node();
    assert_eq!(check.allotment(), Some(7));
    check.record_ticks(2);
    drop(check);
    assert_eq!(
        owner.remaining(),
        Some(5),
        "command entry cannot reset the owner count"
    );
}

#[test]
fn backstop_envelope_unwind_restores_both_walls_and_the_original_callback() {
    use ay_core::resource::{current_check_stop, enter_check_stop, CheckStop};

    let mut exec = Executor::new();
    load_quantified_mix(&mut exec);
    exec.set_timeout(Some(Duration::from_secs(10)));
    exec.set_quantifier_deadline_backstop(true);
    let owner = Instant::now() + Duration::from_secs(60);
    let search = Instant::now() + Duration::from_secs(50);
    exec.set_solve_controls(None, Some(owner));
    exec.set_search_deadline(Some(search));
    let stop = Arc::new(AtomicBool::new(false));
    let observed = stop.clone();
    let callback: CheckStop = Arc::new(move || observed.load(Ordering::Relaxed));
    let _callback_scope = enter_check_stop(callback.clone());
    let caller = ay_core::resource::Guard::root_child(
        ay_core::resource::ChildSpec::new(ay_core::resource::NodeLabel::Check)
            .with_deadline(ay_core::resource::DeadlineSource::Fixed(owner)),
    );
    let _in_caller = caller.enter();
    let command = exec.install_command_publication_deadline();
    stop.store(true, Ordering::Relaxed);
    assert!(
        ay_core::resource::check_stop_requested(),
        "the original callback is composed"
    );
    stop.store(false, Ordering::Relaxed);
    let call = exec.install_timeout_deadline_for_call();
    exec.set_search_deadline(Some(Instant::now()));
    let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        let _command = command;
        let _call = call;
        panic!("abort one decision command");
    }));
    assert!(unwind.is_err());
    assert_eq!(exec.solve_deadline.get(), Some(search));
    assert_eq!(exec.certification_deadline.get(), Some(owner));
    assert!(!exec.command_deadline.active());
    let restored = current_check_stop()
        .expect("readable callback")
        .expect("original callback");
    assert!(Arc::ptr_eq(&restored, &callback));
}
