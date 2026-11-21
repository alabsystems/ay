// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_frontend::command::Term as Parsed;

fn native(exec: &mut Executor, text: &str) -> TermId {
    let ay_frontend::command::Command::Assert(parsed) =
        ay_frontend::parse(&format!("(assert {text})"))
            .unwrap()
            .remove(0)
    else {
        panic!("assertion")
    };
    let term = exec.ctx.elaborate_surface_subterm(&parsed).unwrap();
    exec.ctx.add_native_assertion_with_parsed(
        term,
        Parsed::Symbol(crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.into()),
    );
    term
}

fn fixture(decls: &str, roots: &[&str]) -> (Executor, Vec<TermId>) {
    let mut exec = Executor::new();
    exec.execute_all(&ay_frontend::parse(&format!(
        "(set-logic ALL) (set-option :produce-proofs true) (set-option :check-proofs-strict true) {decls}"
    )).unwrap()).unwrap();
    let originals = roots.iter().map(|s| native(&mut exec, s)).collect();
    exec.begin_external_decision_query(false);
    exec.bind_unsat_query_assumptions(&[]);
    (exec, originals)
}

fn complete(exec: &mut Executor, originals: &[TermId]) -> Proof {
    let before = exec.ctx.assertions.clone();
    let proof = exec
        .native_source_quantifier_refutation()
        .expect("actual full-source derivation");
    assert_eq!(
        before, exec.ctx.assertions,
        "proof planning changes no working root"
    );
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    ay_proof::validate_reachable_assumes_in_problem_scope(&proof, originals).unwrap();
    assert!(proof.steps.iter().all(|s| !matches!(s,
        ProofStep::Assume(term) if !originals.contains(term))));
    proof
}

#[test]
fn native_source_refutation_bool_ite_and_empty_both_polarities_use_originals() {
    for (decls, roots) in [
        (
            "(declare-fun member (Bool) Bool)",
            vec![
                "(forall ((x Bool)) (= (member x) true))",
                "(not (forall ((x Bool)) (=> (member x) (ite x x (not x)))))",
            ],
        ),
        (
            "(declare-fun member (Bool) Bool)",
            vec![
                "(forall ((x Bool)) (= (member x) true))",
                "(not (exists ((x Bool)) (and (member x) (ite x x (not x)))))",
            ],
        ),
        (
            "(declare-sort Empty 0) (declare-fun member (Empty) Bool)",
            vec![
                "(forall ((x Empty)) (= (member x) false))",
                "(not (forall ((x Empty)) (=> (member x) false)))",
            ],
        ),
        (
            "(declare-sort Empty 0) (declare-fun member (Empty) Bool)",
            vec![
                "(forall ((x Empty)) (= (member x) false))",
                "(exists ((x Empty)) (member x))",
            ],
        ),
        (
            "(declare-datatype Unit ((unit))) (declare-fun member (Unit) Bool)",
            vec![
                "(forall ((x Unit)) (= (member x) true))",
                "(forall ((x Unit)) (=> (member x) false))",
            ],
        ),
        (
            "(declare-datatype Unit ((unit))) (declare-fun member (Unit) Bool)",
            vec![
                "(forall ((x Unit)) (= (member x) true))",
                "(not (exists ((x Unit)) (member x)))",
            ],
        ),
    ] {
        let (mut exec, originals) = fixture(decls, &roots);
        let proof = complete(&mut exec, &originals);
        assert!(proof.steps.iter().any(|s| matches!(
            s,
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                ..
            }
        )));
    }
}

#[test]
fn native_source_refutation_guarded_function_range_uses_a_witness_application() {
    let (mut exec, originals) = fixture(
        "(declare-fun valid (Int) Bool) (declare-fun f (Int) Int)",
        &[
            "(forall ((x Int)) (valid x))",
            "(forall ((x Int)) (=> (valid x) (= (f x) x)))",
            "(not (forall ((x Int)) (=> (valid x) (valid (f x)))))",
        ],
    );
    let proof = complete(&mut exec, &originals);
    assert!(proof.steps.iter().any(|step| matches!(step,
        ProofStep::Step { rule: AletheRule::ForallInst, args, .. }
            if args.iter().any(|&arg| matches!(exec.ctx.terms.get(arg),
                TermData::App(name, _) if name.name() == "f")))));
}

#[test]
fn native_source_refutation_does_not_invent_a_guard_or_opaque_inhabitant() {
    for (decls, roots) in [
        (
            "(declare-fun valid (Int) Bool) (declare-fun f (Int) Int)",
            vec![
                "(forall ((x Int)) (=> (valid x) (= (f x) x)))",
                "(not (forall ((x Int)) (valid x)))",
            ],
        ),
        (
            "(declare-sort Empty 0) (declare-fun member (Empty) Bool)",
            vec![
                "(forall ((x Empty)) (= (member x) false))",
                "(not (exists ((x Empty)) (member x)))",
            ],
        ),
        (
            "(declare-datatype Unit ((unit))) (declare-fun member (Unit) Bool)",
            vec![
                "(forall ((x Unit)) (= (member x) true))",
                "(exists ((x Unit)) (member x))",
            ],
        ),
        (
            "(declare-fun member (Bool) Bool)",
            vec![
                "(forall ((x Bool)) (= (member x) true))",
                "(not (forall ((x Bool)) (=> (member x) x)))",
            ],
        ),
    ] {
        let (mut exec, _) = fixture(decls, &roots);
        let original = exec.ctx.assertions.clone();
        assert!(
            exec.native_source_quantifier_refutation().is_none(),
            "{roots:?}"
        );
        assert_eq!(exec.ctx.assertions, original);
        assert_eq!(
            exec.proof_tracker.num_steps(),
            0,
            "no partial fragment is installed"
        );
    }
}

#[test]
fn native_source_refutation_ignores_working_false_and_is_one_attempt_per_owner() {
    let (mut exec, originals) = fixture(
        "(declare-fun p (Bool) Bool)",
        &["(forall ((b Bool)) (p b))", "(p true)"],
    );
    // A false working root cannot replace this actual satisfiable source.
    exec.ctx.assertions = vec![exec.ctx.terms.false_term()];
    assert!(exec.native_source_quantifier_refutation().is_none());
    assert!(exec.native_source_quantifier_refutation().is_none());
    assert_eq!(exec.proof_tracker.num_steps(), 0);
    assert_ne!(exec.ctx.assertions, originals);
}

#[test]
fn native_source_refutation_cascade_retains_a_publishable_incumbent_without_an_attempt() {
    let (mut exec, originals) = fixture(
        "(declare-const p Bool)",
        &["(forall ((b Bool)) (= b b))", "p", "(not p)"],
    );
    let mut proof = Proof::new();
    let positive = proof.add_assume(originals[1], None);
    let negative = proof.add_assume(originals[2], None);
    proof.add_resolution(vec![], originals[1], positive, negative);
    assert!(exec.authored_cascade_publishable(&proof));
    let original = proof.clone();

    exec.run_authored_replacement_cascade(&mut proof);

    assert_eq!(proof, original);
    assert!(
        exec.native_universal_budget
            .borrow_mut()
            .claim_source_refutation()
            .is_some(),
        "the clean proof did not consume a native planning attempt"
    );
}

#[test]
fn native_source_refutation_cancel_is_sticky_and_text_never_supplies_authority() {
    let (mut exec, _) = fixture("", &["(not (forall ((b Bool)) (= b b)))"]);
    let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(true));
    exec.set_interrupt(stop.clone());
    assert!(exec.native_source_quantifier_refutation().is_none());
    stop.store(false, std::sync::atomic::Ordering::SeqCst);
    assert!(exec.native_source_quantifier_refutation().is_none());
    let mut text = Executor::new();
    text.execute_all(
        &ay_frontend::parse(
            "(set-option :produce-proofs true) (assert (not (forall ((b Bool)) (= b b))))",
        )
        .unwrap(),
    )
    .unwrap();
    text.begin_external_decision_query(false);
    text.bind_unsat_query_assumptions(&[]);
    assert!(text.native_source_quantifier_refutation().is_none());
}

#[test]
fn native_source_refutation_final_checker_rejects_wrong_instance_and_dropped_guard() {
    let (mut exec, originals) = fixture(
        "(declare-fun p (Int) Bool)",
        &["(forall ((x Int)) (p x))", "(not (forall ((x Int)) (p x)))"],
    );
    let proof = complete(&mut exec, &originals);
    let mut forged = proof.clone();
    let args = forged
        .steps
        .iter_mut()
        .find_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                args,
                ..
            } => Some(args),
            _ => None,
        })
        .unwrap();
    args[0] = exec.ctx.terms.true_term();
    assert!(exec.check_proof_strict_with_datatypes(&forged).is_err());
    let incomplete = &originals[1..];
    assert!(ay_proof::check_proof_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        Some(incomplete)
    )
    .is_err());
}

#[test]
fn native_source_refutation_exact_wp_native_body_packets_keep_roots_and_5624ms() {
    use crate::api::{NativeReplayArtifact, ProofAcceptanceMode, Solver};
    use sha2::{Digest, Sha256};
    for (input, digest, roots) in [
        (
            include_str!(
                "../../../../../api/solving/native_replay/data/wp_nested_body_native.json"
            ),
            "aaf2050e05a8aec239632e43ef4c99b0250cb734fdf2aad7fec9b3e6c6d6d340",
            &[7_u32, 10, 17, 21][..],
        ),
        (
            include_str!("../../../../../api/solving/native_replay/data/wp_bool_body_native.json"),
            "b2cf0bdb7dc80bc9d704ce0ae35ffa9552ad9e33abe98cf5bdaf9cacdcedee89",
            &[7_u32, 10, 17][..],
        ),
    ] {
        assert_eq!(format!("{:x}", Sha256::digest(input.as_bytes())), digest);
        let original = NativeReplayArtifact::from_json_str(input).unwrap();
        assert_eq!(original.timeout_ms, Some(5_624));
        assert_eq!(
            original
                .assertions
                .iter()
                .map(|a| a.term.0)
                .collect::<Vec<_>>(),
            roots
        );
        let before = original.to_json_value();
        let (details, proof) = Solver::replay_native_replay_artifact_with_checked_proof(
            &original,
            std::time::Duration::from_millis(5_624),
        )
        .unwrap();
        assert_eq!(before, original.to_json_value());
        assert!(details.result.is_unsat(), "{details:?}");
        assert!(details.verification.unsat_proof_strictly_verified);
        let proof = proof.expect("actual full original WP input requires a checked proof");
        proof
            .accept_for_consumer(ProofAcceptanceMode::Strict)
            .unwrap();
        assert_eq!(proof.quality.trust_count, 0);
        assert_eq!(proof.quality.hole_count, 0);
    }
}

#[test]
fn native_source_refutation_completed_attempt_cannot_remint_or_renew() {
    let (mut exec, originals) = fixture("", &["(not (forall ((b Bool)) (= b b)))"]);
    complete(&mut exec, &originals);
    let metadata = exec.ctx.terms.checker_visible_metadata_generation();
    let terms = exec.ctx.terms.len();
    assert!(exec.native_source_quantifier_refutation().is_none());
    assert_eq!(
        exec.ctx.terms.checker_visible_metadata_generation(),
        metadata
    );
    assert_eq!(exec.ctx.terms.len(), terms);
}

#[test]
fn native_source_refutation_whole_pinned_carcara_and_semantic_forgery() {
    use sha2::{Digest, Sha256};
    use std::process::{Command, Stdio};
    use wait_timeout::ChildExt;
    let (mut exec, originals) = fixture(
        "(declare-fun p (Int) Bool)",
        &["(forall ((x Int)) (p x))", "(not (forall ((x Int)) (p x)))"],
    );
    let proof = complete(&mut exec, &originals);
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &originals,
        None,
    )
    .unwrap();
    assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
    let mut problem = String::from("(set-logic ALL)\n(declare-fun p (Int) Bool)\n");
    for &root in &originals {
        problem.push_str(&format!(
            "(assert {})\n",
            ay_proof::format_term_alethe(&exec.ctx.terms, root)
        ));
    }
    problem.push_str("(check-sat)\n");
    ay_core::pinned_carcara::pinned_carcara_can_judge(&problem, &document).unwrap();
    let binary = std::env::var_os("CARCARA_PATH")
        .map(std::path::PathBuf::from)
        .or_else(|| {
            std::env::split_paths(&std::env::var_os("PATH")?)
                .map(|p| p.join("carcara"))
                .find(|p| p.is_file())
        })
        .unwrap()
        .canonicalize()
        .unwrap();
    let before = Sha256::digest(std::fs::read(&binary).unwrap());
    // Exact builds of Carcara at 9a352ee, including the native Linux build
    // used by competition replay. An arbitrary executable from PATH cannot
    // establish the positive or the forged-proof control.
    let expected = match (std::env::consts::OS, std::env::consts::ARCH) {
        ("macos", "aarch64") => "e27cb05e4119ac8ece1b3ba70cab2b7aae710fae70ad2252d0086be8d3b363a9",
        ("macos", "x86_64") => "db27f7fe19c26ee14e53981e333b159dd216a757972ff4fc24d6c8c01703a532",
        ("linux", "x86_64") => "dc5c2dcd78405777cb42ab0c6e98956ea3d450e6d6eaf1cb1d0b4120bce04102",
        host => panic!("no pinned Carcara executable for {host:?}"),
    };
    assert_eq!(format!("{before:x}"), expected);
    let dir = tempfile::tempdir().unwrap();
    let smt = dir.path().join("original.smt2");
    let alethe = dir.path().join("whole.alethe");
    std::fs::write(&smt, &problem).unwrap();
    let mut altered = document.clone();
    let start = altered.rfind(":rule ").unwrap() + 6;
    let end = altered[start..]
        .find(|c: char| c.is_ascii_whitespace() || c == ')')
        .map_or(altered.len(), |n| start + n);
    altered.replace_range(start..end, "refl");
    for (tag, text, expected) in [
        ("positive", &document, "valid"),
        ("forged-refl", &altered, "invalid"),
    ] {
        std::fs::write(&alethe, text).unwrap();
        let out = dir.path().join(format!("{tag}.out"));
        let err = dir.path().join(format!("{tag}.err"));
        let mut child = Command::new(&binary)
            .args(["check", "--"])
            .arg(&alethe)
            .arg(&smt)
            .stdin(Stdio::null())
            .stdout(std::fs::File::create(&out).unwrap())
            .stderr(std::fs::File::create(&err).unwrap())
            .spawn()
            .unwrap();
        let Some(status) = child
            .wait_timeout(std::time::Duration::from_secs(5))
            .unwrap()
        else {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("pinned checker five-second envelope");
        };
        assert!(std::fs::metadata(&out).unwrap().len() < 1 << 20);
        assert!(std::fs::metadata(&err).unwrap().len() < 1 << 20);
        let output = std::fs::read_to_string(&out).unwrap();
        let errors = std::fs::read_to_string(&err).unwrap();
        assert_eq!(status.success(), expected == "valid", "{output}\n{errors}");
        assert!(
            output.lines().any(|line| line == expected),
            "{output}\n{errors}"
        );
    }
    assert_eq!(before, Sha256::digest(std::fs::read(&binary).unwrap()));
    eprintln!("native source refutation whole pinned: checker={before:x} problem={:x} proof={:x}; final empty refl rejected",Sha256::digest(problem.as_bytes()),Sha256::digest(document.as_bytes()));
}

#[test]
fn native_source_refutation_exhausted_shared_work_or_storage_stops_before_terms() {
    for (work, bytes) in [(32 * 1024 * 1024, 0), (0, 32 * 1024 * 1024)] {
        let (mut exec, _) = fixture("", &["(not (forall ((b Bool)) (= b b)))"]);
        let terms = exec.ctx.terms.len();
        let metadata = exec.ctx.terms.checker_visible_metadata_generation();
        assert!(exec.charge_native_universal(work, bytes).is_none());
        assert!(exec.native_source_quantifier_refutation().is_none());
        assert_eq!(exec.ctx.terms.len(), terms);
        assert_eq!(
            exec.ctx.terms.checker_visible_metadata_generation(),
            metadata
        );
        assert_eq!(exec.proof_tracker.num_steps(), 0);
    }
}

#[test]
fn native_source_refutation_borrows_bool_var_and_constant_leaves_without_copying() {
    let (mut exec, _) = fixture("", &["(forall ((b Bool)) b)"]);
    let variable = exec
        .ctx
        .terms
        .mk_fresh_var("borrowed_bool_leaf", Sort::Bool);
    let yes = exec.ctx.terms.true_term();
    let no = exec.ctx.terms.false_term();
    for term in [variable, yes, no] {
        assert!(
            exec.ctx
                .terms
                .try_copy_native_proof_node_with_progress(term, &mut |_, _| true)
                .is_err(),
            "the owned compound-copy API must remain narrow"
        );
    }
    let mut closure = Closure::new(&mut exec);
    let mut left = 4096;
    for term in [variable, yes, no] {
        closure
            .walk(term, 0, &mut left)
            .expect("borrowed actual Bool leaf");
    }
    assert_eq!(left, 4093, "each actual leaf occurrence is debited once");
    assert!(
        closure.proof.steps.is_empty(),
        "a borrowed leaf adds no law"
    );
    assert!(closure.clauses.is_empty());
    assert!(
        closure.visited.is_empty(),
        "leaves need no owned copy/memo payload"
    );
}

#[test]
fn native_source_refutation_choice_walk_borrows_typed_witness_and_int_constant() {
    let (mut exec, _) = fixture(
        "(declare-fun p (Int) Bool) (declare-fun f (Int) Int)",
        &["(not (forall ((x Int)) (=> (p x) (= (f x) 0))))"],
    );
    let initial = NativeUniversalSource::capture(&exec).unwrap();
    let (_, choices, _) = exec.plan_native_source_offers(initial, false).unwrap();
    assert_eq!(choices.len(), 1);
    let witness = choices[0].witness;
    assert!(exec
        .ctx
        .terms
        .try_copy_native_proof_node_with_progress(witness, &mut |_, _| true)
        .is_err());
    let mut closure = Closure::new(&mut exec);
    let mut values = Vec::new();
    closure
        .choice_values(&choices, &Sort::Int, &mut values)
        .unwrap();
    assert!(
        values.contains(&witness),
        "actual typed witness is retained as a proposal"
    );
    assert!(values
        .iter()
        .any(|&term| matches!(closure.exec.ctx.terms.get(term),
        TermData::Const(ay_core::Constant::Int(value)) if value == &num_bigint::BigInt::from(0))));
    assert!(values
        .iter()
        .any(|&term| matches!(closure.exec.ctx.terms.get(term),
        TermData::App(name, args) if name.name() == "f" && args == &[witness])));
    assert!(values
        .iter()
        .all(|&term| closure.exec.ctx.terms.sort(term) == &Sort::Int));
    assert!(
        closure.proof.steps.is_empty(),
        "proposals grant no source/value facts"
    );
}

#[test]
fn native_source_refutation_borrowed_leaves_keep_stored_kind_and_bool_sort_guards() {
    for (literal, sort) in [
        (ay_core::Constant::Int(7.into()), Sort::Bool),
        (ay_core::Constant::Bool(false), Sort::Int),
    ] {
        let mut exec = Executor::new();
        exec.ctx.terms = TermStore::from_entries(
            vec![
                (TermData::Const(ay_core::Constant::Bool(false)), Sort::Bool),
                (TermData::Const(ay_core::Constant::Bool(true)), Sort::Bool),
                (TermData::Const(literal), sort),
            ],
            Some(TermId(1)),
            Some(TermId(0)),
            0,
        );
        exec.begin_external_decision_query(false);
        exec.bind_unsat_query_assumptions(&[]);
        let mut closure = Closure::new(&mut exec);
        assert!(closure.walk(TermId(2), 0, &mut 4096).is_none());
        assert!(closure.proof.steps.is_empty());
        assert!(
            closure.visited.is_empty(),
            "a refused leaf never seeds a successful memo"
        );
        assert!(closure.walk(TermId(u32::MAX), 0, &mut 4096).is_none());
    }
}
