use super::*;

fn provenance_for(
    exec: &mut Executor,
    value: i64,
) -> crate::ematching::ForallInstantiationProvenance {
    let forall = exec.ctx.assertions[0];
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(forall).clone() else {
        panic!("fixture asserts a forall");
    };
    let value = exec.ctx.terms.mk_int(value.into());
    let mut subst = ay_core::kani_compat::DetHashMap::default();
    subst.insert(vars[0].0.clone(), value);
    let instance = crate::ematching::subst_vars_exact_qf(&mut exec.ctx.terms, body, &subst)
        .expect("fixture body is quantifier-free");
    crate::ematching::ForallInstantiationProvenance {
        quantifier: forall,
        binding: vec![value],
        instance,
    }
}

fn executor_with_instance(script: &str, value: i64) -> Executor {
    let commands = ay_frontend::parse(script).expect("ground-pin fixture parses");
    let mut exec = Executor::new();
    assert!(exec
        .execute_all(&commands)
        .expect("fixture loads")
        .is_empty());
    let record = provenance_for(&mut exec, value);
    exec.ematching_proof_records
        .push(crate::executor::EmatchingProofRecord {
            assertion_index: 0,
            quantifier: record.quantifier,
            binding: record.binding,
            instance: record.instance,
        });
    exec
}

fn pinned_instance_executor(pinned_value: i64) -> Executor {
    executor_with_instance(&pinned_instance_problem(pinned_value), 2)
}

fn pinned_instance_problem(pinned_value: i64) -> String {
    format!(
        r#"
                (set-logic AUFLIA)
                (declare-fun f (Int) Int)
                (assert (forall ((x Int)) (< (+ x 1) (f x))))
                (assert (= (f 2) {pinned_value}))
            "#
    )
}

fn direct_candidate(exec: &mut Executor) -> Option<Proof> {
    let record = exec
        .ematching_proof_records
        .first()
        .expect("fixture installed one record");
    let (quantifier, binding, instance) =
        (record.quantifier, record.binding.clone(), record.instance);
    let authored = exec.exact_concrete_authored_scope();
    let closure = exec.authored_and_conjunct_closure(&authored);
    let mut plans = ay_core::kani_compat::DetHashMap::default();
    plans.insert(
        instance,
        ConsequencePlan::ForallInstance {
            quantifier,
            binding,
        },
    );
    exec.try_ground_pinned_instance_refutation(&authored, &closure, &plans, &[instance])
}

#[test]
fn ground_pin_instance_refutation_is_strictly_checked() {
    let mut exec = pinned_instance_executor(3);
    assert!(exec.try_translate_authored_consequence_replay_unsat());
    let proof = exec.last_proof.clone().expect("translation installs proof");
    exec.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::GroundEqualitySubstitution,
            ..
        }
    )));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Evaluate,
            ..
        }
    )));
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(
        !exec.proof_has_known_wire_gap(&proof),
        "structural substitution and the separate checked evaluation are exportable"
    );
    let authored = exec.exact_concrete_authored_scope();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok());
    let overrides = exec.proof_export_term_overrides();
    let text = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &authored,
        overrides.as_ref(),
    )
    .expect("original-scope ground-pin export");
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    let path = std::env::temp_dir().join(format!(
        "ay-ground-pin-original-scope-{}.json",
        std::process::id()
    ));
    let problem = format!("{}\n(check-sat)\n", pinned_instance_problem(3));
    std::fs::write(
        &path,
        serde_json::to_vec(&serde_json::json!({
            "type": "alethe_certificate", "version": "1.0", "problem": problem, "proof": text,
        }))
        .unwrap(),
    )
    .unwrap();
    println!("independent ground-pin certificate: {}", path.display());
}

/// Pinned carcara's last verdict line on `proof` against `problem` in AY's
/// canonical invocation (`carcara check -- PROOF PROBLEM`), or `None` when
/// carcara is not installed; under `CI` a missing carcara fails the test.
fn pinned_carcara_verdict(tag: &str, problem: &str, proof: &str) -> Option<String> {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) {
        panic!("{tag}: {misjudged}\n{proof}");
    }
    let installed = std::env::var_os("CARCARA_PATH")
        .map(std::path::PathBuf::from)
        .into_iter()
        .chain(
            std::env::var_os("HOME")
                .map(|home| std::path::PathBuf::from(home).join(".cargo/bin/carcara")),
        )
        .chain(
            std::env::var_os("PATH")
                .into_iter()
                .flat_map(|path| std::env::split_paths(&path).collect::<Vec<_>>())
                .map(|directory| directory.join("carcara")),
        )
        .find(|candidate| candidate.is_file());
    let Some(carcara) = installed else {
        assert!(
            std::env::var_os("CI").is_none(),
            "{tag}: carcara is not installed, and the replay is mandatory in CI"
        );
        eprintln!("{tag}: carcara is not installed; the pinned replay is skipped");
        return None;
    };
    let stem = std::env::temp_dir().join(format!("ay-ground-pin-{tag}-{}", std::process::id()));
    let (problem_path, proof_path) = (stem.with_extension("smt2"), stem.with_extension("alethe"));
    std::fs::write(&problem_path, problem).expect("write problem");
    std::fs::write(&proof_path, proof).expect("write proof");
    let output = std::process::Command::new(carcara)
        .arg("check")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara");
    let _ = std::fs::remove_file(&problem_path);
    let _ = std::fs::remove_file(&proof_path);
    let stdout = String::from_utf8_lossy(&output.stdout);
    Some(stdout.lines().last().unwrap_or("").trim().to_string())
}

/// The authored instance with the pinned `x = 2`, translated and exported:
/// the screen's wire-gap judgement and the exported document.
fn changed_instance_surface_export(body: &str) -> (String, bool, String) {
    let problem = pinned_instance_problem(3).replace("(< (+ x 1) (f x))", body);
    let mut exec = executor_with_instance(&problem, 2);
    assert!(exec.try_translate_authored_consequence_replay_unsat());
    let proof = exec.last_proof.clone().expect("native proof is complete");
    exec.restore_reachable_authored_assume_surface_overrides(&proof);
    let wire_gap = exec.proof_has_known_wire_gap(&proof);
    let authored = exec.exact_concrete_authored_scope();
    let overrides = exec.proof_export_term_overrides();
    let text = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &authored,
        overrides.as_ref(),
    )
    .expect("the changed instance surface exports");
    (format!("{problem}\n(check-sat)\n"), wire_gap, text)
}

/// The authored `(> (f x) (+ x 1))` instance is not the canonical
/// `(< (+ 2 1) (f 2))` the substitution lemma reads. The publication screen
/// still judges the authored spelling a wire gap (it does not model the
/// confined-instance channel: conservative), but the exporter confines the
/// authored instance to its `forall_inst` and derives the canonical one with
/// `comp_simplify` (`surface_equivalence/comparison.rs`), so the lemma
/// lowers without a `hole` and pinned carcara re-derives every step. Until
/// that schema this document held a `hole` for the instance.
#[test]
fn ground_pin_reversed_instance_surface_is_derived_without_a_hole() {
    let (problem, wire_gap, text) = changed_instance_surface_export("(> (f x) (+ x 1))");
    assert!(wire_gap);
    assert!(
        text.contains(
            "(step t1.fi (cl (or (not (forall ((x Int)) (> (f x) (+ x 1)))) (> (f 2) (+ 2 1)))) \
             :rule forall_inst :args (2))"
        ),
        "{text}"
    );
    assert!(text.contains(":rule comp_simplify"), "{text}");
    assert!(
        !text.contains(":rule hole") && !text.contains(":rule trust"),
        "{text}"
    );
    if let Some(verdict) = pinned_carcara_verdict("reversed", &problem, &text) {
        assert_eq!(verdict, "valid", "{text}");
    }
}

/// NEGATIVE TWIN, the original intent: an instance surface no schema relates
/// to the canonical one (`(+ 1 x)` commuted as well as reversed) keeps the
/// wire gap and an honest `hole`, never a step carcara rejects.
#[test]
fn ground_pin_unrelated_instance_surface_retains_wire_gap() {
    let (problem, wire_gap, text) = changed_instance_surface_export("(> (f x) (+ 1 x))");
    assert!(wire_gap);
    assert!(text.contains(":rule hole"), "{text}");
    if let Some(verdict) = pinned_carcara_verdict("unrelated", &problem, &text) {
        assert_eq!(verdict, "holey", "{text}");
    }
}

#[test]
fn ground_pin_instance_refutation_rejects_consistent_pin() {
    let mut exec = pinned_instance_executor(4);
    assert!(!exec.try_translate_authored_consequence_replay_unsat());
    assert!(exec.last_proof.is_none());
}

#[test]
fn later_extra_record_gets_its_own_bounded_direct_scan() {
    let mut exec = pinned_instance_executor(3);
    let decisive = exec
        .ematching_proof_records
        .pop()
        .expect("fixture installed the decisive x=2 record");
    let base = provenance_for(&mut exec, 0);
    exec.ematching_proof_records
        .push(crate::executor::EmatchingProofRecord {
            assertion_index: 0,
            quantifier: base.quantifier,
            binding: base.binding,
            instance: base.instance,
        });
    assert!(!exec.try_translate_authored_consequence_replay_unsat());
    let (base_fingerprint, base_attempts) = exec
        .consequence_replay_direct_state
        .get()
        .expect("base scan records its bounded state");
    assert_eq!(base_attempts, 1);
    let decisive = crate::ematching::ForallInstantiationProvenance {
        quantifier: decisive.quantifier,
        binding: decisive.binding,
        instance: decisive.instance,
    };
    assert!(exec.try_translate_authored_consequence_replay_unsat_with(&[decisive]));
    let (extra_fingerprint, extra_attempts) = exec
        .consequence_replay_direct_state
        .get()
        .expect("extra scan updates its bounded state");
    assert_ne!(extra_fingerprint, base_fingerprint);
    assert_eq!(extra_attempts, 2);
}

#[test]
fn forged_first_record_does_not_hide_a_later_valid_instance() {
    let mut exec = pinned_instance_executor(3);
    let valid = exec
        .ematching_proof_records
        .pop()
        .expect("fixture installed a record");
    let pin = exec.ctx.assertions[1];
    let TermData::App(_, pin_args) = exec.ctx.terms.get(pin).clone() else {
        panic!("fixture pin is an equality");
    };
    let key = pin_args
        .into_iter()
        .find(|&term| !matches!(exec.ctx.terms.get(term), TermData::Const(_)))
        .expect("pin has a nonconstant key");
    let hundred = exec.ctx.terms.mk_int(100.into());
    let forged_instance = exec
        .ctx
        .terms
        .mk_app(Symbol::named(">"), [key, hundred], Sort::Bool);
    let zero = exec.ctx.terms.mk_int(0.into());
    let records = [
        crate::ematching::ForallInstantiationProvenance {
            quantifier: valid.quantifier,
            binding: vec![zero],
            instance: forged_instance,
        },
        crate::ematching::ForallInstantiationProvenance {
            quantifier: valid.quantifier,
            binding: valid.binding,
            instance: valid.instance,
        },
    ];
    assert!(exec.try_translate_authored_consequence_replay_unsat_with(&records));
}

#[test]
fn two_pins_close_one_ground_instance() {
    let mut exec = executor_with_instance(
        r#"
            (set-logic AUFLIA)
            (declare-fun f (Int) Int)
            (declare-fun g (Int) Int)
            (assert (forall ((x Int)) (> (+ (f x) (g x)) 10)))
            (assert (= (f 2) 4))
            (assert (= (g 2) 6))
        "#,
        2,
    );
    assert!(exec.try_translate_authored_consequence_replay_unsat());
}

#[test]
fn reversed_authored_pin_orientation_is_strictly_bridged() {
    let mut exec = executor_with_instance(
        r#"
            (set-logic AUFLIA)
            (declare-fun f (Int) Int)
            (assert (forall ((x Int)) (> (f x) (+ x 1))))
            (assert (= 3 (f 2)))
        "#,
        2,
    );
    assert!(exec.try_translate_authored_consequence_replay_unsat());
}

#[test]
fn conflicting_authored_pins_decline_the_direct_lane() {
    let mut exec = executor_with_instance(
        r#"
            (set-logic AUFLIA)
            (declare-fun f (Int) Int)
            (assert (forall ((x Int)) (> (f x) (+ x 1))))
            (assert (= (f 2) 3))
            (assert (= (f 2) 4))
        "#,
        2,
    );
    assert!(direct_candidate(&mut exec).is_none());
}

#[test]
fn negative_divisor_is_closed_by_checked_evaluation() {
    let mut exec = executor_with_instance(
        r#"
            (set-logic AUFLIA)
            (declare-fun f (Int) Int)
            (assert (forall ((x Int)) (> (f x) (div x (- 2)))))
            (assert (= (f (- 3)) 2))
        "#,
        -3,
    );
    assert!(direct_candidate(&mut exec).is_some());
}

#[test]
fn zero_divisor_declines_checked_evaluation() {
    let mut exec = executor_with_instance(
        r#"
            (set-logic AUFLIA)
            (declare-fun f (Int) Int)
            (assert (forall ((x Int)) (> (f x) (div x 0))))
            (assert (= (f 2) 0))
        "#,
        2,
    );
    assert!(direct_candidate(&mut exec).is_none());
}

#[test]
fn remaining_unpinned_application_declines() {
    let mut exec = executor_with_instance(
        r#"
            (set-logic AUFLIA)
            (declare-fun f (Int) Int)
            (declare-fun g (Int) Int)
            (assert (forall ((x Int)) (> (+ (f x) (g x)) 10)))
            (assert (= (f 2) 4))
        "#,
        2,
    );
    assert!(!exec.try_translate_authored_consequence_replay_unsat());
    assert!(exec.last_proof.is_none());
}

#[test]
fn direct_scan_depth_preflight_rejects_recursive_overflow_shape() {
    let mut exec = Executor::new();
    let mut root = exec.ctx.terms.true_term();
    for _ in 0..=MAX_INSTANCE_DEPTH {
        root = exec
            .ctx
            .terms
            .mk_app(Symbol::named("depth_guard"), [root], Sort::Bool);
    }
    let mut remaining = MAX_OCCURRENCE_WORK;
    assert!(!Executor::ground_instance_within_budget(
        &exec.ctx.terms,
        root,
        &mut remaining
    ));
}

#[test]
fn direct_scan_width_preflight_charges_queued_children() {
    let mut exec = Executor::new();
    let truth = exec.ctx.terms.true_term();
    let root = exec
        .ctx
        .terms
        .mk_app(Symbol::named("width_guard"), vec![truth; 65], Sort::Bool);
    let mut remaining = 64;
    assert!(!Executor::ground_instance_within_budget(
        &exec.ctx.terms,
        root,
        &mut remaining
    ));
}
