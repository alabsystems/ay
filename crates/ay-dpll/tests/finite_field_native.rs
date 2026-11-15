// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use ay_dpll::{
    api::{FiniteFieldSort, Logic, ModelValue, Solver, Sort},
    Executor,
};
use ay_frontend::parse;
fn run(input: &str) -> (Executor, Vec<String>) {
    let mut e = Executor::new();
    let commands = parse(input).expect("parse field input");
    let output = e.execute_all(&commands).expect("execute field input");
    (e, output)
}

#[test]
fn higher_degree_field_witnesses_preserve_all_authored_constraints() {
    for (prime, body) in [
        (65537u32, "(assert (= (ff.mul x x x) #f27m65537))"),
        (4294967291u32, "(assert (= (ff.mul x x x) #f27m4294967291))"),
        (65537u32, "(assert (= (ff.mul (ff.add x #f65534m65537) (ff.add x #f65532m65537) (ff.add x #f65530m65537)) #f0m65537))"),
        (65537u32, "(assert (= (ff.mul (ff.add x #f65534m65537) (ff.add x #f65532m65537) (ff.add x #f65530m65537)) #f0m65537))(assert (distinct x #f3m65537 #f5m65537))"),
        (65537u32, "(assert (= (ff.mul x x x x) #f16m65537))(assert (distinct x #f2m65537 #f65535m65537 #f512m65537))"),
        (65537u32, "(assert (= (ff.mul (ff.add x #f65534m65537) (ff.add x #f65534m65537) (ff.add x #f65534m65537)) #f0m65537))"),
    ] {
        let input = format!("(set-logic QF_FF)(declare-const x (_ FiniteField {prime})){body}(check-sat)");
        let (executor, output) = run(&input);
        assert_eq!(output, ["sat"], "{input}: {:?}", executor.unknown_reason());
    }
}

#[test]
fn higher_degree_field_refutations_require_independent_native_replay() {
    use ay_core::{ProofStep, TheoryLemmaKind};
    for (prime, value) in [(65537u32, 3u32), (4294967291u32, 3u32)] {
        let input = format!(
            "(set-logic QF_FF)(set-option :produce-proofs true)(declare-const x (_ FiniteField {prime}))(assert (= (ff.mul x x x) #f27m{prime}))(assert (distinct x #f{value}m{prime}))(check-sat)"
        );
        let (executor, output) = run(&input);
        assert_eq!(output, ["unsat"], "{:?}", executor.unknown_reason());
        let proof = executor.last_proof().expect("native field refutation");
        let quality = ay_proof::check_proof_strict(proof, executor.terms()).unwrap();
        assert!(quality.is_complete());
        assert_eq!(quality.trust_count, 0);
        let mut forged = proof.clone();
        let (index, step) = forged
            .steps
            .iter_mut()
            .enumerate()
            .find(|(_, step)| {
                matches!(
                    step,
                    ProofStep::TheoryLemma {
                        kind: TheoryLemmaKind::FiniteFieldUnivariate,
                        ..
                    }
                )
            })
            .expect("dedicated univariate theorem");
        let ProofStep::TheoryLemma { clause, .. } = step else {
            unreachable!()
        };
        // Drop the authored exclusion: the retained cubic alone has root 3,
        // so this is no refutation even if every later resolution is retained.
        clause.truncate(1);
        assert!(matches!(
            ay_proof::check_proof_strict(&forged, executor.terms()),
            Err(ay_proof::ProofCheckError::InvalidTheoryLemma { step, .. })
                if step == ay_core::ProofId(index as u32)
        ));
    }
}

#[test]
fn higher_degree_field_incremental_roots_match_reference_fixture() {
    let (executor, output) = run(include_str!(
        "fixtures/finite_field/univariate_large_prime.smt2"
    ));
    assert_eq!(
        output,
        ["sat", "unsat", "sat", "unsat", "sat", "sat", "unsat", "unsat"],
        "{:?}",
        executor.unknown_reason()
    );
}

fn long_linear_chain(delta: u32) -> String {
    let mut input = String::from("(set-logic QF_FF)(set-option :produce-proofs true)");
    for i in 0..10 {
        input.push_str(&format!("(declare-const q{i} (_ FiniteField 7))"));
    }
    for i in 0..9 {
        input.push_str(&format!("(assert (= q{i} q{}))", i + 1));
    }
    input.push_str(&format!(
        "(assert (= q0 (ff.add q9 #f{delta}m7)))(check-sat)"
    ));
    input
}

#[test]
fn variable_field_certificate_crosses_eight_rows_and_rejects_forged_data() {
    use ay_core::ProofStep;
    let (executor, output) = run(&long_linear_chain(1));
    assert_eq!(output, ["unsat"], "{:?}", executor.unknown_reason());
    let proof = executor.last_proof().unwrap();
    let quality = ay_proof::check_proof_strict(proof, executor.terms()).unwrap();
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
    let index = proof
        .steps
        .iter()
        .position(|step| matches!(step, ProofStep::FiniteFieldLinear { .. }))
        .unwrap();
    let ProofStep::FiniteFieldLinear {
        clause,
        multipliers,
    } = &proof.steps[index]
    else {
        unreachable!()
    };
    assert_eq!(clause.len(), 10);
    assert_eq!(multipliers.len(), 10);
    assert!(
        multipliers.iter().all(|&value| value != 0),
        "every chain row is necessary"
    );
    let end = || ay_core::time::Instant::now() + std::time::Duration::from_secs(30);
    let snapshot = ay_proof::SerializableProofBundle::from_proof(
        proof,
        executor.terms(),
        proof
            .steps
            .iter()
            .filter_map(|step| {
                if let ProofStep::Assume(root) = step {
                    Some(*root)
                } else {
                    None
                }
            })
            .collect(),
    );
    let owner = ay_proof::capture_strict_retained_bundle_with_resource_control(
        snapshot,
        end(),
        &mut |_, _| true,
    )
    .unwrap()
    .finish_exact_with_resource_control(&mut |_, _| true)
    .unwrap()
    .0;
    let limits = ay_proof::RetainedProofTransportLimits {
        max_json_bytes: 1024 * 1024,
        max_storage_bytes: 1024 * 1024,
        max_work: 4_000_000,
    };
    let bytes = owner
        .encode_with_resource_control(limits, end(), &mut |_, _| true)
        .unwrap();
    let replay = ay_proof::re_check_retained_bundle_strict_with_resource_control(
        &bytes,
        limits,
        end(),
        &mut |_, _| true,
    )
    .unwrap();
    assert!(replay.quality.is_complete());
    for mode in 0..4 {
        let mut forged = proof.clone();
        let ProofStep::FiniteFieldLinear {
            clause,
            multipliers,
        } = &mut forged.steps[index]
        else {
            unreachable!()
        };
        match mode {
            0 => multipliers.fill(0),
            1 => {
                multipliers.pop();
            }
            2 => multipliers[0] = 7,
            _ => clause.swap(0, 9),
        }
        assert!(
            ay_proof::check_proof_strict(&forged, executor.terms()).is_err(),
            "forgery {mode}"
        );
    }
    let mut mixed_terms = executor.terms().clone();
    let field = ay_core::FiniteFieldSort::new(11).unwrap();
    let other = mixed_terms.mk_var("other-field", ay_core::Sort::FiniteField(field));
    let zero = mixed_terms.mk_finite_field(0, field);
    let row = mixed_terms.mk_eq(other, zero);
    let negative = mixed_terms.mk_not(row);
    let mut mixed = proof.clone();
    let ProofStep::FiniteFieldLinear { clause, .. } = &mut mixed.steps[index] else {
        unreachable!()
    };
    clause[0] = negative;
    assert!(ay_proof::check_proof_strict(&mixed, &mixed_terms).is_err());
    // Native replay does not invent an external finite-field inference.
    if let Ok(wire) = ay_proof::try_export_alethe(proof, executor.terms()) {
        assert!(wire.contains(&format!(":rule {}", ay_core::UNPROVED_STEP_RULE)));
    }
    let (compatible, output) = run(&long_linear_chain(0));
    assert_eq!(output, ["sat"], "{:?}", compatible.unknown_reason());
}

#[test]
fn full_width_field_linear_models_and_ground_arithmetic_are_exact() {
    for p in [257u32, 65_521, 2_147_483_647, 4_294_967_291] {
        let minus_one = p - 1;
        let script = format!(
            "(set-logic QF_FF)(declare-const x (_ FiniteField {p}))
             (assert (= (ff.mul #f{minus_one}m{p} x) #f1m{p}))
             (assert (= (ff.mul #f{minus_one}m{p} #f{minus_one}m{p}) #f1m{p}))
             (assert (= (ff.add #f{minus_one}m{p} #f{minus_one}m{p}) #f{}m{p}))
             (assert (= (ff.bitsum #f{minus_one}m{p} #f{minus_one}m{p}) #f{}m{p}))
             (check-sat)(get-value (x))",
            p - 2,
            p - 3,
        );
        let (executor, output) = run(&script);
        assert_eq!(output[0], "sat", "p={p}: {:?}", executor.unknown_reason());
        assert!(output[1].contains(&format!("ff{minus_one}")), "{output:?}");
    }
}

#[test]
fn full_width_quadratic_witnesses_and_native_refutations_are_independently_checked() {
    use ay_core::{ProofStep, TheoryLemmaKind};
    for (p, nonsquare) in [(65537u32, 3), (4294967291, 2)] {
        let field = FiniteFieldSort::new(p).unwrap();
        let mut solver = Solver::new(Logic::QfFf);
        let x = solver.declare_const("x", Sort::FiniteField(field));
        let square = solver.try_finite_field_app("ff.mul", &[x, x]).unwrap();
        let four = solver.finite_field_const(&4.into(), field);
        let root = solver.eq(square, four);
        solver.assert_term(root);
        assert!(solver.check_sat().is_sat(), "p={p}");
        let Some(ModelValue::FiniteField {
            value,
            field: actual,
        }) = solver.value(x)
        else {
            panic!("field witness must retain its typed value");
        };
        assert_eq!(actual, field);
        assert_eq!(u64::from(value) * u64::from(value) % u64::from(p), 4);

        let (executor, output) = run(&format!(
            "(set-logic QF_FF)(set-option :produce-proofs true)
             (declare-const x (_ FiniteField {p}))
             (assert (= (ff.mul x x) #f{nonsquare}m{p}))(check-sat)"
        ));
        assert_eq!(output, ["unsat"], "p={p}: {:?}", executor.unknown_reason());
        let proof = executor.last_proof().unwrap();
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::FiniteFieldQuadratic,
                ..
            }
        )));
        let quality = ay_proof::check_proof_strict(proof, executor.terms()).unwrap();
        assert!(quality.is_complete());
        assert_eq!(quality.trust_count, 0);
        let roots = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Assume(root) => Some(*root),
                _ => None,
            })
            .collect();
        let bundle = ay_proof::SerializableProofBundle::from_proof(proof, executor.terms(), roots);
        let bytes = serde_json::to_vec(&bundle).unwrap();
        let decoded = serde_json::from_slice(&bytes).unwrap();
        let checked = ay_proof::re_check_bundle_strict(&decoded).unwrap();
        assert!(checked.quality.is_complete());
        assert_eq!(checked.quality.trust_count, 0);
    }
}

#[test]
fn quadratic_constraints_intersect_roots_and_preserve_zero_polynomial_semantics() {
    let setup = "(set-logic QF_FF)(set-option :produce-proofs true)
        (declare-const x (_ FiniteField 65537))";
    let cases = [
        ("(assert (= (ff.mul x x) #f4m65537))(assert (= x #f2m65537))", "sat"),
        ("(assert (= (ff.mul x x) #f4m65537))(assert (= x #f3m65537))", "unsat"),
        ("(assert (= (ff.mul x x) #f4m65537))(assert (distinct x #f2m65537))", "sat"),
        ("(assert (= (ff.mul x x) #f4m65537))(assert (distinct x #f2m65537 #f65535m65537))", "unsat"),
        ("(assert (= (ff.mul (ff.add x #f65535m65537) (ff.add x #f65535m65537)) #f0m65537))", "sat"),
        ("(assert (= (ff.mul (ff.add x #f65535m65537) (ff.add x #f65535m65537)) #f0m65537))(assert (distinct x #f2m65537))", "unsat"),
        ("(assert (= (ff.add x (ff.neg x)) #f0m65537))(assert (= (ff.mul x x) #f4m65537))", "sat"),
        ("(assert (= (ff.mul x x) #f4m65537))(assert (distinct #f0m65537 #f1m65537))", "sat"),
        ("(assert (distinct (ff.mul x x) #f4m65537 #f3m65537))", "sat"),
        ("(assert (= (ff.add (ff.mul #f3m65537 x x) (ff.mul #f5m65537 x) #f2m65537) #f0m65537))", "sat"),
    ];
    for (body, expected) in cases {
        let (executor, output) = run(&format!("{setup}{body}(check-sat)"));
        assert_eq!(
            output,
            [expected],
            "{body}: {:?}",
            executor.unknown_reason()
        );
        if expected == "unsat" {
            assert!(
                ay_proof::check_proof_strict(executor.last_proof().unwrap(), executor.terms())
                    .unwrap()
                    .is_complete()
            );
        }
    }
}

#[test]
fn large_field_capabilities_and_refusals_retain_original_limits() {
    for (body, expected) in [
        ("(assert (= (ff.mul x x x) #f1m65537))", "sat"),
        ("(assert (or (= (ff.mul x x) #f4m65537) (= (ff.mul x x) #f3m65537)))", "sat"),
        ("(declare-const y (_ FiniteField 65537))(assert (= (ff.mul x y) #f4m65537))", "sat"),
        ("(declare-const y (_ FiniteField 4294967291))(assert (= (ff.mul x x) #f4m65537))(assert (= (ff.mul y y) #f4m4294967291))", "unknown"),
    ] {
        let (executor, output) = run(&format!("(set-logic QF_FF)(declare-const x (_ FiniteField 65537)){body}(check-sat)"));
        assert_eq!(output, [expected], "{body}: {:?}", executor.unknown_reason());
    }
    let setup = "(set-logic QF_FF)(declare-const x (_ FiniteField 65537))
        (assert (= (ff.mul x x) #f4m65537))";
    let mut executor = Executor::new();
    executor.execute_all(&parse(setup).unwrap()).unwrap();
    executor.set_term_memory_limit(Some(executor.terms().true_memory_bytes() + 128));
    assert_eq!(
        executor
            .execute_all(&parse("(check-sat)").unwrap())
            .unwrap(),
        ["unknown"]
    );
    executor.set_term_memory_limit(None);
    assert_eq!(
        executor
            .execute_all(&parse("(check-sat)").unwrap())
            .unwrap(),
        ["sat"]
    );
    let field = FiniteFieldSort::new(65537).unwrap();
    let mut solver = Solver::new(Logic::QfFf);
    let x = solver.declare_const("x", Sort::FiniteField(field));
    let square = solver.try_finite_field_app("ff.mul", &[x, x]).unwrap();
    let four = solver.finite_field_const(&4.into(), field);
    let root = solver.eq(square, four);
    solver.assert_term(root);
    assert!(solver.check_sat_interruptible(|| true).is_unknown());
    assert!(solver.check_sat().is_sat());
}

#[test]
fn full_width_field_linear_proof_replays_and_rejects_a_forged_multiplier() {
    use ay_core::{ProofStep, TheoryLemmaKind};

    let (executor, output) = run("(set-logic QF_FF)(set-option :produce-proofs true)
         (declare-const x (_ FiniteField 4294967291))
         (assert (= x #f1m4294967291))
         (assert (= (ff.mul #f2m4294967291 x) #f3m4294967291))
         (check-sat)");
    assert_eq!(output, ["unsat"], "{:?}", executor.unknown_reason());
    let proof = executor.last_proof().expect("strict native field proof");
    let quality = ay_proof::check_proof_strict(proof, executor.terms()).unwrap();
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
    let mut forged = proof.clone();
    let multipliers = forged
        .steps
        .iter_mut()
        .find_map(|step| match step {
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::FiniteFieldLinearWide(multipliers),
                ..
            } => Some(multipliers),
            _ => None,
        })
        .expect("contradiction needs a multiplier larger than one byte");
    multipliers.fill(0);
    assert!(ay_proof::check_proof_strict(&forged, executor.terms()).is_err());
}
#[test]
fn field_arithmetic_is_positional_exact_and_incremental() {
    let (_, out) = run(include_str!("fixtures/finite_field/arithmetic.smt2"));
    assert_eq!(out[0], "sat", "{out:?}");
    assert!(out[1].contains("(as ff5 (_ FiniteField 7))"), "{out:?}");
    assert!(out[1].contains("(as ff1 (_ FiniteField 7))"), "{out:?}");
    assert_eq!(&out[2..], ["unsat", "sat"]);
}
#[test]
fn exhaustive_nonroot_theorem_has_no_assumed_false_premise() {
    let script = format!(
        "(set-option :produce-proofs true)\n{}",
        include_str!("fixtures/finite_field/nonroot.smt2")
    );
    let (e, out) = run(&script);
    assert_eq!(out, ["unsat"], "{:?}", e.unknown_reason());
    let proof = e.last_proof().expect("native proof");
    let quality = ay_proof::check_proof_strict(proof, e.terms()).expect("independent replay");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
}
#[test]
fn typed_api_returns_field_values_and_checked_native_bundle() {
    let f = FiniteFieldSort::new(7).unwrap();
    let mut s = Solver::new(Logic::QfFf);
    s.set_produce_proofs(true);
    let x = s.declare_const("x", Sort::FiniteField(f));
    let three = s.finite_field_const(&3.into(), f);
    let one = s.finite_field_const(&1.into(), f);
    let sum = s.try_finite_field_app("ff.add", &[x, three]).unwrap();
    assert!(s.independent_closed_finite_field(sum).is_none());
    let ground = s.try_finite_field_app("ff.add", &[three, one]).unwrap();
    let folded = s.independent_closed_finite_field(ground).unwrap();
    assert_eq!(s.numeral_string(folded).as_deref(), Some("4"));
    {
        let mut admission = Solver::new(Logic::QfFf);
        let literal = admission.finite_field_const(&1.into(), f);
        let oversized = admission
            .try_finite_field_app("ff.add", &vec![literal; 1025])
            .unwrap();
        assert!(admission
            .independent_closed_finite_field(oversized)
            .is_none());
    }
    let eq = s.eq(sum, one);
    s.assert_term(eq);
    assert!(s.check_sat().is_sat());
    assert!(s.independent_closed_finite_field(sum).is_none());
    assert_eq!(
        s.value(x),
        Some(ModelValue::FiniteField { value: 5, field: f })
    );
    assert_eq!(
        s.model().unwrap().model().value_by_name("x"),
        Some(ModelValue::FiniteField { value: 5, field: f })
    );
    let square = s.try_finite_field_app("ff.mul", &[x, x]).unwrap();
    let impossible = s.eq(square, three);
    s.assert_term(impossible);
    assert!(s.check_sat().is_unsat());
    let bundle = s
        .export_last_unsat_bundle()
        .expect("export strict native proof");
    let bytes = serde_json::to_vec(&bundle).unwrap();
    let copied = serde_json::from_slice(&bytes).unwrap();
    let checked =
        ay_proof::re_check_bundle_strict(&copied).expect("offline independent field replay");
    assert!(checked.quality.is_complete());
    assert_eq!(checked.quality.trust_count, 0);
}
#[test]
fn unsupported_combinations_and_domains_fail_closed() {
    // A regular parametric family is now supported; unrelated mixed theories
    // and malformed field domains below still refuse.
    let (_, output) = run("(set-logic ALL)(declare-const x (_ FiniteField 251))(declare-const y (_ FiniteField 251))(declare-const z (_ FiniteField 251))(assert (= (ff.mul x y) z))(check-sat)");
    assert_eq!(output, ["sat"]);
    for input in [
        "(set-logic ALL)(declare-fun f ((_ FiniteField 7)) Bool)(declare-const x (_ FiniteField 7))(assert (f x))(check-sat)",
        "(set-logic ALL)(declare-const x (_ FiniteField 7))(declare-const i Int)(assert (= x #f1m7))(assert (> i 0))(check-sat)",
    ]{let (_,out)=run(input);assert_eq!(out,["unknown"],"{input}");}
    for input in [
        "(declare-const x (_ FiniteField 9))",
        "(declare-const x (_ FiniteField 4294967295))",
        "(set-logic QF_FF)(declare-const m2 (_ FiniteField 7))(assert (= #f1m7m2 #f1m7))",
        "(set-logic QF_FF)(declare-const x (_ FiniteField 7))(assert (= #f1m7x #f1m7))",
        "(set-logic QF_FF)(declare-const + (_ FiniteField 7))(assert (= #f1m7+ #f1m7))",
        "(assert (= (ff.add #f1m7 #f1m5) #f2m7))",
        "(assert (= (ff.neg #f1m7 #f2m7) #f2m7))",
        "(assert (= (ff.bitsum true false) #f1m7))",
    ] {
        let mut e = Executor::new();
        assert!(
            parse(input).is_err() || e.execute_all(&parse(input).unwrap()).is_err(),
            "{input}"
        );
    }
}

#[test]
fn boolean_assumptions_are_source_bound_and_reusable() {
    let (_, out) = run(r#"
        (set-logic QF_FF)
        (declare-const b Bool)
        (declare-const x (_ FiniteField 7))
        (assert (=> b (= (ff.mul x x) #f3m7)))
        (check-sat-assuming (b))
        (check-sat-assuming ((not b)))
        (check-sat)
    "#);
    assert_eq!(out, ["unsat", "sat", "sat"]);
}
#[test]
fn prime_boundaries_and_ascribed_negative_literals_are_exact() {
    let (_, empty) =
        run("(set-logic QF_FF)(declare-const free (_ FiniteField 7))(check-sat)(get-value (free))");
    assert_eq!(empty[0], "sat");
    assert!(empty[1].contains("(as ff0 (_ FiniteField 7))"), "{empty:?}");

    let (_, out) = run(include_str!("fixtures/finite_field/boundaries.smt2"));
    assert_eq!(out[0], "sat");
    assert!(out[1].contains("(as ff1 (_ FiniteField 251))"), "{out:?}");
    let (_, root) = run(include_str!("fixtures/finite_field/root.smt2"));
    assert_eq!(root, ["sat"]);
}

#[test]
fn unsupported_strict_wire_presentation_is_not_claimed() {
    let (_, out) = run(r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 7))
        (assert (= (ff.mul x x) #f3m7))
        (check-sat)
    "#);
    assert_eq!(out, ["unknown"]);
}

#[test]
fn field_queries_honor_interrupts_without_poisoning_retry() {
    let f = FiniteFieldSort::new(251).unwrap();
    let mut solver = Solver::new(Logic::QfFf);
    let x = solver.declare_const("x", Sort::FiniteField(f));
    let last = solver.finite_field_const(&250.into(), f);
    let equality = solver.eq(x, last);
    solver.assert_term(equality);
    assert!(solver.check_sat_interruptible(|| true).is_unknown());
    assert!(solver.check_sat().is_sat());
    assert_eq!(
        solver.value(x),
        Some(ModelValue::FiniteField {
            value: 250,
            field: f
        })
    );
}

#[test]
fn field_numerals_respect_lexical_binding_and_export_hygiene() {
    let (_, out) = run(include_str!("fixtures/finite_field/shadowing.smt2"));
    assert_eq!(out, ["sat"]);
    let f = FiniteFieldSort::new(7).unwrap();
    let mut solver = Solver::new(Logic::QfFf);
    let named = solver.declare_const("ff1", Sort::FiniteField(f));
    let other = solver.declare_const("#f1m7", Sort::FiniteField(f));
    let one = solver.finite_field_const(&1.into(), f);
    let two = solver.finite_field_const(&2.into(), f);
    let first = solver.eq(named, one);
    solver.assert_term(first);
    let second = solver.eq(named, two);
    solver.assert_term(second);
    let pin = solver.eq(other, two);
    solver.assert_term(pin);
    assert!(solver.check_sat().is_unsat());
    let script = solver.to_smtlib2();
    let (_, out) = run(&script);
    assert_eq!(out, ["unsat"], "{script}");
}

#[test]
fn field_value_model_and_default_outputs_preserve_shadowed_residues() {
    let field = FiniteFieldSort::new(7).unwrap();
    let mut solver = Solver::new(Logic::QfFf);
    let two = solver.finite_field_const(&2.into(), field);
    for name in ["ff0", "ff1", "#f0m7", "#f1m7"] {
        let variable = solver.declare_const(name, Sort::FiniteField(field));
        let pin = solver.eq(variable, two);
        solver.assert_term(pin);
    }
    let free = solver.declare_const("free", Sort::FiniteField(field));
    assert!(solver.check_sat().is_sat());
    for n in [0, 1] {
        let literal = solver.finite_field_const(&n.into(), field);
        assert_eq!(
            solver.value(literal),
            Some(ModelValue::FiniteField { value: n, field })
        );
        let printed = solver.format_finite_field_literal(n, field).unwrap();
        let setup="(set-logic QF_FF)(declare-const ff0 (_ FiniteField 7))(declare-const ff1 (_ FiniteField 7))(declare-const |#f0m7| (_ FiniteField 7))(declare-const |#f1m7| (_ FiniteField 7))(assert (= ff0 #f2m7))(assert (= ff1 #f2m7))(assert (= |#f0m7| #f2m7))(assert (= |#f1m7| #f2m7))";
        let (_, roundtrip) = run(&format!(
            "{setup}(assert (not (= {printed} #f{}m7)))(check-sat)",
            n + 28
        ));
        assert_eq!(roundtrip, ["unsat"]);
        let decoded = ModelValue::decode_typed_literals(&[(&printed, &Sort::FiniteField(field))]);
        assert_eq!(
            decoded.unwrap(),
            vec![ModelValue::FiniteField { value: n, field }]
        );
    }
    assert_eq!(
        solver.value(free),
        Some(ModelValue::FiniteField { value: 0, field })
    );
    let model = solver.model().unwrap();
    assert_eq!(
        model.model().value_by_name("ff0"),
        Some(ModelValue::FiniteField { value: 2, field })
    );
    assert_eq!(
        model.model().value_by_name("free"),
        Some(ModelValue::FiniteField { value: 0, field })
    );
}

#[test]
fn field_rendering_exhaustion_is_an_error_and_a_fresh_solve_can_retry() {
    use std::fmt::Write;
    for n in [0, 1] {
        let mut input = format!("(set-logic QF_FF)(declare-const ff{n} (_ FiniteField 7))");
        for k in 0..1024 {
            write!(
                input,
                "(declare-const |#f{}m7| (_ FiniteField 7))",
                n + 7 * k
            )
            .unwrap();
        }
        write!(input, "(declare-const witness (_ FiniteField 7))(assert (= witness #f{}m7))(check-sat)(get-value (#f{}m7))(check-sat)(get-model)", n + 7168, n + 7168).unwrap();
        let (_, output) = run(&input);
        assert_eq!(output.len(), 4, "{output:?}");
        assert_eq!(output[0], "sat");
        assert!(output[1].starts_with("(error "), "{output:?}");
        assert_eq!(output[2], "sat");
        assert!(output[3].starts_with("(error "), "{output:?}");
    }
}

#[test]
fn gaussian_affine_witnesses_cross_the_enumeration_bound_and_seal_original_models() {
    let field = FiniteFieldSort::new(251).unwrap();
    let mut solver = Solver::new(Logic::QfFf);
    let variables: Vec<_> = (0..12)
        .map(|i| solver.declare_const(&format!("x{i}"), Sort::FiniteField(field)))
        .collect();
    let three = solver.finite_field_const(&3.into(), field);
    let expected: Vec<u32> = (0..12).map(|i| (17 * i + 9) % 251).collect();
    // Root-stack traversal visits the later rows first, requiring pivot-row
    // exchange. The final equation requires a modular inverse, not division.
    for i in 0..12 {
        let lhs = if i == 11 {
            solver
                .try_finite_field_app("ff.mul", &[three, variables[i]])
                .unwrap()
        } else {
            let scaled = solver
                .try_finite_field_app("ff.mul", &[three, variables[i + 1]])
                .unwrap();
            solver
                .try_finite_field_app("ff.add", &[variables[i], scaled])
                .unwrap()
        };
        let residue = if i == 11 {
            3 * expected[i] % 251
        } else {
            (expected[i] + 3 * expected[i + 1]) % 251
        };
        let rhs = solver.finite_field_const(&residue.into(), field);
        let row = solver.eq(lhs, rhs);
        solver.assert_term(row);
    }
    assert!(solver.check_sat_interruptible(|| true).is_unknown());
    let result = solver.check_sat();
    assert!(result.is_sat(), "{result:?}");
    assert!(result.was_model_validated());
    assert!(solver.model_for_consumer().is_some());
    for (&term, value) in variables.iter().zip(expected) {
        assert_eq!(
            solver.value(term),
            Some(ModelValue::FiniteField { value, field })
        );
    }
}

#[test]
fn underdetermined_linear_models_and_refutations_retain_original_admission() {
    let setup = "(set-logic QF_FF)(declare-const x (_ FiniteField 251))(declare-const y (_ FiniteField 251))(declare-const z (_ FiniteField 251))(assert (= (ff.add x y) z))";
    let (_, out) = run(&format!("{setup}(check-sat)"));
    assert_eq!(out, ["sat"]);
    let (_, out) = run(&format!(
        "{setup}(assert (= x #f1m251))(assert (= x #f2m251))(check-sat)"
    ));
    assert_eq!(
        out,
        ["unsat"],
        "large affine conflicts require independent proof authority"
    );
    let mut executor = Executor::new();
    executor.execute_all(&parse(setup).unwrap()).unwrap();
    let source = executor.terms().true_memory_bytes();
    executor.set_term_memory_limit(Some(source + 128));
    let out = executor
        .execute_all(&parse("(check-sat)").unwrap())
        .unwrap();
    assert_eq!(
        out,
        ["unknown"],
        "new coefficient storage uses the existing attempt budget"
    );
    executor.set_term_memory_limit(None);
    let out = executor
        .execute_all(&parse("(check-sat)").unwrap())
        .unwrap();
    assert_eq!(out, ["sat"]);
}

#[test]
fn gaussian_field_refutation_checks_source_multipliers_after_pivot_swaps() {
    use ay_core::{ProofStep, TheoryLemmaKind};

    let setup = "(set-logic QF_FF)(set-option :produce-proofs true)
        (declare-const a (_ FiniteField 7))(declare-const b (_ FiniteField 7))
        (declare-const c (_ FiniteField 7))(declare-const d (_ FiniteField 7))
        (declare-const e (_ FiniteField 7))(declare-const f (_ FiniteField 7))
        (assert (= (ff.add a b c d e f) #f1m7))
        (assert (= f #f0m7))
        (assert (= (ff.add d e) #f0m7))";
    let (executor, out) = run(&format!(
        "{setup}(assert (= (ff.mul #f2m7 (ff.add a b c d e f)) #f3m7))(check-sat)"
    ));
    assert_eq!(out, ["unsat"], "{:?}", executor.unknown_reason());
    let proof = executor.last_proof().expect("strict native proof");
    let quality = ay_proof::check_proof_strict(proof, executor.terms()).unwrap();
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);

    let mut forged = proof.clone();
    let Some(ProofStep::TheoryLemma {
        kind: TheoryLemmaKind::FiniteFieldLinear(multipliers),
        ..
    }) = forged.steps.iter_mut().find(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::FiniteFieldLinear(_),
                ..
            }
        )
    })
    else {
        panic!("Gaussian proof must carry a linear witness");
    };
    multipliers[0] = (multipliers[0] + 1) % 7;
    assert!(ay_proof::check_proof_strict(&forged, executor.terms()).is_err());
    let authored: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| {
            if let ProofStep::Assume(root) = step {
                Some(*root)
            } else {
                None
            }
        })
        .collect();
    assert!(ay_proof::check_proof_strict_with_context_and_progress(
        proof,
        executor.terms(),
        None,
        None,
        Some(&authored[..authored.len() - 1]),
        &mut |_, _| true,
    )
    .is_err());

    let mut foreign_terms = executor.terms().clone();
    let field = FiniteFieldSort::new(11).unwrap();
    let a = foreign_terms.mk_var("foreign_a", Sort::FiniteField(field));
    let b = foreign_terms.mk_var("foreign_b", Sort::FiniteField(field));
    let foreign = foreign_terms.mk_app(ay_core::Symbol::named("="), &[a, b], Sort::Bool);
    let mut mixed = proof.clone();
    let ProofStep::TheoryLemma {
        clause,
        kind: TheoryLemmaKind::FiniteFieldLinear(coefficients),
        ..
    } = &mut mixed.steps[0]
    else {
        panic!("expected the linear theorem first");
    };
    clause[1] = foreign_terms.mk_not_raw(foreign);
    coefficients[1] = 0;
    assert!(matches!(
        ay_proof::check_proof_strict(&mixed, &foreign_terms),
        Err(ay_proof::ProofCheckError::InvalidTheoryLemma {
            step: ay_core::ProofId(0),
            ..
        })
    ));
    let (_, out) = run(&format!(
        "{setup}(assert (= (ff.mul #f2m7 (ff.add a b c d e f)) #f2m7))(check-sat)"
    ));
    assert_eq!(out, ["sat"]);
}

#[test]
fn sparse_field_ideal_refutations_reconstruct_authored_multiplication_consequences() {
    let input = include_str!("fixtures/finite_field/multivariate_ideal.smt2");
    for (index, source) in input.split("(reset)").enumerate() {
        let (executor, output) = run(source);
        if index == 3 {
            // A lexicographic elimination basis now constructs an actual
            // F_p model for this original control; independent authored-model
            // validation still owns the SAT result.
            assert_eq!(output, ["sat"], "{:?}", executor.unknown_reason());
            continue;
        }
        assert_eq!(
            output,
            ["unsat"],
            "case{index}: {:?}",
            executor.unknown_reason()
        );
        // The ordinary verdict above remains required. Request the public
        // proof surface BEFORE a separate solve; last_proof deliberately
        // withholds artifacts when the caller did not request retention.
        let proof_input = source.replacen(
            "(set-logic QF_FF)",
            "(set-logic QF_FF)(set-option :produce-proofs true)",
            1,
        );
        let (executor, proof_output) = run(&proof_input);
        assert_eq!(proof_output, output);
        let proof = executor.last_proof().expect("owning authored refutation");
        let quality = ay_proof::check_proof_strict(proof, executor.terms()).unwrap();
        assert!(quality.is_complete());
        assert_eq!(quality.trust_count, 0);
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ay_core::ProofStep::TheoryLemma {
                kind: ay_core::TheoryLemmaKind::FiniteFieldIdeal,
                ..
            }
        )));
        if index == 0 {
            let mut forged = proof.clone();
            let lemma = forged
                .steps
                .iter_mut()
                .find_map(|step| match step {
                    ay_core::ProofStep::TheoryLemma {
                        kind: ay_core::TheoryLemmaKind::FiniteFieldIdeal,
                        clause,
                        ..
                    } => Some(clause),
                    _ => None,
                })
                .unwrap();
            let _ = lemma.remove(0); // xy=1 alone has x=y=1; no producer basis can prove it false.
            let mut remaining = 100_000usize;
            assert!(ay_proof::check_proof_strict_with_context_and_progress(
                &forged,
                executor.terms(),
                None,
                None,
                None,
                &mut |work, _| {
                    let Some(left) = remaining.checked_sub(work) else {
                        return false;
                    };
                    remaining = left;
                    true
                }
            )
            .is_err());
        }
    }
}

#[test]
fn boolean_univariate_sets_keep_authored_models_and_independent_refutations() {
    for (body, expected) in [
        (
            "(or (= (ff.mul x x) #f4m65537) (= (ff.mul x x) #f3m65537))",
            "sat",
        ),
        (
            "(and (or (= x #f2m65537) (= x #f3m65537)) (distinct x #f2m65537 #f3m65537))",
            "unsat",
        ),
        (
            "(not (or (distinct x #f2m65537) (distinct x #f3m65537)))",
            "unsat",
        ),
        ("(and (=> (= x #f2m65537) false) (= x #f2m65537))", "unsat"),
        ("(xor (= x #f2m65537) (= x #f3m65537))", "sat"),
        ("(= (= x #f2m65537) (distinct x #f3m65537))", "sat"),
        (
            "(and (= (= x #f2m65537) (= x #f3m65537)) (= x #f2m65537))",
            "unsat",
        ),
        (
            "(distinct (= x #f2m65537) (= x #f3m65537) (= x #f4m65537))",
            "unsat",
        ),
        ("(distinct (= x #f2m65537) (= x #f3m65537))", "sat"),
        ("(ite (= x #f2m65537) false (= x #f3m65537))", "sat"),
        (
            "(not (and (distinct x #f2m65537) (distinct x #f3m65537)))",
            "sat",
        ),
    ] {
        let input=format!("(set-logic QF_FF)(set-option :produce-proofs true)(declare-const x (_ FiniteField 65537))(assert {body})(check-sat)");
        let (executor, output) = run(&input);
        assert_eq!(
            output,
            [expected],
            "{input}: {:?}",
            executor.unknown_reason()
        );
        if expected == "unsat" {
            let proof = executor.last_proof().expect("independent native theorem");
            let quality = ay_proof::check_proof_strict(proof, executor.terms()).unwrap();
            assert!(quality.is_complete());
            assert_eq!(quality.trust_count, 0);
        }
    }
}

#[test]
fn triangular_multivariate_field_models_use_authored_validation_and_keep_refusals() {
    let input = include_str!("fixtures/finite_field/multivariate_models.smt2");
    for (index, source) in input.split("(reset)").enumerate() {
        let (executor, output) = run(source);
        assert_eq!(
            output,
            [if index < 7 { "sat" } else { "unsat" }],
            "model case{index}: {:?}",
            executor.unknown_reason()
        );
    }
}

#[test]
fn finite_domain_refutations_replay_original_mixed_and_large_prime_inputs() {
    let input = include_str!("fixtures/finite_field/finite_domain.smt2");
    for (index, source) in input.split("(reset)").enumerate() {
        let (executor, output) = run(&format!("(set-option :produce-proofs true){source}"));
        let expected = if index == 1 { "sat" } else { "unsat" };
        assert_eq!(
            output,
            [expected],
            "{index}: {:?}",
            executor.unknown_reason()
        );
        if expected == "unsat" {
            let proof = executor
                .last_proof()
                .expect("retained finite-domain refutation");
            let quality = ay_proof::check_proof_strict(proof, executor.terms()).unwrap();
            assert!(quality.is_complete());
            assert_eq!(quality.trust_count, 0);
        }
    }
}

#[test]
fn parametric_field_models_prove_regular_families_before_domain_choice() {
    let input = include_str!("fixtures/finite_field/parametric_models.smt2");
    for (index, source) in input.split("(reset)").enumerate() {
        let (executor, output) = run(source);
        assert_eq!(
            output,
            ["sat"],
            "parametric case{index}: {:?}",
            executor.unknown_reason()
        );
    }
}

#[test]
fn conic_field_models_use_original_authored_validation() {
    let input = include_str!("fixtures/finite_field/conic_models.smt2");
    for (index, body) in input.split("(reset)").enumerate() {
        let (executor, output) = run(body);
        assert_eq!(
            output,
            ["sat"],
            "conic case {index}: {:?}",
            executor.unknown_reason()
        );
    }
}

#[test]
fn quadric_field_models_use_original_authored_validation_and_preserve_higher_degree_refusal() {
    let input = include_str!("fixtures/finite_field/quadric_models.smt2");
    for (index, body) in input.split("(reset)").enumerate() {
        let (executor, output) = run(body);
        assert_eq!(
            output,
            [if index < 6 { "sat" } else { "unknown" }],
            "quadric case {index}: {:?}",
            executor.unknown_reason()
        );
    }
}

#[test]
fn paid_default_field_frontend_preserves_authored_models_above_old_source_caps() {
    let (_, output) = run(include_str!("fixtures/finite_field/paid_frontend.smt2"));
    // These are actual default check-sat requests: both SAT proposals must pass
    // the ordinary independent authored-root gate before becoming public.
    assert_eq!(output, ["sat", "sat"]);
}
