// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn oversized_direct_finite_enum_script() -> String {
    let mut script = String::from(
        "(set-option :produce-proofs true)\n\
         (set-logic QF_DT)\n\
         (declare-datatype Unit ((u0) (u1) (u2)))\n",
    );
    for index in 0..4 {
        script.push_str(&format!("(declare-fun p{index} () Unit)\n"));
    }
    // Cross the generic proof-source root cap with cheap authored roots. The
    // finite-enum exception must select only the six authenticated edges.
    for _ in 0..OVERSIZED_PROOF_ROOTS {
        script.push_str("(assert true)\n");
    }
    for left in 0..4 {
        for right in (left + 1)..4 {
            script.push_str(&format!("(assert (not (= p{left} p{right})))\n"));
        }
    }
    script.push_str("(check-sat)\n(get-proof)\n");
    script
}

fn deep_surface_binary_distinct_script() -> String {
    let mut script = String::from(
        "(set-option :produce-proofs true)\n\
         (set-logic QF_DT)\n\
         (declare-datatype Unit ((u0) (u1) (u2)))\n",
    );
    for index in 0..4 {
        script.push_str(&format!("(declare-fun p{index} () Unit)\n"));
    }
    let mut deep_true = "true".to_string();
    for _ in 0..300 {
        deep_true = format!("(not {deep_true})");
    }
    script.push_str(&format!("(assert {deep_true})\n"));
    script.push_str("(assert (distinct p0 p1))\n");
    for left in 0..4 {
        for right in (left + 1)..4 {
            if (left, right) != (0, 1) {
                script.push_str(&format!("(assert (not (= p{left} p{right})))\n"));
            }
        }
    }
    script.push_str("(check-sat)\n(get-proof)\n");
    script
}

fn direct_finite_enum_assertions_only() -> String {
    let mut script = String::from(
        "(set-logic QF_DT)\n\
         (declare-datatype Unit ((u0) (u1) (u2)))\n",
    );
    for index in 0..4 {
        script.push_str(&format!("(declare-fun p{index} () Unit)\n"));
    }
    for left in 0..4 {
        for right in (left + 1)..4 {
            script.push_str(&format!("(assert (not (= p{left} p{right})))\n"));
        }
    }
    script
}

#[test]
fn direct_finite_enum_strict_wire_mode_declines_holey_native_certificate() {
    let mut script = String::from(
        "(set-option :produce-proofs true)\n\
         (set-option :check-proofs-strict true)\n",
    );
    script.push_str(&direct_finite_enum_assertions_only());
    script.push_str("(check-sat)\n");

    let commands = parse(&script).expect("parse direct strict enum clique");
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands)
            .expect("solve direct strict enum clique"),
        vec!["unknown"]
    );
    assert_eq!(
        exec.unknown_reason(),
        Some(crate::UnknownReason::ProofTrusted)
    );
}

#[test]
fn finite_enum_internal_certificate_does_not_require_parsed_retention() {
    let commands = parse(&direct_finite_enum_assertions_only()).expect("parse direct enum roots");
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(false);
    assert!(exec
        .execute_all(&commands)
        .expect("install direct enum roots")
        .is_empty());
    assert!(exec.ctx.assertions_parsed().is_empty());
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);

    let members: Vec<TermId> = (0..4)
        .map(|index| {
            exec.ctx
                .terms
                .lookup(&format!("p{index}"))
                .expect("declared member")
        })
        .collect();
    let mut edge_sources = ay_core::kani_compat::DetHashMap::default();
    for &source in &exec.ctx.assertions {
        let TermData::Not(equality) = exec.ctx.terms.get(source) else {
            continue;
        };
        let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(*equality) else {
            continue;
        };
        let [left, right] = args.as_slice() else {
            continue;
        };
        if name == "=" {
            let key = if left.0 < right.0 {
                (*left, *right)
            } else {
                (*right, *left)
            };
            edge_sources.insert(key, source);
        }
    }
    exec.last_finite_enum_pigeonhole = Some(crate::executor::FiniteEnumPigeonholeWitness {
        k: 3,
        members,
        edge_sources,
    });

    assert!(exec.try_install_bounded_finite_enum_pigeonhole_proof());
    let proof = exec.last_proof.as_ref().expect("installed internal proof");
    assert!(exec.last_proof_is_checked_finite_enum());
    exec.check_proof_strict_with_datatypes(proof)
        .expect("parsed-free internal proof must replay strictly");
    // Strict internal replay is not a user proof request: the query snapshot
    // must close every public exporter before surface diagnostics can leak it.
    assert!(exec
        .finite_enum_surface_overrides_for_proof(proof)
        .is_none());
    assert!(exec.last_proof.is_some(), "internal proof remains retained");
    assert!(
        exec.try_export_last_proof_alethe_for_problem_scope()
            .is_none(),
        "unrequested internal certificate must not be publicly exported"
    );
}

#[test]
#[timeout(120_000)]
fn oversized_finite_enum_exception_is_internal_strict_and_second_build_stable() {
    let commands =
        parse(&oversized_direct_finite_enum_script()).expect("parse oversized direct enum clique");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("solve oversized direct enum clique");
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    let alethe = outputs.get(1).expect("bounded get-proof output");
    assert!(
        alethe.contains(":rule hole"),
        "the pinned Alethe calculus has no datatype-exhaustiveness rule: {alethe}"
    );
    assert!(
        !alethe.contains(":rule dt_enum_pigeonhole"),
        "an unsupported internal rule name must never be emitted: {alethe}"
    );
    let original = exec.last_proof().expect("checked proof").clone();
    assert_eq!(
        exec.finite_enum_scope_for_proof(&original)
            .expect("sealed direct-root scope")
            .len(),
        6
    );

    // The generic trace has already been consumed. A repeated build must keep
    // the exact checked proof/capability instead of reaching source poison.
    exec.build_unsat_proof();
    assert!(exec
        .finite_enum_scope_for_proof(exec.last_proof().expect("retained proof"))
        .is_some());

    // A foreign candidate cannot borrow the stored proof's narrow root scope.
    let foreign = exec
        .ctx
        .terms
        .mk_var("finite_enum_foreign_assume", Sort::Bool);
    let mut forged = original.clone();
    forged.steps[1] = ProofStep::Assume(foreign);
    assert!(exec.finite_enum_scope_for_proof(&forged).is_none());
    assert!(exec.check_proof_strict_with_datatypes(&forged).is_err());

    assert!(exec
        .finite_enum_surface_overrides_for_proof(&original)
        .is_some());

    // Even a byte-for-byte proof clone loses the capability after a new public
    // decision rotates the opaque query epoch. The raw diagnostic remains so
    // this is non-vacuous, but every authoritative public proof surface closes:
    // returning a stale-surface error would reveal that the hidden proof exists,
    // while `None`/"not generated" consistently reports no eligible artifact.
    exec.advance_query_authority_epoch();
    assert!(exec.finite_enum_scope_for_proof(&original).is_none());
    assert!(exec.last_proof.is_some(), "staling retains the raw proof");
    assert!(exec
        .try_export_last_proof_alethe_for_problem_scope()
        .is_none());
    let mut stale_output = Vec::new();
    assert!(exec
        .try_export_last_proof_alethe_for_problem_scope_to(&mut stale_output)
        .is_none());
    assert!(stale_output.is_empty());
    assert!(exec.get_proof().contains("proof was not generated"));

    // Result invalidation retires a newly recorded detector candidate together
    // with the stale capability sidecar.
    exec.last_finite_enum_pigeonhole = Some(crate::executor::FiniteEnumPigeonholeWitness {
        k: 1,
        members: Vec::new(),
        edge_sources: Default::default(),
    });
    exec.invalidate_last_check_result();
    assert!(exec.last_finite_enum_pigeonhole.is_none());
    assert!(exec.last_checked_finite_enum_pigeonhole.is_none());
}

#[test]
#[timeout(30_000)]
fn binary_distinct_special_proof_is_internal_only_and_all_alethe_exports_decline() {
    let commands = parse(&deep_surface_binary_distinct_script())
        .expect("parse binary-distinct finite enum script");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("solve binary-distinct finite enum script");
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    assert!(outputs
        .get(1)
        .is_some_and(|output| output.contains("no authenticated external surface")));

    let proof = exec.last_proof().expect("internally checked proof");
    assert!(exec.last_proof_is_checked_finite_enum());
    exec.check_proof_strict_with_datatypes(proof)
        .expect("binary distinct canonical root remains valid internal authority");
    assert!(exec
        .finite_enum_surface_overrides_for_proof(proof)
        .is_none());
    assert!(matches!(
        exec.try_export_last_proof_alethe_for_problem_scope(),
        Some(Err(
            AlethePrintError::UnavailableAuthenticatedSurface { .. }
        ))
    ));
    let mut output = Vec::new();
    assert!(matches!(
        exec.try_export_last_proof_alethe_for_problem_scope_to(&mut output),
        Some(Err(ay_proof::AletheStreamError::Print(
            AlethePrintError::UnavailableAuthenticatedSurface { .. }
        )))
    ));
    assert!(output.is_empty());
}

#[test]
fn finite_enum_witness_cannot_replace_an_unrelated_proof() {
    let mut exec = Executor::new();
    let sort = Sort::Uninterpreted("UnrelatedProofUnit".to_string());
    let left = exec.ctx.terms.mk_var("unrelated_left", sort.clone());
    let right = exec.ctx.terms.mk_var("unrelated_right", sort);
    let equality = exec.ctx.terms.mk_eq(left, right);
    let source = exec.ctx.terms.mk_not_raw(equality);
    let key = if left.0 < right.0 {
        (left, right)
    } else {
        (right, left)
    };
    exec.last_finite_enum_pigeonhole = Some(crate::executor::FiniteEnumPigeonholeWitness {
        k: 1,
        members: vec![left, right],
        edge_sources: [(key, source)].into_iter().collect(),
    });

    let foreign = exec.ctx.terms.mk_var(
        "unrelated_foreign",
        Sort::Uninterpreted("UnrelatedProofUnit".to_string()),
    );
    let foreign_equality = exec.ctx.terms.mk_eq(left, foreign);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("foreign", vec![foreign_equality], TheoryLemmaKind::Generic);
    let before = format!("{:?}", proof.steps);
    exec.rebuild_finite_enum_pigeonhole_refutation(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before);
}

#[test]
fn finite_enum_witness_owns_its_normalized_complete_equality_clause() {
    let mut exec = Executor::new();
    let sort = Sort::Uninterpreted("NormalizedProofUnit".to_string());
    let left = exec.ctx.terms.mk_var("normalized_left", sort.clone());
    let right = exec.ctx.terms.mk_var("normalized_right", sort);
    let equality = exec.ctx.terms.mk_eq(left, right);
    let source = exec.ctx.terms.mk_not_raw(equality);
    exec.ctx.assertions.push(source);
    let key = if left.0 < right.0 {
        (left, right)
    } else {
        (right, left)
    };
    exec.last_finite_enum_pigeonhole = Some(crate::executor::FiniteEnumPigeonholeWitness {
        k: 1,
        members: vec![left, right],
        edge_sources: [(key, source)].into_iter().collect(),
    });

    let normalized_complement = exec.ctx.terms.mk_not_raw(source);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "normalized",
        vec![normalized_complement],
        TheoryLemmaKind::Generic,
    );
    exec.rebuild_finite_enum_pigeonhole_refutation(&mut proof);

    assert!(matches!(
        proof.steps.as_slice(),
        [
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::DatatypeEnumPigeonhole,
                clause,
                ..
            },
            ProofStep::Assume(assumption),
            ProofStep::Step {
                rule: AletheRule::Resolution,
                clause: conclusion,
                premises,
                args,
            }
        ] if clause == &[equality]
            && *assumption == source
            && conclusion.is_empty()
            && premises == &[ProofId(0), ProofId(1)]
            && args.is_empty()
    ));
}

#[test]
fn finite_enum_witness_rejects_duplicate_normalized_edge() {
    let mut exec = Executor::new();
    let sort = Sort::Uninterpreted("DuplicateProofUnit".to_string());
    let a = exec.ctx.terms.mk_var("duplicate_a", sort.clone());
    let b = exec.ctx.terms.mk_var("duplicate_b", sort.clone());
    let c = exec.ctx.terms.mk_var("duplicate_c", sort);
    let ab = exec.ctx.terms.mk_eq(a, b);
    let ac = exec.ctx.terms.mk_eq(a, c);
    let bc = exec.ctx.terms.mk_eq(b, c);
    let not_ab = exec.ctx.terms.mk_not_raw(ab);
    let not_ac = exec.ctx.terms.mk_not_raw(ac);
    let not_bc = exec.ctx.terms.mk_not_raw(bc);
    exec.ctx.assertions.extend([not_ab, not_ac, not_bc]);
    let pair = |left: TermId, right: TermId| {
        if left.0 < right.0 {
            (left, right)
        } else {
            (right, left)
        }
    };
    exec.last_finite_enum_pigeonhole = Some(crate::executor::FiniteEnumPigeonholeWitness {
        k: 2,
        members: vec![a, b, c],
        edge_sources: [
            (pair(a, b), not_ab),
            (pair(a, c), not_ac),
            (pair(b, c), not_bc),
        ]
        .into_iter()
        .collect(),
    });

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("duplicate", vec![ab, ac, ac], TheoryLemmaKind::Generic);
    let before = format!("{:?}", proof.steps);
    exec.rebuild_finite_enum_pigeonhole_refutation(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before);
}

#[test]
fn bool_tautology_leaf_promotion_is_semantic_and_fail_closed() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("bool-leaf-p", Sort::Bool);
    let q = exec.ctx.terms.mk_var("bool-leaf-q", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not_raw(p);
    let eq = exec.ctx.terms.mk_eq(p, q);
    let not_eq = exec.ctx.terms.mk_not_raw(eq);

    // Equality transfer: p and p=q entail q.
    let tautology = exec.ctx.terms.mk_or(vec![q, not_p, not_eq]);
    // One-polarity mutation is false at p=false,q=false and must stay Trust.
    let near_tautology = exec.ctx.terms.mk_or(vec![q, p, not_eq]);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![tautology], Vec::new(), Vec::new());
    proof.add_rule_step(
        AletheRule::Trust,
        vec![near_tautology],
        Vec::new(),
        Vec::new(),
    );

    Executor::promote_bool_tautology_leaves(&exec.ctx.terms, &mut proof);

    assert!(matches!(
        &proof.steps[0],
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BoolTautology,
            clause,
            ..
        } if clause == &[tautology]
    ));
    assert!(matches!(
        &proof.steps[1],
        ProofStep::Step {
            rule: AletheRule::Trust,
            clause,
            ..
        } if clause == &[near_tautology]
    ));
}
