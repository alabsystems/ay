// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;
use ay_frontend::parse;

fn fixture(bound: u32, include_second_edge: bool, expected_zero: u32) -> String {
    let second_edge = include_second_edge
        .then_some("(= x3 x2)")
        .unwrap_or("(= unrelated x2)");
    format!(
        r#"(set-logic ALL)
            (declare-const x1 (_ BitVec 64))
            (declare-const x2 (_ BitVec 64))
            (declare-const x3 (_ BitVec 64))
            (declare-const unrelated (_ BitVec 64))
            (assert (and
                (not (= ((_ extract 127 64)
                          (bvmul ((_ zero_extend 64) x1) (_ bv8 128)))
                        (_ bv{expected_zero} 64)))
                (= x2 x1)
                {second_edge}
                (bvult x3 (_ bv{bound} 64))))"#
    )
}

fn ult_fanout_fixture(fact_count: usize) -> String {
    let facts = (0..fact_count)
        .map(|_| "(bvult x3 (_ bv1 64))")
        .collect::<Vec<_>>()
        .join(" ");
    format!(
        r#"(set-logic ALL)
            (declare-const x1 (_ BitVec 64))
            (declare-const x2 (_ BitVec 64))
            (declare-const x3 (_ BitVec 64))
            (assert (and
                (not (= ((_ extract 127 64)
                          (bvmul ((_ zero_extend 64) x1) (_ bv8 128)))
                        (_ bv0 64)))
                (= x2 x1)
                (= x3 x2)
                {facts}))"#
    )
}

fn executor_for(source: &str) -> Executor {
    let commands = parse(source).expect("test input parses");
    let mut executor = Executor::new();
    assert!(executor
        .execute_all(&commands)
        .expect("declarations/assertion execute")
        .is_empty());
    executor
}

fn build_candidate(executor: &mut Executor) -> Option<Proof> {
    let parsed = executor.ctx.assertions_parsed().to_vec();
    let [surface] = parsed.as_slice() else {
        return None;
    };
    let root = build_qfbv_pterm(&mut executor.ctx.terms, surface)?;
    let TermData::App(Symbol::Named(operator), conjuncts) = executor.ctx.terms.get(root).clone()
    else {
        return None;
    };
    if operator != "and" {
        return None;
    }
    executor.build_authored_bv_high_zero_candidate(root, &conjuncts, &[root])
}

fn raw_fixture_root(executor: &mut Executor) -> TermId {
    let parsed = executor.ctx.assertions_parsed().to_vec();
    let [surface] = parsed.as_slice() else {
        panic!("fixture must contain exactly one parsed assertion");
    };
    build_qfbv_pterm(&mut executor.ctx.terms, surface).expect("fixture raw root rebuilds")
}

fn provisional_trust_proof() -> Proof {
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    proof
}

fn assert_single_trust(proof: &Proof) {
    assert!(matches!(
        proof.steps.as_slice(),
        [ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }]
    ));
}

#[test]
fn builds_strict_hole_free_high_zero_refutation() {
    let mut executor = executor_for(&fixture(1, true, 0));
    let proof = build_candidate(&mut executor).expect("exact authored core must reconstruct");
    let authored: Vec<TermId> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    let quality = ay_proof::check_proof_strict_with_context(
        &proof,
        &executor.ctx.terms,
        None,
        None,
        Some(&authored),
    )
    .expect("candidate replays strictly");
    assert!(quality.is_complete());
    assert!(!executor.proof_has_known_wire_gap(&proof));
    let text = ay_proof::export_alethe(&proof, &executor.ctx.terms);
    assert!(text.contains(":rule evaluate"), "{text}");
    assert!(text.contains("pbblast_bvult"), "{text}");
    assert!(!text.contains(":rule hole"), "{text}");
    assert!(!text.contains(":rule trust"), "{text}");
}

#[test]
fn conjunct_projections_carry_the_exact_authored_source_and_index() {
    let mut executor = executor_for(&fixture(1, true, 0));
    let proof = build_candidate(&mut executor).expect("exact authored core must reconstruct");
    let root = proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::Assume(root) => Some(*root),
            _ => None,
        })
        .expect("candidate must assume the exact authored root");
    let TermData::App(Symbol::Named(operator), conjuncts) = executor.ctx.terms.get(root).clone()
    else {
        panic!("authored root must be an application");
    };
    assert_eq!(operator, "and");
    let not_root = executor.ctx.terms.mk_not_raw(root);

    let mut projection_count = 0;
    for step in &proof.steps {
        let ProofStep::Step {
            rule: AletheRule::AndPos(position),
            clause,
            args,
            ..
        } = step
        else {
            continue;
        };
        let conjunct = conjuncts
            .get(usize::try_from(*position).expect("u32 projection index fits usize"))
            .expect("projection index must name an authored conjunct");
        assert_eq!(args.as_slice(), [root]);
        assert_eq!(clause.as_slice(), [not_root, *conjunct]);
        projection_count += 1;
    }
    assert!(
        projection_count >= 4,
        "fixture must exercise repeated projections"
    );
}

#[test]
fn replacement_consumes_preexisting_raw_authority_without_minting_it() {
    let mut executor = executor_for(&fixture(1, true, 0));
    let raw_root = raw_fixture_root(&mut executor);
    executor.record_raw_authored_problem_assertion(raw_root);
    let raw_before = executor.last_proof_raw_original_assertions.clone();
    let rebuild_before = executor.last_proof_rebuild_originals.clone();
    let mut proof = provisional_trust_proof();

    executor.replace_with_exact_authored_bv_high_zero_refutation(&mut proof);

    assert!(Executor::proof_derives_empty_clause(&proof));
    assert!(!proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }
    )));
    assert_eq!(executor.last_proof_raw_original_assertions, raw_before);
    assert_eq!(executor.last_proof_rebuild_originals, rebuild_before);
}

#[test]
fn replacement_declines_when_raw_root_has_no_preexisting_membership() {
    let mut executor = executor_for(&fixture(1, true, 0));
    let mut proof = provisional_trust_proof();

    executor.replace_with_exact_authored_bv_high_zero_refutation(&mut proof);

    assert_single_trust(&proof);
    assert!(executor.last_proof_raw_original_assertions.is_empty());
    assert!(executor.last_proof_rebuild_originals.is_empty());
}

#[test]
fn replacement_declines_misaligned_parsed_and_canonical_indices() {
    let mut executor = executor_for(&fixture(1, true, 0));
    let raw_root = raw_fixture_root(&mut executor);
    executor.record_raw_authored_problem_assertion(raw_root);
    executor.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance {
        original_problem_assertions: Vec::new(),
        problem_assertions: Vec::new(),
        assertion_sources: Default::default(),
    });
    assert_eq!(executor.ctx.assertions_parsed().len(), 1);
    assert!(executor
        .proof_original_problem_assertions_slice()
        .is_empty());
    let mut proof = provisional_trust_proof();

    executor.replace_with_exact_authored_bv_high_zero_refutation(&mut proof);

    assert_single_trust(&proof);
}

#[test]
fn replacement_accepts_exact_membership_when_raw_ledger_order_differs() {
    let source = format!("{}\n(assert (= x1 x1))", fixture(1, true, 0));
    let mut executor = executor_for(&source);
    let parsed = executor.ctx.assertions_parsed().to_vec();
    let [high_zero_surface, other_surface] = parsed.as_slice() else {
        panic!("fixture must contain exactly two parsed assertions");
    };
    let high_zero_raw = build_qfbv_pterm(&mut executor.ctx.terms, high_zero_surface)
        .expect("high-zero raw root rebuilds");
    let other_raw =
        build_qfbv_pterm(&mut executor.ctx.terms, other_surface).expect("other raw root rebuilds");
    executor.last_proof_raw_original_assertions = vec![other_raw, high_zero_raw];
    executor.last_proof_rebuild_originals = vec![high_zero_raw, other_raw];
    assert_eq!(
        executor.last_proof_raw_original_assertions.len(),
        executor.ctx.assertions_parsed().len(),
        "the mismatch is positional, not a cardinality shortcut"
    );
    let mut proof = provisional_trust_proof();

    executor.replace_with_exact_authored_bv_high_zero_refutation(&mut proof);

    assert!(Executor::proof_derives_empty_clause(&proof));
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(!proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }
    )));
}

#[test]
fn replacement_accepts_deduplicated_authority_for_identical_raw_roots() {
    let source = format!(
        "{}\n{}",
        fixture(1, true, 0),
        r#"(assert (and
                (not (= ((_ extract 127 64)
                          (bvmul ((_ zero_extend 64) x1) (_ bv8 128)))
                        (_ bv0 64)))
                (= x2 x1)
                (= x3 x2)
                (bvult x3 (_ bv1 64))))"#
    );
    let mut executor = executor_for(&source);
    let parsed = executor.ctx.assertions_parsed().to_vec();
    let [first_surface, second_surface] = parsed.as_slice() else {
        panic!("fixture must contain two identical parsed assertions");
    };
    let first_raw =
        build_qfbv_pterm(&mut executor.ctx.terms, first_surface).expect("first raw root rebuilds");
    let second_raw = build_qfbv_pterm(&mut executor.ctx.terms, second_surface)
        .expect("second raw root rebuilds");
    assert_eq!(first_raw, second_raw, "raw TermIds identify exact syntax");
    executor.last_proof_raw_original_assertions = vec![first_raw];
    executor.last_proof_rebuild_originals = vec![first_raw];
    let mut proof = provisional_trust_proof();

    executor.replace_with_exact_authored_bv_high_zero_refutation(&mut proof);

    assert!(Executor::proof_derives_empty_clause(&proof));
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
}

#[test]
fn missing_raw_authority_declines_before_publication_walk() {
    let mut executor = executor_for(&fixture(1, true, 0));
    let mut proof = Proof::new();
    let checks_before = executor.strict_check_invocations.get();

    executor.replace_with_exact_authored_bv_high_zero_refutation(&mut proof);

    assert_eq!(executor.strict_check_invocations.get(), checks_before);
    assert!(proof.steps.is_empty());
}

#[test]
fn rejects_non_one_bound() {
    let mut executor = executor_for(&fixture(2, true, 0));
    assert!(build_candidate(&mut executor).is_none());
}

#[test]
fn rejects_broken_variable_equality_path() {
    let mut executor = executor_for(&fixture(1, false, 0));
    assert!(build_candidate(&mut executor).is_none());
}

#[test]
fn rejects_nonzero_target_literal() {
    let mut executor = executor_for(&fixture(1, true, 1));
    assert!(build_candidate(&mut executor).is_none());
}

#[test]
fn rejects_ult_fact_fanout_above_cap() {
    let mut executor = executor_for(&ult_fanout_fixture(MAX_ULT_ONE_FACTS + 1));
    assert!(build_candidate(&mut executor).is_none());
}

#[test]
fn path_search_fails_closed_when_work_budget_is_exhausted() {
    let mut executor = executor_for(&fixture(1, true, 0));
    let parsed = executor.ctx.assertions_parsed().to_vec();
    let root = build_qfbv_pterm(&mut executor.ctx.terms, &parsed[0]).expect("raw root");
    let TermData::App(_, conjuncts) = executor.ctx.terms.get(root).clone() else {
        panic!("fixture root must be an application");
    };
    let target = conjuncts
        .iter()
        .copied()
        .enumerate()
        .find_map(|(index, term)| decode_high_zero_target(&executor.ctx.terms, term, index))
        .expect("target");
    let ult = conjuncts
        .iter()
        .copied()
        .enumerate()
        .find_map(|(index, term)| decode_ult_one_fact(&executor.ctx.terms, term, index))
        .expect("ult fact");
    let edges: Vec<_> = conjuncts
        .iter()
        .copied()
        .enumerate()
        .filter_map(|(index, term)| decode_var_equality(&executor.ctx.terms, term, index))
        .collect();
    let mut no_work = 0;
    assert!(equality_path(&edges, ult.subject, target.subject, &mut no_work).is_none());
}

fn nested_not_surface(depth: usize) -> FrontendTerm {
    let mut term = FrontendTerm::Symbol("surface_depth_leaf".to_string());
    for _ in 0..depth {
        term = FrontendTerm::App("not".to_string(), vec![term]);
    }
    term
}

#[test]
fn surface_rebuild_depth_gate_accepts_exact_boundary_and_rejects_next_level() {
    assert!(qfbv_surface_within_authored_rebuild_budget(
        &nested_not_surface(MAX_AUTHORED_SURFACE_DEPTH)
    ));
    assert!(!qfbv_surface_within_authored_rebuild_budget(
        &nested_not_surface(MAX_AUTHORED_SURFACE_DEPTH + 1)
    ));
}

#[test]
fn surface_rebuild_node_gate_accepts_exact_boundary_and_rejects_one_more() {
    let children = (0..MAX_AUTHORED_SURFACE_NODES - 1)
        .map(|_| FrontendTerm::Const(FrontendConstant::True))
        .collect();
    let mut surface = FrontendTerm::App("and".to_string(), children);
    assert!(qfbv_surface_within_authored_rebuild_budget(&surface));

    let FrontendTerm::App(_, children) = &mut surface else {
        panic!("test surface must remain an application");
    };
    children.push(FrontendTerm::Const(FrontendConstant::True));
    assert!(!qfbv_surface_within_authored_rebuild_budget(&surface));
}

#[test]
fn surface_token_byte_gate_accepts_exact_boundary_and_rejects_one_more() {
    let exact = FrontendTerm::Symbol("x".repeat(MAX_AUTHORED_SURFACE_TOKEN_BYTES));
    assert!(qfbv_surface_within_authored_rebuild_budget(&exact));

    let over = FrontendTerm::Symbol("x".repeat(MAX_AUTHORED_SURFACE_TOKEN_BYTES + 1));
    assert!(!qfbv_surface_within_authored_rebuild_budget(&over));
}

#[test]
fn parsed_root_selection_shares_exact_token_byte_budget_across_roots() {
    let first_len = MAX_AUTHORED_SURFACE_TOKEN_BYTES / 2;
    let second_len = MAX_AUTHORED_SURFACE_TOKEN_BYTES - first_len;
    let exact = vec![
        FrontendTerm::Symbol("x".repeat(first_len)),
        FrontendTerm::Symbol("y".repeat(second_len)),
    ];
    assert_eq!(
        admitted_qfbv_surface_indices(&exact),
        Some(vec![0, 1]),
        "the aggregate token-byte budget must admit its exact boundary"
    );

    let over = vec![
        FrontendTerm::Symbol("x".repeat(first_len)),
        FrontendTerm::Symbol("y".repeat(second_len + 1)),
    ];
    assert_eq!(
        admitted_qfbv_surface_indices(&over),
        Some(vec![0]),
        "the next root must be refused when aggregate token bytes exceed the cap by one"
    );
}

#[test]
fn surface_decimal_token_gate_accepts_exact_digit_boundary_and_rejects_one_more() {
    let indexed_bv = |digits: usize| {
        FrontendTerm::IndexedApp(
            format!("bv{}", "9".repeat(digits)),
            vec![FrontendIndex::Numeral("64".to_string())],
            Vec::new(),
        )
    };
    assert!(qfbv_surface_within_authored_rebuild_budget(&indexed_bv(
        MAX_AUTHORED_DECIMAL_TOKEN_DIGITS
    )));
    assert!(!qfbv_surface_within_authored_rebuild_budget(&indexed_bv(
        MAX_AUTHORED_DECIMAL_TOKEN_DIGITS + 1
    )));

    let indexed_operator = |digits: usize| {
        FrontendTerm::IndexedApp(
            "extract".to_string(),
            vec![
                FrontendIndex::Numeral("9".repeat(digits)),
                FrontendIndex::Numeral("0".to_string()),
            ],
            vec![FrontendTerm::Symbol("decimal_cap_x".to_string())],
        )
    };
    assert!(qfbv_surface_within_authored_rebuild_budget(
        &indexed_operator(MAX_AUTHORED_DECIMAL_TOKEN_DIGITS)
    ));
    assert!(!qfbv_surface_within_authored_rebuild_budget(
        &indexed_operator(MAX_AUTHORED_DECIMAL_TOKEN_DIGITS + 1)
    ));
}

#[test]
fn parsed_root_selection_excludes_overdepth_surface_before_clone() {
    let surfaces = vec![
        nested_not_surface(MAX_AUTHORED_SURFACE_DEPTH + 1),
        nested_not_surface(MAX_AUTHORED_SURFACE_DEPTH),
    ];
    assert_eq!(
        admitted_qfbv_surface_indices(&surfaces),
        Some(vec![1]),
        "only a pre-admitted root may reach the bounded recursive clone/rebuild"
    );
}

#[test]
fn parsed_root_selection_shares_one_node_budget_across_all_roots() {
    let root_nodes = MAX_AUTHORED_SURFACE_NODES / 2;
    let make_root = || {
        FrontendTerm::App(
            "and".to_string(),
            (0..root_nodes - 1)
                .map(|_| FrontendTerm::Const(FrontendConstant::True))
                .collect(),
        )
    };
    let surfaces = vec![make_root(), make_root(), make_root()];
    assert_eq!(
        admitted_qfbv_surface_indices(&surfaces),
        Some(vec![0, 1]),
        "all clone/rebuild attempts must share one aggregate surface-node budget"
    );
}

#[test]
fn canonical_scope_above_root_cap_leaves_proof_unchanged() {
    let mut executor = executor_for(&fixture(1, true, 0));
    let assumptions = (0..MAX_AUTHORED_ROOTS)
        .map(|index| {
            executor
                .ctx
                .terms
                .mk_var(format!("scope_filler_{index}"), Sort::Bool)
        })
        .collect();
    executor.last_assumptions = Some(assumptions);
    assert!(executor.exact_concrete_authored_scope().len() > MAX_AUTHORED_ROOTS);

    let mut proof = provisional_trust_proof();
    executor.replace_with_exact_authored_bv_high_zero_refutation(&mut proof);

    assert_single_trust(&proof);
}
