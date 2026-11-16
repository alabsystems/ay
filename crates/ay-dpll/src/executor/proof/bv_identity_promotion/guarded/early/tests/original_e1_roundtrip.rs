// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::proof_repair::proof_trust_surgery_surface_audit::{
    surface_source_work_probe_as, SurfaceWorkModel,
};
use sha2::{Digest, Sha256};

const QUERY: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/src/executor/proof_original_e1_exit0.smt2"
));

#[test]
fn original_e1_public_memory_entry_retains_a_checked_source_refutation() {
    let mut executor = Executor::new();
    // The retained source requests models; CLI strict mode separately requests
    // proofs. Exercise that same proof-producing public entry here.
    executor.set_produce_proofs(true);
    executor.set_timeout(Some(Duration::from_secs(30)));
    executor.set_memory_limit(Some(8 * 1024 * 1024 * 1024));
    for command in ay_frontend::parse(QUERY).unwrap() {
        if !matches!(command, Command::CheckSat | Command::Exit) {
            executor.execute_authored(&command).unwrap();
        }
    }
    assert_eq!(
        executor
            .execute_authored(&Command::CheckSat)
            .unwrap()
            .as_deref(),
        Some("unsat"),
        "original memory query must survive competing closure candidates: {:?}",
        executor.unknown_reason()
    );
    let proof = executor.last_proof().expect("public source proof retained");
    let scope = executor.proof_export_scope_assertions();
    ay_proof::validate_reachable_assumes_in_problem_scope(proof, &scope).unwrap();
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap()
        .is_complete());
    assert!(executor
        .last_proof_with_authenticated_alethe_surface()
        .is_some());
}

fn dimensions(root: &FrontendTerm) -> (usize, usize, usize) {
    let (mut nodes, mut deepest, mut longest_binary) = (0, 0, 0);
    let mut pending = vec![(root, 0usize)];
    while let Some((term, depth)) = pending.pop() {
        nodes += 1;
        deepest = deepest.max(depth);
        match term {
            FrontendTerm::App(_, children)
            | FrontendTerm::IndexedApp(_, _, children)
            | FrontendTerm::QualifiedApp(_, _, children) => {
                pending.extend(children.iter().map(|child| (child, depth + 1)));
            }
            FrontendTerm::Const(ay_frontend::Constant::Binary(text)) => {
                longest_binary = longest_binary.max(text.len());
            }
            FrontendTerm::Symbol(_) | FrontendTerm::Const(_) => (),
            _ => panic!("unchanged query is ground source"),
        }
    }
    (nodes, deepest, longest_binary)
}

#[test]
fn original_e1_exit0_roundtrips_root_and_generated_negative_under_existing_limits() {
    assert_eq!(QUERY.len(), 1_073_945);
    assert_eq!(
        format!("{:x}", Sha256::digest(QUERY.as_bytes())),
        "79fbfab7d17542fea628e919f8cb9310c88c1a1988be2edf434e15ba1f693773"
    );
    let mut executor = loaded(QUERY);
    let source = executor.ctx.assertions_parsed()[0].clone();
    assert_eq!(dimensions(&source).0, 84_578);
    assert_eq!(dimensions(&source).1, 96);
    let root = executor
        .raw_intern_shared_ground_memory_surface(&source)
        .expect("exact source now reconstructs inside unchanged limits");
    let negative = executor.ctx.terms.mk_not_raw(root);
    let overrides = executor.proof_export_term_overrides().unwrap_or_default();
    for (name, term, expected_depth) in [("root", root, 96), ("negative", negative, 97)] {
        let rendered =
            ay_proof::format_term_alethe_with_overrides(&executor.ctx.terms, term, &overrides);
        let mut parsed = crate::executor::proof::parse_rendered_assertion(&rendered)
            .expect("actual printer output parses");
        let before = dimensions(&parsed);
        let traversal = surface_source_work_probe_as(&parsed, SurfaceWorkModel::Traversal);
        println!(
            "original E1 {name}: bytes={} dimensions={before:?} traversal={traversal:?}",
            rendered.len()
        );
        assert!(traversal.is_ok());
        super::super::super::compact_roundtrip_literal_leaves(&mut parsed)
            .expect("existing temporary literal normalization");
        let after = dimensions(&parsed);
        assert_eq!(after.1, expected_depth);
        let rebuilt = executor.raw_intern_shared_ground_memory_surface(&parsed);
        println!("original E1 {name}: normalized_dimensions={after:?} rebuilt={rebuilt:?} expected={term:?}");
        if name == "root" {
            assert_eq!(rebuilt, Some(term));
        } else {
            assert!(
                rebuilt.is_none(),
                "the whole printed wrapper remains outside source depth96"
            );
        }
    }
    let copy_budget = executor
        .ground_surface_render_budget(&[root, negative], &overrides)
        .expect("full expanded output fits unchanged aggregate byte envelope");
    let (batch, _, actual_copy_work) =
        ay_proof::format_terms_alethe_with_overrides_and_canonical_bounded_with_work(
            &executor.ctx.terms,
            &[root, negative],
            &overrides,
            &[],
            copy_budget,
        )
        .expect("existing shared actual-work renderer");
    assert_eq!(batch[&root].len(), 2_559_750);
    assert_eq!(batch[&negative].len(), 2_559_756);
    assert!(actual_copy_work <= copy_budget);
    println!("original E1 shared printer: output={} actual_copy_work={actual_copy_work} conservative_copy_bound={copy_budget}", batch[&root].len() + batch[&negative].len());
    assert!(executor.early_ground_memory_terms_print_faithfully(&[root]));
    assert!(
        executor.early_ground_memory_terms_print_faithfully(&[root, negative]),
        "generated proof negation must compose the exact child roundtrip without raising source depth"
    );
    assert_eq!(
        executor.last_proof_raw_original_assertions,
        [] as [TermId; 0]
    );
    assert!(executor.last_proof().is_none());
}

fn original_pair() -> (Executor, FrontendTerm, TermId, TermId) {
    let mut executor = loaded(QUERY);
    let source = executor.ctx.assertions_parsed()[0].clone();
    let root = executor
        .raw_intern_shared_ground_memory_surface(&source)
        .unwrap();
    let negative = executor.ctx.terms.mk_not_raw(root);
    (executor, source, root, negative)
}

fn no_authority(executor: &Executor) {
    assert_eq!(
        executor.last_proof_raw_original_assertions,
        [] as [TermId; 0]
    );
    assert_eq!(executor.last_proof_rebuild_originals, [] as [TermId; 0]);
    assert!(executor.last_proof().is_none());
    assert!(executor.last_unsat_certificate.is_none());
}

#[test]
fn authored_depth97_and_nested_generated_shells_get_no_recursive_credit() {
    let (mut executor, source, root, negative) = original_pair();
    let authored = FrontendTerm::App("not".into(), vec![source]);
    assert_eq!(dimensions(&authored).1, 97);
    assert!(executor
        .raw_intern_shared_ground_memory_surface(&authored)
        .is_none());
    let nested = executor.ctx.terms.mk_not_raw(negative);
    assert!(!executor.early_ground_memory_terms_print_faithfully(&[negative, nested]));
    assert!(!executor.early_ground_memory_terms_print_faithfully(&[root, nested]));
    no_authority(&executor);
}

#[test]
fn actual_negative_override_must_keep_the_single_builtin_shell_and_checked_child() {
    let (mut executor, _, root, negative) = original_pair();
    let root_text = ay_proof::format_term_alethe_with_overrides(
        &executor.ctx.terms,
        root,
        &executor.proof_export_term_overrides().unwrap_or_default(),
    );
    for (name, text) in [
        ("replaced whole negative", "false".into()),
        ("wrong child", "(not true)".into()),
        ("missing child", "(not)".into()),
        ("extra child", format!("(not {root_text} {root_text})")),
        ("wrong head", format!("(and {root_text})")),
        ("nested shell", format!("(not (not {root_text}))")),
    ] {
        executor
            .last_proof_term_overrides
            .get_or_insert_with(Default::default)
            .insert(negative, text);
        assert!(
            !executor.early_ground_memory_terms_print_faithfully(&[root, negative]),
            "{name}"
        );
        no_authority(&executor);
    }
    executor
        .last_proof_term_overrides
        .as_mut()
        .unwrap()
        .insert(negative, format!("(not {root_text})"));
    assert!(
        executor.early_ground_memory_terms_print_faithfully(&[root, negative]),
        "an exact own override still describes the actual checked pair"
    );
    no_authority(&executor);
}

#[test]
fn actual_child_override_mismatch_cannot_borrow_root_roundtrip() {
    let (mut executor, _, root, negative) = original_pair();
    let child = executor
        .ctx
        .terms
        .children(root)
        .into_iter()
        .next()
        .unwrap();
    assert_ne!(child, root);
    executor
        .last_proof_term_overrides
        .get_or_insert_with(Default::default)
        .insert(child, "true".into());
    assert!(!executor.early_ground_memory_terms_print_faithfully(&[root, negative]));
    no_authority(&executor);
}

fn small_pair(prelude: &str) -> (Executor, TermId, TermId) {
    let mut executor = loaded(&format!(
        "{prelude} (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))"
    ));
    let commands = ay_frontend::parse("(assert (= (select a #x00) #x00))").unwrap();
    let Command::Assert(source) = &commands[0] else {
        panic!("assertion")
    };
    let root = executor
        .raw_intern_shared_ground_memory_surface(source)
        .unwrap();
    let negative = executor.ctx.terms.mk_not_raw(root);
    (executor, root, negative)
}

#[test]
fn declared_overloaded_defined_and_adopted_not_cannot_own_derived_builtin_shell() {
    let (mut builtin, root, negative) = small_pair("");
    assert!(builtin.early_ground_memory_terms_print_faithfully(&[root, negative]));
    no_authority(&builtin);
    for prelude in [
        "(declare-fun not (Bool) Bool)",
        "(declare-fun not (Bool) Bool) (declare-fun not ((_ BitVec 8)) (_ BitVec 8))",
        "(define-fun not ((p Bool)) Bool p)",
        "(declare-fun not (Bool) Bool) (assert (forall ((p Bool)) (= (not p) p)))",
    ] {
        let (mut executor, root, negative) = small_pair(prelude);
        if prelude.contains("forall") {
            // A builtin-collision declaration has a private core identity;
            // the existing adopter refuses it rather than creating a macro.
            assert!(executor.ctx.adopted_macro_interp("not").is_none());
        }
        assert!(
            !executor.early_ground_memory_terms_print_faithfully(&[root, negative]),
            "{prelude}"
        );
        no_authority(&executor);
    }
}

#[test]
fn full_negative_render_payload_and_existing_stop_controls_remain_bounded() {
    let (mut executor, root, negative) = small_pair("");
    executor
        .last_proof_term_overrides
        .get_or_insert_with(Default::default)
        .insert(negative, "x".repeat(8 * 1024 * 1024 + 1));
    assert!(!executor.early_ground_memory_terms_print_faithfully(&[root, negative]));
    no_authority(&executor);
    for control in 0..3 {
        let (mut executor, root, negative) = small_pair("");
        match control {
            0 => executor.set_interrupt(Arc::new(AtomicBool::new(true))),
            1 => executor.set_deadline(Some(
                Instant::now()
                    .checked_sub(Duration::from_secs(1))
                    .expect("fixture instant supports a one-second past deadline"),
            )),
            _ => executor.set_term_memory_limit(Some(0)),
        }
        assert!(!executor.early_ground_memory_terms_print_faithfully(&[root, negative]));
        no_authority(&executor);
    }
}

#[test]
fn canonical_payload_and_distinct_node_limits_include_the_generated_shell() {
    let mut executor = Executor::new();
    let arguments = (0..16_383)
        .map(|i| executor.ctx.terms.mk_var(format!("p{i}"), Sort::Bool))
        .collect::<Vec<_>>();
    let root = executor
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("and"), arguments, Sort::Bool);
    let negative = executor.ctx.terms.mk_not_raw(root);
    let overrides = Default::default();
    assert!(executor
        .ground_surface_render_budget(&[root], &overrides)
        .is_some());
    assert!(executor
        .ground_surface_render_budget(&[root, negative], &overrides)
        .is_none());
    no_authority(&executor);

    let mut executor = Executor::new();
    let variable = executor.ctx.terms.mk_var("wide", Sort::bitvec(u32::MAX));
    let constant = executor.ctx.terms.mk_bitvec(0.into(), u32::MAX);
    let root = executor.ctx.terms.mk_app(
        ay_core::Symbol::named("="),
        [variable, constant],
        Sort::Bool,
    );
    let negative = executor.ctx.terms.mk_not_raw(root);
    assert!(
        !executor.early_ground_memory_terms_print_faithfully(&[root, negative]),
        "reject before the formatter could allocate an enormous literal"
    );
    no_authority(&executor);
}

#[test]
fn expanded_output_counts_override_multiplicity_and_one_aggregate_pair_cap() {
    use crate::executor::proof_repair::proof_trust_surgery_surface_audit::render_roots_have_bounded_payload;
    let mut executor = Executor::new();
    let leaf = executor.ctx.terms.mk_var("leaf", Sort::Bool);
    let root = executor
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("and"), vec![leaf; 32], Sort::Bool);
    let negative = executor.ctx.terms.mk_not_raw(root);
    let prefix = "(and ";
    let suffix = "true true)";
    let text = format!(
        "{prefix}{}{suffix}",
        " ".repeat(128 * 1024 - prefix.len() - suffix.len())
    );
    assert_eq!(text.len(), 128 * 1024);
    ay_frontend::parse(&format!("(assert {text})")).expect("valid bounded Bool override text");
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(leaf, text);
    // All atomic payload and unique-map screens pass. Each standalone output
    // fits, but the two real outputs together exceed the unchanged 8 MiB cap.
    assert!(render_roots_have_bounded_payload(
        &executor.ctx.terms,
        &[root, negative],
        16_384,
        8 * 1024 * 1024
    ));
    assert!(executor
        .ground_surface_render_budget(&[root], &overrides)
        .is_some());
    assert!(executor
        .ground_surface_render_budget(&[negative], &overrides)
        .is_some());
    assert!(executor
        .ground_surface_render_budget(&[root, negative], &overrides)
        .is_none());
    let repeated =
        executor
            .ctx
            .terms
            .mk_app(ay_core::Symbol::named("and"), vec![leaf; 128], Sort::Bool);
    assert!(executor
        .ground_surface_render_budget(&[repeated], &overrides)
        .is_none());
    executor.last_proof_term_overrides = Some(overrides);
    assert!(!executor.early_ground_memory_terms_print_faithfully(&[root, negative]));
    no_authority(&executor);
}
