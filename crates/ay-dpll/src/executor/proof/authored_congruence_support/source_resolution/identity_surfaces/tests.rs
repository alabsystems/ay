// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{AletheRule, Sort, Symbol};
use ay_frontend::command::Command;

fn parsed(surface: &str) -> FrontendTerm {
    let commands = ay_frontend::parse(&format!("(assert {surface})")).unwrap();
    let [Command::Assert(term)] = commands.as_slice() else {
        panic!("one assertion expected");
    };
    term.clone()
}

fn add_identity(executor: &mut Executor, root: TermId) -> String {
    let surface = ay_proof::format_term_alethe(&executor.ctx.terms, root);
    executor
        .ctx
        .add_assertion_with_parsed(root, parsed(&surface));
    surface
}

fn contradiction(proof: &mut Proof, root: TermId, negative: TermId) {
    let positive = proof.add_assume(root, None);
    let negative = proof.add_assume(negative, None);
    proof.add_resolution(vec![], root, positive, negative);
}

fn declared_terms() -> (Executor, TermId, TermId, TermId) {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    executor
        .execute_all(
            &ay_frontend::parse("(declare-const x Int) (declare-fun f (Int) Int)").unwrap(),
        )
        .unwrap();
    let child = executor
        .ctx
        .elaborate_surface_subterm(&parsed("(f x)"))
        .unwrap();
    let zero = executor.ctx.terms.mk_int(0.into());
    let root = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [child, zero], Sort::Bool);
    let negative = executor.ctx.terms.mk_not_raw(root);
    (executor, root, negative, child)
}

fn fixture() -> (Executor, TermId, TermId, TermId, Proof) {
    let (mut executor, root, negative, child) = declared_terms();
    add_identity(&mut executor, root);
    add_identity(&mut executor, negative);
    let mut proof = Proof::new();
    contradiction(&mut proof, root, negative);
    (executor, root, negative, child, proof)
}

#[test]
fn identity_assumes_pin_their_whole_source_without_erasing_child_spellings() {
    let (mut executor, root, negative, child, proof) = fixture();
    let canonical = ay_proof::format_term_alethe(&executor.ctx.terms, root);
    let negative_canonical = ay_proof::format_term_alethe(&executor.ctx.terms, negative);
    let child_surface = "(+ (f x) 0)".to_string();
    let mut overrides = DetHashMap::default();
    overrides.insert(child, child_surface.clone());
    // This is the actual prior failure: no stale ROOT entry is needed.
    assert!(!overrides.contains_key(&root));
    assert_ne!(
        ay_proof::format_term_alethe_with_overrides(&executor.ctx.terms, root, &overrides),
        canonical
    );
    executor.last_proof_term_overrides = Some(overrides);
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    executor.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    let after = executor.last_proof_term_overrides.as_ref().unwrap();
    assert_eq!(after.get(&child), Some(&child_surface));
    assert_eq!(after.get(&root), Some(&canonical));
    assert_eq!(after.get(&negative), Some(&negative_canonical));
    assert_eq!(
        ay_proof::format_term_alethe_with_overrides(&executor.ctx.terms, child, after),
        child_surface
    );
    let scope = executor.ctx.assertions.clone();
    let wire = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &executor.ctx.terms,
        &scope,
        Some(after),
    )
    .unwrap();
    assert!(wire.contains(&format!("(assume t0 {canonical})")), "{wire}");
    assert!(
        wire.contains(&format!("(assume t1 {negative_canonical})")),
        "{wire}"
    );
    assert!(!wire.contains(":rule hole"));
    assert!(!wire.contains(":rule trust"));
    // This source-bound printer regression does not claim external verification.
}

#[test]
fn a_later_parsed_child_is_considered_before_identity_roots_are_sealed() {
    let (mut executor, child, not_child, _) = declared_terms();
    // Only the deliberately noncanonical child row authenticates its spelling.
    let flag = executor.ctx.terms.mk_var("flag", Sort::Bool);
    let parent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [child, flag], Sort::Bool);
    let not_parent = executor.ctx.terms.mk_not_raw(parent);
    let canonical = add_identity(&mut executor, parent);
    add_identity(&mut executor, not_parent);
    executor
        .ctx
        .add_assertion_with_parsed(child, parsed("(= (f x) (+ 0 0))"));
    add_identity(&mut executor, not_child);
    let mut proof = Proof::new();
    contradiction(&mut proof, parent, not_parent);
    contradiction(&mut proof, child, not_child);
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    executor.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    let overrides = executor.last_proof_term_overrides.as_ref().unwrap();
    assert_eq!(
        overrides.get(&child).map(String::as_str),
        Some("(= (f x) (+ 0 0))")
    );
    assert_eq!(overrides.get(&parent), Some(&canonical));
    assert_eq!(
        ay_proof::format_term_alethe_with_overrides(&executor.ctx.terms, parent, overrides),
        canonical
    );
}

#[test]
fn final_forall_instance_spellings_are_included_in_the_identity_seal() {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    executor
        .execute_all(
            &ay_frontend::parse(
                "(declare-const c Int) (declare-const p Bool) (declare-fun f (Int) Int) \
         (assert (forall ((x Int)) (>= (f x) 0)))",
            )
            .unwrap(),
        )
        .unwrap();
    let quantifier = executor.ctx.assertions[0];
    let instance = executor
        .ctx
        .elaborate_surface_subterm(&parsed("(<= 0 (f c))"))
        .unwrap();
    let flag = executor
        .ctx
        .elaborate_surface_subterm(&parsed("p"))
        .unwrap();
    let parent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), [instance, flag], Sort::Bool);
    let not_parent = executor.ctx.terms.mk_not_raw(parent);
    let not_forall = executor.ctx.terms.mk_not_raw(quantifier);
    let canonical = add_identity(&mut executor, parent);
    add_identity(&mut executor, not_parent);
    add_identity(&mut executor, not_forall);
    let witness = executor
        .ctx
        .elaborate_surface_subterm(&parsed("c"))
        .unwrap();
    let implication =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("or"), [not_forall, instance], Sort::Bool);
    let mut proof = Proof::new();
    contradiction(&mut proof, parent, not_parent);
    contradiction(&mut proof, quantifier, not_forall);
    proof.add_rule_step(
        AletheRule::ForallInst,
        vec![implication],
        vec![],
        vec![witness],
    );
    contradiction(&mut proof, parent, not_parent);
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    executor.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    let overrides = executor.last_proof_term_overrides.as_ref().unwrap();
    assert_eq!(
        overrides.get(&instance).map(String::as_str),
        Some("(>= (f c) 0)")
    );
    assert_eq!(overrides.get(&parent), Some(&canonical));
    assert_eq!(
        ay_proof::format_term_alethe_with_overrides(&executor.ctx.terms, parent, overrides),
        canonical
    );
}

#[test]
fn no_override_and_stale_root_only_cases_keep_the_existing_fast_path() {
    let (mut executor, root, _, _, proof) = fixture();
    executor.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(executor.last_proof_term_overrides.is_none());
    let mut stale = DetHashMap::default();
    stale.insert(root, "(= (+ (f x) 0) 0)".to_string());
    executor.last_proof_term_overrides = Some(stale);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(executor
        .last_proof_term_overrides
        .as_ref()
        .unwrap()
        .is_empty());
    // No rendering is needed for an empty source map, including the paired
    // raw-source lane whose identity roots intentionally bypass rendering.
    let seed = executor.ctx.terms.mk_var("deep", Sort::Int);
    let mut deep = seed;
    for _ in 0..257 {
        deep = executor
            .ctx
            .terms
            .mk_app(Symbol::named("walk"), [deep], Sort::Int);
    }
    let mut empty = DetHashMap::default();
    assert_eq!(
        executor.seal_authored_identity_surfaces(&[deep], &mut empty),
        Some(false)
    );
    assert!(empty.is_empty());
}

#[test]
fn real_later_datatype_merge_preserves_source_pins_and_unrelated_fields() {
    let (mut executor, root, _, child, proof) = fixture();
    executor
        .execute_all(
            &ay_frontend::parse(
                "(declare-datatypes ((Rec 0)) (((mk (left Int) (right Int))))) \
         (declare-const s Rec)",
            )
            .unwrap(),
        )
        .unwrap();
    let fields = executor.ctx.dt_field_surface_overrides();
    assert!(fields.values().any(|surface| surface == "(left s)"));
    let mut overrides = DetHashMap::default();
    overrides.insert(child, "(+ (f x) 0)".to_string());
    executor.last_proof_term_overrides = Some(overrides);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    let merged = executor.proof_export_term_overrides().unwrap();
    for (field, surface) in fields {
        assert_eq!(merged.get(&field), Some(&surface));
        assert_eq!(
            ay_proof::format_term_alethe_with_overrides(&executor.ctx.terms, field, &merged),
            surface
        );
    }
    assert_eq!(
        ay_proof::format_term_alethe_with_overrides(&executor.ctx.terms, root, &merged),
        ay_proof::format_term_alethe(&executor.ctx.terms, root)
    );
    // This deliberately tests unrelated datatype fields, not canonicalizing
    // an identity root containing an invented field or later printer channels.
}

#[test]
fn render_refusal_is_transactional_and_both_batches_share_one_work_cap() {
    let (mut executor, root, _, child, _) = fixture();
    let mut overrides = DetHashMap::default();
    overrides.insert(child, "(+ (f x) 0)".to_string());
    let before = overrides.clone();
    let mut deep = child;
    for _ in 0..257 {
        deep = executor
            .ctx
            .terms
            .mk_app(Symbol::named("walk"), [deep], Sort::Int);
    }
    assert_eq!(
        executor.seal_authored_identity_surfaces(&[root, deep], &mut overrides),
        None
    );
    assert_eq!(overrides, before, "no earlier root may be partially sealed");
    let wide = executor.ctx.terms.mk_bitvec(0.into(), 9_000_000);
    assert_eq!(
        executor.seal_authored_identity_surfaces(&[root, wide], &mut overrides),
        None
    );
    assert_eq!(overrides, before);
    let seed = executor.ctx.terms.mk_var("z".repeat(32), Sort::Int);
    let mut shared = seed;
    for _ in 0..4 {
        shared = executor
            .ctx
            .terms
            .mk_app(Symbol::named("dup"), [shared, shared], Sort::Int);
    }
    assert!(canonical_render::render(&executor.ctx.terms, [shared]).is_some());
    let empty = DetHashMap::default();
    let (_, _, actual_work) =
        ay_proof::format_terms_alethe_with_overrides_and_canonical_bounded_with_work(
            &executor.ctx.terms,
            &[shared],
            &empty,
            &[shared],
            u64::MAX,
        )
        .unwrap();
    // Sharing changes printer cost, so derive the boundary from real work,
    // not an assumed exponential number of copied subterms.
    let budget = actual_work.checked_sub(1).unwrap();
    assert!(
        ay_proof::format_terms_alethe_with_overrides_bounded(
            &executor.ctx.terms,
            &[shared],
            &empty,
            budget,
        )
        .is_ok(),
        "one batch must fit the measured shared boundary"
    );
    assert!(
        ay_proof::format_terms_alethe_with_overrides_and_canonical_bounded(
            &executor.ctx.terms,
            &[shared],
            &empty,
            &[shared],
            budget,
        )
        .is_err(),
        "two individually bounded batches must not each reset the cap"
    );
}

#[test]
fn final_map_capacity_refusal_does_not_publish_partial_identity_pins() {
    let (mut executor, root, negative, child, _) = fixture();
    let mut overrides = DetHashMap::default();
    overrides.insert(child, "(+ (f x) 0)".to_string());
    for index in 1..8192 {
        let unrelated = executor
            .ctx
            .terms
            .mk_var(format!("unrelated_{index}"), Sort::Int);
        overrides.insert(unrelated, "0".to_string());
    }
    assert!(proof_surface_syntax::surface_override_map_is_bounded(
        &overrides
    ));
    let before = overrides.clone();
    assert_eq!(
        executor.seal_authored_identity_surfaces(&[root, negative], &mut overrides),
        None
    );
    assert_eq!(overrides, before);
    assert!(!overrides.contains_key(&root));
    assert!(!overrides.contains_key(&negative));
}

/// A root the RAW-source ledgers authenticate keeps its authored descendant
/// spellings — its grant is about the TERM, never about the text.
///
/// This is the fold-to-false shape: the elaborated assertion is a constant, so
/// no problem row owns the root, and the promoter raw-rebuilds the premise
/// while `collect_subterm_surface_overrides` restores the AUTHOR's spelling on
/// the descendants. `(_ bv4 8)` and `#b00000100` are one constant to every
/// parser, so the effective root rendering is faithful; sealing it to the
/// canonical text would publish an `assume` the problem never wrote AND leave
/// every later step spelling the same conjunct the other way, which is exactly
/// what the printer's `and_pos` surface guard declines.
#[test]
fn a_raw_ledger_root_keeps_its_authored_descendant_spellings() {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    executor
        .execute_all(&ay_frontend::parse("(declare-const b (_ BitVec 8))").unwrap())
        .unwrap();
    let authored = "(bvult b (_ bv4 8))";
    let child = executor
        .ctx
        .elaborate_surface_subterm(&parsed(authored))
        .unwrap();
    let flag = executor.ctx.terms.mk_var("raw_ledger_flag", Sort::Bool);
    let root = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [child, flag], Sort::Bool);
    let negative = executor.ctx.terms.mk_not_raw(root);
    // The problem's own rows are OTHER terms: the raw rebuild owns no row.
    let other = executor.ctx.terms.mk_var("raw_ledger_row", Sort::Bool);
    let not_other = executor.ctx.terms.mk_not_raw(other);
    add_identity(&mut executor, other);
    add_identity(&mut executor, not_other);
    executor.last_proof_rebuild_originals = vec![root, negative];
    executor.last_proof_raw_original_assertions = vec![root, negative];

    let mut overrides = DetHashMap::default();
    overrides.insert(child, authored.to_string());
    let effective =
        ay_proof::format_term_alethe_with_overrides(&executor.ctx.terms, root, &overrides);
    assert_ne!(
        effective,
        ay_proof::format_term_alethe(&executor.ctx.terms, root),
        "the authored literal spelling must differ from the canonical one"
    );
    executor.last_proof_term_overrides = Some(overrides);

    let Ok(sources) = executor.resolve_reachable_authored_sources(&[root, negative]) else {
        panic!("the raw ledgers authenticate both roots");
    };
    assert!(
        sources
            .iter()
            .all(|source| source.canonical_row_root().is_none()),
        "a raw-ledger root authenticates no canonical text, so it is not sealable"
    );

    let mut proof = Proof::new();
    contradiction(&mut proof, root, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    let after = executor.last_proof_term_overrides.as_ref().unwrap();
    assert_eq!(after.get(&child), Some(&authored.to_string()));
    assert_eq!(
        after.get(&root),
        None,
        "a raw-ledger root must not be sealed"
    );
    assert_eq!(
        ay_proof::format_term_alethe_with_overrides(&executor.ctx.terms, root, after),
        effective
    );
}
