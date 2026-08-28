// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scope tests for the certified-reconstruction override purge.
//!
//! The purge exists so that one internal term cannot reach the Alethe printer
//! under two spellings. It must remove exactly the stale spellings the
//! committed proof would print — no more (an unrelated assertion keeps the
//! problem file's syntax) and no fewer (a spelling reached only through a
//! clause's SUBTERMS is exactly the one that collided), and only once the
//! strict checker has actually accepted the candidate.

use super::*;

use ay_core::kani_compat::DetHashMap;
use ay_frontend::command::{Command, Sort as FrontendSort};

fn declare_bv8(executor: &mut Executor, name: &str) -> TermId {
    executor
        .ctx
        .process_command(&Command::DeclareConst(
            name.to_string(),
            FrontendSort::Indexed(
                "BitVec".to_string(),
                vec![FrontendIndex::Numeral("8".to_string())],
            ),
        ))
        .expect("fixture declaration succeeds");
    executor
        .ctx
        .elaborate_surface_subterm(&FrontendTerm::Symbol(name.to_string()))
        .expect("declared fixture symbol elaborates")
}

/// `(= <var> #x10)` plus the surface spellings an ordinary export would have
/// collected for it and for its bitvector operand.
fn pinned_equality(executor: &mut Executor, name: &str) -> (TermId, TermId, TermId) {
    let var = declare_bv8(executor, name);
    let constant = executor.ctx.terms.mk_bitvec(BigInt::from(0x10), 8);
    let equality = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![var, constant], Sort::Bool);
    (equality, var, constant)
}

#[test]
fn purge_drops_only_the_spellings_the_certified_proof_prints() {
    let mut executor = Executor::new();
    let (printed_equality, printed_var, constant) = pinned_equality(&mut executor, "purge_printed");
    let (other_equality, other_var, _) = pinned_equality(&mut executor, "purge_untouched");

    let mut overrides = DetHashMap::default();
    overrides.insert(printed_equality, "(= purge_printed #x10)".to_string());
    overrides.insert(printed_var, "(bvadd purge_printed #x00)".to_string());
    overrides.insert(constant, "#x10".to_string());
    overrides.insert(other_equality, "(= purge_untouched #x10)".to_string());
    overrides.insert(other_var, "(bvadd purge_untouched #x00)".to_string());
    executor.last_proof_term_overrides = Some(overrides);

    let mut candidate = Proof::new();
    let _ = candidate.add_assume(printed_equality, None);
    executor.purge_surface_overrides_for_certified_proof(&candidate);

    let after = executor
        .last_proof_term_overrides
        .clone()
        .expect("the table survives the purge");
    // The clause literal itself...
    assert!(!after.contains_key(&printed_equality));
    // ...and every operand reached through it: the collision the printer
    // reports is between an enclosing spelling and a separately printed
    // SUBTERM, so stopping at the literal would leave it in place.
    assert!(!after.contains_key(&printed_var));
    assert!(!after.contains_key(&constant));
    // An assertion this reconstruction does not print keeps the problem
    // file's own syntax; the purge is not a blanket `= None`.
    assert_eq!(
        after.get(&other_equality),
        Some(&"(= purge_untouched #x10)".to_string())
    );
    assert_eq!(
        after.get(&other_var),
        Some(&"(bvadd purge_untouched #x00)".to_string())
    );
}

#[test]
fn purge_leaves_a_document_that_has_no_surface_spellings_alone() {
    let mut executor = Executor::new();
    let (equality, _, _) = pinned_equality(&mut executor, "purge_no_table");
    executor.last_proof_term_overrides = None;

    let mut candidate = Proof::new();
    let _ = candidate.add_assume(equality, None);
    executor.purge_surface_overrides_for_certified_proof(&candidate);

    assert!(
        executor.last_proof_term_overrides.is_none(),
        "a document with no surface table already prints canonically"
    );
}

#[test]
fn a_candidate_the_strict_gate_rejects_purges_nothing() {
    let mut executor = Executor::new();
    let (equality, var, _) = pinned_equality(&mut executor, "purge_uncommitted");

    let mut overrides = DetHashMap::default();
    overrides.insert(equality, "(= purge_uncommitted #x10)".to_string());
    overrides.insert(var, "(bvadd purge_uncommitted #x00)".to_string());
    executor.last_proof_term_overrides = Some(overrides.clone());

    // Derives nothing, so `commit_if_strictly_checked` must decline.
    let mut candidate = Proof::new();
    let _ = candidate.add_assume(equality, None);
    let mut proof = Proof::new();
    let _ = proof.add_assume(equality, None);

    assert!(!executor.commit_if_strictly_checked(&mut proof, candidate, &[equality]));
    assert_eq!(
        executor.last_proof_term_overrides,
        Some(overrides),
        "the export table may only change for a proof the strict checker accepted"
    );
}

fn parsed_assertion(source: &str) -> FrontendTerm {
    let commands = ay_frontend::parse(source).expect("assertion fixture parses");
    let [Command::Assert(term)] = commands.as_slice() else {
        panic!("fixture must contain one assertion")
    };
    term.clone()
}

fn comparison_surface_fixture(executor: &mut Executor) -> (TermId, TermId) {
    let b = executor.ctx.terms.mk_var("b", Sort::Int);
    let f_b = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [b], Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let canonical = executor
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [zero, f_b], Sort::Bool);
    let negated = executor.ctx.terms.mk_not_raw(canonical);
    (canonical, negated)
}

#[test]
fn reachable_authored_assume_restores_its_exact_unique_source_index() {
    let mut executor = Executor::new();
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (>= (f b) 0))"));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (<= 0 (f b))))"));

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.last_proof_term_overrides = None;
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert_eq!(
        executor
            .last_proof_term_overrides
            .as_ref()
            .and_then(|overrides| overrides.get(&canonical))
            .map(String::as_str),
        Some("(>= (f b) 0)")
    );
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
}

#[test]
fn duplicate_authored_root_indices_decline_assume_surface_restoration() {
    let mut executor = Executor::new();
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (>= (f b) 0))"));
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (<= 0 (f b)))"));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (<= 0 (f b))))"));

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.last_proof_term_overrides = None;
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        executor.last_proof_term_overrides.is_none(),
        "an ambiguous canonical root must not pick one authored spelling"
    );
    assert!(
        executor.last_unsat_proof_reconstruction_suppressed,
        "ambiguous source provenance must suppress external proof publication"
    );
}

#[test]
fn derived_rebuild_authority_is_not_exact_raw_problem_provenance() {
    let mut executor = Executor::new();
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (>= (f b) 0))"));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (<= 0 (f b))))"));

    let derived = executor
        .ctx
        .terms
        .mk_var("derived_repair_premise", Sort::Bool);
    let not_derived = executor.ctx.terms.mk_not_raw(derived);
    executor.record_rebuilt_authored_proof_premise(derived);
    executor.record_rebuilt_authored_proof_premise(not_derived);

    let mut proof = Proof::new();
    let positive = proof.add_assume(derived, None);
    let negative = proof.add_assume(not_derived, None);
    proof.add_resolution(Vec::new(), derived, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        executor.last_unsat_proof_reconstruction_suppressed,
        "general rebuild authority must not masquerade as a top-level problem-file premise"
    );
}

#[test]
fn anchor_edges_retain_reachable_authored_assume_provenance() {
    let mut executor = Executor::new();
    let (canonical, _) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (>= (f b) 0))"));

    let mut proof = Proof::new();
    let assumed = proof.add_assume(canonical, None);
    let anchor = proof.add_step(ProofStep::Anchor {
        end_step: assumed,
        variables: Vec::new(),
    });
    proof.add_rule_step(AletheRule::Trust, Vec::new(), vec![anchor], Vec::new());
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert_eq!(
        executor
            .last_proof_term_overrides
            .as_ref()
            .and_then(|overrides| overrides.get(&canonical))
            .map(String::as_str),
        Some("(>= (f b) 0)")
    );
}

#[test]
fn malformed_anchor_premise_suppresses_restoration_atomically() {
    let mut executor = Executor::new();
    let (canonical, _) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (>= (f b) 0))"));

    let unrelated = executor
        .ctx
        .terms
        .mk_var("unrelated_surface_override", Sort::Bool);
    let mut overrides = DetHashMap::default();
    overrides.insert(unrelated, "unrelated_surface_override".to_string());
    executor.last_proof_term_overrides = Some(overrides.clone());

    let mut proof = Proof::new();
    let assumed = proof.add_assume(canonical, None);
    let malformed_anchor = proof.add_step(ProofStep::Anchor {
        end_step: ProofId(u32::MAX),
        variables: Vec::new(),
    });
    proof.add_rule_step(
        AletheRule::Trust,
        Vec::new(),
        vec![assumed, malformed_anchor],
        Vec::new(),
    );
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert_eq!(executor.last_proof_term_overrides, Some(overrides));
    assert!(
        executor.last_unsat_proof_reconstruction_suppressed,
        "an out-of-range anchor dependency must fail closed before any override is committed"
    );
}

#[test]
fn retention_off_has_no_external_surface_to_restore_or_suppress() {
    let mut executor = Executor::new();
    executor.ctx.set_retain_parsed_assertions(false);
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (>= (f b) 0))"));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (<= 0 (f b))))"));

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(executor.last_proof_term_overrides.is_none());
    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "canonical retention-off certification must keep native authority"
    );
}

#[test]
fn retention_off_cannot_bypass_an_explicit_external_proof_demand() {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    executor.ctx.set_retain_parsed_assertions(false);
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (>= (f b) 0))"));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (<= 0 (f b))))"));

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        executor.last_unsat_proof_reconstruction_suppressed,
        "an explicit proof request must not publish without its authored source ledger"
    );
}

#[test]
fn retained_but_empty_source_ledger_suppresses_external_publication() {
    let mut executor = Executor::new();
    executor.ctx.set_retain_parsed_assertions(false);
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (>= (f b) 0))"));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (<= 0 (f b))))"));
    assert!(executor.ctx.assertions_parsed().is_empty());
    // Turning retention back on does not retroactively recreate the missing
    // prefix. It changes this from intentional retention-off state into a
    // retained-but-misaligned ledger, which must never authenticate export.
    executor.ctx.set_retain_parsed_assertions(true);

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        executor.last_unsat_proof_reconstruction_suppressed,
        "an empty retained ledger beside nonempty authored roots is a publication failure"
    );
}

// ===========================================================================
// Authored-surface respelling
//
// The purge alone prints every operand from the term the checker accepted —
// internally consistent, but where elaboration FOLDED the source that is no
// longer the problem file's syntax, and Carcara matches `assume` against the
// original premises syntactically. The respelling moves the whole certified
// reconstruction onto the raw authored terms so both properties hold at once.
// These tests pin its scope: it fires only on a real fold, it never invents
// premise authority, and the document it produces has ONE spelling per term.
// ===========================================================================

/// The `(bvadd p #x00)` fold: `TermStore::mk_bvadd` hash-conses `x + 0` to `x`,
/// so the authored index and the certified read are one interned term.
const BVADD_FOLD_FIXTURE: &str = "(set-option :produce-proofs true)\n\
     (set-logic QF_ABV)\n\
     (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))\n\
     (declare-const p (_ BitVec 8))\n\
     (declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))\n\
     (assert (= mem2 (store mem (bvadd p #x00) #x10)))\n\
     (assert (= (select mem2 (bvadd p #x00)) #x20))\n\
     (check-sat)\n\
     (get-proof)";

#[test]
fn a_folded_authored_root_exports_with_the_problem_file_spelling() {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(BVADD_FOLD_FIXTURE).expect("the fold fixture parses");
    let outputs = executor
        .execute_all(&commands)
        .expect("the fold fixture executes");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "the cell just written with #x10 cannot read back #x20, got {outputs:?}"
    );
    let proof = outputs.last().expect("`(get-proof)` produces a document");

    // Carcara matches an `assume` against the original problem premises
    // SYNTACTICALLY, and it does not fold `(bvadd p #x00)`. Measured on
    // carcara 1.1.0, the canonical spelling was rejected outright with
    // "could not match term to any of the original problem premises".
    assert!(
        proof.contains("(assume t0 (= mem2 (store mem (bvadd p #b00000000) #b00010000)))"),
        "the assume must carry the problem file's own index spelling:\n{proof}"
    );
    assert!(
        proof.contains("(assume t7 (= (select mem2 (bvadd p #b00000000)) #b00100000))"),
        "every authored root must carry it, not just the first:\n{proof}"
    );
    // ...and ONE spelling per term: the ROW1 index must agree with the store's
    // index and with the reflexive congruence hypothesis, or Carcara's
    // `arrays_idx` / `eq_congruent` reject the very steps the assume unlocked.
    assert!(
        proof.contains(
            "(step t5 (cl (= (select (store mem (bvadd p #b00000000) #b00010000) \
             (bvadd p #b00000000)) #b00010000)) :rule arrays_idx)"
        ),
        "the ROW1 step must read the same index it wrote:\n{proof}"
    );
    assert!(
        !proof.contains("(select mem2 p)"),
        "no step may fall back to the folded spelling:\n{proof}"
    );
}

#[test]
fn respelling_declines_an_authored_root_elaboration_left_intact() {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(
        "(declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))\n\
         (declare-const p (_ BitVec 8))\n\
         (assert (= (select mem p) #x10))",
    )
    .expect("the fold-free fixture parses");
    executor
        .execute_all(&commands)
        .expect("the fold-free fixture executes");
    let root = executor.ctx.assertions[0];

    let mut candidate = Proof::new();
    let _ = candidate.add_assume(root, None);
    assert!(
        executor
            .respell_certified_proof_over_authored_surface(&candidate)
            .is_none(),
        "a root whose raw re-intern IS the canonical term has nothing to respell, \
         so the committed proof must stay exactly as the strict checker accepted it"
    );
}

/// Two authored roots that BOTH fold to the same canonical literal, plus a
/// hand-built refutation of them that the strict checker accepts on its own.
///
/// This is the smallest fixture on which the respelling actually runs to
/// completion, so the guards after the rewrite are reachable from a test.
/// Returns the executor, the canonical roots, their raw re-interns, and the
/// certified candidate.
fn folded_complementary_pair_fixture() -> (Executor, [TermId; 2], [TermId; 2], Proof) {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(
        "(declare-const p (_ BitVec 8))\n\
         (assert (= (bvadd p #x00) #x10))\n\
         (assert (not (= (bvadd p #x00) #x10)))",
    )
    .expect("the folded complementary fixture parses");
    executor
        .execute_all(&commands)
        .expect("the folded complementary fixture executes");

    let roots = [executor.ctx.assertions[0], executor.ctx.assertions[1]];
    let raws = {
        let parsed: Vec<FrontendTerm> = executor.ctx.assertions_parsed()[..2].to_vec();
        [
            executor
                .raw_intern_surface(&parsed[0])
                .expect("the positive spelling re-interns"),
            executor
                .raw_intern_surface(&parsed[1])
                .expect("the negated spelling re-interns"),
        ]
    };
    assert_ne!(raws[0], roots[0], "the fixture must actually fold");
    assert_ne!(raws[1], roots[1], "both spellings must fold");

    let mut candidate = Proof::new();
    let positive = candidate.add_assume(roots[0], None);
    let negative = candidate.add_assume(roots[1], None);
    candidate.add_resolution(Vec::new(), roots[0], positive, negative);
    (executor, roots, raws, candidate)
}

#[test]
fn respelling_declines_a_raw_reintern_the_premise_scope_has_not_admitted() {
    let (mut executor, roots, raws, candidate) = folded_complementary_pair_fixture();
    // The candidate itself is what the commit gate accepts today.
    assert!(Executor::proof_derives_empty_clause(&candidate));
    assert!(executor
        .check_proof_strict_with_datatypes(&candidate)
        .is_ok());
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &roots).is_ok(),
        "the canonical candidate assumes exactly the authored roots"
    );

    // The respelling REUSES the grant `rebuild_trust_leaf_proof_from_original_assertions`
    // records for the raw re-intern of every parsed original; it never mints
    // one. With no grant on record there is no authored premise to assume, so
    // it must decline rather than put an unadmitted term behind `assume`.
    executor.last_proof_rebuild_originals.clear();
    assert!(
        executor
            .respell_certified_proof_over_authored_surface(&candidate)
            .is_none(),
        "an unadmitted raw re-intern must never become an `assume`"
    );

    // Record exactly the grant that pass would have recorded, and the SAME
    // candidate respells — so the decline above was the authority check, not
    // an unrelated failure.
    for raw in raws {
        executor.record_rebuilt_authored_proof_premise(raw);
    }
    let respelled = executor
        .respell_certified_proof_over_authored_surface(&candidate)
        .expect("an admitted raw re-intern respells");
    assert!(
        matches!(respelled.steps[0], ProofStep::Assume(term) if term == raws[0]),
        "the respelled document assumes the problem file's own spelling"
    );
    assert!(matches!(respelled.steps[1], ProofStep::Assume(term) if term == raws[1]));
}

#[test]
fn respelling_refuses_a_rename_another_authored_assume_still_depends_on() {
    let mut executor = Executor::new();
    // Only the FIRST assertion folds. Respelling it maps `p` to
    // `(bvadd p #x00)`, which would rewrite the second assume into
    // `(not (= (bvadd p #x00) #x10))` — a term the problem file never wrote.
    let commands = ay_frontend::parse(
        "(declare-const p (_ BitVec 8))\n\
         (assert (= (bvadd p #x00) #x10))\n\
         (assert (not (= p #x10)))",
    )
    .expect("the mixed-spelling fixture parses");
    executor
        .execute_all(&commands)
        .expect("the mixed-spelling fixture executes");
    let roots = [executor.ctx.assertions[0], executor.ctx.assertions[1]];
    let raws: Vec<TermId> = executor.ctx.assertions_parsed()[..2]
        .to_vec()
        .iter()
        .map(|parsed| {
            executor
                .raw_intern_surface(parsed)
                .expect("both spellings re-intern")
        })
        .collect();
    for &raw in &raws {
        executor.record_rebuilt_authored_proof_premise(raw);
    }

    let mut candidate = Proof::new();
    let positive = candidate.add_assume(roots[0], None);
    let negative = candidate.add_assume(roots[1], None);
    candidate.add_resolution(Vec::new(), roots[0], positive, negative);
    assert!(Executor::proof_derives_empty_clause(&candidate));
    assert!(executor
        .check_proof_strict_with_datatypes(&candidate)
        .is_ok());

    // This is what `bound_override_respells_target` refuses as a PRINTING
    // decision. Here it is refused for a checkable reason instead: the
    // respelled proof would assume a non-problem term, and the gate the
    // respelling is put back through says so.
    assert!(
        executor
            .respell_certified_proof_over_authored_surface(&candidate)
            .is_none(),
        "a respelling may not rename a term a second authored assume spells plainly"
    );
}

#[test]
fn alignment_records_the_fold_point_and_refuses_two_spellings_for_one_term() {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(
        "(declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))\n\
         (declare-const p (_ BitVec 8))\n\
         (declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))\n\
         (assert (= mem2 (store mem (bvadd p #x00) #x10)))\n\
         (assert (= mem2 (store mem (bvsub p #x00) #x10)))",
    )
    .expect("the two-spelling fixture parses");
    executor
        .execute_all(&commands)
        .expect("the two-spelling fixture executes");

    let (first_root, second_root) = (executor.ctx.assertions[0], executor.ctx.assertions[1]);
    let (first_raw, second_raw) = {
        let first = executor.ctx.assertions_parsed()[0].clone();
        let second = executor.ctx.assertions_parsed()[1].clone();
        (
            executor
                .raw_intern_surface(&first)
                .expect("the first spelling re-interns"),
            executor
                .raw_intern_surface(&second)
                .expect("the second spelling re-interns"),
        )
    };
    let p = executor
        .ctx
        .terms
        .lookup("p")
        .expect("the index variable is interned");

    let mut surface = DetHashMap::default();
    let mut work = 4096usize;
    Executor::align_authored_surface_spelling(
        &executor.ctx.terms,
        first_root,
        first_raw,
        &mut surface,
        &mut work,
    )
    .expect("one authored root aligns with its own raw re-intern");
    // The lockstep walk descends the equality and the store, and stops exactly
    // where elaboration folded: the index.
    assert_eq!(
        surface.get(&p).copied(),
        Some(match executor.ctx.terms.get(first_raw) {
            TermData::App(_, args) => match executor.ctx.terms.get(args[1]) {
                TermData::App(_, store_args) => store_args[1],
                _ => panic!("the raw root is an equality over a raw store"),
            },
            _ => panic!("the raw root is an equality"),
        }),
        "the folded index must map to the authored sum"
    );

    // A second authored root that folds the SAME term to a DIFFERENT spelling
    // has no consistent respelling; alignment must fail closed rather than
    // pick one.
    assert!(
        Executor::align_authored_surface_spelling(
            &executor.ctx.terms,
            second_root,
            second_raw,
            &mut surface,
            &mut work,
        )
        .is_none(),
        "one term may not acquire two authored spellings"
    );
}
