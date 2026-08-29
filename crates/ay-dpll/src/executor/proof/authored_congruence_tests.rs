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
fn duplicate_native_identity_rows_keep_assume_surface_authority() {
    let mut executor = Executor::new();
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    let native_source =
        || FrontendTerm::Symbol(crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.to_string());
    executor
        .ctx
        .add_assertion_with_parsed(canonical, native_source());
    executor
        .ctx
        .add_assertion_with_parsed(canonical, native_source());
    executor
        .ctx
        .add_assertion_with_parsed(negated, native_source());

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.last_proof_term_overrides = None;
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        executor.last_proof_term_overrides.is_none(),
        "native identity rows must not invent a surface override"
    );
    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "repeated identity-only rows are presentation-equivalent, not ambiguous"
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

/// An assumption-only query authors no `(assert ...)`, so the source ledger
/// this pass aligns against is EMPTY BY CONSTRUCTION. Nothing to restore is
/// not a failure to restore something: `proof_export_scope_assertions`
/// already folds `last_assumptions` into the authored premise scope, and
/// `unsat_query_has_literal_false_assumption_source` still reports exact
/// source authority for `(check-sat-assuming (false))`. This pass must agree,
/// or a certified assumption-only refutation publishes no proof at all.
#[test]
fn current_query_assumption_roots_need_no_authored_assertion_row() {
    let mut executor = Executor::new();
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor.last_assumptions = Some(vec![canonical, negated]);
    assert!(executor.ctx.assertions_parsed().is_empty());
    assert!(executor.ctx.assertions.is_empty());

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.last_proof_term_overrides = None;
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "an authored query assumption is a premise, not a missing source row"
    );
    assert!(
        executor.last_proof_term_overrides.is_none(),
        "an assumption literal has no `(assert ...)` text, so this pass must \
         neither invent a spelling for it nor remove one"
    );
}

/// The assumption arm admits exactly the terms the CURRENT query bound, and
/// nothing else. A reachable `assume` that no source row, no paired ledger and
/// no bound assumption accounts for still fails closed.
#[test]
fn an_assumption_ledger_admits_only_the_roots_it_actually_holds() {
    let mut executor = Executor::new();
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor.last_assumptions = Some(vec![canonical]);

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        executor.last_unsat_proof_reconstruction_suppressed,
        "an unaccounted reachable assume must still suppress publication"
    );
}

/// A surface override re-spells ONE `TermId` for the WHOLE document. The
/// printer confines an authored assume spelling to its own step only when it
/// can DERIVE `source = canonical` — a comparison reversal, a numeric
/// multiplication reorder, or `cong` under the canonical root's own operator.
/// `(distinct i j)` over the canonical `(not (= i j))` reaches none of those:
/// the entry would leak into every printed occurrence, printing one side of a
/// resolution as an opaque `distinct` atom and the other as `(= i j)`.
///
/// Withholding is the correct answer, not suppression: the root keeps the
/// canonical spelling the strict checker validated, and a confinable sibling
/// root in the same document still gets its authored text.
#[test]
fn an_unconfinable_authored_spelling_is_withheld_not_suppressed() {
    let mut executor = Executor::new();
    let i = executor.ctx.terms.mk_var("i", Sort::Int);
    let j = executor.ctx.terms.mk_var("j", Sort::Int);
    let equality = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [i, j], Sort::Bool);
    let disequality = executor.ctx.terms.mk_not_raw(equality);
    executor
        .ctx
        .add_assertion_with_parsed(equality, parsed_assertion("(assert (= i j))"));
    executor
        .ctx
        .add_assertion_with_parsed(disequality, parsed_assertion("(assert (distinct i j))"));

    let mut proof = Proof::new();
    let positive = proof.add_assume(equality, None);
    let negative = proof.add_assume(disequality, None);
    proof.add_resolution(Vec::new(), equality, positive, negative);
    executor.last_proof_term_overrides = None;
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "a spelling this pass declines to install is not a publication failure"
    );
    let overrides = executor
        .last_proof_term_overrides
        .as_ref()
        .expect("the confinable sibling root still records its authored text");
    assert_eq!(
        overrides.get(&equality).map(String::as_str),
        Some("(= i j)"),
        "a root whose authored head matches the canonical head still restores"
    );
    assert_eq!(
        overrides.get(&disequality),
        None,
        "`distinct` over a negated-equality root cannot be confined to its assume"
    );
}

/// The counterpart of `derived_rebuild_authority_is_not_exact_raw_problem_provenance`:
/// a promoter that rebuilds a parsed top-level assertion itself must record
/// BOTH ledgers, because `raw_intern_surface` fails closed on the shapes those
/// promoters exist for (an elaboration-folded datatype selector application
/// has no live identity to authenticate) and so mints no row of its own.
/// Recording only proof authority is the drift that silently suppresses a
/// certified refutation.
#[test]
fn a_promoted_raw_problem_assertion_is_admitted_by_both_ledgers() {
    let mut executor = Executor::new();
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (>= (f b) 0))"));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (<= 0 (f b))))"));

    let promoted = executor
        .ctx
        .terms
        .mk_var("promoted_raw_problem_assertion", Sort::Bool);
    let not_promoted = executor.ctx.terms.mk_not_raw(promoted);
    executor.record_raw_authored_problem_assertion(promoted);
    executor.record_raw_authored_problem_assertion(not_promoted);

    let mut proof = Proof::new();
    let positive = proof.add_assume(promoted, None);
    let negative = proof.add_assume(not_promoted, None);
    proof.add_resolution(Vec::new(), promoted, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "a raw re-intern of a parsed problem assertion carries exact provenance"
    );
}

/// A COMPOSITE fold result is NOT the atom arm's business, and withholding it
/// must remove nothing.
///
/// `authored_surface_is_assume_confinable` answers `true` unconditionally for a
/// root with no top-level operator. The justification for that arm used to
/// claim `collect_root_surface_term_override` "already owns" the folded
/// `(and p ...)` -> `p` case; it owns the ATOM case only, because
/// `authored_conjunction_folded_onto_variable` exempts a VARIABLE fold result
/// and nothing else. `(and (not p) (= x x))` interns as the composite
/// `(not p)`, whose canonical head `not` differs from the authored `and`, so
/// this pass withholds where it used to re-install.
///
/// Withholding means exactly that: nothing installed AND nothing removed. The
/// authored conjunction an EARLIER pass recorded for that root is what
/// `--test group_proofs`
/// `folded_authored_conjunction_assume_is_the_problem_assertion` reads back out
/// of the published document, so clearing it here would print the bare folded
/// term as an `assume` that is no assertion of the problem.
#[test]
fn a_composite_fold_root_keeps_the_spelling_an_earlier_pass_installed() {
    let mut executor = Executor::new();
    let p = executor.ctx.terms.mk_var("p", Sort::Bool);
    let not_p = executor.ctx.terms.mk_not_raw(p);
    executor
        .ctx
        .add_assertion_with_parsed(not_p, parsed_assertion("(assert (and (not p) (= x x)))"));
    executor
        .ctx
        .add_assertion_with_parsed(p, parsed_assertion("(assert p)"));

    let mut overrides = DetHashMap::default();
    overrides.insert(not_p, "(and (not p) (= x x))".to_string());
    executor.last_proof_term_overrides = Some(overrides);

    let mut proof = Proof::new();
    let negative = proof.add_assume(not_p, None);
    let positive = proof.add_assume(p, None);
    proof.add_resolution(Vec::new(), p, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "a composite fold result is a presentation decision, not a provenance failure"
    );
    assert_eq!(
        executor
            .last_proof_term_overrides
            .as_ref()
            .and_then(|overrides| overrides.get(&not_p))
            .map(String::as_str),
        Some("(and (not p) (= x x))"),
        "the authored conjunction an earlier pass installed must survive untouched"
    );
}

/// The other half of the same fact: with no earlier entry to preserve, a
/// composite fold root gets NOTHING from this pass. It is withheld, never
/// installed and never a suppression, and a confinable sibling root in the
/// same document still restores its authored text.
///
/// Measured end to end on `(assert (and (= a b) (= x x)))` +
/// `(assert (not (= a b)))`: the published document is
/// `(assume t0 (= a b))` ... `(cl)`, strictly Verified with trust=0 and
/// hole=0, and the exported problem transport carries `(assert (= a b))` as an
/// assertion of its own.
#[test]
fn a_composite_fold_root_installs_nothing_when_no_earlier_pass_did() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Int);
    let b = executor.ctx.terms.mk_var("b", Sort::Int);
    let equality = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [a, b], Sort::Bool);
    let disequality = executor.ctx.terms.mk_not_raw(equality);
    executor
        .ctx
        .add_assertion_with_parsed(equality, parsed_assertion("(assert (and (= a b) (= x x)))"));
    executor
        .ctx
        .add_assertion_with_parsed(disequality, parsed_assertion("(assert (not (= a b)))"));

    let mut proof = Proof::new();
    let positive = proof.add_assume(equality, None);
    let negative = proof.add_assume(disequality, None);
    proof.add_resolution(Vec::new(), equality, positive, negative);
    executor.last_proof_term_overrides = None;
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "a spelling this pass declines to install is not a publication failure"
    );
    let overrides = executor
        .last_proof_term_overrides
        .as_ref()
        .expect("the confinable sibling root still records its authored text");
    assert_eq!(
        overrides.get(&equality),
        None,
        "an authored `and` over a folded `=` root is not installed by this pass"
    );
    assert_eq!(
        overrides.get(&disequality).map(String::as_str),
        Some("(not (= a b))"),
        "a root whose authored head matches the canonical head still restores"
    );
}

/// The current query's assumption ledger is folded into a set, so it carries
/// the same row cap every other ledger this pass materializes does — and that
/// cap scopes THE ARM, never the document. A query with more assumptions than
/// the cap whose reachable roots all resolve through the SOURCE ledger keeps
/// publishing, exactly as it did before the assumption arm existed. A cap that
/// suppressed here would be a brand-new certified-but-unpublished path, which
/// is the defect this whole pass is being repaired for.
#[test]
fn an_over_cap_assumption_ledger_still_publishes_a_source_owned_document() {
    let mut executor = Executor::new();
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (>= (f b) 0))"));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (<= 0 (f b))))"));
    executor.last_assumptions = Some(vec![
        canonical;
        support::MAX_AUTHORED_ORIGINAL_INDEX_ROWS + 1
    ]);

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.last_proof_term_overrides = None;
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "an unmeterable assumption ledger must not suppress a document whose \
         roots the source ledger already accounts for"
    );
    assert_eq!(
        executor
            .last_proof_term_overrides
            .as_ref()
            .and_then(|overrides| overrides.get(&canonical))
            .map(String::as_str),
        Some("(>= (f b) 0)"),
        "the authored spelling is still restored"
    );
}

/// ...and over the cap the ARM is genuinely unavailable: the same two roots
/// `current_query_assumption_roots_need_no_authored_assertion_row` admits from
/// a small ledger fail closed once the ledger is too large to meter. The bound
/// is pinned in both directions, so neither dropping it nor widening it to the
/// whole function is silently equivalent.
#[test]
fn an_over_cap_assumption_ledger_withholds_the_assumption_arm() {
    let mut executor = Executor::new();
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    let mut assumptions = vec![canonical; support::MAX_AUTHORED_ORIGINAL_INDEX_ROWS];
    assumptions.push(negated);
    executor.last_assumptions = Some(assumptions);
    assert!(executor.ctx.assertions_parsed().is_empty());

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        executor.last_unsat_proof_reconstruction_suppressed,
        "over the cap the assumption arm has no members, so a root only it \
         could have accounted for must still fail closed"
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
