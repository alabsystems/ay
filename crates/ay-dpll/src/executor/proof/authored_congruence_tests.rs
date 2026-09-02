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
fn duplicate_root_with_identity_row_uses_exact_canonical_surface() {
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
        "an exact canonical row needs no authored override"
    );
    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "a canonical source row authenticates the identity presentation"
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
/// canonical spelling the strict checker validated, and a sibling root in the
/// same document still publishes its authored text. The sibling here spells
/// its root canonically, so it publishes that text with NO table entry;
/// `a_withheld_root_does_not_cost_a_noncanonical_sibling_its_override` pins the
/// same non-interference for a sibling that genuinely needs one.
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
    // Two facts, where this used to pin one. `(assert (= i j))` already
    // spells its root exactly as the printer renders it, so it publishes that
    // authored text with no entry at all — and the ABSENCE is load bearing,
    // not incidental: `restored_authored_override_map` compares any entry it
    // holds for a root against whatever an earlier pass recorded there and
    // declines the WHOLE reconstruction on disagreement, so a redundant
    // identity entry is a live suppression risk for a root the problem file
    // spells canonically.
    assert!(
        executor.last_proof_term_overrides.is_none(),
        "neither root installs a spelling: one is withheld, the other is \
         already canonical"
    );
    assert_eq!(
        ay_proof::format_term_alethe(&executor.ctx.terms, equality),
        "(= i j)",
        "and the canonical text the sibling falls back to IS its authored spelling"
    );
    assert_eq!(
        ay_proof::format_term_alethe(&executor.ctx.terms, disequality),
        "(not (= i j))",
        "`distinct` over a negated-equality root cannot be confined to its \
         assume, so the withheld root keeps canonical text"
    );
}

/// The non-interference half of `an_unconfinable_authored_spelling_is_withheld_not_suppressed`,
/// with a sibling whose authored spelling is genuinely NOT the canonical one.
/// A root this pass withholds must not cost a sibling in the same document the
/// override it does need — withholding is per root, never per document.
#[test]
fn a_withheld_root_does_not_cost_a_noncanonical_sibling_its_override() {
    let mut executor = Executor::new();
    let i = executor.ctx.terms.mk_var("i", Sort::Int);
    let j = executor.ctx.terms.mk_var("j", Sort::Int);
    let equality = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [i, j], Sort::Bool);
    let disequality = executor.ctx.terms.mk_not_raw(equality);
    // Elaboration normalizes `(+ j 0)` away, so this row's spelling differs
    // from the canonical rendering while keeping the `=` head the printer
    // needs to confine it to its own `assume`.
    executor
        .ctx
        .add_assertion_with_parsed(equality, parsed_assertion("(assert (= i (+ j 0)))"));
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
        Some("(= i (+ j 0))"),
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
/// installed and never a suppression, and a sibling root in the same document
/// still publishes its authored text — here by falling back to canonical text
/// its own row spells exactly.
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
    // As above, two facts where this pinned one: nothing is installed for
    // EITHER root — the folded `and` is withheld, and `(assert (not (= a b)))`
    // already spells its root exactly as the printer renders it, so it
    // authenticates canonical text instead of re-deriving it as an entry that
    // an earlier pass's spelling could then collide with.
    assert!(
        executor.last_proof_term_overrides.is_none(),
        "an authored `and` over a folded `=` root is not installed by this \
         pass, and its sibling is already canonical"
    );
    assert_eq!(
        ay_proof::format_term_alethe(&executor.ctx.terms, disequality),
        "(not (= a b))",
        "and the canonical text the sibling falls back to IS its authored spelling"
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

/// Falling back from a narrowed preprocessing provenance ledger to Context's
/// immutable authored rows must not make every recovered row a proof premise.
/// The exact export scope remains the authority boundary.
#[test]
fn fallback_does_not_authorize_a_recovered_row_outside_the_exact_scope() {
    let mut executor = Executor::new();
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (>= (f b) 0))"));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (<= 0 (f b))))"));
    executor.proof_problem_assertion_provenance = Some(
        crate::executor::theories::solve_harness::ProofProblemAssertionProvenance {
            original_problem_assertions: vec![canonical],
            problem_assertions: vec![canonical],
            assertion_sources: Default::default(),
        },
    );

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        executor.last_unsat_proof_reconstruction_suppressed,
        "a recovered source row cannot widen the exact preprocessing/query scope"
    );
}

/// Equal row counts are not enough for fallback alignment. This creates the
/// smallest stale layout possible through Context's solver-facing APIs: a
/// transient parsed row occupies index zero, an authored row records index
/// one, then stack truncation leaves one row on each side but they are not the
/// same row. Zipping by length would lend the transient spelling to the
/// authored root.
#[test]
fn fallback_rejects_equal_length_but_misaligned_source_rows() {
    let mut executor = Executor::new();
    let transient = executor
        .ctx
        .terms
        .mk_var("transient_source_row", Sort::Bool);
    let authored = executor
        .ctx
        .terms
        .mk_var("authored_source_root", Sort::Bool);
    let not_authored = executor.ctx.terms.mk_not_raw(authored);
    executor.ctx.add_transient_assertion_with_parsed(
        transient,
        parsed_assertion("(assert transient_source_row)"),
    );
    executor
        .ctx
        .add_assertion_with_parsed(authored, parsed_assertion("(assert authored_source_root)"));
    executor.ctx.truncate_assertions(1);
    assert_eq!(executor.ctx.assertions_parsed().len(), 1);
    assert_eq!(executor.ctx.concrete_authored_assertion_terms().len(), 1);

    executor.proof_problem_assertion_provenance = Some(
        crate::executor::theories::solve_harness::ProofProblemAssertionProvenance {
            original_problem_assertions: Vec::new(),
            problem_assertions: vec![authored],
            assertion_sources: Default::default(),
        },
    );
    executor.last_assumptions = Some(vec![not_authored]);

    let mut proof = Proof::new();
    let positive = proof.add_assume(authored, None);
    let negative = proof.add_assume(not_authored, None);
    proof.add_resolution(Vec::new(), authored, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(
        executor.last_unsat_proof_reconstruction_suppressed,
        "fallback must validate the recorded parsed index, not only row counts"
    );
    assert!(
        executor.last_proof_term_overrides.is_none(),
        "the transient spelling must never be installed on the authored root"
    );
}

#[test]
fn fallback_scope_aggregate_cap_charges_rows_before_deduplication() {
    let fixture = |assumption_rows: usize| {
        let mut executor = Executor::new();
        let root = executor
            .ctx
            .terms
            .mk_var("fallback_scope_cap_root", Sort::Bool);
        let not_root = executor.ctx.terms.mk_not_raw(root);
        executor
            .ctx
            .add_assertion_with_parsed(root, parsed_assertion("(assert fallback_scope_cap_root)"));
        executor.proof_problem_assertion_provenance = Some(
            crate::executor::theories::solve_harness::ProofProblemAssertionProvenance {
                original_problem_assertions: Vec::new(),
                problem_assertions: vec![root],
                assertion_sources: Default::default(),
            },
        );
        executor.last_assumptions = Some(vec![not_root; assumption_rows]);
        let mut proof = Proof::new();
        let positive = proof.add_assume(root, None);
        let negative = proof.add_assume(not_root, None);
        proof.add_resolution(Vec::new(), root, positive, negative);
        (executor, proof)
    };

    let cap = support::MAX_AUTHORED_ORIGINAL_INDEX_ROWS;
    let (mut at_cap, proof) = fixture(cap - 1);
    at_cap.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(
        !at_cap.last_unsat_proof_reconstruction_suppressed,
        "problem row plus repeated assumptions at the aggregate cap remains admitted"
    );

    let (mut over_cap, proof) = fixture(cap);
    over_cap.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(
        over_cap.last_unsat_proof_reconstruction_suppressed,
        "repeated rows must be charged before set deduplication"
    );
}

fn expanded_let_source_fixture() -> (Executor, Proof, TermId, TermId, String) {
    let mut executor = Executor::new();
    let p = executor.ctx.terms.mk_var("expanded_let_p", Sort::Bool);
    let q = executor.ctx.terms.mk_var("expanded_let_q", Sort::Bool);
    let not_q = executor.ctx.terms.mk_not_raw(q);
    let root = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [p, not_q], Sort::Bool);
    let not_root = executor.ctx.terms.mk_not_raw(root);
    let source = parsed_assertion(
        "(assert (let ((expanded_alias expanded_let_p)) \
         (and expanded_alias (not expanded_let_q))))",
    );
    let source_surface = crate::executor::proof_surface_syntax::format_frontend_term(&source);
    executor.ctx.add_assertion_with_parsed(root, source);
    executor.last_assumptions = Some(vec![not_root]);
    executor.record_raw_authored_problem_assertion(root);
    executor
        .last_proof_expanded_let_sources
        .push((root, 0, source_surface.clone()));

    let mut proof = Proof::new();
    let positive = proof.add_assume(root, None);
    let negative = proof.add_assume(not_root, None);
    proof.add_resolution(Vec::new(), root, positive, negative);
    (executor, proof, root, not_root, source_surface)
}

/// Every ledger field is untrusted at consumption time. Pin the independent
/// index/type/text/expansion/override checks so a future producer refactor
/// cannot turn the repair ledger into source-spelling authority by itself.
#[test]
fn expanded_let_source_metadata_is_revalidated_atomically() {
    for corruption in 0..5 {
        let (mut executor, proof, root, not_root, _) = expanded_let_source_fixture();
        match corruption {
            0 => executor.last_proof_expanded_let_sources[0].1 = usize::MAX,
            1 => {
                let non_let = parsed_assertion("(assert expanded_let_p)");
                let non_let_surface =
                    crate::executor::proof_surface_syntax::format_frontend_term(&non_let);
                executor.ctx.add_assertion_with_parsed(root, non_let);
                executor.last_proof_expanded_let_sources[0].1 = 1;
                executor.last_proof_expanded_let_sources[0].2 = non_let_surface;
            }
            2 => executor.last_proof_expanded_let_sources[0]
                .2
                .push_str(" ; forged"),
            3 => executor.last_proof_expanded_let_sources[0].0 = not_root,
            4 => {
                let mut overrides = DetHashMap::default();
                overrides.insert(root, "forged-expanded-let-surface".to_string());
                executor.last_proof_term_overrides = Some(overrides);
            }
            _ => unreachable!(),
        }

        executor.restore_reachable_authored_assume_surface_overrides(&proof);
        assert!(
            executor.last_unsat_proof_reconstruction_suppressed,
            "expanded-let metadata corruption case {corruption} must fail closed"
        );
    }
}

#[test]
fn canonical_row_supersedes_an_authenticated_expanded_let_surface() {
    let (mut executor, proof, root, _, source_surface) = expanded_let_source_fixture();
    executor.ctx.add_assertion_with_parsed(
        root,
        parsed_assertion("(assert (and expanded_let_p (not expanded_let_q)))"),
    );
    let mut overrides = DetHashMap::default();
    overrides.insert(root, source_surface);
    executor.last_proof_term_overrides = Some(overrides);

    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert_eq!(
        executor
            .last_proof_term_overrides
            .as_ref()
            .and_then(|overrides| overrides.get(&root)),
        None,
        "the direct canonical row clears the now-redundant let override"
    );
    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "canonical problem authority keeps the external proof publishable"
    );
}

#[test]
fn expanded_let_source_requires_both_proof_and_raw_source_grants() {
    for has_canonical_row in [false, true] {
        for missing_raw_grant in [false, true] {
            let (mut executor, proof, root, _, _) = expanded_let_source_fixture();
            if has_canonical_row {
                executor.ctx.add_assertion_with_parsed(
                    root,
                    parsed_assertion("(assert (and expanded_let_p (not expanded_let_q)))"),
                );
            }
            if missing_raw_grant {
                executor.last_proof_raw_original_assertions.clear();
            } else {
                executor.last_proof_rebuild_originals.clear();
            }

            executor.restore_reachable_authored_assume_surface_overrides(&proof);
            assert!(
                executor.last_unsat_proof_reconstruction_suppressed,
                "expanded-let source needs both grants even with canonical row: \
                 canonical={has_canonical_row}, missing_raw={missing_raw_grant}"
            );
        }
    }
}

#[test]
fn conflicting_expanded_let_spellings_for_one_root_fail_closed() {
    let (mut executor, proof, root, _, _) = expanded_let_source_fixture();
    let second_source = parsed_assertion(
        "(assert (let ((second_alias expanded_let_p)) \
         (and second_alias (not expanded_let_q))))",
    );
    let second_surface =
        crate::executor::proof_surface_syntax::format_frontend_term(&second_source);
    executor.ctx.add_assertion_with_parsed(root, second_source);
    executor
        .last_proof_expanded_let_sources
        .push((root, 1, second_surface));

    executor.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(
        executor.last_unsat_proof_reconstruction_suppressed,
        "one raw root cannot select between two distinct authored let spellings"
    );
}

#[test]
fn expanded_let_consumer_uses_the_producer_cap() {
    let producer_cap = crate::executor::proof_trust_surgery_provenance::MAX_PROVENANCE_REPAIR_TERMS;
    let (mut at_cap, proof, root, _, source_surface) = expanded_let_source_fixture();
    at_cap.last_proof_expanded_let_sources = vec![(root, 0, source_surface); producer_cap];
    at_cap.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(
        !at_cap.last_unsat_proof_reconstruction_suppressed,
        "the exact producer boundary remains consumable"
    );

    let (mut over_cap, proof, root, _, source_surface) = expanded_let_source_fixture();
    over_cap.last_proof_expanded_let_sources = vec![(root, 0, source_surface); producer_cap + 1];
    over_cap.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(
        over_cap.last_unsat_proof_reconstruction_suppressed,
        "consumer work must stop at the same boundary enforced by the producer"
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

/// Seed one stale earlier-pass spelling on `root` so the next pass has
/// something to either clear, keep, or refuse.
fn seed_stale_override(executor: &mut Executor, root: TermId, spelling: &str) {
    let mut overrides = DetHashMap::default();
    overrides.insert(root, spelling.to_string());
    executor.last_proof_term_overrides = Some(overrides);
}

/// `duplicate_root_with_identity_row_uses_exact_canonical_surface` starts from
/// an EMPTY override table, so it cannot tell an authenticated identity
/// presentation apart from a silent `AletheSurfaceUnavailable` decline: both
/// leave the table `None` and the suppression flag clear. Seeding a stale
/// spelling separates them — only the identity classification actively REMOVES
/// it, restoring the canonical text the duplicate's own `(assert (<= 0 (f b)))`
/// row authenticates.
#[test]
fn duplicate_identity_row_clears_a_stale_spelling_on_its_root() {
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
    seed_stale_override(&mut executor, canonical, "(>= (f b) 0)");

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert_eq!(
        executor
            .last_proof_term_overrides
            .as_ref()
            .and_then(|overrides| overrides.get(&canonical)),
        None,
        "the identity row authenticates canonical text, so the stale spelling \
         must be cleared rather than kept by a decline or replaced by one of \
         the duplicate rows"
    );
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
}

/// The same authentication with ONE source row. A row that already spells the
/// root exactly as the Alethe printer renders it is the problem file's own
/// evidence for canonical text, so a stale earlier-pass spelling is cleared.
/// Before this was wired, the single-row arm re-derived the identical spelling
/// as an override, found the stale entry disagreed, and suppressed the whole
/// reconstruction — publishing NO proof for a root the problem file spells
/// canonically.
#[test]
fn single_identity_row_clears_a_stale_spelling_instead_of_suppressing() {
    let mut executor = Executor::new();
    let (canonical, negated) = comparison_surface_fixture(&mut executor);
    executor
        .ctx
        .add_assertion_with_parsed(canonical, parsed_assertion("(assert (<= 0 (f b)))"));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (<= 0 (f b))))"));
    seed_stale_override(&mut executor, canonical, "(>= (f b) 0)");

    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert_eq!(
        executor
            .last_proof_term_overrides
            .as_ref()
            .and_then(|overrides| overrides.get(&canonical)),
        None,
        "an exact canonical source row clears a stale spelling for its root"
    );
    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "a root the problem file spells canonically must never cost the query \
         its whole external proof"
    );
}
