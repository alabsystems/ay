// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pinned-carcara replay of the OR-packed `eq_transitive` spelling.
//!
//! The lazy-EUF lane states a transitivity explanation as ONE or-literal,
//! `(cl (or (not (= a b)) .. (= s t)))`, which the strict `EufTransitive`
//! validator flattens. `alethe_printer_eq_transitive.rs` spells that unit as
//! an `eq_transitive` over the printed disjuncts, one `or_neg` per disjunct
//! and a `resolution` back to the unit's exact text (aa1909575). When the
//! printed disjuncts meet only at two spellings of one closed bit-vector
//! value, the `eq_transitive` is the flat path's checked closed-spelling
//! bridge (43a040081) instead; any other break ships the honest hole. These
//! fixtures run each case past carcara 1.1.0 (git 9a352ee) with NO allowance,
//! inside the refutation the lane builds: the unit, its `or` unpack and one
//! resolution per disjunct.
//!
//! Measured 2026-09-26 at 8e2f8867b, with every decline instrumented: no
//! packed unit reached the printer from the 93 corpus rows (all three proof
//! postures, plus forced dumps of the withheld internal proofs); 735 further
//! distinct `benchmarks/` files gave 27 packed units in 6 documents, every one
//! chaining over its printed text; group_proofs gave none. The bridged case
//! below is the one the flat path already met in two corpus rows.

use super::{carcara_verdict_without_allowances, require_carcara_or_skip, CarcaraVerdict};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};
use ntest::timeout;
use std::path::PathBuf;

/// `(= lhs rhs)` exactly as oriented: `mk_eq` would canonicalise operand
/// order, and the orientation is what carcara reads.
fn raw_eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool)
}

/// The packed unit over `hypotheses` (each a `(lhs, rhs)` pair) with
/// `conclusion` last, refuted the way the lazy-EUF lane consumes it: the
/// `EufTransitive` unit, its `or` unpack, then one resolution per disjunct
/// against the problem premises `hypotheses` and `(not conclusion)`.
/// Returns the proof and the premises the problem must assert.
fn packed_refutation(
    terms: &mut TermStore,
    hypotheses: &[(TermId, TermId)],
    conclusion: (TermId, TermId),
) -> (Proof, Vec<TermId>) {
    let mut disjuncts = Vec::with_capacity(hypotheses.len() + 1);
    let mut premises = Vec::with_capacity(hypotheses.len() + 1);
    for &(lhs, rhs) in hypotheses {
        let equality = raw_eq(terms, lhs, rhs);
        disjuncts.push(terms.mk_not_raw(equality));
        premises.push(equality);
    }
    let goal = raw_eq(terms, conclusion.0, conclusion.1);
    disjuncts.push(goal);
    premises.push(terms.mk_not_raw(goal));
    let unit = terms.mk_app(Symbol::named("or"), disjuncts.clone(), Sort::Bool);

    let mut proof = Proof::new();
    let lemma = proof.add_step(ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause: vec![unit],
        farkas: None,
        kind: TheoryLemmaKind::EufTransitive,
        lia: None,
    });
    let mut current = proof.add_rule_step(AletheRule::Or, disjuncts.clone(), vec![lemma], vec![]);
    for (index, &premise) in premises.iter().enumerate() {
        let pivot = if index + 1 < premises.len() {
            premise
        } else {
            goal
        };
        let assume = proof.add_assume(premise, None);
        current = proof.add_resolution(disjuncts[index + 1..].to_vec(), pivot, current, assume);
    }
    (proof, premises)
}

/// One fixture: the packed unit `shape` (hypotheses, conclusion) refuted over
/// the problem `declarations`, with `overrides` (premise index, printed
/// spelling) applied to the authored surface. `strict` is whether AY's own
/// checker accepts the proof over the term DAG. Returns the problem, whose
/// assertions are exactly the document's printed `assume` leaves so every
/// premise matches as carcara reads it, and the document.
fn export_packed(
    label: &str,
    terms: &mut TermStore,
    declarations: &str,
    shape: (&[(TermId, TermId)], (TermId, TermId)),
    overrides: &[(usize, &str)],
    strict: bool,
) -> (String, String) {
    let (proof, premises) = packed_refutation(terms, shape.0, shape.1);
    assert_eq!(
        ay_proof::check_proof_strict(&proof, terms).is_ok(),
        strict,
        "{label}: AY's strict checker over the term DAG"
    );
    let overrides: DetHashMap<TermId, String> = overrides
        .iter()
        .map(|&(premise, spelling)| (premises[premise], spelling.to_string()))
        .collect();
    let overrides = (!overrides.is_empty()).then_some(&overrides);
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof, terms, &premises, overrides,
    )
    .expect("the packed refutation exports");
    let mut problem = declarations.to_string();
    for line in document.lines() {
        if let Some((_, assumed)) = line
            .strip_prefix("(assume ")
            .and_then(|rest| rest.split_once(' '))
        {
            problem.push_str(&format!("(assert {assumed}\n"));
        }
    }
    problem.push_str("(check-sat)\n");
    (problem, document)
}

const INTS: &str = "(set-logic QF_LIA)\n\
    (declare-fun a () Int)\n(declare-fun b () Int)\n(declare-fun c () Int)\n\
    (declare-fun d () Int)\n(declare-fun e () Int)\n";

const BYTES: &str = "(set-logic QF_BV)\n\
    (declare-fun lo () (_ BitVec 8))\n(declare-fun hi () (_ BitVec 8))\n";

fn int_vars(terms: &mut TermStore) -> [TermId; 5] {
    ["a", "b", "c", "d", "e"].map(|name| terms.mk_var(name, Sort::Int))
}

/// `lo`, `hi` and the folded constant `#x04`, all 8 bits wide.
fn byte_terms(terms: &mut TermStore) -> [TermId; 3] {
    let lo = terms.mk_var("lo", Sort::bitvec(8));
    let hi = terms.mk_var("hi", Sort::bitvec(8));
    let four = terms.mk_bitvec(num_bigint::BigInt::from(4u8), 8);
    [lo, hi, four]
}

/// The shipped spelling carries every `required` fragment and no unchecked
/// step, and pinned carcara re-derives it: a literal `valid`.
fn assert_packed_valid(
    label: &str,
    carcara: Option<&PathBuf>,
    (problem, document): (String, String),
    required: &[&str],
) {
    for fragment in [":rule or_neg :args (0))"].iter().chain(required) {
        assert!(
            document.contains(fragment),
            "{label}: the unit is spelled with `{fragment}`:\n{document}"
        );
    }
    assert!(
        !document.contains(":rule hole") && !document.contains(":rule trust"),
        "{label}: no unchecked step:\n{document}"
    );
    let Some(carcara) = carcara else {
        return;
    };
    assert_eq!(
        carcara_verdict_without_allowances(carcara, label, &problem, &document),
        CarcaraVerdict::Valid,
        "{label}: pinned carcara must re-derive the packed spelling trust-free"
    );
}

#[test]
#[timeout(60_000)]
fn a_packed_transitivity_unit_prints_a_carcara_valid_chain() {
    // Resolved once: without carcara every case still runs its own checks.
    let carcara = require_carcara_or_skip();
    let mut terms = TermStore::new();
    let [a, b, c, d, e] = int_vars(&mut terms);
    for (label, hypotheses, conclusion) in [
        ("packed_chain_two_hops", vec![(a, b), (b, c)], (a, c)),
        // Out of chain order and every hypothesis flipped: carcara's
        // `find_chain` orients each hypothesis itself, so no `eq_symmetric`.
        (
            "packed_chain_flipped_out_of_order",
            vec![(d, c), (b, a), (c, b), (e, d)],
            (a, e),
        ),
    ] {
        let exported = export_packed(
            label,
            &mut terms,
            INTS,
            (&hypotheses, conclusion),
            &[],
            true,
        );
        assert_packed_valid(label, carcara.as_ref(), exported, &["(step t0.et (cl "]);
    }
}

#[test]
#[timeout(60_000)]
fn a_packed_unit_broken_only_by_a_closed_bitvec_spelling_is_bridged_valid() {
    // The authored surface spells the premise `lo = #x04` as AY's input did,
    // `(= lo (concat #x0 #x4))`, so the printed disjuncts meet at two
    // spellings of one value and carcara would refuse a plain
    // `eq_transitive` as a broken chain. The bridge proves the missing link
    // with `evaluate` (concat is exact in pinned carcara) and the packed
    // repack is unchanged.
    let carcara = require_carcara_or_skip();
    let label = "packed_closed_bitvec_bridged";
    let mut terms = TermStore::new();
    let [lo, hi, four] = byte_terms(&mut terms);
    let exported = export_packed(
        label,
        &mut terms,
        BYTES,
        (&[(lo, four), (hi, four)], (lo, hi)),
        &[(0, "(= lo (concat #x0 #x4))")],
        true,
    );
    assert_packed_valid(
        label,
        carcara.as_ref(),
        exported,
        &[
            "(step t0.et.gb0 (cl (= (concat #x0 #x4) #b00000100)) :rule evaluate)",
            "(step t0.et.gb.et (cl ",
            "(step t0.et (cl (not (= lo (concat #x0 #x4))) (not (= hi #b00000100)) (= lo hi)) :rule resolution",
        ],
    );
}

/// One negative twin: the packed unit must ship as exactly one disclosed hole
/// with no `eq_transitive`, `or_neg` or `evaluate`, and carcara then reports
/// `holey`, never `valid` and never `invalid`.
fn assert_packed_hole(label: &str, (problem, document): (String, String)) {
    assert_eq!(
        document.matches(":rule hole").count(),
        1,
        "{label}: the unit is one honest hole:\n{document}"
    );
    for rule in [":rule eq_transitive", ":rule or_neg", ":rule evaluate"] {
        assert!(
            !document.contains(rule),
            "{label}: no `{rule}` for a chain the printed text does not instantiate:\n{document}"
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert_eq!(
        carcara_verdict_without_allowances(&carcara, label, &problem, &document),
        CarcaraVerdict::Holey,
        "{label}: every other step checks and the hole is named, never valid or invalid"
    );
}

#[test]
#[timeout(60_000)]
fn a_packed_unit_whose_printed_disjuncts_do_not_chain_stays_an_honest_hole() {
    let mut terms = TermStore::new();
    let [a, b, c, d, _] = int_vars(&mut terms);
    let chain: &[(TermId, TermId)] = &[(a, b), (b, c)];
    for (label, shape, overrides, strict) in [
        // The sixth false green's surface: a chain over the term DAG whose
        // first premise the authored surface re-spells as its Boolean-as-Int
        // encoding. No closed bit-vector term, so nothing to bridge.
        (
            "packed_respelled_hypothesis",
            (chain, (a, c)),
            &[(0, "(= (ite (not (= a b)) 1 0) 0)")][..],
            true,
        ),
        // The only packed decline measured from SMT-LIB input (QF_UF atoms
        // authored as a chainable `=`): carcara's `eq_transitive` reads only
        // binary equalities, and the bridge plans none but binary links.
        (
            "packed_chainable_equality",
            (chain, (a, c)),
            &[(1, "(= b c c)")][..],
            true,
        ),
        // A producer defect: the shapes are right and no chain connects the
        // conclusion. The problem is satisfiable (a = b = 0, c = d = 1), so a
        // `valid` here would be a false refutation.
        (
            "packed_disconnected_chain",
            (&[(a, b), (c, d)][..], (a, d)),
            &[][..],
            false,
        ),
        // Fewer than three operands: carcara's `eq_transitive` floor.
        (
            "packed_one_hypothesis",
            (&[(a, b)][..], (b, a)),
            &[][..],
            true,
        ),
    ] {
        let exported = export_packed(label, &mut terms, INTS, shape, overrides, strict);
        assert_packed_hole(label, exported);
    }

    // The closed bit-vector break through an operator pinned carcara
    // evaluates wrongly (#xfc here, not #x04): the bridge never evaluates it.
    let label = "packed_excluded_operator_spelling";
    let mut terms = TermStore::new();
    let [lo, hi, four] = byte_terms(&mut terms);
    let exported = export_packed(
        label,
        &mut terms,
        BYTES,
        (&[(lo, four), (hi, four)], (lo, hi)),
        &[(0, "(= lo (bvsub #xff #xfb))")],
        true,
    );
    assert_packed_hole(label, exported);
}
