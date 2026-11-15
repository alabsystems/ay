// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pinned-carcara replay of the printer's read-over-write and
//! equality-predicate repairs.
//!
//! `mk_select` folds `(select (store a i v1) i)` to `v1` while the problem is
//! elaborated, so the assertion `(= (select (store a i v1) i) v2)` is the
//! internal `(= v1 v2)` printed back under its authored override, while the
//! negated atom from `(distinct v1 v2)` prints through the confined
//! `distinct_elim` bridge as `(not (= v1 v2))`. The refutation's two-literal
//! transitivity lemma then printed as
//! `(cl (not (= v1 v2)) (= (select (store a i v1) i) v2))` (a `hole`: carcara's
//! `eq_transitive` needs a chain, and a third literal), and the closing
//! resolution met the two spellings of one pivot, so `--proof` REFUSED the
//! export: `unsat` with no document. Both are now spelled with carcara's
//! `arrays_idx` (`alethe_printer_eq_transitive_bridge.rs`,
//! `printed_resolution/pivot_bridge.rs`). The cases cover the read on either
//! side of the authored equality (`cong` checks a binary `=` in every
//! orientation), a read that is the DENIED spelling of a Boolean pivot (the
//! mirrored `equiv_pos1` arm), a written element AY folded (`arrays_idx`,
//! `evaluate`, `trans`), and a read link inside a longer chain.
//!
//! An `EufCongruentPred` lemma over the equality predicate whose conclusion
//! prints in the problem's operand order no longer pairs positionally, so it
//! shipped as `hole`; it is printed as the `eq_transitive` chain it states
//! (`alethe_printer_eq_congruent_pred.rs`).
//!
//! Every positive case is a literal `valid` from carcara 1.1.0 (git 9a352ee)
//! with no allowance. The negative twins keep their refusal or their hole.

use super::{
    carcara_verdict_without_allowances, require_carcara_or_skip, run_carcara_trust_free,
    solve_unsat_and_get_proof, CarcaraVerdict,
};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};
use ntest::timeout;

/// `benchmarks/conformance/QF_AX/unsat_store_mismatch.smt2`, inlined.
const STORE_MISMATCH: &str = r#"
(set-logic QF_AX)
(declare-sort Idx 0)
(declare-sort Elm 0)
(declare-const a (Array Idx Elm))
(declare-const i Idx)
(declare-const v1 Elm)
(declare-const v2 Elm)
(assert (distinct v1 v2))
(assert (= (select (store a i v1) i) v2))
(check-sat)
"#;

/// `STORE_MISMATCH` with the authored equality's operands swapped and the
/// rows reordered: the respelled pivot `(= v2 (select (store a i v1) i))`
/// pairs with `(= v1 v2)` only through `cong`'s operand swap for `=`.
const SWAPPED_STORE_MISMATCH: &str = r#"
(set-logic QF_AX)
(declare-sort Idx 0)
(declare-sort Elm 0)
(declare-const a (Array Idx Elm))
(declare-const i Idx)
(declare-const v1 Elm)
(declare-const v2 Elm)
(assert (= v2 (select (store a i v1) i)))
(assert (distinct v1 v2))
(check-sat)
"#;

/// `regression/soundness_sat_chokepoint/qf_alia_read_over_store_via_maximize`
/// without its objective: the read is the conclusion's right operand.
const READ_OVER_STORE: &str = r#"
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun x () Int)
(assert (= x (select (store a i 5) i)))
(assert (distinct x 5))
(check-sat)
"#;

/// The written element is itself a read over a write: two `arrays_idx`
/// links joined by `trans`.
const NESTED_READ: &str = r#"
(set-logic QF_AX)
(declare-sort Idx 0)
(declare-sort Elm 0)
(declare-const a (Array Idx Elm))
(declare-const b (Array Idx Elm))
(declare-const i Idx)
(declare-const k Idx)
(declare-const u Elm)
(declare-const v2 Elm)
(assert (= (select (store a i (select (store b k u) k)) i) v2))
(assert (distinct u v2))
(check-sat)
"#;

/// A three-literal transitivity lemma whose middle link is a read over a
/// write: AY's chain runs through `v3`, the printed hypothesis through the
/// read, so the step shipped as `hole` until `arrays_idx` supplied the link.
const READ_LINK_IN_A_LONGER_CHAIN: &str = r#"
(set-logic QF_AX)
(declare-sort Idx 0)
(declare-sort Elm 0)
(declare-const a (Array Idx Elm))
(declare-const i Idx)
(declare-const v1 Elm)
(declare-const v2 Elm)
(declare-const v3 Elm)
(assert (distinct v1 v2))
(assert (= (select (store a i v3) i) v2))
(assert (= v3 v1))
(check-sat)
"#;

/// The written element is a closed bit-vector term AY folded: the link is
/// `arrays_idx` to the element, `evaluate` from the element to the value AY
/// prints, and `trans`; the pivot then meets `(= x #b00000010)` only through
/// `cong`'s operand swap for `=`.
const RESPELLED_ELEMENT: &str = r#"
(set-logic QF_ABV)
(declare-sort Idx 0)
(declare-const a (Array Idx (_ BitVec 8)))
(declare-const i Idx)
(declare-const x (_ BitVec 8))
(assert (= (select (store a i (bvadd #x01 #x01)) i) x))
(assert (distinct x #x02))
(check-sat)
"#;

/// The read is the DENIED spelling of a Boolean pivot inside a clause, so no
/// authored-assume bridge confines it first: `arrays_idx` proves the mirror
/// of `(= p read)`, and the implication is `equiv_pos1` over that mirror.
const MIRRORED_PIVOT: &str = r#"
(set-logic QF_AX)
(declare-sort Idx 0)
(declare-const ba (Array Idx Bool))
(declare-const k Idx)
(declare-const p Bool)
(declare-const r Bool)
(assert (or r (not (select (store ba k p) k))))
(assert p)
(assert (not r))
(check-sat)
"#;

/// `benchmarks/smt/QF_AX/three_store_chain.smt2`, inlined.
const THREE_STORE_CHAIN: &str = r#"
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun c () (Array Index Element))
(declare-fun d () (Array Index Element))
(declare-fun i () Index)
(declare-fun v () Element)
(assert (= b (store a i v)))
(assert (= c b))
(assert (= d c))
(assert (not (= (select d i) v)))
(check-sat)
"#;

fn assert_trust_free_valid(label: &str, problem: &str, required: &str) {
    let proof = solve_unsat_and_get_proof(problem, label);
    assert!(
        proof.contains(required),
        "{label}: the repair must spell `{required}`:\n{proof}"
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{label}: no unchecked step:\n{proof}"
    );
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara_trust_free(&carcara, label, problem, &proof),
        "{label}: pinned carcara must re-derive the document trust-free"
    );
}

#[test]
#[timeout(60_000)]
fn a_folded_read_over_write_assertion_publishes_a_carcara_valid_proof() {
    for (label, problem, required) in [
        (
            "read_over_write_store_mismatch",
            STORE_MISMATCH,
            ":rule arrays_idx",
        ),
        (
            "read_over_write_swapped_operands",
            SWAPPED_STORE_MISMATCH,
            ":rule arrays_idx",
        ),
        (
            "read_over_write_read_over_store",
            READ_OVER_STORE,
            ":rule arrays_idx",
        ),
        (
            "read_over_write_nested_read",
            NESTED_READ,
            ":rule arrays_idx",
        ),
        (
            "read_over_write_link_in_a_longer_chain",
            READ_LINK_IN_A_LONGER_CHAIN,
            "(cl (= (select (store a i v3) i) v3)) :rule arrays_idx)",
        ),
        (
            "read_over_write_respelled_element",
            RESPELLED_ELEMENT,
            "(cl (= (bvadd #x01 #x01) #b00000010)) :rule evaluate)",
        ),
        (
            "read_over_write_mirrored_pivot",
            MIRRORED_PIVOT,
            "(cl (not (= (select (store ba k p) k) p)) (select (store ba k p) k) (not p)) \
             :rule equiv_pos1)",
        ),
    ] {
        assert_trust_free_valid(label, problem, required);
    }
}

#[test]
#[timeout(60_000)]
fn an_equality_predicate_lemma_out_of_position_publishes_its_chain() {
    assert_trust_free_valid(
        "equality_predicate_three_store_chain",
        THREE_STORE_CHAIN,
        "(not (= v (select c i))) (= (select d i) v)) :rule eq_transitive)",
    );
}

/// `(= lhs rhs)` exactly as oriented.
fn raw_eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool)
}

/// `(distinct v1 v2)`'s atom and the folded assertion `(= v1 v2)`, refuted the
/// way the executor does: the assumed premises, the two-literal
/// `EufTransitive` lemma, and two resolutions. The assertion prints under
/// `spelling`; the negated atom under `(distinct v1 v2)`.
fn folded_assertion_export(spelling: &str) -> Result<String, ay_proof::AlethePrintError> {
    let mut terms = TermStore::new();
    let elm = Sort::Uninterpreted("Elm".to_string());
    let v1 = terms.mk_var("v1", elm.clone());
    let v2 = terms.mk_var("v2", elm);
    let atom = raw_eq(&mut terms, v1, v2);
    let negated = terms.mk_not_raw(atom);
    let mut proof = Proof::new();
    let distinct = proof.add_assume(negated, None);
    let folded = proof.add_assume(atom, None);
    let lemma = proof.add_step(ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause: vec![negated, atom],
        farkas: None,
        kind: TheoryLemmaKind::EufTransitive,
        lia: None,
    });
    let unit = proof.add_rule_step(
        AletheRule::ThResolution,
        vec![atom],
        vec![lemma, folded],
        Vec::new(),
    );
    proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![unit, distinct],
        Vec::new(),
    );
    assert!(
        ay_proof::check_proof_strict(&proof, &terms).is_ok(),
        "AY's strict checker accepts the refutation over the term DAG"
    );
    let overrides: DetHashMap<TermId, String> = [
        (negated, "(distinct v1 v2)".to_string()),
        (atom, spelling.to_string()),
    ]
    .into_iter()
    .collect();
    ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[negated, atom],
        Some(&overrides),
    )
}

const ELM_DECLARATIONS: &str = "(set-logic QF_AX)\n(declare-sort Idx 0)\n(declare-sort Elm 0)\n\
     (declare-const a (Array Idx Elm))\n(declare-const i Idx)\n(declare-const j Idx)\n\
     (declare-const v1 Elm)\n(declare-const v2 Elm)\n(declare-const v3 Elm)\n";

/// The minimal fixture of the lowering, and its negative twins. The same
/// refutation over a read `arrays_idx` cannot prove — another index, another
/// written element — is a document about a SATISFIABLE problem, and the
/// printer must keep refusing it rather than bridge it.
#[test]
#[timeout(60_000)]
fn the_read_over_write_lowering_proves_only_the_same_index_read() {
    let carcara = require_carcara_or_skip();
    let read = "(select (store a i v1) i)";
    // The second spelling swaps the authored operands: the pivot meets the
    // canonical `(= v1 v2)` only through `cong`'s operand swap for `=`.
    for (label, spelling, chain) in [
        (
            "read_over_write_fixture",
            format!("(= {read} v2)"),
            format!("(cl (not (= {read} v1)) (not (= v1 v2)) (= {read} v2)) :rule eq_transitive)"),
        ),
        (
            "read_over_write_swapped_fixture",
            format!("(= v2 {read})"),
            format!("(cl (not (= v1 v2)) (not (= {read} v1)) (= v2 {read})) :rule eq_transitive)"),
        ),
    ] {
        let document = folded_assertion_export(&spelling).expect("the same-index read is bridged");
        for fragment in [
            format!("(cl (= {read} v1)) :rule arrays_idx)"),
            chain,
            format!("(cl (= {spelling} (= v1 v2))) :rule cong"),
            ":rule equiv_pos2)".to_string(),
        ] {
            assert!(
                document.contains(&fragment),
                "{label}: missing `{fragment}`:\n{document}"
            );
        }
        assert!(!document.contains(":rule hole"), "{label}: {document}");
        if let Some(carcara) = carcara.as_ref() {
            let problem = format!(
                "{ELM_DECLARATIONS}(assert (distinct v1 v2))\n(assert {spelling})\n(check-sat)\n"
            );
            assert_eq!(
                carcara_verdict_without_allowances(carcara, label, &problem, &document),
                CarcaraVerdict::Valid,
                "{label}: the minimal fixture must replay trust-free"
            );
        }
    }
    for spelling in [
        "(= (select (store a i v1) j) v2)",
        "(= (select (store a i v3) i) v2)",
        "(= v2 (select (store a i v3) i))",
        "(= v2 (select (store a i v1) j))",
    ] {
        let refused = folded_assertion_export(spelling)
            .expect_err("a read arrays_idx cannot prove must stay refused");
        assert!(
            refused
                .to_string()
                .contains("do not eliminate the printed resolution pivot"),
            "{spelling}: {refused}"
        );
    }
}
