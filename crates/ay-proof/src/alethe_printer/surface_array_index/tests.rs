// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::kani_compat::DetHashMap;

fn fixture() -> (TermStore, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(8);
    let array = Sort::array(sort.clone(), sort.clone());
    let mem = terms.mk_var("mem", array.clone());
    let p = terms.mk_var("p", sort.clone());
    let value = terms.mk_bitvec(16.into(), 8);
    let store = terms.mk_app(Symbol::named("store"), [mem, p, value], array);
    let select = terms.mk_app(Symbol::named("select"), [store, p], sort);
    let row = terms.mk_app(Symbol::named("="), [select, value], Sort::Bool);
    (terms, store, select, row)
}

#[test]
fn row1_transports_each_zero_fold_and_both_equality_orientations() {
    let (terms, store, select, row) = fixture();
    for (case, (written, read)) in [
        ("(bvadd p #x00)", "p"),
        ("p", "(bvadd #x00 p)"),
        ("(bvadd p #x00)", "(bvadd p #x00)"),
        ("(bvadd #x00 p)", "(bvadd p #x00)"),
    ]
    .into_iter()
    .enumerate()
    {
        for reversed in [false, true] {
            let stored = format!("(store mem {written} #b00010000)");
            let selected = format!("(select {stored} {read})");
            let equality = if reversed {
                format!("(= #b00010000 {selected})")
            } else {
                format!("(= {selected} #b00010000)")
            };
            let overrides = [(store, stored), (select, selected), (row, equality.clone())]
                .into_iter()
                .collect();
            let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
            let proof = printer
                .format_array_select_store(ProofId(1), &[row], true)
                .unwrap();
            assert!(proof.contains(":rule arrays_idx"));
            assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
            let problem = format!("(set-logic QF_ABV)(declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))(declare-const p (_ BitVec 8))(assert (not {equality}))(check-sat)");
            let proof = format!("(assume premise (not {equality}))\n{proof}\n(step done (cl) :rule resolution :premises (premise t1))\n");
            let path = std::env::temp_dir().join(format!(
                "ay-row-zero-index-{case}-{reversed}-{}.json",
                std::process::id()
            ));
            std::fs::write(
                &path,
                serde_json::to_vec(&serde_json::json!({
                    "type":"alethe_certificate", "version":"1.0", "problem":problem, "proof":proof
                }))
                .unwrap(),
            )
            .unwrap();
            println!("independent replay certificate: {}", path.display());
        }
    }
}

#[test]
fn row1_zero_bridge_refuses_changed_arrays_values_indices_and_conclusions() {
    let (terms, store, select, row) = fixture();
    for (base, written, read, value, conclusion) in [
        ("other", "(bvadd p #x00)", "p", "#b00010000", false),
        ("mem", "(bvadd p #x01)", "p", "#b00010000", false),
        ("mem", "(bvadd p #x00)", "q", "#b00010000", false),
        ("mem", "(bvadd q #x00)", "p", "#b00010000", false),
        ("mem", "(bvadd p #b0)", "p", "#b00010000", false),
        ("mem", "(bvadd p #x00)", "p", "#b11111111", false),
        ("mem", "(bvadd p #x00)", "p", "#b00010000", true),
    ] {
        let stored = format!("(store {base} {written} {value})");
        let selected = format!("(select {stored} {read})");
        let mut overrides = [(store, stored), (select, selected)]
            .into_iter()
            .collect::<DetHashMap<_, _>>();
        if conclusion {
            overrides.insert(row, "(= p #b00010000)".into());
        }
        let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
        assert!(matches!(
            printer.format_array_select_store(ProofId(1), &[row], true),
            Err(AlethePrintError::InvalidArrayStep { .. })
        ));
    }
}

#[test]
fn row1_zero_bridge_retains_the_output_work_limit() {
    let (terms, store, _, row) = fixture();
    let overrides = [(store, "(store mem (bvadd p #x00) #b00010000)".into())]
        .into_iter()
        .collect();
    let printer =
        AlethePrinter::new_with_overrides_and_budget(&terms, Some(&overrides), Some(1024));
    assert!(printer
        .format_array_select_store(ProofId(1), &[row], true)
        .is_err());
    assert!(printer.work_budget_exhausted());
}

/// `(cl (not (= 0 s)) (= (select (store a 0 v) s) v))` — a conditional ROW1
/// whose guard node and whose read index carry DIFFERENT authored spellings of
/// one `TermId`.
fn conditional_fixture() -> (TermStore, TermId, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let int = Sort::Int;
    let array = Sort::array(int.clone(), int.clone());
    let a = terms.mk_var("a", array.clone());
    let v = terms.mk_var("v", int.clone());
    let s = terms.mk_var("s", int.clone());
    let zero = terms.mk_int(0.into());
    let store = terms.mk_app(Symbol::named("store"), [a, zero, v], array);
    let select = terms.mk_app(Symbol::named("select"), [store, s], int);
    let row = terms.mk_app(Symbol::named("="), [select, v], Sort::Bool);
    let index_eq = terms.mk_app(Symbol::named("="), [zero, s], Sort::Bool);
    let guard = terms.mk_not_raw(index_eq);
    (terms, s, row, guard, index_eq)
}

#[test]
fn conditional_row1_guard_bridges_an_ancestor_level_zero_addition_spelling() {
    let (terms, s, row, guard, index_eq) = conditional_fixture();
    // The #7956 shape: the problem file authors BOTH `(= (seq_offset ..) 0)`
    // as a top-level assertion — whose spelling lands on the equality NODE —
    // and `(+ (seq_offset ..) 0)` as a read index inside an authored `store`,
    // whose spelling lands on the INDEX. Elaboration folds `(+ x 0)` onto `x`,
    // so that is one `TermId` with two authored texts at two nesting depths,
    // and each is needed verbatim by the `assume` carrying its own assertion.
    let overrides = [
        (s, "(+ s 0)".to_string()),
        (index_eq, "(= s 0)".to_string()),
    ]
    .into_iter()
    .collect();
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let proof = printer
        .format_array_select_store(ProofId(1), &[row, guard], true)
        .expect("the bridged guard must export");
    // The subproof assumes the GUARD's own text, so `subproof :discharge`
    // concludes exactly the literal the rest of the document resolves against.
    assert!(proof.contains("(assume t1.h (= s 0))"), "{proof}");
    assert!(
        proof.contains("(step t1.gsa (cl (= (+ s 0) s)) :rule poly_simp)"),
        "{proof}"
    );
    assert!(
        proof.contains("(step t1.gs (cl (= (+ s 0) 0)) :rule trans :premises (t1.gsa t1.h))"),
        "{proof}"
    );
    assert!(proof.contains(":rule arrays_idx"), "{proof}");
    assert!(proof.contains(":rule cong :premises (t1.gs)"), "{proof}");
    assert!(
        proof.contains("(cl (not (= s 0)) (= (select (store a 0 v) (+ s 0)) v)) :rule subproof"),
        "{proof}"
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{proof}"
    );
    // MEASURED against the pinned checker outside the harness: carcara 1.1.0
    // (git 9a352ee) answers `valid` on exactly this derivation, and `invalid`
    // ("terms are not equal after polynomial normalization") when the bridge
    // step is perturbed to `(= (+ s 1) s)`.
}

#[test]
fn conditional_row1_guard_keeps_its_plain_form_without_an_override() {
    let (terms, _, row, guard, _) = conditional_fixture();
    let overrides = DetHashMap::default();
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let proof = printer
        .format_array_select_store(ProofId(1), &[row, guard], true)
        .expect("the unbridged guard must export exactly as before");
    assert!(proof.contains("(assume t1.h (= 0 s))"), "{proof}");
    assert!(!proof.contains("poly_simp"), "{proof}");
    assert!(proof.contains(":rule cong :premises (t1.h)"), "{proof}");
}

#[test]
fn conditional_row1_guard_bridge_refuses_a_spelling_it_cannot_decide() {
    // `on_guard_node` overrides the NEGATION itself; otherwise the override
    // sits on the inner equality, exactly where the #7956 shape puts it.
    for (index_spelling, guard_text, on_guard_node) in [
        // The guard names a DIFFERENT constant, not another spelling of `0`.
        ("(+ s 0)", "(= s 1)", false),
        // The index spelling is not the same linear term as the guard's side.
        ("(+ s 1)", "(= s 0)", false),
        // The guard names a different symbol entirely.
        ("(+ s 0)", "(= t 0)", false),
        // An opaque re-spelling `poly_simp` cannot decide affirmatively.
        ("(f s)", "(= s 0)", false),
        // The guard surface is not a negation, so there is nothing to assume.
        ("(+ s 0)", "(= s 0)", true),
    ] {
        let (terms, s, row, guard, index_eq) = conditional_fixture();
        let key = if on_guard_node { guard } else { index_eq };
        let overrides = [
            (s, index_spelling.to_string()),
            (key, guard_text.to_string()),
        ]
        .into_iter()
        .collect();
        let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
        assert!(
            matches!(
                printer.format_array_select_store(ProofId(1), &[row, guard], true),
                Err(AlethePrintError::InvalidArrayStep { .. })
            ),
            "index={index_spelling} guard={guard_text}"
        );
    }
}
