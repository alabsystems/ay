// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ArrayGuardedRowExpansion` lowering: every lowered spelling replays
//! `valid` in pinned Carcara's PLAIN invocation; every clause outside the
//! lowerable subset keeps the honest `hole` (never a rule it does not
//! instantiate), and a clause the strict validator refuses gets no lowering.

use super::*;
use ay_core::{Proof, TheoryLemmaKind};
use std::process::Command;

/// The declarations every fixture below may name.
const PRELUDE: &str = "(set-logic QF_AUFLIA)
(declare-fun V () (Array Int Int))
(declare-fun U () (Array Int Int))
(declare-fun W () (Array Int Int))
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(declare-fun i () Int)
(declare-fun k () Int)
(declare-fun x () Int)
(declare-fun y () Int)
";

struct Fixture {
    terms: TermStore,
    v: TermId,
    u: TermId,
    w: TermId,
    i: TermId,
    k: TermId,
    x: TermId,
    y: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let array = Sort::array(Sort::Int, Sort::Int);
        let v = terms.mk_var("V", array.clone());
        let u = terms.mk_var("U", array.clone());
        let w = terms.mk_var("W", array);
        let [i, k, x, y] = ["i", "k", "x", "y"].map(|name| terms.mk_var(name, Sort::Int));
        Self {
            terms,
            v,
            u,
            w,
            i,
            k,
            x,
            y,
        }
    }

    fn store(&mut self, array: TermId, index: TermId, value: TermId) -> TermId {
        let sort = self.terms.sort(array).clone();
        self.terms
            .mk_app(Symbol::named("store"), [array, index, value], sort)
    }

    fn select(&mut self, array: TermId, index: TermId) -> TermId {
        self.terms
            .mk_app(Symbol::named("select"), [array, index], Sort::Int)
    }

    /// `(= left right)` in exactly this orientation.
    fn eq(&mut self, left: TermId, right: TermId) -> TermId {
        self.terms
            .mk_app(Symbol::named("="), [left, right], Sort::Bool)
    }

    fn not(&mut self, term: TermId) -> TermId {
        self.terms.mk_not_raw(term)
    }

    fn or(&mut self, literals: [TermId; 3]) -> TermId {
        self.terms.mk_app(Symbol::named("or"), literals, Sort::Bool)
    }

    /// `(sk V U)`, the measured corpus probe's spelling.
    fn skolem(&mut self) -> TermId {
        self.terms
            .mk_app(Symbol::named("sk"), [self.v, self.u], Sort::Int)
    }

    fn lowered(&self, clause: &[TermId]) -> Option<String> {
        AlethePrinter::new(&self.terms).format_array_guarded_row_expansion(ProofId(9), clause)
    }
}

/// Pinned carcara's PLAIN-invocation verdict, or `None` when it is absent.
/// The scratch pair is kept for inspection only when the verdict is not
/// `expected`.
fn carcara_verdict(case: &str, problem: &str, proof: &str, expected: &str) -> Option<String> {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) {
        panic!("{case}: {misjudged}\n{proof}");
    }
    let probe = Command::new("carcara").arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        eprintln!("carcara not on PATH: the {case} replay is skipped");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("ay-guarded-row-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("p.smt2"), problem).unwrap();
    std::fs::write(dir.join("p.alethe"), proof).unwrap();
    let output = Command::new("carcara")
        .arg("check")
        .arg("--")
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    let stderr = String::from_utf8_lossy(&output.stderr);
    if verdict == expected {
        let _ = std::fs::remove_dir_all(&dir);
    }
    Some(format!("{verdict}\n{stderr}\nkept: {}", dir.display()))
}

/// NEGATIVE CONTROL: the replay refuses, before the checker runs, the pair
/// pinned carcara prints `valid` for only through its `evaluate` defect.
#[test]
#[should_panic(expected = "is not evidence")]
fn the_carcara_replay_refuses_a_document_pinned_carcara_misjudges() {
    carcara_verdict(
        "false_valid_control",
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
        "valid",
    );
}

fn assert_verdict(case: &str, problem: &str, document: &str, expected: &str) {
    let scope = crate::ProblemScope::from_smtlib_source(problem);
    if let Err(defect) = crate::check_alethe_document(document, &scope) {
        panic!("{case}: round-trip self-check refused the document: {defect}\n{document}");
    }
    if let Some(verdict) = carcara_verdict(case, problem, document, expected) {
        let first = verdict.lines().next().unwrap_or("");
        assert_eq!(first, expected, "{case}: {verdict}\n{document}");
    }
}

/// The lowered step `t9` closed against the negation of each of its clause
/// literals, asserted in the problem and assumed in the document.
fn assert_lowering_valid(case: &str, fixture: &Fixture, clause: &[TermId]) {
    assert!(
        crate::recognize_array_guarded_row_expansion(&fixture.terms, clause),
        "{case}: the fixture must be a strictly checked guarded ROW expansion"
    );
    let proof = fixture
        .lowered(clause)
        .expect("lowerable guarded ROW expansion");
    assert!(!proof.contains(":rule hole"), "{case}:\n{proof}");
    let mut problem = PRELUDE.to_string();
    let mut document = String::new();
    let mut premises = vec!["t9".to_string()];
    for (position, &literal) in clause.iter().enumerate() {
        let literal = crate::format_term_alethe(&fixture.terms, literal);
        problem.push_str(&format!("(assert (not {literal}))\n"));
        document.push_str(&format!("(assume h{position} (not {literal}))\n"));
        premises.push(format!("h{position}"));
    }
    problem.push_str("(check-sat)\n");
    document.push_str(&proof);
    document.push_str(&format!(
        "\n(step done (cl) :rule resolution :premises ({}))\n",
        premises.join(" ")
    ));
    assert_verdict(case, &problem, &document, "valid");
}

/// The measured `storeinv_sf_size3` shape: both guard sides are stores at
/// `i`, the conclusion skips the LEFT store and reads the right side whole,
/// packed into one `or` with the index literal first.
#[test]
fn measured_store_pair_skipping_one_side_replays_valid() {
    let mut f = Fixture::new();
    let probe = f.skolem();
    let left = f.store(f.v, f.i, f.x);
    let right = f.store(f.u, f.i, f.y);
    let index = f.eq(f.i, probe);
    let guard_atom = f.eq(left, right);
    let guard = f.not(guard_atom);
    let base_read = f.select(f.v, probe);
    let whole_read = f.select(right, probe);
    let conclusion = f.eq(base_read, whole_read);
    let packed = f.or([index, guard, conclusion]);
    assert_lowering_valid("measured_packed", &f, &[packed]);
}

/// Flat clause, mirrored index spelling `(= k i)` (the `not_symm` bridge),
/// the store on the RIGHT, the conclusion in the reverse orientation.
#[test]
fn mirrored_index_and_right_store_replay_valid() {
    let mut f = Fixture::new();
    let store = f.store(f.u, f.i, f.y);
    let guard_atom = f.eq(f.v, store);
    let guard = f.not(guard_atom);
    let index = f.eq(f.k, f.i);
    let read = f.select(f.v, f.k);
    let base_read = f.select(f.u, f.k);
    let conclusion = f.eq(read, base_read);
    assert_lowering_valid("mirrored_flat", &f, &[guard, conclusion, index]);
}

/// Shape D: both guard sides skip their store at the same index.
#[test]
fn store_pair_reading_both_bases_replays_valid() {
    let mut f = Fixture::new();
    let left = f.store(f.v, f.i, f.x);
    let right = f.store(f.u, f.i, f.y);
    let guard_atom = f.eq(left, right);
    let guard = f.not(guard_atom);
    let index = f.eq(f.i, f.k);
    let left_read = f.select(f.v, f.k);
    let right_read = f.select(f.u, f.k);
    let conclusion = f.eq(left_read, right_read);
    let packed = f.or([guard, conclusion, index]);
    assert_lowering_valid("store_pair_packed", &f, &[packed]);
}

/// Shape C: the stored value read back, flat and packed, store on either side.
#[test]
fn read_back_replays_valid() {
    let mut f = Fixture::new();
    let store = f.store(f.v, f.i, f.x);
    let read = f.select(f.u, f.k);
    for (case, store_left) in [("read_back_left", true), ("read_back_right", false)] {
        let guard_atom = if store_left {
            f.eq(store, f.u)
        } else {
            f.eq(f.u, store)
        };
        let guard = f.not(guard_atom);
        let index_atom = f.eq(f.k, f.i);
        let index = f.not(index_atom);
        let conclusion = f.eq(read, f.x);
        assert_lowering_valid(case, &f, &[index, conclusion, guard]);
        let packed = f.or([guard, index, conclusion]);
        assert_lowering_valid(&format!("{case}_packed"), &f, &[packed]);
    }
}

/// The dispatch arm end to end: the exported certificate of a refutation
/// whose only theory step is the measured shape carries no `hole`.
#[test]
fn exported_certificate_is_hole_free_and_valid() {
    let mut f = Fixture::new();
    let probe = f.skolem();
    let left = f.store(f.v, f.i, f.x);
    let right = f.store(f.u, f.i, f.y);
    let index = f.eq(f.i, probe);
    let guard_atom = f.eq(left, right);
    let guard = f.not(guard_atom);
    let base_read = f.select(f.v, probe);
    let whole_read = f.select(right, probe);
    let conclusion = f.eq(base_read, whole_read);
    let packed = f.or([index, guard, conclusion]);
    let (problem, document) = export_refutation(&mut f.terms, packed);
    assert!(!document.contains(":rule hole"), "{document}");
    assert!(document.contains(":rule arrays_row"), "{document}");
    let mut remaining = SCREEN_WORK_BUDGET;
    assert!(checked_guarded_row_expansion_lowering_supported(
        &f.terms,
        &[packed],
        None,
        &mut remaining
    ));
    assert!(remaining < SCREEN_WORK_BUDGET, "the screen ask is charged");
    assert_verdict("exported", &problem, &document, "valid");
}

/// NEGATIVE: the screen's shared allowance is real. An allowance smaller than
/// the derivation's text, or an exhausted one, answers "not lowered" (the
/// screen keeps the gap), and so does a printer whose own budget the
/// derivation overruns. Counterfactual: with the derivation uncharged, every
/// ask below would answer `true`.
#[test]
fn exhausted_work_allowance_keeps_the_gap() {
    let mut f = Fixture::new();
    let store = f.store(f.v, f.i, f.x);
    let guard_atom = f.eq(f.u, store);
    let guard = f.not(guard_atom);
    let index = f.eq(f.i, f.k);
    let base_read = f.select(f.v, f.k);
    let read = f.select(f.u, f.k);
    let conclusion = f.eq(base_read, read);
    let clause = [guard, index, conclusion];
    let text = f.lowered(&clause).expect("lowerable guarded ROW expansion");
    let mut ample = SCREEN_WORK_BUDGET;
    assert!(checked_guarded_row_expansion_lowering_supported(
        &f.terms, &clause, None, &mut ample
    ));
    let cost = SCREEN_WORK_BUDGET - ample;
    assert!(
        cost >= text.len() as u64,
        "the derivation's text is charged"
    );
    let mut short = cost - 1;
    assert!(!checked_guarded_row_expansion_lowering_supported(
        &f.terms, &clause, None, &mut short
    ));
    let mut spent = 0;
    assert!(!checked_guarded_row_expansion_lowering_supported(
        &f.terms, &clause, None, &mut spent
    ));
    let printer = AlethePrinter::new_with_overrides_and_budget(&f.terms, None, Some(1));
    assert!(printer
        .format_array_guarded_row_expansion(ProofId(9), &clause)
        .is_none());
}

/// The strictly checked refutation `(not packed)` against the
/// `ArrayGuardedRowExpansion` lemma `packed`, exported.
fn export_refutation(terms: &mut TermStore, packed: TermId) -> (String, String) {
    let root = terms.mk_not_raw(packed);
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "array",
        vec![packed],
        TheoryLemmaKind::ArrayGuardedRowExpansion,
    );
    proof.add_resolution(vec![], packed, lemma, assume);
    crate::check_proof_strict(&proof, terms).expect("native strict validation");
    let document =
        crate::try_export_alethe_with_problem_scope_and_overrides(&proof, terms, &[root], None)
            .expect("Alethe export");
    let problem = format!(
        "{PRELUDE}(assert {})\n(check-sat)\n",
        crate::format_term_alethe(terms, root)
    );
    (problem, document)
}

/// NEGATIVE: the constant-array fold (the untouched cell spelled as the fill
/// `0`) is strictly valid, but no pinned rule reads a constant array, so the
/// export keeps the honest `hole` — Carcara answers `holey`, never `invalid`.
#[test]
fn constant_array_fill_keeps_the_hole() {
    let mut f = Fixture::new();
    let zero = f.terms.mk_int(0.into());
    let filled = f.terms.mk_const_array(Sort::Int, zero);
    let store = f.store(filled, f.i, f.x);
    let guard_atom = f.eq(f.u, store);
    let guard = f.not(guard_atom);
    let index = f.eq(f.i, f.k);
    let read = f.select(f.u, f.k);
    let conclusion = f.eq(zero, read);
    let packed = f.or([guard, index, conclusion]);
    assert!(crate::recognize_array_guarded_row_expansion(
        &f.terms,
        &[packed]
    ));
    assert!(f.lowered(&[packed]).is_none());
    let mut allowance = SCREEN_WORK_BUDGET;
    assert!(!checked_guarded_row_expansion_lowering_supported(
        &f.terms,
        &[packed],
        None,
        &mut allowance
    ));
    let (problem, document) = export_refutation(&mut f.terms, packed);
    assert!(document.contains(":rule hole"), "{document}");
    assert_verdict("constant_fill", &problem, &document, "holey");
}

/// NEGATIVE TWINS: one changed term makes each lowered shape falsifiable.
/// The strict validator refuses every one, and none gets a derivation.
#[test]
fn falsifiable_twins_get_no_derivation() {
    let mut f = Fixture::new();
    let store = f.store(f.v, f.i, f.x);
    let guard_atom = f.eq(f.u, store);
    let guard = f.not(guard_atom);
    let index = f.eq(f.i, f.k);
    let not_index = f.not(index);
    let mut twins = Vec::new();
    // The untouched cell read from the wrong base (`W`, not `V`).
    let wrong_base = f.select(f.w, f.k);
    let read = f.select(f.u, f.k);
    let conclusion = f.eq(wrong_base, read);
    twins.push(("wrong_base", vec![guard, index, conclusion]));
    // The untouched cell read at an index the guard never names.
    let base_at_x = f.select(f.v, f.x);
    let read_at_x = f.select(f.u, f.x);
    let conclusion = f.eq(base_at_x, read_at_x);
    twins.push(("wrong_probe", vec![guard, index, conclusion]));
    // The stored value read back as the OTHER value.
    let read_back = f.select(f.u, f.k);
    let conclusion = f.eq(f.y, read_back);
    twins.push(("wrong_value", vec![guard, not_index, conclusion]));
    // The guard's polarity flipped: `(= U S)` is not an assumption.
    let base_read = f.select(f.v, f.k);
    let conclusion = f.eq(base_read, read);
    twins.push(("positive_guard", vec![guard_atom, index, conclusion]));
    // A stored-value read-back under the untouched-cell polarity.
    let conclusion = f.eq(f.x, read);
    twins.push(("read_back_without_index", vec![guard, index, conclusion]));
    for (case, clause) in twins {
        assert!(
            !crate::recognize_array_guarded_row_expansion(&f.terms, &clause),
            "{case}: the strict validator must refuse the twin"
        );
        assert!(f.lowered(&clause).is_none(), "{case}");
    }
}

/// NEGATIVE: a surface override that is not the compositional rendering of
/// the certified store (its index re-spelled `(+ i 0)`) names a term the
/// conclusion's reads do not, so the lowering declines rather than emit
/// `arrays_row` over two different index spellings.
#[test]
fn non_compositional_store_surface_declines() {
    let mut f = Fixture::new();
    let store = f.store(f.v, f.i, f.x);
    let guard_atom = f.eq(f.u, store);
    let guard = f.not(guard_atom);
    let index = f.eq(f.i, f.k);
    let base_read = f.select(f.v, f.k);
    let read = f.select(f.u, f.k);
    let conclusion = f.eq(base_read, read);
    let clause = [guard, index, conclusion];
    assert!(f.lowered(&clause).is_some());
    let mut overrides = HashMap::default();
    overrides.insert(store, "(store V (+ i 0) x)".to_string());
    let printer = AlethePrinter::new_with_overrides_and_budget(&f.terms, Some(&overrides), None);
    assert!(printer
        .format_array_guarded_row_expansion(ProofId(9), &clause)
        .is_none());
    let mut allowance = SCREEN_WORK_BUDGET;
    assert!(!checked_guarded_row_expansion_lowering_supported(
        &f.terms,
        &clause,
        Some(&overrides),
        &mut allowance
    ));
}
