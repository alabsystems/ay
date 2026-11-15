// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ArithClauseTautology` equality chains: every lowered spelling replays
//! `valid` in pinned Carcara's PLAIN invocation and passes AY's own document
//! round trip; every clause outside the chain subset gets no lowering (the
//! caller's later lanes, then the honest `hole`).

use super::*;
use ay_core::{ProofStep, Sort, Symbol, TheoryLemmaKind};
use std::process::Command;

/// The declarations every fixture below may name.
const PRELUDE: &str = "(set-logic QF_AUFLIA)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)
(declare-fun x () Int)
";

struct Fixture {
    terms: TermStore,
}

impl Fixture {
    fn new() -> Self {
        Self {
            terms: TermStore::new(),
        }
    }

    fn int(&mut self, name: &str) -> TermId {
        self.terms.mk_var(name, Sort::Int)
    }

    fn array(&mut self, name: &str) -> TermId {
        self.terms.mk_var(name, Sort::array(Sort::Int, Sort::Int))
    }

    /// `(= left right)` in exactly this orientation (`mk_eq` canonicalises).
    fn eq(&mut self, left: TermId, right: TermId) -> TermId {
        self.terms
            .mk_app(Symbol::named("="), [left, right], Sort::Bool)
    }

    fn neq(&mut self, left: TermId, right: TermId) -> TermId {
        let equality = self.eq(left, right);
        self.terms.mk_not_raw(equality)
    }

    /// The producer's packed unit, disjuncts in exactly this order.
    fn or(&mut self, disjuncts: &[TermId]) -> TermId {
        self.terms
            .mk_app(Symbol::named("or"), disjuncts, Sort::Bool)
    }

    fn select(&mut self, array: TermId, index: TermId) -> TermId {
        self.terms
            .mk_app(Symbol::named("select"), [array, index], Sort::Int)
    }

    fn store(&mut self, array: TermId, index: TermId, value: TermId) -> TermId {
        let sort = self.terms.sort(array).clone();
        self.terms
            .mk_app(Symbol::named("store"), [array, index, value], sort)
    }

    fn lowered(&self, clause: &[TermId]) -> Option<String> {
        AlethePrinter::new(&self.terms).format_arith_equality_chain(ProofId(9), clause)
    }

    /// The whole theory-lemma step as the exporter prints it.
    fn printed_step(&self, clause: &[TermId]) -> Result<String, String> {
        let step = ProofStep::TheoryLemma {
            theory: "arith".to_string(),
            clause: clause.to_vec(),
            farkas: None,
            kind: TheoryLemmaKind::ArithClauseTautology,
            lia: None,
        };
        AlethePrinter::new(&self.terms)
            .format_step(&step, ProofId(9))
            .map_err(|error| error.to_string())
    }

    fn screened(&self, clause: &[TermId], overrides: Option<&DetHashMap<TermId, String>>) -> bool {
        let mut work = 8 * 1024 * 1024;
        arith_equality_chain_lowering_supported(&self.terms, clause, overrides, &mut work)
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
    let dir = std::env::temp_dir().join(format!("ay-arith-chain-{}-{case}", std::process::id()));
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

/// The lowered step `t9` closed against the negation of each of its clause
/// literals, asserted in the problem and assumed in the document; AY's own
/// round trip and pinned carcara must both accept it.
fn assert_lowering_valid(case: &str, fixture: &Fixture, clause: &[TermId]) -> String {
    assert!(
        crate::recognize_arith_clause_tautology(&fixture.terms, clause),
        "{case}: the fixture must be a strictly checked ArithClauseTautology"
    );
    let proof = fixture.lowered(clause).expect("an equality chain lowers");
    assert!(!proof.contains(":rule hole"), "{case}:\n{proof}");
    assert_eq!(
        Ok(proof.clone()),
        fixture.printed_step(clause),
        "{case}: the exporter's arm"
    );
    assert!(
        fixture.screened(clause, None),
        "{case}: the wire-gap screen"
    );
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
    let scope = crate::ProblemScope::from_smtlib_source(&problem);
    if let Err(defect) = crate::check_alethe_document(&document, &scope) {
        panic!("{case}: round-trip self-check refused the document: {defect}\n{document}");
    }
    if let Some(verdict) = carcara_verdict(case, &problem, &document, "valid") {
        let first = verdict.lines().next().unwrap_or("");
        assert_eq!(first, "valid", "{case}: {verdict}\n{document}");
    }
    proof
}

/// The measured `storeinv_sf_size7` leaf, exactly: an `Int` chain packed
/// into one `or`, conclusion last.
#[test]
fn measured_size7_packed_chain_replays_valid() {
    let mut f = Fixture::new();
    let [a1, a2] = [f.array("a1"), f.array("a2")];
    let probe = f.terms.mk_app(Symbol::named("sk"), [a1, a2], Sort::Int);
    let [i2, i3] = [f.int("i2"), f.int("i3")];
    let first = f.neq(i2, i3);
    let second = f.neq(i3, probe);
    let conclusion = f.eq(i2, probe);
    let unit = f.or(&[first, second, conclusion]);
    let proof = assert_lowering_valid("size7_packed", &f, &[unit]);
    let packed = "(or (not (= i2 i3)) (not (= i3 (sk a1 a2))) (= i2 (sk a1 a2)))";
    let expected = format!(
        "(step t9.et (cl (not (= i2 i3)) (not (= i3 (sk a1 a2))) (= i2 (sk a1 a2))) :rule eq_transitive)\n\
         (step t9.o0 (cl {packed} (not (not (= i2 i3)))) :rule or_neg :args (0))\n\
         (step t9.o1 (cl {packed} (not (not (= i3 (sk a1 a2))))) :rule or_neg :args (1))\n\
         (step t9.o2 (cl {packed} (not (= i2 (sk a1 a2)))) :rule or_neg :args (2))\n\
         (step t9 (cl {packed}) :rule resolution :premises (t9.et t9.o0 t9.o1 t9.o2))"
    );
    assert_eq!(proof, expected);
}

/// The measured `storeinv_sf_size5` mechanism: reads over stores, the
/// conclusion the SECOND disjunct and the hypotheses out of chain order.
/// The chain step moves only the conclusion; every `or_neg` quotes the
/// recorded disjunct order.
#[test]
fn measured_size5_conclusion_inside_the_packed_unit_replays_valid() {
    let mut f = Fixture::new();
    let [a1, a2] = [f.array("a1"), f.array("a2")];
    let probe = f.terms.mk_app(Symbol::named("sk"), [a1, a2], Sort::Int);
    let [i1, i2] = [f.int("i1"), f.int("i2")];
    let read_a2_i1 = f.select(a2, i1);
    let v1 = f.store(a1, i1, read_a2_i1);
    let read_v1_i2 = f.select(v1, i2);
    let v3 = f.store(v1, i2, read_v1_i2);
    let read_a1_i1 = f.select(a1, i1);
    let v0 = f.store(a2, i1, read_a1_i1);
    let [r_a1, r_a2, r_v0, r_v1, r_v3] = [a1, a2, v0, v1, v3].map(|array| f.select(array, probe));
    let first = f.neq(r_a2, r_v0);
    let conclusion = f.eq(r_a1, r_a2);
    let third = f.neq(r_v3, r_v1);
    let fourth = f.neq(r_a1, r_v1);
    let fifth = f.neq(r_v3, r_v0);
    let unit = f.or(&[first, conclusion, third, fourth, fifth]);
    let proof = assert_lowering_valid("size5_packed", &f, &[unit]);
    let first_line = proof.lines().next().unwrap_or("");
    assert!(
        first_line
            .ends_with("(= (select a1 (sk a1 a2)) (select a2 (sk a1 a2)))) :rule eq_transitive)"),
        "{proof}"
    );
    assert!(proof.contains(":rule or_neg :args (1))"), "{proof}");
}

/// A flat clause already in carcara's order is the plain rule.
#[test]
fn flat_chain_with_its_conclusion_last_is_one_eq_transitive_step() {
    let mut f = Fixture::new();
    let [a, b, c] = [f.int("a"), f.int("b"), f.int("c")];
    let clause = [f.neq(b, a), f.neq(c, b), f.eq(a, c)];
    let proof = assert_lowering_valid("flat_last", &f, &clause);
    assert_eq!(
        proof,
        "(step t9 (cl (not (= b a)) (not (= c b)) (= a c)) :rule eq_transitive)"
    );
}

/// A flat clause with its conclusion first is the reordered chain plus one
/// `reordering` back to the recorded literal order.
#[test]
fn flat_chain_with_its_conclusion_first_is_reordered_back() {
    let mut f = Fixture::new();
    let [a, b, c, d] = [f.int("a"), f.int("b"), f.int("c"), f.int("d")];
    let clause = [f.eq(d, a), f.neq(a, b), f.neq(c, d), f.neq(b, c)];
    let proof = assert_lowering_valid("flat_first", &f, &clause);
    assert_eq!(
        proof,
        "(step t9.et (cl (not (= a b)) (not (= c d)) (not (= b c)) (= d a)) :rule eq_transitive)\n\
         (step t9 (cl (= d a) (not (= a b)) (not (= c d)) (not (= b c))) :rule reordering :premises (t9.et))"
    );
}

/// NEGATIVE TWIN of the packed lanes: a positive equality that the
/// hypotheses do not connect is no chain, whatever its order. The clause is
/// not a tautology, so it must not lower (and the screen keeps the gap).
#[test]
fn a_disconnected_chain_gets_no_lowering() {
    let mut f = Fixture::new();
    let [a, b, c, d] = [f.int("a"), f.int("b"), f.int("c"), f.int("d")];
    let [first, second, conclusion] = [f.neq(a, b), f.neq(c, d), f.eq(a, d)];
    let unit = f.or(&[first, conclusion, second]);
    assert!(!crate::recognize_arith_clause_tautology(&f.terms, &[unit]));
    assert_eq!(f.lowered(&[unit]), None);
    assert!(!f.screened(&[unit], None));
    assert_eq!(f.lowered(&[first, conclusion, second]), None);
}

/// NEGATIVE TWIN: a valid arithmetic tautology that is not an equality
/// chain — two positive equalities, or an order literal — keeps every later
/// lane and never prints `eq_transitive`.
#[test]
fn arithmetic_tautologies_outside_the_chain_subset_are_left_to_later_lanes() {
    let mut f = Fixture::new();
    let [a, b, c, x] = [f.int("a"), f.int("b"), f.int("c"), f.int("x")];
    // (a = b) ∨ ¬(a = b) ∨ (b = c): two positive equalities.
    let [positive, negative, other] = [f.eq(a, b), f.neq(a, b), f.eq(b, c)];
    let unit = f.or(&[positive, negative, other]);
    assert_eq!(f.lowered(&[unit]), None);
    assert!(!f.screened(&[unit], None));
    // ¬(x <= 0) ∨ (x <= 1): an order tautology with no equality at all.
    let zero = f.terms.mk_int(0.into());
    let one = f.terms.mk_int(1.into());
    let le_zero = f.terms.mk_app(Symbol::named("<="), [x, zero], Sort::Bool);
    let le_one = f.terms.mk_app(Symbol::named("<="), [x, one], Sort::Bool);
    let clause = [f.terms.mk_not_raw(le_zero), le_one];
    assert!(crate::recognize_arith_clause_tautology(&f.terms, &clause));
    assert_eq!(f.lowered(&clause), None);
    assert!(!f
        .printed_step(&clause)
        .unwrap_or_default()
        .contains("eq_transitive"));
    // An arithmetic link in place of an equality hypothesis: ¬(a = b) ∨
    // ¬(b <= c) ∨ ¬(c <= b) ∨ (a = c) is LIA-valid but no `eq_transitive`.
    let [ab, bc_le, cb_le, ac] = [
        f.neq(a, b),
        f.terms.mk_app(Symbol::named("<="), [b, c], Sort::Bool),
        f.terms.mk_app(Symbol::named("<="), [c, b], Sort::Bool),
        f.eq(a, c),
    ];
    let clause = [ab, f.terms.mk_not_raw(bc_le), f.terms.mk_not_raw(cb_le), ac];
    assert!(crate::recognize_arith_clause_tautology(&f.terms, &clause));
    assert_eq!(f.lowered(&clause), None);
    assert!(!f
        .printed_step(&clause)
        .unwrap_or_default()
        .contains("eq_transitive"));
}

/// NEGATIVE TWIN of the surface: over the term DAG this is the chain
/// a = b, b = c |- a = c, but the source surface re-spells one hypothesis
/// so the PRINTED text no longer chains. The judge reads the text, so the
/// lemma is refused by both the printer and the screen.
#[test]
fn a_printed_surface_that_breaks_the_chain_gets_no_lowering() {
    let mut f = Fixture::new();
    let [a, b, c] = [f.int("a"), f.int("b"), f.int("c")];
    let [first, second, conclusion] = [f.neq(a, b), f.neq(b, c), f.eq(a, c)];
    let unit = f.or(&[first, second, conclusion]);
    let mut overrides = DetHashMap::default();
    let eq_bc = f.eq(b, c);
    overrides.insert(eq_bc, "(= (ite (not (= b c)) 1 0) 0)".to_string());
    let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&overrides));
    assert_eq!(
        printer.format_arith_equality_chain(ProofId(9), &[unit]),
        None
    );
    assert!(!f.screened(&[unit], Some(&overrides)));
    assert!(
        f.screened(&[unit], None),
        "the twin without the re-spelling"
    );
}

/// The packed repack is charged BEFORE it is built: a budget that covers
/// rendering the unit and one more quote of it, not the five the repack
/// makes, declines the lowering (the step boundary then discards the
/// document), and the screen keeps the gap under the same allowance while
/// still charging the declined ask. An allowance of zero is refused before
/// any rendering. Counterfactual: without the charge, rendering alone fits
/// the budget and both lower.
#[test]
fn the_packed_repack_is_charged_against_the_work_budget() {
    let mut f = Fixture::new();
    let [a, b, c] = [f.int("a"), f.int("b"), f.int("c")];
    let [first, second, conclusion] = [f.neq(a, b), f.neq(b, c), f.eq(a, c)];
    let unit = f.or(&[first, second, conclusion]);
    let render = AlethePrinter::new(&f.terms);
    let printed = render.format_derived_literal(unit);
    let rendering = render.work_used();
    let quote = printed.len() as u64;
    let budget = rendering + quote;
    let bounded = AlethePrinter::new_with_overrides_and_budget(&f.terms, None, Some(budget));
    assert_eq!(
        bounded.format_arith_equality_chain(ProofId(9), &[unit]),
        None
    );
    assert!(bounded.work_budget_exhausted());
    let mut work = budget;
    assert!(!arith_equality_chain_lowering_supported(
        &f.terms,
        &[unit],
        None,
        &mut work
    ));
    assert!(work < budget, "the declined ask is still charged");
    let unbounded = AlethePrinter::new(&f.terms);
    assert!(unbounded
        .format_arith_equality_chain(ProofId(9), &[unit])
        .is_some());
    assert!(unbounded.work_used() >= rendering + 5 * quote);
    let mut exhausted = 0;
    assert!(!arith_equality_chain_lowering_supported(
        &f.terms,
        &[unit],
        None,
        &mut exhausted
    ));
}
