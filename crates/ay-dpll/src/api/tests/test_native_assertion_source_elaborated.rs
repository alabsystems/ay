// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native proof programs that retain an authored assertion elaboration
//! rewrote (deduplicated conjuncts, folded closed subterms, `(= p false)`,
//! pruned `false` disjuncts, lifted `ite` equalities, reoriented comparisons,
//! literal `(not true)`, closed bit-vector arithmetic).
//!
//! Each program was UNSAT with a strict artifact while the native API kept
//! only a placeholder, and became `unknown` or artifact-less once the
//! submitted source was retained. Every refutation below must publish a
//! strict artifact whose Alethe text assumes the exact authored assertion;
//! every mutant twin must stay satisfiable.

use crate::api::{Logic, ProofAcceptanceMode, Solver, Sort};
use ay_frontend::Command;

/// Declare every `declare-const` and assert every `assert` line of `input`
/// through the native API, retaining the line itself as the checked source.
fn solve_with_sources(input: &str) -> (Solver, Vec<String>) {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    solver.set_produce_proofs(true);
    let mut sources = Vec::new();
    for line in input.lines().filter(|line| !line.trim().is_empty()) {
        let mut commands = ay_frontend::parse(line).unwrap();
        assert_eq!(commands.len(), 1, "{line}");
        match commands.pop().unwrap() {
            Command::DeclareConst(name, sort) => {
                let sort = match format!("{sort:?}").as_str() {
                    text if text.contains("Bool") => Sort::Bool,
                    text if text.contains("Int") => Sort::Int,
                    other => panic!("fixture sort {other}"),
                };
                solver.declare_const(&name, sort);
            }
            Command::Assert(term) => {
                let id = solver
                    .executor
                    .context_mut_internal()
                    .elaborate_surface_subterm(&term)
                    .expect("fixture assertion elaborates");
                let native = solver.wrap_term(id);
                solver.try_assert_term_with_source(native, line).unwrap();
                sources.push(line.trim()["(assert ".len()..line.trim().len() - 1].to_string());
            }
            other => panic!("unexpected fixture command {other:?}"),
        }
    }
    (solver, sources)
}

fn assert_strict_refutation(input: &str) {
    let (mut solver, sources) = solve_with_sources(input);
    assert!(solver.check_sat().is_unsat(), "{input}");
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("an UNSAT native proof with retained sources publishes an artifact");
    artifact
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    for source in sources {
        assert!(
            artifact.alethe.contains(&format!("(assume t0 {source})"))
                || artifact.alethe.contains(&source),
            "the artifact must assume the authored assertion {source}:\n{}",
            artifact.alethe
        );
    }
}

fn assert_satisfiable(input: &str) {
    let (mut solver, _) = solve_with_sources(input);
    assert!(solver.check_sat().is_sat(), "{input}");
}

const INTS: &str = "(declare-const a Int)\n(declare-const k Int)\n(declare-const m Int)\n\
                    (declare-const n Int)\n(declare-const x Int)\n(declare-const i Int)\n";
const BOOLS: &str = "(declare-const p Bool)\n(declare-const q Bool)\n(declare-const r Bool)\n";

fn program(assertion: &str) -> String {
    format!("{INTS}{BOOLS}(assert {assertion})\n")
}

/// A repeated conjunct whose operand elaboration reorients (`(>= x 16)` to
/// `(<= 16 x)`): the deduplicating surgery must assume the exact authored
/// conjunction, not a canonical/raw hybrid.
#[test]
fn duplicated_conjunct_over_a_reoriented_comparison() {
    let refuted = "(and (= p (>= x 16)) (not (>= x 16)) (>= x 0) (<= x 4294967295) \
                   (<= i 4294967295) (= p (>= x 16)) (= i x) (= q (< i 16)) (>= i 16))";
    assert_strict_refutation(&program(refuted));
    assert_satisfiable(&program(&refuted.replace("(>= i 16)", "(>= i 15)")));
}

/// A repeated conjunct next to an equality the elaborator reorients.
#[test]
fn duplicated_conjunct_next_to_a_reoriented_equality() {
    let refuted = "(and (or (= a 0) (= a 1)) (>= k 0) (<= k 18446744073709551615) \
                   (or (= a 0) (= a 1)) (= m a) (= n m) (= r (< n 4)) (>= n 4))";
    assert_strict_refutation(&program(refuted));
    assert_satisfiable(&program(&refuted.replace("(>= n 4)", "(>= n 1)")));
}

/// `(=> (>= a 0) (= k a))` next to `(>= a 0)` elaborates to `(= k a)`.
#[test]
fn implication_discharged_by_a_sibling_conjunct() {
    let refuted = "(and (>= a 0) (<= a 3) (=> (>= a 0) (= k a)) \
                   (=> (not (>= a 0)) (= k (+ a 18446744073709551616))) (= m k) \
                   (= q (< m 4)) (>= m 4))";
    assert_strict_refutation(&program(refuted));
    assert_satisfiable(&program(&refuted.replace("(<= a 3)", "(<= a 4)")));
}

/// `(= p (= 2 0))` elaborates to `(not p)` and the closed `div`/`mod`/`ite`
/// operand to `2`.
#[test]
fn folded_closed_subterms_and_equality_with_false() {
    let refuted = "(and (= p (= 2 0)) (not p) (>= k 0) (= p (= 2 0)) \
                   (= m (div (- 4 (ite (>= 4 0) (mod 4 2) (- (mod (- 4) 2)))) 2)) \
                   (<= m 4) (= n m) (= q (< n 4)) (>= n 4))";
    assert_strict_refutation(&program(refuted));
    let mutant = refuted.replace(
        "(div (- 4 (ite (>= 4 0) (mod 4 2) (- (mod (- 4) 2)))) 2)",
        "(div (- 4 (ite (>= 4 0) (mod 4 2) (- (mod (- 4) 2)))) 1)",
    );
    assert_satisfiable(&program(&mutant));
}

/// A disjunct that folds to `false` is dropped, and `(= k (ite c u v))` is
/// lifted to `(ite c' (= k u) (= k v))` with a reoriented condition.
#[test]
fn pruned_false_disjunct_and_lifted_ite_equality() {
    let refuted = "(and (= p (= 4 0)) (not p) (>= a 0) (<= a 18446744073709551615) \
                   (or (= 4 0) (< k 4)) (= p (= 4 0)) \
                   (= k (ite (>= a 0) (mod a 4) (- (mod (- a) 4)))) (= q (< k 4)) (>= k 4))";
    assert_strict_refutation(&program(refuted));
    let mutant = refuted
        .replace("(< k 4)) (= p", "(< k 5)) (= p")
        .replace("(mod a 4) (- (mod (- a) 4))", "(mod a 5) (- (mod (- a) 5))");
    assert_satisfiable(&program(&mutant));
}

/// A literal `(not true)` conjunct.
#[test]
fn literal_not_true_conjunct() {
    let refuted = "(and (<= 0 (* x 2)) (= k (* x 2)) (<= 0 2) (not p) (= m n) (not true))";
    assert_strict_refutation(&program(refuted));
    assert_satisfiable(&program(&refuted.replace("(not true)", "(not false)")));
}

/// Nested term-level `ite` with negated conditions, a reoriented condition
/// and a normalized branch value.
#[test]
fn nested_ite_equality_lift() {
    let refuted = include_str!("native_assertion_source_fixtures/nested_ite_lift.smt2");
    assert_strict_refutation(refuted);
    let mutant = refuted.replace(
        "(ite (not (> width 0)) 0 (- width 1)) col)",
        "(ite (not (> width 0)) 0 (- width 1)) width)",
    );
    assert_ne!(mutant, refuted);
    assert_satisfiable(&mutant);
}

/// A congruence over a substituted variable whose defining equality is one
/// conjunct of the authored assertion, with `(- n)` bounds.
#[test]
fn congruence_through_an_authored_conjunct_equality() {
    let refuted = include_str!("native_assertion_source_fixtures/substituted_congruence.smt2");
    assert_strict_refutation(refuted);
    let mutant = refuted.replace("(< y 2)", "(< y 18446744073709551615)");
    assert_ne!(mutant, refuted);
    assert_satisfiable(&mutant);
}

/// A disjunction the elaborator reorders and whose comparison it reorients,
/// next to repeated bounds.
#[test]
fn permuted_disjunction_with_reoriented_comparison() {
    let refuted = include_str!("native_assertion_source_fixtures/permuted_disjunction.smt2");
    assert_strict_refutation(refuted);
    let mutant = refuted.replace("(<= _18 3)", "(<= _18 18446744073709551615)");
    assert_ne!(mutant, refuted);
    assert_satisfiable(&mutant);
}

/// Closed `bv2int`/`int2bv`/`extract`/`bvand` arithmetic that folds the whole
/// assertion to `false`.
#[test]
fn closed_bit_vector_arithmetic_fold() {
    let refuted = include_str!("native_assertion_source_fixtures/closed_bit_vector_fold.smt2");
    assert_strict_refutation(refuted);
    let mutant = refuted.replace("(not (= _0 3))", "(not (= _0 4))");
    assert_ne!(mutant, refuted);
    assert_satisfiable(&mutant);
}

/// A congruence whose premise equality is the consequent of an authored
/// implication discharged by a sibling conjunct.
#[test]
fn implied_equality_inside_a_congruence() {
    let refuted = include_str!("native_assertion_source_fixtures/implied_congruence_equality.smt2");
    assert_strict_refutation(refuted);
    let mutant = refuted.replace("(<= _4 3)", "(<= _4 4)");
    assert_ne!(mutant, refuted);
    assert_satisfiable(&mutant);
}

/// Nested conjunctions that elaboration flattens, inside a disjunction whose
/// other branch `(and false ...)` is pruned.
#[test]
fn flattened_conjunction_under_a_pruned_disjunction() {
    let refuted =
        include_str!("native_assertion_source_fixtures/flattened_pruned_disjunction.smt2");
    assert_strict_refutation(refuted);
    let mutant = refuted.replace("(<= x 1000)", "(<= x 4294967295)");
    assert_ne!(mutant, refuted);
    assert_satisfiable(&mutant);
}

/// Trust's `a[(i & 1) as usize]` bounds row over `[u8; 3]` (deductive-checksgen
/// `uninhabited_arm_realmir`, `live_arm_oob` fixture): no range on the index
/// (the function has no back edge), the global bitmask facts `_6 <= 1`,
/// `_10 <= 1`, the discriminant facts, a literal `true`, and the authored
/// `(bv2int (bvand ((_ int2bv 8) _4) ((_ int2bv 8) 1)))`, which elaboration
/// turns into `(mod _4 2)`. The dropped `true` shifts every conjunct index,
/// so the proof is re-homed onto the authored conjunction, and that needs a
/// checked link from the authored mask to the residue.
#[test]
fn masked_low_bit_index_residue() {
    let refuted = include_str!("native_assertion_source_fixtures/masked_low_bit_index.smt2");
    assert_strict_refutation(refuted);
    // `(i & 1) >= 1` holds at every odd `i`.
    let mutant = refuted.replace("(>= _5 3)", "(>= _5 1)");
    assert_ne!(mutant, refuted);
    assert_satisfiable(&mutant);
    // Without the bitmask fact, a mask of 3 reaches 3.
    let mutant = refuted.replace("(<= _6 1) ", "").replace(
        "((_ int2bv 8) _4) ((_ int2bv 8) 1)",
        "((_ int2bv 8) _4) ((_ int2bv 8) 3)",
    );
    assert_ne!(mutant, refuted);
    assert_satisfiable(&mutant);
}
