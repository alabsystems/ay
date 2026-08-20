// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The DT axiom expander's modus-ponens-collapsed ground facts are DERIVED,
//! not trusted, so proofs that consume them publish certified.
//!
//! `dt_selector_axioms_to_depth` asserts entailed UNITS whose premises it
//! drops at emission: the same-binding pairwise equality (`f(0) = mk-some(5)`
//! and `f(1) = mk-some(5)` gives `f(0) = f(1)`) and the equality-to-tester
//! fact (`s = mk-some(5)` gives `is-mk-some(s)`). Both used to be recorded as
//! bare `Generic` trust lemmas, so every UNSAT whose refutation consumed one
//! carried unverified fallback steps, mandatory certification demoted the
//! verdict to `proof-trusted`, and downstream embedders saw a genuine proof
//! degrade to `unknown` — measured end to end on verification-consumer's extern_spec
//! Option::unwrap obligation, whose bridge equality
//! `(= (bridge old_opt) (bridge opt))` is exactly the pairwise shape.
//!
//! The recording now derives each unit — an `EufTransitive` /
//! `EufCongruentPred` guarded tautology (plus a `DatatypeTesterEval` unit)
//! resolved against the `Assume`s of the asserted bindings — every step
//! re-checked by the UNCHANGED strict checker before publication. Both
//! fixtures were measured `unknown` before the derivation landed and `unsat`
//! after; the arithmetic coupling forces the refutation to CONSUME the
//! derived unit on the combined DT+LIA route (the axiom-based lane; pure
//! QF_DT solves interactively and never needed the axioms).

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const SAME_BINDING_PAIRWISE_EQ: &str = "\
(set-logic ALL)
(declare-datatype OptI ((mk-some (some-v Int)) (mk-none)))
(declare-fun f (Int) OptI)
(declare-const x Int)
(assert (= (f 0) (mk-some 5)))
(assert (= (f 1) (mk-some 5)))
(assert (=> (= (f 0) (f 1)) (> x 0)))
(assert (< x 0))
(check-sat)
";

const EQUALITY_TO_TESTER: &str = "\
(set-logic ALL)
(declare-datatype OptI ((mk-some (some-v Int)) (mk-none)))
(declare-const s OptI)
(declare-const x Int)
(assert (= s (mk-some 5)))
(assert (=> ((_ is mk-some) s) (> x 0)))
(assert (< x 0))
(check-sat)
";

fn assert_certified_unsat(smt: &str, label: &str) {
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let outputs = exec.execute_all(&commands).expect("execute_all");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{label}: the derived-unit lane must publish a certified UNSAT"
    );
    assert_eq!(
        exec.unknown_reason(),
        None,
        "{label}: a certified verdict must carry no withholding reason"
    );
}

#[test]
#[timeout(60_000)]
fn test_same_binding_pairwise_equality_publishes_certified_unsat() {
    assert_certified_unsat(SAME_BINDING_PAIRWISE_EQ, "same-binding pairwise eq");
}

#[test]
#[timeout(60_000)]
fn test_equality_to_tester_publishes_certified_unsat() {
    assert_certified_unsat(EQUALITY_TO_TESTER, "equality-to-tester");
}
