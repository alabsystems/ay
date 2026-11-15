// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The QSAT route's `unsat` documents check `valid` in pinned carcara.
//!
//! Measured on the branch that introduced the route (0807e0828), each of these
//! published `unsat` with a document pinned carcara 1.1.0 rejects (`invalid`
//! at its first `assume`: AY's canonical `(or p q)` for the authored `(not
//! (and (not p) (not q)))`, `(or q (not p))` for `(=> p q)`) or with no
//! document at all (a negated existential's `qnt_neg_exists` dual over an
//! alpha-renamed binder; an alternation's `forall_inst` over a body that
//! still binds `y`). The route now publishes only a document AY renders
//! complete and verbatim; this pins that the external checker agrees.

use super::{exact_carcara_verdict, require_carcara_or_skip, solve_unsat_and_get_proof};
use ntest::timeout;

const FIXTURES: [(&str, &str); 5] = [
    (
        "qsat_not_and",
        "(set-logic LIA)(declare-fun p () Bool)(declare-fun q () Bool)\
         (assert (not (and (not p) (not q))))(assert (not p))(assert (not q))\
         (assert (forall ((x Int)) (> (+ x 1) x)))(check-sat)",
    ),
    (
        "qsat_implies",
        "(set-logic LIA)(declare-fun p () Bool)(declare-fun q () Bool)\
         (assert (=> p q))(assert p)(assert (not q))\
         (assert (forall ((x Int)) (> (+ x 1) x)))(check-sat)",
    ),
    (
        "qsat_not_exists",
        "(set-logic LIA)(assert (not (exists ((x Int)) (< x 13))))(check-sat)",
    ),
    (
        "qsat_not_exists_eq",
        "(set-logic LIA)(declare-fun a () Int)(assert (not (exists ((x Int)) (= x a))))(check-sat)",
    ),
    (
        "qsat_alternation",
        "(set-logic LIA)(declare-fun a () Int)\
         (assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (< y (+ x a))))))\
         (assert (< a 2))(check-sat)",
    ),
];

#[test]
#[timeout(120_000)]
fn qsat_unsat_documents_check_valid() {
    for (label, problem) in FIXTURES {
        let proof = solve_unsat_and_get_proof(problem, label);
        assert!(
            !proof.contains(":rule hole") && !proof.contains(":rule trust"),
            "{label}:\n{proof}"
        );
        if let Some(carcara) = require_carcara_or_skip() {
            let (valid, diagnostic) = exact_carcara_verdict(&carcara, problem, &proof);
            assert!(
                valid,
                "{label}: pinned carcara must check the document: {diagnostic}\n{proof}"
            );
        }
    }
}
