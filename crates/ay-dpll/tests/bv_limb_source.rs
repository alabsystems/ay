// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! external-codegen's i128 multiply lowering (gate row 2023), at 8-bit limbs: a
//! product of two-limb `concat`s against the schoolbook sum of its partial
//! products, with the carry limb spelled as the high half of a widened
//! product. The identity is decided by the limb fold of the BV normalizer and
//! certified over its limbs: one bit-blast lemma for the limb facts, ring
//! steps that `poly_simp` replays, congruence and one transitivity chain.

use ay_dpll::Executor;
use ay_frontend::parse;

const LOWERING: &str = "(set-logic QF_BV)
(declare-const a_lo (_ BitVec 8))
(declare-const a_hi (_ BitVec 8))
(declare-const b_lo (_ BitVec 8))
(declare-const b_hi (_ BitVec 8))
(assert (not (= (bvmul (concat a_hi a_lo) (concat b_hi b_lo)) (concat (bvadd (bvadd ((_ extract 15 8) (bvmul ((_ zero_extend 8) a_lo) ((_ zero_extend 8) b_lo))) (bvmul a_hi b_lo)) (bvmul a_lo b_hi)) (bvmul a_lo b_lo)))))
(check-sat)
";

fn solve(input: &str, proofs: bool) -> Vec<String> {
    let query = if proofs {
        format!("{input}(get-proof)\n")
    } else {
        input.to_string()
    };
    let mut executor = Executor::new();
    executor.set_produce_proofs(proofs);
    executor.execute_all(&parse(&query).unwrap()).unwrap()
}

#[test]
fn a_two_limb_product_is_certified_over_its_limbs() {
    let outputs = solve(LOWERING, true);
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs.get(1).expect("published proof");
    for rule in [
        ":rule poly_simp",
        ":rule eq_congruent",
        ":rule eq_transitive",
    ] {
        assert!(proof.contains(rule), "missing {rule}: {proof}");
    }
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
}

#[test]
fn a_wrong_carry_limb_is_refuted() {
    // The carry of `a_hi * b_lo` is not the carry of `a_lo * b_lo`.
    let input = LOWERING.replacen(
        "((_ zero_extend 8) a_lo) ((_ zero_extend 8) b_lo)",
        "((_ zero_extend 8) a_hi) ((_ zero_extend 8) b_lo)",
        1,
    );
    assert_ne!(input, LOWERING);
    let outputs = solve(&input, false);
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}
