// Copyright 2026 Andrew Yates
// Binary DRAT format tests: end-to-end verification of proofs containing
// deletion steps encoded in binary format.

use super::*;
use crate::cnf_parser::parse_cnf;
use crate::drat_parser::{parse_drat, ProofStep};

/// Binary DRAT with deletion steps: encode a proof that uses both 'a' (add)
/// and 'd' (delete) markers, parse it, and verify through both forward and
/// backward checkers.
///
/// Formula: XOR-2 (UNSAT): (a v b), (~a v b), (a v ~b), (~a v ~b).
/// Proof: add(b), delete(a v b), add(~b), add(empty).
///
/// The deletion step exercises binary_format_tests delete parsing (0x64 marker)
/// and the checker's clause deletion path during proof verification.
#[test]
fn test_binary_drat_with_deletions_end_to_end() {
    let cnf_text = "\
p cnf 2 4
1 2 0
-1 2 0
1 -2 0
-1 -2 0
";
    // Binary DRAT proof with deletion:
    //   add(b):        0x61, LEB128(4)=0x04, 0x00
    //   delete(a, b):  0x64, LEB128(2)=0x02, LEB128(4)=0x04, 0x00
    //   add(~b):       0x61, LEB128(5)=0x05, 0x00
    //   add(empty):    0x61, 0x00
    //
    // Literal encoding: DIMACS lit n -> 2*n for positive, 2*|n|+1 for negative
    //   DIMACS  1 -> 2*(0+1)   = 2
    //   DIMACS  2 -> 2*(1+1)   = 4
    //   DIMACS -2 -> 2*(1+1)+1 = 5
    let proof_data: Vec<u8> = vec![
        0x61, 0x04, 0x00, // add (b)
        0x64, 0x02, 0x04, 0x00, // delete (a, b) — first use of 0x64 marker
        0x61, 0x05, 0x00, // add (~b)
        0x61, 0x00, // add (empty clause)
    ];

    let cnf = parse_cnf(cnf_text.as_bytes()).expect("CNF parse");
    let steps = parse_drat(&proof_data).expect("binary DRAT parse");
    assert_eq!(
        steps.len(),
        4,
        "expected 4 proof steps (add, delete, add, add)"
    );

    // Verify step types.
    assert!(
        matches!(&steps[0], ProofStep::Add(_)),
        "step 0 should be Add"
    );
    assert!(
        matches!(&steps[1], ProofStep::Delete(_)),
        "step 1 should be Delete"
    );
    assert!(
        matches!(&steps[2], ProofStep::Add(_)),
        "step 2 should be Add"
    );
    assert!(
        matches!(&steps[3], ProofStep::Add(_)),
        "step 3 should be Add (empty clause)"
    );

    // Forward checker
    let mut fwd = DratChecker::new(cnf.num_vars, false);
    let fwd_result = fwd.verify(&cnf.clauses, &steps);
    assert!(
        fwd_result.is_ok(),
        "forward must accept binary proof with deletions: {fwd_result:?}"
    );
    assert!(
        fwd.stats.deletions >= 1,
        "forward checker must process at least 1 deletion"
    );

    // Backward checker
    let mut bwd = backward::BackwardChecker::new(cnf.num_vars, false);
    let bwd_result = bwd.verify(&cnf.clauses, &steps);
    assert!(
        bwd_result.is_ok(),
        "backward must accept binary proof with deletions: {bwd_result:?}"
    );
}
