// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `benchmarks/smt/QF_ABV/wide_mul_unsat.smt2` over every index width: an
//! authored read-over-write that elaboration folds, refuted with `(= x 0)`.
//! The published refutation must render with no unproved step.
//!
//! MEASURED on 1c4ed9d77 with `:produce-proofs true` and `(get-proof)`: at
//! idx4, idx9, idx16 and idx32 the published proof was the guarded collapse's
//! joint `BvBitBlast` lemma over the raw authored roots, which keeps the
//! authored array read and prints as `hole`; `ay --strict-proofs --proof`
//! answered `unknown (incomplete proof-trusted)` there. Only idx7 and idx8
//! published the exact authored BV refutation (a complete blast bridged to the
//! read by `arrays_idx`), because the strict checker could not bit-blast the
//! read at those widths and refused the collapse. Once the checker can
//! bit-blast those reads, the collapse wins there too: measured with only
//! that checker change applied (a 413fa7ee3 build), idx7 and idx8 printed the
//! hole as well.
//!
//! This asks for the document `--strict-proofs` admits, not for the in-script
//! `:check-proofs-strict` verdict: that library gate still withholds this
//! answer through the conservative known-wire-gap screen, which reports every
//! multi-literal bit-blast lemma as a gap on purpose
//! (`ay_proof::alethe_printer::complete_blast::clause`).

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

#[test]
#[timeout(600_000)]
fn authored_read_over_write_conflict_clause_renders_without_an_unproved_step() {
    for index in [4, 7, 8, 9, 16, 32] {
        let label = format!("wide_mul idx{index}");
        let script = format!(
            "(set-option :produce-proofs true)\n\
             (set-logic QF_ABV)\n\
             (declare-fun a () (Array (_ BitVec {index}) (_ BitVec 32)))\n\
             (declare-fun x () (_ BitVec 32))\n\
             (declare-fun y () (_ BitVec 32))\n\
             (assert (= x #x00000000))\n\
             (assert (bvugt (select (store a (_ bv0 {index}) (bvmul x y)) (_ bv0 {index})) #x00000000))\n\
             (check-sat)\n\
             (get-proof)\n"
        );
        let commands = parse(&script).expect("fixture script must parse");
        let mut exec = Executor::new();
        let outputs = exec
            .execute_all(&commands)
            .expect("fixture script must run");
        let [verdict, proof] = outputs.as_slice() else {
            panic!("{label}: expected a verdict and a proof, got {outputs:?}");
        };
        assert_eq!(verdict, "unsat", "{label}");
        assert!(
            proof.contains("(assume ") && proof.contains("(cl)"),
            "{label}: expected an Alethe refutation, got:\n{proof}"
        );
        for gap in [":rule hole", ":rule trust"] {
            assert!(
                !proof.contains(gap),
                "{label}: the published proof must not rest on `{gap}`:\n{proof}"
            );
        }
        for rule in ["arrays_idx", "bitblast_mult"] {
            assert!(
                proof.contains(&format!(":rule {rule}")),
                "{label}: expected a `{rule}` step:\n{proof}"
            );
        }
    }
}
