// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `forall-int-unsat` under `--strict-proofs`: a universal whose body the
//! store folds to `false` is published `unsat` on a hole-free certificate.
//!
//! `(forall ((q Int)) (not (= q q)))` is false in every model. AY refutes it
//! through its Skolem instance, and the instance is the store's `false`. The
//! printer used to spell that shared `false` with the authored instance text
//! everywhere, so the `false` axiom printed as `(not (not (= c c)))`, was
//! demoted to `:rule hole`, and `--strict-proofs` withheld the verdict as
//! `unknown` (MEASURED at bca3b7c78, both spellings below). The anchor now
//! derives `(= (not (= q q)) false)` with `eq_simplify`, `cong`,
//! `not_simplify` and `trans`, and the instance keeps the constant's
//! spelling (`alethe_printer/constant_skolem_bridge.rs` in `ay-proof`).

use ntest::timeout;
use std::io::Write as _;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

/// The query, in the plain spelling and in Trust's binder spelling.
const FORALL_INT_UNSAT: [&str; 2] = [
    "(set-logic LIA)\n(assert (forall ((q Int)) (not (= q q))))\n(check-sat)\n",
    "(set-logic LIA)\n\
     (assert (forall ((__trust_u_q Int)) (not (= __trust_u_q __trust_u_q))))\n\
     (check-sat)\n",
];

#[test]
#[timeout(120_000)]
fn strict_proofs_publish_forall_int_unsat_on_a_hole_free_certificate() {
    for script in FORALL_INT_UNSAT {
        let dir = tempfile::tempdir().expect("tempdir");
        let smt2 = dir.path().join("query.smt2");
        let proof = dir.path().join("query.smt2.alethe");
        let mut file = std::fs::File::create(&smt2).expect("create query file");
        file.write_all(script.as_bytes()).expect("write query");
        file.write_all(b"(exit)\n").expect("write exit");
        drop(file);
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("-smt2")
            .arg(&smt2)
            .arg("--strict-proofs")
            .arg("--proof")
            .arg(&proof)
            .args(["--proof-format", "alethe"])
            .output_timeout(Duration::from_secs(60))
            .expect("run ay one-shot");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let context = format!(
            "{script}(exit {:?})\nstdout:\n{stdout}\nstderr:\n{stderr}",
            output.status
        );
        assert!(output.status.success(), "{context}");
        let verdicts: Vec<&str> = stdout
            .lines()
            .map(str::trim)
            .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
            .collect();
        assert_eq!(verdicts, ["unsat"], "{context}");
        let certificate = stderr
            .lines()
            .find(|line| line.contains("c ay.proof.certificate "))
            .unwrap_or_else(|| panic!("published unsat without a certificate line: {context}"));
        for field in ["unproved_steps=0", "foreign_assumes=no", "trust_free=yes"] {
            assert!(
                certificate.split_whitespace().any(|word| word == field),
                "strict unsat without {field}: {context}"
            );
        }
        let document = std::fs::read_to_string(&proof).expect("read the published certificate");
        assert!(
            !document.contains(":rule hole") && !document.contains(":rule trust"),
            "{context}\n{document}"
        );
        assert!(
            document.contains(":rule sko_forall)")
                && document.contains("(cl (not false)) :rule false)"),
            "{context}\n{document}"
        );
    }
}
