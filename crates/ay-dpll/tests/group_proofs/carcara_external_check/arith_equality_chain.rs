// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An `ArithClauseTautology` that is an equality chain exports as a checked
//! `eq_transitive` derivation.
//!
//! REGRESSION (measured 2026-10-09 at 2fc273d06, carcara 1.1.0 git 9a352ee,
//! plain invocation): `benchmarks/smt/QF_AUFLIA/storeinv_sf_size7.smt2`
//! answered `unsat` with `unproved_steps=1` and pinned Carcara said `holey`;
//! `--debug-cert` named the hole `wire downgrade at ProofId(618): kind
//! ArithClauseTautology prints as hole`, the packed congruence explanation
//! `(cl (or (not (= i2 i3)) (not (= i3 (sk a1 a2))) (= i2 (sk a1 a2))))`.
//! `storeinv_sf_size5`'s one hole (ProofId(198)) is an eleven-disjunct chain
//! over `select` reads with its positive equality SECOND. The finalize-time
//! intrinsic battery files such `Int` chains as `ArithClauseTautology`, and
//! no arithmetic lowering could spell them. They now lower to
//! `eq_transitive` + `or_neg` + `resolution` (`ay-proof`
//! `alethe_printer_eq_transitive_arith.rs`). The same holes were the only
//! ones of the five other rows below, so all seven are pinned here.
//!
//! NEGATIVE CONTROLS live with the lowering
//! (`alethe_printer_eq_transitive_arith_tests.rs`): a disconnected chain, two
//! positive equalities, an order literal, a re-spelled surface and an
//! exhausted screen allowance all get no derivation.

use super::{exact_carcara_verdict, parse, require_carcara_or_skip, workspace_root, Executor};
use ntest::timeout;

/// The corpus rows whose only unproved steps were equality-chain
/// `ArithClauseTautology` lemmas.
const ROWS: &[&str] = &[
    "benchmarks/smt/QF_AUFLIA/storeinv_sf_size5.smt2",
    "benchmarks/smt/QF_AUFLIA/storeinv_sf_size7.smt2",
    "benchmarks/smt/QF_AUFLIA/storeinv_nf_size2_nosk.smt2",
    "benchmarks/smt/QF_AUFLIA/storeinv_nf_size3.smt2",
    "benchmarks/smt/QF_AUFLIA/storeinv_nf_size5.smt2",
    "benchmarks/smt/QF_AUFLIA/storeinv_nf_size7.smt2",
    "benchmarks/smt/QF_AUFLIA/storeinv_crossswap_flat.smt2",
];

#[test]
#[timeout(240_000)]
fn arith_equality_chains_export_valid_certificates() {
    let carcara = require_carcara_or_skip();
    for row in ROWS {
        let path = workspace_root().join(row);
        let problem = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {row}: {e}"));
        let session = problem
            .lines()
            .filter(|line| line.trim() != "(exit)")
            .collect::<Vec<_>>()
            .join("\n");
        let script = format!("(set-option :produce-proofs true)\n{session}\n");
        let commands = parse(&script).unwrap_or_else(|e| panic!("{row}: {e}"));
        let mut exec = Executor::new();
        let outputs = exec
            .execute_all(&commands)
            .unwrap_or_else(|e| panic!("{row}: {e}"));
        assert_eq!(
            outputs.last().map(String::as_str),
            Some("unsat"),
            "{row}: {:?}",
            exec.unknown_reason()
        );
        let proof = exec
            .last_proof()
            .unwrap_or_else(|| panic!("{row}: no retained proof"));
        assert!(
            proof.steps.iter().any(|step| matches!(
                step,
                ay_core::ProofStep::TheoryLemma {
                    kind: ay_core::TheoryLemmaKind::ArithClauseTautology,
                    ..
                }
            )),
            "{row}: the refutation no longer rests on an arithmetic tautology; re-pin the row"
        );
        let (document, _surface) = exec
            .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
            .unwrap_or_else(|| panic!("{row}: no retained proof"))
            .unwrap_or_else(|e| panic!("{row}: {e}"));
        assert!(
            !document.contains(":rule hole") && !document.contains(":rule trust"),
            "{row}: {document}"
        );
        if let Some(carcara) = carcara.as_deref() {
            let (valid, why) = exact_carcara_verdict(carcara, &problem, &document);
            assert!(valid, "{row}: {why}\n{document}");
        }
    }
}
