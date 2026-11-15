// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A guarded read-over-write expansion exports as checked array rules.
//!
//! REGRESSION (measured 2026-10-08 at 8a0e18584, carcara 1.1.0 git 9a352ee,
//! plain invocation): `benchmarks/smt/QF_AUFLIA/storeinv_sf_size3.smt2`
//! answered `unsat` with `unproved_steps=2 foreign_assumes=no trust_free=no`
//! and pinned Carcara said `holey`; `--debug-cert` named both holes
//! `kind ArrayGuardedRowExpansion prints as hole`, the packed clauses
//! `(cl (or (= i3 k) (not (= S T)) (= (select V k) (select T k))))` with
//! `S = (store V i3 _)`. The printer had no lowering for the kind, so every
//! instance printed as `hole`. It now lowers to `arrays_row` / `arrays_idx` /
//! `cong` / `trans` (`ay-proof` `alethe_printer/guarded_row_expansion.rs`).
//! Those holes were also the only ones of `storeinv_nf_size4`,
//! `QF_AX/storeinv_cross_2idx_minimal` and `QF_AX/storeinv_cross_swap` (whose
//! probe is the `arrays_ext` choice term), so all four rows are pinned here.
//!
//! NEGATIVE CONTROLS live with the lowering (`guarded_row_expansion_tests.rs`):
//! the constant-array fill spelling, for which pinned Carcara has no rule,
//! keeps its honest `hole`, and every falsifiable twin gets no derivation.

use super::{exact_carcara_verdict, parse, require_carcara_or_skip, workspace_root, Executor};
use ntest::timeout;

/// The corpus rows whose only unproved steps were guarded ROW expansions.
const ROWS: &[&str] = &[
    "benchmarks/smt/QF_AUFLIA/storeinv_sf_size3.smt2",
    "benchmarks/smt/QF_AUFLIA/storeinv_nf_size4.smt2",
    "benchmarks/smt/QF_AX/storeinv_cross_2idx_minimal.smt2",
    "benchmarks/smt/QF_AX/storeinv_cross_swap.smt2",
];

#[test]
#[timeout(240_000)]
fn guarded_row_expansions_export_valid_certificates() {
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
                    kind: ay_core::TheoryLemmaKind::ArrayGuardedRowExpansion,
                    ..
                }
            )),
            "{row}: the refutation no longer rests on a guarded ROW expansion; re-pin the row"
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
