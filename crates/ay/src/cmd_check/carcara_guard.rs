// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay check carcara-guard PROOF PROBLEM`: the pinned-Carcara misjudgment scan
//! (`ay_core::pinned_carcara`) for the scripts that run Carcara themselves
//! (`scripts/check_proofs.sh`, `scripts/evidence_gate.sh`,
//! `scripts/carcara_conformance.py`), so they refuse exactly what every Rust
//! gate refuses without a second implementation of the scan.
//!
//! Pinned carcara 1.1.0 prints `valid` for some refutations of SATISFIABLE
//! problems: through an `evaluate` step it computes wrongly, through a binder
//! it reads as capturing a `:named` label or `define-fun`, or through an
//! `aci_simp` step that drops a repeat of a non-idempotent operator. On such a
//! pair its verdict is not evidence in either direction. Exit 0 with
//! `pinned-carcara-guard: clean` when no scan flags the pair, exit 1 with
//! `pinned-carcara-guard: refused` and one line per flagged step or binder
//! otherwise; an unreadable file is an error (non-zero), never clean.

use std::fmt::Write as _;
use std::io::Write as _;
use std::path::Path;

use anyhow::Context;

pub(super) fn run(proof: &Path, problem: &Path) -> anyhow::Result<()> {
    let read = |path: &Path| {
        std::fs::read_to_string(path).with_context(|| format!("cannot read '{}'", path.display()))
    };
    let (clean, report) = guard_report(&read(problem)?, &read(proof)?);
    let mut out = std::io::stdout();
    out.write_all(report.as_bytes())?;
    out.flush()?;
    std::process::exit(if clean { 0 } else { 1 });
}

/// Whether the pair is clean, and the report the command prints.
fn guard_report(problem: &str, proof: &str) -> (bool, String) {
    let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) else {
        return (true, "pinned-carcara-guard: clean\n".to_string());
    };
    let mut report = String::from(
        "pinned-carcara-guard: refused (pinned Carcara's verdict on this pair is not evidence)\n",
    );
    for step in &misjudged.evaluate_steps {
        let step = step.split_whitespace().collect::<Vec<_>>().join(" ");
        let _ = writeln!(report, "misjudged-evaluate: {step}");
    }
    for (bound, definition) in &misjudged.binders {
        let _ = writeln!(report, "misread-binder: `{bound}` against `{definition}`");
    }
    for step in &misjudged.aci_simp_steps {
        let step = step.split_whitespace().collect::<Vec<_>>().join(" ");
        let _ = writeln!(report, "misjudged-aci-simp: {step}");
    }
    (false, report)
}

#[cfg(test)]
mod tests {
    use super::guard_report;
    use ay_core::pinned_carcara::{
        FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM, FALSE_VALID_ACI_SIMP_CONTROL_PROOF,
        FALSE_VALID_CONTROL_PROBLEM, FALSE_VALID_CONTROL_PROOF,
    };

    /// NEGATIVE CONTROL: the pair pinned Carcara prints `valid` for only
    /// through its `evaluate` defect is refused, naming the step on one line;
    /// a binder capture is refused too; a clean pair is clean.
    #[test]
    fn the_guard_refuses_what_pinned_carcara_misjudges_and_passes_the_rest() {
        let (clean, report) = guard_report(FALSE_VALID_CONTROL_PROBLEM, FALSE_VALID_CONTROL_PROOF);
        assert!(!clean, "{report}");
        assert_eq!(
            report,
            "pinned-carcara-guard: refused (pinned Carcara's verdict on this pair is not \
             evidence)\nmisjudged-evaluate: (step t1 (cl (= (bvsge #xf #xe) false)) :rule \
             evaluate)\n"
        );
        let capture = "(declare-const y Int)\n(assert (! (= y 0) :named n))\n\
                       (assert (forall ((y Int)) n))\n";
        let (clean, report) = guard_report(capture, "");
        assert!(
            !clean && report.ends_with("misread-binder: `y` against `n`\n"),
            "{report}"
        );
        let (clean, report) = guard_report(
            FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM,
            FALSE_VALID_ACI_SIMP_CONTROL_PROOF,
        );
        assert!(
            !clean
                && report.ends_with(
                    "misjudged-aci-simp: (step t1 (cl (= (bvmul a a) a)) :rule aci_simp)\n"
                ),
            "{report}"
        );
        let (clean, report) = guard_report(
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n",
            "(assume h1 p)\n(assume h2 (not p))\n(step t3 (cl) :rule resolution :premises (h1 h2))\n",
        );
        assert!(clean, "{report}");
        assert_eq!(report, "pinned-carcara-guard: clean\n");
    }

    /// The harness self-test's fake solver only replays the guard verdict a
    /// fixture spells out (`; AY-GUARD: refused`, default clean). Every
    /// `benchmarks/proof-fixtures/checker` fixture's directive must be what
    /// the REAL guard answers on its embedded proof, so the two cannot drift;
    /// and the set must hold a refused one (`c10_misjudged_valid`).
    #[test]
    fn every_harness_fixture_spells_the_real_guard_verdict() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../benchmarks/proof-fixtures/checker");
        let mut refused = Vec::new();
        for entry in std::fs::read_dir(&directory).expect("the harness fixtures") {
            let path = entry.expect("fixture entry").path();
            if path.extension().and_then(|e| e.to_str()) != Some("smt2") {
                continue;
            }
            let text = std::fs::read_to_string(&path).expect("fixture text");
            let mut proof = String::new();
            for line in text.lines().filter_map(|line| line.strip_prefix(";| ")) {
                proof.push_str(line);
                proof.push('\n');
            }
            let (clean, report) = guard_report(&text, &proof);
            let spelled = text
                .lines()
                .any(|line| line.trim() == "; AY-GUARD: refused");
            assert_eq!(!clean, spelled, "{}: {report}", path.display());
            if spelled {
                refused.push(path.file_name().map(|n| n.to_string_lossy().into_owned()));
            }
        }
        assert_eq!(refused, vec![Some("c10_misjudged_valid.smt2".to_string())]);
    }
}
