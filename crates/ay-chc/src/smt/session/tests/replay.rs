// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Design §8 / §10.1 Rung 1 — `replay`: the dumped PDR query corpora
//! (`crates/ay-chc/tests/fixtures/session_replay/<key>/`, gzip'd
//! concatenations of the microbenchmark's `q_*.smt2` files with their
//! `index.tsv`) in corpus order through the warm production router path vs a
//! fresh legacy context per query vs z3 vs the recorded verdicts.
//!
//! The corpora are materialised with the system `gzip` (no decompression
//! crate in the tree); a machine without it skips with a message.
//! `AY_REPLAY_LIMIT` caps queries per corpus (0 = all, the default);
//! `AY_REPLAY_KEYS` selects corpora (comma-separated).

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use crate::smt::lane::ScopedSessionMode;
use crate::smt::session::harness::{parse_script_assertions, run_pushpop_files, run_replay};
use crate::smt::{SmtContext, SmtResult};

fn fixtures_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("session_replay")
}

/// Expand `<key>/queries.smt2.gz` (records separated by `;; @file <name>`
/// lines) into `<tmp>/<key>/q_*.smt2` next to a copy of `index.tsv`.
fn materialize(key: &str) -> Option<tempfile::TempDir> {
    let src = fixtures_root().join(key);
    let gz = src.join("queries.smt2.gz");
    if !gz.exists() {
        eprintln!("[replay] no fixture for {key} at {}", gz.display());
        return None;
    }
    let out = Command::new("gzip").arg("-dc").arg(&gz).output().ok()?;
    if !out.status.success() {
        eprintln!("[replay] gzip failed for {key}; skipping");
        return None;
    }
    let text = String::from_utf8_lossy(&out.stdout);
    let dir = tempfile::tempdir().ok()?;
    let corpus_dir = dir.path().join(key);
    std::fs::create_dir_all(&corpus_dir).ok()?;
    let mut name: Option<String> = None;
    let mut body = String::new();
    let mut flush = |name: &Option<String>, body: &mut String| {
        if let Some(n) = name {
            std::fs::write(corpus_dir.join(n), body.as_bytes()).expect("write query");
        }
        body.clear();
    };
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix(";; @file ") {
            flush(&name, &mut body);
            name = Some(rest.trim().to_owned());
        } else {
            body.push_str(line);
            body.push('\n');
        }
    }
    flush(&name, &mut body);
    if let Ok(index) = std::fs::read(src.join("index.tsv")) {
        std::fs::write(corpus_dir.join("index.tsv"), index).ok()?;
    }
    Some(dir)
}

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|v| v.trim().parse().ok())
        .unwrap_or(default)
}

/// The 17 om1relays queries the ay-dpll push/pop lane answered `unsat`
/// (all satisfiable) in the 2026-09-18 microbenchmark (§5.1 of
/// the development design notes at `9598c4206`; design §7.3 (ii)).
const OM1_FLAGGED: [&str; 17] = [
    "q_000024_19",
    "q_000082_19",
    "q_000140_15",
    "q_000141_15",
    "q_000205_13",
    "q_000227_17",
    "q_000240_17",
    "q_000294_17",
    "q_000320_17",
    "q_000332_19",
    "q_000333_18",
    "q_000346_17",
    "q_000355_16",
    "q_000388_17",
    "q_000400_19",
    "q_000406_17",
    "q_000437_16",
];

fn replay_key(key: &str) {
    let Some(dir) = materialize(key) else {
        return;
    };
    let corpus: &Path = &dir.path().join(key);
    let limit = env_usize("AY_REPLAY_LIMIT", 0);
    let report = run_replay(corpus, true, limit).expect("replay");
    eprintln!("[replay {key}] {}", report.summary());
    for d in report.diff.disagreements.iter().take(5) {
        eprintln!("[replay {key}] DISAGREEMENT {d}");
    }
    for d in report.recorded_disagreements.iter().take(5) {
        eprintln!("[replay {key}] RECORDED-DISAGREEMENT {d}");
    }
    for e in report.diff.errors.iter().take(5) {
        eprintln!("[replay {key}] ERROR {e}");
    }
    assert!(
        report.diff.errors.is_empty(),
        "harness errors: {:?}",
        report.diff.errors
    );
    assert!(
        report.diff.disagreements.is_empty(),
        "{} disagreements (first: {})",
        report.diff.disagreements.len(),
        report.diff.disagreements[0]
    );
    assert!(
        report.recorded_disagreements.is_empty(),
        "{} disagreements with the recorded verdicts (first: {})",
        report.recorded_disagreements.len(),
        report.recorded_disagreements[0]
    );
    assert_eq!(report.diff.real_false_unsat, 0, "Real false-UNSAT counter");
    assert_eq!(report.diff.ext_full_reset_hits, 0, "ext_full_reset_hits");
    assert!(report.queries > 0);
    if key == "om1relays" && limit == 0 {
        let mut seen = 0;
        for (file, s, l, z) in &report.per_query {
            if OM1_FLAGGED.iter().any(|f| file.starts_with(f)) {
                seen += 1;
                eprintln!(
                    "[replay om1relays] flagged {file}: session={} legacy={} z3={}",
                    s.as_str(),
                    l.as_str(),
                    z.map_or("-", |v| v.as_str())
                );
                assert_ne!(
                    s.as_str(),
                    "unsat",
                    "{file} is satisfiable (the 2026-09-18 push/pop false-UNSAT query)"
                );
            }
        }
        assert_eq!(
            seen,
            OM1_FLAGGED.len(),
            "all 17 flagged queries are in the corpus"
        );
        // Rung-4 finding: 7 queries of this corpus ended in a hint-converged
        // `Sat` whose model violated a disequality, which the router's strict
        // check demoted to `Unknown` ("router-side" Unknowns: an Unknown with
        // no session Unknown class). The bridge's hint re-check closes them.
        let d = &report.diff;
        let classes = d.unknown_budget
            + d.unknown_unsupported
            + d.unknown_theory_incomplete
            + d.unknown_poisoned;
        let router_side = d.session_unknown.saturating_sub(classes);
        eprintln!("[replay om1relays] router-side unknowns={router_side}");
        assert_eq!(
            router_side, 0,
            "session Sats demoted by the router's strict check"
        );
    }
}

fn selected(key: &str) -> bool {
    match std::env::var("AY_REPLAY_KEYS") {
        Ok(keys) => keys.split(',').any(|k| k.trim() == key),
        Err(_) => true,
    }
}

#[test]
fn script_assertions_round_trip_through_the_chc_parser() {
    let text = "(set-logic QF_LRA)\n(set-option :produce-models true)\n(declare-const x Real)\n(declare-const b Bool)\n(assert (<= x (/ 3 2)))\n(assert (not b))\n(assert (or b (> x 0.0)))\n(check-sat)\n(get-model)\n";
    let e = parse_script_assertions(text).expect("parse");
    let s = crate::smt::session::dump::script_for(&e, false);
    assert_eq!(s.matches("(assert ").count(), 3, "{s}");
    assert!(
        s.contains("(declare-const x Real)") && s.contains("(declare-const b Bool)"),
        "{s}"
    );
}

#[test]
fn replay_om1relays() {
    if selected("om1relays") {
        replay_key("om1relays");
    }
}

#[test]
fn replay_ak_s1min() {
    if selected("ak_s1min") {
        replay_key("ak_s1min");
    }
}

#[test]
fn replay_s3_srvr_4() {
    if selected("s3_srvr_4") {
        replay_key("s3_srvr_4");
    }
}

/// Design §7.3 (ii): the push/pop false-UNSAT repros of
/// `repros/lra-pushpop-false-unsat-2026-09-18/` (the ay-dpll inc-engine
/// selector-aliasing bug) replayed through the session's logical scopes;
/// every check must agree with z3 (the last scope of each file is `sat`).
#[test]
fn replay_pushpop_repros() {
    if !selected("pushpop_repros") {
        return;
    }
    let dir = fixtures_root().join("pushpop_repros");
    let report = run_pushpop_files(&dir, true).expect("pushpop repros");
    eprintln!("[replay pushpop_repros] {}", report.summary());
    for d in report.disagreements.iter().take(5) {
        eprintln!("[replay pushpop_repros] DISAGREEMENT {d}");
    }
    assert!(
        report.errors.is_empty(),
        "harness errors: {:?}",
        report.errors
    );
    assert!(
        report.scripts >= 5,
        "expected the five repro files, got {}",
        report.scripts
    );
    assert!(
        report.disagreements.is_empty(),
        "{} disagreements (first: {})",
        report.disagreements.len(),
        report.disagreements[0]
    );
    assert_eq!(report.real_false_unsat, 0, "Real false-UNSAT counter");
    assert_eq!(
        report.session_unknown, 0,
        "every repro check must be decided by the session"
    );
}

/// `scripts/chc_session_replay.py run <dir>` entry: replay the dump directory
/// named by `AY_REPLAY_DIR` (plain `q_*.smt2` + `index.tsv`, e.g. a fresh
/// `--chc-session-dump` directory) and print the summary line. A no-op
/// unless `AY_REPLAY_DIR` is set; asserts the same 0-disagreement bar.
#[test]
fn replay_dir_from_env() {
    let Ok(dir) = std::env::var("AY_REPLAY_DIR") else {
        eprintln!("[replay-dir] AY_REPLAY_DIR not set; nothing to do");
        return;
    };
    let limit = env_usize("AY_REPLAY_LIMIT", 0);
    let report = run_replay(Path::new(&dir), true, limit).expect("replay");
    eprintln!("[replay-dir {dir}] {}", report.summary());
    for d in report.diff.disagreements.iter().take(5) {
        eprintln!("[replay-dir] DISAGREEMENT {d}");
    }
    for d in report.recorded_disagreements.iter().take(5) {
        eprintln!("[replay-dir] RECORDED-DISAGREEMENT {d}");
    }
    assert!(
        report.passed(),
        "replay of {dir} failed: {}",
        report.summary()
    );
}

/// Rung-4 finding (see `replay_om1relays`): the 7 om1relays queries whose
/// warm-session answer was a hint-converged `Sat` violating a disequality
/// (all satisfiable per z3, `tests/fixtures/session_replay/
/// om1relays_hint_demotions`). Each one through a fresh session-only Search
/// context must come back `Sat` with a model the router accepts.
#[test]
fn om1relays_hint_convergence_demotions_are_decided() {
    let key = "om1relays_hint_demotions";
    if !selected(key) {
        return;
    }
    let Some(dir) = materialize(key) else {
        return;
    };
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir.path().join(key))
        .expect("materialized corpus")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "smt2"))
        .collect();
    files.sort();
    assert_eq!(files.len(), 7, "the seven demoted queries");
    for f in files {
        let text = std::fs::read_to_string(&f).expect("read query");
        let expr = parse_script_assertions(&text).expect("parse");
        let _mode = ScopedSessionMode::set(2);
        let _fresh = crate::smt::ScopedNoProgressBreaker::new();
        let mut ctx = SmtContext::new_search();
        let r = ctx.check_sat_with_timeout(&expr, Duration::from_secs(10));
        eprintln!(
            "[replay {key}] {}: {}",
            f.display(),
            if matches!(r, SmtResult::Sat(_)) {
                "sat"
            } else {
                "not sat"
            }
        );
        assert!(
            matches!(r, SmtResult::Sat(_)),
            "{}: {r:?} (z3: sat)",
            f.display()
        );
    }
}
