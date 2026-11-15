// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A resident `ay --incremental` session must answer every query exactly as a
//! fresh process does, whatever the session answered before.
//!
//! external-codegen (the Trust codegen verifier) keeps one resident AY per process and
//! frames each obligation as `<body>(echo "==TCG_SRV_n==")(reset)`. On AY
//! 0.13.0 build 8256 (dd4de9e94) the copy-refutation obligation
//! `p1_copy_wrong_offset_finalmem_mem_base_v51_0_8` answered `unsat` as the
//! first window of a session but a bare `unknown` after ANY earlier
//! `check-sat` in the same process (even an empty one), and its strict one-shot
//! proof was rejected by AY's own certification ("step t0 assumes term t1028
//! outside the supplied problem obligation"). external-codegen's anti-tautology tests
//! therefore passed or failed depending on test order.
//!
//! The cause was session state, not the queries: the first public solve of a
//! process switched parsed-assertion retention on for every later query, and
//! retention selects the certification funnel's lanes. The first query and all
//! later ones therefore certified differently, which is visible in the
//! per-query strict-check counters even where the verdicts agree, and flips the
//! verdict where the lanes disagree (`benchmarks/smt/QF_LIA/system_03.smt2` on
//! 5da8198d1).
//!
//! The corpus under `fixtures/external_codegen_resident_session/` is every query body
//! that external-codegen's plugin tests sent, byte-exact; `MANIFEST.tsv` records the
//! capture and the fresh-session verdicts.

use ntest::timeout;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::Command;
use std::sync::Mutex;
use std::time::Duration;

use crate::spawn::OutputTimeout;

/// The two copy-refutation obligations whose verdict depended on session
/// history on build 8256.
const WRONG_OFFSET_COPY: &str = "380af8bb3d7a";
const WRONG_SOURCE_COPY: &str = "5268fd88579f";
/// The two windows external-codegen sent immediately before them in the failing test
/// order (`advance_when_done_range_next_is_refuted`): the query, then its
/// SAT-only model window.
const PREDECESSOR_QUERY: &str = "f9a2398a3b09";
const PREDECESSOR_MODEL: &str = "f5394bbe42f8";

/// Fixed seeds keep failures reproducible; each seed is one whole-corpus
/// session in a different order.
const SESSION_ORDER_SEEDS: [u64; 3] = [0x7c61_0001, 0x7c61_0002, 0x7c61_0003];

const SESSION_TIMEOUT: Duration = Duration::from_mins(25);
const QUERY_TIMEOUT: Duration = Duration::from_mins(5);

#[derive(Debug)]
struct Query {
    id: String,
    body: String,
    expected: String,
    obligations: String,
}

#[derive(Debug)]
struct Window {
    verdicts: Vec<String>,
    lines: Vec<String>,
}

fn fixture_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/group_soundness/fixtures/external_codegen_resident_session")
}

fn corpus() -> Vec<Query> {
    let dir = fixture_dir();
    let manifest = std::fs::read_to_string(dir.join("MANIFEST.tsv")).expect("read MANIFEST.tsv");
    let mut queries = Vec::new();
    for line in manifest
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
    {
        let mut cols = line.splitn(3, '\t');
        let id = cols.next().expect("id column").to_string();
        let expected = cols.next().expect("expected column").to_string();
        let obligations = cols.next().unwrap_or("-").to_string();
        assert!(
            expected == "sat" || expected == "unsat",
            "{id}: manifest verdict must be definite, got {expected:?}"
        );
        let body = std::fs::read_to_string(dir.join(format!("{id}.smt2")))
            .unwrap_or_else(|e| panic!("read fixture {id}.smt2: {e}"));
        let mut hex = String::new();
        for byte in &Sha256::digest(body.as_bytes())[..6] {
            write!(hex, "{byte:02x}").expect("write to String");
        }
        assert_eq!(hex, id, "fixture {id}.smt2 does not match its id");
        queries.push(Query {
            id,
            body,
            expected,
            obligations,
        });
    }
    assert_eq!(
        queries.len(),
        249,
        "the captured corpus has 249 distinct bodies"
    );
    queries
}

fn by_id<'a>(corpus: &'a [Query], id: &str) -> &'a Query {
    corpus
        .iter()
        .find(|q| q.id == id)
        .unwrap_or_else(|| panic!("fixture {id} missing"))
}

/// Run `queries` in one resident session with external-codegen's exact framing and
/// return one parsed window per query plus the session's stderr.
fn run_session(queries: &[&Query], timeout: Duration) -> (Vec<Window>, String) {
    let mut script = String::new();
    for (k, q) in queries.iter().enumerate() {
        script.push_str(&q.body);
        script.push_str(&format!("(echo \"==session-window-{k}==\")\n(reset)\n"));
    }
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--incremental")
        .output_timeout_with_stdin(script.as_bytes(), timeout)
        .expect("run ay --incremental session");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let mut windows = Vec::new();
    let mut current = Vec::new();
    for line in stdout.lines() {
        let trimmed = line.trim();
        if trimmed == format!("==session-window-{}==", windows.len()) {
            let verdicts = current
                .iter()
                .filter(|l: &&String| matches!(l.trim(), "sat" | "unsat" | "unknown"))
                .map(|l| l.trim().to_string())
                .collect();
            windows.push(Window {
                verdicts,
                lines: std::mem::take(&mut current),
            });
        } else {
            current.push(line.to_string());
        }
    }
    assert_eq!(
        windows.len(),
        queries.len(),
        "session ended after {} of {} windows (status {:?})\nstderr tail:\n{}",
        windows.len(),
        queries.len(),
        output.status,
        tail(&stderr, 40)
    );
    (windows, stderr)
}

fn tail(text: &str, lines: usize) -> String {
    let all: Vec<&str> = text.lines().collect();
    all[all.len().saturating_sub(lines)..].join("\n")
}

/// The verdict a window published, or a description of why it has none.
fn verdict(window: &Window) -> String {
    match window.verdicts.as_slice() {
        [one] => one.clone(),
        other => format!(
            "{} verdict lines {:?}: {:?}",
            other.len(),
            other,
            window.lines
        ),
    }
}

/// Deterministic Fisher-Yates over splitmix64.
fn shuffled(corpus: &[Query], seed: u64) -> Vec<&Query> {
    let mut state = seed;
    let mut next = move || {
        state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    let mut order: Vec<&Query> = corpus.iter().collect();
    for i in (1..order.len()).rev() {
        let j = (next() % (i as u64 + 1)) as usize;
        order.swap(i, j);
    }
    order
}

/// The failing external-codegen order, replayed byte-exact: the predecessor test's two
/// windows, then each copy refutation. Both must stay `unsat`.
#[test]
#[timeout(600_000)]
fn copy_refutations_stay_unsat_after_the_predecessor_windows() {
    let corpus = corpus();
    let query = by_id(&corpus, PREDECESSOR_QUERY);
    let model = by_id(&corpus, PREDECESSOR_MODEL);
    for id in [WRONG_OFFSET_COPY, WRONG_SOURCE_COPY] {
        let refutation = by_id(&corpus, id);
        let (fresh, fresh_err) = run_session(&[refutation], QUERY_TIMEOUT);
        assert_eq!(
            verdict(&fresh[0]),
            "unsat",
            "{id} ({}) alone in a fresh session\nstderr:\n{}",
            refutation.obligations,
            tail(&fresh_err, 20)
        );
        let (after, after_err) = run_session(&[query, model, refutation], QUERY_TIMEOUT);
        let got: Vec<String> = after.iter().map(verdict).collect();
        assert_eq!(
            got,
            ["sat", "sat", "unsat"],
            "{id} ({}) after external-codegen's predecessor windows must still be unsat\nstderr:\n{}",
            refutation.obligations,
            tail(&after_err, 20)
        );
    }
}

/// external-codegen's one-shot path (`-smt2 FILE --strict-proofs --proof FILE.alethe
/// --proof-format alethe`) must publish `unsat` with a certificate that passed
/// AY's own strict self-check: no unproved step, no foreign assumption, no
/// trust step.
#[test]
#[timeout(600_000)]
fn copy_refutation_strict_one_shot_proofs_pass_self_check() {
    let corpus = corpus();
    for id in [WRONG_OFFSET_COPY, WRONG_SOURCE_COPY] {
        let query = by_id(&corpus, id);
        let dir = tempfile::tempdir().expect("tempdir");
        let smt2 = dir.path().join("query.smt2");
        let proof = dir.path().join("query.smt2.alethe");
        let mut file = std::fs::File::create(&smt2).expect("create query file");
        file.write_all(query.body.as_bytes()).expect("write query");
        file.write_all(b"(exit)").expect("write exit");
        drop(file);
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("-smt2")
            .arg(&smt2)
            .arg("--strict-proofs")
            .arg("--proof")
            .arg(&proof)
            .args(["--proof-format", "alethe"])
            .output_timeout(QUERY_TIMEOUT)
            .expect("run ay one-shot");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let context = format!(
            "{id} ({})\nstdout:\n{stdout}\nstderr:\n{stderr}",
            query.obligations
        );
        assert!(
            output.status.success(),
            "exit status {:?}: {context}",
            output.status
        );
        assert_eq!(stdout.trim(), "unsat", "{context}");
        let certificate = stderr
            .lines()
            .chain(stdout.lines())
            .find(|l| l.contains("ay.proof.certificate"))
            .unwrap_or_else(|| panic!("no certificate line: {context}"));
        for field in [
            "unproved_steps=0",
            "foreign_assumes=no",
            "trust_free=yes",
            "ay_self_checkable=yes",
        ] {
            assert!(
                certificate.split_whitespace().any(|w| w == field),
                "{field} missing: {context}"
            );
        }
        let written = std::fs::metadata(&proof).map(|m| m.len()).unwrap_or(0);
        assert!(
            written > 0,
            "certified proof file is empty or missing: {context}"
        );
    }
}

/// Every captured body, alone in a fresh session, gets its recorded verdict.
/// This is the baseline the order test compares against.
#[test]
#[timeout(1_800_000)]
fn every_captured_query_matches_its_fresh_session_verdict() {
    let corpus = corpus();
    let failures = Mutex::new(Vec::new());
    let next = std::sync::atomic::AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(query) = corpus.get(i) else { break };
                let (windows, stderr) = run_session(&[query], QUERY_TIMEOUT);
                let got = verdict(&windows[0]);
                if got != query.expected {
                    failures.lock().expect("failures lock").push(format!(
                        "{} ({}): expected {}, fresh session said {got}\nstderr:\n{}",
                        query.id,
                        query.obligations,
                        query.expected,
                        tail(&stderr, 10)
                    ));
                }
            });
        }
    });
    let failures = failures.into_inner().expect("failures lock");
    assert!(
        failures.is_empty(),
        "{} fresh-session verdicts differ:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The whole corpus in one session, in several seeded orders: every window
/// must publish the same verdict the body gets in a fresh session.
#[test]
#[timeout(1_800_000)]
fn captured_queries_are_session_order_independent() {
    let corpus = corpus();
    let expected: HashMap<&str, &str> = corpus
        .iter()
        .map(|q| (q.id.as_str(), q.expected.as_str()))
        .collect();
    let reports = Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for seed in SESSION_ORDER_SEEDS {
            let corpus = &corpus;
            let expected = &expected;
            let reports = &reports;
            scope.spawn(move || {
                let order = shuffled(corpus, seed);
                let (windows, stderr) = run_session(&order, SESSION_TIMEOUT);
                let mut mismatches = Vec::new();
                for (position, (query, window)) in order.iter().zip(&windows).enumerate() {
                    let got = verdict(window);
                    if got != expected[query.id.as_str()] {
                        let predecessor = position.checked_sub(1).map_or("-", |p| order[p].id.as_str());
                        mismatches.push(format!(
                            "seed {seed:#x} window {position}: {} ({}) expected {}, got {got}; predecessor {predecessor}",
                            query.id, query.obligations, expected[query.id.as_str()]
                        ));
                    }
                }
                if !mismatches.is_empty() {
                    let reasons: Vec<&str> = stderr
                        .lines()
                        .filter(|l| l.contains("reason-unknown") || l.contains("rejected by"))
                        .collect();
                    mismatches.push(format!("seed {seed:#x} stderr reasons:\n{}", reasons.join("\n")));
                }
                reports.lock().expect("reports lock").extend(mismatches);
            });
        }
    });
    let reports = reports.into_inner().expect("reports lock");
    assert!(
        reports.is_empty(),
        "session history changed verdicts:\n{}",
        reports.join("\n")
    );
}

/// The per-query certification counters of one window, from an in-band
/// `(get-info :all-statistics)`. `begin_public_solve` resets both for every
/// public decision, so equal counters mean the query took the same lanes.
fn strict_check_counters(window: &Window) -> (String, String) {
    let counter = |key: &str| {
        window
            .lines
            .iter()
            .find_map(|l| {
                let mut words = l.trim_start_matches(['(', ' ']).split_whitespace();
                (words.next() == Some(key))
                    .then(|| words.next().unwrap_or("").trim_end_matches(')').to_string())
            })
            .unwrap_or_else(|| panic!("no {key} in window: {:?}", window.lines))
    };
    (
        counter(":proof.strict-check-invocations"),
        counter(":proof.strict-check-steps-validated"),
    )
}

/// The same copy refutation, first in a session and again after `(reset)`,
/// must certify through the same lanes, not merely reach the same verdict.
#[test]
#[timeout(600_000)]
fn a_repeated_query_certifies_through_the_same_lanes() {
    let corpus = corpus();
    for id in [WRONG_OFFSET_COPY, WRONG_SOURCE_COPY] {
        let refutation = by_id(&corpus, id);
        let with_stats = Query {
            id: refutation.id.clone(),
            body: format!("{}(get-info :all-statistics)\n", refutation.body),
            expected: refutation.expected.clone(),
            obligations: refutation.obligations.clone(),
        };
        let (windows, stderr) = run_session(&[&with_stats, &with_stats], QUERY_TIMEOUT);
        let verdicts: Vec<String> = windows.iter().map(verdict).collect();
        assert_eq!(
            verdicts,
            ["unsat", "unsat"],
            "{id}\nstderr:\n{}",
            tail(&stderr, 20)
        );
        assert_eq!(
            strict_check_counters(&windows[0]),
            strict_check_counters(&windows[1]),
            "{id} ({}): the second window certified through different lanes than the first",
            refutation.obligations
        );
    }
}

/// A benchmark whose lanes disagree: `unsat` first in the session, and it must
/// stay `unsat` after an earlier `check-sat` (5da8198d1 answered
/// `unknown (incomplete self-check-rejected)` there).
#[test]
#[timeout(600_000)]
fn system_03_is_unsat_wherever_it_sits_in_the_session() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/smt/QF_LIA/system_03.smt2");
    let text =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let body = text.replace("(exit)", "");
    let query = Query {
        id: "system_03".to_string(),
        body,
        expected: "unsat".to_string(),
        obligations: "-".to_string(),
    };
    let empty = Query {
        id: "empty".to_string(),
        body: "(check-sat)\n".to_string(),
        expected: "sat".to_string(),
        obligations: "-".to_string(),
    };
    let (first, first_err) = run_session(&[&query], QUERY_TIMEOUT);
    assert_eq!(
        verdict(&first[0]),
        "unsat",
        "first in session\nstderr:\n{}",
        tail(&first_err, 20)
    );
    let (later, later_err) = run_session(&[&empty, &query], QUERY_TIMEOUT);
    let got: Vec<String> = later.iter().map(verdict).collect();
    assert_eq!(
        got,
        ["sat", "unsat"],
        "after an earlier check-sat\nstderr:\n{}",
        tail(&later_err, 20)
    );
}
