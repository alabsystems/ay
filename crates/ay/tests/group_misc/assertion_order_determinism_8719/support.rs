// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Support helpers for the assertion-order determinism guard (#8719):
//! fixtures, SMT-LIB splitter / rebuilder, deterministic permutation set,
//! and the subprocess runner for `ay`.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

pub(super) struct Fixture {
    pub name: &'static str,
    pub expected: ExpectedAnswer,
    pub source: &'static str,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ExpectedAnswer {
    Sat,
    Unsat,
}

impl ExpectedAnswer {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
        }
    }
}

pub(super) const FIXTURES: &[Fixture] = &[
    Fixture {
        name: "qf_lia_sat",
        expected: ExpectedAnswer::Sat,
        // 6 assertions => 720 distinct permutations, plenty for N=10.
        source: "(set-logic QF_LIA)\n\
                 (declare-const x Int)\n\
                 (declare-const y Int)\n\
                 (declare-const z Int)\n\
                 (assert (>= x 0))\n\
                 (assert (<= x 10))\n\
                 (assert (= y (+ x 1)))\n\
                 (assert (>= z 5))\n\
                 (assert (<= z 15))\n\
                 (assert (= z (+ y 2)))\n\
                 (check-sat)\n",
    },
    Fixture {
        name: "qf_lia_unsat",
        expected: ExpectedAnswer::Unsat,
        // 5 assertions => 120 distinct permutations.
        source: "(set-logic QF_LIA)\n\
                 (declare-const x Int)\n\
                 (declare-const y Int)\n\
                 (assert (>= x 0))\n\
                 (assert (<= x 10))\n\
                 (assert (= y (+ x 1)))\n\
                 (assert (>= y 20))\n\
                 (assert (<= y 30))\n\
                 (check-sat)\n",
    },
    Fixture {
        name: "qf_lra_sat",
        expected: ExpectedAnswer::Sat,
        // 5 assertions => 120 distinct permutations.
        source: "(set-logic QF_LRA)\n\
                 (declare-const a Real)\n\
                 (declare-const b Real)\n\
                 (declare-const c Real)\n\
                 (assert (>= a 0.0))\n\
                 (assert (<= a 1.0))\n\
                 (assert (= b (+ a 0.5)))\n\
                 (assert (<= c 2.0))\n\
                 (assert (>= c (* 2.0 b)))\n\
                 (check-sat)\n",
    },
    Fixture {
        name: "qf_uf_unsat",
        expected: ExpectedAnswer::Unsat,
        // 5 assertions: 5! = 120 distinct permutations, plenty for N=10.
        source: "(set-logic QF_UF)\n\
                 (declare-sort U 0)\n\
                 (declare-fun f (U) U)\n\
                 (declare-const a U)\n\
                 (declare-const b U)\n\
                 (declare-const c U)\n\
                 (declare-const d U)\n\
                 (assert (= a b))\n\
                 (assert (= b c))\n\
                 (assert (= c d))\n\
                 (assert (= (f a) a))\n\
                 (assert (not (= (f d) a)))\n\
                 (check-sat)\n",
    },
    Fixture {
        name: "qf_bv_sat",
        expected: ExpectedAnswer::Sat,
        // 5 assertions => 120 distinct permutations.
        source: "(set-logic QF_BV)\n\
                 (declare-const x (_ BitVec 8))\n\
                 (declare-const y (_ BitVec 8))\n\
                 (declare-const z (_ BitVec 8))\n\
                 (assert (bvult x #x10))\n\
                 (assert (bvugt y #x05))\n\
                 (assert (= z (bvadd x y)))\n\
                 (assert (bvult z #xFF))\n\
                 (assert (bvuge z #x06))\n\
                 (check-sat)\n",
    },
    Fixture {
        name: "qf_abv_sat",
        expected: ExpectedAnswer::Sat,
        // 5 assertions => 120 distinct permutations.
        source: "(set-logic QF_ABV)\n\
                 (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\n\
                 (declare-const i (_ BitVec 8))\n\
                 (declare-const j (_ BitVec 8))\n\
                 (declare-const v (_ BitVec 8))\n\
                 (assert (= (select a i) v))\n\
                 (assert (bvult i j))\n\
                 (assert (= (select (store a j v) i) v))\n\
                 (assert (bvult v #x10))\n\
                 (assert (bvugt j #x00))\n\
                 (check-sat)\n",
    },
];

// ---------------------------------------------------------------------------
// SMT-LIB assertion splitter
// ---------------------------------------------------------------------------

/// Decomposition of an SMT-LIB script: prelude, top-level `(assert ...)` s-exprs
/// in original order, and epilogue (typically `(check-sat)` and friends).
pub(super) struct SplitScript {
    pub prelude: String,
    pub assertions: Vec<String>,
    pub epilogue: String,
}

/// Split an SMT-LIB script into prelude / assertions / epilogue.
///
/// Only top-level (depth-0) `(assert ...)` forms are extracted.  String and
/// `|quoted|` literals, plus `;` line comments, are respected.  This is
/// deliberately minimal — enough to round-trip fixtures without pulling in
/// the full ay-frontend parser.
pub(super) fn split_script(src: &str) -> SplitScript {
    let bytes = src.as_bytes();
    let mut prelude = String::new();
    let mut assertions: Vec<String> = Vec::new();
    let mut epilogue = String::new();
    let mut last_end = 0usize;
    let mut last_assert_end: Option<usize> = None;
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b';' => i = skip_line_comment(bytes, i),
            b'"' => i = skip_string(bytes, i),
            b'|' => i = skip_quoted_symbol(bytes, i),
            b'(' => {
                let start = i;
                let Some(end) = scan_balanced(bytes, start) else {
                    break; // unbalanced — bail
                };
                let form = &src[start..end];
                if is_assert_form(form) {
                    if assertions.is_empty() {
                        prelude.push_str(&src[last_end..start]);
                    }
                    assertions.push(form.to_string());
                    last_assert_end = Some(end);
                    last_end = end;
                }
                i = end;
            }
            _ => i += 1,
        }
    }

    if let Some(end) = last_assert_end {
        epilogue.push_str(&src[end..]);
    } else {
        prelude.push_str(&src[last_end..]);
    }

    SplitScript {
        prelude,
        assertions,
        epilogue,
    }
}

fn skip_line_comment(bytes: &[u8], mut i: usize) -> usize {
    while i < bytes.len() && bytes[i] != b'\n' {
        i += 1;
    }
    i
}

fn skip_string(bytes: &[u8], mut i: usize) -> usize {
    i += 1;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            // Escaped `""` in SMT-LIB string literals.
            if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                i += 2;
                continue;
            }
            return i + 1;
        }
        i += 1;
    }
    i
}

fn skip_quoted_symbol(bytes: &[u8], mut i: usize) -> usize {
    i += 1;
    while i < bytes.len() && bytes[i] != b'|' {
        i += 1;
    }
    if i < bytes.len() {
        i + 1
    } else {
        i
    }
}

fn scan_balanced(bytes: &[u8], start: usize) -> Option<usize> {
    debug_assert_eq!(bytes[start], b'(');
    let mut depth = 0i32;
    let mut i = start;
    while i < bytes.len() {
        match bytes[i] {
            b';' => i = skip_line_comment(bytes, i),
            b'"' => i = skip_string(bytes, i),
            b'|' => i = skip_quoted_symbol(bytes, i),
            b'(' => {
                depth += 1;
                i += 1;
            }
            b')' => {
                depth -= 1;
                i += 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => i += 1,
        }
    }
    None
}

fn is_assert_form(form: &str) -> bool {
    let inner = form.trim_start_matches('(').trim_start();
    inner
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .next()
        .is_some_and(|tok| tok == "assert")
}

/// Rebuild an SMT-LIB script with the assertions emitted in the given order.
pub(super) fn rebuild(script: &SplitScript, order: &[usize]) -> String {
    let mut out = String::with_capacity(script.prelude.len() + script.epilogue.len() + 128);
    out.push_str(&script.prelude);
    if !out.ends_with('\n') && !out.is_empty() {
        out.push('\n');
    }
    for &idx in order {
        out.push_str(&script.assertions[idx]);
        out.push('\n');
    }
    let epilogue = script.epilogue.trim_start_matches(['\n', ' ', '\t']);
    out.push_str(epilogue);
    if !out.ends_with('\n') {
        out.push('\n');
    }
    out
}

// ---------------------------------------------------------------------------
// Permutation strategies
// ---------------------------------------------------------------------------

/// Build up to `count` distinct deterministic permutations of `0..n`.
///
/// Strategy: seed the output with structural permutations (identity, reverse,
/// rotations) so the first few trials cover obvious boundary cases, then fill
/// the remaining slots with seeded Fisher-Yates shuffles driven by a fixed
/// LCG. The seed is a compile-time constant so the permutation set is
/// reproducible across runs — determinism is the property under test, and
/// the driver itself must therefore be deterministic. This is equivalent to
/// `proptest` with a fixed seed but without the dependency cost.
///
/// If `n! < count`, returns `n!` distinct permutations (all of them). If
/// `n == 0`, returns a single empty permutation.
pub(super) fn permutations(n: usize, count: usize) -> Vec<Vec<usize>> {
    if n == 0 {
        return vec![Vec::new()];
    }
    let identity: Vec<usize> = (0..n).collect();

    // Upper bound on the number of distinct permutations: n! (saturating at
    // `count` to avoid large allocations for n >= 13).
    let max_distinct = factorial_saturating(n, count);
    let target = count.min(max_distinct);

    let mut seen: Vec<Vec<usize>> = Vec::with_capacity(target);
    let push_if_new = |cand: Vec<usize>, seen: &mut Vec<Vec<usize>>| {
        if !seen.iter().any(|s| s == &cand) {
            seen.push(cand);
        }
    };

    // Structural permutations first — these cover the most common order
    // regressions (re-order forward/back, swap first/last, rotate by half).
    push_if_new(identity.clone(), &mut seen);
    if seen.len() < target {
        let mut reversed = identity.clone();
        reversed.reverse();
        push_if_new(reversed, &mut seen);
    }
    if n >= 2 {
        let rotations = [n / 2, 1, n - 1, n / 3 + 1, (2 * n) / 3 + 1];
        for &k in &rotations {
            if seen.len() >= target {
                break;
            }
            push_if_new(rotate(&identity, k), &mut seen);
        }
    }

    // Fill the rest with seeded Fisher-Yates shuffles. The LCG constants are
    // from Numerical Recipes (Knuth-style MMIX). Seed is fixed so the test is
    // reproducible.
    let mut rng_state: u64 = 0x243F_6A88_85A3_08D3;
    let mut attempts: usize = 0;
    // Bound attempts so tiny factorial spaces don't loop forever.
    let max_attempts = target.saturating_mul(16).max(64);
    while seen.len() < target && attempts < max_attempts {
        attempts += 1;
        let mut perm = identity.clone();
        // Fisher-Yates: from i=n-1 downto 1, swap perm[i] with perm[rand_in_0..=i].
        for i in (1..n).rev() {
            rng_state = rng_state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let j = (rng_state >> 33) as usize % (i + 1);
            perm.swap(i, j);
        }
        push_if_new(perm, &mut seen);
    }
    seen
}

/// Saturating factorial: returns min(n!, cap). Never overflows because we
/// stop multiplying once the running product reaches `cap`.
fn factorial_saturating(n: usize, cap: usize) -> usize {
    let mut acc: usize = 1;
    for k in 2..=n {
        acc = acc.saturating_mul(k);
        if acc >= cap {
            return cap;
        }
    }
    acc
}

fn rotate(slice: &[usize], k: usize) -> Vec<usize> {
    let n = slice.len();
    if n == 0 {
        return Vec::new();
    }
    let k = k % n;
    let mut out = Vec::with_capacity(n);
    out.extend_from_slice(&slice[k..]);
    out.extend_from_slice(&slice[..k]);
    out
}

// ---------------------------------------------------------------------------
// Subprocess runner
// ---------------------------------------------------------------------------

pub(super) struct TempFile(PathBuf);

impl TempFile {
    pub(super) fn new(contents: &str, tag: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "ay_determinism_{pid}_{tag}_{suffix}.smt2",
            pid = std::process::id(),
            suffix = rand_suffix(),
        ));
        fs::write(&path, contents).expect("write temp fixture");
        Self(path)
    }

    pub(super) fn path(&self) -> &PathBuf {
        &self.0
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn rand_suffix() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    // Wall-clock nanos used only for file-name disambiguation.
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| u64::from(d.subsec_nanos()))
        .unwrap_or(0)
}

/// Outcome of a single `ay` subprocess run.
pub(super) struct RunOutcome {
    pub answer: String,
    pub elapsed: std::time::Duration,
}

/// Spawn `ay` on `path` with a 30s timeout and return the trimmed first line
/// of stdout (typically `sat` / `unsat` / `unknown`).  Panics with full
/// stdout+stderr if `ay` does not exit with status 0.
pub(super) fn run_ay(ay_path: &str, path: &PathBuf) -> String {
    run_ay_timed(ay_path, path).answer
}

/// Spawn `ay` and also capture elapsed wall-clock time. Timing is advisory
/// only — used by the determinism harness to warn on >2x median jitter, not
/// to fail the test (timing is too noisy to gate correctness on).
pub(super) fn run_ay_timed(ay_path: &str, path: &PathBuf) -> RunOutcome {
    let start = std::time::Instant::now();
    let output = Command::new(ay_path)
        .arg("--timeout")
        .arg("30000")
        .arg(path)
        .output()
        .expect("failed to spawn ay");
    let elapsed = start.elapsed();
    let status = output.status;
    let stdout_str = String::from_utf8_lossy(&output.stdout);
    let stderr_str = String::from_utf8_lossy(&output.stderr);
    assert!(
        status.success(),
        "ay exited with {status:?}\nstdout:\n{stdout_str}\nstderr:\n{stderr_str}",
    );
    let answer = stdout_str.lines().next().unwrap_or("").trim().to_string();
    RunOutcome { answer, elapsed }
}
