// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE GATE: a test may not assert a DELTA of a process-global counter.
//!
//! # The defect this stops
//!
//! `ay-milp` keeps a family of process-global `Atomic*` diagnostic totals.
//! Tests read them as NON-VACUITY GUARDS — "and the engine I claim to be
//! testing actually fired". libtest runs this crate's other ~1,450 tests on
//! other threads while any one of them runs, and hundreds of them solve
//! models, so `COUNTER.load() - before` is what the whole BINARY charged in
//! that interval, not what this test charged.
//!
//! Both directions are wrong and the second is the dangerous one:
//!
//! * an EXACT delta (`- before == 2`) flakes — measured on a clean `main`,
//!   one failure in 15 runs of the efficacy-floor census (`759cf08c6`), and
//!   two in 5,400 replicas of the work-clock test (`1717807f1`);
//! * any delta can be SUPPLIED by a sibling, so a mutation that stopped the
//!   engine charging still passes. For a FLOOR (`> before`) that is the ONLY
//!   failure mode, which is why floors look safe and are not: the guard reads
//!   "the engine fired" and means "SOMETHING in this binary fired".
//!
//! TWENTY-TWO sites of this class existed, and finding them by hand is what
//! let twenty survive the first two fixes. The hand census that enumerated the
//! survivors put the total at twenty and missed two, both because it looked
//! for `static NAME: Atomic…` declarations in the files it expected:
//! `simplex::perturb_retry_declines_when_the_work_budget_is_already_spent`
//! (`PERTURB_RETRY_SKIPPED`, in `simplex.rs` rather than `bab.rs`) and
//! `cuts::the_violation_screen_is_bit_identical` (`SCREEN_SKIP`, which is
//! declared by the `counters!` MACRO and so has no `static` line to find).
//! This test is the mechanism, and it found the second one.
//!
//! # The fix a flagged site should take
//!
//! [`ay_milp::local_census`] (crate-private) mirrors each charge into a
//! per-thread slot written inside the same bump path. `Floor::usize_at(&C,
//! "C")` before the window, `floor.report()` after: same assertion, this
//! thread's charges only, and the process counter keeps its `--trace`
//! meaning. The shipped build is unchanged — the mirror is `#[cfg(test)]`.
//!
//! # What is scanned
//!
//! `#[test]` function bodies in `src/`, for the shape "snapshot a crate
//! `Atomic*` static, then read the same static again". That is the delta
//! shape and nothing else is flagged: a test that asserts an ABSOLUTE value
//! of a counter is measuring the process on purpose and is not this defect.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// Sites that may legitimately read a process-global counter twice.
///
/// A bare list rots into a suppression file, so each entry carries the REASON
/// and the test prints it when the entry is the only thing standing between a
/// site and a per-thread instrument. The bar for an entry: a per-thread mirror
/// would be the WRONG instrument here, not merely inconvenient.
const ALLOWED: &[(&str, &str, &str)] = &[(
    "local_census.rs",
    "the_mirror_is_per_thread_and_the_global_is_not",
    "This is the module that OWNS the distinction. It charges a private probe \
     counter from two threads and asserts that the global carries both while \
     each thread's mirror carries only its own — the global delta is the \
     THING UNDER TEST, not the instrument.",
)];

fn src_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src")
}

fn rust_sources(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir).unwrap_or_else(|e| panic!("read {}: {e}", dir.display()));
    for entry in entries {
        let path = entry.expect("readable dir entry").path();
        if path.is_dir() {
            rust_sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

/// Every `Atomic*` static this crate declares, by NAME.
///
/// Declaration shapes covered: `static N: AtomicU64`, `pub(crate) static N:
/// [AtomicUsize; 2]`, and the `counters! { A, B, C }` macro in `sepstat.rs`.
/// A name that reaches this set is a process-global whatever its type spelling.
fn declared_atomics(files: &[PathBuf]) -> BTreeMap<String, String> {
    let mut found = BTreeMap::new();
    for path in files {
        let text = std::fs::read_to_string(path).expect("readable source");
        let name = path
            .file_name()
            .expect("named file")
            .to_string_lossy()
            .to_string();
        for (idx, line) in text.lines().enumerate() {
            let trimmed = line.trim_start();
            let Some(rest) = strip_static_prefix(trimmed) else {
                continue;
            };
            let Some((ident, ty)) = rest.split_once(':') else {
                continue;
            };
            let ident = ident.trim();
            if ident.is_empty()
                || !ident
                    .chars()
                    .all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
            {
                continue;
            }
            // The type may wrap onto the next line; look at both.
            let ty_window: String = ty
                .chars()
                .chain(text.lines().nth(idx + 1).unwrap_or("").chars())
                .collect();
            if ty_window.contains("Atomic") {
                found.insert(ident.to_string(), name.clone());
            }
        }
        // `sepstat.rs`'s `counters! { .. }` macro expands to `pub static N: AtomicU64`.
        if let Some(start) = text.find("counters! {") {
            let body = &text[start + "counters! {".len()..];
            if let Some(end) = body.find('}') {
                for token in body[..end].split(',') {
                    let token = token
                        .lines()
                        .map(str::trim)
                        .find(|l| !l.is_empty() && !l.starts_with("//"))
                        .unwrap_or("")
                        .trim();
                    if !token.is_empty()
                        && token
                            .chars()
                            .all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
                    {
                        found.insert(token.to_string(), name.clone());
                    }
                }
            }
        }
    }
    found
}

fn strip_static_prefix(line: &str) -> Option<&str> {
    for prefix in [
        "pub(crate) static ",
        "pub(super) static ",
        "pub(in crate) static ",
        "pub static ",
        "static ",
    ] {
        if let Some(rest) = line.strip_prefix(prefix) {
            return Some(rest);
        }
    }
    None
}

struct Site {
    file: String,
    line: usize,
    test: String,
    counter: String,
}

/// `#[test]` bodies, as `(name, 1-based line, body)`.
fn test_bodies(text: &str) -> Vec<(String, usize, String)> {
    let bytes: Vec<char> = text.chars().collect();
    let mut out = Vec::new();
    let mut cursor = 0usize;
    while let Some(hit) = text[cursor..].find("#[test]") {
        let at = cursor + hit;
        cursor = at + "#[test]".len();
        // The fn name is the first `fn <ident>` after the attribute.
        let Some(fn_off) = text[cursor..].find("fn ") else {
            break;
        };
        let name_start = cursor + fn_off + 3;
        let name: String = text[name_start..]
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        let Some(brace_off) = text[name_start..].find('{') else {
            break;
        };
        let open = name_start + brace_off;
        let open_idx = text[..open].chars().count();
        let mut depth = 0i32;
        let mut end = open_idx;
        for (i, ch) in bytes.iter().enumerate().skip(open_idx) {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        end = i;
                        break;
                    }
                }
                _ => {}
            }
        }
        let body: String = bytes[open_idx..=end.min(bytes.len() - 1)].iter().collect();
        let line = text[..at].matches('\n').count() + 1;
        out.push((name, line, body));
    }
    out
}

/// Does `body` read `counter` twice — the delta shape?
///
/// A single read is an absolute assertion and is not this defect. Two reads
/// are a before/after pair whatever the variable is called, which is what
/// makes this robust against `_before` naming conventions.
fn reads_twice(body: &str, counter: &str) -> bool {
    let mut count = 0usize;
    let mut rest = body;
    while let Some(at) = rest.find(counter) {
        let after = &rest[at + counter.len()..];
        // `NAME.load(` or `NAME[i].load(` — a read of the process global.
        let tail = after.trim_start();
        let tail = if let Some(open) = tail.strip_prefix('[') {
            open.split_once(']').map_or("", |(_, t)| t)
        } else {
            tail
        };
        if tail.trim_start().starts_with(".load(") {
            count += 1;
        }
        rest = &rest[at + counter.len()..];
    }
    count >= 2
}

#[test]
fn no_test_asserts_a_delta_of_a_process_global_counter() {
    let mut files = Vec::new();
    rust_sources(&src_root(), &mut files);
    files.sort();
    let atomics = declared_atomics(&files);
    assert!(
        atomics.len() > 40,
        "the static scan found only {} atomics — the declaration shapes moved and this gate \
         is scanning nothing",
        atomics.len()
    );
    assert!(
        atomics.contains_key("DUAL_NOENTER_SHORTCUT"),
        "the array-typed counter that the first hand census missed must be in scope"
    );

    let mut sites = Vec::new();
    for path in &files {
        let text = std::fs::read_to_string(path).expect("readable source");
        let file = path
            .file_name()
            .expect("named file")
            .to_string_lossy()
            .to_string();
        for (test, line, body) in test_bodies(&text) {
            for counter in atomics.keys() {
                if reads_twice(&body, counter) {
                    sites.push(Site {
                        file: file.clone(),
                        line,
                        test: test.clone(),
                        counter: counter.clone(),
                    });
                }
            }
        }
    }

    let mut unexpected = Vec::new();
    let mut matched_allowances = Vec::new();
    for site in &sites {
        match ALLOWED
            .iter()
            .find(|(f, t, _)| *f == site.file && *t == site.test)
        {
            Some((_, _, why)) => matched_allowances.push((site, *why)),
            None => unexpected.push(site),
        }
    }

    assert!(
        !matched_allowances.is_empty(),
        "every allowance went unused — the scan stopped seeing the shape it is supposed to \
         see, so a green result here means nothing"
    );

    assert!(
        unexpected.is_empty(),
        "these tests assert a DELTA of a process-global counter, which measures the whole \
         binary rather than the test:\n{}\n\nFIX: snapshot with \
         `crate::local_census::Floor::usize_at(&COUNTER, \"COUNTER\")` before the window and \
         assert on `floor.report()` after. That is the same number with the other ~1,450 \
         concurrently-running tests removed, and the shipped build is unchanged. If a \
         per-thread mirror is genuinely the WRONG instrument for a site (the charge happens \
         on a thread the test does not own), add it to ALLOWED with the reason.",
        unexpected
            .iter()
            .map(|s| format!(
                "  src/{}:{} {} reads {} twice",
                s.file, s.line, s.test, s.counter
            ))
            .collect::<Vec<_>>()
            .join("\n")
    );
}
