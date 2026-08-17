// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Explicit-trust lemma-recording census (#trust->0 C6 API ratchet).
//!
//! `TheoryLemmaKind::Generic` is the only trust kind: a step recorded without
//! a typed kind can enter a published proof only through the deferred-trust
//! discharge lane and is never strict-checkable on its own. C6 renamed the
//! tracker's bare recorder `add_theory_lemma` to the explicit-trust name
//! `add_explicit_trust_lemma`, so the compiler already rejects any call under
//! the old innocuous name. This census closes the remaining gap: it reads the
//! crate's sources at test time and fails whenever a NEW explicit-trust call
//! site (or a NEW bare-`Generic` recording path) appears without being vetted
//! here — no new trust admission can land silently.
//!
//! Two inventories are kept, per source file (pattern: the B2 negated-proof-
//! gate census in `executor/proof_gate_census_tests.rs`):
//! - `add_explicit_trust_lemma` name-token sites — the named explicit-trust
//!   entry point: its single definition, its internal weakened-prefix
//!   fallback, and every caller. A new caller must either be re-routed
//!   through a typed kind (`add_theory_lemma_with_kind`,
//!   `add_theory_lemma_with_farkas_and_kind`, the `theory_inference`
//!   classifier funnel) or be vetted here with a rationale.
//! - bare `add_theory_lemma(` call-token sites — the ay-proof
//!   `Proof::add_theory_lemma` bare-`Generic` recorder (and any resurrected
//!   tracker method of that name). Production code must never grow a second
//!   path that records `Generic` while bypassing the named entry point.
//!
//! The scan strips `//` line comments (which covers `///` doc comments),
//! skips `tests`/`*_tests` directories and `*_tests.rs`/`tests.rs` files
//! (cfg(test)-only modules), and requires identifier-boundary matches so
//! `add_theory_lemma_with_kind(` and prose tokens do not count. Inline
//! `#[cfg(test)]` modules inside production files are deliberately NOT
//! stripped — their sites are counted and vetted, and overcounting fails
//! safe (census mismatch). Known limitation: a call inside a `/* */` block
//! comment would still be counted — same fail-safe direction.

use std::fs;
use std::path::{Path, PathBuf};

/// One vetted source file: (path relative to `src/`,
/// `add_explicit_trust_lemma` name-token sites, bare `add_theory_lemma(`
/// call-token sites, vetting rationale).
///
/// TO UPDATE THIS LIST you must justify the trust: a NEW
/// `add_explicit_trust_lemma` caller records a `Generic`/trust step that only
/// the deferred-trust discharge lane can admit into a published proof —
/// first try a typed kind or the `theory_inference` classifier funnel; vet a
/// bare site here only when no validator can express the clause, and say why.
/// A NEW bare `add_theory_lemma(` site outside the tracker's own delegation
/// is a bypass of the ratchet and should not be vetted at all — route it
/// through the tracker.
const VETTED: &[(&str, usize, usize, &str)] = &[
    (
        "clause_application.rs",
        1,
        0,
        "string lemma applied to the SAT solver in proof mode; recorded as a \
         trust premise so SAT clause insertion and proof tracking stay \
         aligned (no string-lemma validator exists)",
    ),
    (
        "executor/dt_axioms/selector.rs",
        0,
        1,
        "cfg(test)-only module: builds a Proof fixture directly to exercise \
         promote_array_extensionality_axioms retagging",
    ),
    (
        "executor/theories/euf.rs",
        1,
        0,
        "residual arm after recognize_array_theory_lemma + EufCongruent \
         probes decline (C1.ii); unrecognized packed axiom stays trust",
    ),
    (
        "executor/theories/euf/dt.rs",
        1,
        0,
        "residual arm after the DT recognizer probes decline; unrecognized \
         packed DT axiom stays trust",
    ),
    (
        "executor/theories/incremental_scope.rs",
        1,
        0,
        "cfg(test)-only module: records a step inside an isolated sub-solve \
         to prove the proof window survives for the outer publication flow",
    ),
    (
        "pipeline_fns.rs",
        1,
        0,
        "Generic residual arm of the kind/farkas match when replaying trace \
         theory clauses; typed kinds take the other arms",
    ),
    (
        "proof_tracker/mod.rs",
        2,
        1,
        "the single definition of the named explicit-trust entry point + the \
         weakened-lemma prefix-violation fallback (debug_assert'd \
         unreachable); the one bare Proof::add_theory_lemma delegation lives \
         INSIDE the named entry point",
    ),
    (
        "theory_inference/funnel.rs",
        1,
        0,
        "the classifier funnel's shared recorder residual after every typed \
         classifier has declined; moved from theory_inference/mod.rs during \
         the existing funnel extraction (C1/C3 audited)",
    ),
    (
        "theory_inference/mod.rs",
        5,
        0,
        "the classifier funnel's own Generic residuals: blocking-clause-miss \
         fallback + whole-conflict Generic + extension-lane \
         polarity-incomplete fallback + extension-lane Generic + farkas-path \
         Generic (each after classification declined; C1/C3 audited)",
    ),
];

/// Count identifier-boundary occurrences of `needle` in `text`, with `//`
/// line comments stripped. The char before a match must not be an identifier
/// char (so `foo_add_theory_lemma(` does not count); when the needle ends in
/// an identifier char, the char after must not be one either (so a
/// `add_explicit_trust_lemma_v2` token does not count as the entry point).
fn count_token_sites(text: &str, needle: &str) -> usize {
    let ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    let needle_ends_ident = needle.chars().next_back().is_some_and(ident);
    let mut count = 0;
    for line in text.lines() {
        let code = match line.find("//") {
            Some(idx) => &line[..idx],
            None => line,
        };
        let mut start = 0;
        while let Some(found) = code[start..].find(needle) {
            let at = start + found;
            start = at + needle.len();
            let before_ok = !matches!(code[..at].chars().next_back(), Some(c) if ident(c));
            let after_ok =
                !needle_ends_ident || !matches!(code[start..].chars().next(), Some(c) if ident(c));
            if before_ok && after_ok {
                count += 1;
            }
        }
    }
    count
}

/// Walk `src/`, skipping cfg(test)-only sources: `*_tests.rs` and `tests.rs`
/// files, and any `tests` or `*_tests` directory component. Unlike the B2
/// walker this also skips files named exactly `tests.rs` (e.g.
/// `proof_tracker/tests.rs`, `executor/proof/tests.rs`) — they are
/// `#[cfg(test)]`-registered modules full of fixture recordings.
fn census_sources(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display()));
    for entry in entries {
        let entry = entry.expect("dir entry");
        let path = entry.path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| {
                name == "tests" || name.to_str().is_some_and(|name| name.ends_with("_tests"))
            }) {
                continue;
            }
            census_sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs")
            && !path
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.ends_with("_tests.rs") || n == "tests.rs")
        {
            out.push(path);
        }
    }
}

#[test]
fn explicit_trust_call_site_census_matches_vetted_list() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    census_sources(&src, &mut files);
    files.sort();
    assert!(
        files.len() > 100,
        "census walked only {} files — the source layout moved; fix the walker, \
         do not weaken the census",
        files.len()
    );

    let mut observed: Vec<(String, usize, usize)> = Vec::new();
    for path in &files {
        let text =
            fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let explicit_trust = count_token_sites(&text, "add_explicit_trust_lemma");
        let bare_generic = count_token_sites(&text, "add_theory_lemma(");
        if explicit_trust + bare_generic > 0 {
            let rel = path
                .strip_prefix(&src)
                .expect("under src/")
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, "/");
            observed.push((rel, explicit_trust, bare_generic));
        }
    }
    observed.sort();

    let vetted: Vec<(String, usize, usize)> = VETTED
        .iter()
        .map(|&(path, a, b, _)| (path.to_string(), a, b))
        .collect();
    // VETTED must stay sorted so diffs against `observed` line up.
    {
        let mut sorted = vetted.clone();
        sorted.sort();
        assert_eq!(vetted, sorted, "keep the VETTED list sorted by path");
    }

    if observed != vetted {
        let render = |rows: &[(String, usize, usize)]| {
            rows.iter()
                .map(|(p, a, b)| {
                    format!("  {p}: add_explicit_trust_lemma={a} bare_add_theory_lemma={b}")
                })
                .collect::<Vec<_>>()
                .join("\n")
        };
        panic!(
            "explicit-trust census mismatch (#trust->0 C6).\n\
             A Generic/trust lemma-recording site was added, removed, or moved \
             without re-vetting. A NEW site records a step only the \
             deferred-trust discharge lane can admit into a published proof: \
             first route it through a typed kind \
             (add_theory_lemma_with_kind / add_theory_lemma_with_farkas_and_kind) \
             or the theory_inference classifier funnel; if no validator can \
             express the clause, name the trust via add_explicit_trust_lemma \
             and vet the site in the VETTED list with a rationale. A new bare \
             add_theory_lemma( site outside proof_tracker/mod.rs bypasses the \
             tracker and must be re-routed, not vetted.\n\nobserved:\n{}\n\nvetted:\n{}",
            render(&observed),
            render(&vetted),
        );
    }
}

/// The ratchet's compile-time half, pinned: the tracker itself must expose
/// exactly one definition of the explicit-trust entry point, in
/// `proof_tracker/mod.rs`, and no `fn add_theory_lemma(` may reappear there
/// under the old innocuous name.
#[test]
fn tracker_defines_exactly_one_explicit_trust_entry_point() {
    let mod_rs = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/proof_tracker/mod.rs");
    let text =
        fs::read_to_string(&mod_rs).unwrap_or_else(|e| panic!("read {}: {e}", mod_rs.display()));
    let definitions = text
        .lines()
        .filter(|line| {
            let code = match line.find("//") {
                Some(idx) => &line[..idx],
                None => line,
            };
            code.contains("fn add_explicit_trust_lemma(")
        })
        .count();
    assert_eq!(
        definitions, 1,
        "proof_tracker/mod.rs must define add_explicit_trust_lemma exactly once"
    );
    let old_name_definitions = text
        .lines()
        .filter(|line| {
            let code = match line.find("//") {
                Some(idx) => &line[..idx],
                None => line,
            };
            code.contains("fn add_theory_lemma(")
        })
        .count();
    assert_eq!(
        old_name_definitions, 0,
        "the bare `fn add_theory_lemma(` tracker method was privatized by the \
         C6 ratchet; do not resurrect it — kinds are required, Generic goes \
         through add_explicit_trust_lemma"
    );
}
