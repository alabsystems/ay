// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
//! Divergence detector for the crate's contract-carrying fragment twins.
//!
//! A native Trust contract clause is RAW GRAMMAR: cfg-stripping runs after parsing,
//! so no `cfg` can hide one and a compiler without the extension rejects the whole
//! file it appears in. Two proven gates in this crate therefore exist twice — the
//! authority carrying the clause, and a twin without it, selected on
//! `cfg(deductive_verify)`:
//!
//!   src/eval/vig_core.rs                  <-> src/eval/vig_core_stock.rs
//!   src/portfolio/optimum_guard.rs        <-> src/portfolio/optimum_guard_stock.rs
//!
//! Two definitions are a place to diverge, and the consequence of divergence is
//! specific and bad: the verifier reads only the authority, so a twin that decided
//! something different would ship a gate no prover ever saw. This test derives one
//! from the other — the twin must be the authority with its clause lines removed —
//! so the twins cannot drift without failing the suite.

use std::path::PathBuf;

fn read(rel: &str) -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("cannot read {}: {e}", p.display()))
}

/// Trust's function- and loop-clause keywords.
const CLAUSE_KEYWORDS: [&str; 4] = ["requires", "ensures", "decreases", "invariant"];

/// Whether `line` is a native contract clause occupying its own line — the shape
/// `trustfmt` produces, and the only shape this crate writes.
fn is_contract_clause(line: &str) -> bool {
    let clause = line.trim_start();
    if clause.len() == line.len() || clause.ends_with(';') {
        return false;
    }
    CLAUSE_KEYWORDS.iter().any(|keyword| {
        clause
            .strip_prefix(keyword)
            .is_some_and(|rest| rest.starts_with(char::is_whitespace))
    })
}

/// The executable part of a fragment, as ONE whitespace-normalized string.
///
/// Comments are dropped because the twin documents itself differently on purpose
/// (it says "see the authority"); the CODE is what must agree. Line structure is
/// dropped for a sharper reason: `trustfmt` owns it. A clause forces the signature
/// onto its own lines (`) -> bool` / `ensures ..` / `{`) where the twin writes
/// `) -> bool {`, so a line-by-line comparison would report a formatting artifact
/// as a divergence. Comparing the token text catches every real difference — a
/// changed operand, operator or call — and no formatting one.
fn code_text(text: &str) -> String {
    // `is_contract_clause` reads the RAW line — its indentation is one of the three
    // conditions — so it must run before the trim, not after.
    text.lines()
        .filter(|l| !is_contract_clause(l))
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with("//"))
        .collect::<Vec<_>>()
        .join(" ")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn assert_twin(authority_rel: &str, twin_rel: &str, clauses: usize) {
    let authority = read(authority_rel);
    let twin = read(twin_rel);

    let carried = authority.lines().filter(|l| is_contract_clause(l)).count();
    assert_eq!(
        carried, clauses,
        "{authority_rel} must carry {clauses} native contract clause(s), found {carried} — a \
         clause is raw grammar, so it can only be deleted, never rendered inert, and deleting \
         it deletes the machine-checked half of this gate's soundness argument."
    );
    assert_eq!(
        twin.lines().filter(|l| is_contract_clause(l)).count(),
        0,
        "{twin_rel} exists only because it carries no native contract clause; with one it is \
         unparseable by the compilers it serves."
    );

    let want = code_text(&authority);
    let got = code_text(&twin);
    assert_eq!(
        want, got,
        "{twin_rel} is no longer {authority_rel} minus its contract clause(s).\n  \
         authority: {want}\n  twin:      {got}\n\
         The verifier reads ONLY the authority, so a divergent twin ships a gate decision no \
         prover ever saw. Re-derive the twin from the authority."
    );
}

#[test]
fn vig_core_twin_matches_the_contract_carrying_authority() {
    assert_twin("src/eval/vig_core.rs", "src/eval/vig_core_stock.rs", 1);
}

#[test]
fn optimum_guard_twin_matches_the_contract_carrying_authority() {
    assert_twin(
        "src/portfolio/optimum_guard.rs",
        "src/portfolio/optimum_guard_stock.rs",
        1,
    );
}

/// The selection itself: each home file must offer BOTH fragments, gated on
/// complementary `cfg(deductive_verify)` arms. A dropped arm is either a build that
/// cannot parse (stock) or a gate that silently loses its contract (Trust).
#[test]
fn home_files_select_both_arms() {
    for (home, authority, twin) in [
        (
            "src/eval.rs",
            "include!(\"eval/vig_core.rs\");",
            "include!(\"eval/vig_core_stock.rs\");",
        ),
        (
            "src/portfolio.rs",
            "include!(\"portfolio/optimum_guard.rs\");",
            "include!(\"portfolio/optimum_guard_stock.rs\");",
        ),
    ] {
        let text = read(home);
        for needle in [
            "#[cfg(deductive_verify)]",
            "#[cfg(not(deductive_verify))]",
            authority,
            twin,
        ] {
            assert!(
                text.contains(needle),
                "{home} must select both contract fragments on `cfg(deductive_verify)`; \
                 `{needle}` is missing."
            );
        }
    }
}
