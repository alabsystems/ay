// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ay-theories ledger must stay complete and DERIVED.
//!
//! P6 rollout, first crate group. This is `ay-milp`'s `tests/env_ledger.rs` raised to
//! the theory crates, with the one lesson `ay-milp` learned the hard way applied from
//! the start: **the read-site column is derived from the source, never hand-typed.**
//! In ay-milp it was hand-typed, checked by nothing, wrong on 23 of 353 entries, and
//! still being quoted as evidence when the derivation was finally written.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

fn theories_root() -> PathBuf {
    // crates/ay-theories/euf -> crates/ay-theories
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("euf must live under crates/ay-theories")
        .to_path_buf()
}

/// Count literal `env::var("AY_…")` / `env::var_os("AY_…")` sites per name.
fn scan(dir: &Path, into: &mut BTreeMap<String, u32>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            if p.file_name().is_some_and(|f| f == "target") {
                continue;
            }
            scan(&p, into);
            continue;
        }
        if p.extension().is_none_or(|x| x != "rs")
            || p.file_name().is_some_and(|f| f == "theories_ledger.rs")
        {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&p) else {
            continue;
        };
        for (i, _) in text.match_indices("env::var") {
            let rest = &text[i + "env::var".len()..];
            let rest = rest.strip_prefix("_os").unwrap_or(rest);
            let Some(rest) = rest.trim_start().strip_prefix('(') else {
                continue;
            };
            let Some(rest) = rest.trim_start().strip_prefix('"') else {
                continue;
            };
            let Some(end) = rest.find('"') else { continue };
            let name = &rest[..end];
            if name.starts_with("AY_") {
                *into.entry(name.to_string()).or_default() += 1;
            }
        }
    }
}

fn actual() -> BTreeMap<String, u32> {
    let mut out = BTreeMap::new();
    scan(&theories_root(), &mut out);
    out
}

/// A name added at a fresh site must fail here rather than appear in silence. This
/// is the whole point of an inventory, and it is what makes the unknown-name audit
/// trustworthy: that report is only as good as the ledger is exhaustive.
#[test]
fn every_name_in_source_is_in_the_ledger() {
    let ledger: std::collections::BTreeSet<&str> = ay_euf::theories_ledger::KNOBS
        .iter()
        .map(|k| k.name)
        .collect();
    let found = actual();
    let missing: Vec<&String> = found
        .keys()
        .filter(|n| !ledger.contains(n.as_str()))
        .collect();
    assert!(
        missing.is_empty(),
        "these AY_* names are read in ay-theories but are not in the ledger: {missing:?}"
    );
}

/// And the ledger must not invent names, or the audit starts reporting knobs that
/// cannot be set.
#[test]
fn the_ledger_does_not_invent_names() {
    let found = actual();
    let stale: Vec<&str> = ay_euf::theories_ledger::KNOBS
        .iter()
        .map(|k| k.name)
        .filter(|n| !found.contains_key(*n))
        .collect();
    assert!(stale.is_empty(), "ledger lists unread names: {stale:?}");
}

/// THE LESSON FROM ay-milp, APPLIED FROM COMMIT ONE.
///
/// `read_sites` there was hand-typed and checked by nothing. When a derivation was
/// finally written it disagreed with the source on 23 of 353 entries — twelve of them
/// knobs whose literal reads a migration had DELETED, three read by nothing at all —
/// and the column had been quoted as evidence in a debt census the whole time.
#[test]
fn read_site_counts_are_derived() {
    let found = actual();
    let wrong: Vec<String> = ay_euf::theories_ledger::KNOBS
        .iter()
        .filter_map(|k| {
            let a = found.get(k.name).copied().unwrap_or(0);
            (a != k.read_sites).then(|| {
                format!(
                    "  {:38} declared {:3}  actual {:3}",
                    k.name, k.read_sites, a
                )
            })
        })
        .collect();
    assert!(
        wrong.is_empty(),
        "{} entries declare a read-site count the source does not support:\n{}\n\
         Re-derive the column; do not hand-edit it.",
        wrong.len(),
        wrong.join("\n")
    );
}

/// Sorted and duplicate-free, so a reader can find a name and a diff stays legible.
#[test]
fn the_table_is_sorted_and_has_no_duplicates() {
    for w in ay_euf::theories_ledger::KNOBS.windows(2) {
        assert!(
            w[0].name < w[1].name,
            "ledger not sorted at {} / {}",
            w[0].name,
            w[1].name
        );
    }
}

/// The duplication `SIZE_GATE_ANTIPATTERN.md` flags, pinned so it cannot be lost:
/// `PHASE_EPOCH_MIN_ATOMS = 8192` is declared in ay-lia AND in ay-dpll's combiner
/// with no shared definition. Both are instrumented to separate `ay_core::forgone`
/// indices so the census keeps them apart.
#[test]
fn the_duplicated_phase_epoch_gate_stays_visible() {
    let lia = std::fs::read_to_string(theories_root().join("lia/src/theory_impl.rs"))
        .expect("ay-lia theory_impl must exist");
    assert!(
        lia.contains("PHASE_EPOCH_MIN_ATOMS"),
        "the duplicated constant moved; re-check its ay-dpll twin and the forgone sites"
    );
    assert!(
        lia.contains("forgone::PHASE_EPOCH_LIA"),
        "the ay-lia copy must charge its own forgone-cost index, not share the combiner's"
    );
}
