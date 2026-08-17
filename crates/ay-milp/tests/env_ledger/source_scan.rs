// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeSet;
use std::path::Path;

/// Names whose READ SITES batches B6-B11 of the env-flag retirement deleted
/// (see `scripts/flag_audit.py`'s docstring for the ratchet history), still
/// mentioned by the comments that document what replaced them. A name here has
/// NO live `env::var` read in this crate; if one gains a read again it must
/// come off the list and back into the ledger. The names live in a sibling
/// text file, NOT as Rust literals: the exact-set quality gate counts every
/// quoted `AY_*` literal in Rust source as a key site, and these are
/// documentation, not keys.
pub(super) fn retired_in_comments() -> BTreeSet<&'static str> {
    include_str!("../retired_env_names.txt")
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .collect()
}

/// Pull every `AY_[A-Z0-9_]+` token out of `text`.
///
/// The `AY_` must start a WORD. Without that boundary the scan matched the
/// literal at any byte offset, so ordinary Rust identifiers manufactured
/// phantom env names out of their own middles: `AMO_MULTIW|AY_MAX_WIDTH` and
/// `AMO_MULTIW|AY_MAX_CANDIDATES` (`src/cardinality_branch.rs`) were reported
/// as unregistered knobs.
///
/// Registering a phantom is the trap, not the fix. `every_ay_env_name_in_source
/// _is_in_the_ledger` would pass because the name is now listed, AND
/// `the_ledger_does_not_invent_names` would pass because it uses this same
/// scanner and still finds the substring — two mutually self-consistent tests,
/// both wrong, with `ay-milp knobs --list` advertising a switch nothing reads.
/// That is precisely the `AY_MILP_NO_CUTZ` defect this ledger exists to catch,
/// installed inside the ledger. Fix the scanner.
fn tokens(text: &str) -> BTreeSet<String> {
    let b = text.as_bytes();
    let mut out = BTreeSet::new();
    let mut i = 0;
    while i + 3 <= b.len() {
        let boundary = i == 0 || !(b[i - 1].is_ascii_alphanumeric() || b[i - 1] == b'_');
        if &b[i..i + 3] == b"AY_" && boundary {
            let mut j = i + 3;
            while j < b.len()
                && (b[j].is_ascii_uppercase() || b[j].is_ascii_digit() || b[j] == b'_')
            {
                j += 1;
            }
            out.insert(text[i..j].to_string());
            i = j;
        } else {
            i += 1;
        }
    }
    out
}

pub(super) fn scan(dir: &Path, into: &mut BTreeSet<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            scan(&p, into);
        } else if p.extension().is_some_and(|x| x == "rs") {
            if let Ok(t) = std::fs::read_to_string(&p) {
                into.extend(tokens(&t));
            }
        }
    }
}
