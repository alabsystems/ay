// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Validates the clause-free `src/literal_stock.rs` twin used by non-Trust compilers.
//!
//! `literal.rs` carries native Trust contract clauses (`fn f(..) -> T requires P`).
//! Those are RAW GRAMMAR: cfg-stripping runs after parsing, so no `cfg` inside the
//! file can hide them and a stock rustc rejects the whole file — measured, on
//! `nightly-2025-12-03`:
//!
//!     error: expected one of `!`, `(`, `+`, `::`, `<`, `where`, or `{`,
//!            found `requires`
//!
//! That is not a hypothetical audience. `model-checker-consumer`'s Kani-compatibility lane is a
//! `rustc_private` driver frozen on that nightly, it links this crate, and since
//! 2026-08-27 it has not built at all.
//!
//! THE FILE CANNOT ANSWER THAT BY MOVING. the development design notes
//! keys 15 solver-discharged obligations by the string
//! `crates/ay-proof-common/src/literal.rs` (4 of them on the two contracted
//! constructors), and `scripts/trust_ratchet_accounting.py`
//! reads a vanished key as a LOST PROOF (`REMOVED while proved`), which is a ratchet
//! failure. So the verifier keeps reading `literal.rs` at its own path, byte for
//! byte, and every other compiler reads a checked-in clause-free twin. The twin is
//! source rather than generated `OUT_DIR` code so repository source audits and
//! formatters can inspect it; this build script refuses semantic drift on every
//! build.
//!
//! RECOGNISED CLAUSE SHAPE, deliberately narrow: the clause owns its line, is
//! indented, and carries no trailing `;`. That is the shape this repo writes;
//! `ay-quality-gate`'s `function_scan::native_contracts` is the tokenizing version
//! of the same rule, which a build script may not depend on. A clause written
//! outside that shape is left alone and fails LOUDLY at the stock parse — it is
//! never silently dropped, and a Rust statement (which ends in `;`) is never
//! mistaken for one.

use std::env;
use std::fs;
use std::path::PathBuf;

/// The one file in this crate that carries native contract clauses.
const SOURCE: &str = "src/literal.rs";

/// Clause-free source selected by `lib.rs` for non-Trust compilers.
const STOCK: &str = "src/literal_stock.rs";

/// Trust's function- and loop-clause keywords.
const CLAUSE_KEYWORDS: [&str; 4] = ["requires", "ensures", "decreases", "invariant"];

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed={SOURCE}");
    println!("cargo:rerun-if-changed={STOCK}");

    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let source_path = manifest.join(SOURCE);
    let source = fs::read_to_string(&source_path)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", source_path.display()));
    let stock_path = manifest.join(STOCK);
    let stock = fs::read_to_string(&stock_path)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", stock_path.display()));
    let expected = without_contract_clauses(&source);

    assert_eq!(
        stock,
        expected,
        "{} must be the exact clause-stripped twin of {}; update both together",
        stock_path.display(),
        source_path.display()
    );
}

/// Remove every contract-clause line and join its opening brace to the signature.
///
/// The brace join is the only extra canonicalization needed to make the checked-in
/// Rust twin stable under rustfmt. Any clause not followed by the exact standalone
/// opening-brace shape fails closed instead of producing a silently divergent twin.
fn without_contract_clauses(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut removed_clause = false;
    for line in text.lines() {
        if is_contract_clause(line) {
            removed_clause = true;
            continue;
        }
        if removed_clause {
            assert_eq!(
                line.trim(),
                "{",
                "a native contract clause must be followed by a standalone opening brace"
            );
            assert!(out.ends_with('\n'));
            out.pop();
            out.push_str(" {\n");
            removed_clause = false;
        } else {
            out.push_str(line);
            out.push('\n');
        }
    }
    assert!(
        !removed_clause,
        "native contract clause is missing its body"
    );
    out
}

/// Whether `line` is a native contract clause in the signature position.
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
