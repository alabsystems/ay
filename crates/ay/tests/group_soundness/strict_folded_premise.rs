// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authored assertion that elaboration FOLDS is assumed as written, and the
//! folded term is derived from it with checked steps, so its certificate is a
//! strict one.
//!
//! `strict_folded_conjunct_rewritten_premise.smt2` asserts
//! `(and (< x 3) (= x x))`, which interns as `(< x 3)`. Until the proof
//! restoration asked the printer to confine the authored spelling, the
//! certificate assumed the folded `(< x 3)` (the native SOS lane had purged
//! the authored spelling), `--strict-proofs` withheld `unsat` on every route,
//! and the default certificate line read `foreign_assumes=yes` (it was a
//! fixture of
//! `a_certificate_that_assumes_a_rewritten_premise_is_not_a_strict_certificate`).
//! MEASURED since: every strict route answers `unsat`, and the certificate
//! assumes the assertion as written and projects `(< x 3)` with `and_pos`;
//! pinned carcara 1.1.0 checks it `valid`.

use super::strict_admission_routes::{
    authored_assertions, premise_assumes, run_route, StrictRoute, ALL_ROUTES,
};
use ntest::timeout;
use std::path::PathBuf;

#[test]
#[timeout(600_000)]
fn a_folded_authored_conjunction_is_a_strict_premise() {
    let relative = "crates/ay-dpll/tests/fixtures/strict_folded_conjunct_rewritten_premise.smt2";
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative);
    let script =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let authored = authored_assertions(&script);
    assert!(
        authored.contains(&"(and (< x 3) (= x x))".to_string()),
        "{relative}: {authored:?}"
    );
    for route in ALL_ROUTES {
        let outcome = run_route(route, &script);
        let context = format!("{relative}: {}", outcome.context);
        assert_eq!(outcome.verdicts, ["unsat"], "{context}");
        if matches!(route, StrictRoute::StdinPlain) {
            continue;
        }
        let assumes = premise_assumes(&outcome.document);
        assert!(
            assumes.contains(&"(and (< x 3) (= x x))".to_string()),
            "the certificate assumes the folded assertion as written: {context}"
        );
        for assume in &assumes {
            assert!(
                authored.contains(assume),
                "strict published a certificate assuming `{assume}`, which the input does \
                 not assert: {context}"
            );
        }
        assert!(
            outcome.document.contains(":rule and_pos"),
            "the folded conjunct is projected, not assumed: {context}"
        );
    }
}
