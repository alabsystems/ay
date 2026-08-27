// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The anchor-inventory meta-guard and the reader's own self-test.

#![allow(dead_code)]

use super::{crate_root, LogicalModule};

// ---------------------------------------------------------------------------
// Meta-guard: the anchor inventory must be complete.
// ---------------------------------------------------------------------------

/// Every anchor a conformance suite hands to [`LogicalModule::locate`],
/// [`LogicalModule::region`] or [`LogicalModule::region_to_item_end`] must be
/// listed in the suite's inventory, and every inventoried anchor must resolve
/// exactly once in its logical module.
///
/// `locate` already enforces uniqueness at every call, but only for the calls a
/// given test run reaches. This walks the suite's OWN source so a newly added
/// anchor cannot arrive un-inventoried, and re-resolves the whole inventory in
/// one place so a duplicate introduced elsewhere is reported even when the test
/// that uses it is filtered out.
pub(crate) fn assert_anchor_inventory(suite_sources: &[&str], inventory: &[(&str, &[&str])]) {
    for (root, anchors) in inventory {
        let module = LogicalModule::load(root);
        module.assert_anchors_resolve_uniquely(anchors);
    }
    let inventoried = inventory
        .iter()
        .flat_map(|(_, anchors)| anchors.iter().copied())
        .collect::<Vec<_>>();

    let base = crate_root();
    let mut scanned = 0usize;
    for suite in suite_sources {
        let path = base.join(suite);
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()));
        for anchor in extract_anchor_literals(&text) {
            scanned += 1;
            assert!(
                inventoried.contains(&anchor.as_str()),
                "conformance suite {suite} resolves the anchor {anchor:?} but it is not in the \
                 anchor inventory, so nothing checks that it resolves exactly once across its \
                 logical module. Add it to the inventory."
            );
        }
    }
    assert!(
        scanned >= inventoried.len(),
        "the anchor inventory lists {} anchors but only {scanned} anchor uses were found in \
         {suite_sources:?} — the inventory has gone stale relative to the suite",
        inventoried.len()
    );
}

/// Pull every string literal that is an argument of `.locate(`, `.region(` or
/// `.region_to_item_end(` out of a conformance suite's source text.
fn extract_anchor_literals(text: &str) -> Vec<String> {
    const CALLS: [&str; 3] = [".locate(", ".region(", ".region_to_item_end("];
    let bytes = text.as_bytes();
    let mut found = Vec::new();
    for call in CALLS {
        let mut from = 0;
        while let Some(offset) = text[from..].find(call) {
            let mut index = from + offset + call.len();
            from = index;
            let mut depth = 1usize;
            while index < bytes.len() && depth > 0 {
                match bytes[index] {
                    b'(' => {
                        depth += 1;
                        index += 1;
                    }
                    b')' => {
                        depth -= 1;
                        index += 1;
                    }
                    b'"' => {
                        let (literal, next) = read_literal(text, index);
                        found.push(literal);
                        index = next;
                    }
                    _ => index += 1,
                }
            }
        }
    }
    found
}

// ---------------------------------------------------------------------------
// The reader's own load-bearing behaviour.
// ---------------------------------------------------------------------------

/// Pinned here rather than in a suite file so the meta-guard's anchor scan
/// never sees these deliberately-unresolvable and deliberately-duplicated
/// anchors.
#[test]
fn logical_module_reader_refuses_duplicate_anchors_and_straddling_regions() {
    // `begin_public_solve` is defined twice in this crate: the lifecycle
    // entrypoint and an unrelated array-cache method under `executor/theories`.
    // Addressed from the `executor` root both are in scope, and the reader must
    // REFUSE rather than silently bind to whichever sorted first.
    let executor = LogicalModule::load("src/executor.rs");
    assert!(
        std::panic::catch_unwind(|| {
            executor.locate("pub(crate) fn begin_public_solve(");
        })
        .is_err(),
        "the reader must refuse an anchor that resolves more than once"
    );
    assert!(
        std::panic::catch_unwind(|| {
            executor.locate("fn no_such_anchor_exists_anywhere_9f1c(");
        })
        .is_err(),
        "the reader must refuse an anchor that resolves nowhere"
    );

    // These two endpoints now live in different files of one logical module —
    // exactly the shape that silently unbounded three UNSAT guards. A region
    // over them must fail LOUD, never quietly widen.
    let lifecycle = LogicalModule::load("src/executor/lifecycle.rs");
    assert!(
        std::panic::catch_unwind(|| {
            lifecycle.region(
                "pub(crate) fn begin_public_solve(",
                "pub(crate) fn note_api_assertion_mutation",
            );
        })
        .is_err(),
        "the reader must refuse a region whose endpoints straddle a module split"
    );

    // A region is a contiguous slice of ONE file, and an item-bounded region
    // never runs past the enclosing block.
    let unsat = LogicalModule::load("src/executor/unsat_cert.rs");
    let consumer = unsat.region_to_item_end("pub(crate) fn take_unsat_certificate(");
    assert_eq!(
        consumer.file(),
        "src/executor/unsat_cert/query_epoch_access.rs",
        "the consumer must be found in the submodule the refactor moved it to"
    );
    assert!(
        !consumer.contains("#[cfg(test)]"),
        "an item-bounded region must not run on into a test module"
    );
}

/// Read the Rust string literal starting at `open` (the opening quote) and
/// return its unescaped value plus the index just past the closing quote.
fn read_literal(text: &str, open: usize) -> (String, usize) {
    let bytes = text.as_bytes();
    let mut index = open + 1;
    let mut value = String::new();
    while index < bytes.len() {
        match bytes[index] {
            b'"' => return (value, index + 1),
            b'\\' => {
                let escape = bytes.get(index + 1).copied().unwrap_or(b'\\');
                match escape {
                    b'n' => value.push('\n'),
                    b't' => value.push('\t'),
                    b'r' => value.push('\r'),
                    b'0' => value.push('\0'),
                    b'\n' => {
                        // A `\` line continuation swallows the newline and the
                        // following indentation.
                        index += 2;
                        while index < bytes.len() && (bytes[index] as char).is_whitespace() {
                            index += 1;
                        }
                        continue;
                    }
                    other => value.push(other as char),
                }
                index += 2;
            }
            _ => {
                let ch = text[index..].chars().next().unwrap_or('\u{fffd}');
                value.push(ch);
                index += ch.len_utf8();
            }
        }
    }
    (value, index)
}
