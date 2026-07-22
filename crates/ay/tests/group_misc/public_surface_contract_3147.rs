// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guardrail test: the development design notes must stay aligned with the
//! actual root-crate public surface defined in crates/ay/src/lib.rs.
//!
//! Part of #3147 — API contract drift prevention.

fn migration_doc() -> Option<String> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    std::fs::read_to_string(root.join("the development design notes")).ok()
}

/// Extract the "Available Root Crate Surfaces" section from the migration doc.
fn extract_root_surface_section(doc: &str) -> &str {
    let heading = "## Available Root Crate Surfaces";
    let start = doc
        .find(heading)
        .expect("CONSUMER_MIGRATION.md must contain '## Available Root Crate Surfaces'");
    let section = &doc[start..];
    // End at the next H2 heading or end-of-file.
    if let Some(next) = section[heading.len()..].find("\n## ") {
        &section[..heading.len() + next]
    } else {
        section
    }
}

#[test]
fn test_consumer_migration_root_surface_table_matches_facade() {
    // The published crate snapshot intentionally omits top-level docs. Enforce
    // this contract only in a full source checkout where the migration guide is
    // present.
    let Some(migration_doc) = migration_doc() else {
        return;
    };
    let section = extract_root_surface_section(&migration_doc);

    // Positive: all implemented surfaces must be documented.
    assert!(
        section.contains("ay::api"),
        "migration doc must document ay::api"
    );
    assert!(
        section.contains("ay::chc"),
        "migration doc must document ay::chc"
    );
    assert!(
        section.contains("ay::executor"),
        "migration doc must document ay::executor"
    );
    assert!(
        section.contains("ay::prelude"),
        "migration doc must document ay::prelude"
    );
    assert!(
        section.contains("ay::Solver"),
        "migration doc must document root flat import ay::Solver"
    );

    // Negative: removed/non-existent surfaces must not be advertised.
    assert!(
        !section.contains("ay::core"),
        "migration doc must NOT advertise ay::core (not a real module)"
    );
    assert!(
        !section.contains("ay::theories"),
        "migration doc must NOT advertise ay::theories (not a real module)"
    );
}
