// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parsed-assertion retention is session configuration: `(reset)` returns it
//! to what the host configured, whatever the discarded script switched on.

use super::*;

fn run(ctx: &mut Context, script: &str) {
    for command in &parse(script).expect("retention fixture parses") {
        ctx.process_command(command)
            .expect("retention fixture elaborates");
    }
}

const QUERY: &str = "(set-logic QF_UF) (declare-const p Bool) (assert p)";

/// A host that turned retention off gets it back off after `(reset)`, even
/// when the script it discarded had asked for proofs.
#[test]
fn reset_discards_script_armed_retention() {
    let mut fresh = Context::new();
    fresh.set_retain_parsed_assertions(false);
    run(&mut fresh, QUERY);

    let mut reused = Context::new();
    reused.set_retain_parsed_assertions(false);
    run(&mut reused, "(set-option :produce-proofs true)");
    assert!(
        reused.retains_parsed_assertions(),
        ":produce-proofs true arms retention for the script that set it"
    );
    run(&mut reused, "(reset)");
    run(&mut reused, QUERY);

    assert!(!reused.retains_parsed_assertions());
    assert_eq!(
        reused.assertions_parsed().len(),
        fresh.assertions_parsed().len(),
        "the query after (reset) must retain exactly what a fresh context retains"
    );
    assert!(reused.assertions_parsed().is_empty());
}

/// A retaining host stays retaining across `(reset)`.
#[test]
fn reset_keeps_host_configured_retention() {
    for retain in [true, false] {
        let mut ctx = Context::new();
        ctx.set_retain_parsed_assertions(retain);
        run(&mut ctx, "(reset)");
        run(&mut ctx, QUERY);
        assert_eq!(ctx.retains_parsed_assertions(), retain);
        assert_eq!(ctx.assertions_parsed().len(), usize::from(retain));
    }
}

/// A retention snapshot restores both the effective value and the policy that
/// a later `(reset)` returns to.
#[test]
fn parsed_retention_snapshot_restores_effective_value_and_policy() {
    let mut ctx = Context::new();
    ctx.set_retain_parsed_assertions(false);
    run(&mut ctx, "(set-option :produce-proofs true)");
    let snapshot = ctx.parsed_retention();

    ctx.set_retain_parsed_assertions(true);
    ctx.restore_parsed_retention(snapshot);
    assert_eq!(ctx.parsed_retention(), snapshot);
    assert!(ctx.retains_parsed_assertions(), "effective value restored");
    run(&mut ctx, "(reset)");
    assert!(!ctx.retains_parsed_assertions(), "policy restored");
}
