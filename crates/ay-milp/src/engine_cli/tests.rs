// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Test module for the engine CLI's parsing and flag-application contracts.

use super::{apply, edit_distance, switch_flags, Flags, SolveOpts, VALUE_FLAGS};

fn parse(args: &[&str]) -> Result<Flags, String> {
    let owned: Vec<String> = args.iter().map(|s| (*s).to_string()).collect();
    Flags::parse(&owned, VALUE_FLAGS, &switch_flags())
}

#[test]
fn known_switches_and_value_flags_still_parse() {
    let f = parse(&[
        "model.mps",
        "60",
        "--devex",
        "--no-cuts",
        "--gmi-rounds",
        "7",
        "--root-cuts-per-round=40",
        "--trace",
    ])
    .expect("every one of these is a known flag");
    assert_eq!(f.positional, ["model.mps", "60"]);
    assert!(f.has("devex") && f.has("no-cuts") && f.has("trace"));
    assert_eq!(f.get("gmi-rounds").map(String::as_str), Some("7"));
    assert_eq!(f.get("root-cuts-per-round").map(String::as_str), Some("40"));
}

/// A known flag still reaches the ENGINE, not just the argument bag.
#[test]
fn a_known_flag_still_lowers_into_the_engine() {
    let f = parse(&["--devex", "--gmi-rounds", "7"]).expect("known flags");
    let opts = apply(&f, SolveOpts::new()).expect("applies");
    let want = crate::EngineEconomics::default()
        .with_force_devex(true)
        .with_gmi_rounds(7);
    assert_eq!(opts.engine(), want);
}

/// The refusal for `args`. (`Flags` is not `Debug`, so `expect_err` is
/// not available; the panic message names the argv instead.)
fn refusal(args: &[&str]) -> String {
    match parse(args) {
        Err(e) => e,
        Ok(_) => panic!("{args:?} parsed cleanly — this is the defect, not the fix"),
    }
}

/// The defect: `--devx` used to parse as a switch and change nothing.
#[test]
fn a_misspelled_switch_is_refused_with_the_nearest_spelling() {
    let e = refusal(&["model.mps", "--devx"]);
    assert!(e.contains("--devx"), "{e}");
    assert!(e.contains("--devex"), "{e}");
}

/// The worse defect: a misspelled VALUE flag donated its value to
/// `positional`, where `mps_solve` reads a seed-solution path.
#[test]
fn a_misspelled_value_flag_does_not_leak_its_value_into_positionals() {
    let e = refusal(&["model.mps", "60", "--gmi-round", "7"]);
    assert!(e.contains("--gmi-round"), "{e}");
    assert!(e.contains("--gmi-rounds"), "{e}");
}

#[test]
fn nonsense_is_refused_without_a_bogus_suggestion() {
    let e = refusal(&["model.mps", "--total-nonsense-zz"]);
    assert!(e.contains("--total-nonsense-zz"), "{e}");
    assert!(!e.contains("did you mean"), "no flag is near this: {e}");
}

#[test]
fn a_bare_double_dash_ends_flag_parsing() {
    let f = parse(&["--devex", "--", "--not-a-flag"]).expect("`--` ends flags");
    assert!(f.has("devex"));
    assert_eq!(f.positional, ["--not-a-flag"]);
}

#[test]
fn a_switch_still_refuses_a_value_and_a_value_flag_still_needs_one() {
    assert!(refusal(&["--devex=1"]).contains("takes no value"));
    assert!(refusal(&["--gmi-rounds"]).contains("needs a value"));
}

/// A name in both tables would resolve as a value flag and silently
/// swallow the next argument.
#[test]
fn the_value_and_switch_tables_are_disjoint_and_duplicate_free() {
    let switches = switch_flags();
    for (i, name) in switches.iter().enumerate() {
        assert!(
            !VALUE_FLAGS.contains(name),
            "--{name} is both a value flag and a switch"
        );
        assert!(
            !switches[i + 1..].contains(name),
            "--{name} appears twice in the switch table"
        );
    }
    for (i, name) in VALUE_FLAGS.iter().enumerate() {
        assert!(
            !VALUE_FLAGS[i + 1..].contains(name),
            "--{name} appears twice in VALUE_FLAGS"
        );
    }
}

/// Every builder that takes a value must be reachable: a name in
/// `USIZE_BUILDERS`/`FLOAT_BUILDERS` and not in `VALUE_FLAGS` now REJECTS
/// the invocation that sets it (before this change it silently donated the
/// value to the positionals).
#[test]
fn every_value_builder_is_declared_a_value_flag() {
    for &(name, _) in super::USIZE_BUILDERS {
        assert!(
            VALUE_FLAGS.contains(&name),
            "--{name} (usize) not in VALUE_FLAGS"
        );
    }
    for &(name, _) in super::FLOAT_BUILDERS {
        assert!(
            VALUE_FLAGS.contains(&name),
            "--{name} (float) not in VALUE_FLAGS"
        );
    }
}

/// [`super::applied_flags`] is a CONTRACT read by `ay-milp diag`'s front
/// door: a name it lists is accepted there, a name it omits is refused. Both
/// halves have to stay true, so every entry must be a flag the parser knows.
#[test]
fn every_applied_flag_is_a_flag_the_parser_knows() {
    let switches = switch_flags();
    for name in super::applied_flags() {
        assert!(
            VALUE_FLAGS.contains(&name) || switches.contains(&name),
            "--{name} is applied but is neither a value flag nor a switch"
        );
    }
}

/// The hand-rolled arms of [`apply`] are the half no builder table can
/// enumerate, so they are declared once and pinned here. If `apply` grows an
/// arm that reads a name absent from `HAND_ROLLED`, `diag` refuses a flag it
/// could have honoured — loud, but wrong, and this is the reminder.
#[test]
fn hand_rolled_names_are_declared_value_flags() {
    for &name in super::HAND_ROLLED {
        assert!(
            VALUE_FLAGS.contains(&name),
            "--{name} is hand-rolled in apply() but not in VALUE_FLAGS"
        );
    }
}

/// `applied_flags` must EXCLUDE the `solve`-stage names that share the
/// table. Accepting `--emit-cert` on a diagnostic that emits no certificate
/// is the dead-flag failure wearing a different hat.
#[test]
fn applied_flags_excludes_the_solve_only_names() {
    let applied = super::applied_flags();
    // NOTE `--verify-after` is deliberately absent from this list: it looks
    // like a solve-stage name but it IS an `EngineEconomics` builder
    // (`FLOAT_BUILDERS`), so `apply` reads it and `diag` should accept it.
    // The first draft of this test asserted otherwise and failed, which is
    // the point of deriving `applied_flags` from the tables instead of from
    // anyone's memory of what the flags do.
    for name in [
        "emit-cert",
        "require",
        "threads",
        "seed",
        "time-limit",
        "check-sol",
        "emit-witness",
        "witness-format",
    ] {
        assert!(
            !applied.contains(&name),
            "--{name} is a solve-stage flag; apply() does not read it"
        );
    }
    // …and INCLUDE the ones it does read, from all five sources.
    for name in ["devex", "trace", "gmi-rounds", "flip-share", "child-order"] {
        assert!(applied.contains(&name), "--{name} is applied by apply()");
    }
}

/// `names_given` reports what was on the command line, values and switches
/// alike — the input `diag`'s refusal is computed from.
#[test]
fn names_given_reports_values_and_switches_together() {
    let f = parse(&["model.mps", "--devex", "--gmi-rounds", "7", "--trace"]).expect("known");
    assert_eq!(f.names_given(), ["devex", "gmi-rounds", "trace"]);
    let bare = parse(&["model.mps"]).expect("no flags at all");
    assert!(bare.names_given().is_empty());
}

#[test]
fn edit_distance_is_the_usual_one() {
    assert_eq!(edit_distance("devx", "devex"), 1);
    assert_eq!(edit_distance("", "abc"), 3);
    assert_eq!(edit_distance("kitten", "sitting"), 3);
    assert_eq!(edit_distance("same", "same"), 0);
}
