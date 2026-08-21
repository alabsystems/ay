// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE GATE: a tuning knob may not have a reader and no writer.
//!
//! # The defect this stops
//!
//! `examples/mps_solve.rs` parses arguments with `engine_cli::Flags::parse`,
//! which used to accept **any** bare `--x` as a switch. So a flag whose knob
//! has no writer — no [`ay_milp::EngineEconomics`] field, no builder, no
//! `engine_cli` table entry — parsed cleanly, set nothing, and the run
//! reported its result under the flagged name. The A/B measured the same arm
//! twice, with no error, no warning, and nothing in the output that said so.
//!
//! The parser now REFUSES a flag that is in no table (naming the nearest known
//! spelling, exit 2), which closes the half of the hole an unknown NAME made.
//! This gate closes the other half, which no parser can see: a name that IS in
//! the table and still carries nothing.
//!
//! This campaign has paid for that four times: `--root-cuts-per-round`,
//! `--gmi-rounds` (plus three presence gates), `--eager-perturb-mode`, and
//! `--no-float`, which invalidated a brief's premise by silently measuring the
//! float lane it claimed to have disabled. A census at the fifth incident
//! counted 64 knobs still in that state, including families that could never be
//! switched on by any surface at all: `--rlt`, `--cut-warm`, `--ms-dive`,
//! `--relax-lift`, `--devex`, `--bump-btf`, `--node-gmi*`, `--orbitope-branch*`.
//!
//! Finding them by hand is what failed four times. This test is the mechanism.
//!
//! # What counts as a writer
//!
//! Only `src/opts/` — the modules where `EngineEconomics` lowers a typed
//! setting into the [`Profile`]. A `.with(Knob::X, ..)` inside `bab.rs` is a
//! sub-solve override or a guard-test fixture; it configures the engine from
//! inside the engine and gives an operator no way in. Counting those as
//! carriers is exactly how `--node-gmi` looked wired while being unreachable.
//!
//! # And the mirror image
//!
//! [`no_knob_has_a_writer_and_no_reader`] catches the other half: a flag with a
//! full carrier chain whose knob nothing reads. `--node-cuts` was that — field,
//! builder, CLI entry, profile line, and no reader anywhere.

use std::path::Path;

#[path = "knob_census/scan.rs"]
mod scan;

use scan::{census, Row};

/// Knobs that may legitimately have a reader and no writer.
///
/// A bare list would rot into a suppression file, so each entry carries the
/// REASON it is exempt, and the test prints the reason when it is the thing
/// standing between a knob and a carrier. The bar for an entry: the knob is
/// deliberately compile-time, and giving it a runtime carrier would be a lie
/// about what the build can do.
///
/// It is currently empty, and that is the point — every knob in this crate is
/// reachable from the surface that names it.
const READER_ONLY_ALLOWED: &[(&str, &str)] = &[];

/// Knobs that may legitimately have a writer and no reader.
///
/// Same contract as [`READER_ONLY_ALLOWED`]: a reason per entry, not a list.
const WRITER_ONLY_ALLOWED: &[(&str, &str)] = &[];

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn describe(row: &Row) -> String {
    let readers = row
        .readers
        .iter()
        .map(|s| format!("{}:{} [tune::{}]", s.file, s.line, s.how))
        .collect::<Vec<_>>()
        .join(", ");
    let writers = if row.writers.is_empty() {
        if row.internal_writers.is_empty() {
            "NONE".to_string()
        } else {
            format!(
                "NONE reachable (internal only: {})",
                row.internal_writers
                    .iter()
                    .map(|s| format!("{}:{}", s.file, s.line))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    } else {
        row.writers
            .iter()
            .map(|s| format!("{}:{}", s.file, s.line))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "  Knob::{} (--{})\n      read by : {}\n      written : {}\n      default : {}",
        row.variant,
        row.label,
        if readers.is_empty() { "NONE" } else { &readers },
        writers,
        if row.default.is_empty() {
            "-"
        } else {
            &row.default
        },
    )
}

const HOW_TO_FIX: &str = "\n\
HOW TO FIX (pick one, and say which in the commit):\n\
  WIRE it — the feature is reachable and someone may want to A/B it:\n\
    1. add a field to `EngineEconomics` (src/opts.rs),\n\
    2. add a builder + a lowering line (src/opts/carriers.rs is the file for this),\n\
    3. add the flag to BOOL_BUILDERS / USIZE_BUILDERS / FLOAT_BUILDERS\n\
       (and VALUE_FLAGS for a value flag) in src/engine_cli.rs.\n\
    If the reader sits on a lane that installs no `tune::activate_caller`\n\
    frame, use the TWO-LAYER pattern: read the typed `SolveOpts` value FIRST\n\
    and fall through to `tune` behind it. Precedents in-tree:\n\
    `EngineEconomics::eager_perturb_mode` and `session::float_lane_enabled`.\n\
  RETIRE it — the reader is vestigial or the feature is gone: delete the knob,\n\
    the reader and the flag. A dead flag in the CLI surface is worse than no\n\
    flag, because it reads as a measurement lever and is not one.\n\
  EXEMPT it — only if the knob is deliberately compile-time: add it to\n\
    READER_ONLY_ALLOWED in this file WITH A REASON.";

#[test]
fn no_knob_has_a_reader_and_no_writer() {
    let rows = census(root());
    assert!(
        rows.len() > 200,
        "the scan found only {} knobs — it stopped matching the source, which \
         would make this gate vacuous",
        rows.len()
    );
    let offenders: Vec<&Row> = rows
        .iter()
        .filter(|r| !r.readers.is_empty() && r.writers.is_empty())
        .filter(|r| !READER_ONLY_ALLOWED.iter().any(|(k, _)| *k == r.variant))
        .collect();
    assert!(
        offenders.is_empty(),
        "{} knob(s) have a READER and NO WRITER. Their flags parse as bare \
         switches and change nothing, so any A/B that set one measured the \
         same arm twice:\n\n{}\n{}",
        offenders.len(),
        offenders
            .iter()
            .map(|r| describe(r))
            .collect::<Vec<_>>()
            .join("\n"),
        HOW_TO_FIX
    );
}

#[test]
fn no_knob_has_a_writer_and_no_reader() {
    let rows = census(root());
    let offenders: Vec<&Row> = rows
        .iter()
        .filter(|r| !r.writers.is_empty() && r.readers.is_empty())
        .filter(|r| !WRITER_ONLY_ALLOWED.iter().any(|(k, _)| *k == r.variant))
        .collect();
    assert!(
        offenders.is_empty(),
        "{} knob(s) have a full carrier chain and NO READER. The flag parses, \
         validates, lowers into the profile — and no code consults it:\n\n{}\n{}",
        offenders.len(),
        offenders
            .iter()
            .map(|r| describe(r))
            .collect::<Vec<_>>()
            .join("\n"),
        HOW_TO_FIX
    );
}

/// Nothing may be exempted without a reason.
///
/// The allow-lists are the one place this gate can be silenced, so they get
/// their own guard: an entry with an empty reason is a bare suppression, which
/// is the shape this whole test exists to prevent.
#[test]
fn every_exemption_carries_a_reason() {
    for (knob, reason) in READER_ONLY_ALLOWED.iter().chain(WRITER_ONLY_ALLOWED) {
        assert!(
            reason.len() >= 40,
            "exemption for {knob} needs a REASON, not a note: {reason:?}"
        );
    }
    let rows = census(root());
    let stale: Vec<&str> = READER_ONLY_ALLOWED
        .iter()
        .chain(WRITER_ONLY_ALLOWED)
        .map(|(k, _)| *k)
        .filter(|k| !rows.iter().any(|r| r.variant == *k))
        .collect();
    assert!(
        stale.is_empty(),
        "these exemptions name knobs that no longer exist: {stale:?}"
    );
}

/// The census table itself: `cargo test -p ay-milp --release --test knob_census \
/// -- --nocapture emit_the_knob_census` reproduces it.
///
/// It is a test rather than a script so it cannot drift from the gate: both read
/// the same scan of the same source.
#[test]
fn emit_the_knob_census() {
    let rows = census(root());
    println!(
        "variant\tflag\tn_readers\tn_writers\tn_internal_writers\tdefault\tcached\t\
         reader_file_installs_frame\treader_sites\twriter_sites"
    );
    for r in &rows {
        println!(
            "{}\t--{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            r.variant,
            r.label,
            r.readers.len(),
            r.writers.len(),
            r.internal_writers.len(),
            if r.default.is_empty() {
                "-"
            } else {
                &r.default
            },
            r.cached,
            r.file_installs_frame,
            join(&r.readers),
            join(&r.writers),
        );
    }
    println!(
        "# {} knobs; {} reader-without-writer; {} writer-without-reader; {} unread-and-unwritten",
        rows.len(),
        rows.iter()
            .filter(|r| !r.readers.is_empty() && r.writers.is_empty())
            .count(),
        rows.iter()
            .filter(|r| r.readers.is_empty() && !r.writers.is_empty())
            .count(),
        rows.iter()
            .filter(|r| r.readers.is_empty() && r.writers.is_empty())
            .count(),
    );
}

fn join(sites: &[scan::Site]) -> String {
    if sites.is_empty() {
        return "-".to_string();
    }
    sites
        .iter()
        .map(|s| format!("{}:{}:{}", s.file, s.line, s.how))
        .collect::<Vec<_>>()
        .join(";")
}
