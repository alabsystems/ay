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

#[path = "knob_census/harness.rs"]
mod harness;
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

// ─── THE HARNESS-FLAG HALF ───────────────────────────────────────────────────
//
// WHAT THE TESTS ABOVE DO NOT COVER, stated so nobody reads them as wider than
// they are. Their universe is `Knob::label` — 226 variants parsed out of
// `src/tune/knob.rs` — and their file set is `src/`. So:
//
//   * a flag that is not a `Knob` is invisible to them. `--lu` was exactly
//     that: a bare name pushed onto `milp_profile`'s own `switch_flags` vector,
//     read into a `let`, echoed, and carried nowhere. It survived the
//     reader-without-writer gate because it had neither a reader NOR a writer
//     in the sense that gate means.
//   * `examples/` is not walked at all, and `examples/` is where every
//     harness-local flag lives.
//   * whether the SURFACE a flag was typed at can carry it is not asked. A
//     perfectly wired knob still measures nothing on a harness that parses the
//     engine tables and never calls `engine_cli::apply` — `AY_LP_ONLY`'s
//     missing `tune` frame in its original form, and `milp_speed` in this one.
//
// The three tests below close the third bullet mechanically — at FILE
// granularity (`no_harness_parses_engine_flags_without_applying_them`) and at
// NAME granularity (`no_surface_accepts_a_flag_only_solve_can_carry`) — and put
// the first two behind a disposition table. None of them can prove a carrier
// exists; that still takes a measurement. What they make impossible is adding a
// lever nobody looked at.
//
// ─── WHAT A GREEN RUN OF THESE THREE DOES *NOT* MEAN ─────────────────────────
//
// Written down here because the failure this whole file exists to stop is a
// green signal read as wider coverage than it has.
//
//   1. NOT "every flag moves something". No source scan can decide that, and an
//      identical A/B does not decide it either: `--no-cold-lu` is fully wired —
//      reader, writer in `src/opts/`, its own builder — and is bit-identical to
//      default on haprp (450 nodes / 649 LUFACT / 374 REFAC, 3 interleaved
//      reps) because m < 3 000 puts its band gate out of reach. That is the
//      negative control that killed the two purely differential scanner
//      prototypes, and it is why the INERT half of HARNESS_FLAGS is a written
//      disposition and not a computed one.
//
//   2. NOT "`--lu` is caught by a scanner". It is caught by the DISPOSITION
//      TABLE: `every_harness_declared_flag_is_dispositioned` fires on any
//      harness-local name nobody has written down, and `--lu` is in the table
//      saying INERT. Textually `--lu` HAS a reader (`let lu = flags.has("lu")`)
//      and would satisfy any reader-existence test; only a human noticed the
//      reader reaches nothing but a banner. Deleting its entry is the fire
//      proof, not a re-scan.
//
//   3. NOT "every name a surface accepts is dispositioned". The scan sees names
//      pushed onto a table called `switch_flags`/`switches`/`value_flags`/
//      `values`, and string literals inside a `parse_applied(..)` call. A name
//      reaching a parse table through a CONST — `ay-milp.rs`'s `DIAG_OWN_FLAGS`
//      (`--time-limit`, `--memory-budget`, `--row`, `--solution`) — is invisible
//      to it, and so is one built by a helper function. Const-array and
//      computed spellings are the standing hole; a new surface should pass its
//      names inline.
//
//      The same hole bounds `no_surface_accepts_a_flag_only_solve_can_carry`
//      from the other side: it fires on a surface that names `VALUE_FLAGS`, and
//      a surface that hand-rolls a table containing `"emit-cert"` without ever
//      naming the constant would slip past THAT test. It would still be caught
//      by `every_harness_declared_flag_is_dispositioned`, which sees the
//      literal — but only because the literal is inline. Two literal-blind
//      spellings at once (a const table, hand-rolled) defeat both.
//
//   4. NOT "the knob census covers these files". `scan.rs`'s universe is `src/`
//      and `Knob` variants; `examples/` has no `Knob` readers at all. The two
//      halves share a file and nothing else.
//
//   5. NOT "the 38 non-`Knob` CLI names are carrier-checked". They are not
//      `Knob` labels, so the census above cannot see them, and they are not
//      harness-local, so the disposition table does not hold them either. Their
//      carrier is `engine_cli::apply` and it is pinned by
//      `hand_rolled_names_are_declared` and `applied_flags_excludes_solve_stage`
//      in `src/engine_cli/tests.rs`, not here.

/// Harness-local flags: names a measurement surface adds to its parse tables
/// beyond `engine_cli`'s own. `apply` has never heard of any of them, so each
/// needs a reader in its own file, and each entry here records where.
///
/// Same contract as [`READER_ONLY_ALLOWED`]: a REASON per entry, not a list.
/// An INERT entry is allowed — `--lu` is deliberately not deleted, because six
/// `simplex.rs` docstrings cite it and erasing the flag would erase the trail —
/// but it must SAY it is inert, and the harness must say so at runtime too.
const HARNESS_FLAGS: &[(&str, &str, &str)] = &[
    (
        "examples/milp_profile.rs",
        "lu",
        "INERT, KNOWN, KEPT. Read at `main` into `let lu` and used only to pick the \
         banner text; `apply` cannot carry it because it is not in any builder table. \
         The lever the docstrings citing `--lu` actually used was the env var \
         `AY_MILP_LU=1`, live 939184496 (2026-07-14) .. 8875fea71 (2026-08-15), retired \
         to a constant `false` at 165cf57db. Measured on 5ebf652ba, milp_profile mip \
         mode on a synthetic m=1050 tall model, 3 interleaved reps: `--lu` leaves \
         `LUFACT count` in the same nonzero range as no flag at all (41..79 either \
         side), while `--no-tall-lu` — a real carrier on the same harness — drives it \
         to 0 in 3 reps of 3. Retained ONLY as the evidence trail; the banner prints \
         REQUESTED-BUT-INERT(no carrier).",
    ),
    (
        "examples/milp_profile.rs",
        "prefix-cols",
        "WIRED, harness-local. `flags.get(\"prefix-cols\")` is the required \
         comma-separated column list for the shared/proof/family modes and the run \
         panics without it, so an inert version could not survive one invocation. \
         Was the env var AY_MILP_PREFIX_COLS before B40b.",
    ),
    (
        "examples/milp_profile.rs",
        "obbt-cols",
        "WIRED, harness-local. `flags.get(\"obbt-cols\")` is the required path to the \
         column-index file for obbt mode; the mode `.expect()`s it, so it cannot be \
         inert. Was the env var AY_OBBT_COLS before B40b.",
    ),
    (
        "examples/milp_profile.rs",
        "basis-file",
        "WIRED, harness-local, by a SECOND reader: `basis_file_arg()` walks \
         `env::args()` directly. It is declared here only so strict parsing does not \
         refuse it and does not donate its value to `positional`. Was a retired env \
         var (B20).",
    ),
    (
        "examples/mps_solve.rs",
        "check-sol",
        "WIRED, harness-local, AND MOVED HERE from `engine_cli::VALUE_FLAGS`. \
         `flags.get(\"check-sol\")` at the foot of this file is the ONLY reader of the \
         name in the crate (`grep -rn '\"check-sol\"' src/` finds it in the flag tables \
         and nowhere else), so while it sat in the shared table `ay-milp solve \
         --check-sol f.sol` parsed cleanly and checked nothing. `solve` now refuses it \
         by name.",
    ),
    (
        "examples/mps_solve.rs",
        "dual-cutoff",
        "WIRED, harness-local, AND MOVED HERE from `engine_cli::VALUE_FLAGS`. The KNOB \
         is fully carried (writer src/opts/profile.rs:272, reader \
         src/bab/search_runtime.rs:103) — this is the WIRED-BUT-NOT-ON-THAT-SURFACE \
         shape, not a dead knob. `apply` has no builder for the name, so only this \
         file, which reads it by hand and rescales it into the model frame, could ever \
         honour it. Measured on 6f45bcf66, 2 interleaved reps: `ay-milp solve \
         aflow30a.mps 5 --dual-cutoff 0.0` was indistinguishable from no flag (both \
         `FEASIBLE 1459`, both an identical 11,304-byte certificate) and printed no \
         acknowledgement, while `mps_solve … --dual-cutoff 0.0` echoed `--dual-cutoff: \
         0.0 (file frame) -> 0 (model frame, obj_scale 1)` on both reps.",
    ),
    (
        "examples/mps_solve.rs",
        "seed-solution",
        "WIRED, in BOTH places, which is why it stays in `VALUE_FLAGS` as well: \
         `ay-milp.rs:283` reads it for `solve`, and this file reads it at line 160 to \
         adopt a warm start. Declared here because `parse_applied` supplies only what \
         `apply` carries, and `apply` does not carry this one.",
    ),
    (
        "examples/mps_solve.rs",
        "margin-row",
        "WIRED, harness-local. `flags.get(\"margin-row\")` selects the row, marks it \
         on a cloned model and calls `diag_margin_reframe_with`; a bad or absent row \
         exits 2. The same lever exists on the CLI as `ay-milp diag margin-row --row`.",
    ),
    (
        "examples/mps_solve.rs",
        "iter-ledger",
        "WIRED, harness-local, TWO-PART: it sets this file's ITER_LEDGER atomic AND \
         calls `ay_milp::enable_iter_ledger()`, without which the library never \
         accumulates and the flag printed an empty ledger (the B38 follow-up).",
    ),
    (
        "examples/mps_solve.rs",
        "allocstat",
        "WIRED, harness-local, by an `env::args()` scan rather than through `flags` \
         (the allocator hook at the top of the file runs before parsing exists). \
         Declared here so strict parsing accepts it. Was a retired env var (B20).",
    ),
    (
        "examples/milp_speed.rs",
        "time-limit",
        "WIRED, harness-local, with the env spelling as a fallback (`AY_MILP_TIME_LIMIT`), \
         added when this surface was found parsing the whole engine table and applying \
         none of it. `apply` does not carry `--time-limit`; this file reads it by hand \
         and builds the `SolveOpts` time limit from it.",
    ),
    (
        "examples/milp_speed.rs",
        "threads",
        "WIRED, harness-local, same repair as `--time-limit` above. The harness's own \
         comment records why it must be read here: ignoring the worker count `would \
         make its 8T comparison a mislabeled 1T run`. `apply` does not carry the name.",
    ),
    (
        "src/bin/ay-milp.rs",
        "no-emit-cert",
        "WIRED. Read in `cmd_solve` to suppress the certificate path, and again in \
         `solve_options.rs` where it drops the tree-certificate leaf budget unless the \
         caller asked for full evidence or set a budget explicitly.",
    ),
    (
        "src/bin/ay-milp.rs",
        "no-opt-tree",
        "WIRED. Read in `cmd_solve` to skip whole-tree optimality derivation.",
    ),
    (
        "src/bin/ay-milp.rs",
        "no-root-dual",
        "WIRED. Read in `cmd_solve` (`flags.has(\"no-root-dual\")`) to skip the ROOT DUAL \
         BOUND derivation — the partial dual evidence offered where the whole-tree proof \
         declined. Its two value siblings `--root-dual-rim` and `--root-dual-secs` are in \
         `VALUE_FLAGS` and read in the same block.",
    ),
    (
        "src/bin/ay-milp.rs",
        "deterministic",
        "WIRED, in the `ay_milp` bin SUBMODULE (`solve_options.rs`), which is why a \
         grep of `ay-milp.rs` alone finds no reader and must not be trusted: it calls \
         `SolveOpts::with_determinism(true)`.",
    ),
    (
        "src/bin/ay-milp.rs",
        "no-deterministic",
        "WIRED, in `solve_options.rs`: `SolveOpts::with_determinism(false)`. The \
         counterpart `--threads n>1` sets the same field implicitly.",
    ),
    (
        "src/bin/ay-milp.rs",
        "skip-finalize-reverify",
        "WIRED, in `solve_options.rs`: `SolveOpts::with_skip_finalize_reverify(true)`, \
         the opt-in that skips the tree-certificate emission self-verify (a duplicate \
         CHECK; the certificate bytes are identical either way). Deliberately NOT in \
         any engine builder table: it is `solve`'s own evidence-policy switch, like \
         its sibling `--tree-cert-leaves` in `VALUE_FLAGS`.",
    ),
    (
        "src/bin/ay-milp.rs",
        "phase-ledger",
        "WIRED, harness-local, REPORTING ONLY. Read once in `cmd_solve` into `let \
         ledger` and gating exactly one `eprintln!` that attributes this process's \
         wall across dispatch/read/parse/shape/session/solve/opt_tree/cert/require \
         plus the residual no phase claimed. It carries no engine option, skips no \
         phase and reorders nothing, so it is deliberately NOT in any builder table \
         and `apply` must never hear of it. Measured byte-identical verdicts and node \
         counts with it on and off on 8 instances (gt2 OPTIMAL 21166 / 4954 nodes, \
         flugpl OPTIMAL 1201500 / 1592, gr4x6 OPTIMAL 202.35 / 78, p0201 OPTIMAL 7615 \
         / 110, stein45inf INFEASIBLE / 933, mod008inf INFEASIBLE / 1025, neos859080 \
         INFEASIBLE / 197, g503inf INFEASIBLE / 3). The two `Instant::now()` calls it \
         needs are unconditional — ~20 ns each — because a clock read that only \
         happens under the flag cannot time the code path the flag exists to \
         measure. Written to open the `1.492 s + 26.51 us/node` least-squares \
         intercept that the campaign had been treating as a real fixed per-solve \
         cost; the ledger's residual is 0.1 ms over 167.84 s across 37 instances, \
         which is what makes the attribution a decomposition rather than an \
         estimate.",
    ),
];

/// A surface that ACCEPTS the engine flags must APPLY them.
///
/// THE DEFECT THIS STOPS, measured rather than argued. `milp_speed` handed
/// `VALUE_FLAGS` and `switch_flags()` to `Flags::parse` — 247 names — and never
/// called `engine_cli::apply`, so every engine knob typed at it parsed cleanly,
/// validated, and changed nothing. On `5ebf652ba`, `milp_speed 14 8 --trace`
/// and `milp_speed 14 8` produced byte-identical 98-byte stderr with zero
/// `--trace` lines across 2 reps each, while the same switch on `mps_solve`
/// (which does call `apply`) produced 250 trace lines / 21,913 bytes against
/// 576 unflagged, also 2 reps each. Same flag, same engine, same build.
///
/// This is the `AY_LP_ONLY` shape — a real knob that cannot apply on the
/// surface a measurement used — and it is the one the census could not see,
/// because nothing about the knob is wrong.
#[test]
fn no_harness_parses_engine_flags_without_applying_them() {
    let surfaces = harness::surfaces(root());
    assert!(
        surfaces.len() >= 4,
        "the harness scan found only {} flag-parsing surfaces — it stopped matching \
         the source, which would make this gate vacuous",
        surfaces.len()
    );
    let offenders: Vec<&harness::Surface> = surfaces
        .iter()
        .filter(|s| s.declares_engine_surface && !s.applies_engine_flags)
        .collect();
    assert!(
        offenders.is_empty(),
        "{} measurement surface(s) ACCEPT the whole engine flag surface and never \
         call `engine_cli::apply`. Every engine knob typed at them parses, validates \
         and changes NOTHING, so any A/B run there measured the same arm twice:\n\n{}\n\n\
         HOW TO FIX (pick one, and say which in the commit):\n\
         \x20 APPLY them — `opts = engine_cli::apply(&flags, opts)?`. It is a no-op when \
         no engine flag is passed (`touched` stays false), so an unflagged run stays \
         byte-identical.\n\
         \x20 STOP ACCEPTING them — hand `Flags::parse` only the names this harness reads. \
         A flag the parser accepts reads as a measurement lever and is not one.",
        offenders.len(),
        offenders
            .iter()
            .map(|s| format!("  {} (engine tables parsed, `apply` never called)", s.file))
            .collect::<Vec<_>>()
            .join("\n"),
    );
}

/// A surface may not ACCEPT a name that only `ay-milp solve` can carry.
///
/// # The defect this stops, and why the file-granular gate above cannot
///
/// [`no_harness_parses_engine_flags_without_applying_them`] asks one question:
/// does this file call `engine_cli::apply` at all. Every one of the five
/// measurement harnesses answered YES and was still broken, because they handed
/// [`ay_milp::engine_cli::VALUE_FLAGS`] to the parser — the `ay-milp solve`
/// SUBCOMMAND's table, a strict superset of `applied_flags()`. The difference
/// is the names only `solve` itself reads, and no amount of calling `apply`
/// makes a harness able to honour one of those: `apply` never reads them
/// either. Each harness accepted 13 to 16 such names.
///
/// This is the `AY_LP_ONLY` shape at NAME granularity — a real flag on a
/// surface that cannot apply it — and unlike the knob census it is decidable,
/// because both tables are `pub` and the test can just ask the library.
///
/// MEASURED on `6f45bcf66`, three interleaved reps each, load 57-69 on a
/// 14-core box. Counts, exit codes and file sizes only; nothing here is wall-
/// coupled:
///
///   * `cert_probe m 5 --require optimal` printed `require_certificates=0` and
///     `evidence=witness+uncertified-dual-bound` on 3 of 3, while `cert_probe
///     m 5 1` — the positional the harness actually reads — printed
///     `require_certificates=1` and `evidence=witness-only` on 3 of 3. Worse
///     than inert: the flag NAMED one arm and MEASURED the other, on the
///     harness that exists to price certificate requirements.
///   * `cert_probe m 5 --emit-cert F` exited 0 leaving F ABSENT on 3 of 3;
///     `ay-milp solve m 5 --emit-cert F` wrote 11,304 bytes on 3 of 3.
///
/// # Why the reader test is deliberately generous
///
/// A name is treated as read if it appears as a QUOTED LITERAL anywhere in the
/// entry point's spliced text. That over-matches. It is the right direction to
/// over-match in: a missed reader would make this gate name a working surface,
/// and a gate that cries wolf gets muted — this repo has refused two scanner
/// proposals for precisely that, one of which separated the known-good and
/// known-bad cases BACKWARDS. Over-matching only ever makes this quieter, and
/// the ONE surface that legitimately holds `VALUE_FLAGS` — `src/bin/ay-milp.rs`
/// — passes on the strict test too: it reads all fourteen.
#[test]
fn no_surface_accepts_a_flag_only_solve_can_carry() {
    let applied = ay_milp::engine_cli::applied_flags();
    let solve_only: Vec<&str> = ay_milp::engine_cli::VALUE_FLAGS
        .iter()
        .copied()
        .filter(|name| !applied.contains(name))
        .collect();
    assert!(
        !solve_only.is_empty(),
        "VALUE_FLAGS and applied_flags() have converged, so this gate can no longer \
         separate a harness table from the solve table and is vacuous"
    );
    let surfaces = harness::surfaces(root());
    assert!(
        surfaces.len() >= 4,
        "the harness scan found only {} flag-parsing surfaces — it stopped matching \
         the source, which would make this gate vacuous",
        surfaces.len()
    );
    let mut offenders = Vec::new();
    for surface in &surfaces {
        if !surface.uses_solve_value_table {
            continue;
        }
        let dead: Vec<&str> = solve_only
            .iter()
            .copied()
            .filter(|name| !surface.unit.contains(&format!("\"{name}\"")))
            .collect();
        if !dead.is_empty() {
            offenders.push(format!(
                "  {} accepts {} solve-only name(s) it cannot carry:\n      {}",
                surface.file,
                dead.len(),
                dead.iter()
                    .map(|n| format!("--{n}"))
                    .collect::<Vec<_>>()
                    .join(" "),
            ));
        }
    }
    assert!(
        offenders.is_empty(),
        "{} surface(s) hand `VALUE_FLAGS` to `Flags::parse` and accept names only \
         `ay-milp solve` reads. Each such flag parses, validates, and is DROPPED — and \
         when the harness has its own spelling for the same setting, the run is \
         labelled with the flag and measured without it:\n\n{}\n\n\
         HOW TO FIX (pick one, and say which in the commit):\n\
         \x20 CALL `engine_cli::parse_applied(args, own_values, own_switches)` — it \
         supplies exactly what `apply` carries, and the surface names the handful it \
         reads itself. Those names then need a HARNESS_FLAGS disposition, which is the \
         point.\n\
         \x20 KEEP `VALUE_FLAGS` only if the surface genuinely READS the solve-only \
         names, as `src/bin/ay-milp.rs` does.",
        offenders.len(),
        offenders.join("\n"),
    );
}

/// Every flag a harness adds to its own parse tables must be dispositioned.
///
/// This one cannot prove a carrier — no source scan can, which is why the
/// previous two attempts at a behavioural scanner failed, one of them
/// separating the known-good/known-bad pair backwards. What it CAN do is make
/// an undispositioned harness flag impossible: a name reaches
/// [`HARNESS_FLAGS`] only when somebody has written down where it is read, or
/// written down that it is read nowhere.
///
/// It fires on `--lu` (which is why the entry exists and says INERT) and is
/// silent on every engine flag, because engine flags come from `engine_cli`'s
/// tables and are never pushed by a harness.
#[test]
fn every_harness_declared_flag_is_dispositioned() {
    let surfaces = harness::surfaces(root());
    let mut undispositioned = Vec::new();
    for surface in &surfaces {
        for flag in &surface.local_flags {
            if !HARNESS_FLAGS
                .iter()
                .any(|(file, name, _)| *file == surface.file && name == flag)
            {
                undispositioned.push(format!("  {} declares --{flag}", surface.file));
            }
        }
    }
    assert!(
        undispositioned.is_empty(),
        "{} harness-local flag(s) are declared in a parse table and dispositioned \
         nowhere. `engine_cli::apply` has never heard of them, so each one either has \
         a reader in its own file or is a dead lever:\n\n{}\n\n\
         Add each to HARNESS_FLAGS in this file with the reader site, or with the \
         word INERT and the evidence that it moves nothing.",
        undispositioned.len(),
        undispositioned.join("\n"),
    );
    // And the mirror: a disposition that names a flag no harness declares is a
    // stale suppression, exactly as in `every_exemption_carries_a_reason`.
    let stale: Vec<String> = HARNESS_FLAGS
        .iter()
        .filter(|(file, name, _)| {
            !surfaces
                .iter()
                .any(|s| s.file == *file && s.local_flags.iter().any(|f| f == name))
        })
        .map(|(file, name, _)| format!("  {file} --{name}"))
        .collect();
    assert!(
        stale.is_empty(),
        "these dispositions name flags no harness declares any more:\n{}",
        stale.join("\n"),
    );
    for (file, flag, reason) in HARNESS_FLAGS {
        assert!(
            reason.len() >= 40,
            "disposition for {file} --{flag} needs a REASON, not a note: {reason:?}"
        );
    }
}

/// The harness census table: `cargo test -p ay-milp --release --test knob_census \
/// -- --nocapture emit_the_harness_census` reproduces it.
#[test]
fn emit_the_harness_census() {
    println!(
        "file\tdeclares_engine_surface\tapplies_engine_flags\tuses_solve_value_table\tlocal_flags"
    );
    for s in harness::surfaces(root()) {
        println!(
            "{}\t{}\t{}\t{}\t{}",
            s.file,
            s.declares_engine_surface,
            s.applies_engine_flags,
            s.uses_solve_value_table,
            if s.local_flags.is_empty() {
                "-".to_string()
            } else {
                s.local_flags.join(",")
            },
        );
    }
    let applied = ay_milp::engine_cli::applied_flags();
    let solve_only: Vec<&str> = ay_milp::engine_cli::VALUE_FLAGS
        .iter()
        .copied()
        .filter(|n| !applied.contains(n))
        .collect();
    println!(
        "# applied_flags={} VALUE_FLAGS={} solve_only={} [{}]",
        applied.len(),
        ay_milp::engine_cli::VALUE_FLAGS.len(),
        solve_only.len(),
        solve_only.join(","),
    );
}
