// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The original `rem_u32_digits` query on the default native proof route,
//! under a counted diagnostic owner.
//!
//! The owner was a 20 s wall. In the debug test profile the route spent
//! 18-19 s solving, 1.0 s exporting and 0.9 s in the wire check on an idle
//! fast core, so that wall left it under half a second and the test failed
//! whenever the host was loaded ("same diagnostic owner through export").
//! The route's work is not the clock's: it spent the same 24,708 CDCL
//! conflicts under a 20 s wall, a 600 s wall and no wall, at f6555db0b and at
//! 7726721a1, which added this test and whose route that wall already cut.
//! So the owner is now a work ceiling (`ay_core::resource::enter_work_ceiling`),
//! a GuardTree node the executor's deadline cell reads as a passed deadline:
//! a route that needs more counted work ends `unknown` at the same step on
//! every host and under any load. The wall that remains is a backstop against
//! a hang, as production's counted owners keep one for the phases that charge
//! no unit (`ay-chc`'s `ExecutorWork`).
//!
//! What the count saw, measured at f6555db0b in the debug test profile: the
//! executor's search, which refutes the query at 3,832 units (0.8 s), and the
//! 20,876 units that the residual-trust rescue's strict bit-blast of the whole
//! query (`rescue_bv_bitblast_collapse`) reports from the SAT sweep of its
//! exact-division attempt (about 4 s). What it did not see: that bit-blast's
//! case split before the sweep (`sat_sweep::split`), whose leaf solves then
//! reported no unit (about 13 s), because ay-sat reported a solve's conflicts
//! at its restarts only; every solve now charges them at its stop polls and
//! at its end (`ay-sat`'s `solver/work_report.rs`). That attempt refused, and
//! the cascade's BvUremBound joint then certified the query. The joint is now
//! asked where the rescue would pay for the exact divider
//! (`guarded/urem_bound/before_division.rs`), so the route no longer sweeps:
//! 899 units in all, and 0.2 s instead of 18 s to the end of the solve, with
//! the same exported document. The count does not see the export and the
//! wire check either; the test bounds the export by twice its measured size.
//! Their time belongs to the release-profile R35 and consumer rows.

use super::*;

const REM_DIGITS: &str = include_str!("rem_u32_digits.smt2");

/// Work units (CDCL conflicts plus split-loop round trips) the whole native
/// route spends on the original, measured with the BvUremBound joint asked
/// ahead of the rescue's exact divider: 899 conflicts and no round trips, all
/// inside `execute_all`. While ay-sat reported conflicts at its restarts only,
/// the count read 897: the strict bit-blast check's replay
/// (`validate_bv_bitblast_semantics`) ran a local solve of 115 conflicts whose
/// last 2 came after its last restart, and its solver was dropped unreported.
/// It was 24,708 at f6555db0b, 20,876 of them in the residual-trust rescue's
/// sweep. The native check, the export and the wire check spend none.
const REM_DIGITS_MEASURED_WORK: u64 = 899;

/// The diagnostic owner: half again the measured route, counted. The
/// rescue's exact-division sweep, should the route pay for it again (20,876
/// units), crosses it many times over.
const REM_DIGITS_WORK_CEILING: u64 = REM_DIGITS_MEASURED_WORK + REM_DIGITS_MEASURED_WORK / 2;

/// The exported document on the original, measured at f6555db0b: byte-identical
/// under a 20 s wall, a 600 s wall and no wall, and on fast and slow cores, and
/// with the joint asked ahead of the rescue's exact divider (the same joint's
/// document). The count never sees the printer or the wire check; this bounds
/// what they read.
const REM_DIGITS_MEASURED_DOCUMENT_BYTES: usize = 2_655_793;

/// The `step` commands of that document.
const REM_DIGITS_MEASURED_WIRE_STEPS: usize = 9_507;

/// A wall far beyond the route (about 20 s idle in the debug test profile,
/// 85 s as one of four copies on two slow cores). It ends a hang; it does not
/// bound the route.
const REM_DIGITS_WALL_BACKSTOP: std::time::Duration = std::time::Duration::from_secs(600);

/// The work units a counted owner's node has recorded, nested work included.
fn work_units(owner: &ay_core::resource::Guard) -> u64 {
    let work = owner.ledger();
    work.sat_conflicts.saturating_add(work.split_round_trips)
}

/// A fresh proof-producing executor whose only wall is the backstop.
fn backstopped_executor() -> (Executor, ay_core::time::Instant) {
    let mut executor = Executor::new();
    let started = ay_core::time::Instant::now();
    let backstop = started
        .checked_add(REM_DIGITS_WALL_BACKSTOP)
        .expect("finite wall backstop");
    executor.set_deadline(Some(backstop));
    executor.set_produce_proofs(true);
    (executor, started)
}

#[test]
fn exact_rem_u32_digits_keeps_complete_strict_proof_in_native_diagnostic() {
    use sha2::{Digest, Sha256};
    // A bounded native regression, not an invented standalone CLI acceptance
    // grant or a replacement for the seven original 30-second consumer rows.
    let owner = ay_core::resource::enter_work_ceiling(Some(REM_DIGITS_WORK_CEILING));
    let ledger = ay_core::resource::current_guard().expect("the counted owner is entered");
    let (mut executor, started) = backstopped_executor();
    let mut previous = started;
    let mut phase = |name: &str| {
        let now = ay_core::time::Instant::now();
        eprintln!(
            "original rem_u32_digits phase={name} phase_ns={} elapsed_ns={} work_units={}",
            now.saturating_duration_since(previous).as_nanos(),
            now.saturating_duration_since(started).as_nanos(),
            work_units(&ledger)
        );
        previous = now;
    };
    assert_eq!(REM_DIGITS.len(), 2957);
    assert_eq!(
        format!("{:x}", Sha256::digest(REM_DIGITS)),
        "6d7b2def6ce2bebfffcdf648b6e3148b9bc2b5c4da4fe27f3b675a99a0efe70e"
    );
    let results = executor
        .execute_all(&ay_frontend::parse(REM_DIGITS).expect("original query"))
        .expect("actual default native proof route");
    phase("solve");
    assert_eq!(
        results,
        ["unsat"],
        "{:?} after {} of {REM_DIGITS_WORK_CEILING} work units",
        executor.unknown_reason(),
        work_units(&ledger)
    );
    let proof = executor
        .last_proof()
        .cloned()
        .expect("requested actual proof");
    assert_strict(&mut executor, &proof);
    phase("native-proof-check");
    let document = executor
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("requested proof")
        .expect("source-bound proof export");
    phase("source-bound-export");
    assert_ne!(document, "");
    assert!(
        !document.contains(":rule hole") && !document.contains(":rule trust"),
        "native completeness must not conceal an unproved exported step"
    );
    // The native replay above checks semantics; this separate wire check reads
    // the actual exported bytes against the unchanged original declarations.
    // Both remain inside the same original diagnostic owner.
    let scope = ay_proof::ProblemScope::from_smtlib_source(REM_DIGITS);
    let wire = ay_proof::check_alethe_document(&document, &scope).unwrap_or_else(|error| {
        // Diagnostic only: retain the exact failed command without renewing the
        // original grant or turning a parser failure into an accepted proof.
        let command = match &error {
            ay_proof::AletheDefect::UnexpectedToken { pos, .. } => document
                .lines()
                .nth(pos.line)
                .map(|line| line.chars().take(512).collect::<String>()),
            _ => None,
        };
        panic!("original declaration-scoped Alethe document must round-trip: {error:?}; command={command:?}");
    });
    phase("alethe-wire-check");
    assert!(wire.steps > 0 && wire.assumes > 0, "nonempty wire replay");
    assert!(
        document.len() <= 2 * REM_DIGITS_MEASURED_DOCUMENT_BYTES
            && wire.steps <= 2 * REM_DIGITS_MEASURED_WIRE_STEPS,
        "the exported proof stays within twice its measured size: {} bytes, {} steps",
        document.len(),
        wire.steps
    );
    let spent = work_units(&ledger);
    assert!(
        spent >= REM_DIGITS_MEASURED_WORK / 2,
        "the counted owner must see the route's search and its counted assembly, \
         or it bounds less than it claims: {spent} work units"
    );
    assert!(
        !owner.spent() && !executor.make_proof_assembly_should_stop()(),
        "same diagnostic owner through export: {spent} of {REM_DIGITS_WORK_CEILING} work units"
    );
}

/// The negative twin: the same route under a sixteenth of its measured work
/// stops mid-search and fails closed, and the stop the test above asserts is
/// clear reports the spent owner. So the ceiling is an owner this route obeys.
#[test]
fn exact_rem_u32_digits_declines_without_proof_once_its_counted_owner_is_spent() {
    let allowance = REM_DIGITS_MEASURED_WORK / 16;
    let owner = ay_core::resource::enter_work_ceiling(Some(allowance));
    let ledger = ay_core::resource::current_guard().expect("the counted owner is entered");
    let (mut executor, _) = backstopped_executor();
    let results = executor
        .execute_all(&ay_frontend::parse(REM_DIGITS).expect("original query"))
        .expect("actual default native proof route");
    assert_eq!(results, ["unknown"], "{:?}", executor.unknown_reason());
    let spent = work_units(&ledger);
    assert!(
        owner.spent() && (allowance..REM_DIGITS_MEASURED_WORK).contains(&spent),
        "the count, not the wall, must stop the route mid-search: {spent} of {allowance}"
    );
    assert!(
        executor.make_proof_assembly_should_stop()(),
        "the assembly stop must read the spent counted owner"
    );
    assert!(
        !matches!(
            executor.try_export_last_proof_alethe_for_problem_scope(),
            Some(Ok(_))
        ),
        "a spent owner must export no proof"
    );
}
