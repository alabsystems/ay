// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! `parse_logic` must admit every attested SMT-LIB logic name.
//!
//! An unrecognized name is not a degraded run on this lane: it is
//! `ExecuteError::UnsupportedLogic`, which aborts the whole solve into NO
//! VERDICT. Sixteen real SMT-LIB names used to fall through that hole while
//! the external `ay` binary accepted all of them.

use super::super::logic::{parse_logic, Declaration};
use crate::program::AYProgram;

/// The SMT-LIB logic set, transcribed independently of the production table so
/// a typo in one is not silently mirrored by the other.
///
/// Source: the SMT-LIB / SMT-COMP division set, plus `AX`, `QF_AUFBVLIA`,
/// `QF_AUFBVNIA` and `QF_UFSLIA` — attested SMT-LIB logics without a recent
/// competition division — and `HORN`, which is attested but routes to the CHC
/// lane and is asserted separately below.
const ATTESTED: &[&str] = &[
    "ABV",
    "ABVFP",
    "ABVFPLRA",
    "ALIA",
    "ANIA",
    "AUFBV",
    "AUFBVDTLIA",
    "AUFBVDTNIA",
    "AUFBVDTNIRA",
    "AUFBVFP",
    "AUFDTLIA",
    "AUFDTLIRA",
    "AUFDTNIRA",
    "AUFFPDTNIRA",
    "AUFLIA",
    "AUFLIRA",
    "AUFNIA",
    "AUFNIRA",
    "AX",
    "BV",
    "BVFP",
    "BVFPLRA",
    "FP",
    "FPLRA",
    "LIA",
    "LRA",
    "NIA",
    "NRA",
    "QF_ABV",
    "QF_ABVFP",
    "QF_ABVFPLRA",
    "QF_ALIA",
    "QF_ANIA",
    "QF_AUFBV",
    "QF_AUFBVFP",
    "QF_AUFBVLIA",
    "QF_AUFBVNIA",
    "QF_AUFLIA",
    "QF_AUFNIA",
    "QF_AX",
    "QF_BV",
    "QF_BVFP",
    "QF_BVFPLRA",
    "QF_DT",
    "QF_FP",
    "QF_FPLRA",
    "QF_IDL",
    "QF_LIA",
    "QF_LIRA",
    "QF_LRA",
    "QF_NIA",
    "QF_NIRA",
    "QF_NRA",
    "QF_RDL",
    "QF_S",
    "QF_SLIA",
    "QF_SNIA",
    "QF_UF",
    "QF_UFBV",
    "QF_UFBVDT",
    "QF_UFBVLIA",
    "QF_UFDT",
    "QF_UFDTLIA",
    "QF_UFDTLIRA",
    "QF_UFDTNIA",
    "QF_UFFP",
    "QF_UFFPDTNIRA",
    "QF_UFIDL",
    "QF_UFLIA",
    "QF_UFLRA",
    "QF_UFNIA",
    "QF_UFNRA",
    "QF_UFSLIA",
    "UF",
    "UFBV",
    "UFBVDT",
    "UFBVFP",
    "UFBVLIA",
    "UFDT",
    "UFDTLIA",
    "UFDTLIRA",
    "UFDTNIA",
    "UFDTNIRA",
    "UFFPDTNIRA",
    "UFIDL",
    "UFLIA",
    "UFLRA",
    "UFNIA",
    "UFNIRA",
];

/// The sixteen names MEASURED as refused before the fix. Kept as their own
/// list so a regression names the exact hole it reopened.
const PREVIOUSLY_REFUSED: &[&str] = &[
    "QF_UFFP",
    "FP",
    "BVFP",
    "QF_ANIA",
    "FPLRA",
    "ABVFP",
    "UFBVFP",
    "QF_AUFBVFP",
    "QF_BVFPLRA",
    "ANIA",
    "AUFBVFP",
    "UFBVLIA",
    "BVFPLRA",
    "QF_ABVFPLRA",
    "QF_AUFBVNIA",
    "ABVFPLRA",
];

fn program_with_logic(name: &str) -> AYProgram {
    let mut program = AYProgram::new();
    program.set_logic(name);
    program
}

#[test]
fn every_attested_smt_lib_logic_name_is_accepted() {
    for name in ATTESTED {
        let parsed = parse_logic(&program_with_logic(name));
        assert!(
            parsed.is_ok(),
            "attested SMT-LIB logic '{name}' must not abort the solve: {parsed:?}"
        );
    }
}

/// The sixteen names that had no `Logic` variant are installed BY NAME, so the
/// executor's `ctx.logic()` is the DECLARED logic and category routing is the
/// same one `(set-logic <name>)` gets through the SMT-LIB text lane.
///
/// They used to answer `Logic::All` here, on the reasoning that `ALL` admits
/// more than the named logic and so could only widen the query. True of the
/// CAPABILITY, false of the ROUTE: `ALL` is also what switches
/// `detect_logic_category` over to CONTENT detection, which runs after
/// quantifier preprocessing and therefore over whatever ground assertions
/// survive it. `super::super::logic::Declaration` carries the measurement —
/// `∀q:Float64. fp.isNaN(q)` leaves an EMPTY ground window, content detection
/// of nothing infers `QF_UF`, and the FP theory never runs.
#[test]
fn the_sixteen_measured_refusals_are_installed_by_name() {
    for name in PREVIOUSLY_REFUSED {
        assert!(
            ATTESTED.contains(name),
            "'{name}' must be in the transcribed SMT-LIB table"
        );
        let parsed = parse_logic(&program_with_logic(name)).expect("must be accepted");
        assert_eq!(
            parsed,
            Declaration::SmtLibName((*name).to_string()),
            "'{name}' must reach the executor as its own declared name, not as ALL"
        );
    }
}

#[test]
fn all_and_its_alias_are_accepted() {
    for name in ["ALL", "ALL_SUPPORTED"] {
        assert_eq!(
            parse_logic(&program_with_logic(name)).expect("ALL is accepted"),
            Declaration::Capability(ay_dpll::api::Logic::All),
            "{name}"
        );
    }
}

/// Non-vacuity control: a fabricated name must still be refused, otherwise the
/// acceptance assertions above would pass under a blanket "accept everything".
#[test]
fn fabricated_logic_names_are_still_refused() {
    for bogus in [
        "QF_BOGUS",
        "NOT_A_LOGIC",
        "QF_UFFPX",
        "ABVFPLRAZ",
        "qf_lia",
        "",
        " QF_LIA",
    ] {
        let parsed = parse_logic(&program_with_logic(bogus));
        assert!(
            parsed.is_err(),
            "fabricated logic '{bogus}' must be refused, got {parsed:?}"
        );
    }
}

/// `HORN` is attested but needs the CHC lane, not a theory configuration, so it
/// keeps its own refusal — the table must not have swallowed it.
#[test]
fn horn_still_routes_away_from_the_direct_lane() {
    assert!(parse_logic(&program_with_logic("HORN")).is_err());
}
