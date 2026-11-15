// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use ay_dpll::api::Logic;

use crate::constraint::Constraint;
use crate::program::AYProgram;

use super::ExecuteError;

/// The attested SMT-LIB logic names, transcribed from the SMT-LIB / SMT-COMP
/// division set.
///
/// WHY THE LANE NEEDS THIS TABLE. `parse_logic` used to accept only the names
/// [`Logic::from_str`] knows plus a hand-kept list, and an unknown name is not
/// a degraded run — it is [`ExecuteError::UnsupportedLogic`], which aborts the
/// WHOLE solve into no verdict. Sixteen real SMT-LIB names fell through that
/// hole (`QF_UFFP`, `FP`, `BVFP`, `QF_ANIA`, `FPLRA`, `ABVFP`, `UFBVFP`,
/// `QF_AUFBVFP`, `QF_BVFPLRA`, `ANIA`, `AUFBVFP`, `UFBVLIA`, `BVFPLRA`,
/// `QF_ABVFPLRA`, `QF_AUFBVNIA`, `ABVFPLRA`), while the EXTERNAL `ay` binary
/// accepted every one of them — the two lanes disagreed on what an SMT-LIB
/// query even IS.
///
/// WHY A TABLE AND NOT `Logic::from_str`. [`Logic`] is a CAPABILITY enum: each
/// variant names a solver configuration ay actually implements, and
/// `Logic::from_str`'s `Err` is load-bearing elsewhere (`split_leading_set_logic`
/// falls back on it; native replay propagates it). Teaching `from_str` these
/// names would either claim configurations that do not exist or map a name onto
/// a NARROWER variant — `QF_UFFP` onto `QF_FP` drops UF, `FP` onto `QF_FP`
/// drops the quantifiers — which is the unsound direction. This table maps them
/// to [`Logic::All`] instead, exactly as the quantified and `DT` arms below
/// already do: `ALL` admits MORE than any named logic, and the executor
/// auto-detects the live theories at check-sat time.
///
/// `HORN` is an attested division and is deliberately NOT here: it has its own
/// arm, because it needs the CHC lane rather than a theory configuration.
const SMT_LIB_LOGICS: &[&str] = &[
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
    // Quantified arrays with extensionality: an SMT-LIB logic with no recent
    // competition division, so it is absent from the division list above.
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
    // Array + UF + BV + integer arithmetic: attested, and `QF_AUFBVNIA` was one
    // of the sixteen measured refusals.
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
    // Strings + UF + linear integer arithmetic: attested, no recent division.
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

/// Whether `name` is an attested SMT-LIB logic name (see [`SMT_LIB_LOGICS`]).
fn is_smt_lib_logic(name: &str) -> bool {
    SMT_LIB_LOGICS.contains(&name)
}

/// How this lane should configure the solver for the program's declared logic.
///
/// THE NAME IS NOT DECORATION. Mapping an attested SMT-LIB name onto
/// [`Logic::All`] keeps the right CAPABILITY (`ALL` admits more than any named
/// logic) and throws away the ROUTE. `Executor::detect_logic_category` sends a
/// MAPPED declared logic straight to its category and only falls back to
/// content detection for `ALL`/unset — and content detection runs AFTER
/// quantifier preprocessing, on whatever ground assertions survive it.
///
/// Measured on trust's `FP` shape, `∀q:Float64. fp.isNaN(q)` (truth UNSAT,
/// false at `+0.0`), which is a single unhandled `forall` and therefore leaves
/// the ground window EMPTY:
///
/// | lane | `ctx.logic()` | category | verdict |
/// |---|---|---|---|
/// | SMT-LIB text, `(set-logic FP)` | `FP` | `QfFp` | `unsat` |
/// | native `AYProgram`, `set_logic("FP")` | `ALL` | `QfUf` (zero assertions) | `Unknown("(incomplete quantifier-unhandled)")` |
///
/// Under `QfUf` the FP theory never runs, so the MBQI refutation rescue's
/// ground instance `fp.isNaN(+0.0)` is an uninterpreted atom that nothing
/// refutes and the whole query degrades. Detection cannot recover a theory
/// from a window it is no longer in, so the declared NAME has to reach the
/// executor. [`Declaration::SmtLibName`] is how it does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Declaration {
    /// A name [`Logic`] has a variant for, or one this lane deliberately
    /// widens (`ALL`, the DT family): construct from the capability.
    Capability(Logic),
    /// An attested SMT-LIB name with no [`Logic`] variant: construct by NAME,
    /// so `ctx.logic()` is the declared logic and routing matches the text
    /// lane exactly.
    SmtLibName(String),
}

/// Parse the program's logic into the solver configuration this lane should
/// construct with (see [`Declaration`]).
pub(super) fn parse_logic(program: &AYProgram) -> Result<Declaration, ExecuteError> {
    // First check the program's metadata field (set by program.set_logic()),
    // then fall back to scanning commands for a SetLogic constraint.
    // Bug fix for #5405: set_logic() stores the logic as metadata, NOT as a
    // Constraint::SetLogic command. The old code only checked commands, so
    // programs using set_logic() would silently default to QF_AUFBV.
    let logic_str = if let Some(logic) = program.get_logic() {
        logic.to_string()
    } else {
        // Fall back to scanning commands for SetLogic constraint
        let mut found = None;
        for constraint in program.commands() {
            if let Constraint::SetLogic(s) = constraint {
                found = Some(s.clone());
                break;
            }
        }
        match found {
            Some(s) => s,
            None => {
                // When datatypes are declared, use ALL so the executor can
                // auto-detect the combined DT+BV/DT+LIA logic. Without this,
                // the default QF_AUFBV misses the DT axiom generation path.
                if program.has_datatypes() {
                    return Ok(Declaration::Capability(Logic::All));
                }
                return Err(ExecuteError::UnsupportedLogic(
                    "no logic set: call set_logic() before execute_direct".to_string(),
                ));
            }
        }
    };

    match logic_str.as_str() {
        // ALL and ALL_SUPPORTED: auto-detect theories at check-sat time
        "ALL" | "ALL_SUPPORTED" => Ok(Declaration::Capability(Logic::All)),
        // FP + other theories: no combined solver yet, use ALL for auto-detection
        "QF_ABVFP" | "QF_FPLRA" => Ok(Declaration::Capability(Logic::All)),
        // Non-QF (quantified) logics still rely on direct-path theory auto-detection
        // instead of the canonical quantified enum variants.
        "LIA" | "LRA" | "LIRA" | "NIA" | "NRA" | "NIRA" | "UF" | "UFLIA" | "UFLRA" | "UFNIA"
        | "UFNRA" | "UFNIRA" | "UFBV" | "AUFLIA" | "AUFLRA" | "AUFLIRA" | "AUFNIA" | "AUFNRA"
        | "AUFNIRA" | "BV" | "ABV" | "AUFBV" | "ALIA" | "ALRA" | "ALIRA" => {
            Ok(Declaration::Capability(Logic::All))
        }
        // DT-containing logics: use ALL to let executor handle DT + other theories
        _ if logic_str.contains("DT") => Ok(Declaration::Capability(Logic::All)),
        // HORN requires CHC solving infrastructure
        "HORN" => Err(ExecuteError::UnsupportedLogic(format!(
            "logic '{logic_str}' requires fallback path"
        ))),
        other => match other.parse::<Logic>() {
            Ok(logic) => Ok(Declaration::Capability(logic)),
            // An attested SMT-LIB name with no dedicated `Logic` variant is
            // installed BY NAME (`Solver::try_new_with_smtlib_logic`).
            //
            // This arm used to answer `Logic::All`, on the reasoning that `ALL`
            // admits MORE than the named logic and so could only widen what the
            // query is allowed to contain. That is true of the CAPABILITY and
            // false of the ROUTE: `ALL` is also the one value that turns
            // `detect_logic_category` over to content detection, and content
            // detection runs after quantifier preprocessing. See [`Declaration`]
            // for the measurement — trust's `FP` shape answers `unsat` through
            // the text lane and `Unknown("(incomplete quantifier-unhandled)")`
            // here, entirely because of this arm.
            //
            // Installing the name is what the text lane's `(set-logic <name>)`
            // does, so the two lanes now reach `classify_quantifier_result` with
            // the same category. It is still not a refusal: a name the frontend
            // rejects surfaces as an ordinary `UnsupportedLogic`, exactly as
            // before, rather than aborting the solve some other way.
            Err(_) if is_smt_lib_logic(other) => Ok(Declaration::SmtLibName(other.to_string())),
            Err(_) => Err(ExecuteError::UnsupportedLogic(other.to_string())),
        },
    }
}
