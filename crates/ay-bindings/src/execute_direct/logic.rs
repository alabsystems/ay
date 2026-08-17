// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use ay_dpll::api::Logic;

use crate::constraint::Constraint;
use crate::program::AYProgram;

use super::ExecuteError;

/// Parse the program's logic into ay_dpll Logic enum.
pub(super) fn parse_logic(program: &AYProgram) -> Result<Logic, ExecuteError> {
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
                    return Ok(Logic::All);
                }
                return Err(ExecuteError::UnsupportedLogic(
                    "no logic set: call set_logic() before execute_direct".to_string(),
                ));
            }
        }
    };

    match logic_str.as_str() {
        // ALL and ALL_SUPPORTED: auto-detect theories at check-sat time
        "ALL" | "ALL_SUPPORTED" => Ok(Logic::All),
        // FP + other theories: no combined solver yet, use ALL for auto-detection
        "QF_ABVFP" | "QF_FPLRA" => Ok(Logic::All),
        // Non-QF (quantified) logics still rely on direct-path theory auto-detection
        // instead of the canonical quantified enum variants.
        "LIA" | "LRA" | "LIRA" | "NIA" | "NRA" | "NIRA" | "UF" | "UFLIA" | "UFLRA" | "UFNIA"
        | "UFNRA" | "UFNIRA" | "UFBV" | "AUFLIA" | "AUFLRA" | "AUFLIRA" | "AUFNIA" | "AUFNRA"
        | "AUFNIRA" | "BV" | "ABV" | "AUFBV" | "ALIA" | "ALRA" | "ALIRA" => Ok(Logic::All),
        // DT-containing logics: use ALL to let executor handle DT + other theories
        _ if logic_str.contains("DT") => Ok(Logic::All),
        // HORN requires CHC solving infrastructure
        "HORN" => Err(ExecuteError::UnsupportedLogic(format!(
            "logic '{logic_str}' requires fallback path"
        ))),
        other => match other.parse::<Logic>() {
            Ok(logic) => Ok(logic),
            Err(_) => Err(ExecuteError::UnsupportedLogic(other.to_string())),
        },
    }
}
