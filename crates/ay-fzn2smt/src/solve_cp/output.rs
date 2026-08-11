// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// DZN solution formatting for the CP-SAT solver path.

use std::collections::BTreeMap as HashMap;
use std::fmt::Write;

use ay_cp::variable::IntVarId;

use crate::error::{Fzn2smtError, Result};

use super::CpContext;

impl CpContext {
    pub(super) fn format_solution(&self, assignment: &[(IntVarId, i64)]) -> Result<String> {
        let value_map: HashMap<IntVarId, i64> = assignment.iter().copied().collect();
        let mut dzn = String::new();

        for ov in &self.output_vars {
            if ov.is_set {
                // Set variable output
                let (lo, hi) = ov.array_range.unwrap_or((1, ov.set_var_names.len() as i64));
                let vals = ov
                    .set_var_names
                    .iter()
                    .map(|name| self.format_set_value(name, &value_map))
                    .collect::<Result<Vec<_>>>()?;
                if ov.is_array {
                    let _ = writeln!(
                        dzn,
                        "{} = array1d({}..{}, [{}]);",
                        ov.fzn_name,
                        lo,
                        hi,
                        vals.join(", ")
                    );
                } else {
                    let value =
                        vals.first()
                            .ok_or_else(|| Fzn2smtError::MissingOutputAssignment {
                                output: ov.fzn_name.clone(),
                            })?;
                    let _ = writeln!(dzn, "{} = {};", ov.fzn_name, value);
                }
            } else if ov.is_array {
                let (lo, hi) = ov.array_range.unwrap_or((1, ov.var_ids.len() as i64));
                let vals = ov
                    .var_ids
                    .iter()
                    .map(|id| format_cp_value(*id, ov.is_bool, &ov.fzn_name, &value_map))
                    .collect::<Result<Vec<_>>>()?;
                let _ = writeln!(
                    dzn,
                    "{} = array1d({}..{}, [{}]);",
                    ov.fzn_name,
                    lo,
                    hi,
                    vals.join(", ")
                );
            } else {
                let id = ov.var_ids.first().copied().ok_or_else(|| {
                    Fzn2smtError::MissingOutputAssignment {
                        output: ov.fzn_name.clone(),
                    }
                })?;
                let formatted = format_cp_value(id, ov.is_bool, &ov.fzn_name, &value_map)?;
                let _ = writeln!(dzn, "{} = {};", ov.fzn_name, formatted);
            }
        }
        Ok(dzn)
    }

    /// Format a set variable as `{e1, e2, ...}` from its boolean indicators.
    fn format_set_value(&self, name: &str, value_map: &HashMap<IntVarId, i64>) -> Result<String> {
        let (lo, indicators) =
            self.set_var_map
                .get(name)
                .ok_or_else(|| Fzn2smtError::UnknownOutputSetVariable {
                    name: name.to_string(),
                })?;
        let mut elems = Vec::new();
        for (offset, id) in indicators.iter().enumerate() {
            let present = value_map.get(id).copied().ok_or_else(|| {
                Fzn2smtError::MissingOutputAssignment {
                    output: name.to_string(),
                }
            })?;
            if present != 0 {
                elems.push((lo + offset as i64).to_string());
            }
        }
        Ok(format!("{{{}}}", elems.join(", ")))
    }
}

fn format_cp_value(
    id: IntVarId,
    is_bool: bool,
    output: &str,
    values: &HashMap<IntVarId, i64>,
) -> Result<String> {
    let v = values
        .get(&id)
        .copied()
        .ok_or_else(|| Fzn2smtError::MissingOutputAssignment {
            output: output.to_string(),
        })?;
    Ok(if is_bool {
        if v != 0 {
            "true".to_string()
        } else {
            "false".to_string()
        }
    } else {
        v.to_string()
    })
}
