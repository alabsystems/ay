// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// DZN solution formatting for the CP-SAT solver path.

use std::collections::BTreeMap as HashMap;
use std::fmt::Write;

use ay_cp::variable::IntVarId;

use super::CpContext;

impl CpContext {
    pub(super) fn format_solution(&self, assignment: &[(IntVarId, i64)]) -> String {
        let value_map: HashMap<IntVarId, i64> = assignment.iter().copied().collect();
        let mut dzn = String::new();

        for ov in &self.output_vars {
            if !ov.set_var_names.is_empty() {
                // Set variable output
                let (lo, hi) = ov.array_range.unwrap_or((1, ov.set_var_names.len() as i64));
                let vals: Vec<String> = ov
                    .set_var_names
                    .iter()
                    .map(|name| self.format_set_value(name, &value_map))
                    .collect();
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
                    let _ = writeln!(dzn, "{} = {};", ov.fzn_name, vals[0]);
                }
            } else if ov.is_array {
                let (lo, hi) = ov.array_range.unwrap_or((1, ov.var_ids.len() as i64));
                let vals: Vec<String> = ov
                    .var_ids
                    .iter()
                    .map(|id| format_cp_value(*id, ov.is_bool, &value_map))
                    .collect();
                let _ = writeln!(
                    dzn,
                    "{} = array1d({}..{}, [{}]);",
                    ov.fzn_name,
                    lo,
                    hi,
                    vals.join(", ")
                );
            } else {
                let id = ov.var_ids[0];
                let formatted = format_cp_value(id, ov.is_bool, &value_map);
                let _ = writeln!(dzn, "{} = {};", ov.fzn_name, formatted);
            }
        }
        dzn
    }

    /// Format a set variable as `{e1, e2, ...}` from its boolean indicators.
    fn format_set_value(&self, name: &str, value_map: &HashMap<IntVarId, i64>) -> String {
        if let Some((lo, indicators)) = self.set_var_map.get(name) {
            let elems: Vec<String> = indicators
                .iter()
                .enumerate()
                .filter(|(_, id)| value_map.get(id).copied().unwrap_or(0) != 0)
                .map(|(i, _)| (lo + i as i64).to_string())
                .collect();
            format!("{{{}}}", elems.join(", "))
        } else {
            "{}".to_string()
        }
    }
}

fn format_cp_value(id: IntVarId, is_bool: bool, values: &HashMap<IntVarId, i64>) -> String {
    let v = values.get(&id).copied().unwrap_or(0);
    if is_bool {
        if v != 0 {
            "true".to_string()
        } else {
            "false".to_string()
        }
    } else {
        v.to_string()
    }
}
