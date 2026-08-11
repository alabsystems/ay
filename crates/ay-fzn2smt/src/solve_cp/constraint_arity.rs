// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arity validation at the direct-CP FlatZinc boundary.

use ay_flatzinc_parser::ast::ConstraintItem;

use crate::error::{Fzn2smtError, Result};

/// Validate input before the specialized translators index
/// [`ConstraintItem::args`]. Unknown constraints are deliberately left alone
/// so the normal unsupported-constraint reporting path handles them.
pub(super) fn validate_constraint_arity(c: &ConstraintItem) -> Result<()> {
    let accepted: &[usize] = match c.id.as_str() {
        "fzn_all_different_int"
        | "alldifferent"
        | "alldifferent_int"
        | "all_different_int"
        | "fzn_circuit"
        | "circuit" => &[1],

        "int_eq"
        | "int_ne"
        | "int_lt"
        | "int_le"
        | "int_gt"
        | "int_ge"
        | "bool_lt"
        | "bool_le"
        | "bool_gt"
        | "bool_ge"
        | "int_negate"
        | "bool_eq"
        | "bool_not"
        | "bool_clause"
        | "bool2int"
        | "array_bool_and"
        | "array_bool_or"
        | "set_in"
        | "set_card"
        | "set_subset"
        | "set_superset"
        | "set_eq"
        | "set_ne"
        | "set_lt"
        | "set_le"
        | "fzn_table_int"
        | "table_int"
        | "fzn_inverse"
        | "inverse"
        | "int_abs"
        | "array_int_maximum"
        | "fzn_array_int_maximum"
        | "array_int_minimum"
        | "fzn_array_int_minimum"
        | "fzn_lex_lesseq_int"
        | "lex_lesseq_int"
        | "fzn_lex_less_int"
        | "lex_less_int"
        | "fzn_nvalue"
        | "nvalue" => &[2],

        "bool_and" | "bool_or" | "bool_xor" => &[2, 3],

        "int_lin_eq"
        | "int_lin_le"
        | "bool_lin_eq"
        | "bool_lin_le"
        | "int_plus"
        | "int_minus"
        | "array_int_element"
        | "array_var_int_element"
        | "array_bool_element"
        | "array_var_bool_element"
        | "set_intersect"
        | "set_union"
        | "set_diff"
        | "set_symdiff"
        | "array_set_element"
        | "int_eq_reif"
        | "int_ne_reif"
        | "int_le_reif"
        | "int_lt_reif"
        | "int_ge_reif"
        | "int_gt_reif"
        | "bool_le_reif"
        | "bool_lt_reif"
        | "bool_gt_reif"
        | "bool_ge_reif"
        | "bool_eq_reif"
        | "bool_not_reif"
        | "bool_ne_reif"
        | "bool_and_reif"
        | "bool_or_reif"
        | "bool_clause_reif"
        | "int_le_imp"
        | "int_lt_imp"
        | "int_eq_imp"
        | "int_ne_imp"
        | "int_ge_imp"
        | "int_gt_imp"
        | "bool_lt_imp"
        | "bool_le_imp"
        | "bool_gt_imp"
        | "bool_ge_imp"
        | "int_times"
        | "int_min"
        | "int_max"
        | "int_lin_ne"
        | "int_div"
        | "int_mod"
        | "int_pow"
        | "set_in_reif"
        | "set_eq_reif"
        | "set_ne_reif"
        | "set_subset_reif"
        | "set_superset_reif"
        | "set_le_reif"
        | "set_lt_reif"
        | "fzn_count_eq"
        | "count_eq"
        | "fzn_count_leq"
        | "count_leq"
        | "fzn_count_geq"
        | "count_geq"
        | "fzn_count_lt"
        | "count_lt"
        | "fzn_count_gt"
        | "count_gt"
        | "fzn_count_neq"
        | "count_neq"
        | "fzn_global_cardinality"
        | "global_cardinality" => &[3],

        "int_lin_le_reif" | "int_lin_eq_reif" | "bool_lin_le_reif" | "bool_lin_eq_reif"
        | "int_lin_ne_reif" | "bool_lin_ne_reif" | "int_lin_le_imp" | "int_lin_eq_imp"
        | "bool_lin_le_imp" | "bool_lin_eq_imp" | "int_lin_ne_imp" | "bool_lin_ne_imp"
        | "fzn_cumulative" | "cumulative" | "fzn_diffn" | "diffn" => &[4],

        _ => return Ok(()),
    };

    if accepted.contains(&c.args.len()) {
        return Ok(());
    }

    let expected = accepted
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(" or ");
    Err(Fzn2smtError::InvalidConstraintArity {
        constraint: c.id.clone(),
        expected,
        actual: c.args.len(),
    })
}
