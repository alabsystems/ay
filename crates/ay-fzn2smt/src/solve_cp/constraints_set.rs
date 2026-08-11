// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Set variable constraint translations for solve-cp.
//
// Boolean indicator encoding: var set of lo..hi → (hi-lo+1) bool vars.
// set_card = sum of indicators, set_intersect = elementwise AND,
// set_diff = elementwise AND-NOT, set_symdiff = elementwise XOR,
// set_subset/set_superset = elementwise implication, set_eq = elementwise
// equality, set_ne = any elementwise difference.  set_le/set_lt compare the
// sorted element lists lexicographically, as required by FlatZinc; they are
// deliberately distinct from subset/strict-subset relations.

use crate::error::{Fzn2smtError, Result};
use ay_cp::propagator::Constraint;
use ay_cp::variable::IntVarId;
use ay_flatzinc_parser::ast::ConstraintItem;

use super::numeric::linear_encoding_overflow;
use super::{CpContext, MAX_MATERIALIZED_VALUES};

#[derive(Clone, Copy)]
enum SetLexOrder {
    Less,
    LessEqual,
}

impl CpContext {
    /// set_card(S, c): |S| = c
    /// Encoding: sum of boolean indicators = c.
    pub(super) fn translate_set_card(&mut self, c: &ConstraintItem) -> Result<()> {
        let set_name = match &c.args[0] {
            ay_flatzinc_parser::ast::Expr::Ident(name) => name.clone(),
            _ => {
                return Err(Fzn2smtError::ExpectedSetVariableIdentifier {
                    constraint: "set_card".into(),
                });
            }
        };
        let (_, indicators) = self
            .set_var_map
            .get(&set_name)
            .ok_or_else(|| Fzn2smtError::UnknownSetVariable {
                constraint: "set_card".into(),
                name: set_name.clone(),
            })?
            .clone();

        if let Some(card) = self.eval_const_int(&c.args[1]) {
            let n = indicators.len();
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1; n],
                vars: indicators,
                rhs: card,
            });
        } else {
            let c_var = self.resolve_var(&c.args[1])?;
            let n = indicators.len();
            let mut coeffs = vec![1i64; n];
            coeffs.push(-1);
            let mut vars = indicators;
            vars.push(c_var);
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs,
                vars,
                rhs: 0,
            });
        }
        Ok(())
    }

    /// set_intersect(S1, S2, S3): S3 = S1 ∩ S2
    /// Encoding: for each position i, b3[i] = b1[i] AND b2[i].
    pub(super) fn translate_set_intersect(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_intersect")?;
        let name2 = resolve_set_name(&c.args[1], "set_intersect")?;
        let name3 = resolve_set_name(&c.args[2], "set_intersect")?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;
        let (lo3, ind3) = self.get_set_indicators(&name3)?;

        let elems =
            combined_set_values(&[(lo1, &ind1), (lo2, &ind2), (lo3, &ind3)], "set_intersect")?;
        let zero = self.get_const_var(0);

        for elem in elems {
            let b1 = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            let b2 = get_indicator(&ind2, lo2, elem).unwrap_or(zero);
            let b3 = get_indicator(&ind3, lo3, elem).unwrap_or(zero);
            self.add_bool_and(b1, b2, b3);
        }
        Ok(())
    }

    /// set_union(S1, S2, S3): S3 = S1 ∪ S2
    /// Encoding: for each position i, b3[i] = b1[i] OR b2[i].
    pub(super) fn translate_set_union(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_union")?;
        let name2 = resolve_set_name(&c.args[1], "set_union")?;
        let name3 = resolve_set_name(&c.args[2], "set_union")?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;
        let (lo3, ind3) = self.get_set_indicators(&name3)?;

        let elems = combined_set_values(&[(lo1, &ind1), (lo2, &ind2), (lo3, &ind3)], "set_union")?;
        let zero = self.get_const_var(0);

        for elem in elems {
            let b1 = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            let b2 = get_indicator(&ind2, lo2, elem).unwrap_or(zero);
            let b3 = get_indicator(&ind3, lo3, elem).unwrap_or(zero);
            // b3 = b1 OR b2, including elements absent from the result domain.
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1],
                vars: vec![b1, b3],
                rhs: 0,
            });
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1],
                vars: vec![b2, b3],
                rhs: 0,
            });
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1, -1],
                vars: vec![b3, b1, b2],
                rhs: 0,
            });
        }
        Ok(())
    }

    /// set_diff(S1, S2, S3): S3 = S1 \ S2
    /// Encoding: for each position i, b3[i] = b1[i] AND NOT b2[i].
    pub(super) fn translate_set_diff(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_diff")?;
        let name2 = resolve_set_name(&c.args[1], "set_diff")?;
        let name3 = resolve_set_name(&c.args[2], "set_diff")?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;
        let (lo3, ind3) = self.get_set_indicators(&name3)?;

        let elems = combined_set_values(&[(lo1, &ind1), (lo2, &ind2), (lo3, &ind3)], "set_diff")?;
        let zero = self.get_const_var(0);

        for elem in elems {
            let b1 = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            let b2 = get_indicator(&ind2, lo2, elem).unwrap_or(zero);
            let b3 = get_indicator(&ind3, lo3, elem).unwrap_or(zero);
            self.add_bool_and_not(b1, b2, b3);
        }
        Ok(())
    }

    fn add_bool_and_not(&mut self, lhs: IntVarId, rhs: IntVarId, result: IntVarId) {
        // result = lhs AND NOT rhs
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![result, lhs],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, 1],
            vars: vec![result, rhs],
            rhs: 1,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, -1],
            vars: vec![lhs, rhs, result],
            rhs: 0,
        });
    }

    /// set_symdiff(S1, S2, S3): S3 = (S1 \ S2) ∪ (S2 \ S1)
    /// Encoding: for each position i, b3[i] = b1[i] XOR b2[i].
    pub(super) fn translate_set_symdiff(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_symdiff")?;
        let name2 = resolve_set_name(&c.args[1], "set_symdiff")?;
        let name3 = resolve_set_name(&c.args[2], "set_symdiff")?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;
        let (lo3, ind3) = self.get_set_indicators(&name3)?;

        let elems =
            combined_set_values(&[(lo1, &ind1), (lo2, &ind2), (lo3, &ind3)], "set_symdiff")?;
        let zero = self.get_const_var(0);

        for elem in elems {
            let b1 = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            let b2 = get_indicator(&ind2, lo2, elem).unwrap_or(zero);
            let b3 = get_indicator(&ind3, lo3, elem).unwrap_or(zero);
            self.add_bool_xor(b1, b2, b3);
        }
        Ok(())
    }

    fn add_bool_xor(&mut self, lhs: IntVarId, rhs: IntVarId, result: IntVarId) {
        // result = lhs XOR rhs for boolean 0/1 variables.
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, -1],
            vars: vec![result, lhs, rhs],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, -1],
            vars: vec![lhs, rhs, result],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, -1],
            vars: vec![rhs, lhs, result],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, 1, 1],
            vars: vec![result, lhs, rhs],
            rhs: 2,
        });
    }

    /// set_subset(S1, S2): every element in S1 is also in S2.
    /// Encoding: for each element value, b1 => b2, with absent indicators
    /// represented as fixed zero.
    pub(super) fn translate_set_subset(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_subset")?;
        let name2 = resolve_set_name(&c.args[1], "set_subset")?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;

        let elems = combined_set_values(&[(lo1, &ind1), (lo2, &ind2)], "set_subset")?;
        let zero = self.get_const_var(0);

        for elem in elems {
            let lhs = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            let rhs = get_indicator(&ind2, lo2, elem).unwrap_or(zero);
            self.add_bool_implies(lhs, rhs);
        }
        Ok(())
    }

    /// set_superset(S1, S2): every element in S2 is also in S1.
    /// Encoding: reverse of set_subset, with absent indicators represented as
    /// fixed zero.
    pub(super) fn translate_set_superset(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_superset")?;
        let name2 = resolve_set_name(&c.args[1], "set_superset")?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;

        let elems = combined_set_values(&[(lo1, &ind1), (lo2, &ind2)], "set_superset")?;
        let zero = self.get_const_var(0);

        for elem in elems {
            let lhs = get_indicator(&ind2, lo2, elem).unwrap_or(zero);
            let rhs = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            self.add_bool_implies(lhs, rhs);
        }
        Ok(())
    }

    /// set_eq(S1, S2): both sets contain exactly the same elements.
    /// Encoding: elementwise equality over the union of declared domains, with
    /// absent indicators represented as fixed zero.
    pub(super) fn translate_set_eq(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_eq")?;
        let name2 = resolve_set_name(&c.args[1], "set_eq")?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;

        let elems = combined_set_values(&[(lo1, &ind1), (lo2, &ind2)], "set_eq")?;
        let zero = self.get_const_var(0);

        for elem in elems {
            let lhs = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            let rhs = get_indicator(&ind2, lo2, elem).unwrap_or(zero);
            self.add_bool_eq(lhs, rhs);
        }
        Ok(())
    }

    /// set_ne(S1, S2): at least one element is in exactly one set.
    /// Encoding: XOR aligned indicators over the union of declared domains,
    /// then require at least one XOR result to be true.
    pub(super) fn translate_set_ne(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_ne")?;
        let name2 = resolve_set_name(&c.args[1], "set_ne")?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;

        let elems = combined_set_values(&[(lo1, &ind1), (lo2, &ind2)], "set_ne")?;
        let zero = self.get_const_var(0);
        let mut diffs = Vec::new();

        for elem in elems {
            let lhs = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            let rhs = get_indicator(&ind2, lo2, elem).unwrap_or(zero);
            if lhs == rhs {
                continue;
            }
            let diff = self.engine.new_bool_var(None);
            self.var_bounds.insert(diff, (0, 1));
            self.add_bool_xor(lhs, rhs, diff);
            diffs.push(diff);
        }

        if diffs.is_empty() {
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1],
                vars: vec![zero],
                rhs: -1,
            });
        } else {
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![-1; diffs.len()],
                vars: diffs,
                rhs: -1,
            });
        }
        Ok(())
    }

    /// set_lt(S1, S2): the sorted element list of S1 is lexicographically less
    /// than the sorted element list of S2.
    pub(super) fn translate_set_lt(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_lt")?;
        let name2 = resolve_set_name(&c.args[1], "set_lt")?;
        let required = self.get_const_var(1);
        self.add_set_lex_reif(&name1, &name2, required, SetLexOrder::Less, "set_lt")
    }

    /// set_eq_reif(S1, S2, r): r is true iff both sets contain exactly the
    /// same elements.
    pub(super) fn translate_set_eq_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_eq_reif")?;
        let name2 = resolve_set_name(&c.args[1], "set_eq_reif")?;
        let result = self.resolve_var(&c.args[2])?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;

        let elems = combined_set_values(&[(lo1, &ind1), (lo2, &ind2)], "set_eq_reif")?;
        let zero = self.get_const_var(0);
        let mut diffs = Vec::new();

        for elem in elems {
            let lhs = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            let rhs = get_indicator(&ind2, lo2, elem).unwrap_or(zero);
            if lhs == rhs {
                continue;
            }
            let diff = self.engine.new_bool_var(None);
            self.var_bounds.insert(diff, (0, 1));
            self.add_bool_xor(lhs, rhs, diff);
            diffs.push(diff);
        }

        if diffs.is_empty() {
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1],
                vars: vec![result],
                rhs: 1,
            });
        } else {
            for &diff in &diffs {
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, 1],
                    vars: vec![result, diff],
                    rhs: 1,
                });
            }

            let mut vars = Vec::with_capacity(diffs.len() + 1);
            vars.push(result);
            vars.extend(diffs);
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![-1; vars.len()],
                vars,
                rhs: -1,
            });
        }
        Ok(())
    }

    /// set_ne_reif(S1, S2, r): r is true iff at least one element is in
    /// exactly one set.
    pub(super) fn translate_set_ne_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_ne_reif")?;
        let name2 = resolve_set_name(&c.args[1], "set_ne_reif")?;
        let result = self.resolve_var(&c.args[2])?;
        self.add_set_ne_reif(&name1, &name2, result)
    }

    fn add_set_ne_reif(&mut self, name1: &str, name2: &str, result: IntVarId) -> Result<()> {
        let (lo1, ind1) = self.get_set_indicators(name1)?;
        let (lo2, ind2) = self.get_set_indicators(name2)?;

        let elems = combined_set_values(&[(lo1, &ind1), (lo2, &ind2)], "set_ne_reif")?;
        let zero = self.get_const_var(0);
        let mut diffs = Vec::new();

        for elem in elems {
            let lhs = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            let rhs = get_indicator(&ind2, lo2, elem).unwrap_or(zero);
            if lhs == rhs {
                continue;
            }
            let diff = self.engine.new_bool_var(None);
            self.var_bounds.insert(diff, (0, 1));
            self.add_bool_xor(lhs, rhs, diff);
            diffs.push(diff);
        }

        if diffs.is_empty() {
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1],
                vars: vec![result],
                rhs: 0,
            });
        } else {
            for &diff in &diffs {
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![diff, result],
                    rhs: 0,
                });
            }

            let mut coeffs = Vec::with_capacity(diffs.len() + 1);
            coeffs.push(1);
            coeffs.extend(vec![-1; diffs.len()]);
            let mut vars = Vec::with_capacity(diffs.len() + 1);
            vars.push(result);
            vars.extend(diffs);
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs,
                vars,
                rhs: 0,
            });
        }
        Ok(())
    }

    /// set_subset_reif(S1, S2, r): r is true iff every element in S1 is also
    /// in S2.
    pub(super) fn translate_set_subset_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        self.translate_set_subset_reif_with_name(c, "set_subset_reif")
    }

    /// set_superset_reif(S1, S2, r): r is true iff every element in S2 is also
    /// in S1.
    pub(super) fn translate_set_superset_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_superset_reif")?;
        let name2 = resolve_set_name(&c.args[1], "set_superset_reif")?;
        let result = self.resolve_var(&c.args[2])?;
        self.add_set_subset_reif(&name2, &name1, result)
    }

    /// set_le_reif(S1, S2, r): r is true iff the sorted element list of S1 is
    /// lexicographically less than or equal to that of S2.
    pub(super) fn translate_set_le_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_le_reif")?;
        let name2 = resolve_set_name(&c.args[1], "set_le_reif")?;
        let result = self.resolve_var(&c.args[2])?;
        self.add_set_lex_reif(
            &name1,
            &name2,
            result,
            SetLexOrder::LessEqual,
            "set_le_reif",
        )
    }

    /// set_lt_reif(S1, S2, r): r is true iff the sorted element list of S1 is
    /// lexicographically less than that of S2.
    pub(super) fn translate_set_lt_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_lt_reif")?;
        let name2 = resolve_set_name(&c.args[1], "set_lt_reif")?;
        let result = self.resolve_var(&c.args[2])?;
        self.add_set_lex_reif(&name1, &name2, result, SetLexOrder::Less, "set_lt_reif")
    }

    fn translate_set_subset_reif_with_name(
        &mut self,
        c: &ConstraintItem,
        constraint: &str,
    ) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], constraint)?;
        let name2 = resolve_set_name(&c.args[1], constraint)?;
        let result = self.resolve_var(&c.args[2])?;
        self.add_set_subset_reif(&name1, &name2, result)
    }

    fn add_set_subset_reif(&mut self, name1: &str, name2: &str, result: IntVarId) -> Result<()> {
        let (lo1, ind1) = self.get_set_indicators(name1)?;
        let (lo2, ind2) = self.get_set_indicators(name2)?;

        let elems = combined_set_values(&[(lo1, &ind1), (lo2, &ind2)], "set_subset_reif")?;
        let zero = self.get_const_var(0);
        let mut violations = Vec::new();

        for elem in elems {
            let lhs = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            let rhs = get_indicator(&ind2, lo2, elem).unwrap_or(zero);
            if lhs == zero || lhs == rhs {
                continue;
            }

            let violation = if rhs == zero {
                lhs
            } else {
                let violation = self.engine.new_bool_var(None);
                self.var_bounds.insert(violation, (0, 1));
                self.add_bool_and_not(lhs, rhs, violation);
                violation
            };
            violations.push(violation);
        }

        if violations.is_empty() {
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1],
                vars: vec![result],
                rhs: 1,
            });
        } else {
            for &violation in &violations {
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, 1],
                    vars: vec![result, violation],
                    rhs: 1,
                });
            }

            let mut vars = Vec::with_capacity(violations.len() + 1);
            vars.push(result);
            vars.extend(violations);
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![-1; vars.len()],
                vars,
                rhs: -1,
            });
        }
        Ok(())
    }

    /// Reify lexicographic comparison of the sets' sorted element lists.
    ///
    /// Scanning represented values from high to low lets each step refer to
    /// whether either remaining suffix is non-empty.  If the memberships at
    /// the current value agree, comparison continues with the suffix.  If only
    /// the left set contains the value, it is smaller exactly when the right
    /// suffix is non-empty; if only the right contains it, the left is smaller
    /// exactly when its suffix is empty (the proper-prefix case).
    fn add_set_lex_reif(
        &mut self,
        name1: &str,
        name2: &str,
        result: IntVarId,
        order: SetLexOrder,
        operation: &str,
    ) -> Result<()> {
        let (lo1, ind1) = self.get_set_indicators(name1)?;
        let (lo2, ind2) = self.get_set_indicators(name2)?;
        let elems = combined_set_values(&[(lo1, &ind1), (lo2, &ind2)], operation)?;
        let zero = self.get_const_var(0);
        let one = self.get_const_var(1);
        let mut any1_next = zero;
        let mut any2_next = zero;
        let mut lex_next = match order {
            SetLexOrder::Less => zero,
            SetLexOrder::LessEqual => one,
        };

        for elem in elems.into_iter().rev() {
            let b1 = get_indicator(&ind1, lo1, elem).unwrap_or(zero);
            let b2 = get_indicator(&ind2, lo2, elem).unwrap_or(zero);

            let equal = if b1 == b2 {
                one
            } else {
                let equal = self.new_aux_bool();
                self.add_reif_eq(&[1, -1], &[b1, b2], 0, equal, operation)?;
                equal
            };
            let equal_branch = self.add_bool_conjunction(&[(equal, true), (lex_next, true)]);
            let left_branch =
                self.add_bool_conjunction(&[(b1, true), (b2, false), (any2_next, true)]);
            let right_branch =
                self.add_bool_conjunction(&[(b1, false), (b2, true), (any1_next, false)]);
            let lex = self.new_aux_bool();
            // The three branches are mutually exclusive.
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1, -1, -1, -1],
                vars: vec![lex, equal_branch, left_branch, right_branch],
                rhs: 0,
            });

            any1_next = self.add_bool_or_var(b1, any1_next, zero, one);
            any2_next = self.add_bool_or_var(b2, any2_next, zero, one);
            lex_next = lex;
        }

        self.add_bool_eq(result, lex_next);
        Ok(())
    }

    fn add_bool_conjunction(&mut self, literals: &[(IntVarId, bool)]) -> IntVarId {
        let result = self.new_aux_bool();
        for &(var, positive) in literals {
            if positive {
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![result, var],
                    rhs: 0,
                });
            } else {
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, 1],
                    vars: vec![result, var],
                    rhs: 1,
                });
            }
        }

        let positive_count = literals.iter().filter(|(_, positive)| *positive).count() as i64;
        let mut coeffs: Vec<i64> = literals
            .iter()
            .map(|(_, positive)| if *positive { 1 } else { -1 })
            .collect();
        let mut vars: Vec<IntVarId> = literals.iter().map(|(var, _)| *var).collect();
        coeffs.push(-1);
        vars.push(result);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs,
            vars,
            rhs: positive_count - 1,
        });
        result
    }

    fn add_bool_or_var(
        &mut self,
        lhs: IntVarId,
        rhs: IntVarId,
        zero: IntVarId,
        one: IntVarId,
    ) -> IntVarId {
        if lhs == one || rhs == one {
            return one;
        }
        if lhs == zero {
            return rhs;
        }
        if rhs == zero || lhs == rhs {
            return lhs;
        }
        let result = self.new_aux_bool();
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![lhs, result],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![rhs, result],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, -1],
            vars: vec![result, lhs, rhs],
            rhs: 0,
        });
        result
    }

    fn new_aux_bool(&mut self) -> IntVarId {
        let var = self.engine.new_bool_var(None);
        self.var_bounds.insert(var, (0, 1));
        var
    }

    fn add_bool_and(&mut self, lhs: IntVarId, rhs: IntVarId, result: IntVarId) {
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![result, lhs],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![result, rhs],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, 1, -1],
            vars: vec![lhs, rhs, result],
            rhs: 1,
        });
    }

    fn add_bool_implies(&mut self, lhs: IntVarId, rhs: IntVarId) {
        // lhs => rhs, for boolean 0/1 variables.
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![lhs, rhs],
            rhs: 0,
        });
    }

    fn add_bool_eq(&mut self, lhs: IntVarId, rhs: IntVarId) {
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs: vec![1, -1],
            vars: vec![lhs, rhs],
            rhs: 0,
        });
    }

    /// array_set_element(i, array_of_sets, S): S = array_of_sets[i]
    ///
    /// Two cases:
    /// - Constant array of sets (Ident → par_set_arrays): build constant indicator
    ///   tables and use Element per indicator position.
    /// - Variable array of sets (ArrayLit of set var Idents): link set variable
    ///   indicators via Element per indicator position.
    pub(super) fn translate_array_set_element(&mut self, c: &ConstraintItem) -> Result<()> {
        use ay_flatzinc_parser::ast::Expr;

        let index = self.resolve_var(&c.args[0])?;
        let result_name = resolve_set_name(&c.args[2], "array_set_element")?;
        let (res_lo, res_ind) = self.get_set_indicators(&result_name)?;

        match &c.args[1] {
            Expr::Ident(name) => {
                let array_lo = self
                    .par_array_ranges
                    .get(name)
                    .or_else(|| self.array_var_ranges.get(name))
                    .map_or(1, |(lo, _)| *lo);
                if let Some(const_sets) = self.par_set_arrays.get(name).cloned() {
                    self.add_array_set_element_const(
                        index, array_lo, res_lo, &res_ind, const_sets,
                    )?;
                } else if let Some(set_names) = self.set_array_var_map.get(name).cloned() {
                    self.add_array_set_element_vars(index, array_lo, res_lo, &res_ind, set_names)?;
                } else {
                    return Err(Fzn2smtError::UnknownSetArray {
                        constraint: "array_set_element".into(),
                        name: name.clone(),
                    });
                }
            }
            Expr::ArrayLit(elems) => {
                // Variable array of sets.
                let set_names: Vec<String> = elems
                    .iter()
                    .map(|e| resolve_set_name(e, "array_set_element"))
                    .collect::<Result<Vec<_>>>()?;
                self.add_array_set_element_vars(index, 1, res_lo, &res_ind, set_names)?;
            }
            _ => {
                return Err(Fzn2smtError::ExpectedSetArray {
                    constraint: "array_set_element".into(),
                });
            }
        }
        Ok(())
    }

    fn add_array_set_element_const(
        &mut self,
        index: IntVarId,
        array_lo: i64,
        res_lo: i64,
        res_ind: &[IntVarId],
        const_sets: Vec<Vec<i64>>,
    ) -> Result<()> {
        if const_sets.is_empty() {
            return Err(Fzn2smtError::ArrayElementEmptyArray {
                constraint: "array_set_element".into(),
            });
        }
        let n = i64::try_from(const_sets.len())
            .map_err(|_| linear_encoding_overflow("array_set_element"))?;
        let index_0 = self.engine.new_int_var(ay_cp::Domain::new(0, n - 1), None);
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs: vec![1, -1],
            vars: vec![index, index_0],
            rhs: array_lo,
        });
        // A selected source set containing an unrepresentable value cannot equal
        // the result set. Ban that array index explicitly.
        for (offset, set) in const_sets.iter().enumerate() {
            if set
                .iter()
                .any(|&value| get_indicator(res_ind, res_lo, value).is_none())
            {
                self.engine.add_constraint(Constraint::LinearNotEqual {
                    coeffs: vec![1],
                    vars: vec![index_0],
                    rhs: i64::try_from(offset)
                        .map_err(|_| linear_encoding_overflow("array_set_element"))?,
                });
            }
        }
        // For each value v in the result set's range, build a constant
        // membership table and add an Element constraint.
        for (offset, &res_v) in res_ind.iter().enumerate() {
            let v = checked_indicator_value(res_lo, offset, "array_set_element result")?;
            let table: Vec<IntVarId> = const_sets
                .iter()
                .map(|s| {
                    let member = if s.contains(&v) { 1 } else { 0 };
                    self.get_const_var(member)
                })
                .collect();
            self.engine.add_constraint(Constraint::Element {
                index: index_0,
                array: table,
                result: res_v,
            });
        }
        Ok(())
    }

    fn add_array_set_element_vars(
        &mut self,
        index: IntVarId,
        array_lo: i64,
        res_lo: i64,
        res_ind: &[IntVarId],
        set_names: Vec<String>,
    ) -> Result<()> {
        if set_names.is_empty() {
            return Err(Fzn2smtError::ArrayElementEmptyArray {
                constraint: "array_set_element".into(),
            });
        }
        let mut array_sets: Vec<(i64, Vec<IntVarId>)> = Vec::new();
        for name in &set_names {
            let (s_lo, s_ind) = self.get_set_indicators(name)?;
            array_sets.push((s_lo, s_ind));
        }
        let mut domains = Vec::with_capacity(array_sets.len() + 1);
        domains.push((res_lo, res_ind));
        domains.extend(
            array_sets
                .iter()
                .map(|(set_lo, indicators)| (*set_lo, indicators.as_slice())),
        );
        let elems = combined_set_values(&domains, "array_set_element")?;
        let n = i64::try_from(array_sets.len())
            .map_err(|_| linear_encoding_overflow("array_set_element"))?;
        let zero = self.get_const_var(0);
        let index_0 = self.engine.new_int_var(ay_cp::Domain::new(0, n - 1), None);
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs: vec![1, -1],
            vars: vec![index, index_0],
            rhs: array_lo,
        });
        for v in elems {
            let res_v = get_indicator(res_ind, res_lo, v).unwrap_or(zero);
            let elem_inds: Vec<IntVarId> = array_sets
                .iter()
                .map(|(s_lo, s_ind)| get_indicator(s_ind, *s_lo, v).unwrap_or(zero))
                .collect();
            self.engine.add_constraint(Constraint::Element {
                index: index_0,
                array: elem_inds,
                result: res_v,
            });
        }
        Ok(())
    }

    /// set_le(S1, S2): the sorted element list of S1 is lexicographically less
    /// than or equal to the sorted element list of S2.
    pub(super) fn translate_set_le(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_le")?;
        let name2 = resolve_set_name(&c.args[1], "set_le")?;
        let required = self.get_const_var(1);
        self.add_set_lex_reif(&name1, &name2, required, SetLexOrder::LessEqual, "set_le")
    }

    /// Look up a set variable's indicators, returning (lo, indicators).
    fn get_set_indicators(&self, name: &str) -> Result<(i64, Vec<IntVarId>)> {
        self.set_var_map
            .get(name)
            .cloned()
            .ok_or_else(|| Fzn2smtError::UnknownSetVariable {
                constraint: "set".into(),
                name: name.to_string(),
            })
    }
}

fn resolve_set_name(expr: &ay_flatzinc_parser::ast::Expr, constraint: &str) -> Result<String> {
    match expr {
        ay_flatzinc_parser::ast::Expr::Ident(n) => Ok(n.clone()),
        _ => Err(Fzn2smtError::ExpectedSetVariableIdentifier {
            constraint: constraint.to_string(),
        }),
    }
}

fn get_indicator(indicators: &[IntVarId], lo: i64, elem: i64) -> Option<IntVarId> {
    let idx = usize::try_from(i128::from(elem) - i128::from(lo)).ok()?;
    indicators.get(idx).copied()
}

fn checked_indicator_value(lo: i64, offset: usize, context: &str) -> Result<i64> {
    let offset = i64::try_from(offset).map_err(|_| {
        Fzn2smtError::UnsupportedExpression(format!(
            "{context}: indicator offset does not fit in an integer"
        ))
    })?;
    lo.checked_add(offset).ok_or_else(|| {
        Fzn2smtError::UnsupportedExpression(format!(
            "{context}: indicator range starting at {lo} exceeds the integer range"
        ))
    })
}

/// Return disjoint sorted ranges for the union of contiguous indicator domains.
/// The limit applies after overlap is removed: repeated references to the same
/// large domain must not consume the budget more than once.
fn combined_set_ranges(sets: &[(i64, usize)], context: &str) -> Result<Vec<(i64, i64)>> {
    let mut ranges = Vec::with_capacity(sets.len());
    for &(lo, len) in sets {
        if len == 0 {
            continue;
        }
        let hi = checked_indicator_value(lo, len - 1, context)?;
        ranges.push((lo, hi));
    }
    ranges.sort_unstable();

    let mut merged: Vec<(i64, i64)> = Vec::with_capacity(ranges.len());
    for (lo, hi) in ranges {
        if let Some((_, merged_hi)) = merged.last_mut() {
            let touches = lo <= *merged_hi || merged_hi.checked_add(1) == Some(lo);
            if touches {
                *merged_hi = (*merged_hi).max(hi);
                continue;
            }
        }
        merged.push((lo, hi));
    }

    let mut total = 0usize;
    for &(lo, hi) in &merged {
        let len = usize::try_from(i128::from(hi) - i128::from(lo) + 1).map_err(|_| {
            Fzn2smtError::UnsupportedExpression(format!(
                "{context}: combined set domain is too large to materialize"
            ))
        })?;
        total = total.checked_add(len).ok_or_else(|| {
            Fzn2smtError::UnsupportedExpression(format!(
                "{context}: combined set domain is too large to materialize"
            ))
        })?;
        if total > MAX_MATERIALIZED_VALUES {
            return Err(Fzn2smtError::UnsupportedExpression(format!(
                "{context}: combined set domain materializes {total} distinct values, exceeding the maximum supported {MAX_MATERIALIZED_VALUES}"
            )));
        }
    }
    Ok(merged)
}

/// Return the sorted union of values represented by several indicator arrays.
fn combined_set_values(sets: &[(i64, &[IntVarId])], context: &str) -> Result<Vec<i64>> {
    let shapes: Vec<(i64, usize)> = sets
        .iter()
        .map(|(lo, indicators)| (*lo, indicators.len()))
        .collect();
    let ranges = combined_set_ranges(&shapes, context)?;
    let capacity = ranges.iter().try_fold(0usize, |total, &(lo, hi)| {
        let len = usize::try_from(i128::from(hi) - i128::from(lo) + 1).map_err(|_| {
            Fzn2smtError::UnsupportedExpression(format!(
                "{context}: combined set domain is too large to materialize"
            ))
        })?;
        total.checked_add(len).ok_or_else(|| {
            Fzn2smtError::UnsupportedExpression(format!(
                "{context}: combined set domain is too large to materialize"
            ))
        })
    })?;
    let mut values = Vec::with_capacity(capacity);
    for (lo, hi) in ranges {
        let len = usize::try_from(i128::from(hi) - i128::from(lo) + 1).map_err(|_| {
            Fzn2smtError::UnsupportedExpression(format!(
                "{context}: combined set domain is too large to materialize"
            ))
        })?;
        for offset in 0..len {
            values.push(checked_indicator_value(lo, offset, context)?);
        }
    }
    Ok(values)
}

#[cfg(test)]
mod combined_set_range_tests {
    use super::*;

    #[test]
    fn duplicate_domains_are_capped_after_deduplication() {
        let len = MAX_MATERIALIZED_VALUES / 2 + 1;
        let ranges = combined_set_ranges(&[(0, len), (0, len)], "set_eq")
            .expect("the distinct union remains below the limit");
        assert_eq!(ranges, vec![(0, len as i64 - 1)]);
    }

    #[test]
    fn distinct_domains_still_respect_the_materialization_limit() {
        let len = MAX_MATERIALIZED_VALUES / 2 + 1;
        let error = combined_set_ranges(&[(0, len), (2_000_000, len)], "set_eq")
            .expect_err("the distinct union exceeds the limit");
        assert!(error.to_string().contains("distinct values"), "{error}");
    }
}
