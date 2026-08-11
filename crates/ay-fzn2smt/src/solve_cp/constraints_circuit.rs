// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Circuit and Inverse constraint decompositions for solve-cp.
//
// These global constraints are decomposed into primitives that the
// ay-cp engine already compiles (AllDifferent, Linear, Element).

use crate::error::{Fzn2smtError, Result};
use ay_cp::propagator::Constraint;
use ay_cp::Domain;
use ay_flatzinc_parser::ast::ConstraintItem;

use super::numeric::{encoding_i64, linear_encoding_overflow, quadratic_global_work_supported};
use super::CpContext;

impl CpContext {
    /// `circuit(x)`: the entries of `x` form a Hamiltonian cycle over the
    /// array's declared index set, and each entry is its node's successor.
    ///
    /// Decomposition using O(n) Element-based MTZ subtour constraints. Each
    /// `Element` owns an O(n) array, so translation work/storage is guarded as
    /// O(n²) before any decomposition constraints are added:
    /// 1. AllDifferent(x) — successor is a permutation
    /// 2. No self-loops: `x[i] != i` for every array index `i`
    /// 3. Position variables for all nodes after the first, domain {2..n}
    ///    (the first node has implicit position 1)
    /// 4. For each non-root node i: pos(succ(i)) >= pos(i) + 1 when succ(i) != root
    ///    Encoded via Element constraint on an extended position array.
    pub(super) fn translate_circuit(&mut self, c: &ConstraintItem) -> Result<()> {
        // A circuit's successor values range over the array's declared index
        // set. Named arrays may be zero-based (or use another lower bound),
        // while inline array literals use FlatZinc's builtin 1..len index set.
        // Deriving this from successor variable bounds is unsound: ordinary
        // constraints may have tightened every successor's lower bound without
        // changing the nodes in the circuit.
        let (lo, declared_hi, vars) = self.resolve_var_array_with_bounds(&c.args[0])?;
        let n = vars.len();

        if n == 0 {
            return Ok(());
        }
        if !quadratic_global_work_supported(n) {
            self.mark_unsupported(&c.id);
            return Ok(());
        }

        let n_i64 = i64::try_from(n).map_err(|_| linear_encoding_overflow(&c.id))?;

        let hi = encoding_i64(i128::from(lo) + i128::from(n_i64) - 1, &c.id)?;
        if hi != declared_hi {
            return Err(Fzn2smtError::UnsupportedExpression(format!(
                "{}: array index range {lo}..{declared_hi} does not match {n} elements",
                c.id
            )));
        }

        for &var in &vars {
            self.engine.add_constraint(Constraint::LinearGe {
                coeffs: vec![1],
                vars: vec![var],
                rhs: lo,
            });
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1],
                vars: vec![var],
                rhs: hi,
            });
        }

        // 1. AllDifferent on successor variables
        self.engine
            .add_constraint(Constraint::AllDifferent(vars.clone()));

        if n == 1 {
            // The sole node's successor must be itself. The previous early
            // return left the variable unconstrained and admitted non-circuits.
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1],
                vars,
                rhs: lo,
            });
            return Ok(());
        }

        // 2. No self-loops: vars[i] != (lo + i) for all i
        for (i, &var) in vars.iter().enumerate() {
            let self_value = encoding_i64(i128::from(lo) + i as i128, &c.id)?;
            let self_val = self.get_const_var(self_value);
            self.engine
                .add_constraint(Constraint::AllDifferent(vec![var, self_val]));
        }

        // For n=2, AllDifferent + no self-loops is sufficient
        if n == 2 {
            return Ok(());
        }

        self.encode_mtz_subtour_elimination(&vars, n, lo, &c.id)
    }

    /// MTZ subtour elimination encoding.
    ///
    /// Creates position variables u[k] for non-root nodes and adds constraints:
    /// for each non-root node, pos(successor) >= pos(node) + 1 when successor != root.
    fn encode_mtz_subtour_elimination(
        &mut self,
        vars: &[ay_cp::variable::IntVarId],
        n: usize,
        lo: i64,
        context: &str,
    ) -> Result<()> {
        let n_i64 = i64::try_from(n).map_err(|_| linear_encoding_overflow(context))?;
        let hi = encoding_i64(i128::from(lo) + i128::from(n_i64) - 1, context)?;
        let after_lo = encoding_i64(i128::from(lo) + 1, context)?;

        // Position variables for every node after the first, domain {2..n}.
        let u: Vec<_> = (0..(n - 1))
            .map(|_| self.engine.new_int_var(Domain::new(2, n_i64), None))
            .collect();

        // Extended position array: u_ext[0] = 1 (the first-indexed root),
        // u_ext[k] = u[k-1] for k=1..n-1.
        let root_pos = self.get_const_var(1);
        let mut u_ext = vec![root_pos];
        u_ext.extend_from_slice(&u);

        // M must satisfy: max(u[k]) - min(pos_succ) <= -1 + M
        // u[k] ∈ {2..n}, pos_succ ∈ {1..n}, max diff = n-1. Need M >= n.
        let big_m = n_i64;

        for k in 0..(n - 1) {
            // a. idx = vars[k+1] - lo (0-indexed into u_ext)
            let idx = self.engine.new_int_var(Domain::new(0, n_i64 - 1), None);
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1, -1],
                vars: vec![vars[k + 1], idx],
                rhs: lo,
            });

            // b. pos_succ = element(idx, u_ext)
            let pos_succ = self.engine.new_int_var(Domain::new(1, n_i64), None);
            self.engine.add_constraint(Constraint::Element {
                index: idx,
                array: u_ext.clone(),
                result: pos_succ,
            });

            // c. root_flag ∈ {0,1}: root_flag=1 ↔ vars[k+1]=lo (the root node)
            //    root_flag=1 → vars[k+1] <= lo: vars[k+1] + (n-1)*root_flag <= hi
            //    root_flag=0 → vars[k+1] >= lo+1: vars[k+1] + root_flag >= lo+1
            let root_flag = self.engine.new_bool_var(None);
            self.var_bounds.insert(root_flag, (0, 1));
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, n_i64 - 1],
                vars: vec![vars[k + 1], root_flag],
                rhs: hi,
            });
            self.engine.add_constraint(Constraint::LinearGe {
                coeffs: vec![1, 1],
                vars: vec![vars[k + 1], root_flag],
                rhs: after_lo,
            });

            // d. u[k] - pos_succ - M*root_flag <= -1
            //    root_flag=0: pos_succ >= u[k] + 1
            //    root_flag=1: relaxed (always true since M >= n)
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1, -big_m],
                vars: vec![u[k], pos_succ, root_flag],
                rhs: -1,
            });
        }
        Ok(())
    }

    /// `inverse(x, y)`: `x[i] = j` iff `y[j] = i` for indices `i` of
    /// `x` and `j` of `y`.
    ///
    /// Decomposition: range constraints and AllDifferent on both arrays, plus
    /// `Element` channeling from each entry of `x` into `y`. Named arrays retain
    /// their declared index sets; inline arrays use FlatZinc's builtin 1..len
    /// index set.
    pub(super) fn translate_inverse(&mut self, c: &ConstraintItem) -> Result<()> {
        let (x_lo, x_hi, x) = self.resolve_var_array_with_bounds(&c.args[0])?;
        let (y_lo, y_hi, y) = self.resolve_var_array_with_bounds(&c.args[1])?;
        let n = x.len();

        if y.len() != n {
            return Err(Fzn2smtError::InverseArrayLengthMismatch {
                left: n,
                right: y.len(),
            });
        }
        if !quadratic_global_work_supported(n) {
            self.mark_unsupported(&c.id);
            return Ok(());
        }

        let n_i64 = i64::try_from(n).map_err(|_| linear_encoding_overflow(&c.id))?;
        let expected_x_hi = encoding_i64(i128::from(x_lo) + i128::from(n_i64) - 1, &c.id)?;
        let expected_y_hi = encoding_i64(i128::from(y_lo) + i128::from(n_i64) - 1, &c.id)?;
        if x_hi != expected_x_hi || y_hi != expected_y_hi {
            return Err(Fzn2smtError::UnsupportedExpression(format!(
                "{}: inverse array index ranges {x_lo}..{x_hi} and {y_lo}..{y_hi} do not match their {n} elements",
                c.id
            )));
        }

        // Values of x are indices of y, while values of y are indices of x.
        for &xi in &x {
            self.engine.add_constraint(Constraint::LinearGe {
                coeffs: vec![1],
                vars: vec![xi],
                rhs: y_lo,
            });
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1],
                vars: vec![xi],
                rhs: y_hi,
            });
        }
        for &yi in &y {
            self.engine.add_constraint(Constraint::LinearGe {
                coeffs: vec![1],
                vars: vec![yi],
                rhs: x_lo,
            });
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1],
                vars: vec![yi],
                rhs: x_hi,
            });
        }

        // Both arrays are permutations
        self.engine
            .add_constraint(Constraint::AllDifferent(x.clone()));
        self.engine
            .add_constraint(Constraint::AllDifferent(y.clone()));

        // Channeling: for each i in index_set(x), y[x[i]] = i. Element uses
        // zero-based positions, hence subtract y's declared lower bound.
        for (offset, &xi) in x.iter().enumerate() {
            let idx = self.engine.new_int_var(Domain::new(0, n_i64 - 1), None);
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1, -1],
                vars: vec![xi, idx],
                rhs: y_lo,
            });
            let result_value = encoding_i64(i128::from(x_lo) + offset as i128, &c.id)?;
            let result_val = self.get_const_var(result_value);
            self.engine.add_constraint(Constraint::Element {
                index: idx,
                array: y.clone(),
                result: result_val,
            });
        }

        Ok(())
    }
}
