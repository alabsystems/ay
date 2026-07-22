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

use super::CpContext;

impl CpContext {
    /// circuit(x): x[1..n] forms a Hamiltonian cycle (1-indexed successors).
    ///
    /// Decomposition using O(n) Element-based MTZ subtour elimination:
    /// 1. AllDifferent(x) — successor is a permutation
    /// 2. No self-loops: x[i] != i+1 for all i
    /// 3. Position variables u[k] for nodes 2..n, domain {2..n}
    ///    (node 1 has implicit position 1)
    /// 4. For each non-root node i: pos(succ(i)) >= pos(i) + 1 when succ(i) != root
    ///    Encoded via Element constraint on an extended position array.
    pub(super) fn translate_circuit(&mut self, c: &ConstraintItem) -> Result<()> {
        let vars = self.resolve_var_array(&c.args[0])?;
        let n = vars.len();

        if n <= 1 {
            return Ok(());
        }

        let n_i64 = n as i64;

        // fzn_circuit is emitted under either a 1-based (values 1..n) or 0-based
        // (values 0..n-1) node convention depending on the model — e.g. MZC-2025
        // `is` produces `[v1..v5, 0]` (0-based, node n's successor is literal 0),
        // which the old hardcoded 1-based `[1,n]` bound rejected as spurious UNSAT.
        // Infer the node-id base `lo` from the smallest successor lower bound; the
        // n node-ids are then the consecutive range `[lo, lo+n-1]` and node at
        // position i (0-based) has self-value `lo + i`. Imposing this range is
        // sound (a circuit's successors must lie in the node set) and still proves
        // out-of-range successors UNSAT.
        let lo = vars
            .iter()
            .map(|&v| self.get_var_bounds(v).0)
            .min()
            .unwrap();
        let hi = lo + n_i64 - 1;

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

        // 2. No self-loops: vars[i] != (lo + i) for all i
        for (i, &var) in vars.iter().enumerate() {
            let self_val = self.get_const_var(lo + i as i64);
            self.engine
                .add_constraint(Constraint::AllDifferent(vec![var, self_val]));
        }

        // For n=2, AllDifferent + no self-loops is sufficient
        if n == 2 {
            return Ok(());
        }

        self.encode_mtz_subtour_elimination(&vars, n, lo)
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
    ) -> Result<()> {
        let n_i64 = n as i64;
        let hi = lo + n_i64 - 1;

        // Position variables: u[k] for nodes 2..n (1-based), domain {2..n}
        let u: Vec<_> = (0..(n - 1))
            .map(|_| self.engine.new_int_var(Domain::new(2, n_i64), None))
            .collect();

        // Extended position array: u_ext[0] = 1 (root), u_ext[k] = u[k-1] for k=1..n-1
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
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, n_i64 - 1],
                vars: vec![vars[k + 1], root_flag],
                rhs: hi,
            });
            self.engine.add_constraint(Constraint::LinearGe {
                coeffs: vec![1, 1],
                vars: vec![vars[k + 1], root_flag],
                rhs: lo + 1,
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

    /// inverse(x, y): x[y[i]] = i and y[x[i]] = i for all i (1-based).
    ///
    /// Decomposition: AllDifferent on both arrays + Element channeling.
    /// For each i: y[x[i] - 1] = i+1 (using 0-indexed Element + 1-based values).
    pub(super) fn translate_inverse(&mut self, c: &ConstraintItem) -> Result<()> {
        let x = self.resolve_var_array(&c.args[0])?;
        let y = self.resolve_var_array(&c.args[1])?;
        let n = x.len();

        if y.len() != n {
            return Err(Fzn2smtError::InverseArrayLengthMismatch {
                left: n,
                right: y.len(),
            });
        }

        // Both arrays are permutations
        self.engine
            .add_constraint(Constraint::AllDifferent(x.clone()));
        self.engine
            .add_constraint(Constraint::AllDifferent(y.clone()));

        // Channeling: for each i, y[x[i]-1] = i+1
        let n_i64 = n as i64;
        for (i, &xi) in x.iter().enumerate() {
            let idx = self.engine.new_int_var(Domain::new(0, n_i64 - 1), None);
            // idx = x[i] - 1
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1, -1],
                vars: vec![xi, idx],
                rhs: 1,
            });
            let result_val = self.get_const_var((i + 1) as i64);
            self.engine.add_constraint(Constraint::Element {
                index: idx,
                array: y.clone(),
                result: result_val,
            });
        }

        Ok(())
    }
}
