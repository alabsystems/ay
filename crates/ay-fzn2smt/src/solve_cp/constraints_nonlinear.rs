// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Big-M and linear constraint linearizations for solve-cp.
//
// FlatZinc constraints that are not directly linear (int_times, int_abs,
// int_min, int_max, int_lin_ne, bool_xor) are translated to combinations
// of linear constraints using Big-M indicator variables where needed.
// Table-based constraints (int_div, int_mod, int_pow) are in
// constraints_table.rs.

use crate::error::Result;
use ay_cp::propagator::Constraint;
use ay_flatzinc_parser::ast::ConstraintItem;

use super::CpContext;

impl CpContext {
    /// int_times(a, b, c): c = a * b
    ///
    /// - Constant × variable: direct LinearEq
    /// - Variable × variable with small domains: Table constraint
    /// - Otherwise: unsupported
    pub(super) fn translate_int_times(&mut self, c: &ConstraintItem) -> Result<()> {
        let a_const = self.eval_const_int(&c.args[0]);
        let b_const = self.eval_const_int(&c.args[1]);
        let r = self.resolve_var(&c.args[2])?;

        match (a_const, b_const) {
            (Some(k), _) => {
                let b = self.resolve_var(&c.args[1])?;
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![k, -1],
                    vars: vec![b, r],
                    rhs: 0,
                });
            }
            (_, Some(k)) => {
                let a = self.resolve_var(&c.args[0])?;
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![k, -1],
                    vars: vec![a, r],
                    rhs: 0,
                });
            }
            (None, None) => {
                let a = self.resolve_var(&c.args[0])?;
                let b = self.resolve_var(&c.args[1])?;
                let (a_lb, a_ub) = self.get_var_bounds(a);
                let (b_lb, b_ub) = self.get_var_bounds(b);
                let domain_size = (a_ub - a_lb + 1).saturating_mul(b_ub - b_lb + 1);

                if domain_size <= 10_000 {
                    let mut tuples = Vec::new();
                    for av in a_lb..=a_ub {
                        for bv in b_lb..=b_ub {
                            if let Some(product) = av.checked_mul(bv) {
                                tuples.push(vec![av, bv, product]);
                            }
                        }
                    }
                    self.engine.add_constraint(Constraint::Table {
                        vars: vec![a, b, r],
                        tuples,
                    });
                } else {
                    self.mark_unsupported("int_times");
                }
            }
        }
        Ok(())
    }

    /// int_abs(a, c): c = |a|
    ///
    /// Linearization via Big-M with binary indicator d:
    ///   c >= a, c >= -a  (c is at least |a|)
    ///   d=0 → c <= a (a >= 0 case), d=1 → c <= -a (a <= 0 case)
    pub(super) fn translate_int_abs(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let r = self.resolve_var(&c.args[1])?;
        let (a_lb, a_ub) = self.get_var_bounds(a);
        let (_, r_ub) = self.get_var_bounds(r);

        // c >= a
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![1, -1],
            vars: vec![r, a],
            rhs: 0,
        });
        // c >= -a
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![1, 1],
            vars: vec![r, a],
            rhs: 0,
        });

        let d = self.engine.new_bool_var(None);

        // c <= a + M1*d: c - a - M1*d <= 0
        // d=0 → c <= a; d=1 → relaxed
        let m1 = (r_ub - a_lb).max(1);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, -m1],
            vars: vec![r, a, d],
            rhs: 0,
        });

        // c <= -a + M2*(1-d): c + a + M2*d <= M2
        // d=0 → relaxed; d=1 → c + a <= 0 → c <= -a
        let m2 = (r_ub + a_ub).max(1);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, 1, m2],
            vars: vec![r, a, d],
            rhs: m2,
        });

        Ok(())
    }

    /// int_min(a, b, c): c = min(a, b)
    ///
    /// Linearization via Big-M with binary indicator d:
    ///   c <= a, c <= b  (c is at most min(a,b))
    ///   d=1 → c >= a (tight with a), d=0 → c >= b (tight with b)
    pub(super) fn translate_int_min(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;
        let a_ub = self.get_var_bounds(a).1;
        let b_ub = self.get_var_bounds(b).1;
        let r_lb = self.get_var_bounds(r).0;

        // c <= a
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![r, a],
            rhs: 0,
        });
        // c <= b
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![r, b],
            rhs: 0,
        });

        let d = self.engine.new_bool_var(None);

        // c >= a - M1*(1-d): -c + a + M1*d <= M1
        // d=1 → -c + a <= 0 → c >= a; d=0 → relaxed
        let m1 = (a_ub - r_lb).max(1);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![-1, 1, m1],
            vars: vec![r, a, d],
            rhs: m1,
        });

        // c >= b - M2*d: -c + b - M2*d <= 0
        // d=0 → -c + b <= 0 → c >= b; d=1 → relaxed
        let m2 = (b_ub - r_lb).max(1);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![-1, 1, -m2],
            vars: vec![r, b, d],
            rhs: 0,
        });

        Ok(())
    }

    /// int_max(a, b, c): c = max(a, b)
    ///
    /// Linearization via Big-M with binary indicator d:
    ///   c >= a, c >= b  (c is at least max(a,b))
    ///   d=0 → c <= a (tight with a), d=1 → c <= b (tight with b)
    pub(super) fn translate_int_max(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;
        let a_lb = self.get_var_bounds(a).0;
        let b_lb = self.get_var_bounds(b).0;
        let r_ub = self.get_var_bounds(r).1;

        // c >= a
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![1, -1],
            vars: vec![r, a],
            rhs: 0,
        });
        // c >= b
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![1, -1],
            vars: vec![r, b],
            rhs: 0,
        });

        let d = self.engine.new_bool_var(None);

        // c <= a + M1*d: c - a - M1*d <= 0
        // d=0 → c <= a; d=1 → relaxed
        let m1 = (r_ub - a_lb).max(1);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, -m1],
            vars: vec![r, a, d],
            rhs: 0,
        });

        // c <= b + M2*(1-d): c - b + M2*d <= M2
        // d=0 → relaxed; d=1 → c <= b
        let m2 = (r_ub - b_lb).max(1);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, m2],
            vars: vec![r, b, d],
            rhs: m2,
        });

        Ok(())
    }

    /// int_lin_ne(coeffs, vars, rhs): sum(coeffs[i]*vars[i]) != rhs
    ///
    /// Special case: 2-variable difference `x - y != k` uses direct pairwise
    /// exclusion clauses (no auxiliary variables, no propagators).
    /// General case: Big-M linearization with binary indicator.
    pub(super) fn translate_int_lin_ne(&mut self, c: &ConstraintItem) -> Result<()> {
        let coeffs = self.resolve_const_int_array(&c.args[0])?;
        let vars = self.resolve_var_array(&c.args[1])?;
        let rhs = self.resolve_const_int(&c.args[2])?;

        // Fast path: 2-variable difference x - y != k → pairwise exclusion
        if coeffs.len() == 2 && vars.len() == 2 {
            if coeffs[0] == 1 && coeffs[1] == -1 {
                self.engine.add_constraint(Constraint::PairwiseNeq {
                    x: vars[0],
                    y: vars[1],
                    offset: rhs,
                });
                return Ok(());
            } else if coeffs[0] == -1 && coeffs[1] == 1 {
                self.engine.add_constraint(Constraint::PairwiseNeq {
                    x: vars[1],
                    y: vars[0],
                    offset: rhs,
                });
                return Ok(());
            }
        }

        // General case: native propagator (replaces Big-M linearization).
        // The propagator tracks fixed-variable count and removes the single
        // forbidden value when n-1 variables are fixed. No auxiliary variables,
        // no M parameter, no linearization artifacts.
        self.engine
            .add_constraint(Constraint::LinearNotEqual { coeffs, vars, rhs });

        Ok(())
    }

    /// bool_xor: 2-arg `bool_xor(a, b)` means `a != b`;
    /// 3-arg `bool_xor(a, b, c)` means `c = a XOR b`. All values in {0,1}.
    pub(super) fn translate_bool_xor(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;

        if c.args.len() == 2 {
            // 2-arg: a XOR b (i.e., a != b). For booleans: a + b = 1.
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1, 1],
                vars: vec![a, b],
                rhs: 1,
            });
            return Ok(());
        }

        let r = self.resolve_var(&c.args[2])?;

        // c >= a - b
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![1, -1, 1],
            vars: vec![r, a, b],
            rhs: 0,
        });
        // c >= b - a
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![1, 1, -1],
            vars: vec![r, a, b],
            rhs: 0,
        });
        // c <= a + b
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, -1],
            vars: vec![r, a, b],
            rhs: 0,
        });
        // c + a + b <= 2
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, 1, 1],
            vars: vec![r, a, b],
            rhs: 2,
        });

        Ok(())
    }
}
