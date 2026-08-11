// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Table-based constraint linearizations for solve-cp.
//
// FlatZinc constraints int_div, int_mod, int_pow are translated to Table
// constraints over enumerated domain values. For small domains (≤10,000
// cross-product entries), all valid (input, output) tuples are enumerated.
// Special constant cases (divisor ±1, exponent 0/1) use direct LinearEq.

use crate::error::Result;
use ay_cp::propagator::Constraint;
use ay_flatzinc_parser::ast::ConstraintItem;

use super::numeric::{interval_size_within, product_size_within};
use super::CpContext;

impl CpContext {
    /// int_div(a, b, c): c = a div b (truncated towards zero)
    ///
    /// - b constant 1: identity c = a
    /// - b constant -1: negate c = -a
    /// - b constant, small a domain: Table constraint
    /// - Both variable, small domains: Table constraint (excludes b=0)
    /// - Otherwise: unsupported
    pub(super) fn translate_int_div(&mut self, c: &ConstraintItem) -> Result<()> {
        let b_const = self.eval_const_int(&c.args[1]);

        if b_const == Some(0) {
            self.mark_unsupported("int_div");
            return Ok(());
        }

        let r = self.resolve_var(&c.args[2])?;

        if let Some(k) = b_const {
            if k == 1 {
                let a = self.resolve_var(&c.args[0])?;
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, -1],
                    vars: vec![a, r],
                    rhs: 0,
                });
            } else if k == -1 {
                let a = self.resolve_var(&c.args[0])?;
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, 1],
                    vars: vec![a, r],
                    rhs: 0,
                });
            } else {
                let a = self.resolve_var(&c.args[0])?;
                let (a_lb, a_ub) = self.get_var_bounds(a);
                if interval_size_within(a_lb, a_ub, 10_000) {
                    let mut tuples = Vec::new();
                    for av in a_lb..=a_ub {
                        if let Some(q) = av.checked_div(k) {
                            tuples.push(vec![av, q]);
                        }
                    }
                    self.engine.add_constraint(Constraint::Table {
                        vars: vec![a, r],
                        tuples,
                    });
                } else {
                    self.mark_unsupported("int_div");
                }
            }
        } else {
            let a = self.resolve_var(&c.args[0])?;
            let b = self.resolve_var(&c.args[1])?;
            let (a_lb, a_ub) = self.get_var_bounds(a);
            let (b_lb, b_ub) = self.get_var_bounds(b);
            if product_size_within((a_lb, a_ub), (b_lb, b_ub), 10_000) {
                let mut tuples = Vec::new();
                for av in a_lb..=a_ub {
                    for bv in b_lb..=b_ub {
                        if bv != 0 {
                            if let Some(q) = av.checked_div(bv) {
                                tuples.push(vec![av, bv, q]);
                            }
                        }
                    }
                }
                self.engine.add_constraint(Constraint::Table {
                    vars: vec![a, b, r],
                    tuples,
                });
            } else {
                self.mark_unsupported("int_div");
            }
        }
        Ok(())
    }

    /// int_mod(a, b, c): c = a mod b (truncation remainder, same sign as a)
    ///
    /// - b constant, small a domain: Table constraint
    /// - Both variable, small domains: Table constraint (excludes b=0)
    /// - Otherwise: unsupported
    pub(super) fn translate_int_mod(&mut self, c: &ConstraintItem) -> Result<()> {
        let b_const = self.eval_const_int(&c.args[1]);

        if b_const == Some(0) {
            self.mark_unsupported("int_mod");
            return Ok(());
        }

        let r = self.resolve_var(&c.args[2])?;

        if let Some(k) = b_const {
            let a = self.resolve_var(&c.args[0])?;
            let (a_lb, a_ub) = self.get_var_bounds(a);
            if interval_size_within(a_lb, a_ub, 10_000) {
                let mut tuples = Vec::new();
                for av in a_lb..=a_ub {
                    if let Some(r) = av.checked_rem(k) {
                        tuples.push(vec![av, r]);
                    }
                }
                self.engine.add_constraint(Constraint::Table {
                    vars: vec![a, r],
                    tuples,
                });
            } else {
                self.mark_unsupported("int_mod");
            }
        } else {
            let a = self.resolve_var(&c.args[0])?;
            let b = self.resolve_var(&c.args[1])?;
            let (a_lb, a_ub) = self.get_var_bounds(a);
            let (b_lb, b_ub) = self.get_var_bounds(b);
            if product_size_within((a_lb, a_ub), (b_lb, b_ub), 10_000) {
                let mut tuples = Vec::new();
                for av in a_lb..=a_ub {
                    for bv in b_lb..=b_ub {
                        if bv != 0 {
                            if let Some(r) = av.checked_rem(bv) {
                                tuples.push(vec![av, bv, r]);
                            }
                        }
                    }
                }
                self.engine.add_constraint(Constraint::Table {
                    vars: vec![a, b, r],
                    tuples,
                });
            } else {
                self.mark_unsupported("int_mod");
            }
        }
        Ok(())
    }

    /// int_pow(a, b, c): c = a^b
    ///
    /// - b constant 0: c = 1
    /// - b constant 1: c = a (identity)
    /// - b constant ≥2, small a domain: Table constraint
    /// - Both variable, small domains: Table constraint (b≥0 only)
    /// - Otherwise: unsupported
    pub(super) fn translate_int_pow(&mut self, c: &ConstraintItem) -> Result<()> {
        let b_const = self.eval_const_int(&c.args[1]);
        let r = self.resolve_var(&c.args[2])?;

        if let Some(k) = b_const {
            if k == 0 {
                // a^0 = 1 for any a
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1],
                    vars: vec![r],
                    rhs: 1,
                });
            } else if k == 1 {
                let a = self.resolve_var(&c.args[0])?;
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, -1],
                    vars: vec![a, r],
                    rhs: 0,
                });
            } else if (2..=63).contains(&k) {
                let a = self.resolve_var(&c.args[0])?;
                let (a_lb, a_ub) = self.get_var_bounds(a);
                if interval_size_within(a_lb, a_ub, 10_000) {
                    let k_u32 = k as u32;
                    let mut tuples = Vec::new();
                    for av in a_lb..=a_ub {
                        if let Some(pv) = av.checked_pow(k_u32) {
                            tuples.push(vec![av, pv]);
                        }
                    }
                    self.engine.add_constraint(Constraint::Table {
                        vars: vec![a, r],
                        tuples,
                    });
                } else {
                    self.mark_unsupported("int_pow");
                }
            } else {
                // Negative exponent or too large — not meaningful for integers
                self.mark_unsupported("int_pow");
            }
        } else {
            let a = self.resolve_var(&c.args[0])?;
            let b = self.resolve_var(&c.args[1])?;
            let (a_lb, a_ub) = self.get_var_bounds(a);
            let (b_lb, b_ub) = self.get_var_bounds(b);
            if product_size_within((a_lb, a_ub), (b_lb, b_ub), 10_000) {
                let mut tuples = Vec::new();
                for av in a_lb..=a_ub {
                    for bv in b_lb..=b_ub {
                        if (0..=63).contains(&bv) {
                            if let Some(pv) = av.checked_pow(bv as u32) {
                                tuples.push(vec![av, bv, pv]);
                            }
                        }
                    }
                }
                self.engine.add_constraint(Constraint::Table {
                    vars: vec![a, b, r],
                    tuples,
                });
            } else {
                self.mark_unsupported("int_pow");
            }
        }
        Ok(())
    }
}
