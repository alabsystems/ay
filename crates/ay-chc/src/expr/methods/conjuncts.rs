// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conjunction flattening and equality propagation.

use super::{maybe_grow_expr_stack, ChcExpr, ChcOp, ChcVar, MAX_EXPR_RECURSION_DEPTH};

impl ChcExpr {
    /// Propagate equalities to simplify expressions with known values.
    /// Extracts `var = const` from top-level conjuncts and substitutes throughout.
    /// Iterates until fixpoint.
    pub(crate) fn propagate_equalities(&self) -> Self {
        self.clone().into_propagate_equalities()
    }

    /// Propagate equalities to simplify expressions with known values, consuming the expression
    /// to avoid an initial clone.
    pub(crate) fn into_propagate_equalities(self) -> Self {
        let debug = crate::debug_prop_enabled();
        let mut current = self;

        for iteration in 0..5 {
            let equalities = current.extract_var_const_equalities();

            if debug {
                safe_eprintln!(
                    "[PROP iter {}] Extracted {} equalities:",
                    iteration,
                    equalities.len()
                );
                for (var, val) in &equalities {
                    safe_eprintln!("  {} = {}", var.name, val);
                }
            }

            if equalities.is_empty() {
                if debug {
                    safe_eprintln!("[PROP iter {}] No equalities, returning current", iteration);
                }
                return current;
            }

            let subst: Vec<(ChcVar, Self)> = equalities
                .into_iter()
                .map(|(var, val)| (var, Self::Int(val)))
                .collect();

            let result = current.substitute(&subst).simplify_constants();

            if debug {
                safe_eprintln!("[PROP iter {}] After substitution: {}", iteration, result);
            }

            if result == current {
                if debug {
                    safe_eprintln!("[PROP iter {}] Fixpoint reached", iteration);
                }
                return result;
            }
            if matches!(result, Self::Bool(_)) {
                if debug {
                    safe_eprintln!("[PROP iter {}] Simplified to Bool", iteration);
                }
                return result;
            }
            current = result;
        }
        current
    }

    /// Recursively flatten an AND expression into a vector of conjuncts.
    ///
    /// Given `(and (and a b) c)`, returns `[a, b, c]`. Non-AND expressions
    /// are returned as single-element results. This is the canonical
    /// implementation — use it instead of per-file copies.
    pub fn collect_conjuncts(&self) -> Vec<Self> {
        let mut result = Vec::new();
        self.collect_conjuncts_into(&mut result);
        result
    }

    /// Collect conjuncts into an existing vector (avoids allocation when appending).
    pub(crate) fn collect_conjuncts_into(&self, result: &mut Vec<Self>) {
        fn collect_into(expr: &ChcExpr, out: &mut Vec<ChcExpr>, depth: usize) {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                out.push(expr.clone());
                return;
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Op(ChcOp::And, args) => {
                    for arg in args {
                        collect_into(arg.as_ref(), out, depth + 1);
                    }
                }
                other => out.push(other.clone()),
            });
        }

        collect_into(self, result, 0);
    }

    /// Like [`collect_conjuncts`] but filters out trivial `Bool(true)` conjuncts.
    ///
    /// This is the canonical "flatten + filter" pattern used by interpolation and
    /// generalization code. Use this instead of per-file `flatten_conjuncts` copies.
    pub(crate) fn collect_conjuncts_nontrivial(&self) -> Vec<Self> {
        let mut result = self.collect_conjuncts();
        result.retain(|c| !matches!(c, Self::Bool(true)));
        result
    }

    /// Like [`collect_conjuncts_into`] but skips trivial `Bool(true)` conjuncts.
    pub(crate) fn collect_conjuncts_nontrivial_into(&self, result: &mut Vec<Self>) {
        self.collect_conjuncts_into(result);
        result.retain(|c| !matches!(c, Self::Bool(true)));
    }

    /// Like `collect_conjuncts` but returns borrowed references (no cloning).
    pub fn conjuncts(&self) -> Vec<&Self> {
        let mut result = Vec::new();
        self.conjuncts_into(&mut result);
        result
    }

    /// Collect borrowed conjunct references into an existing vector.
    fn conjuncts_into<'a>(&'a self, result: &mut Vec<&'a Self>) {
        fn collect_refs<'a>(expr: &'a ChcExpr, out: &mut Vec<&'a ChcExpr>, depth: usize) {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                out.push(expr);
                return;
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Op(ChcOp::And, args) => {
                    for arg in args {
                        collect_refs(arg.as_ref(), out, depth + 1);
                    }
                }
                other => out.push(other),
            });
        }

        collect_refs(self, result, 0);
    }
}
