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
        let _ = self.collect_conjuncts_into_checked(result, &mut || false);
    }

    /// Preserve the canonical order and depth fallback, returning no partial
    /// conjunction when cancellation is observed.
    pub(crate) fn collect_conjuncts_checked(
        &self,
        mut should_stop: impl FnMut() -> bool,
    ) -> Option<Vec<Self>> {
        let mut result = Vec::new();
        self.collect_conjuncts_into_checked(&mut result, &mut should_stop)?;
        Some(result)
    }

    fn collect_conjuncts_into_checked(
        &self,
        result: &mut Vec<Self>,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Option<()> {
        fn collect_into(
            expr: &ChcExpr,
            out: &mut Vec<ChcExpr>,
            depth: usize,
            stop: &mut dyn FnMut() -> bool,
        ) -> Option<()> {
            if stop() {
                return None;
            }
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                out.push(expr.clone());
                return Some(());
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Op(ChcOp::And, args) => {
                    for arg in args {
                        collect_into(arg.as_ref(), out, depth + 1, stop)?;
                    }
                    Some(())
                }
                other => {
                    out.push(other.clone());
                    Some(())
                }
            })
        }

        collect_into(self, result, 0, should_stop)?;
        if should_stop() {
            None
        } else {
            Some(())
        }
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
        self.conjuncts_checked(|| false).unwrap_or_default()
    }

    /// Borrowed equivalent of the canonical collector, including its depth
    /// fallback. A cancelled traversal never exposes its partial vector.
    pub(crate) fn conjuncts_checked(&self, mut stop: impl FnMut() -> bool) -> Option<Vec<&Self>> {
        fn collect_refs<'a>(
            expr: &'a ChcExpr,
            out: &mut Vec<&'a ChcExpr>,
            depth: usize,
            stop: &mut dyn FnMut() -> bool,
        ) -> Option<()> {
            if stop() {
                return None;
            }
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                out.push(expr);
                return Some(());
            }
            maybe_grow_expr_stack(|| {
                match expr {
                    ChcExpr::Op(ChcOp::And, args) => {
                        for arg in args {
                            collect_refs(arg, out, depth + 1, stop)?;
                        }
                    }
                    other => out.push(other),
                }
                Some(())
            })
        }
        let mut result = Vec::new();
        collect_refs(self, &mut result, 0, &mut stop)?;
        if stop() {
            None
        } else {
            Some(result)
        }
    }
}
