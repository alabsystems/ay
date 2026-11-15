// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Attempt-local alpha-renaming for exact and polynomial acyclic encodings.
//!
//! Source identifiers are never rewritten. On a potential reserved-family
//! collision, every generated local/formal gets a suffix absent from the end
//! of every source symbol. The legacy spelling is retained otherwise.
//! Each substitution is admitted by a complete bounded walk, not `vars()`'s
//! depth-truncated census. This is cooperative cancellation, not an allocation
//! or wall-clock bound on individual string/hash/clone operations.

use crate::{ChcExpr, ChcProblem, ChcVar, HornClause};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

mod scan;
use scan::{Node, Scan};

const SUFFIX: &str = "__ay_exact_";

/// Resource/shape refusal is not an ordinary unavailable exact encoding.
#[derive(Debug)]
pub(super) struct ExactExpansionRefused;

pub(super) struct AcyclicNames<'a> {
    control: Control<'a>,
    suffix: String,
    next_instance: usize,
    next_square: usize,
}

struct Control<'a> {
    keep_going: &'a mut dyn FnMut() -> bool,
    stopped: bool,
}

impl Control<'_> {
    fn poll(&mut self) -> Option<()> {
        if self.stopped {
            return None;
        }
        // A panic caught further out must not revive this naming attempt.
        self.stopped = true;
        if !(self.keep_going)() {
            return None;
        }
        self.stopped = false;
        Some(())
    }

    fn refuse<T>(&mut self) -> Option<T> {
        self.stopped = true;
        None
    }
}

impl<'a> AcyclicNames<'a> {
    pub(super) fn new(
        problem: &ChcProblem,
        keep_going: &'a mut dyn FnMut() -> bool,
    ) -> Option<Self> {
        let mut control = Control {
            keep_going,
            stopped: false,
        };
        control.poll()?;
        let mut collision = false;
        let mut occupied = DetHashSet::default();
        Scan::new(&mut control).problem(problem, &mut |node| {
            if let Node::Name(name) = node {
                collision |= name.starts_with("__bmc_dag_")
                    || name.starts_with("__bmc_reach_")
                    || name.starts_with("__bmc_poly_")
                    || name.starts_with("__bmc_square_lia_aux_");
                if let Some((_, ordinal)) = name.rsplit_once(SUFFIX) {
                    if let Ok(ordinal) = ordinal.parse::<usize>() {
                        occupied.insert(ordinal);
                    }
                }
            }
            Some(())
        })?;
        let suffix = if collision {
            let mut ordinal = 0usize;
            while occupied.contains(&ordinal) {
                control.poll()?;
                ordinal = ordinal.checked_add(1)?;
            }
            format!("{SUFFIX}{ordinal}")
        } else {
            String::new()
        };
        drop(occupied);
        control.poll()?;
        Some(Self {
            control,
            suffix,
            next_instance: 0,
            next_square: 0,
        })
    }

    pub(super) fn poll(&mut self) -> Option<()> {
        self.control.poll()
    }

    pub(super) fn stopped(&self) -> bool {
        self.control.stopped
    }

    pub(super) fn refuse<T>(&mut self) -> Option<T> {
        self.control.refuse()
    }

    pub(super) fn instance(&mut self) -> Option<usize> {
        self.poll()?;
        let instance = self.next_instance;
        let Some(next) = instance.checked_add(1) else {
            return self.control.refuse();
        };
        self.next_instance = next;
        Some(instance)
    }

    pub(super) fn name(&mut self, stem: String) -> Option<String> {
        self.poll()?;
        Some(format!("{stem}{}", self.suffix))
    }

    /// Independent conjunct groups can coexist in one polynomial query.
    /// Their existential square witnesses must never reuse an auxiliary.
    pub(super) fn square_name(&mut self) -> Option<String> {
        self.poll()?;
        let ordinal = self.next_square;
        let Some(next) = ordinal.checked_add(1) else {
            return self.refuse();
        };
        self.next_square = next;
        Some(format!("__bmc_square_lia_aux_{ordinal}{}", self.suffix))
    }

    pub(super) fn variables<'b>(&mut self, clause: &'b HornClause) -> Option<Vec<&'b ChcVar>> {
        // Complete every nested sort before the collecting pass uses Eq.
        Scan::new(&mut self.control).clause(clause, &mut |_| Some(()))?;
        let mut variables = Vec::new();
        let mut seen = DetHashMap::default();
        Scan::new(&mut self.control).clause(clause, &mut |node| {
            if let Node::Expr(ChcExpr::Var(var), _) = node {
                if let Some(previous) = seen.get(var.name.as_str()) {
                    if *previous != &var.sort {
                        return None;
                    }
                } else {
                    seen.insert(var.name.as_str(), &var.sort);
                    variables.push(var);
                }
            }
            Some(())
        })?;
        self.poll()?;
        Some(variables)
    }

    pub(super) fn check(&mut self, expression: &ChcExpr) -> Option<()> {
        Scan::new(&mut self.control).expression(expression, &mut |_| Some(()))?;
        self.poll()
    }

    pub(super) fn check_all(&mut self, expressions: &[ChcExpr]) -> Option<()> {
        let mut scan = Scan::new(&mut self.control);
        scan.conjunction(expressions)?;
        self.poll()
    }

    pub(super) fn recursion(&mut self, depth: usize) -> Option<()> {
        self.poll()?;
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return self.control.refuse();
        }
        Some(())
    }

    pub(super) fn instance_vars(
        &mut self,
        clause: &HornClause,
    ) -> Option<DetHashMap<String, ChcExpr>> {
        let instance = self.instance()?;
        let mut substitutions = DetHashMap::default();
        for (index, variable) in self.variables(clause)?.into_iter().enumerate() {
            let name = self.name(format!("__bmc_dag_e{instance}_v{index}"))?;
            substitutions.insert(
                variable.name.clone(),
                ChcExpr::Var(ChcVar::new(name, variable.sort.clone())),
            );
        }
        Some(substitutions)
    }

    pub(super) fn substitute_all(
        &mut self,
        expressions: &[ChcExpr],
        substitutions: &DetHashMap<String, ChcExpr>,
    ) -> Option<Vec<ChcExpr>> {
        expressions
            .iter()
            .map(|expr| self.substitute(expr, substitutions))
            .collect()
    }

    pub(super) fn substitute_typed(
        &mut self,
        expression: &ChcExpr,
        substitutions: &[(ChcVar, ChcExpr)],
    ) -> Option<ChcExpr> {
        self.check(expression)?;
        for (_, replacement) in substitutions {
            self.check(replacement)?;
        }
        let result = expression.substitute(substitutions);
        self.check(&result)?;
        Some(result)
    }

    pub(super) fn substitute(
        &mut self,
        expression: &ChcExpr,
        substitutions: &DetHashMap<String, ChcExpr>,
    ) -> Option<ChcExpr> {
        self.check(expression)?;
        for replacement in substitutions.values() {
            self.check(replacement)?;
        }
        // The input walk bounds EVERY occurrence below the existing depth and
        // node limits, hence its memoized substitution cannot partially bail.
        let result = expression.substitute_name_map(substitutions);
        // Substitution can increase depth/size. Reject before another rewrite
        // or truncated variable census can consume that expanded expression.
        self.check(&result)?;
        Some(result)
    }
}

#[cfg(test)]
mod square_names;
#[cfg(test)]
mod tests;
