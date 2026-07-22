// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! IUC solver result type and term-walking helpers.

use crate::smt::{FarkasConflict, Partition, SmtValue, UnsatCoreDiagnostics};
use crate::ChcExpr;
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Result of an IUC solver query.
#[derive(Debug, Clone)]
pub(crate) enum IucResult {
    /// Formula is satisfiable, with a model (read in tests for correctness verification).
    Sat(FxHashMap<String, SmtValue>),
    /// Formula is unsatisfiable.
    Unsat {
        /// The expanded core with partition information for each constraint.
        core: Vec<(ChcExpr, Partition)>,
        /// Farkas conflicts from the arithmetic theory.
        farkas_conflicts: Vec<FarkasConflict>,
        /// Optional SMT-level diagnostics from UNSAT-core extraction.
        diagnostics: Option<UnsatCoreDiagnostics>,
    },
    /// Solver couldn't determine satisfiability.
    Unknown,
}

impl std::fmt::Display for IucResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sat(_) => write!(f, "sat"),
            Self::Unsat { core, .. } => write!(f, "unsat (core size: {})", core.len()),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

#[cfg(test)]
impl IucResult {
    /// Returns true if the result is UNSAT.
    pub(crate) fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat { .. })
    }

    /// Returns true if the result is SAT.
    pub(crate) fn is_sat(&self) -> bool {
        matches!(self, Self::Sat(_))
    }
}

/// Collect variable names referenced by a term, walking the term tree.
///
/// Appends variable names to `out` for all `Var(name, _)` nodes reachable
/// from `root` in the TermStore. Used for partition re-tagging of Farkas
/// conflict terms (#816 Phase 2).
pub(super) fn collect_term_var_names<'a>(
    terms: &ay_core::TermStore,
    root: ay_core::TermId,
    reverse_var_map: &FxHashMap<ay_core::TermId, &'a str>,
    out: &mut Vec<&'a str>,
) {
    use ay_core::TermData;
    let mut stack = vec![root];
    let mut visited = FxHashSet::default();

    while let Some(tid) = stack.pop() {
        if !visited.insert(tid) {
            continue;
        }

        // If this TermId is a named variable, record it
        if let Some(&name) = reverse_var_map.get(&tid) {
            out.push(name);
        }

        // Walk children
        match terms.get(tid) {
            TermData::Const(_) => {}
            TermData::Var(_, _) => {} // Already handled above via reverse_var_map
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            // Unknown TermData variant; skip (#6091).
            _ => {}
        }
    }
}

/// Collect all theory atoms reachable from `root`.
///
/// Mirrors `smt.rs` atom collection logic but scoped locally so IUC can capture
/// original A/B atom membership before proxy implications are introduced.
pub(super) fn collect_theory_atoms_from_root(
    terms: &ay_core::TermStore,
    root: ay_core::TermId,
    out: &mut FxHashSet<ay_core::TermId>,
) {
    use ay_core::TermData;
    let mut stack = vec![root];
    let mut visited: FxHashSet<ay_core::TermId> = FxHashSet::default();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        if crate::smt::is_theory_atom(terms, t) {
            out.insert(t);
            continue;
        }
        match terms.get(t) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, then_br, else_br) => {
                stack.push(*c);
                stack.push(*then_br);
                stack.push(*else_br);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            // Unknown TermData variant; skip (#6091).
            _ => {}
        }
    }
}
