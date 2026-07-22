// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound refinement target analysis and queuing for implied bounds.
//!
//! Extracted from `implied_bounds.rs` to reduce file size.
//! Contains: refinement eligibility checks, target reconstruction,
//! `prepare_bound_refinement_request`, `push_bound_refinement_request`,
//! `queue_bound_refinement_request`, and `queue_post_simplex_refinements`.

use super::*;

impl LraSolver {
    pub(crate) fn term_supports_bound_refinement(&self, term: TermId) -> bool {
        match self.terms().get(term) {
            TermData::Var(_, _) => true,
            TermData::Const(_)
            | TermData::Ite(_, _, _)
            | TermData::Let(_, _)
            | TermData::Not(_) => false,
            TermData::App(Symbol::Named(name), _) => {
                !matches!(name.as_str(), "+" | "-" | "*" | "/" | "to_real" | "to_int")
            }
            TermData::App(_, _) => true,
            TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => false,
            other => unreachable!(
                "unhandled TermData variant in term_supports_bound_refinement(): {other:?}"
            ),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn term_as_rational(&self, term: TermId) -> Option<BigRational> {
        match self.terms().get(term) {
            TermData::Const(Constant::Int(value)) => Some(BigRational::from(value.clone())),
            TermData::Const(Constant::Rational(value)) => Some(value.0.clone()),
            _ => None,
        }
    }

    /// Recognize affine source terms that are exactly `var + c`.
    ///
    /// This keeps bound refinement scoped to registered relative templates with
    /// one arithmetic variable per side. Multi-variable additive terms remain
    /// out of scope for #6566/#6579.
    #[allow(dead_code)]
    pub(crate) fn term_as_affine_refinement_target(
        &self,
        term: TermId,
    ) -> Option<(TermId, BigRational)> {
        match self.terms().get(term) {
            TermData::Var(_, _) => Some((term, BigRational::zero())),
            TermData::App(Symbol::Named(name), args) if name == "+" => {
                let mut constant = BigRational::zero();
                let mut variable = None;
                for &arg in args {
                    if let Some(value) = self.term_as_rational(arg) {
                        constant += value;
                        continue;
                    }
                    let (var, offset) = self.term_as_affine_refinement_target(arg)?;
                    if !offset.is_zero() || variable.replace(var).is_some() {
                        return None;
                    }
                }
                variable.map(|var| (var, constant))
            }
            TermData::App(Symbol::Named(name), args) if name == "-" => {
                let (&first, rest) = args.split_first()?;
                let (variable, mut constant) = self.term_as_affine_refinement_target(first)?;
                for &arg in rest {
                    constant -= self.term_as_rational(arg)?;
                }
                Some((variable, constant))
            }
            _ => None,
        }
    }

    // Registered relative atoms can share a slack row with internal-only or
    // additive atoms. Only reconstruct through the already-registered source
    // atom indexed under that slack; arbitrary internal slack rows remain out
    // of scope (#6548, #6566).
    #[allow(dead_code)]
    pub(crate) fn slack_bound_refinement_target(
        &self,
        slack: u32,
        slack_bound_value: &BigRational,
        is_upper: bool,
    ) -> Option<(TermId, Option<TermId>, BigRational, bool)> {
        let row_idx = *self.basic_var_to_row.get(&slack)?;
        let row = self.rows.get(row_idx)?;
        let orig_constant = row.constant.to_big();
        let atoms = self.atom_index.get(&slack)?;

        for atom in atoms {
            let Some(Some(info)) = self.atom_cache.get(&atom.term) else {
                continue;
            };
            if info.is_eq || info.is_distinct {
                continue;
            }
            let adjusted_bound =
                slack_bound_value.clone() + info.expr.constant.to_big() - &orig_constant;
            let TermData::App(Symbol::Named(name), args) = self.terms().get(atom.term) else {
                continue;
            };
            if args.len() != 2 || !matches!(name.as_str(), "<" | "<=" | ">" | ">=") {
                continue;
            }
            if let Some(rhs_constant) = self.term_as_rational(args[1]) {
                let (lhs_var, lhs_offset) = self.term_as_affine_refinement_target(args[0])?;
                return Some((
                    lhs_var,
                    None,
                    rhs_constant + adjusted_bound - lhs_offset,
                    is_upper,
                ));
            }
            if let Some(lhs_constant) = self.term_as_rational(args[0]) {
                let (rhs_var, rhs_offset) = self.term_as_affine_refinement_target(args[1])?;
                return Some((
                    rhs_var,
                    None,
                    lhs_constant - adjusted_bound - rhs_offset,
                    !is_upper,
                ));
            }
            // Two-variable (compound) slack refinements are only safe when the
            // refinement direction matches the atom's direction. The slack
            // expression stores `lhs - rhs` with the atom's original polarity.
            // An upper-bound refinement on the slack corresponds to tightening
            // `lhs <= rhs + δ`, which is safe when the atom is also upper-bound
            // direction (< or <=). A lower-bound refinement corresponds to
            // `lhs >= rhs + δ`, which CONTRADICTS atoms like `(< lhs rhs)`.
            //
            // Without this guard, `(< y x)` (slack `y - x`, is_upper=true) can
            // produce `y >= x` via a lower-bound refinement, directly
            // contradicting the original `y < x` constraint (#6548).
            if atom.is_upper != is_upper {
                continue;
            }
            let (lhs_var, lhs_offset) = self.term_as_affine_refinement_target(args[0])?;
            let (rhs_var, rhs_offset) = self.term_as_affine_refinement_target(args[1])?;
            return Some((
                lhs_var,
                Some(rhs_var),
                adjusted_bound + rhs_offset - lhs_offset,
                is_upper,
            ));
        }
        None
    }

    #[allow(dead_code)]
    pub(crate) fn bound_refinement_target(
        &self,
        var: u32,
        bound_value: &BigRational,
        is_upper: bool,
    ) -> Option<(TermId, Option<TermId>, BigRational, bool)> {
        if let Some(&term) = self.var_to_term.get(&var) {
            return Some((term, None, bound_value.clone(), is_upper));
        }
        if self.slack_var_set.contains(&var) {
            return self.slack_bound_refinement_target(var, bound_value, is_upper);
        }
        None
    }

    /// Whether a variable can currently map back to a registered source atom.
    pub(crate) fn can_materialize_bound_refinement_var(&self, var: u32) -> bool {
        if self.var_to_term.contains_key(&var) {
            return true;
        }
        self.atom_index.get(&var).is_some_and(|atoms| {
            atoms.iter().any(|atom| {
                self.atom_cache
                    .get(&atom.term)
                    .and_then(|info| info.as_ref())
                    .is_some_and(|info| !info.is_eq && !info.is_distinct)
            })
        })
    }

    #[allow(dead_code)]
    pub(crate) fn prepare_bound_refinement_request(
        &self,
        var: u32,
        bound_value: &BigRational,
        is_upper: bool,
    ) -> Option<(TermId, Option<TermId>, BigRational, bool, bool)> {
        let debug = self.debug_lra;
        if !self.can_materialize_bound_refinement_var(var) {
            return None;
        }
        let Some((term, rhs_term, request_bound_value, request_is_upper)) =
            self.bound_refinement_target(var, bound_value, is_upper)
        else {
            if debug {
                safe_eprintln!(
                    "[LRA] skip refinement: var {} has no materializable target ({} {})",
                    var,
                    if is_upper { "<=" } else { ">=" },
                    bound_value
                );
            }
            return None;
        };
        // Use cached refinement eligibility (#6590 Packet 1); fall back to
        // self.terms on cache miss for terms registered before caching was added.
        let eligible = self
            .refinement_eligible_cache
            .get(&term)
            .copied()
            .unwrap_or_else(|| self.term_supports_bound_refinement(term));
        if !eligible {
            if debug {
                safe_eprintln!(
                    "[LRA] skip refinement: term {:?} does not support refinement",
                    term
                );
            }
            return None;
        }
        let vi = var as usize;
        let Some(info) = self.vars.get(vi) else {
            if debug {
                safe_eprintln!("[LRA] skip refinement: missing VarInfo for {}", var);
            }
            return None;
        };
        // Use cached integer-sort check (#6590 Packet 1); fall back to
        // self.terms on cache miss.
        let is_integer = self
            .is_integer_sort_cache
            .get(&term)
            .copied()
            .unwrap_or_else(|| self.terms().sort(term) == &Sort::Int);

        // Mirror Z3's refine_bound guards: for reals, only create a new bound
        // when the variable lacks that direct bound; integers also refine when
        // the opposite-direction bound exists.
        if is_integer {
            if request_is_upper {
                if info.lower.is_none() && info.upper.is_some() {
                    if debug {
                        safe_eprintln!(
                            "[LRA] skip refinement: int {:?} upper already directly bounded",
                            term
                        );
                    }
                    return None;
                }
            } else if info.upper.is_none() && info.lower.is_some() {
                if debug {
                    safe_eprintln!(
                        "[LRA] skip refinement: int {:?} lower already directly bounded",
                        term
                    );
                }
                return None;
            }
        } else {
            // For reals: skip if the existing direct bound is at least as tight.
            let dominated = if request_is_upper {
                info.upper
                    .as_ref()
                    .is_some_and(|ub| ub.value <= request_bound_value)
            } else {
                info.lower
                    .as_ref()
                    .is_some_and(|lb| lb.value >= request_bound_value)
            };
            if dominated {
                if debug {
                    safe_eprintln!(
                        "[LRA] skip refinement: real {:?} direct {} bound already tighter",
                        term,
                        if request_is_upper { "upper" } else { "lower" }
                    );
                }
                return None;
            }
        }

        Some((
            term,
            rhs_term,
            request_bound_value,
            request_is_upper,
            is_integer,
        ))
    }

    #[allow(dead_code)]
    pub(crate) fn push_bound_refinement_request(
        &mut self,
        variable: TermId,
        rhs_term: Option<TermId>,
        bound_value: BigRational,
        is_upper: bool,
        is_integer: bool,
        reason: Vec<TheoryLit>,
    ) {
        let debug = self.debug_lra;
        if self.pending_bound_refinements.iter().any(|req| {
            req.variable == variable
                && req.rhs_term == rhs_term
                && req.bound_value == bound_value
                && req.is_upper == is_upper
        }) {
            if debug {
                safe_eprintln!(
                    "[LRA] skip refinement: duplicate {:?} ({} {})",
                    variable,
                    if is_upper { "<=" } else { ">=" },
                    bound_value
                );
            }
            return;
        }
        self.pending_bound_refinements.push(BoundRefinementRequest {
            variable,
            rhs_term,
            bound_value,
            is_upper,
            is_integer,
            reason,
        });
        if debug {
            safe_eprintln!(
                "[LRA] queued refinement {:?} ({} {})",
                variable,
                if is_upper { "<=" } else { ">=" },
                self.pending_bound_refinements
                    .last()
                    .expect("just pushed")
                    .bound_value
            );
        }
    }

    /// Bound refinement enqueue — DISABLED pending soundness fix.
    ///
    /// DISABLED (#8187, root cause #8254): Bound refinements create permanent
    /// SAT clauses from implied bounds, but implied bounds can become stale
    /// after DPLL backtracking (the bounds they were derived from may be
    /// retracted, but the implied bounds persist until pop()). This causes
    /// false UNSAT on 6+ QF_LRA benchmarks where Z3 returns SAT.
    ///
    /// Re-enabling requires tying implied-bound provenance to the DPLL trail
    /// so stale entries are retracted on backtrack. Tracked by #8187 (CHC/SMT
    /// epic #8164). Callers may also set `--no-bound-refinement` to make the
    /// disable explicit at the call site (`check_atoms.rs` already gates on
    /// `self.no_bound_refinement`).
    #[allow(dead_code)]
    pub(crate) fn queue_bound_refinement_request(
        &mut self,
        _var: u32,
        _bound_value: BigRational,
        _is_upper: bool,
        _row_idx: usize,
    ) {
        // Body intentionally empty: see DISABLED note in doc comment.
    }

    /// Per-call cap on bound refinement atoms to prevent unbounded atom
    /// creation during BCP, where the theory callback fires hundreds of times
    /// per solve. Z3 has no explicit cap but its filtering (skip composed
    /// columns, only refine when same-side missing) naturally limits creation.
    /// AY's filtering is ported from Z3 (prepare_bound_refinement_request),
    /// and this budget is a safety valve for pathological cases.
    ///
    /// Currently unused while bound refinement is DISABLED (#8187) but kept
    /// so the budget value is ready for re-enablement.
    #[allow(dead_code)]
    const MAX_REFINEMENTS_PER_CHECK: usize = 8;

    /// Post-simplex bound refinement scan — DISABLED pending soundness fix.
    ///
    /// DISABLED (#8187, root cause #8254): Same cause as
    /// `queue_bound_refinement_request`. Implied bounds used for refinement
    /// derivation can be stale after DPLL backtracking, producing permanent
    /// SAT clauses with insufficient justification.
    ///
    /// Original design (#4919 BP_REFINE Phase 6): after
    /// `compute_implied_bounds()` populates `self.implied_bounds`, scan
    /// variables with row-derived implied bounds that can be materialized
    /// back into concrete arithmetic atoms. For each direction (upper/lower)
    /// where the implied bound is tighter than ALL existing unasserted atoms,
    /// queue a `BoundRefinementRequest` so the DPLL executor can create a new
    /// bound atom, subject to `MAX_REFINEMENTS_PER_CHECK` per-call budget.
    ///
    /// Reference: Z3 `propagate_lp_solver_bound() / refine_bound()` at
    /// `theory_lra.cpp:2407-2504`. Z3 iterates `m_bp.ibounds()` from the LP
    /// solver, which includes all variables with LP-derived bounds.
    ///
    /// Callers may also set `--no-bound-refinement`; `check_atoms.rs`
    /// already gates the call on `self.no_bound_refinement` (#8319).
    pub(crate) fn queue_post_simplex_refinements(
        &mut self,
        _newly_bounded: &DenseU32Set,
        _debug: bool,
    ) {
        // Body intentionally empty: see DISABLED note in doc comment.
    }
}
