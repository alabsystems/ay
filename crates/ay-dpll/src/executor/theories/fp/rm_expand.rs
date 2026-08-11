// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Symbolic-RoundingMode finite-domain enumeration for the FP lane
//! (Pass C of #P0.2 symbolic RoundingMode).
//!
//! A declared `RoundingMode` constant used as a rounding-op operand
//! (`(fp.roundToIntegral rm x)` with `(= rm roundTowardZero)`) used to
//! fail closed to `unknown` (`check_fp_support`'s non-literal-mode guard).
//! RoundingMode is a FIXED 5-element domain, so the problem DECIDES by
//! case-splitting the declared RM constants over {RNE, RNA, RTP, RTN, RTZ}:
//!
//! * substitute each assignment into the assertion set,
//! * constant-fold the RM-literal equality atoms the substitution exposes
//!   (`(= RTZ RNE)` → `false` — leaving them as opaque atoms would hand the
//!   SAT layer a free variable, the classic false-SAT hole #6189),
//! * solve each branch through the ordinary literal-mode FP pipeline,
//! * `sat` on the first satisfiable branch (recording the winning modes into
//!   the model), `unsat` when EVERY branch is unsat, `unknown` if any branch
//!   is unknown and none is sat.
//!
//! Soundness: the branches are exactly the models of the original formula
//! partitioned by the (finite, total) RM assignment — a disjunctive split,
//! each branch solved by the existing verified pipeline. No new encoding is
//! trusted. Shapes outside the enumeration's scope (a non-Var symbolic RM
//! term such as `(ite b RTP RTZ)` or an RM-valued UF application, more than
//! [`RM_ENUM_MAX_VARS`] RM consts, quantifiers) are left to
//! `check_fp_support`'s strengthened fail-closed backstop — `unknown`, never
//! a guess.
//!
//! Proofs: an enumeration `unsat` has no single reconstructable certificate
//! (the per-branch traces attest substituted problems), so the proof/trace
//! state is WIPED on the unsat return — the CLI then takes its honest
//! "no proof certificate emitted" degrade, and `--strict-proofs` /
//! self-check refuse the uncertified verdict rather than trusting a bogus
//! one.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::TermId;
use ay_fp::RoundingMode;

use crate::ematching::contains_quantifier;
use crate::executor::rm_domain::{
    is_rm_literal, is_rm_sort, rm_literal_mode, rm_literal_term, rm_long_name, RM_MODES,
};
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult, UnknownReason};

/// Enumeration cap: 5^k branches; k ≤ 3 keeps the worst case at 125 ordinary
/// literal-mode solves. Beyond that the backstop fails closed.
const RM_ENUM_MAX_VARS: usize = 3;

impl Executor {
    /// Attempt the symbolic-RM enumeration over `ctx.assertions`.
    ///
    /// `Ok(None)` means "not applicable — continue the normal solve_fp
    /// pipeline" (which fail-closes via `check_fp_support` when a symbolic RM
    /// remains). `Ok(Some(result))` is a final verdict for this solve.
    pub(in crate::executor) fn try_solve_fp_symbolic_rm(&mut self) -> Result<Option<SolveResult>> {
        // ---- Scope check: every symbolic RM term must be a plain Var ----
        let mut rm_vars: Vec<TermId> = Vec::new();
        {
            let terms = &self.ctx.terms;
            let mut seen: HashSet<TermId> = HashSet::default();
            let mut stack: Vec<TermId> = self.ctx.assertions.clone();
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                if is_rm_sort(terms.sort(t)) && !is_rm_literal(terms, t) {
                    if matches!(terms.get(t), TermData::Var(..)) {
                        rm_vars.push(t);
                    } else {
                        // Non-Var symbolic RM shape (RM ite, RM-valued UF …):
                        // stays fail-closed at the backstop.
                        return Ok(None);
                    }
                }
                match terms.get(t) {
                    TermData::App(_, args) => stack.extend_from_slice(args),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Let(bindings, body) => {
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                        stack.push(*body);
                    }
                    // Quantified FP + symbolic RM: out of scope (QF lane).
                    TermData::Forall(..) | TermData::Exists(..) => return Ok(None),
                    _ => {}
                }
            }
        }
        if rm_vars.is_empty() {
            return Ok(None);
        }
        if rm_vars.len() > RM_ENUM_MAX_VARS {
            return Ok(None);
        }
        if self
            .ctx
            .assertions
            .iter()
            .any(|&a| contains_quantifier(&self.ctx.terms, a))
        {
            return Ok(None);
        }
        // Deterministic var order (first-visit order depends on stack order;
        // sort by TermId for stability).
        rm_vars.sort_unstable_by_key(|t| t.0);

        // ---- Enumerate 5^k assignments in canonical mode order ----
        let saved_assertions = self.ctx.assertions.clone();
        let k = rm_vars.len();
        let total: usize = 5usize.pow(k as u32);
        let mut any_unknown = false;
        for branch in 0..total {
            if self.should_abort_theory_loop() {
                self.ctx.assertions = saved_assertions;
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                return Ok(Some(SolveResult::Unknown));
            }
            // Decode branch index to a mode per var.
            let mut idx = branch;
            let assignment: Vec<RoundingMode> = (0..k)
                .map(|_| {
                    let m = RM_MODES[idx % 5];
                    idx /= 5;
                    m
                })
                .collect();

            // Pass 1: substitute the RM vars by their assigned literals.
            let mut map: HashMap<TermId, TermId> = HashMap::default();
            for (i, &v) in rm_vars.iter().enumerate() {
                let lit = rm_literal_term(&mut self.ctx.terms, assignment[i]);
                map.insert(v, lit);
            }
            let substituted: Vec<TermId> = saved_assertions
                .iter()
                .map(|&a| self.ctx.terms.substitute_terms(a, &map))
                .collect();

            // Pass 2: fold RM-literal equality/distinct atoms to Bool
            // constants (substitute_terms rebuilds apps WITHOUT
            // smart-constructor folding, and an unfolded `(= RTZ RNE)` atom
            // would be a free SAT variable — false-SAT risk #6189).
            let fold_map = self.collect_rm_literal_atom_folds(&substituted);
            let folded: Vec<TermId> = if fold_map.is_empty() {
                substituted
            } else {
                substituted
                    .iter()
                    .map(|&a| self.ctx.terms.substitute_terms(a, &fold_map))
                    .collect()
            };

            // Solve the branch through the ordinary pipeline (recursion depth
            // is 1: the branch has no symbolic RM left, so the enumeration
            // hook is a no-op; any RM shape that somehow survives hits the
            // fail-closed backstop and the branch counts as unknown).
            self.ctx.assertions = folded;
            let branch_result = self.solve_fp();
            self.ctx.assertions = saved_assertions.clone();
            match branch_result? {
                SolveResult::Sat => {
                    // Pin the winning modes into the model so evaluation,
                    // printing, and the independent gate all read the same
                    // literal (evaluate_var consults `completed_values` after
                    // the theory chain; the FP lane has no EUF model).
                    if let Some(model) = self.last_model.as_mut() {
                        for (i, &v) in rm_vars.iter().enumerate() {
                            model.completed_values.insert(
                                v,
                                crate::executor::model::EvalValue::Element(
                                    rm_long_name(assignment[i]).to_string(),
                                ),
                            );
                        }
                    }
                    self.last_unknown_reason = None;
                    return Ok(Some(SolveResult::Sat));
                }
                SolveResult::Unknown => {
                    any_unknown = true;
                }
                unsat => {
                    debug_assert!(unsat.is_unsat());
                }
            }
        }
        if any_unknown {
            // At least one branch could not be decided: `unsat` is unproven.
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(Some(SolveResult::Unknown));
        }
        // FAIL THE PROOF-EMISSION PATH CLOSED: an enumeration `unsat` is the
        // conjunction of 5^k per-branch refutations, but the proof/trace state
        // now holds only the LAST branch's session — reconstructing a
        // certificate from it would attest the wrong (substituted) problem.
        // Wipe it so the CLI takes its honest "no proof certificate emitted"
        // degrade (and `--strict-proofs` / self-check refuse the uncertified
        // verdict) instead of emitting a bogus certificate.
        self.last_proof = None;
        self.clear_finite_enum_proof_state();
        self.last_lrat_certificate = None;
        self.last_proof_term_overrides = None;
        self.last_proof_quality = None;
        self.last_clause_trace = None;
        self.last_checked_sat_refutation = None;
        self.last_var_to_term = None;
        self.last_trail_provenance = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.proof_problem_assertion_provenance = None;
        self.proof_tracker.reset_session();
        self.last_unknown_reason = None;
        Ok(Some(SolveResult::unsat()))
    }

    /// Map every `=`/`distinct` application over ALL-RM-literal operands in
    /// `roots` to its truth constant. (`mk_distinct` expands n-ary distinct at
    /// elaboration, so the `distinct` arm is defensive for embedder terms.)
    fn collect_rm_literal_atom_folds(&self, roots: &[TermId]) -> HashMap<TermId, TermId> {
        let mut folds: HashMap<TermId, TermId> = HashMap::default();
        let mut modes_scratch: Vec<RoundingMode> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots.to_vec();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    stack.extend_from_slice(args);
                    let name = sym.name();
                    if (name == "=" || name == "distinct") && args.len() >= 2 {
                        modes_scratch.clear();
                        for &a in args {
                            match rm_literal_mode(&self.ctx.terms, a) {
                                Some(m) => modes_scratch.push(m),
                                None => {
                                    modes_scratch.clear();
                                    break;
                                }
                            }
                        }
                        if modes_scratch.len() == args.len() {
                            let value = if name == "=" {
                                modes_scratch.windows(2).all(|w| w[0] == w[1])
                            } else {
                                // distinct: pairwise different
                                let mut ms = modes_scratch.clone();
                                ms.sort_unstable_by_key(|m| *m as u8);
                                ms.windows(2).all(|w| w[0] != w[1])
                            };
                            let b = if value {
                                self.ctx.terms.true_term()
                            } else {
                                self.ctx.terms.false_term()
                            };
                            folds.insert(t, b);
                        }
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, el) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                _ => {}
            }
        }
        folds
    }
}
