// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Atom parsing and linear expression construction for LRA.
//!
//! Variable interning, linear expression parsing, and atom normalization.
//! Bound assertion, slack variable management, and compound atom propagation
//! are in `atom_assertion`.

use super::*;
use crate::rational::Rational;

/// Cached `Rational::Small(-1, 1)` for `lhs - rhs` parsing.
/// Avoids `BigRational::from(BigInt::from(-1))` heap allocation per atom (#8406).
fn neg_one_rat() -> &'static Rational {
    use std::sync::OnceLock;
    static NEG_ONE: OnceLock<Rational> = OnceLock::new();
    NEG_ONE.get_or_init(|| Rational::Small(-1, 1))
}

impl LraSolver {
    /// Get or create an internal variable for a term
    pub(crate) fn intern_var(&mut self, term: TermId) -> u32 {
        if let Some(&var) = self.term_to_var.get(&term) {
            if self.debug_intern {
                safe_eprintln!("[INTERN] term {:?} already mapped to var {}", term, var);
            }
            return var;
        }
        let var = self.next_var;
        if self.debug_intern {
            let bt = std::backtrace::Backtrace::force_capture();
            safe_eprintln!(
                "[INTERN] term {:?} -> var {}\nBacktrace:\n{}",
                term,
                var,
                bt
            );
        }
        self.next_var += 1;
        self.term_to_var.insert(term, var);
        self.var_to_term.insert(var, term);
        // Extend vars vector if needed
        while self.vars.len() <= var as usize {
            self.vars.push(VarInfo::default());
        }
        self.vars[var as usize].status = Some(VarStatus::NonBasic);
        var
    }

    /// Recount `unassigned_atom_count` from `atom_cache` and `asserted`.
    /// Called after pop() to restore correct counts since atoms that were
    /// asserted in the popped scope become unasserted again.
    /// Counts ALL atoms (single + compound) per variable (#4919 Phase D).
    pub(crate) fn recount_unassigned_atoms(&mut self) {
        // Zero out all counts
        self.unassigned_atom_count.fill(0);
        // Count unasserted atoms from var_to_atoms (covers both single + compound).
        // Each unasserted atom contributes +1 to every variable it references.
        //
        // Dedup per-variable using a small local HashSet (reset per var) instead
        // of a global HashSet<(u32, TermId)>. The global version caused HashSet
        // rehash storms on every pop() — 48% of sc-6 runtime (#6772).
        let mut seen_atoms: HashSet<TermId> = HashSet::default();
        for (&var, atoms) in &self.var_to_atoms {
            let vi = var as usize;
            if vi >= self.unassigned_atom_count.len() {
                self.unassigned_atom_count.resize(vi + 1, 0);
            }
            seen_atoms.clear();
            for &atom_term in atoms {
                // Only count each atom once per variable (var_to_atoms may have duplicates)
                if !seen_atoms.insert(atom_term) {
                    continue;
                }
                // Skip eq/distinct atoms (not tracked for propagation filtering)
                let dominated = self
                    .atom_cache
                    .get(&atom_term)
                    .is_some_and(|info| info.as_ref().is_some_and(|i| i.is_eq || i.is_distinct));
                if dominated {
                    continue;
                }
                if !self.asserted.contains_key(&atom_term) {
                    self.unassigned_atom_count[vi] += 1;
                }
            }
        }
    }

    /// Mark the current parsing atom (if any) as having unsupported
    /// sub-expressions (#6167). Only atoms being parsed from the asserted
    /// trail have current_parsing_atom set; shared equalities, cross-sort
    /// bounds, and to_int axioms do not.
    pub(crate) fn mark_atom_unsupported(&mut self, atom: TermId) {
        if self.persistent_unsupported_atoms.insert(atom) {
            self.persistent_unsupported_trail.push(atom);
        }
    }

    pub(crate) fn mark_current_atom_unsupported(&mut self) {
        if let Some(atom) = self.current_parsing_atom {
            self.mark_atom_unsupported(atom);
        }
    }

    pub(crate) fn rewind_persistent_unsupported_atoms(&mut self, mark: usize) {
        while self.persistent_unsupported_trail.len() > mark {
            let atom = self
                .persistent_unsupported_trail
                .pop()
                .expect("scope mark must not exceed unsupported trail length");
            let removed = self.persistent_unsupported_atoms.remove(&atom);
            debug_assert!(
                removed,
                "unsupported atom trail/set out of sync for {atom:?}"
            );
        }
    }

    /// Parse a term into a linear expression
    pub fn parse_linear_expr(&mut self, term: TermId) -> LinearExpr {
        match self.terms().get(term) {
            TermData::Const(Constant::Int(n)) => {
                // #8406: Convert integer constant to Rational directly, avoiding
                // BigRational heap allocation when the value fits in i64.
                LinearExpr::constant_rat(Rational::from(n.clone()))
            }
            TermData::Const(Constant::Rational(r)) => {
                // #8406: Convert rational constant to Rational, shrinking to
                // Small(i64, i64) when numerator and denominator fit.
                LinearExpr::constant_rat(Rational::from_big(r.0.clone()))
            }
            TermData::Var(_, _) => {
                let var = self.intern_var(term);
                LinearExpr::var(var)
            }
            TermData::App(Symbol::Named(name), args) => {
                match name.as_str() {
                    "+" => {
                        let mut result = LinearExpr::zero();
                        for &arg in args {
                            let sub_expr = self.parse_linear_expr(arg);
                            result.add(&sub_expr);
                        }
                        result
                    }
                    "-" if args.len() == 1 => {
                        // Unary minus
                        let mut result = self.parse_linear_expr(args[0]);
                        result.negate();
                        result
                    }
                    "-" if args.len() >= 2 => {
                        // Binary/n-ary minus: a - b - c = a + (-b) + (-c)
                        let mut result = self.parse_linear_expr(args[0]);
                        for &arg in &args[1..] {
                            let mut sub_expr = self.parse_linear_expr(arg);
                            sub_expr.negate();
                            result.add(&sub_expr);
                        }
                        result
                    }
                    "*" => {
                        // Find constant and variable parts
                        // #8406: Use Rational instead of BigRational to avoid heap
                        // allocation when all multiplicands are small constants.
                        let mut const_part = Rational::one();
                        let mut var_expr: Option<LinearExpr> = None;

                        for &arg in args {
                            let sub_expr = self.parse_linear_expr(arg);
                            if sub_expr.is_constant() {
                                const_part = &const_part * &sub_expr.constant;
                            } else if var_expr.is_none() {
                                var_expr = Some(sub_expr);
                            } else {
                                // Non-linear: over-approximate as fresh variable.
                                // In combined_theory_mode, nonlinear multiplication is
                                // handled by the outer theory (NRA/NIA) — don't flag
                                // as unsupported (#4125).
                                if !self.combined_theory_mode {
                                    self.mark_current_atom_unsupported();
                                }
                                let var = self.intern_var(term);
                                return LinearExpr::var(var);
                            }
                        }

                        match var_expr {
                            Some(mut expr) => {
                                expr.scale_rat(&const_part);
                                expr
                            }
                            None => LinearExpr::constant_rat(const_part),
                        }
                    }
                    "/" if args.len() == 2 => {
                        // Division by constant
                        let num = self.parse_linear_expr(args[0]);
                        let denom = self.parse_linear_expr(args[1]);
                        if denom.is_constant() && !denom.constant.is_zero() {
                            let mut result = num;
                            let inv = denom.constant.recip();
                            result.scale_rat(&inv);
                            result
                        } else {
                            // Non-linear real "/" with non-constant denominator, or
                            // division by 0: over-approximate as fresh variable.
                            // In combined_theory_mode, symbolic division is handled
                            // by the outer theory (NRA) via monomial purification —
                            // don't flag as unsupported (#6811).
                            if !self.combined_theory_mode {
                                self.mark_current_atom_unsupported();
                            }
                            let var = self.intern_var(term);
                            LinearExpr::var(var)
                        }
                    }
                    "to_real" if args.len() == 1 => {
                        // Sort coercion Int -> Real is identity in the real domain (#4915).
                        // Parse the inner term directly so that to_real(x) shares
                        // the same LRA variable as x, enabling N-O equality propagation
                        // between LIA and LRA in the LIRA combined solver.
                        self.parse_linear_expr(args[0])
                    }
                    "to_int" if args.len() == 1 => {
                        // to_int(r) = floor(r). Create slack variable and record for
                        // floor axiom injection: to_int(x) <= x < to_int(x) + 1.
                        // The axiom is injected as bounds during check() (#5944).
                        let var = self.intern_var(term);
                        self.to_int_terms.push((var, args[0]));
                        LinearExpr::var(var)
                    }
                    // SMT-LIB abs: |x| = (ite (>= x 0) x (- x))
                    // Over-approximate as fresh variable (non-linear in general).
                    "abs" if args.len() == 1 => {
                        // In combined_theory_mode, abs terms are handled as opaque
                        // variables by the outer theory solver — don't mark as
                        // unsupported. Unlike div/mod (which always mark
                        // unsupported), abs model validation succeeds with
                        // opaque assignments.
                        if !self.combined_theory_mode {
                            self.mark_current_atom_unsupported();
                        }
                        let var = self.intern_var(term);
                        LinearExpr::var(var)
                    }
                    // Integer div/mod: opaque to LRA. Always mark as
                    // unsupported even in combined_theory_mode — model
                    // validation cannot verify opaque variable assignments
                    // match div/mod semantics (#6165).
                    "div" | "mod" if !args.is_empty() => {
                        self.mark_current_atom_unsupported();
                        let var = self.intern_var(term);
                        LinearExpr::var(var)
                    }
                    other => {
                        // Unknown function: create slack variable.
                        // In combined_theory_mode, cross-theory functions (UF, select)
                        // are expected — don't mark as unsupported (#5524).
                        //
                        // Boolean connectives (xor, and, or, not, =>) that appear
                        // inside arithmetic terms (e.g., (ite (xor a b) 1 0)) are
                        // fully handled by the SAT-level Tseitin encoding. The LRA
                        // solver correctly interns a fresh variable for the Boolean
                        // sub-expression — marking the enclosing atom unsupported
                        // would cause check_impl() to downgrade Sat to Unknown,
                        // producing spurious Unknown results (#8452).
                        let is_bool_connective =
                            matches!(other, "xor" | "and" | "or" | "not" | "=>" | "ite");
                        if self.debug_lra {
                            safe_eprintln!("[LRA] Unknown function: {:?}", other);
                        }
                        if !self.combined_theory_mode && !is_bool_connective {
                            self.mark_current_atom_unsupported();
                        }
                        let var = self.intern_var(term);
                        LinearExpr::var(var)
                    }
                }
            }
            TermData::Ite(cond, then_t, else_t) => {
                // Term-level ITE inside arithmetic: its value is condition-
                // dependent, and the condition is a SAT-layer choice.
                //
                // The old behavior substituted the branch selected by the
                // condition's CURRENT Boolean assignment. That is UNSOUND:
                // bounds and conflicts derived from the substituted parse did
                // not carry the condition literal as a premise, so learned
                // clauses over-generalized to assignments where the condition
                // flips. Concretely, with `k = (ite c -2 2)` and `c` currently
                // false, the split atom `(<= k 1)` parsed as `2 <= 1` and
                // produced the length-1 conflict `{(<= k 1)}` — learned as the
                // unit clause `k > 1`, which is FALSE for `c = true` (k = -2)
                // and caused a wrong UNSAT on satisfiable array/LIA formulas.
                // The `atom_cache` also pinned the substitution across
                // backtracking, so re-assertions under the flipped condition
                // kept the stale branch.
                //
                // Sound handling: treat the ITE as an opaque variable and
                // record it so check() can request the SAT-level link lemmas
                // `cond => (= ite then)` and `(not cond) => (= ite else)`
                // (via NeedModelEqualities with `implied: true`). The equality
                // atoms carry the exact branch semantics into the tableau with
                // the condition literal as a real, per-assignment premise in
                // every explanation.
                let is_arith_sorted = matches!(self.terms().sort(term), Sort::Int | Sort::Real);
                if is_arith_sorted && self.ite_link_terms_seen.insert(term) {
                    self.ite_link_terms.push((term, *cond, *then_t, *else_t));
                }
                let var = self.intern_var(term);
                LinearExpr::var(var)
            }
            _ => {
                // Unknown term: create slack variable.
                // In combined_theory_mode, cross-theory terms are expected —
                // don't mark as unsupported (#5524).
                if self.debug_lra {
                    safe_eprintln!("[LRA] Unknown term: {:?}", self.terms().get(term));
                }
                if !self.combined_theory_mode {
                    self.mark_current_atom_unsupported();
                }
                let var = self.intern_var(term);
                LinearExpr::var(var)
            }
        }
    }

    /// Standalone-simplex faithfulness audit, part 1 of 2 (#unbounded-oo):
    /// true iff EVERY asserted literal was parsed into an arithmetic
    /// constraint (a cached [`ParsedAtomInfo`] without unsupported
    /// sub-expressions).
    ///
    /// DPLL(T) lanes deliberately skip Boolean structure (or/and/xor/`=>`,
    /// Bool-sorted `=`/`distinct`, Bool ITEs, Bool vars) WITHOUT marking it
    /// unsupported, because the SAT solver owns it (#8452/#8003). That is
    /// wrong to rely on for a standalone caller that asserted the WHOLE
    /// formula: every skipped literal weakens the tableau into a RELAXATION
    /// of the formula. A relaxation is fine for verdicts that get per-model
    /// confirmation (finite optima are re-confirmed against the full solver),
    /// but `OptimizationResult::Unbounded` gets no such confirmation — a
    /// relaxation being unbounded proves nothing about the formula itself
    /// (#wrong-optimization-result). Callers trusting `Unbounded` must check
    /// this audit (and [`Self::all_interned_vars_are_declared_vars`]) first.
    pub fn all_asserted_atoms_parsed(&self) -> bool {
        self.asserted
            .iter()
            .all(|(t, &val)| match self.atom_cache.get(t) {
                Some(Some(info)) => !info.has_unsupported,
                // Not parsed as an arithmetic atom. The only harmless shape is
                // a constant Boolean asserted with satisfying polarity
                // (`(assert true)`); anything else (Boolean connectives, Bool
                // vars, foreign atoms) was skipped and weakened the polyhedron.
                _ => matches!(self.terms().get(*t),
                              TermData::Const(Constant::Bool(b)) if *b == val),
            })
    }

    /// Standalone-simplex faithfulness audit, part 2 of 2 (#unbounded-oo):
    /// true iff every interned tableau variable is backed by a DECLARED
    /// variable (`TermData::Var`).
    ///
    /// [`Self::parse_linear_expr`] over-approximates every opaque sub-term —
    /// nonlinear `*`, non-constant `/`, `abs`, `div`/`mod`, `to_int`, unknown
    /// functions, term ITEs, foreign terms — as a FRESH tableau variable, and
    /// a fresh variable is FREE: unbounded in both directions. Its only
    /// unsupported signal (`mark_current_atom_unsupported`) is a no-op when
    /// parsing an OBJECTIVE (no `current_parsing_atom`), so a bounded
    /// `(maximize (* x x))` parses as maximizing a free variable and the
    /// relaxed LP is trivially unbounded. Term ITEs are the sharpest atom-side
    /// case: their [`ParsedAtomInfo`] deliberately has
    /// `has_unsupported == false` (branch semantics arrive later via
    /// NeedModelEqualities link lemmas), but standalone mode suppresses those
    /// lemmas — only this uniform backing-term rule catches them, and any
    /// future opaque category, in both objectives and atoms. Slack variables
    /// and the optimizer's objective variable are not term-backed and are
    /// exempt (they are DEFINED by rows, not free).
    pub fn all_interned_vars_are_declared_vars(&self) -> bool {
        self.term_to_var
            .keys()
            .all(|t| matches!(self.terms().get(*t), TermData::Var(_, _)))
    }

    /// Parse an arithmetic atom and return (normalized_expr, is_le, is_strict)
    /// Normalized: expr <= 0 (for <=) or expr < 0 (for <)
    pub(crate) fn parse_atom(&mut self, term: TermId) -> Option<(LinearExpr, bool, bool)> {
        match self.terms().get(term) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let lhs = args[0];
                let rhs = args[1];

                match name.as_str() {
                    "<" => {
                        // lhs < rhs => lhs - rhs < 0
                        let mut expr = self.parse_linear_expr(lhs);
                        let rhs_expr = self.parse_linear_expr(rhs);
                        expr.add_scaled_rat(&rhs_expr, neg_one_rat());
                        Some((expr, true, true)) // is_le=true (upper bound), strict=true
                    }
                    "<=" => {
                        // lhs <= rhs => lhs - rhs <= 0
                        let mut expr = self.parse_linear_expr(lhs);
                        let rhs_expr = self.parse_linear_expr(rhs);
                        expr.add_scaled_rat(&rhs_expr, neg_one_rat());
                        Some((expr, true, false)) // is_le=true, strict=false
                    }
                    ">" => {
                        // lhs > rhs => lhs - rhs > 0 (is_le=false, strict=true)
                        // Preserves same expression direction as "<" (lhs - rhs) so that
                        // decomposed equalities share slack variables (#4919).
                        let mut expr = self.parse_linear_expr(lhs);
                        let rhs_expr = self.parse_linear_expr(rhs);
                        expr.add_scaled_rat(&rhs_expr, neg_one_rat());
                        Some((expr, false, true)) // is_le=false, strict=true
                    }
                    ">=" => {
                        // lhs >= rhs => lhs - rhs >= 0 (is_le=false, strict=false)
                        // Preserves same expression direction as "<=" (lhs - rhs) so that
                        // decomposed equalities share slack variables (#4919).
                        let mut expr = self.parse_linear_expr(lhs);
                        let rhs_expr = self.parse_linear_expr(rhs);
                        expr.add_scaled_rat(&rhs_expr, neg_one_rat());
                        Some((expr, false, false)) // is_le=false, strict=false
                    }
                    "=" => {
                        // Bool-sort equality (e.g., (= x_48 (not x_40))) is a Boolean
                        // connective (iff), not an arithmetic predicate. Return None so
                        // the Tseitin/DPLL layer handles it. Parsing Bool args through
                        // parse_linear_expr would hit the catch-all branch and mark the
                        // atom unsupported, converting SAT→Unknown (#4919).
                        if self.terms().sort(lhs) == &Sort::Bool {
                            return None;
                        }
                        // Equality: handle as both <= and >= in check
                        let mut expr = self.parse_linear_expr(lhs);
                        let rhs_expr = self.parse_linear_expr(rhs);
                        expr.add_scaled_rat(&rhs_expr, neg_one_rat());
                        Some((expr, true, false)) // For equality, we'll handle specially
                    }
                    "distinct" => {
                        // Bool-sort distinct is a Boolean connective (xor), not arithmetic.
                        if self.terms().sort(lhs) == &Sort::Bool {
                            return None;
                        }
                        // Distinct: same expression as equality, but with inverted semantics
                        // (distinct a b) with value=true means a != b (disequality)
                        // (distinct a b) with value=false means a = b (equality)
                        let mut expr = self.parse_linear_expr(lhs);
                        let rhs_expr = self.parse_linear_expr(rhs);
                        expr.add_scaled_rat(&rhs_expr, neg_one_rat());
                        Some((expr, true, false)) // Handled specially in check()
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}
