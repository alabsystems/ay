// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause application methods for `DpllT`: split atoms, bound refinements,
//! theory lemmas, and string lemma clauses.
//!
//! These methods translate theory-level requests (splits, lemmas, model
//! equalities) into SAT-level clauses and variable registrations.
//! Extracted from `lib.rs` as part of #6860 module-split work.

use ay_core::{
    term::{Constant, Symbol, TermData},
    TermId, TheoryLit, TheorySolver,
};
use ay_sat::{Literal, Variable};

use crate::proof_tracker;
use crate::DpllT;

impl<T: TheorySolver> DpllT<'_, T> {
    /// Generate and add incremental bound ordering axioms for a newly-created
    /// atom (#4919). Connects the atom to existing bounds on the same variable
    /// via nearest-neighbor transitivity clauses, enabling BCP-level propagation.
    fn add_incremental_bound_axioms(&mut self, atom: TermId) {
        // #8319: AY_NO_BOUND_AXIOMS disables incremental axiom generation too.
        if crate::theory_debug_flags::no_bound_axioms() {
            return;
        }
        let axiom_terms = self.theory.generate_incremental_bound_axioms(atom);
        for (t1, p1, t2, p2) in &axiom_terms {
            if let (Some(&v1), Some(&v2)) = (self.term_to_var.get(t1), self.term_to_var.get(t2)) {
                let l1 = if *p1 {
                    Literal::positive(Variable::new(v1))
                } else {
                    Literal::negative(Variable::new(v1))
                };
                let l2 = if *p2 {
                    Literal::positive(Variable::new(v2))
                } else {
                    Literal::negative(Variable::new(v2))
                };
                self.sat.add_clause(vec![l1, l2]);
            }
        }
    }

    /// Apply a split by adding the split atoms and splitting clause.
    ///
    /// Call this after receiving `SolveStepResult::NeedSplit` and creating
    /// the split atoms (x <= floor and x >= ceil).
    ///
    /// If the atoms were already registered (e.g., from a previous iteration),
    /// this reuses the existing SAT variable mappings.
    pub fn apply_split(&mut self, le_atom: TermId, ge_atom: TermId) {
        self.apply_split_with_hint(le_atom, ge_atom, None);
    }

    /// Apply a split with a hint about which branch to try first.
    ///
    /// # Arguments
    /// * `le_atom` - The atom for x <= floor
    /// * `ge_atom` - The atom for x >= ceil
    /// * `prefer_ceil` - If Some(true), prefer ceil branch first; if Some(false), prefer floor;
    ///   if None, no preference (use default SAT heuristics)
    ///
    /// When splitting on a variable with fractional value, the solver should try the
    /// closer integer first. For value 3.7 (frac > 0.5), prefer ceil (4); for value 3.2
    /// (frac < 0.5), prefer floor (3). This reduces unnecessary backtracking.
    pub fn apply_split_with_hint(
        &mut self,
        le_atom: TermId,
        ge_atom: TermId,
        prefer_ceil: Option<bool>,
    ) {
        // Check if atoms are already mapped (reuse from previous iteration)
        let le_var = if let Some(&var_idx) = self.term_to_var.get(&le_atom) {
            Variable::new(var_idx)
        } else {
            // Allocate new SAT variable and register the mapping
            let var = self.sat.new_var();
            self.register_theory_atom(le_atom, var.id());
            var
        };

        let ge_var = if let Some(&var_idx) = self.term_to_var.get(&ge_atom) {
            Variable::new(var_idx)
        } else {
            // Allocate new SAT variable and register the mapping
            let var = self.sat.new_var();
            self.register_theory_atom(ge_atom, var.id());
            var
        };

        // Set phase hints if provided
        // The split clause is: (le_var) OR (ge_var) - at least one must be true
        // If we prefer ceil, set ge_var to true (try x >= ceil first)
        // If we prefer floor, set le_var to true (try x <= floor first)
        if let Some(prefer_ceil) = prefer_ceil {
            if prefer_ceil {
                // Prefer ceil: set ge_var=true, le_var=false
                self.sat.set_var_phase(ge_var, true);
                self.sat.set_var_phase(le_var, false);
            } else {
                // Prefer floor: set le_var=true, ge_var=false
                self.sat.set_var_phase(le_var, true);
                self.sat.set_var_phase(ge_var, false);
            }
        }

        // Generate incremental bound axioms for the new split atoms (#4919).
        // Without these, split-introduced atoms miss transitivity clauses
        // against existing bounds, forcing the theory solver to re-derive them.
        self.add_incremental_bound_axioms(le_atom);
        self.add_incremental_bound_axioms(ge_atom);

        // Add the splitting clause: (var <= floor) OR (var >= ceil)
        let split_clause = vec![Literal::positive(le_var), Literal::positive(ge_var)];
        self.sat.add_clause(split_clause);
    }

    /// Apply a disequality split by adding atoms for `x < c` and `x > c`.
    ///
    /// Call this after receiving `SolveStepResult::NeedDisequalitySplit` and creating
    /// the split atoms (x < excluded_value and x > excluded_value).
    ///
    /// When `disequality_term` is Some, creates a conditional clause:
    /// - For `distinct` terms (is_distinct=true): `~term OR (x < c) OR (x > c)`
    ///   Forces split when distinct=true (disequality holds)
    /// - For `=` terms (is_distinct=false): `term OR (x < c) OR (x > c)`
    ///   Forces split when equality=false (disequality holds)
    ///
    /// When `disequality_term` is None, this adds the unconditional clause:
    ///   `(x < c) OR (x > c)`
    /// Note: This can cause soundness issues when used in iterative solving!
    pub fn apply_disequality_split(
        &mut self,
        lt_atom: TermId,
        gt_atom: TermId,
        disequality_term: Option<TermId>,
        is_distinct: bool,
    ) {
        // Check if atoms are already mapped (reuse from previous iteration)
        let lt_var = if let Some(&var_idx) = self.term_to_var.get(&lt_atom) {
            Variable::new(var_idx)
        } else {
            // Allocate new SAT variable and register the mapping
            let var = self.sat.new_var();
            self.register_theory_atom(lt_atom, var.id());
            var
        };

        let gt_var = if let Some(&var_idx) = self.term_to_var.get(&gt_atom) {
            Variable::new(var_idx)
        } else {
            // Allocate new SAT variable and register the mapping
            let var = self.sat.new_var();
            self.register_theory_atom(gt_atom, var.id());
            var
        };

        // Generate incremental bound axioms for the new disequality split
        // atoms (#4919). Connects lt/gt atoms to existing bounds on the same
        // variable, enabling BCP propagation of bound ordering implications.
        self.add_incremental_bound_axioms(lt_atom);
        self.add_incremental_bound_axioms(gt_atom);

        // Build the splitting clause
        if let Some(diseq) = disequality_term {
            if let Some(diseq_lit) = self.disequality_split_guard_literal(diseq, is_distinct) {
                // Polarity depends on term type:
                // - distinct terms (is_distinct=true): use negative literal
                //   Clause: ~distinct OR (x < c) OR (x > c)
                //   Forces split when distinct=true (disequality holds)
                // - equality terms (is_distinct=false): use positive literal
                //   Clause: (= x c) OR (x < c) OR (x > c)
                //   Forces split when equality=false (disequality holds)
                let split_clause = vec![
                    diseq_lit,
                    Literal::positive(lt_var),
                    Literal::positive(gt_var),
                ];
                self.sat.add_clause(split_clause);
            } else {
                // Disequality term not mapped - fall back to unconditional
                let split_clause = vec![Literal::positive(lt_var), Literal::positive(gt_var)];
                self.sat.add_clause(split_clause);
            }
        } else {
            // Unconditional split: (var < c) OR (var > c)
            let split_clause = vec![Literal::positive(lt_var), Literal::positive(gt_var)];
            self.sat.add_clause(split_clause);
        }
    }

    fn disequality_split_guard_literal(
        &self,
        diseq_term: TermId,
        is_distinct: bool,
    ) -> Option<Literal> {
        let terms = self.terms?;
        if let Some(&diseq_var) = self.term_to_var.get(&diseq_term) {
            let var = Variable::new(diseq_var);
            return Some(if term_is_not_app(terms, diseq_term) || is_distinct {
                Literal::negative(var)
            } else {
                Literal::positive(var)
            });
        }

        let inner = match terms.get(diseq_term) {
            TermData::Not(inner) => Some(*inner),
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => Some(args[0]),
            _ => None,
        }?;
        self.term_to_var
            .get(&inner)
            .map(|&inner_var| Literal::positive(Variable::new(inner_var)))
    }

    /// Apply an expression split by adding atoms for `E < F` and `E > F`.
    ///
    /// Call this after receiving `SolveStepResult::NeedExpressionSplit` and creating
    /// the split atoms.
    ///
    /// Uses the same conditional-clause encoding as [`Self::apply_disequality_split`]:
    /// - For `distinct` terms (is_distinct=true): `~term OR (E < F) OR (E > F)`
    /// - For `=` terms (is_distinct=false): `term OR (E < F) OR (E > F)`
    pub fn apply_expression_split(
        &mut self,
        lt_atom: TermId,
        gt_atom: TermId,
        disequality_term: TermId,
        is_distinct: bool,
    ) {
        self.apply_disequality_split(lt_atom, gt_atom, Some(disequality_term), is_distinct);
    }

    /// Apply a theory-implied bound refinement clause `reason -> bound_atom`.
    ///
    /// Returns `false` when at least one reason literal cannot be mapped to the
    /// SAT layer. In that case the caller should treat the refinement as
    /// unavailable rather than adding a too-strong clause with missing premises.
    pub fn apply_bound_refinement(&mut self, bound_atom: TermId, reason: &[TheoryLit]) -> bool {
        let bound_var = if let Some(&var_idx) = self.term_to_var.get(&bound_atom) {
            Variable::new(var_idx)
        } else {
            let var = self.sat.new_var();
            self.register_theory_atom(bound_atom, var.id());
            var
        };
        // Split-loop pipelines rebuild DpllT from the original Tseitin result on
        // every iteration. Replay must re-register refinement atoms with the
        // fresh theory instance or LRA will keep re-discovering the same
        // missing atoms and never observe its own refinements.
        self.theory.register_atom(bound_atom);

        // Generate bound ordering axioms for the new atom against existing atoms
        // on the same variable (#4919). Without this, refined atoms miss the
        // transitivity clauses that enable BCP-level bound propagation.
        self.add_incremental_bound_axioms(bound_atom);

        let mut clause = Vec::with_capacity(reason.len() + 1);
        for reason_lit in reason {
            let Some(sat_lit) = self.term_to_literal(reason_lit.term, !reason_lit.value) else {
                tracing::warn!(
                    term = ?reason_lit.term,
                    value = reason_lit.value,
                    "Skipping bound refinement with unmapped reason literal"
                );
                return false;
            };
            clause.push(sat_lit);
        }

        self.sat.set_var_phase(bound_var, true);
        clause.push(Literal::positive(bound_var));
        self.sat.add_clause(clause);
        true
    }

    /// Apply a model equality by creating `(= lhs rhs)` as a SAT variable
    /// with phase hint `true` and aggressive VSIDS priority (#4906).
    ///
    /// Used for Nelson-Oppen theory combination with non-convex theories.
    /// The equality becomes a retractable CDCL decision: if it leads to conflict,
    /// the solver backtracks past the decision and tries `(= lhs rhs) = false`.
    ///
    /// The VSIDS activity is bumped aggressively (20x) to ensure the variable
    /// is decided promptly. Without this, model equality variables — which are
    /// not in any clause — may never be selected by VSIDS, causing the solver
    /// to return Unknown on satisfiable AUFLIA/AUFLRA formulas.
    ///
    /// Reference: Z3 `assume_eq` + `try_true_first` (smt_context.cpp:4576-4632).
    /// Z3 internalizes the equality into clauses (le/ge decomposition) and
    /// propagates `try_true_first` to auxiliary atoms. We approximate this by
    /// bumping activity high enough to guarantee prompt decision.
    pub fn apply_model_equality(&mut self, eq_atom: TermId) {
        let eq_var = if let Some(&var_idx) = self.term_to_var.get(&eq_atom) {
            Variable::new(var_idx)
        } else {
            let var = self.sat.new_var();
            self.register_theory_atom(eq_atom, var.id());
            var
        };
        // Bias the SAT solver to decide this equality as true.
        self.sat.set_var_phase(eq_var, true);
        // Bump activity aggressively so VSIDS prioritizes this variable.
        // register_theory_atom already gives one bump; add more to ensure
        // the variable rises above conflict-bumped variables. Without this,
        // model equality variables sit in the VSIDS heap indefinitely because
        // they are never bumped during conflict analysis (no clause participation).
        for _ in 0..20 {
            self.sat.bump_variable_activity(eq_var);
        }
    }

    /// Lower top-level disjunctions in a string lemma clause into clause literals.
    ///
    /// `mk_implies(a, b)` canonicalizes to `(or (not a) b)`. If we keep that `or`
    /// term opaque, the clause becomes unit instead of binary. Flattening preserves
    /// clause semantics and avoids creating a SAT variable for the `or` wrapper.
    fn lower_string_lemma_atoms(&self, atoms: &[TermId]) -> Vec<TermId> {
        let Some(terms) = self.terms else {
            return atoms.to_vec();
        };

        let mut lowered = Vec::with_capacity(atoms.len());
        let mut pending: Vec<TermId> = atoms.iter().rev().copied().collect();

        while let Some(atom) = pending.pop() {
            match terms.get(atom) {
                TermData::App(Symbol::Named(name), args) if name == "or" && !args.is_empty() => {
                    pending.extend(args.iter().rev().copied());
                }
                _ => lowered.push(atom),
            }
        }

        lowered
    }

    fn theory_clause_to_sat_literals(&mut self, clause: &[TheoryLit]) -> Vec<Literal> {
        clause
            .iter()
            .map(|lit| {
                let var = if let Some(&var_idx) = self.term_to_var.get(&lit.term) {
                    Variable::new(var_idx)
                } else {
                    let var = self.sat.new_var();
                    self.register_theory_atom(lit.term, var.id());
                    var
                };
                if lit.value {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                }
            })
            .collect()
    }

    /// Apply a permanent theory lemma clause to the SAT solver.
    pub fn apply_theory_lemma(&mut self, clause: &[TheoryLit]) {
        let lits = self.theory_clause_to_sat_literals(clause);
        self.sat.add_clause(lits);
        self.theory.note_applied_theory_lemma(clause);
    }

    /// Apply a string lemma clause: a disjunction of term atoms.
    ///
    /// Each atom is registered as a theory atom (if not already). The resulting
    /// disjunction is added to the SAT solver. When the SAT solver assigns one
    /// of the atoms to true, the DPLL(T) layer routes it back to the theory
    /// solver via `assert_literal()`.
    pub fn apply_string_lemma(&mut self, atoms: &[TermId]) {
        let lowered_atoms = self.lower_string_lemma_atoms(atoms);
        let lits: Vec<Literal> = lowered_atoms
            .iter()
            .map(|&atom| {
                // Detect negated atoms: NOT(inner) should use the negative literal
                // of inner's SAT variable, not create a separate variable.
                // Bug #3375: without this, LengthSplit [eq, NOT(eq)] creates two
                // independent SAT variables, so the SAT solver can't propagate the
                // decision back to the string solver correctly.
                let (base_atom, positive) = if let Some(terms) = self.terms {
                    match terms.get(atom) {
                        TermData::Not(inner) => (*inner, false),
                        _ => (atom, true),
                    }
                } else {
                    (atom, true)
                };
                let var = if let Some(&var_idx) = self.term_to_var.get(&base_atom) {
                    Variable::new(var_idx)
                } else {
                    let var = self.sat.new_var();
                    self.register_theory_atom(base_atom, var.id());
                    var
                };
                if positive {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                }
            })
            .collect();
        // Polarity hint for LengthSplit: if the clause is a tautological split
        // [eq, NOT(eq)] (same variable, opposite polarities), prefer the positive
        // branch. CVC5 does this via preferPhase in term_registry.cpp.
        //
        // For LengthSplit, preferring len(x)=len(y) leads to N_UNIFY (x=y),
        // which is more productive than the disequal branch (VarSplit stalls
        // because fresh-solver-per-iteration loses skolem constraints).
        if lits.len() == 2 {
            let (v0, v1) = (lits[0].variable(), lits[1].variable());
            if v0 == v1 && lits[0].is_positive() != lits[1].is_positive() {
                self.sat.set_var_phase(v0, true);
            } else if v0 != v1 && lits[0].is_positive() && lits[1].is_positive() {
                // Polarity hint for ConstSplit (#3429): clause [x="", x=str.++(c,k)]
                // has two positive atoms with different variables. Detect which atom
                // is the "x = empty" escape literal and prefer the decomposition.
                // Without this, the SAT solver may not decide the decomposition,
                // causing the string theory to re-request the same ConstSplit.
                // CVC5 uses preferPhase(concat_eq, true) in core_solver.cpp.
                if let Some(terms) = self.terms {
                    let empty_idx = lowered_atoms.iter().position(|&atom| {
                        if let TermData::App(Symbol::Named(name), args) = terms.get(atom) {
                            name == "="
                                && args.len() == 2
                                && (matches!(
                                    terms.get(args[0]),
                                    TermData::Const(Constant::String(s)) if s.is_empty()
                                ) || matches!(
                                    terms.get(args[1]),
                                    TermData::Const(Constant::String(s)) if s.is_empty()
                                ))
                        } else {
                            false
                        }
                    });
                    if let Some(ei) = empty_idx {
                        let decomp_idx = 1 - ei;
                        // Prefer the decomposition (true) over the empty escape (false).
                        self.sat.set_var_phase(lits[decomp_idx].variable(), true);
                        self.sat.set_var_phase(lits[ei].variable(), false);
                    }
                }
            }
        }
        // Polarity hint for VarSplit (#3429): clause [len(x)=len(y), x=str.++(y,k), y=str.++(x,k)]
        // has 3 positive atoms. Prefer decomposition branches (true) over the
        // len-equality escape (false). Without this hint, the SAT solver may satisfy
        // the clause via the escape literal, preventing the string theory from seeing
        // the variable decomposition. CVC5 uses preferPhase(concat_eq, true).
        if lits.len() == 3 {
            if let Some(terms) = self.terms {
                let len_eq_idx = atoms.iter().position(|&atom| {
                    if let TermData::App(Symbol::Named(name), args) = terms.get(atom) {
                        if name == "=" && args.len() == 2 {
                            let l_is_len = matches!(
                                terms.get(args[0]),
                                TermData::App(Symbol::Named(n), _) if n == "str.len"
                            );
                            let r_is_len = matches!(
                                terms.get(args[1]),
                                TermData::App(Symbol::Named(n), _) if n == "str.len"
                            );
                            l_is_len && r_is_len
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                });
                if let Some(lei) = len_eq_idx {
                    // Prefer len(x)=len(y) TRUE (the equal-length escape).
                    // When lengths are equal, N_UNIFY infers x=y which is the most
                    // productive path (immediately resolves the NF comparison).
                    // Preferring decomposition branches (x=str.++(y,k)) leads to
                    // endpoint-empty cascades and containment cycle conflicts that
                    // waste SAT solver effort. CVC5 uses areEqual(lenx,leny) check
                    // before VarSplit; AY achieves the same effect by biasing SAT.
                    self.sat.set_var_phase(lits[lei].variable(), true);
                    // Leave decomposition branches at default phase (false).
                }
            }
        }
        self.sat.add_clause(lits);
    }

    /// Apply a string lemma clause and record it as a proof premise.
    ///
    /// Keeps SAT clause insertion and proof-premise tracking aligned when the
    /// executor runs in proof mode.
    pub(crate) fn apply_string_lemma_with_proof_tracking(
        &mut self,
        atoms: &[TermId],
        tracker: &mut proof_tracker::ProofTracker,
    ) {
        self.apply_string_lemma(atoms);
        let _ = tracker.add_theory_lemma(atoms.to_vec());
    }
}

fn term_is_not_app(terms: &ay_core::TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Not(_) => true,
        TermData::App(sym, args) => sym.name() == "not" && args.len() == 1,
        _ => false,
    }
}
