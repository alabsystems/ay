// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assumption-based solving for check-sat-assuming.
//!
//! Contains `solve_with_assumptions_for_theory()` and the `run_dpll_with_models!`
//! helper macro. These implement the generic check-sat-assuming engine that takes
//! (assertions, assumptions, theory_kind) and returns SolveResult with optional
//! UNSAT core extraction.

mod array_preprocess;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermId, Tseitin};
use ay_dt::DtSolver;
use ay_euf::EufSolver;
use ay_lia::LiaModel;
use ay_lra::LraSolver;
use ay_nia::NiaSolver;
use ay_nra::NraSolver;
use ay_sat::{AssumeResult, Literal as SatLiteral, SatResult};
use ay_strings::{StringModel, StringSolver};

use super::mod_div_elim::{contains_int_mod_div_by_constant, eliminate_int_mod_div_by_constant};
use super::Executor;
use crate::combined_solvers::combiner::TheoryCombiner;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::logic_detection::TheoryKind;
use crate::{DpllT, PropositionalTheory};

impl Executor {
    /// Solve with assertions and separate assumptions using SAT assumption-based solving.
    ///
    /// This method uses the SAT solver's assumption machinery to:
    /// - Encode assertions as normal clauses
    /// - Pass assumptions as SAT assumptions (temporary unit clauses)
    /// - Extract minimal UNSAT core when UNSAT
    ///
    /// The core is stored in `last_assumption_core` for `get_unsat_assumptions`.
    pub(in crate::executor) fn solve_with_assumptions_for_theory(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
        theory_kind: TheoryKind,
    ) -> Result<SolveResult> {
        use ay_core::TermData;

        // Guard: return Unknown for unsupported Seq operations (#5985).
        if theory_kind == TheoryKind::Seq && self.assertions_contain_unsupported_seq_ops() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        // BV theories use their own unified pipeline with dedicated Tseitin,
        // bitblasting, and assumption handling (#5276 Step 3).
        //
        // The `assertions` parameter may contain extra axioms (e.g., DT selector
        // axioms from the DtUfbv/DtAufbv callers) beyond `self.ctx.assertions`.
        // Temporarily extend ctx.assertions so solve_bv_core sees the full set.
        if matches!(
            theory_kind,
            TheoryKind::Bv | TheoryKind::ArrayBv | TheoryKind::UfBv | TheoryKind::AufBv
        ) {
            use super::theories::bv::BvSolveConfig;
            let config = match theory_kind {
                TheoryKind::Bv => BvSolveConfig::qf_bv(),
                TheoryKind::ArrayBv => BvSolveConfig::qf_abv(),
                TheoryKind::UfBv => BvSolveConfig::qf_ufbv(),
                TheoryKind::AufBv => BvSolveConfig::qf_aufbv(),
                _ => unreachable!(),
            };

            // Add any extra assertions (e.g., DT axioms) not already in ctx.assertions
            let base_assertions_exact = self.ctx.assertions.clone();
            let base_set: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
            for &a in assertions {
                if !base_set.contains(&a) {
                    self.ctx.assertions.push(a);
                }
            }

            // Include assumption terms as extra roots for array axiom
            // generation so assumption-only store/select get axioms (#6736).
            let has_array_assumptions =
                matches!(theory_kind, TheoryKind::ArrayBv | TheoryKind::AufBv);
            let result = if has_array_assumptions && !assumptions.is_empty() {
                self.solve_bv_core_with_assumption_roots(config, assumptions, assumptions)
            } else {
                self.solve_bv_core(config, assumptions)
            };

            // Restore the exact prefix: array/BV preprocessing may rewrite
            // existing assertions without changing their length.
            self.ctx.assertions = base_assertions_exact;
            return result;
        }

        // Preprocess assertions (ITE lifting, etc.)
        let needs_ite_lifting = matches!(
            theory_kind,
            TheoryKind::Euf | TheoryKind::Lra | TheoryKind::UfLra | TheoryKind::AufLra
        );

        let mut preprocessed_assertions: Vec<TermId> = if needs_ite_lifting {
            self.ctx.terms.lift_arithmetic_ite_all(assertions)
        } else {
            assertions.to_vec()
        };

        if theory_kind == TheoryKind::Dt {
            let base: HashSet<TermId> = preprocessed_assertions.iter().copied().collect();
            preprocessed_assertions.extend(self.dt_selector_axioms(&base));
        }

        // Preprocess assumptions (ITE lifting) BEFORE creating Tseitin
        // Store (preprocessed, original) pairs for later core mapping
        let preprocessed_assumptions: Vec<(TermId, TermId)> = if needs_ite_lifting {
            assumptions
                .iter()
                .map(|&a| (self.ctx.terms.lift_arithmetic_ite(a), a))
                .collect()
        } else {
            assumptions.iter().map(|&a| (a, a)).collect()
        };

        // Mod/div elimination for LIA-family theories (#1614) is handled in
        // solve_auf_lia_with_assumptions / solve_lira_with_assumptions, not here.
        let needs_mod_div_elim = false;
        let (preprocessed_assertions, preprocessed_assumptions) = if needs_mod_div_elim {
            let assert_len = preprocessed_assertions.len();
            let mut combined =
                Vec::with_capacity(preprocessed_assertions.len() + preprocessed_assumptions.len());
            combined.extend(preprocessed_assertions.iter().copied());
            combined.extend(preprocessed_assumptions.iter().map(|(t, _)| *t));

            if !contains_int_mod_div_by_constant(&self.ctx.terms, &combined) {
                (preprocessed_assertions, preprocessed_assumptions)
            } else {
                let mod_elim = eliminate_int_mod_div_by_constant(&mut self.ctx.terms, &combined);
                let mut rewritten = mod_elim.rewritten;
                let rewritten_assumptions = rewritten.split_off(assert_len);
                let rewritten_assertions = rewritten;

                let mut final_assertions = mod_elim.constraints;
                final_assertions.extend(rewritten_assertions);

                let final_assumptions: Vec<(TermId, TermId)> = rewritten_assumptions
                    .into_iter()
                    .zip(preprocessed_assumptions)
                    .map(|(rewritten, (_pre, original))| (rewritten, original))
                    .collect();

                (final_assertions, final_assumptions)
            }
        } else {
            (preprocessed_assertions, preprocessed_assumptions)
        };

        // Eager array axioms for theories involving arrays (#4304, #6736).
        // Include assumption terms in the axiom generation root set so
        // assumption-only array operations get proper axioms.
        let has_arrays = matches!(
            theory_kind,
            TheoryKind::ArrayEuf | TheoryKind::AufLra | TheoryKind::ArrayBv | TheoryKind::AufBv
        );
        let mut preprocessed_assertions = preprocessed_assertions;
        if has_arrays {
            preprocessed_assertions = self.prepare_assumption_array_assertions(
                preprocessed_assertions,
                &preprocessed_assumptions,
                theory_kind,
            );
        }

        // Purify compound Boolean arguments to uninterpreted functions: replace
        // `f((and ...))` with `f(p)` + `(= p (and ...))` for a fresh Bool proxy
        // `p`. Without this, EUF cannot congruence-close over UF applications
        // whose Bool argument is a compound term, yielding false-SAT on QF_UF /
        // QF_UFLIA (B-method CLEARSY) benchmarks. Equisatisfiable; a no-op when
        // there are no such arguments.
        // #boolarg-orphan: see the field doc — the rewritten applications must
        // stay resolvable to the twin the solve actually pinned.
        self.bool_arg_orphan_index = crate::executor::purify_bool_args::purify_bool_args(
            &mut self.ctx.terms,
            &mut preprocessed_assertions,
        );

        // Nelson-Oppen purification of opaque Int-sorted UF applications inside
        // arithmetic (e.g. `(__euclid!div a b)` in `(* b div)`): replace each
        // with a fresh Int variable `v` + `(= v u)` so LRA/NIA can register it
        // as a first-class arithmetic variable and share it across the N-O
        // interface. Without this, a shared (dis)equality over such an opaque
        // operand never resolves and a satisfiable formula stalls to Unknown.
        // Equisatisfiable; a no-op when there are no such operands.
        crate::executor::purify_int_uf_arith::purify_int_uf_arith(
            &mut self.ctx.terms,
            &mut preprocessed_assertions,
        );

        // Congruence exposure for CONSTANT-divisor `mod`/`div` under an
        // uninterpreted function (#G2-uflia-mod-in-uf-congruence): name each shared
        // `(mod x k)`/`(div x k)` (constant `k`) that sits as a UF argument with ONE
        // proxy `v` + `(= v u)`, rewriting all occurrences, so `(f (mod x k))` and
        // `(= (mod x k) c)` become congruence-linked `f(v)`/`(= v c)`.
        // Equisatisfiable; a no-op when no constant-divisor mod/div sits under a UF.
        // Mirrors the check-sat path.
        crate::executor::purify_int_uf_arith::purify_mod_div_uf_args(
            &mut self.ctx.terms,
            &mut preprocessed_assertions,
        );

        // Rewrite const-array reads through a ground `V = const-array(c)`
        // equality: replace each syntactic `select(V, idx)` with `c`. Without
        // this, a read of a variable that is only tied to a constant array by a
        // separate ground assertion stays opaque to LRA/LIA, so arithmetic that
        // consumes it (set-length ite-defs) is left unconstrained and a genuine
        // counterexample stalls to Unknown. Equisatisfiable
        // (`select(const-array(c), idx) = c` is valid under `V = const-array(c)`);
        // a no-op when there is no such ground equality with a matching read.
        crate::executor::rewrite_const_array_reads::rewrite_const_array_reads(
            &mut self.ctx.terms,
            &mut preprocessed_assertions,
        );

        // Create the Tseitin transformation with the same proof annotations as
        // the plain check-sat pipelines. Assumption solving still installs the
        // generated definitional clauses as ORIGINAL SAT clauses; without the
        // parallel annotations, a conflict against one of those clauses (the
        // smallest example is an assumed literal `false`, whose `¬false`
        // clause is justified by Alethe `false`) reaches reconstruction with
        // no exact authority and the public UNSAT is downgraded to
        // ProofTrusted.
        let proof_enabled = self.produce_proofs_enabled();
        let mut tseitin = if proof_enabled {
            Tseitin::new_with_proofs(&self.ctx.terms)
        } else {
            Tseitin::new(&self.ctx.terms)
        };

        // Encode each assertion and add as unit clause using the incremental API
        for &assertion in &preprocessed_assertions {
            tseitin.assert_term(assertion);
        }

        // Encode assumptions to get SAT literals (but don't add as unit clauses)
        let mut sat_assumptions: Vec<SatLiteral> = Vec::with_capacity(assumptions.len());
        let mut assumption_to_term: Vec<(SatLiteral, TermId)> =
            Vec::with_capacity(assumptions.len());

        for (preprocessed_assumption, original_assumption) in preprocessed_assumptions {
            // Handle negation: (not x) should use the negated literal for x
            let (base_term, positive) = match self.ctx.terms.get(preprocessed_assumption) {
                TermData::Not(inner) => (*inner, false),
                _ => (preprocessed_assumption, true),
            };

            // Encode the base term to get its CNF variable (doesn't add unit clause)
            let cnf_lit = tseitin.encode(base_term, true);

            // Convert CNF literal to SAT literal, respecting polarity
            let sat_var = ay_sat::Variable::new(cnf_lit.unsigned_abs() - 1);
            let sat_lit = if (cnf_lit > 0) == positive {
                SatLiteral::positive(sat_var)
            } else {
                SatLiteral::negative(sat_var)
            };

            sat_assumptions.push(sat_lit);
            // Store mapping to ORIGINAL assumption for core extraction
            assumption_to_term.push((sat_lit, original_assumption));
        }

        // Get clauses and mappings from Tseitin context
        let clauses = tseitin.all_clauses().to_vec();
        let proof_annotations = tseitin.proof_annotations().map(<[_]>::to_vec);
        let num_vars = tseitin.num_vars();

        // Build TseitinResult for DpllT
        let result = ay_core::TseitinResult::new(
            clauses,
            tseitin.term_to_var().clone(),
            tseitin.var_to_term().clone(),
            0, // Not used when we manually add unit clauses
            num_vars,
        )
        .with_parallel_proof_annotations(proof_annotations);

        // Build negations map for proof tracking if needed
        let negations: HashMap<TermId, TermId> = if proof_enabled {
            result
                .var_to_term
                .values()
                .map(|&term| (term, self.ctx.terms.mk_not(term)))
                .collect()
        } else {
            HashMap::default()
        };

        // #8123: Pre-generate datatype tautology literals (constructor
        // disjointness + tester evaluation) so the DpllT conflict verifier can
        // confirm genuine constructor-clash conflicts (`x = Ok(a) AND x = Err(b)`)
        // in a fresh EUF solver instead of reporting them SAT and degrading the
        // solve to Unknown. These are true in every model, so they are sound to
        // assert in the verifier. Generated here while `&mut self.ctx.terms` is
        // available (the DpllT built below borrows it immutably); only for
        // datatype-bearing problems to avoid scanning the store otherwise.
        let dt_verification_axioms: Vec<ay_core::TheoryLit> =
            if matches!(theory_kind, TheoryKind::Dt) {
                let dt_ctors: std::collections::HashMap<String, Vec<String>> = self
                    .ctx
                    .datatype_iter()
                    .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
                    .collect();
                crate::verification::build_datatype_tautology_axioms(&mut self.ctx.terms, &dt_ctors)
            } else {
                Vec::new()
            };

        // #AUFLIA-support: the ground-instance support literals threaded to the
        // DpllT conflict verifier, FILTERED to roots that are CURRENTLY in
        // `ctx.assertions`. Membership makes the soundness airtight independent
        // of any cross-check-sat staleness: a root present in the current
        // assertion set is a current top-level assertion, hence true in every
        // model of the current problem. Empty (and skips the scan) for
        // quantifier-free problems, keeping the path byte-identical.
        let ematching_support_axioms: Vec<ay_core::TheoryLit> =
            if self.active_support_axioms.is_empty() {
                Vec::new()
            } else {
                let asserted: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
                self.active_support_axioms
                    .iter()
                    .filter(|lit| asserted.contains(&lit.term))
                    .copied()
                    .collect()
            };

        // Record assume steps for assertions in the proof tracker.
        // The check-sat path (e.g., solve_lra) does this in each
        // theory-specific solver, but check-sat-assuming routes here,
        // so we must add them to ensure the proof has the required
        // (assume ...) steps for the th_resolution chain.
        if proof_enabled {
            let theory_name = match theory_kind {
                TheoryKind::Propositional => "SAT",
                TheoryKind::Euf => "EUF",
                TheoryKind::ArrayEuf => "Arrays",
                TheoryKind::Lra | TheoryKind::UfLra | TheoryKind::AufLra => "LRA",
                TheoryKind::Nia => "NIA",
                TheoryKind::Nra => "NRA",
                TheoryKind::Bv | TheoryKind::ArrayBv | TheoryKind::UfBv | TheoryKind::AufBv => "BV",
                TheoryKind::Dt => "DT",
                TheoryKind::Strings => "Strings",
                TheoryKind::Seq => "Seq",
            };
            self.proof_tracker.set_theory(theory_name);
            for (idx, &assertion) in assertions.iter().enumerate() {
                let _ = self
                    .proof_tracker
                    .add_assumption(assertion, Some(format!("h{idx}")));
            }
            for (idx, (_, assumption)) in assumption_to_term.iter().enumerate() {
                let _ = self
                    .proof_tracker
                    .add_assumption(*assumption, Some(format!("ha{idx}")));
            }
        }

        // Helper macro to run solver and extract theory models (#1160)
        // Returns (result, Option<LiaModel>, Option<LraModel>, Option<EufModel>,
        //          Option<ArrayModel>, Option<StringModel>, sat_unknown_reason)
        //
        // The @solve arm factors out the common create-solve-trace pattern.
        // Each variant arm handles theory-specific model extraction.
        macro_rules! run_dpll_with_models {
            // Internal: create DpllT, solve, save clause trace on UNSAT (#4176)
            (@solve $dpll:ident, $res:ident, $sat_reason:ident, $theory:expr) => {
                let mut $dpll = if proof_enabled {
                    DpllT::from_tseitin_with_proof(&self.ctx.terms, &result, $theory)
                } else {
                    DpllT::from_tseitin(&self.ctx.terms, &result, $theory)
                };
                $dpll.set_proof_bookkeeping_budget(self.search_proof_bookkeeping_budget());
                self.apply_random_seed_to_dpll(&mut $dpll);
                self.apply_progress_to_dpll(&mut $dpll);
                // #8123: hand the datatype tautology literals to the conflict
                // verifier (no-op clone for non-DT theories: vector is empty).
                $dpll.set_dt_verification_axioms(dt_verification_axioms.clone());
                // #AUFLIA-support: hand the ground instances of unconditionally-
                // asserted Foralls (accumulated by this check-sat's quantifier
                // refinement, filtered to still-asserted roots) to the conflict
                // verifier, combined at read time with the dt tautologies. Empty
                // (no-op clone) for quantifier-free problems, so the verification
                // path stays byte-identical.
                $dpll.set_ematching_support_axioms(ematching_support_axioms.clone());
                $dpll.set_max_learned_clauses(self.learned_clause_limit);
                // Thread the executor's solve controls (interrupt flag +
                // wall-clock deadline from `:timeout`/`set_solve_controls`)
                // into the DPLL(T) instance. Without this the refinement loop
                // ran the extension CDCL entry with `should_stop = || false`,
                // making a non-converging solve unkillable from the outside.
                $dpll.set_solve_controls(self.solve_interrupt.clone(), self.solve_deadline.get());
                // Deterministic resource budgets (#8749 `:rlimit` +
                // #ground-determinism defaults).
                {
                    let _sat = $dpll.sat_solver_mut();
                    let _budget = crate::pipeline_fns::effective_conflict_allowance(
                        self.resource_limit,
                        self.ground_budget_enabled,
                    )
                    .map(|n| _sat.num_conflicts().saturating_add(n));
                    _sat.set_conflict_budget(_budget);
                    let _dec_budget =
                        crate::pipeline_fns::effective_decision_allowance(self.decision_limit, self.ground_budget_enabled)
                            .map(|n| _sat.num_decisions().saturating_add(n));
                    _sat.set_decision_budget(_dec_budget);
                }
                if let Some(seed) = self.random_seed {
                    $dpll.sat_solver_mut().set_random_seed(seed);
                }
                let $res = if proof_enabled {
                    $dpll.solve_with_assumptions_and_proof_tracking(
                        &sat_assumptions,
                        &mut self.proof_tracker,
                        &negations,
                    )?
                } else {
                    $dpll.solve_with_assumptions(&sat_assumptions)?
                };
                let $sat_reason = if matches!($res, AssumeResult::Unknown) {
                    $dpll.sat_unknown_reason()
                } else {
                    None
                };
                // Save clause trace for UNSAT proof reconstruction (#4176).
                // Without this, build_unsat_proof() falls back to :rule hole
                // because last_clause_trace is None.
                if proof_enabled && matches!($res, AssumeResult::Unsat(..)) {
                    self.last_clause_trace = $dpll.take_clause_trace();
                    self.last_var_to_term = Some(
                        result.var_to_term.iter().map(|(&v, &t)| (v - 1, t)).collect(),
                    );
                    self.last_negations = Some(negations.clone());
                    // Exact, index-aligned authority for every Tseitin clause
                    // loaded into this SAT instance. The strict checker
                    // independently validates each annotation's rule and
                    // source shape; missing/forged entries therefore continue
                    // to fail closed.
                    self.last_clausification_proofs = result.proof_annotations.clone();
                    self.last_original_clause_theory_proofs = None;
                }
            };
            ($theory:expr, extract_lia) => {{
                run_dpll_with_models!(@solve dpll, res, sat_unknown_reason, $theory);
                let lia_model = if matches!(res, AssumeResult::Sat(_)) {
                    dpll.theory_solver()
                        .extract_model()
                        .map(|m| LiaModel { values: m.values })
                } else {
                    None
                };
                (res, lia_model, None, None, None, None, sat_unknown_reason)
            }};
            ($theory:expr, extract_lra) => {{
                run_dpll_with_models!(@solve dpll, res, sat_unknown_reason, $theory);
                let lra_model = if matches!(res, AssumeResult::Sat(_)) {
                    Some(dpll.theory_solver().extract_model())
                } else {
                    None
                };
                (res, None, lra_model, None, None, None, sat_unknown_reason)
            }};
            ($theory:expr, extract_euf_lra) => {{
                run_dpll_with_models!(@solve dpll, res, sat_unknown_reason, $theory);
                let (euf_model, lra_model) = if matches!(res, AssumeResult::Sat(_)) {
                    let (euf, lra) = dpll.theory_solver_mut().extract_euf_lra_models();
                    (Some(euf), Some(lra))
                } else {
                    (None, None)
                };
                (
                    res,
                    None,
                    lra_model,
                    euf_model,
                    None,
                    None,
                    sat_unknown_reason,
                )
            }};
            ($theory:expr, extract_auf_lra) => {{
                run_dpll_with_models!(@solve dpll, res, sat_unknown_reason, $theory);
                let (euf_model, array_model, lra_model) = if matches!(res, AssumeResult::Sat(_)) {
                    let (euf, arr, lra) = dpll.theory_solver_mut().extract_all_models_auflra();
                    (Some(euf), Some(arr), Some(lra))
                } else {
                    (None, None, None)
                };
                (
                    res,
                    None,
                    lra_model,
                    euf_model,
                    array_model,
                    None,
                    sat_unknown_reason,
                )
            }};
            ($theory:expr, extract_euf) => {{
                run_dpll_with_models!(@solve dpll, res, sat_unknown_reason, $theory);
                let euf_model = if matches!(res, AssumeResult::Sat(_)) {
                    Some(dpll.theory_solver_mut().extract_model())
                } else {
                    None
                };
                (res, None, None, euf_model, None, None, sat_unknown_reason)
            }};
            ($theory:expr, extract_array_euf) => {{
                run_dpll_with_models!(@solve dpll, res, sat_unknown_reason, $theory);
                let (euf_model, array_model) = if matches!(res, AssumeResult::Sat(_)) {
                    let (euf, arr) = dpll.theory_solver_mut().extract_euf_array_models();
                    (Some(euf), Some(arr))
                } else {
                    (None, None)
                };
                (
                    res,
                    None,
                    None,
                    euf_model,
                    array_model,
                    None,
                    sat_unknown_reason,
                )
            }};
            ($theory:expr, extract_strings) => {{
                run_dpll_with_models!(@solve dpll, res, sat_unknown_reason, $theory);
                let string_model: Option<StringModel> = if matches!(res, AssumeResult::Sat(_)) {
                    Some(dpll.theory_solver().extract_model())
                } else {
                    None
                };
                (
                    res,
                    None,
                    None,
                    None,
                    None,
                    string_model,
                    sat_unknown_reason,
                )
            }};
            ($theory:expr, no_extract) => {{
                run_dpll_with_models!(@solve dpll, res, sat_unknown_reason, $theory);
                (res, None, None, None, None, None, sat_unknown_reason)
            }};
        }

        // Create the appropriate theory solver and run with assumptions
        // Each theory extracts its relevant models (#1160)
        let (
            solve_result,
            lia_model,
            lra_model,
            euf_model,
            array_model,
            string_model,
            sat_unknown_reason,
        ) = match theory_kind {
            TheoryKind::Propositional => run_dpll_with_models!(PropositionalTheory, no_extract),
            TheoryKind::Euf => {
                run_dpll_with_models!(EufSolver::new(&self.ctx.terms), extract_euf)
            }
            TheoryKind::ArrayEuf => {
                run_dpll_with_models!(
                    {
                        let mut tc = TheoryCombiner::array_euf(&self.ctx.terms);
                        tc.set_interrupt(self.solve_interrupt.clone());
                        tc.set_deadline(self.solve_deadline.get());
                        // Enable the D0 datatype clash/acyclicity final-check
                        // pass for datatype-bearing problems (no-op otherwise).
                        let dt_info: Vec<(String, Vec<String>)> = self
                            .ctx
                            .datatype_iter()
                            .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
                            .collect();
                        tc.register_datatypes(&dt_info);
                        tc
                    },
                    extract_array_euf
                )
            }
            TheoryKind::Lra => {
                run_dpll_with_models!(LraSolver::new(&self.ctx.terms), extract_lra)
            }
            TheoryKind::Nia => {
                run_dpll_with_models!(NiaSolver::new(&self.ctx.terms), extract_lia)
            }
            TheoryKind::Nra => {
                run_dpll_with_models!(NraSolver::new(&self.ctx.terms), extract_lra)
            }
            TheoryKind::UfLra => {
                run_dpll_with_models!(
                    {
                        let mut tc = TheoryCombiner::uf_lra(&self.ctx.terms);
                        tc.set_interrupt(self.solve_interrupt.clone());
                        tc.set_deadline(self.solve_deadline.get());
                        // Enable the D0 datatype clash/acyclicity final-check
                        // pass for datatype-bearing problems (no-op otherwise;
                        // stage-4 review F1).
                        let dt_info: Vec<(String, Vec<String>)> = self
                            .ctx
                            .datatype_iter()
                            .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
                            .collect();
                        tc.register_datatypes(&dt_info);
                        tc
                    },
                    extract_euf_lra
                )
            }
            TheoryKind::AufLra => {
                run_dpll_with_models!(
                    {
                        let mut tc = TheoryCombiner::auf_lra(&self.ctx.terms);
                        tc.set_interrupt(self.solve_interrupt.clone());
                        tc.set_deadline(self.solve_deadline.get());
                        // Enable the D0 datatype clash/acyclicity final-check
                        // pass for datatype-bearing problems (no-op otherwise;
                        // stage-4 review F1).
                        let dt_info: Vec<(String, Vec<String>)> = self
                            .ctx
                            .datatype_iter()
                            .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
                            .collect();
                        tc.register_datatypes(&dt_info);
                        tc
                    },
                    extract_auf_lra
                )
            }
            TheoryKind::Strings => {
                // Keep assumptions-based string solving aligned with
                // solve_strings()/solve_strings_lia(): endpoint-empty
                // inferences require a registered empty-string term even
                // when the formula contains no explicit "" literal.
                let empty_id = self.ctx.terms.mk_string(String::new());
                let mut solver = StringSolver::new(&self.ctx.terms);
                solver.set_empty_string_id(empty_id);
                run_dpll_with_models!(solver, extract_strings)
            }
            TheoryKind::Seq => {
                run_dpll_with_models!(ay_seq::SeqSolver::new(&self.ctx.terms), no_extract)
            }
            // BV theories: handled by early return to solve_bv_core above (#5276 Step 3)
            TheoryKind::Bv | TheoryKind::ArrayBv | TheoryKind::UfBv | TheoryKind::AufBv => {
                unreachable!("BV theories handled by early return to solve_bv_core above")
            }
            TheoryKind::Dt => {
                // Create DT solver with reference to term store and register datatypes
                let mut dt_solver = DtSolver::new(&self.ctx.terms);
                for (dt_name, constructors) in self.ctx.datatype_iter() {
                    dt_solver.register_datatype(dt_name, constructors);
                }
                run_dpll_with_models!(dt_solver, no_extract)
            }
        };

        // Process result and extract assumption core
        match solve_result {
            AssumeResult::Sat(_model)
                if self.revoke_provisional_sat_if_finite_array_incomplete(true) =>
            {
                Ok(SolveResult::Unknown)
            }
            AssumeResult::Sat(model) => {
                self.last_assumption_core = None;
                self.solve_and_store_model_full(
                    SatResult::Sat(model),
                    &result,
                    euf_model,
                    array_model,
                    lra_model,
                    lia_model,
                    None,
                    None,
                    string_model,
                    None,
                )
            }
            AssumeResult::Unsat(core_lits, _) => {
                // Map SAT literals back to TermIds
                // Match by variable AND polarity to handle cases like (a (not a))
                let core_terms: Vec<TermId> = core_lits
                    .iter()
                    .filter_map(|&lit| {
                        // Find the assumption term that corresponds to this literal
                        assumption_to_term
                            .iter()
                            .find(|(sat_lit, _)| {
                                // Match by variable AND polarity
                                sat_lit.variable() == lit.variable()
                                    && sat_lit.is_positive() == lit.is_positive()
                            })
                            .map(|(_, term)| *term)
                    })
                    .collect();

                // Assumption core subset contract (#4642): every core term must
                // be a member of the original assumption set.
                debug_assert!(
                    core_terms.iter().all(|ct| assumptions.contains(ct)),
                    "BUG: assumption core contains term not in original assumptions"
                );

                self.last_assumption_core = Some(core_terms);
                self.solve_and_store_model(
                    SatResult::Unsat(ay_sat::ProofCertificate::empty()),
                    &result,
                    None,
                    None,
                )
            }
            AssumeResult::Unknown => {
                self.last_assumption_core = None;
                Self::record_sat_unknown_reason(&mut self.last_unknown_reason, sat_unknown_reason);
                if self.last_unknown_reason.is_none() {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                }
                self.last_result = Some(SolveResult::Unknown);
                Ok(SolveResult::Unknown)
            }
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }
}
