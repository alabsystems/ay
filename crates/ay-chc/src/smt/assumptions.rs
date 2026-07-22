// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assumption-based solving with UNSAT core extraction.

use super::context::SmtContext;
use super::model_verify::{
    collect_theory_atoms_into, is_theory_atom, verify_sat_model_conjunction_strict_with_mod_retry,
};
use super::types::{
    DiseqGuardKind, FarkasConflict, ModelVerifyResult, Partition, SmtResult, SmtValue, UnsatCore,
    UnsatCoreDiagnostics,
};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{FarkasAnnotation, Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::Rational64;
use num_traits::{One, ToPrimitive};

pub(super) fn new_assumption_sat_solver(num_vars: usize) -> ay_sat::Solver {
    let mut sat = ay_sat::Solver::new(num_vars);
    // Assumption-mode CHC solving is a one-shot SAT query with temporary guards.
    // Preprocessing is disabled because it can distort assumption-sensitive clauses.
    sat.set_preprocess_enabled(false);
    // #8199: Disable ALL inprocessing for assumption-mode solvers. Previous code
    // (#8160) only disabled destructive techniques (BVE, BCE, etc.) via
    // disable_destructive_inprocessing(), leaving subsumption, probe, backbone,
    // HTR, transred, gate, congruence, reorder, and CCE enabled. While the
    // assumption CDCL loop in ay-sat does not call run_restart_inprocessing()
    // during search, non-destructive techniques could still fire if the
    // empty-assumption fast path falls through to solve_no_assumptions().
    // For one-shot CHC queries, inprocessing is pure overhead — assumption
    // variables must remain unmodified, and the solver is discarded after each
    // query. disable_all_inprocessing() is the correct defense-in-depth
    // approach, replacing the partial disable_destructive_inprocessing() +
    // set_vivify_enabled(false) combination.
    sat.disable_all_inprocessing();
    sat
}

impl SmtContext {
    pub fn check_sat_with_assumption_conjuncts(
        &mut self,
        background: &[ChcExpr],
        assumptions: &[ChcExpr],
    ) -> SmtResult {
        use ay_core::{TheoryResult, TheorySolver, Tseitin};
        use ay_lia::LiaSolver;

        // Track consecutive budget exceedances (#2472).
        if self.conversion_budget_exceeded {
            self.conversion_budget_strikes = self.conversion_budget_strikes.saturating_add(1);
        } else {
            self.conversion_budget_strikes = 0;
        }

        // Reset per-check conversion budget (#2771).
        self.reset_conversion_budget();

        // Short-circuit on repeated budget exhaustion (#2472).
        if self.conversion_budget_strikes >= super::context::MAX_CONVERSION_STRIKES {
            return SmtResult::Unknown;
        }

        fn is_assumed_iuc_proxy_var(expr: &ChcExpr, assumed_proxies: &FxHashSet<&str>) -> bool {
            match expr {
                ChcExpr::Var(v) => assumed_proxies.contains(v.name.as_str()),
                _ => false,
            }
        }

        fn collect_iuc_proxy_implication_consequent_terms(
            ctx: &mut SmtContext,
            expr: &ChcExpr,
            assumed_proxies: &FxHashSet<&str>,
            out: &mut Vec<TermId>,
        ) -> bool {
            match expr {
                ChcExpr::Op(ChcOp::Implies, args)
                    if args.len() == 2
                        && is_assumed_iuc_proxy_var(args[0].as_ref(), assumed_proxies) =>
                {
                    out.push(ctx.convert_expr(args[1].as_ref()));
                    true
                }
                ChcExpr::Op(ChcOp::Or, args) => {
                    let saw_guard = args.iter().any(|arg| match arg.as_ref() {
                        ChcExpr::Op(ChcOp::Not, not_args) if not_args.len() == 1 => {
                            is_assumed_iuc_proxy_var(not_args[0].as_ref(), assumed_proxies)
                        }
                        _ => false,
                    });
                    if !saw_guard {
                        return false;
                    }

                    let mut saw_consequent = false;
                    for arg in args {
                        let is_guard = match arg.as_ref() {
                            ChcExpr::Op(ChcOp::Not, not_args) if not_args.len() == 1 => {
                                is_assumed_iuc_proxy_var(not_args[0].as_ref(), assumed_proxies)
                            }
                            _ => false,
                        };
                        if is_guard {
                            continue;
                        }
                        saw_consequent = true;
                        out.push(ctx.convert_expr(arg.as_ref()));
                    }
                    saw_consequent
                }
                _ => false,
            }
        }

        if assumptions.is_empty() {
            let bg = background
                .iter()
                .cloned()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));
            return self.check_sat(&bg);
        }

        let debug = crate::debug_chc_smt_enabled();

        let assumed_iuc_proxies: FxHashSet<&str> = assumptions
            .iter()
            .filter_map(|assumption| match assumption {
                ChcExpr::Var(v)
                    if v.sort == ChcSort::Bool && v.name.starts_with("__iuc_proxy_") =>
                {
                    Some(v.name.as_str())
                }
                _ => None,
            })
            .collect();

        // Collect var=const equalities with transitive var=var closure (#2445).
        // Uses union-find to resolve chains like A=B, B=C, C=5 → {A:5, B:5, C:5}.
        // TPA needs populated models for MBP midpoint extraction. propagate_constants()
        // eliminates these variables, so we must capture them first.
        let mut propagated_equalities: FxHashMap<String, i128> = FxHashMap::default();
        // #5877: Collect BV var=const equalities for BV-native PDR mode.
        let mut propagated_bv_equalities: FxHashMap<String, (u128, u32)> = FxHashMap::default();
        let all_exprs: Vec<&ChcExpr> = background.iter().chain(assumptions.iter()).collect();
        let contradiction =
            Self::collect_int_equalities_with_closure(&all_exprs, &mut propagated_equalities);
        if contradiction {
            // Transitive equality closure found conflicting constants (e.g., A=B, A=1, B=2).
            // This is UNSAT — return immediately with a conservative core.
            return SmtResult::UnsatWithCore(UnsatCore {
                conjuncts: assumptions.to_vec(),
                ..Default::default()
            });
        }

        // Build substitution list from collected equalities to propagate across expressions.
        // e.g., if we have "x = 5" and "y = x + 1", substitute x=5 into the second to get y=6.
        let subst: Vec<(ChcVar, ChcExpr)> = propagated_equalities
            .iter()
            .map(|(name, val)| (ChcVar::new(name, ChcSort::Int), ChcExpr::int(*val)))
            .collect();

        // Collect theory atoms from the A (background) and B (assumptions) partitions for
        // per-literal origin tagging on Farkas conflicts (#982).
        //
        // Special case: IUC introduces proxy implications in the background:
        //   (¬proxy ∨ assumption_body)
        // where `proxy` is assumed as a B-conjunct. We attribute theory atoms from the
        // implication body to partition B (not A) to avoid A-partition leakage (#1030).
        let mut a_partition_terms: Vec<TermId> = Vec::with_capacity(background.len());
        let mut b_partition_terms: Vec<TermId> = Vec::new();

        let mut bg_terms: Vec<TermId> = Vec::with_capacity(background.len());
        for (idx, b) in background.iter().enumerate() {
            let namespace = format!("bg{idx}");
            // Apply cross-expression substitution before preprocessing
            let substituted = if subst.is_empty() {
                b.clone()
            } else {
                b.substitute(&subst)
            };
            // Use preprocess_incremental_assumption which skips propagate_constants()
            // (#2913). Per-expression constant propagation eliminates variables from
            // individual expressions, but those variables may still be referenced in
            // other background/assumption expressions. This causes the theory solver
            // to treat the eliminated variable as unconstrained, producing invalid
            // models. Cross-expression propagation via `subst` already handles the
            // var=const case; var=var equalities are preserved for the theory solver.
            let normalized = Self::preprocess_incremental_assumption(&substituted, &namespace);
            Self::collect_int_var_const_equalities(&normalized, &mut propagated_equalities);
            Self::collect_bv_var_const_equalities(&normalized, &mut propagated_bv_equalities);

            let is_proxy_implication = collect_iuc_proxy_implication_consequent_terms(
                self,
                &normalized,
                &assumed_iuc_proxies,
                &mut b_partition_terms,
            );

            let term = self.convert_expr(&normalized);
            bg_terms.push(term);
            if !is_proxy_implication {
                a_partition_terms.push(term);
            }
        }

        let mut assumption_terms: Vec<(ChcExpr, TermId)> = Vec::with_capacity(assumptions.len());
        for (idx, a) in assumptions.iter().enumerate() {
            let namespace = format!("a{idx}");
            // Apply cross-expression substitution before preprocessing
            let substituted = if subst.is_empty() {
                a.clone()
            } else {
                a.substitute(&subst)
            };
            // Use preprocess_incremental_assumption — see background loop comment (#2913)
            let normalized = Self::preprocess_incremental_assumption(&substituted, &namespace);
            Self::collect_int_var_const_equalities(&normalized, &mut propagated_equalities);
            Self::collect_bv_var_const_equalities(&normalized, &mut propagated_bv_equalities);
            match normalized {
                ChcExpr::Bool(true) => continue,
                ChcExpr::Bool(false) => {
                    return SmtResult::UnsatWithCore(UnsatCore {
                        conjuncts: vec![a.clone()],
                        ..Default::default()
                    });
                }
                _ => {
                    assumption_terms.push((a.clone(), self.convert_expr(&normalized)));
                }
            }
        }

        if assumption_terms.is_empty() {
            let bg = background
                .iter()
                .cloned()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));
            let result = self.check_sat(&bg);
            // When all assumptions simplified to `true` via constant propagation
            // (e.g., assumption `x = 5` → `5 = 5` → `true`), the propagated
            // equalities must be merged into the returned model so callers see
            // the correct variable bindings.
            if let SmtResult::Sat(mut model) = result {
                // Propagated equalities override solver-assigned values because
                // the solver only sees the substituted background (where the
                // variable may appear unconstrained) while the propagated value
                // is the binding from the original assumption equality.
                for (name, value) in &propagated_equalities {
                    model.insert(name.clone(), SmtValue::Int(*value));
                }
                for (name, (value, width)) in &propagated_bv_equalities {
                    model.insert(name.clone(), SmtValue::BitVec(*value, *width));
                }
                return SmtResult::Sat(model);
            }
            return result;
        }

        // Bail out if conversion budget was exceeded (#2771).
        if self.conversion_budget_exceeded {
            return SmtResult::Unknown;
        }

        // Collect theory atoms from the A (background) and B (assumptions) partitions for
        // per-literal origin tagging on Farkas conflicts (#982).
        let mut a_partition_atoms: FxHashSet<TermId> = FxHashSet::default();
        let mut b_partition_atoms: FxHashSet<TermId> = FxHashSet::default();
        collect_theory_atoms_into(
            &self.terms,
            a_partition_terms.iter().copied(),
            &mut a_partition_atoms,
        );
        collect_theory_atoms_into(
            &self.terms,
            assumption_terms.iter().map(|(_, t)| *t),
            &mut b_partition_atoms,
        );
        collect_theory_atoms_into(
            &self.terms,
            b_partition_terms.iter().copied(),
            &mut b_partition_atoms,
        );

        let mut tseitin = Tseitin::new(&self.terms);
        for term in bg_terms {
            let _ = tseitin.encode_and_assert(term);
        }

        const MAX_FARKAS_CONFLICTS: usize = 64;

        let mut sat_assumptions: Vec<ay_sat::Literal> =
            Vec::with_capacity(assumption_terms.len() + MAX_FARKAS_CONFLICTS);
        let mut assumption_map: FxHashMap<ay_sat::Literal, ChcExpr> = FxHashMap::default();
        for (a, term) in assumption_terms {
            let cnf_lit = tseitin.encode(term, true);
            let sat_lit = ay_sat::Literal::from_dimacs(cnf_lit);
            sat_assumptions.push(sat_lit);
            assumption_map.insert(sat_lit, a);
        }

        let mut sat = new_assumption_sat_solver(tseitin.num_vars() as usize);
        for clause in tseitin.all_clauses() {
            let lits: Vec<ay_sat::Literal> = clause
                .0
                .iter()
                .map(|&lit| ay_sat::Literal::from_dimacs(lit))
                .collect();
            sat.add_clause(lits);
        }

        let mut term_to_var = tseitin.term_to_var().clone();
        let mut var_to_term = tseitin.var_to_term().clone();
        let mut num_vars = tseitin.num_vars();

        let mut split_count: usize = 0;
        let max_splits: usize = 1_000_000; // #2472: uniform cap, per-variable cap handles runaway
                                           // Phase 3 Fix 4: model-equality encoding state (mirrors the main
                                           // theory loop; see term_growth.rs `apply_model_equalities`).
        let mut seen_model_eq_requests: FxHashSet<(TermId, TermId)> = FxHashSet::default();
        let mut model_eq_rounds: usize = 0;
        const MAX_MODEL_EQ_ROUNDS: usize = 20;
        let mut dt_iterations: usize = 0;
        let mut theory_unsat_count: usize = 0; // #2450: track Unsat (no Farkas) conflicts
        let mut theory_farkas_count: usize = 0; // #2450: track UnsatWithFarkas conflicts
        let mut theory_farkas_none_count: usize = 0; // #2450: UnsatWithFarkas but farkas=None
        let mut farkas_conflicts: Vec<FarkasConflict> = Vec::with_capacity(MAX_FARKAS_CONFLICTS);
        let mut farkas_assumption_to_conflict_idx: FxHashMap<ay_sat::Literal, usize> =
            FxHashMap::default();
        farkas_assumption_to_conflict_idx.reserve(MAX_FARKAS_CONFLICTS);

        // Track atoms introduced by DPLL(T) splitting. We distinguish:
        // - case_split_atoms: branch-and-bound NeedSplit atoms, classified as Partition::Split
        // - split_atom_partitions: disequality decomposition atoms (NeedDisequalitySplit,
        //   NeedExpressionSplit) that inherit A/B partition from their triggering guard atom
        // See the development design notes for rationale.
        let mut case_split_atoms: FxHashSet<TermId> = FxHashSet::default();
        let mut split_atom_partitions: FxHashMap<TermId, Partition> = FxHashMap::default();

        let get_partition = |term: TermId,
                             case_split_atoms: &FxHashSet<TermId>,
                             split_atom_partitions: &FxHashMap<TermId, Partition>|
         -> Partition {
            // Check case split atoms first - these are pure branch-and-bound splits
            if case_split_atoms.contains(&term) {
                return Partition::Split;
            }
            // Check disequality decomposition splits - these inherit partition from guard
            if let Some(&partition) = split_atom_partitions.get(&term) {
                return partition;
            }
            // Fall back to original A/B atom sets
            let in_a = a_partition_atoms.contains(&term);
            let in_b = b_partition_atoms.contains(&term);
            match (in_a, in_b) {
                (true, false) => Partition::A,
                (false, true) => Partition::B,
                _ => Partition::AB,
            }
        };

        // #5925: Detect Real-sorted theory atoms for LRA incompleteness guard.
        let has_real_theory_atoms = var_to_term.values().any(|&term_id| {
            if !is_theory_atom(&self.terms, term_id) {
                return false;
            }
            match self.terms.get(term_id) {
                TermData::App(_, args) => args
                    .iter()
                    .any(|&a| matches!(self.terms.sort(a), Sort::Real)),
                _ => false,
            }
        });

        loop {
            if TermStore::global_memory_exceeded() {
                if debug {
                    safe_eprintln!("[CHC-SMT] assumption-mode global term memory budget exceeded");
                }
                return SmtResult::Unknown;
            }
            // Per-engine term memory budget guard (#8600).
            if self.term_memory_exceeded() {
                if debug {
                    safe_eprintln!(
                        "[CHC-SMT] assumption-mode per-engine term memory budget exceeded"
                    );
                }
                return SmtResult::Unknown;
            }
            // #5925: DPLL(T) iteration cap for Real-sorted formulas.
            if has_real_theory_atoms && dt_iterations > 1000 {
                return SmtResult::Unknown;
            }
            dt_iterations += 1;
            if debug && dt_iterations.is_multiple_of(10_000) {
                safe_eprintln!(
                    "[CHC-SMT] assumption-mode DPLL(T) iteration {}",
                    dt_iterations
                );
            }

            let verified_assume = sat.solve_with_assumptions(&sat_assumptions);
            match verified_assume.result() {
                ay_sat::AssumeResult::Sat(model) => {
                    let mut lia = LiaSolver::new(&self.terms);
                    for (&var_idx, &term_id) in &var_to_term {
                        if !is_theory_atom(&self.terms, term_id) {
                            continue;
                        }
                        // KNOWN ISSUE (fail-safe, incomplete): this lane has NO
                        // BV bit-blasting. The comment this skip was copied
                        // with ("already encoded in SAT via bit-blasting",
                        // #5122) is true only for `check_sat`'s CNF pipeline
                        // (`attach_bv_bitblasting`); `check_sat_with_assumption_conjuncts`
                        // builds its own Tseitin CNF and never instantiates a
                        // BvSolver. BV atoms here are therefore FREE BOOLEANS:
                        // no bit semantics constrain them, and BV variable
                        // values only enter the model via the syntactic
                        // var=const propagation (`propagated_bv_equalities`).
                        // Any query whose satisfying model depends on real BV
                        // reasoning (e.g. `(= (bvadd acc 1) #xFF..F)` from
                        // model-checker-consumer PDR inductiveness queries) produces a model
                        // that fails the strict background+assumptions
                        // re-verification below and is demoted to Unknown —
                        // sound but incomplete (the "violates
                        // background+assumptions" WARN). Completing this lane
                        // means wiring the same persistent-cache bit-blast
                        // attach + BV model extraction that check_sat uses.
                        if Self::is_bv_theory_atom(&self.terms, term_id) {
                            continue;
                        }
                        // Skip array atoms — no array theory in CHC DPLL(T) (#6047).
                        if Self::is_array_theory_atom(&self.terms, term_id) {
                            continue;
                        }
                        let sat_var = ay_sat::Variable::new(var_idx - 1);
                        if let Some(value) = model.get(sat_var.index()) {
                            lia.assert_literal(term_id, *value);
                        }
                    }

                    match lia.check() {
                        TheoryResult::Sat => {
                            // Build model from LIA solver, SAT model (Bool), and propagated
                            // equalities as fallback (#1009, #2913).
                            //
                            // Priority: LIA model > LRA fallback > propagated equalities.
                            // LIA/LRA values are authoritative because the theory solver
                            // enforced all constraints it received. Propagated equalities
                            // are only needed for variables eliminated during preprocessing
                            // (e.g., var=const substitution turned `x = 5` into `true`,
                            // removing `x` from the formula). If the LIA solver still has
                            // a value for such a variable, prefer it — it accounts for
                            // interactions with other constraints that propagation missed.
                            let mut values = FxHashMap::default();

                            // First pass: extract from LIA model and SAT model (authoritative)
                            let lia_model = lia.extract_model();
                            for (qualified_name, &term_id) in &self.var_map {
                                // #6100: var_map keys are sort-qualified; emit
                                // original CHC names in the model.
                                let name = self.original_var_name(qualified_name);
                                match self.terms.sort(term_id) {
                                    Sort::Bool => {
                                        if let Some(&cnf_var) = term_to_var.get(&term_id) {
                                            let sat_var = ay_sat::Variable::new(cnf_var - 1);
                                            if let Some(value) = model.get(sat_var.index()) {
                                                values.insert(
                                                    name.to_owned(),
                                                    SmtValue::Bool(*value),
                                                );
                                            }
                                        }
                                    }
                                    Sort::Int => {
                                        if let Some(m) = &lia_model {
                                            if let Some(v) = m.values.get(&term_id) {
                                                // #3827: skip on overflow
                                                if let Some(i) = v.to_i128() {
                                                    values
                                                        .insert(name.to_owned(), SmtValue::Int(i));
                                                }
                                                continue;
                                            }
                                        }
                                        // Fallback: try LRA solver
                                        if let Some(v) = lia.lra_solver().get_value(term_id) {
                                            if v.denom().is_one() {
                                                // #3827: skip on overflow
                                                if let Some(i) = v.numer().to_i128() {
                                                    values
                                                        .insert(name.to_owned(), SmtValue::Int(i));
                                                }
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }

                            // Second pass: fill in propagated equalities for variables
                            // not present in the theory solver (eliminated by preprocessing)
                            for (name, value) in &propagated_equalities {
                                values.entry(name.clone()).or_insert(SmtValue::Int(*value));
                            }
                            // #5877: Fill in BV propagated equalities with proper type.
                            for (name, (value, width)) in &propagated_bv_equalities {
                                values
                                    .entry(name.clone())
                                    .or_insert(SmtValue::BitVec(*value, *width));
                            }

                            // #7380: Reverse-map namespaced model entries to un-namespaced base names.
                            use crate::smt::incremental::strip_namespace_suffix;
                            let mut extra_entries = Vec::new();
                            for (name, value) in &values {
                                if let Some(base) = strip_namespace_suffix(name) {
                                    if !values.contains_key(base) {
                                        extra_entries.push((base.to_owned(), value.clone()));
                                    }
                                }
                            }
                            for (name, value) in extra_entries {
                                values.insert(name, value);
                            }

                            let verify_result = verify_sat_model_conjunction_strict_with_mod_retry(
                                // Verify model against conjunction of background + assumptions.
                                background.iter().chain(assumptions.iter()),
                                &values,
                            );
                            if matches!(verify_result, ModelVerifyResult::Invalid) {
                                // The DPLL(T) + LIA solver found a model for the
                                // preprocessed formula that does not satisfy the
                                // original expressions. Return Unknown rather than
                                // crashing — soundness is preserved since we do not
                                // claim Sat for an invalid model. Consistent with
                                // check_sat.rs (#4729) and incremental.rs behavior.
                                tracing::warn!(
                                    "SAT model from check_sat_with_assumption_conjuncts violates background+assumptions; returning Unknown"
                                );
                                return SmtResult::Unknown;
                            }
                            if matches!(verify_result, ModelVerifyResult::Indeterminate) {
                                // #6047/#7016: When array/DT operations are present
                                // and model verification is indeterminate, degrade to
                                // Unknown. Without array/DT theory, the SAT model may
                                // violate axioms.
                                let has_array_ops =
                                    background.iter().any(ChcExpr::contains_array_ops)
                                        || assumptions.iter().any(ChcExpr::contains_array_ops);
                                let has_dt = background.iter().any(ChcExpr::contains_dt_ops)
                                    || assumptions.iter().any(ChcExpr::contains_dt_ops);
                                // #7380: Also check for mod auxiliary variables.
                                let has_mod_aux = background.iter().any(ChcExpr::has_mod_aux_vars)
                                    || assumptions.iter().any(ChcExpr::has_mod_aux_vars);
                                if has_array_ops || has_dt || has_mod_aux {
                                    tracing::debug!(
                                        "SAT model indeterminate with array/DT/mod ops in assumption solver; degrading to Unknown"
                                    );
                                    return SmtResult::Unknown;
                                }
                                // Indeterminate = evaluation incomplete (missing vars,
                                // predicates, etc.), not model wrong. Accept as Sat (#4712).
                                tracing::debug!(
                                    "SAT model verification indeterminate in check_sat_with_assumption_conjuncts; accepting as Sat"
                                );
                            }
                            return SmtResult::Sat(values);
                        }
                        TheoryResult::Unknown => return SmtResult::Unknown,
                        TheoryResult::Unsat(conflict) => {
                            theory_unsat_count += 1;
                            if conflict.is_empty() {
                                if crate::proof_interpolation::iuc_trace_enabled() {
                                    safe_eprintln!(
                                        "[IUC-SMT] returning plain UNSAT from TheoryResult::Unsat: empty conflict (dt_iters={}, theory_unsat={}, theory_farkas={}, theory_farkas_none={}, splits={})",
                                        dt_iterations,
                                        theory_unsat_count,
                                        theory_farkas_count,
                                        theory_farkas_none_count,
                                        split_count
                                    );
                                }
                                // #5925: LRA incompleteness guard
                                return if has_real_theory_atoms {
                                    SmtResult::Unknown
                                } else {
                                    SmtResult::Unsat
                                };
                            }
                            // Verify conflict literals match current SAT assignment
                            assert!(
                                conflict.iter().all(|lit| {
                                    term_to_var.get(&lit.term).is_none_or(|&cnf_var| {
                                        let sat_var = ay_sat::Variable::new(cnf_var - 1);
                                        model
                                            .get(sat_var.index())
                                            .is_none_or(|&v| v == lit.value)
                                    })
                                }),
                                "BUG: theory conflict literal contradicts SAT assignment (assumption solver)"
                            );
                            // Synthesize a Farkas conflict with uniform weights.
                            // The theory returned UNSAT without a Farkas certificate
                            // (e.g., from integer infeasibility: Diophantine, modular
                            // arithmetic, or GCD test). Uniform weights are a valid
                            // over-approximation — interpolation strategies will filter
                            // or adjust during constraint combination.
                            let conflict_terms: Vec<TermId> =
                                conflict.iter().map(|l| l.term).collect();
                            let polarities: Vec<bool> = conflict.iter().map(|l| l.value).collect();
                            let origins: Vec<Partition> = conflict_terms
                                .iter()
                                .map(|&t| {
                                    get_partition(t, &case_split_atoms, &split_atom_partitions)
                                })
                                .collect();
                            let synth_farkas =
                                FarkasAnnotation::new(vec![Rational64::from(1); conflict.len()]);
                            let mut conflict_idx: Option<usize> = None;
                            if farkas_conflicts.len() < MAX_FARKAS_CONFLICTS {
                                farkas_conflicts.push(FarkasConflict {
                                    conflict_terms: conflict_terms.clone(),
                                    polarities: polarities.clone(),
                                    farkas: synth_farkas,
                                    origins,
                                });
                                conflict_idx = Some(farkas_conflicts.len() - 1);
                            }
                            let mut clause: Vec<ay_sat::Literal> = conflict
                                .iter()
                                .filter_map(|lit| {
                                    term_to_var.get(&lit.term).map(|&cnf_var| {
                                        let sat_var = ay_sat::Variable::new(cnf_var - 1);
                                        if lit.value {
                                            ay_sat::Literal::negative(sat_var)
                                        } else {
                                            ay_sat::Literal::positive(sat_var)
                                        }
                                    })
                                })
                                .collect();
                            if clause.is_empty() {
                                if crate::proof_interpolation::iuc_trace_enabled() {
                                    safe_eprintln!(
                                        "[IUC-SMT] returning plain UNSAT from TheoryResult::Unsat: conflict literals unmapped to CNF (terms={}, dt_iters={}, theory_unsat={}, theory_farkas={}, theory_farkas_none={}, splits={})",
                                        conflict_terms.len(),
                                        dt_iterations,
                                        theory_unsat_count,
                                        theory_farkas_count,
                                        theory_farkas_none_count,
                                        split_count
                                    );
                                }
                                // #5925: LRA incompleteness guard
                                return if has_real_theory_atoms {
                                    SmtResult::Unknown
                                } else {
                                    SmtResult::Unsat
                                };
                            }
                            // Track with activation literal (same as UnsatWithFarkas)
                            if let Some(idx) = conflict_idx {
                                num_vars += 1;
                                sat.ensure_num_vars(num_vars as usize);
                                let act_var = ay_sat::Variable::new(num_vars - 1);
                                let act_assumption = ay_sat::Literal::negative(act_var);
                                sat_assumptions.push(act_assumption);
                                farkas_assumption_to_conflict_idx.insert(act_assumption, idx);
                                clause.push(ay_sat::Literal::positive(act_var));
                            }
                            sat.add_clause(clause);
                        }
                        TheoryResult::NeedSplit(split) => {
                            // Split value must be non-integral (branch-and-bound invariant)
                            debug_assert!(
                                !split.value.is_integer(),
                                "BUG: CHC-ASSUME NeedSplit value {} is integral (floor={}, ceil={})",
                                split.value,
                                split.floor,
                                split.ceil
                            );
                            debug_assert!(
                                split.floor < split.ceil,
                                "BUG: CHC-ASSUME NeedSplit floor {} >= ceil {}",
                                split.floor,
                                split.ceil
                            );

                            split_count += 1;
                            if split_count > max_splits {
                                return SmtResult::Unknown;
                            }

                            // Guard: mk_le/mk_ge require Int or Real sort (#2941)
                            let var_sort = self.terms.sort(split.variable);
                            if !matches!(var_sort, Sort::Int | Sort::Real) {
                                return SmtResult::Unknown;
                            }

                            let floor_term = self.terms.mk_int(split.floor.clone());
                            let ceil_term = self.terms.mk_int(split.ceil.clone());
                            let le_atom = self.terms.mk_le(split.variable, floor_term);
                            let ge_atom = self.terms.mk_ge(split.variable, ceil_term);

                            // Track as case split atoms (branch-and-bound `NeedSplit`), classified as `Partition::Split`.
                            case_split_atoms.insert(le_atom);
                            case_split_atoms.insert(ge_atom);

                            let le_var = *term_to_var.entry(le_atom).or_insert_with(|| {
                                num_vars += 1;
                                var_to_term.insert(num_vars, le_atom);
                                num_vars
                            });
                            let ge_var = *term_to_var.entry(ge_atom).or_insert_with(|| {
                                num_vars += 1;
                                var_to_term.insert(num_vars, ge_atom);
                                num_vars
                            });

                            sat.ensure_num_vars(num_vars as usize);

                            let le_sat_var = ay_sat::Variable::new(le_var - 1);
                            let ge_sat_var = ay_sat::Variable::new(ge_var - 1);
                            sat.add_clause(vec![
                                ay_sat::Literal::positive(le_sat_var),
                                ay_sat::Literal::positive(ge_sat_var),
                            ]);
                            continue;
                        }
                        TheoryResult::NeedDisequalitySplit(split) => {
                            split_count += 1;
                            if split_count > max_splits {
                                return SmtResult::Unknown;
                            }

                            let var_sort = self.terms.sort(split.variable).clone();
                            let (left_atom, right_atom) =
                                if var_sort == Sort::Int && split.excluded_value.is_integer() {
                                    let excluded = split.excluded_value.numer().clone();
                                    let le_bound = self.terms.mk_int(&excluded - BigInt::from(1));
                                    let ge_bound = self.terms.mk_int(&excluded + BigInt::from(1));
                                    (
                                        self.terms.mk_le(split.variable, le_bound),
                                        self.terms.mk_ge(split.variable, ge_bound),
                                    )
                                } else if var_sort == Sort::Int {
                                    // Int variable with non-integer excluded value - same as above.
                                    // Convert strict inequalities to integer bounds via floor/ceil.
                                    let floor_val = split.excluded_value.floor().to_integer();
                                    let ceil_val = split.excluded_value.ceil().to_integer();
                                    let le_bound = self.terms.mk_int(floor_val);
                                    let ge_bound = self.terms.mk_int(ceil_val);
                                    (
                                        self.terms.mk_le(split.variable, le_bound),
                                        self.terms.mk_ge(split.variable, ge_bound),
                                    )
                                } else {
                                    // Real variable - use rational term directly
                                    let excluded_term =
                                        self.terms.mk_rational(split.excluded_value.clone());
                                    (
                                        self.terms.mk_lt(split.variable, excluded_term),
                                        self.terms.mk_gt(split.variable, excluded_term),
                                    )
                                };

                            // Find the guard atom and compute its partition to inherit
                            let guard_info = self.find_diseq_guard_atom(
                                split.variable,
                                &split.excluded_value,
                                model,
                                var_to_term.iter(),
                            );

                            // Inherit partition from the guard atom (the disequality that triggered
                            // this split). If no guard found, fall back to Partition::AB since the
                            // split atoms are solver-introduced but not pure case splits.
                            let inherited_partition =
                                guard_info
                                    .as_ref()
                                    .map_or(Partition::AB, |(guard_term, _)| {
                                        let in_a = a_partition_atoms.contains(guard_term);
                                        let in_b = b_partition_atoms.contains(guard_term);
                                        match (in_a, in_b) {
                                            (true, false) => Partition::A,
                                            (false, true) => Partition::B,
                                            _ => Partition::AB,
                                        }
                                    });

                            // Track split atoms with inherited partition for interpolation
                            split_atom_partitions.insert(left_atom, inherited_partition);
                            split_atom_partitions.insert(right_atom, inherited_partition);

                            let lt_var = *term_to_var.entry(left_atom).or_insert_with(|| {
                                num_vars += 1;
                                var_to_term.insert(num_vars, left_atom);
                                num_vars
                            });
                            let gt_var = *term_to_var.entry(right_atom).or_insert_with(|| {
                                num_vars += 1;
                                var_to_term.insert(num_vars, right_atom);
                                num_vars
                            });

                            sat.ensure_num_vars(num_vars as usize);

                            let lt_sat_var = ay_sat::Variable::new(lt_var - 1);
                            let gt_sat_var = ay_sat::Variable::new(gt_var - 1);
                            let guard_lit = guard_info.and_then(|(guard_term, kind)| {
                                term_to_var.get(&guard_term).copied().map(|cnf_var| {
                                    let sat_var = ay_sat::Variable::new(cnf_var - 1);
                                    match kind {
                                        DiseqGuardKind::Distinct => {
                                            ay_sat::Literal::negative(sat_var)
                                        }
                                        DiseqGuardKind::Eq => ay_sat::Literal::positive(sat_var),
                                    }
                                })
                            });
                            // Same pruning as in `check_sat`: if current bounds make one branch
                            // infeasible, force the other branch as a unit clause.
                            // i128-lockstep: exact excluded value (the previous
                            // saturating i64 conversion could force the wrong
                            // branch when a bound sat at i64::MAX); beyond-i128
                            // skips pruning entirely (fail-closed: no forcing).
                            let (can_lt, can_gt) = if let Some(excluded) = split
                                .excluded_value
                                .is_integer()
                                .then(|| split.excluded_value.numer().to_i128())
                                .flatten()
                            {
                                let (lb, ub) = self.infer_int_bounds_from_sat_model(
                                    split.variable,
                                    model,
                                    var_to_term.iter(),
                                );
                                let lt_threshold = excluded.checked_sub(1);
                                let gt_threshold = excluded.checked_add(1);

                                let can_lt =
                                    lt_threshold.is_some_and(|t| lb.is_none_or(|l| l <= t));
                                let can_gt =
                                    gt_threshold.is_some_and(|t| ub.is_none_or(|u| u >= t));
                                (can_lt, can_gt)
                            } else {
                                (true, true)
                            };

                            if !can_lt && !can_gt {
                                if let Some(g) = guard_lit {
                                    sat.add_clause(vec![g]);
                                    continue;
                                }
                            }
                            if !can_lt && can_gt {
                                if let Some(g) = guard_lit {
                                    sat.add_clause(vec![g, ay_sat::Literal::positive(gt_sat_var)]);
                                } else {
                                    sat.add_clause(vec![ay_sat::Literal::positive(gt_sat_var)]);
                                }
                            } else if !can_gt && can_lt {
                                if let Some(g) = guard_lit {
                                    sat.add_clause(vec![g, ay_sat::Literal::positive(lt_sat_var)]);
                                } else {
                                    sat.add_clause(vec![ay_sat::Literal::positive(lt_sat_var)]);
                                }
                            } else if let Some(g) = guard_lit {
                                sat.add_clause(vec![
                                    g,
                                    ay_sat::Literal::positive(lt_sat_var),
                                    ay_sat::Literal::positive(gt_sat_var),
                                ]);
                            } else {
                                sat.add_clause(vec![
                                    ay_sat::Literal::positive(lt_sat_var),
                                    ay_sat::Literal::positive(gt_sat_var),
                                ]);
                            }
                            continue;
                        }
                        TheoryResult::NeedExpressionSplit(split) => {
                            // Multi-variable disequality split: E != F
                            // Create atoms (E < F) OR (E > F)
                            split_count += 1;
                            if split_count > max_splits {
                                return SmtResult::Unknown;
                            }

                            // Extract LHS and RHS from the disequality term
                            let (lhs, rhs) = match self.terms.get(split.disequality_term) {
                                TermData::App(Symbol::Named(name), args)
                                    if args.len() == 2 && (name == "=" || name == "distinct") =>
                                {
                                    (args[0], args[1])
                                }
                                _ => return SmtResult::Unknown,
                            };

                            if !matches!(self.terms.sort(lhs), Sort::Int | Sort::Real)
                                || self.terms.sort(lhs) != self.terms.sort(rhs)
                            {
                                return SmtResult::Unknown;
                            }

                            // Create (E < F) and (E > F) atoms
                            let lt_atom = self.terms.mk_lt(lhs, rhs);
                            let gt_atom = self.terms.mk_gt(lhs, rhs);

                            // Inherit partition from the disequality term that triggered this split.
                            // Like NeedDisequalitySplit, we check if the guard term is in A/B partitions.
                            let guard_term = split.disequality_term;
                            let in_a = a_partition_atoms.contains(&guard_term);
                            let in_b = b_partition_atoms.contains(&guard_term);
                            let inherited_partition = match (in_a, in_b) {
                                (true, false) => Partition::A,
                                (false, true) => Partition::B,
                                _ => Partition::AB,
                            };

                            // Track split atoms with inherited partition for interpolation
                            split_atom_partitions.insert(lt_atom, inherited_partition);
                            split_atom_partitions.insert(gt_atom, inherited_partition);

                            // Allocate CNF variables
                            let lt_var = *term_to_var.entry(lt_atom).or_insert_with(|| {
                                num_vars += 1;
                                var_to_term.insert(num_vars, lt_atom);
                                num_vars
                            });
                            let gt_var = *term_to_var.entry(gt_atom).or_insert_with(|| {
                                num_vars += 1;
                                var_to_term.insert(num_vars, gt_atom);
                                num_vars
                            });

                            sat.ensure_num_vars(num_vars as usize);

                            let lt_sat_var = ay_sat::Variable::new(lt_var - 1);
                            let gt_sat_var = ay_sat::Variable::new(gt_var - 1);

                            // Add guarded splitting clause: ¬diseq ∨ (E < F) ∨ (E > F)
                            // This mirrors NeedDisequalitySplit's guarded encoding.
                            // The guard literal is the negation of the "distinct" or positive of "=".
                            let guard_lit = term_to_var.get(&guard_term).map(|&cnf_var| {
                                let sat_var = ay_sat::Variable::new(cnf_var - 1);
                                // If guard is (distinct E F), negate it to get ¬(distinct E F)
                                // If guard is (= E F), use positive to get (= E F)
                                // The disequality is asserted when distinct is true or = is false
                                match self.terms.get(guard_term) {
                                    TermData::App(Symbol::Named(name), _) if name == "distinct" => {
                                        ay_sat::Literal::negative(sat_var)
                                    }
                                    _ => ay_sat::Literal::positive(sat_var),
                                }
                            });

                            if let Some(g) = guard_lit {
                                sat.add_clause(vec![
                                    g,
                                    ay_sat::Literal::positive(lt_sat_var),
                                    ay_sat::Literal::positive(gt_sat_var),
                                ]);
                            } else {
                                // Fallback: unconditional split if guard not in CNF
                                sat.add_clause(vec![
                                    ay_sat::Literal::positive(lt_sat_var),
                                    ay_sat::Literal::positive(gt_sat_var),
                                ]);
                            }
                            continue;
                        }
                        TheoryResult::NeedStringLemma(_) => {
                            // String theory not supported in CHC; return Unknown to avoid
                            // spinning the DPLL(T) loop requesting the same lemma (#6091).
                            return SmtResult::Unknown;
                        }
                        TheoryResult::UnsatWithFarkas(conflict) => {
                            // #2450: count main-loop Farkas conflicts
                            if conflict.farkas.is_some() {
                                theory_farkas_count += 1;
                            } else {
                                theory_farkas_none_count += 1;
                            }
                            // If we have Farkas coefficients, preserve them for interpolation
                            if let Some(ref farkas) = conflict.farkas {
                                let conflict_terms: Vec<TermId> =
                                    conflict.literals.iter().map(|l| l.term).collect();
                                let polarities: Vec<bool> =
                                    conflict.literals.iter().map(|l| l.value).collect();
                                let origins: Vec<Partition> = conflict_terms
                                    .iter()
                                    .map(|&t| {
                                        get_partition(t, &case_split_atoms, &split_atom_partitions)
                                    })
                                    .collect();
                                let mut conflict_idx: Option<usize> = None;
                                if farkas_conflicts.len() < MAX_FARKAS_CONFLICTS {
                                    farkas_conflicts.push(FarkasConflict {
                                        conflict_terms: conflict_terms.clone(),
                                        polarities: polarities.clone(),
                                        farkas: farkas.clone(),
                                        origins: origins.clone(),
                                    });
                                    conflict_idx = Some(farkas_conflicts.len() - 1);
                                }
                                // Empty conflict = direct theory UNSAT
                                if conflict.literals.is_empty() {
                                    // #5925: LRA incompleteness guard
                                    return if has_real_theory_atoms {
                                        SmtResult::Unknown
                                    } else {
                                        SmtResult::UnsatWithFarkas(FarkasConflict {
                                            conflict_terms,
                                            polarities,
                                            farkas: farkas.clone(),
                                            origins,
                                        })
                                    };
                                }
                                // Non-empty conflict: check if blocking clause is empty
                                let mut clause: Vec<ay_sat::Literal> = conflict
                                    .literals
                                    .iter()
                                    .filter_map(|lit| {
                                        term_to_var.get(&lit.term).map(|&cnf_var| {
                                            let sat_var = ay_sat::Variable::new(cnf_var - 1);
                                            if lit.value {
                                                ay_sat::Literal::negative(sat_var)
                                            } else {
                                                ay_sat::Literal::positive(sat_var)
                                            }
                                        })
                                    })
                                    .collect();
                                if clause.is_empty() {
                                    // All conflict literals unmapped = direct theory UNSAT
                                    // #5925: LRA incompleteness guard
                                    return if has_real_theory_atoms {
                                        SmtResult::Unknown
                                    } else {
                                        SmtResult::UnsatWithFarkas(FarkasConflict {
                                            conflict_terms,
                                            polarities,
                                            farkas: farkas.clone(),
                                            origins,
                                        })
                                    };
                                }
                                if let Some(idx) = conflict_idx {
                                    // Clause-to-Farkas tracking (Corrected Phase 1, #1276):
                                    //
                                    // Guard each Farkas-derived blocking clause with an activation
                                    // literal `a_i` and assume ¬a_i. When SAT later reports UNSAT
                                    // under assumptions, the returned assumption core tells us which
                                    // Farkas clauses were actually needed. We then filter
                                    // `farkas_conflicts` to those relevant conflicts.
                                    //
                                    // Encoding: (a_i ∨ clause), assume ¬a_i.
                                    num_vars += 1;
                                    sat.ensure_num_vars(num_vars as usize);
                                    let act_var = ay_sat::Variable::new(num_vars - 1);
                                    let act_assumption = ay_sat::Literal::negative(act_var);
                                    sat_assumptions.push(act_assumption);
                                    farkas_assumption_to_conflict_idx.insert(act_assumption, idx);
                                    clause.push(ay_sat::Literal::positive(act_var));
                                }
                                sat.add_clause(clause);
                            } else {
                                // UnsatWithFarkas but farkas is None — synthesize uniform weights.
                                if conflict.literals.is_empty() {
                                    if crate::proof_interpolation::iuc_trace_enabled() {
                                        safe_eprintln!(
                                            "[IUC-SMT] returning plain UNSAT from TheoryResult::UnsatWithFarkas(None): empty literals (dt_iters={}, theory_unsat={}, theory_farkas={}, theory_farkas_none={}, splits={})",
                                            dt_iterations,
                                            theory_unsat_count,
                                            theory_farkas_count,
                                            theory_farkas_none_count,
                                            split_count
                                        );
                                    }
                                    // #5925: LRA incompleteness guard
                                    return if has_real_theory_atoms {
                                        SmtResult::Unknown
                                    } else {
                                        SmtResult::Unsat
                                    };
                                }
                                let conflict_terms: Vec<TermId> =
                                    conflict.literals.iter().map(|l| l.term).collect();
                                let polarities: Vec<bool> =
                                    conflict.literals.iter().map(|l| l.value).collect();
                                let origins: Vec<Partition> = conflict_terms
                                    .iter()
                                    .map(|&t| {
                                        get_partition(t, &case_split_atoms, &split_atom_partitions)
                                    })
                                    .collect();
                                let synth_farkas =
                                    FarkasAnnotation::new(vec![
                                        Rational64::from(1);
                                        conflict.literals.len()
                                    ]);
                                let mut conflict_idx: Option<usize> = None;
                                if farkas_conflicts.len() < MAX_FARKAS_CONFLICTS {
                                    farkas_conflicts.push(FarkasConflict {
                                        conflict_terms: conflict_terms.clone(),
                                        polarities: polarities.clone(),
                                        farkas: synth_farkas,
                                        origins,
                                    });
                                    conflict_idx = Some(farkas_conflicts.len() - 1);
                                }
                                let mut clause: Vec<ay_sat::Literal> = conflict
                                    .literals
                                    .iter()
                                    .filter_map(|lit| {
                                        term_to_var.get(&lit.term).map(|&cnf_var| {
                                            let sat_var = ay_sat::Variable::new(cnf_var - 1);
                                            if lit.value {
                                                ay_sat::Literal::negative(sat_var)
                                            } else {
                                                ay_sat::Literal::positive(sat_var)
                                            }
                                        })
                                    })
                                    .collect();
                                if clause.is_empty() {
                                    if crate::proof_interpolation::iuc_trace_enabled() {
                                        safe_eprintln!(
                                            "[IUC-SMT] returning plain UNSAT from TheoryResult::UnsatWithFarkas(None): conflict literals unmapped to CNF (terms={}, dt_iters={}, theory_unsat={}, theory_farkas={}, theory_farkas_none={}, splits={})",
                                            conflict_terms.len(),
                                            dt_iterations,
                                            theory_unsat_count,
                                            theory_farkas_count,
                                            theory_farkas_none_count,
                                            split_count
                                        );
                                    }
                                    // #5925: LRA incompleteness guard
                                    return if has_real_theory_atoms {
                                        SmtResult::Unknown
                                    } else {
                                        SmtResult::Unsat
                                    };
                                }
                                if let Some(idx) = conflict_idx {
                                    num_vars += 1;
                                    sat.ensure_num_vars(num_vars as usize);
                                    let act_var = ay_sat::Variable::new(num_vars - 1);
                                    let act_assumption = ay_sat::Literal::negative(act_var);
                                    sat_assumptions.push(act_assumption);
                                    farkas_assumption_to_conflict_idx.insert(act_assumption, idx);
                                    clause.push(ay_sat::Literal::positive(act_var));
                                }
                                sat.add_clause(clause);
                            }
                        }
                        result @ (TheoryResult::NeedModelEquality(_)
                        | TheoryResult::NeedModelEqualities(_)) => {
                            // Phase 3 Fix 4: encode speculative model-equality
                            // atoms and continue (was: Unknown). Created atoms
                            // are tagged Partition::Split via case_split_atoms
                            // so Farkas origin tagging stays correct.
                            let eqs = match result {
                                TheoryResult::NeedModelEquality(eq) => vec![eq],
                                TheoryResult::NeedModelEqualities(eqs) => eqs,
                                _ => unreachable!(),
                            };
                            let new_eqs: Vec<_> = eqs
                                .into_iter()
                                .filter(|eq| {
                                    let key = if eq.lhs <= eq.rhs {
                                        (eq.lhs, eq.rhs)
                                    } else {
                                        (eq.rhs, eq.lhs)
                                    };
                                    !seen_model_eq_requests.contains(&key)
                                })
                                .collect();
                            if new_eqs.is_empty() {
                                // No progress possible; fail closed (status quo).
                                return SmtResult::Unknown;
                            }
                            model_eq_rounds += 1;
                            if model_eq_rounds > MAX_MODEL_EQ_ROUNDS {
                                return SmtResult::Unknown;
                            }
                            for eq in new_eqs {
                                let key = if eq.lhs <= eq.rhs {
                                    (eq.lhs, eq.rhs)
                                } else {
                                    (eq.rhs, eq.lhs)
                                };
                                seen_model_eq_requests.insert(key);

                                let eq_term = self.terms.mk_eq_coerce(eq.lhs, eq.rhs);
                                case_split_atoms.insert(eq_term);
                                let eq_var = *term_to_var.entry(eq_term).or_insert_with(|| {
                                    num_vars += 1;
                                    var_to_term.insert(num_vars, eq_term);
                                    num_vars
                                });
                                sat.ensure_num_vars(num_vars as usize);
                                let eq_sat_var = ay_sat::Variable::new(eq_var - 1);
                                // Phase bias: try the equality first; CDCL
                                // retracts via theory conflict if wrong.
                                sat.set_var_phase(eq_sat_var, true);
                                for _ in 0..20 {
                                    sat.bump_variable_activity(eq_sat_var);
                                }

                                // Triangle axioms (same-sort Int/Real only, #8596).
                                let lhs_sort = self.terms.sort(eq.lhs).clone();
                                if matches!(lhs_sort, Sort::Int | Sort::Real)
                                    && &lhs_sort == self.terms.sort(eq.rhs)
                                {
                                    let le_lr = self.terms.mk_le(eq.lhs, eq.rhs);
                                    let le_rl = self.terms.mk_le(eq.rhs, eq.lhs);
                                    case_split_atoms.insert(le_lr);
                                    case_split_atoms.insert(le_rl);
                                    let le_lr_var =
                                        *term_to_var.entry(le_lr).or_insert_with(|| {
                                            num_vars += 1;
                                            var_to_term.insert(num_vars, le_lr);
                                            num_vars
                                        });
                                    let le_rl_var =
                                        *term_to_var.entry(le_rl).or_insert_with(|| {
                                            num_vars += 1;
                                            var_to_term.insert(num_vars, le_rl);
                                            num_vars
                                        });
                                    sat.ensure_num_vars(num_vars as usize);
                                    let le_lr_lit = ay_sat::Literal::positive(
                                        ay_sat::Variable::new(le_lr_var - 1),
                                    );
                                    let le_rl_lit = ay_sat::Literal::positive(
                                        ay_sat::Variable::new(le_rl_var - 1),
                                    );
                                    let eq_pos = ay_sat::Literal::positive(eq_sat_var);
                                    let eq_neg = ay_sat::Literal::negative(eq_sat_var);
                                    sat.add_clause(vec![eq_neg, le_lr_lit]);
                                    sat.add_clause(vec![eq_neg, le_rl_lit]);
                                    sat.add_clause(vec![
                                        eq_pos,
                                        le_lr_lit.negated(),
                                        le_rl_lit.negated(),
                                    ]);
                                }

                                // Optional theory-proved lemma ¬reason ∨ eq.
                                if eq.implied && !eq.reason.is_empty() {
                                    let mut clause = Vec::with_capacity(eq.reason.len() + 1);
                                    let mut all_mapped = true;
                                    for lit in &eq.reason {
                                        match term_to_var.get(&lit.term) {
                                            Some(&cnf_var) => {
                                                let sv = ay_sat::Variable::new(cnf_var - 1);
                                                clause.push(if lit.value {
                                                    ay_sat::Literal::negative(sv)
                                                } else {
                                                    ay_sat::Literal::positive(sv)
                                                });
                                            }
                                            None => {
                                                all_mapped = false;
                                                break;
                                            }
                                        }
                                    }
                                    if all_mapped {
                                        clause.push(ay_sat::Literal::positive(eq_sat_var));
                                        sat.add_clause(clause);
                                    }
                                }
                            }
                            continue;
                        }
                        _ => {
                            // Unknown TheoryResult variant; return Unknown (#6091).
                            return SmtResult::Unknown;
                        }
                    }
                }
                ay_sat::AssumeResult::Unsat(core, _) => {
                    let mut conjuncts = Vec::new();
                    let mut needed_conflict_indices: FxHashSet<usize> = FxHashSet::default();
                    for lit in core {
                        if let Some(expr) = assumption_map.get(lit) {
                            conjuncts.push(expr.clone());
                        }
                        if let Some(&idx) = farkas_assumption_to_conflict_idx.get(lit) {
                            needed_conflict_indices.insert(idx);
                        }
                    }
                    let total_farkas_conflicts = farkas_conflicts.len();
                    if crate::proof_interpolation::iuc_trace_enabled() {
                        safe_eprintln!(
                            "[IUC-SMT] UNSAT core: {} activation lits matched of {} total Farkas conflicts (dt_iters={}, theory_unsat={}, theory_farkas={}, theory_farkas_none={}, splits={})",
                            needed_conflict_indices.len(),
                            total_farkas_conflicts,
                            dt_iterations,
                            theory_unsat_count,
                            theory_farkas_count,
                            theory_farkas_none_count,
                            split_count
                        );
                    }
                    farkas_conflicts = Self::filter_farkas_conflicts_by_indices(
                        &needed_conflict_indices,
                        farkas_conflicts,
                    );
                    if !conjuncts.is_empty() || !farkas_conflicts.is_empty() {
                        // #5925: LRA incompleteness guard
                        return if has_real_theory_atoms {
                            SmtResult::Unknown
                        } else {
                            SmtResult::UnsatWithCore(UnsatCore {
                                conjuncts,
                                farkas_conflicts,
                                diagnostics: UnsatCoreDiagnostics {
                                    dt_iterations: dt_iterations as u64,
                                    theory_unsat_count: theory_unsat_count as u64,
                                    theory_farkas_count: theory_farkas_count as u64,
                                    theory_farkas_none_count: theory_farkas_none_count as u64,
                                    split_count: split_count as u64,
                                    activation_core_conflicts: needed_conflict_indices.len() as u64,
                                    total_farkas_conflicts: total_farkas_conflicts as u64,
                                },
                            })
                        };
                    }
                    // #5925: LRA incompleteness guard
                    return if has_real_theory_atoms {
                        SmtResult::Unknown
                    } else {
                        SmtResult::Unsat
                    };
                }
                ay_sat::AssumeResult::Unknown => return SmtResult::Unknown,
                // Future AssumeResult variants: treat as Unknown (sound) (#6091).
                #[allow(unreachable_patterns)]
                _ => return SmtResult::Unknown,
            }
        }
    }
}
