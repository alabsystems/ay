// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental FP solve pipeline: one SAT solver for the whole session.
//!
//! ## Why this exists
//!
//! [`Executor::solve_fp`](super::super::super::Executor::solve_fp) builds
//! `Tseitin::new`, `FpSolver::new_with_tseitin` and `SatSolver::new`
//! function-locally on EVERY check-sat, so push/pop never reached the FP lane
//! and each solve handed a brand-new SAT solver the same CNF. `Solver::solve`
//! runs `preprocess_interruptible` at the top of every solve, gated only on
//! `preprocess_enabled` — which defaults to true and is disarmed exactly once
//! per solver LIFETIME by `finish_initial_preprocessing`. A new lifetime per
//! check-sat therefore re-arms and re-runs the whole probing + level-0 GC suite
//! over essentially unchanged CNF; that suite was measured at 73-94% of
//! main-thread time on an incremental FP workload, while FP word-blasting
//! itself was noise (0.2-1.2%). Merely SURVIVING is the fix — persisting the
//! bit-blast caches alone buys about 1%.
//!
//! ## The blocker this had to solve first
//!
//! FP variable numbering was recomputed per call and was NOT stable:
//! `var_offset = tseitin_result.num_vars` moves with the assertion set, because
//! `Tseitin::new` restarts numbering at 1 every call. Persisting clauses on top
//! of that would mis-wire every FP literal — the circuit constraining a bit and
//! the clause reading it would name different SAT variables, leaving the bit
//! free for the solver to exploit, and model extraction would read the wrong
//! index. `IncrementalFpState::fp_var_offset` freezes it once, and the sync
//! pair keeps the two variable spaces disjoint.
//!
//! ## What is NOT handled here (it declines instead)
//!
//! Disjoint FP-relevant query batches are never admitted. Uninterpreted
//! structure needing Ackermann congruence, unsupported FP predicates, and base
//! encoding gaps take the sticky opt-out. Declining is always safe: "disabled"
//! is the pre-existing stateless behaviour.
//!
//! ## Admission
//! Persistence is never seeded speculatively. Every current FP-relevant
//! authored [`TermId`] must have appeared in the prior observation or active
//! encoding; pop/reassert counts because identity is immutable. A novel root
//! restarts statelessly and may re-admit only after the full set recurs.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{CnfClause, TermId, Tseitin, TseitinResult};
use ay_fp::FpSolver;
use ay_sat::{SatResult, Solver as SatSolver};

use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::incremental_state::{FpIncrementalAdmission, IncrementalFpState};

use super::super::super::Executor;
use super::support::FpPredicateResult;
use super::{congruence, to_real::offset_cnf_lit};

/// Root preprocessing on the PERSISTENT solver.
///
/// `false`, deliberately, and this is the one place the design copies
/// `bv_incremental.rs` (`sat.set_preprocess_enabled(false)`) rather than the
/// FP-specific plan. Keeping it enabled would let preprocessing run its one
/// permitted pass — but BVE may then eliminate a variable that a LATER
/// check-sat's global clause mentions, whose value is reconstructed from a
/// witness stack that never saw that clause. `add_clause_unscoped_global` does
/// reactivate removed variables (#7981), but that interaction is untested for
/// FP and its failure mode is a silent wrong SAT. The measured win is NOT
/// running the suite once per check-sat, and that survives either way: this
/// trades one useful pass for a closed soundness question.
const PERSISTENT_FP_SAT_PREPROCESS: bool = false;

/// Reorder gate threshold, mirroring the stateless path (#8118).
const REORDER_DISABLE_VARS: usize = 50_000;

impl Executor {
    /// Attempt persistence. Novel active roots tear the solver down before
    /// `Ok(None)`; no discarded clause can reach the stateless fallback.
    pub(super) fn try_solve_fp_incremental(&mut self) -> Result<Option<SolveResult>> {
        // The complete FP-relevant root set is the admission proof.
        // There is no speculative seed, and an active novel set restarts
        // statelessly before its first answer.
        // Its recorded full set is admission evidence only for a later query;
        // no encoding or SAT clause survives the deferred answer.
        let admission = self
            .incr_fp_state
            .get_or_insert_with(IncrementalFpState::new)
            .observe_live_assertion_reuse(&self.ctx.terms, &self.ctx.assertions);
        match admission {
            FpIncrementalAdmission::Admit => {}
            FpIncrementalAdmission::Defer => return Ok(None),
        }

        // Congruence needs append-only pair tracking and re-scans as foreign
        // terms grow; a missed pair is a wrong `sat`, so decline this shape.
        if !congruence::scan_foreign(&self.ctx.terms, &self.ctx.assertions).is_empty() {
            self.disable_fp_incremental_lane();
            return Ok(None);
        }

        // Authorization (`fp_persistent_armed`) is fail-safe by POLARITY, but
        // it is still an audit: it assumes no route reaches `solve_fp` with a
        // substituted `ctx.assertions` while the flag is live. Six such routes
        // were enumerated and disarmed; one could not be ruled out by reading
        // alone — the DT-certificate ground-core solve
        // (`check_sat.rs`, `mem::replace(&mut self.ctx.assertions, ground)`)
        // reaches `route_to_solver` a second time from INSIDE the armed window,
        // so a ground core that classified as `QfFp`/`QfBvfp` would be encoded
        // and activated into the session state.
        //
        // Rather than rest on that audit, check the invariant the audit is
        // supposed to establish, in release builds, on every solve: every
        // assertion this lane still holds a live activation unit for must still
        // be in the assertion stack. `pop` already drops the records deeper
        // than the new depth, and a shallower record can only belong to an
        // assertion no `pop` has retracted — so on an authorized session this
        // is trivially true, and it is false exactly when a substituted set
        // installed an activation the frontend never retracts (a wrong `unsat`
        // on the next check-sat).
        //
        // Firing is fail-CLOSED: tear the session state down and hand the
        // problem to the untouched stateless pipeline. It costs speed, never
        // correctness, so it is safe to leave armed permanently.
        let provenance_violation = self.incr_fp_state.as_ref().is_some_and(|state| {
            !state.assertion_activation_scope.is_empty() && {
                let live: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
                state
                    .assertion_activation_scope
                    .keys()
                    .any(|term| !live.contains(term))
            }
        });
        // Stateless fallback repopulates statistics, so report via tracing.
        if provenance_violation {
            tracing::warn!(
                "persistent FP lane holds an activation for an assertion that is no longer in \
                 the assertion stack — a substituted assertion set reached it; tearing the \
                 session state down and falling back to the stateless pipeline"
            );
            self.disable_fp_incremental_lane();
            return Ok(None);
        }

        let random_seed = self.current_random_seed();
        self.record_applied_sat_random_seed_for_test(random_seed);
        let progress_enabled = self.progress_enabled;
        let progress_json_path = self.progress_json_path.clone();

        // ---- Phase 1: Tseitin encoding over the PERSISTENT state ----
        let state = self
            .incr_fp_state
            .get_or_insert_with(IncrementalFpState::new);

        // Order is load-bearing (#7031): the Tseitin sync needs the current FP
        // frontier, the FP sync needs the updated Tseitin frontier.
        state.sync_tseitin_next_var();
        state.sync_next_fp_var();

        let new_assertions: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .filter(|&term| !state.encoded_assertions.contains_key(term))
            .copied()
            .collect();

        let mut tseitin =
            Tseitin::from_state(&self.ctx.terms, std::mem::take(&mut state.tseitin_state));
        // `encode_assertion`, not `assert_term`. The stateless path folds the
        // activation unit into the clause list, which makes it impossible to
        // install the definitions globally without ALSO installing the
        // assertion globally — and that is precisely the wrong answer this
        // whole design exists to avoid.
        let mut def_clauses: Vec<CnfClause> = Vec::new();
        for &term in &new_assertions {
            let enc = tseitin.encode_assertion(term);
            def_clauses.extend(enc.def_clauses);
            state.encoded_assertions.insert(term, enc.root_lit);
        }
        state.tseitin_state = tseitin.into_state();

        // ---- The set-once offset ----
        // FP bit-blaster variable `v` occupies SAT variable `v + offset` for
        // the whole session. Written once; read by the circuit clauses, the
        // Tseitin↔FP links, the ITE/Bool-input links, and model extraction. All
        // four must agree or a cached bit names a different SAT variable than
        // the clause constraining it (#1453 for the BV twin).
        let var_offset = match state.fp_var_offset {
            Some(offset) => offset,
            None => {
                let offset = state.tseitin_state.next_var as i32;
                state.fp_var_offset = Some(offset);
                offset
            }
        };
        // A frozen offset means the Tseitin space is no longer a contiguous
        // prefix: variables allocated just above would land INSIDE the FP
        // range. Re-run the pair now that this call's Tseitin allocation is
        // done, so the next allocation jumps the range (#7015).
        state.sync_tseitin_next_var();
        state.sync_next_fp_var();

        // Snapshot what Phase 2 needs, then release the state borrow:
        // `bitblast_fp_predicate` takes `&self`.
        let fp_cache = state.fp_cache.clone();
        let tseitin_term_to_var = state.tseitin_state.term_to_var.clone();
        let tseitin_var_to_term = state.tseitin_state.var_to_term.clone();
        let already_linked = state.linked_predicate_vars.clone();
        let already_repaired = state.linked_bool_inputs.clone();

        // ---- Phase 2: FP bit-blasting with the persistent caches ----
        // `new_with_tseitin` re-supplies `term_to_cnf` from the CURRENT Tseitin
        // map. That refresh is necessary (a term named only on a later
        // check-sat must become linkable) but NOT sufficient — see the repair
        // pass below.
        let mut fp_solver = FpSolver::new_with_tseitin(&self.ctx.terms, &tseitin_term_to_var);
        fp_solver.import_cache(fp_cache);

        let mut linking_pairs: Vec<(i32, i32)> = Vec::new();
        let mut newly_linked: HashSet<u32> = HashSet::default();
        let mut unsupported_predicate = false;
        for (&tseitin_var, &term) in &tseitin_var_to_term {
            // With a persistent Tseitin state this walk sees the WHOLE
            // accumulated map. Re-blasting an already-linked predicate is sound
            // (both literals define the same Boolean function of the same
            // cached bits, so both biconditionals are simultaneously
            // satisfiable) but allocates fresh variables every call and grows
            // the encoding without bound. FP has no `predicate_to_var` cache,
            // so this set is the guard.
            if already_linked.contains(&tseitin_var) || newly_linked.contains(&tseitin_var) {
                continue;
            }
            match self.bitblast_fp_predicate(&mut fp_solver, term) {
                FpPredicateResult::Bitblasted(fp_lit) => {
                    linking_pairs.push((tseitin_var as i32, fp_lit));
                    newly_linked.insert(tseitin_var);
                }
                FpPredicateResult::NotFpPredicate => {
                    // Term data is immutable, so this verdict cannot change.
                    newly_linked.insert(tseitin_var);
                }
                FpPredicateResult::Unsupported => {
                    unsupported_predicate = true;
                    break;
                }
            }
        }

        // ---- The Bool-input link pass ----
        //
        // A free Bool `b` reachable only under an FP `ite` gets an UNLINKED
        // fresh FP literal from `bool_input_lit`, because the Tseitin walk had
        // not named it. That is sound for a ONE-SHOT solve, and it is exactly
        // what breaks under persistence: `term_to_fp` caches the enclosing
        // decomposition, so when a LATER check-sat asserts `b` and gives it a
        // Tseitin variable, `encode_bool_condition` is never called again and
        // the mux stays wired to the unlinked literal. The SAT solver then
        // satisfies `(assert b)` through the Tseitin variable while the mux
        // takes the ELSE branch through the independent FP literal — a wrong
        // `sat` the model gate cannot see, because the published FP value is
        // internally consistent and the disagreement is between two names for
        // the same symbol. Refreshing `term_to_cnf` above does NOT fix it, for
        // exactly that caching reason.
        //
        // So do not wait for the term to acquire a Tseitin variable: give it
        // one NOW (Phase 3 below) and tie the two names together immediately,
        // for every entry, on the check-sat that creates it. Then no unlinked
        // literal ever survives a solve and the hazard cannot arise.
        //
        // This also repairs a MODEL defect the stateless path still has: `b`
        // had no Tseitin variable, so it was published as the default `false`
        // regardless of which branch the mux actually took, and the soundness
        // gate rejected the (real) model as invalid.
        let mut pending_bool_links: Vec<(TermId, i32)> = fp_solver
            .bool_input_lits()
            .iter()
            .filter(|(&term, _)| !already_repaired.contains(&term))
            .map(|(&term, &lit)| (term, lit))
            .collect();
        // `bool_input_lits` is a hash map; fix a deterministic order.
        pending_bool_links.sort_unstable();

        // Drain the gap flag rather than reading it: it is sticky by
        // construction (set in ~11 places, cleared only by the constructors).
        let encoding_gap = fp_solver.take_encoding_gap();
        let fp_clauses = fp_solver.take_clauses();
        let condition_links = fp_solver.take_pending_condition_links();
        let updated_cache = fp_solver.export_cache();
        let fp_next_var = updated_cache.next_var;
        let term_to_fp = updated_cache.term_to_fp.clone();
        let bv_term_bits = updated_cache.bv_term_bits.clone();
        drop(fp_solver);

        // ---- Decline: `fp.to_{s,u}bv` conversions ----
        //
        // MEASURED, not theorised. On a synthetic incremental corpus saturated
        // with `fp.to_ubv`/`fp.to_sbv`, lane-on lost 16 of 777 check-sat
        // indices from a definite `sat` to a fail-closed `unknown` — the model
        // gate reporting the conversion "evaluates to <unknown>". Instrumenting
        // both paths showed `term_to_fp` and `bv_term_bits` IDENTICAL across
        // them, so the encoding is not the problem and no wrong answer is in
        // play; something downstream of model extraction reads a conversion the
        // stateless path resolves. On the general corpus (1631 indices, no
        // conversions) the lane loses nothing and gains 8.
        //
        // Rather than ship a completeness regression on a shape whose last hop
        // is not yet understood, hand exactly that shape back. `unsat` and
        // `sat` are both unaffected — the stateless pipeline decides these
        // files precisely as it did before this subsystem existed — and the
        // decline is sticky, so the cost is one wasted encode per session.
        // Remove this the moment the extraction gap is found and fixed.
        if !updated_cache.to_bv_unspec_sites.is_empty() {
            self.disable_fp_incremental_lane();
            return Ok(None);
        }

        // ---- Declines discovered after encoding began ----
        // Both publish exactly what the stateless path publishes for the same
        // cause, and both tear the session state down first, so the very next
        // check-sat is a clean stateless solve.
        if unsupported_predicate {
            self.disable_fp_incremental_lane();
            self.last_unknown_reason = Some(UnknownReason::Unsupported);
            return Ok(Some(SolveResult::Unknown));
        }
        if encoding_gap {
            self.disable_fp_incremental_lane();
            tracing::warn!("FP encoding has unresolvable ITE condition — returning Unknown");
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.record_unknown_diagnostic(
                UnknownReason::Incomplete,
                "FP base encoding left an `ite` condition unresolved (not an FP predicate and not \
                 linkable through the Tseitin map), so a `sat` over it would be unsound",
            );
            return Ok(Some(SolveResult::Unknown));
        }

        // ---- Phase 3: install clauses on the persistent SAT solver ----
        let state = self
            .incr_fp_state
            .as_mut()
            .expect("incremental FP state must exist after encoding");
        state.fp_cache = updated_cache;
        state.next_fp_var = state.next_fp_var.max(fp_next_var);
        for var in newly_linked {
            state.linked_predicate_vars.insert(var);
        }

        // Name every free Bool input at the Tseitin level and record the pair
        // to link (see the Bool-input link pass above). `encode_root` allocates
        // the variable if the term does not already have one and returns the
        // literal WITHOUT installing an activation unit — the term is being
        // named, not asserted.
        let mut bool_link_pairs: Vec<(i32, i32)> = Vec::new();
        if !pending_bool_links.is_empty() {
            // Phase 2 allocated FP variables, so the Tseitin frontier saved in
            // Phase 1 may now sit INSIDE the frozen FP range. Jump it out
            // before allocating, not after — the offending variable would
            // already have been handed out.
            state.sync_tseitin_next_var();
            let mut naming =
                Tseitin::from_state(&self.ctx.terms, std::mem::take(&mut state.tseitin_state));
            for &(term, fp_lit) in &pending_bool_links {
                bool_link_pairs.push((naming.encode_root(term), fp_lit));
            }
            def_clauses.extend(naming.take_new_clauses());
            state.tseitin_state = naming.into_state();
            for &(term, _) in &pending_bool_links {
                state.linked_bool_inputs.insert(term);
            }
            state.sync_next_fp_var();
        }

        let total_vars = (state.tseitin_state.next_var.saturating_sub(1) as usize)
            .max((var_offset as i64 + state.next_fp_var as i64 - 1).max(0) as usize);

        let mut solver = match state.persistent_sat.take() {
            Some(existing) => existing,
            None => {
                let mut sat = SatSolver::new(total_vars);
                sat.set_random_seed(random_seed);
                // Construction-time only, like the BV persistent solver: a
                // progress observer re-installed per check-sat would reopen the
                // JSON sink on every solve.
                if progress_enabled {
                    sat.set_progress_enabled(true);
                }
                if let Some(ref path) = progress_json_path {
                    if let Ok(obs) = ay_sat::json_observer::JsonProgressObserver::new_append(path) {
                        sat.set_observer(Some(Box::new(obs)));
                    }
                }
                // Structurally similar encoding variables (carry bits, …) are
                // semantically distinct, as on the stateless path.
                sat.set_congruence_enabled(false);
                sat.set_preprocess_enabled(PERSISTENT_FP_SAT_PREPROCESS);
                if total_vars > REORDER_DISABLE_VARS {
                    sat.set_reorder_enabled(false);
                }
                // Pushes that arrived before any solver existed.
                for _ in 0..state.pending_pushes {
                    sat.push();
                }
                state.pending_pushes = 0;
                sat
            }
        };
        solver.ensure_num_vars(total_vars);

        // Re-sync both frontiers past the scope selectors `push()` allocated.
        // A Tseitin variable colliding with a live selector is assumed
        // `¬selector` and silently forced — a wrong answer with no symptom.
        let sat_total = solver.total_num_vars() as i64;
        state.tseitin_state.next_var = state
            .tseitin_state
            .next_var
            .max((sat_total + 1).max(1) as u32);
        state.next_fp_var = state
            .next_fp_var
            .max((sat_total - var_offset as i64 + 1).max(1) as u32);
        state.fp_cache.next_var = state.fp_cache.next_var.max(state.next_fp_var);

        // BUCKET 1 — scope-INDEPENDENT, installed with `add_clause_global`.
        //
        // Every clause below either defines a FRESH variable as a Boolean
        // function of already-defined ones (a definitional extension, which
        // removes no model of the user's formula) or is an equivalence between
        // two defined names for the same term. Neither can over-constrain a
        // shallower scope, which is why `pop` needs no teardown at all.
        // `add_clause_global` also routes them through
        // `OriginalLedger::push_clause_global`, so they replay past `pop_scope`
        // truncation (#9378).

        // (1a) Tseitin definitional clauses.
        for clause in &def_clauses {
            let lits: Vec<ay_sat::Literal> = clause
                .literals()
                .iter()
                .map(|&lit| crate::cnf_lit_to_sat(lit))
                .collect();
            solver.add_clause_global(lits);
        }

        // (1b) FP circuit clauses. Every one comes from `fresh_var()` +
        // `add_clause` inside the gate/adder/multiplier circuits, pinning a
        // fresh FP variable to a function of existing FP bits; the leaves are
        // `fresh_decomposed`, an unconstrained naming of a value the formula
        // already denotes. `FpSolver` never receives `ctx.assertions`.
        for clause in &fp_clauses {
            let lits: Vec<ay_sat::Literal> = clause
                .literals()
                .iter()
                .map(|&lit| crate::cnf_lit_to_sat(offset_cnf_lit(lit, var_offset)))
                .collect();
            solver.add_clause_global(lits);
        }

        // (1c) Tseitin↔FP predicate equivalences: two defined names for one
        // predicate. (1d) ITE condition links and the Bool-input repair links
        // have exactly the same shape.
        let ite_links = condition_links
            .into_iter()
            .map(|(fp_var, tseitin_var)| (tseitin_var as i32, fp_var as i32));
        for (tseitin_lit, fp_lit) in linking_pairs
            .into_iter()
            .chain(ite_links)
            .chain(bool_link_pairs)
        {
            let fp_lit_offset = offset_cnf_lit(fp_lit, var_offset);
            solver.add_clause_global(vec![
                crate::cnf_lit_to_sat(-tseitin_lit),
                crate::cnf_lit_to_sat(fp_lit_offset),
            ]);
            solver.add_clause_global(vec![
                crate::cnf_lit_to_sat(tseitin_lit),
                crate::cnf_lit_to_sat(-fp_lit_offset),
            ]);
        }

        state.solves += 1;
        let lane_solve_index = state.solves;

        // BUCKET 2 — the ONLY scope-dependent object: the activation unit on
        // each surviving assertion's Tseitin root. At depth 0 `add_clause`
        // installs a permanent unit; at depth d>0 it appends `+selector_d`, and
        // the scope is entered by assuming `¬selector_d`. `Solver::pop` asserts
        // `+selector_d` permanently and GCs the guarded clauses, retracting the
        // activation exactly — which is why `pop` drops the deeper activation
        // records, so survivors are re-activated here on the next solve (#2822).
        let scope_depth = state.scope_depth;
        for &assertion in &self.ctx.assertions {
            let Some(&root_lit) = state.encoded_assertions.get(&assertion) else {
                continue;
            };
            let needs_activation = state
                .assertion_activation_scope
                .get(&assertion)
                .is_none_or(|&depth| depth > scope_depth);
            if needs_activation {
                solver.add_clause(vec![crate::cnf_lit_to_sat(root_lit)]);
                state
                    .assertion_activation_scope
                    .insert(assertion, scope_depth);
            }
        }

        let solve_tseitin_result = TseitinResult::new(
            vec![],
            state.tseitin_state.term_to_var.clone(),
            state.tseitin_state.var_to_term.clone(),
            1,
            state.tseitin_state.next_var.saturating_sub(1),
        );

        // ---- Phase 4: solve ----
        // Deterministic `:rlimit` conflict budget (#8749). The target is
        // ABSOLUTE and relative to the conflicts this PERSISTENT solver has
        // already accrued across the session, so one allowance bounds this
        // check-sat rather than the session.
        self.arm_sat_conflict_budget(&mut solver, 0);
        let should_stop = self.make_should_stop();
        let result = solver.solve_interruptible(should_stop).into_inner();

        collect_sat_stats!(self, &solver);
        // Proof that the lane actually engaged, and how far into the session
        // this solve is. A differential sweep over a corpus that never reached
        // the lane is a clean result about nothing.
        self.last_statistics
            .set_int("fp_incremental.solves", lane_solve_index);

        let (fp_model, bv_model) = if let SatResult::Sat(ref sat_model) = result {
            let fp = Self::extract_fp_model_from_bits(
                sat_model,
                &term_to_fp,
                var_offset,
                &self.ctx.terms,
            );
            let bv = if bv_term_bits.is_empty() {
                None
            } else {
                Some(Self::extract_bv_model_from_fp_bits(
                    sat_model,
                    &bv_term_bits,
                    var_offset,
                    &self.ctx.terms,
                ))
            };
            (Some(fp), bv)
        } else {
            (None, None)
        };

        // Hand the solver back BEFORE any `&mut self` call that can return.
        // Leaving `persistent_sat` at `None` while the caches survive would be
        // a MISSING-CLAUSE wrong SAT on the next check-sat: the cached encoding
        // would be treated as already installed on a solver that never got it.
        self.incr_fp_state
            .as_mut()
            .expect("incremental FP state must exist after solving")
            .persistent_sat = Some(solver);

        self.solve_and_store_model_full(
            result,
            &solve_tseitin_result,
            None,
            None,
            None,
            None,
            bv_model,
            fp_model,
            None,
            None,
        )
        .map(Some)
    }

    /// Permanently opt this session out of the persistent FP lane and drop
    /// everything it built, so every later `solve_fp` runs the untouched
    /// stateless pipeline. Always safe: "disabled" IS the pre-existing
    /// behaviour.
    fn disable_fp_incremental_lane(&mut self) {
        self.incr_fp_state
            .get_or_insert_with(IncrementalFpState::new)
            .disable_and_teardown();
    }
}
