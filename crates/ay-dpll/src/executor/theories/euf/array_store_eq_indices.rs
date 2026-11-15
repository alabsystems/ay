// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Congruence instances for a re-solve after a refuted array model
//! (#array-refutation-retry).
//!
//! Two shapes end the search on an assignment the model builder cannot turn
//! into arrays, so the independent gate refutes the model (or the validation
//! pipeline cannot validate it) and the verdict fail-closes to `unknown` where
//! z3 answers at once (2026-09-24 arrays fix-up):
//!
//! * A select-free STORE-CHAIN EQUALITY, `(= L R)`, holds exactly when the two
//!   arrays agree at every index, but the lazy array solver reads a chain only
//!   at indices where some `select` term exists. With the store indices
//!   undecided, the equality is true in the Boolean skeleton while the
//!   reconstructed chains differ at a written index (hunt D4-b/D4-c witnesses;
//!   the D4-a repair's lost `sat` answers). z3 never reaches that state: its
//!   read-over-write axioms put a `select` at every store index into the
//!   congruence closure, and congruence carries it across the equality.
//!   Supplied here as, for every index `t` written along either chain,
//!   `(or (not (= L R)) (= (select L t) (select R t)))`.
//! * Two applications of an ARRAY-VALUED uninterpreted function, `g(s)` and
//!   `g(t)`, whose arguments the arithmetic model makes equal while the search
//!   never merged the applications (hunt M1/M2: `(g (+ i2 1))` and `(g 2)` at
//!   `i2 = 1`). Supplied as the Ackermann instance
//!   `(or (not (= s t)) (= (g s) (g t)))`.
//!
//! Every instance is a congruence tautology, valid in every model, and is
//! recorded as a theory lemma through `push_array_axiom_assertion_site`. The
//! read-over-write machinery then peels each new read through its chain,
//! exposing the index relations the search must decide.

use super::super::super::Executor;
use crate::executor_types::{Result, SolveResult, UnknownReason};
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermData, TermId};

/// Longest syntactic store chain walked for its written indices.
const MAX_WRITTEN_INDEX_DEPTH: usize = 64;

/// At most this many instances per armed fixpoint.
pub(in crate::executor) const ARRAY_REFUTATION_INSTANCE_CAP: usize = 512;

/// At most this many read-over-write clauses peeling the new reads (the bound
/// of the QF_AX escalation's deep peel).
const ARRAY_REFUTATION_PEEL_CAP: usize = 20_000;

/// The array-sort equalities with a store side and the applications of
/// array-valued uninterpreted functions reachable from a set of roots.
#[derive(Default)]
struct RefutationTargets {
    store_equalities: Vec<(TermId, TermId, TermId)>,
    array_valued_apps: Vec<(TermId, Vec<TermId>)>,
}

impl RefutationTargets {
    fn is_empty(&self) -> bool {
        self.store_equalities.is_empty() && self.array_valued_apps.len() < 2
    }
}

impl Executor {
    /// #array-refutation-retry: REACTIVE re-solve of a plain `check-sat` whose
    /// first model was refuted by the independent gate or left unvalidated,
    /// on a problem with a store-chain equality or array-valued uninterpreted
    /// applications (module docs).
    ///
    /// The re-solve arms `array_refutation_instances_armed`, so the array axiom
    /// fixpoint asserts the congruence instances inside the solve's own proof
    /// session. A first pass whose model the gates accept never reaches here,
    /// so files already decided keep their path and cost; the re-solve only
    /// replaces a fail-closed `unknown`. SOUND: the instances are congruence
    /// tautologies, the re-solve decides the same assertion set, and its
    /// verdict passes the same gates through `emit_sat_verdict`; a
    /// still-refuted model stays `unknown`. Retry-once latch and deadline
    /// guard as the other model-rejection re-solves in `check_sat_guarded`.
    pub(in crate::executor) fn array_refutation_resolve(
        &mut self,
        result: SolveResult,
    ) -> Result<SolveResult> {
        if !self.array_refutation_retry_armed(&result, &[]) {
            return Ok(result);
        }
        self.array_refutation_retry_done = true;
        self.array_refutation_instances_armed = true;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.last_model = None;
        let retry = self.check_sat_internal();
        // Never let the fixpoint-facing flag outlive the re-solve.
        self.array_refutation_instances_armed = false;
        let retry = retry?;
        if retry.is_unsat() && self.produce_proofs_enabled() && self.last_proof.is_none() {
            self.build_unsat_proof();
        }
        let result = self.emit_sat_verdict(retry, &[])?;
        self.last_statistics
            .set_int("model_validation.array_refutation_retry", 1);
        Ok(result)
    }

    /// Whether a query that answered `result` gets the re-solve: `unknown` for
    /// a reason other than the deadline, after a model refuted by the
    /// independent gate or left unvalidated by the validation pipeline, with
    /// budget left, not yet retried, and something to instantiate.
    pub(in crate::executor) fn array_refutation_retry_armed(
        &self,
        result: &SolveResult,
        assumption_roots: &[TermId],
    ) -> bool {
        *result == SolveResult::Unknown
            && !self.array_refutation_retry_done
            && (self.array_model_refuted || self.last_statistics.model_validation_failures > 0)
            && !matches!(self.last_unknown_reason, Some(UnknownReason::Timeout))
            && !self.solve_deadline.expired()
            && !self.refutation_targets(assumption_roots).is_empty()
    }

    /// Whether the array axiom fixpoint scopes itself to the terms the current
    /// assertions (and assumption roots) reach: in incremental mode (#6726), on
    /// a derived query sharing an outer term store (#7956), in the
    /// #array-refutation-retry re-solve, and for the single AUFLIA
    /// preprocessing call on a branch-assignment-rewritten window (whose
    /// original conditional store equalities are unreachable by design).
    ///
    /// The re-solve runs on the term store its refuted first pass filled --
    /// Nelson-Oppen and split atoms, their negations, the first fixpoint's
    /// reads -- and the whole-store scans index congruence and extensionality
    /// axioms at every one of them. Measured on fresh storeeq_2410_0508
    /// (`--debug auflia-fix-summary`): first pass 21 assertions (`ext=0 sv=21
    /// os=7`), re-solve 322 (`ext=16 sv=166 os=221`) and 547 split rounds to
    /// the deadline, while a FRESH solve of the input plus the same instances
    /// needs 33 (`ext=0 sv=30 os=22`) and answers `sat` in 0.4 s. Scoping
    /// only withholds axiom instances at terms no current assertion reaches;
    /// every instance is valid, and every model still passes the gates.
    pub(in crate::executor) fn live_array_axiom_scope_wanted(&self) -> bool {
        self.incremental_mode
            || self.shared_store_derived_query
            || self.array_refutation_instances_armed
            || self.branch_assign_scoped_fixpoint
    }

    /// Assert the congruence instances of the module docs for everything
    /// reachable from the current assertions and `assumption_roots`, at most
    /// `cap` of them. Returns the number asserted.
    pub(in crate::executor) fn add_array_refutation_instances(
        &mut self,
        cap: usize,
        assumption_roots: &[TermId],
    ) -> usize {
        let mut new_reads: Vec<TermId> = Vec::new();
        let emitted =
            self.add_array_refutation_congruence_instances(cap, assumption_roots, &mut new_reads);
        if !new_reads.is_empty() {
            // The fixpoint's bounded eager phase peels a read one store layer
            // deep (#8785); the index relation that decides a new read can sit
            // several layers down, so peel every layer of the reads created
            // here, as the QF_AX escalation's demand-driven peel does
            // (#mgr-row-peel). Only these reads: peeling every read in the
            // problem re-expands the eager fixpoint's own seeded reads as well.
            self.add_array_row_deep_peel_clauses_for_selects(&new_reads, ARRAY_REFUTATION_PEEL_CAP);
        }
        emitted
    }

    fn add_array_refutation_congruence_instances(
        &mut self,
        cap: usize,
        assumption_roots: &[TermId],
        new_reads: &mut Vec<TermId>,
    ) -> usize {
        let targets = self.refutation_targets(assumption_roots);
        let mut emitted = 0_usize;
        for (eq_term, lhs, rhs) in targets.store_equalities {
            let mut indices = self.store_chain_written_indices(lhs);
            indices.extend(self.store_chain_written_indices(rhs));
            indices.sort_unstable_by_key(|t| t.0);
            indices.dedup();
            for index in indices {
                if emitted >= cap {
                    return emitted;
                }
                let lhs_read = self.ctx.terms.mk_select(lhs, index);
                let rhs_read = self.ctx.terms.mk_select(rhs, index);
                if lhs_read == rhs_read {
                    continue;
                }
                let reads_agree = self.ctx.terms.mk_eq(lhs_read, rhs_read);
                let not_equal = self.ctx.terms.mk_not(eq_term);
                let instance = self.ctx.terms.mk_or(vec![not_equal, reads_agree]);
                if self.push_new_refutation_instance(instance, "store_eq_written_index") {
                    emitted += 1;
                    new_reads.extend([lhs_read, rhs_read]);
                }
            }
        }
        let mut groups: HashMap<(String, Sort, Vec<Sort>), Vec<(TermId, Vec<TermId>)>> =
            HashMap::default();
        for (app, args) in targets.array_valued_apps {
            let TermData::App(sym, _) = self.ctx.terms.get(app) else {
                continue;
            };
            let signature = (
                sym.name().to_string(),
                self.ctx.terms.sort(app).clone(),
                args.iter()
                    .map(|&arg| self.ctx.terms.sort(arg).clone())
                    .collect::<Vec<_>>(),
            );
            groups.entry(signature).or_default().push((app, args));
        }
        let mut signatures: Vec<_> = groups.keys().cloned().collect();
        signatures.sort_unstable_by(|a, b| a.0.cmp(&b.0).then(a.2.len().cmp(&b.2.len())));
        for signature in signatures {
            let apps = &groups[&signature];
            for (i, (lhs_app, lhs_args)) in apps.iter().enumerate() {
                for (rhs_app, rhs_args) in &apps[i + 1..] {
                    if emitted >= cap {
                        return emitted;
                    }
                    let mut disjuncts: Vec<TermId> = Vec::with_capacity(lhs_args.len() + 1);
                    for (&a, &b) in lhs_args.iter().zip(rhs_args) {
                        if a != b {
                            let args_equal = self.ctx.terms.mk_eq(a, b);
                            disjuncts.push(self.ctx.terms.mk_not(args_equal));
                        }
                    }
                    disjuncts.push(self.ctx.terms.mk_eq(*lhs_app, *rhs_app));
                    let instance = if disjuncts.len() == 1 {
                        disjuncts[0]
                    } else {
                        self.ctx.terms.mk_or(disjuncts)
                    };
                    if self.push_new_refutation_instance(instance, "array_valued_uf_ackermann") {
                        emitted += 1;
                    }
                }
            }
        }
        emitted
    }

    fn push_new_refutation_instance(&mut self, instance: TermId, site: &str) -> bool {
        if instance == self.ctx.terms.true_term() || self.ctx.assertions.contains(&instance) {
            return false;
        }
        self.push_array_axiom_assertion_site(instance, site);
        true
    }

    /// The equalities between arrays with a store on at least one side, and
    /// the applications of array-valued uninterpreted functions, reachable
    /// from the current assertions and `assumption_roots`, in term order.
    fn refutation_targets(&self, assumption_roots: &[TermId]) -> RefutationTargets {
        let mut targets = RefutationTargets::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        stack.extend_from_slice(assumption_roots);
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(term) {
                let array_valued = matches!(self.ctx.terms.sort(term), Sort::Array(_));
                if sym.name() == "="
                    && args.len() == 2
                    && matches!(self.ctx.terms.sort(args[0]), Sort::Array(_))
                    && self.ctx.terms.sort(args[0]) == self.ctx.terms.sort(args[1])
                    && (self.term_is_store_application(args[0])
                        || self.term_is_store_application(args[1]))
                {
                    targets.store_equalities.push((term, args[0], args[1]));
                } else if array_valued
                    && !args.is_empty()
                    && !crate::features::is_builtin_symbol_name(sym.name())
                {
                    targets.array_valued_apps.push((term, args.clone()));
                }
            }
            stack.extend(self.ctx.terms.children(term));
        }
        targets
            .store_equalities
            .sort_unstable_by_key(|&(eq, _, _)| eq.0);
        targets
            .array_valued_apps
            .sort_unstable_by_key(|(app, _)| app.0);
        targets
    }

    fn term_is_store_application(&self, term: TermId) -> bool {
        matches!(
            self.ctx.terms.get(term),
            TermData::App(sym, args) if sym.name() == "store" && args.len() == 3
        )
    }

    /// The indices written along `array`'s syntactic store chain, outermost
    /// first.
    fn store_chain_written_indices(&self, array: TermId) -> Vec<TermId> {
        let mut indices = Vec::new();
        let mut current = array;
        for _ in 0..MAX_WRITTEN_INDEX_DEPTH {
            match self.ctx.terms.get(current) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    indices.push(args[1]);
                    current = args[0];
                }
                _ => break,
            }
        }
        indices
    }
}
