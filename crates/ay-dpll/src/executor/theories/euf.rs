// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF, DT, and Array+EUF solving.

#[cfg(test)]
mod array_axiom_attribution_tests;
mod array_congruence;
mod array_fixpoint;
mod array_patterns;
mod array_row;
mod dt;
mod enum_sat;
mod pigeonhole_core;
#[cfg(test)]
mod tests;

use super::super::Executor;
use crate::executor::theories::solve_harness::TheoryModels;
use crate::executor_types::{Result, SolveResult};
use crate::term_helpers::{collect_bool_arg_congruence_lemmas, or_implies_eq_endpoints};
// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore, TheoryLemmaKind};
use ay_euf::EufSolver;

/// `--euf-bool-arg-repair` enables the targeted Bool-arg congruence repair
/// loop in `solve_euf`. DEFAULT OFF: unset keeps the historical behaviour of
/// surrendering the check-sat to `Unknown` when the post-SAT guard rejects a
/// non-congruent model, so the default path is byte-identical. Single cached
/// env read.
fn bool_arg_repair_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().euf_bool_arg_repair)
}

/// Collect all TermIds transitively reachable from the given root terms (#6726).
/// Used to scope array axiom generation to terms in the current assertion set,
/// excluding dead terms from popped scopes in the ordinary append-only
/// history. The isolated speculative DT lane discards its entire suffix only
/// after its solver state is dropped, before this scope is observed.
pub(crate) fn reachable_term_set(terms: &TermStore, roots: &[TermId]) -> HashSet<TermId> {
    let mut visited = ay_core::kani_compat::det_hash_set_with_capacity(roots.len() * 4);
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        for child in terms.children(t) {
            stack.push(child);
        }
    }
    visited
}

/// Controls whether array ROW/ROW2b axioms are generated eagerly during
/// preprocessing or deferred to `ArraySolver::final_check()`.
///
/// Routes backed by `TheoryCombiner` (which includes `ArraySolver` with
/// `set_defer_expensive_checks(true)`) already have runtime lazy ROW
/// handling. Using `LazyRow2FinalCheck` on those routes avoids the
/// O(selects × stores) eager blowup from ROW2b while preserving ROW1
/// clauses that the SAT solver needs for basic store-chain reasoning.
///
/// Matches Z3's architecture: ROW1 (axiom 1) is always eager, ROW2b
/// (axiom 2b upward) is deferred to `final_check_eh` (#6546 Packet 4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::executor) enum ArrayAxiomMode {
    /// Generate all axioms eagerly: structural + ROW1 + ROW2b.
    /// Used by BV-array routes and paths without a lazy `ArraySolver`.
    EagerAll,
    /// Generate structural + ROW1 eagerly; defer ROW2b to
    /// `ArraySolver::final_check()`. Matches Z3's default behavior
    /// where `assert_store_axiom1` is always eager but `assert_store_axiom2`
    /// with `m_array_delay_exp_axiom=true` defers expensive instances.
    /// Used by TheoryCombiner-backed array routes (#6546 Packet 4).
    LazyRow2FinalCheck,
}

impl Executor {
    /// Inject the eager Bool-arg congruence lemmas
    /// `\/_i ~(a_i = b_i) \/ (f(ā) = f(b̄))` for every reachable pair of UF
    /// applications that differ only in Bool-sorted argument positions.
    ///
    /// SOUND BY CONSTRUCTION: each clause is an instance of the EUF congruence
    /// axiom, i.e. a theory tautology, so it can neither create nor destroy a
    /// model — only expose the Bool-arg equalities to the SAT skeleton, where
    /// DPLL(T) can branch on them. See the long-form rationale at the call site
    /// in `solve_euf`; the scope rule (NON-incremental only) is preserved here
    /// so the measured incremental completeness collapse cannot recur.
    ///
    /// Extracted from `solve_euf` so the ARRAY-carrying routes can share it:
    /// `purify_bool_args` hoists a compound Bool UF argument (e.g. the array
    /// read in `(g (select s1 5))`) to a fresh `boolarg` proxy, and on the
    /// AUFLIA/Array+EUF routes nothing then ties that proxy's truth value back
    /// to the `true`/`false` constant the sibling application `(g true)` uses —
    /// so `(assert (= (g true) false)) (assert (select s1 5)) (assert (g
    /// (select s1 5)))` answered `unknown` where z3 answers `unsat`. That is
    /// the same Bool-arg gap this lemma already closes on the pure-EUF route.
    ///
    /// `declared_uf_heads_only` restricts the emission to NON-builtin heads.
    /// The collector's structural scan admits any named application with a
    /// Bool-sorted argument, which on an array problem includes `select` — and
    /// `select` congruence is the ARRAY theory's own obligation, already
    /// discharged by the finite-index extensionality closure. Emitting it here
    /// too is sound but not inert: it adds equality candidates the route-level
    /// closure then expands, which moved
    /// `smt.array.finite_ext.emitted_equalities` from 3 to 5 on the QF_AX
    /// nested-extensionality gate (verdict unchanged, telemetry pin broken).
    /// The pure-EUF caller passes `false` and stays byte-identical.
    pub(in crate::executor) fn inject_bool_arg_congruence_lemmas(
        &mut self,
        declared_uf_heads_only: bool,
    ) {
        if self.incremental_mode {
            return;
        }
        let reachable = reachable_term_set(&self.ctx.terms, &self.ctx.assertions);
        let lemmas = collect_bool_arg_congruence_lemmas(&self.ctx.terms, &reachable);
        if lemmas.is_empty() {
            return;
        }
        let mut existing: HashSet<TermId> = HashSet::default();
        for &assertion in &self.ctx.assertions {
            existing.insert(assertion);
        }
        let mut seen: HashSet<(TermId, TermId)> = HashSet::default();
        for lemma in lemmas {
            if declared_uf_heads_only {
                let head_is_builtin = match self.ctx.terms.get(lemma.app_a) {
                    TermData::App(sym, _) => crate::features::is_builtin_symbol_name(sym.name()),
                    _ => true,
                };
                if head_is_builtin {
                    continue;
                }
            }
            if !seen.insert((lemma.app_a, lemma.app_b)) {
                continue;
            }
            // Consequent: f(a) = f(b). Skip degenerate self-equalities.
            let app_eq = self.ctx.terms.mk_eq(lemma.app_a, lemma.app_b);
            // Build clause literals: ~(a_i = b_i) for each differing Bool
            // position, plus the consequent app_eq.
            let mut clause_lits: Vec<TermId> = Vec::with_capacity(lemma.bool_pairs.len() + 1);
            for (a, b) in &lemma.bool_pairs {
                let arg_eq = self.ctx.terms.mk_eq(*a, *b);
                let not_arg_eq = self.ctx.terms.mk_not(arg_eq);
                clause_lits.push(not_arg_eq);
            }
            clause_lits.push(app_eq);
            let clause = self.ctx.terms.mk_or(clause_lits);
            // Re-entry guard: the array routes inject before dispatch and
            // `solve_euf` injects again on its own entry. Hash-consing makes the
            // repeat clause the same `TermId`, so skipping it keeps the
            // assertion window byte-identical to the single-injection case.
            if existing.contains(&clause) {
                continue;
            }
            self.ctx.assertions.push(clause);
        }
    }

    /// Check whether a term is in scope for array axiom generation (#6726).
    /// Returns `true` when no scope filter is active (non-incremental mode),
    /// when the term was created during the current fixpoint (idx >= start_len),
    /// or when the term is reachable from current assertions.
    #[inline]
    fn term_in_array_scope(&self, term_id: TermId) -> bool {
        // A term built over a witness only a PREVIOUS query could name is out
        // of scope no matter what the reachability filter says — see
        // `array_axiom_dead_skolems`. This is checked first because it is the
        // one exclusion that also applies when no scope filter is active at
        // all, which is the ordinary state of a non-incremental solve.
        if self.term_indexes_dead_skolem(term_id) {
            return false;
        }
        match &self.array_axiom_scope {
            None => true,
            Some((reachable, start_len)) => {
                (term_id.0 as usize) >= *start_len || reachable.contains(&term_id)
            }
        }
    }

    /// Whether `term_id` IS, or is applied directly to, a dead engine-minted
    /// witness from an earlier query (see `array_axiom_dead_skolems`).
    ///
    /// One level deep is exactly the leak surface: the whole-store scans admit
    /// `select`/`store`/`=` applications and then use their INDEX argument as
    /// an axiom index, so a dead witness reaches axiom generation only as a
    /// direct operand. Deeper occurrences are reached through their own
    /// enclosing application, which this same test declines.
    #[inline]
    fn term_indexes_dead_skolem(&self, term_id: TermId) -> bool {
        if self.array_axiom_dead_skolems.is_empty() {
            return false;
        }
        if self.array_axiom_dead_skolems.contains(&term_id) {
            return true;
        }
        match self.ctx.terms.get(term_id) {
            TermData::App(_, args) => args
                .iter()
                .any(|arg| self.array_axiom_dead_skolems.contains(arg)),
            _ => false,
        }
    }

    /// True when the TermStore holds a free quantifier `Var` node that is NOT
    /// reachable from the current (ground) assertions — i.e. a leftover ghost of
    /// a finite-domain-expanded / skolemized quantifier. After expansion replaces
    /// `(forall ((v Bool)) (= (select a v) (select b v)))` with its ground
    /// conjunction, the original `(select a v)` terms (index = the now-free `v`)
    /// remain as dead terms in the ordinary append-only history. If the
    /// array-axiom fixpoint were to treat that free `v` as a witness index,
    /// sharing one free Bool `v`
    /// as the extensionality / ROW witness across many array (dis)equalities
    /// over-constrains the problem and yields spurious UNSAT. Detecting these
    /// ghosts lets `solve_array_euf` enable reachability scoping, which keeps
    /// legitimate fixpoint-created witnesses (idx >= start_len) and reachable
    /// terms while excluding the unreachable ghosts. (#dis514 wrong-unsat)
    pub(in crate::executor) fn has_unreachable_var_ghost(
        &self,
        reachable: &HashSet<TermId>,
    ) -> bool {
        let len = self.ctx.terms.len();
        for idx in 0..len {
            let t = TermId::new(idx as u32);
            if matches!(self.ctx.terms.get(t), TermData::Var(..)) && !reachable.contains(&t) {
                return true;
            }
        }
        false
    }

    /// Cheap `Var`-tag scan: true if the TermStore holds any `Var` node at all.
    /// Used to gate the more expensive `reachable_term_set` + ghost check — a
    /// quantifier-free problem has no `Var` terms, so the ghost path is skipped.
    pub(in crate::executor) fn store_has_free_var(&self) -> bool {
        let len = self.ctx.terms.len();
        (0..len).any(|idx| {
            matches!(
                self.ctx.terms.get(TermId::new(idx as u32)),
                TermData::Var(..)
            )
        })
    }

    #[allow(dead_code)]
    fn push_array_axiom_assertion(&mut self, axiom: TermId) {
        self.push_array_axiom_assertion_site(axiom, "unknown")
    }

    /// Debug-only helper: pretty-print a term to an s-expression up to
    /// the given depth. Used by `AY_DEBUG_ARRAY_AXIOM_SITE` tracing.
    fn pretty_print_term_for_debug(&self, term: TermId, depth: u32) -> String {
        if depth == 0 {
            return format!("#{}", term.0);
        }
        match self.ctx.terms.get(term) {
            TermData::Const(c) => format!("{c:?}"),
            TermData::Var(name, _) => format!("{}#{}", name, term.0),
            TermData::App(sym, args) => {
                let mut s = format!("({}#{}", sym.name(), term.0);
                for a in args {
                    s.push(' ');
                    s.push_str(&self.pretty_print_term_for_debug(*a, depth - 1));
                }
                s.push(')');
                s
            }
            TermData::Not(inner) => {
                format!(
                    "(not#{} {})",
                    term.0,
                    self.pretty_print_term_for_debug(*inner, depth - 1)
                )
            }
            TermData::Ite(c, t, e) => {
                format!(
                    "(ite#{} {} {} {})",
                    term.0,
                    self.pretty_print_term_for_debug(*c, depth - 1),
                    self.pretty_print_term_for_debug(*t, depth - 1),
                    self.pretty_print_term_for_debug(*e, depth - 1)
                )
            }
            _ => format!("#{}", term.0),
        }
    }

    // `pub(in crate::executor)`: also used by the RoundingMode finite-domain
    // pass (executor/rm_domain.rs call sites in check_sat.rs /
    // check_sat_assuming.rs) so its injected axioms carry the same
    // proof/unsat-core provenance as the array/enum-coverage axioms.
    pub(in crate::executor) fn push_array_axiom_assertion_site(
        &mut self,
        axiom: TermId,
        site: &str,
    ) {
        // Do not retain or certify a generator result that simplified to the
        // Boolean constant `true`.  Besides wasting assertion/proof space, the
        // old site-based fallback labelled such tautologies as ROW2 even though
        // they contain no read-over-write instance at all.
        if axiom == self.ctx.terms.true_term() {
            return;
        }
        self.trace_array_axiom_assertion_site(axiom, site);
        self.ctx.assertions.push(axiom);
        self.record_array_axiom_proof(axiom);
    }

    /// Ensure a cached solver axiom is installed in the current assertion
    /// view and registered in the current proof session.
    ///
    /// Assertion swaps and proof-tracker checkpoints have independent
    /// lifetimes: an axiom term can remain live while either its assertion or
    /// its proof lemma is absent. Cache hits therefore deduplicate the former
    /// but always replay the latter. Returns whether a new assertion entry was
    /// appended.
    pub(in crate::executor) fn ensure_array_axiom_assertion_site(
        &mut self,
        axiom: TermId,
        site: &str,
    ) -> bool {
        if axiom == self.ctx.terms.true_term() {
            return false;
        }
        let inserted = if self.ctx.assertions.contains(&axiom) {
            false
        } else {
            self.trace_array_axiom_assertion_site(axiom, site);
            self.ctx.assertions.push(axiom);
            true
        };
        self.record_array_axiom_proof(axiom);
        inserted
    }

    /// Batch form of [`Self::ensure_array_axiom_assertion_site`].
    ///
    /// Exact finite-array closure can replay thousands of cached axioms in one
    /// invocation. Re-scanning the assertion vector for every replay makes that
    /// path quadratic, so its caller builds one exact active-membership set and
    /// updates it alongside the assertion vector through this helper.
    pub(in crate::executor) fn ensure_array_axiom_assertion_site_with_active_set(
        &mut self,
        axiom: TermId,
        site: &str,
        active_assertions: &mut HashSet<TermId>,
    ) -> bool {
        if axiom == self.ctx.terms.true_term() {
            return false;
        }
        let inserted = active_assertions.insert(axiom);
        if inserted {
            self.trace_array_axiom_assertion_site(axiom, site);
            self.ctx.assertions.push(axiom);
        }
        self.record_array_axiom_proof(axiom);
        inserted
    }

    fn trace_array_axiom_assertion_site(&self, axiom: TermId, site: &str) {
        if ay_core::debug_channel_active(ay_core::DebugChannel::ArrayAxiomSite) {
            let pretty = self.pretty_print_term_for_debug(axiom, 3);
            eprintln!(
                "[array_axiom] site={} axiom=#{} pretty={}",
                site, axiom.0, pretty
            );
        }
    }

    fn record_array_axiom_proof(&mut self, axiom: TermId) {
        if self.produce_proofs_enabled() {
            // Attribution is a semantic boundary: only the checker's exact
            // array/EUF recognizers may choose a rule. Other consequences stay
            // `Generic`; the diagnostic `site` string carries no authority.
            let clause = match self.ctx.terms.get(axiom) {
                TermData::App(sym, args) if sym.name() == "or" => args.clone(),
                _ => vec![axiom],
            };
            // Finite enum carriers cannot be authenticated from the term store:
            // datatype applications intentionally retain `Uninterpreted` sorts.
            // Supply the same exact declaration/signature authority used by
            // strict proof checking so enum expansion lemmas receive an honest
            // finite-array rule instead of falling back to explicit trust.
            let array_kind = ay_proof::recognize_array_theory_lemma(&self.ctx.terms, &clause)
                .or_else(|| {
                    // Only enum-carrier finite-array schemas need declaration
                    // authority. Keep the ubiquitous ROW/default/congruence
                    // proof path allocation-free, and do not let an unrelated
                    // malformed datatype registry demote a schema the ordinary
                    // term-store recognizer already authenticated.
                    let datatype_declarations = self.datatype_decls_for_strict_proof();
                    let constructor_selectors = self.ctor_selector_decls_for_strict_proof();
                    let datatype_member_signatures =
                        self.datatype_member_signatures_for_strict_proof()?;
                    ay_proof::recognize_array_theory_lemma_with_typed_context(
                        &self.ctx.terms,
                        &clause,
                        &datatype_declarations,
                        &constructor_selectors,
                        &datatype_member_signatures,
                    )
                });
            if let Some(kind) = array_kind {
                let _ = self
                    .proof_tracker
                    .add_theory_lemma_with_kind(vec![axiom], kind);
            } else if ay_proof::recognize_euf_congruent(&self.ctx.terms, &clause) {
                let _ = self
                    .proof_tracker
                    .add_theory_lemma_with_kind(vec![axiom], TheoryLemmaKind::EufCongruent);
            } else {
                let _ = self.proof_tracker.add_explicit_trust_lemma(vec![axiom]);
            }
        }
    }

    /// #mgr-uf-ackermann: emit pairwise functional-congruence (Ackermann)
    /// instances for ground uninterpreted applications of the same symbol:
    /// `(= a1 b1) ∧ … ∧ (= an bn) → (= f(a…) f(b…))`.
    ///
    /// Demand channel for the UFLIA model-based combination gap (U4_rand
    /// class): the lazy Nelson-Oppen loop only enforces congruence between
    /// application terms whose arguments are EUF-equal by *assertion*; a
    /// candidate LIA model may then assign two argument tuples the same
    /// values while their applications differ — a first-order-inconsistent
    /// model the independent gate rightly rejects, fail-closing to unknown.
    /// Asserting the Ackermann instances makes functional consistency visible
    /// to the SAT+LIA search itself, so it either separates the argument
    /// values or merges the application values.
    ///
    /// SOUNDNESS: every instance is a congruence tautology valid in every
    /// interpretation of the uninterpreted symbols, recorded as a theory
    /// lemma through `push_array_axiom_assertion_site`; verdicts remain
    /// licensed by the solve pipeline + the independent model gate.
    /// BOUND: pairs within each same-symbol group; `cap` fences quadratic
    /// blowup (the stage only runs on otherwise-unknown ground problems).
    /// Returns the number of clauses emitted.
    pub(in crate::executor) fn add_uf_ackermann_congruence_clauses(&mut self, cap: usize) -> usize {
        use ay_core::kani_compat::DetHashMap;
        let should_stop = self.make_should_stop();
        let mut groups: DetHashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> =
            DetHashMap::default();
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if let TermData::App(sym, args) = self.ctx.terms.get(term_id) {
                if args.is_empty() || crate::features::is_builtin_symbol_name(sym.name()) {
                    continue;
                }
                groups
                    .entry((sym.name().to_string(), args.len()))
                    .or_default()
                    .push((term_id, args.clone()));
            }
        }
        let mut keys: Vec<(String, usize)> = groups.keys().cloned().collect();
        keys.sort_unstable();
        let mut emitted = 0_usize;
        for key in keys {
            let apps = &groups[&key];
            for i in 0..apps.len() {
                for j in (i + 1)..apps.len() {
                    if emitted >= cap || should_stop() {
                        return emitted;
                    }
                    let (lhs_app, ref lhs_args) = apps[i];
                    let (rhs_app, ref rhs_args) = apps[j];
                    if self.ctx.terms.sort(lhs_app) != self.ctx.terms.sort(rhs_app)
                        || lhs_args
                            .iter()
                            .zip(rhs_args.iter())
                            .any(|(&a, &b)| self.ctx.terms.sort(a) != self.ctx.terms.sort(b))
                    {
                        // Same-named symbol at different signatures: skip.
                        continue;
                    }
                    let mut disj: Vec<TermId> = Vec::with_capacity(lhs_args.len() + 1);
                    for (&a, &b) in lhs_args.iter().zip(rhs_args.iter()) {
                        if a == b {
                            continue;
                        }
                        let arg_eq = self.ctx.terms.mk_eq(a, b);
                        disj.push(self.ctx.terms.mk_not(arg_eq));
                    }
                    let app_eq = self.ctx.terms.mk_eq(lhs_app, rhs_app);
                    disj.push(app_eq);
                    let clause = if disj.len() == 1 {
                        disj[0]
                    } else {
                        self.ctx.terms.mk_or(disj)
                    };
                    self.push_array_axiom_assertion_site(clause, "uf_ackermann");
                    emitted += 1;
                }
            }
        }
        emitted
    }

    /// Solve QF_UF using eager DPLL(T) with theory-SAT interleaving.
    ///
    /// Uses `solve_incremental_split_loop_pipeline!` with `eager_extension: true`
    /// so the EUF solver runs as a TheoryExtension during BCP. This ensures all
    /// theory-relevant equality atoms are assigned by the SAT solver — the lazy
    /// pipeline could leave them unassigned and miss congruence closure conflicts.
    ///
    /// Or-eq-lemma implications (transitivity shortcuts for eq_diamond patterns)
    /// are injected as assertion-level implications that flow through Tseitin
    /// encoding automatically.
    pub(in crate::executor) fn solve_euf(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Lift ITEs from equalities involving uninterpreted sorts.
        self.ctx.assertions = self.ctx.terms.lift_arithmetic_ite_all(&self.ctx.assertions);

        // Pre-compute or_eq_lemma pairs and inject as assertion-level
        // implications (¬or_term ∨ eq_term). These flow through Tseitin
        // encoding via pipeline_incremental_setup!, ensuring eq_terms become
        // active theory atoms via collect_active_theory_atoms.
        {
            let mut seen: HashSet<(TermId, TermId)> = HashSet::default();
            let len = self.ctx.terms.len();
            for idx in 0..len {
                let t = TermId(idx as u32);
                if let Some((a, b)) = or_implies_eq_endpoints(&self.ctx.terms, t) {
                    let eq_term = self.ctx.terms.mk_eq(a, b);
                    if seen.insert((t, eq_term)) {
                        let not_or = self.ctx.terms.mk_not(t);
                        let implication = self.ctx.terms.mk_or(vec![not_or, eq_term]);
                        self.ctx.assertions.push(implication);
                    }
                }
            }
        }

        // #bool-arg-congruence: Inject functional-congruence lemmas for UF
        // applications that differ only in Bool-sorted argument positions.
        //
        // When a UF `f` is applied to Bool arguments — e.g. `fb(true)` vs
        // `fb(p0)`, or CLEARSY's `(bool (and ...))` vs `(bool (and ...'))` — the
        // congruence axiom requires `f(a) = f(b)` whenever the Bool args `a`, `b`
        // share a truth value. Those Bool args appear ONLY inside opaque UF
        // applications, so the SAT layer never branches on them and the EUF
        // truth-value class merge never fires (the args never reach EUF's
        // `assigns`). The result is a non-congruent model accepted as SAT.
        //
        // Injecting the lemma `(/\_i a_i = b_i) -> (f(a) = f(b))` as the clause
        // `\/_i ~(a_i = b_i) \/ (f(a) = f(b))` flows the Bool-arg equalities and
        // the application equality through Tseitin into the SAT skeleton, so
        // DPLL(T) decides the Bool args and EUF enforces the congruence. This is
        // sound (a valid axiom instance) and complete over the Bool-arg gap.
        //
        // Always injected in the single-shot case (the former
        // AY_EUF_BOOL_ARG_CONGRUENCE=0 opt-out is removed; ON was the
        // default).
        //
        // SCOPE: eager lemma injection runs in NON-incremental (single
        // check-sat) mode only. In deep incremental sessions (e.g. the
        // 20190906-CLEARSY proof-obligation files: 100+ check-sats, dense
        // equality structure) the lemmas' fresh equality atoms inflate the EUF
        // proof-forest and the per-conflict `explain()` walk, collapsing
        // completeness (121 -> ~50 solved check-sats — measured). Those
        // incremental files are already SOUND under the base solver (0 z3
        // conflicts across the CLEARSY sweep), so skipping the lemma there costs
        // no soundness. The lemma is reserved for the single-shot case (the
        // false-SAT witnesses, fuzz) where Bool UF-args are buried and would
        // otherwise never reach EUF. (The former
        // `AY_EUF_BOOL_ARG_LEMMA_INCREMENTAL=1` incremental force-enable is
        // removed; OFF in incremental mode is the measured-sound default.)
        self.inject_bool_arg_congruence_lemmas(false);

        // #bool-arg-congruence: the SOUND post-SAT model-validation guard runs in
        // BOTH incremental and non-incremental modes. It only ever downgrades a
        // candidate `Sat` to `Unknown` (never asserts UNSAT), so it carries zero
        // false-UNSAT risk. In incremental mode it is the soundness net for the
        // Bool-arg congruence FALSE-SATs (e.g. `uf_inc_1560`: `pb` distinguishes
        // `fb(p1)` / `fb(false)`, forcing `p1 = true`, which then refutes a
        // duplicate-`distinct` — a backward-congruence chain the SAT layer never
        // branches on because the Bool args live only inside opaque UF apps). The
        // base solver alone false-SATs these (it accepts a non-congruent model);
        // the eager congruence LEMMA that closes them non-incrementally is unsound
        // across push/pop (its injected clauses leak through the persistent SAT
        // state and emit false UNSATs), so the guard — not the lemma — is the
        // incremental fix.
        //
        // Completeness cost: the guard refuses to certify a non-congruent model
        // even when a *different* congruent model exists (z3 finds one), so on
        // dense CLEARSY proof-obligation files it downgrades a small number of
        // SAT verdicts that were backed by non-congruent models to `Unknown`
        // (measured ~0.6% of aligned check-sats). This is a sound trade: those
        // verdicts were certified against models that violate functional
        // congruence. `AY_EUF_BOOL_ARG_VALIDATE=0` disables the guard entirely
        // for experiments.
        // #clearsy-repair: targeted Bool-arg congruence repair (DEFAULT OFF).
        //
        // The post-SAT guard downgrades `Sat` -> `Unknown` when the candidate
        // model is non-congruent over Bool UF-args, even where a *congruent*
        // model exists (z3 finds one). On the 20190906-CLEARSY incremental
        // proof-obligation files that costs 57 otherwise-decidable check-sats
        // (measured: Inc QF_Equality 14,001 of a 14,060 ceiling).
        //
        // Rather than surrender, re-solve with the congruence axiom instances
        // for exactly the app pairs the guard found FORCED equal under that
        // model. Injecting a lemma for every Bool-arg pair in the reachable set
        // is measured DEAD here (completeness 121 -> ~50); this set is
        // model-specific and small, which is what makes it viable.
        //
        // SOUND BY CONSTRUCTION: only valid instances of the congruence axiom
        // are added, so no sat/unsat verdict can flip; the lemmas ride through
        // `solve_euf_once(Some(..))`, whose isolation discards them on exit so
        // they cannot leak into a later check-sat; and exhausting the attempt
        // bound returns the guard's original `Unknown`, i.e. today's behaviour.
        //
        // UNMEASURED — gate stays OFF until a CLEARSY-sweep differential shows
        // the completeness collapse does not recur at this granularity.
        if !bool_arg_repair_enabled() {
            return self.solve_euf_once(None);
        }

        const MAX_REPAIR_ROUNDS: usize = 4;
        ay_euf::clear_bool_arg_repair_candidates();
        let base_assertions = self.ctx.assertions.clone();
        let mut extra: Vec<TermId> = Vec::new();
        let mut seen: HashSet<(TermId, TermId)> = HashSet::default();

        for _round in 0..=MAX_REPAIR_ROUNDS {
            let run_assertions = if extra.is_empty() {
                None
            } else {
                let mut v = base_assertions.clone();
                v.extend(extra.iter().copied());
                Some(v)
            };
            let result = self.solve_euf_once(run_assertions)?;
            if !matches!(result, SolveResult::Unknown) {
                return Ok(result);
            }
            let candidates = ay_euf::take_bool_arg_repair_candidates();
            let mut added = false;
            for (app_a, app_b) in candidates {
                let key = if app_a.0 <= app_b.0 {
                    (app_a, app_b)
                } else {
                    (app_b, app_a)
                };
                if !seen.insert(key) {
                    continue;
                }
                if let Some(lemma) = self.bool_arg_congruence_lemma(app_a, app_b) {
                    extra.push(lemma);
                    added = true;
                }
            }
            if !added {
                return Ok(result);
            }
        }
        // Attempt bound exhausted: fall back to the guard's verdict.
        self.solve_euf_once(None)
    }

    /// Build `(/\_i a_i = b_i) -> f(a) = f(b)` as the clause
    /// `\/_i ~(a_i = b_i) \/ (f(a) = f(b))` for one forced-congruence app pair,
    /// restricted to the Bool-sorted argument positions where the two differ.
    ///
    /// Returns `None` when the pair is not two same-arity applications, or when
    /// no Bool-sorted position actually differs (nothing to constrain).
    fn bool_arg_congruence_lemma(&mut self, app_a: TermId, app_b: TermId) -> Option<TermId> {
        if app_a == app_b {
            return None;
        }
        let (args_a, args_b) = match (self.ctx.terms.get(app_a), self.ctx.terms.get(app_b)) {
            (TermData::App(sym_a, aa), TermData::App(sym_b, bb)) => {
                if sym_a != sym_b || aa.len() != bb.len() {
                    return None;
                }
                (aa.clone(), bb.clone())
            }
            _ => return None,
        };
        let mut bool_pairs: Vec<(TermId, TermId)> = Vec::new();
        for (&a, &b) in args_a.iter().zip(args_b.iter()) {
            if a == b {
                continue;
            }
            if self.ctx.terms.sort(a) == &Sort::Bool && self.ctx.terms.sort(b) == &Sort::Bool {
                bool_pairs.push((a, b));
            } else {
                // A differing NON-Bool position means these apps are not related
                // by the Bool-arg gap; emitting the lemma would be unhelpful (and
                // its antecedent would not be the congruence trigger).
                return None;
            }
        }
        if bool_pairs.is_empty() {
            return None;
        }
        let mut clause_lits: Vec<TermId> = Vec::with_capacity(bool_pairs.len() + 1);
        for (a, b) in bool_pairs {
            let arg_eq = self.ctx.terms.mk_eq(a, b);
            clause_lits.push(self.ctx.terms.mk_not(arg_eq));
        }
        let app_eq = self.ctx.terms.mk_eq(app_a, app_b);
        clause_lits.push(app_eq);
        Some(self.ctx.terms.mk_or(clause_lits))
    }

    /// One EUF solve attempt, optionally with a REPLACEMENT assertion list.
    ///
    /// `assertions: Some(v)` routes through `with_isolated_incremental_state`'s
    /// swap-and-restore, which also installs a fresh `IncrementalTheoryState`
    /// (and therefore a fresh `persistent_sat`). Anything the attempt Tseitin-
    /// encodes is discarded on exit, so extra lemmas passed here CANNOT leak into
    /// a later check-sat — the property the targeted congruence repair relies on.
    fn solve_euf_once(&mut self, assertions: Option<Vec<TermId>>) -> Result<SolveResult> {
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        self.with_isolated_incremental_state(assertions, |this| {
            solve_incremental_split_loop_pipeline!(this,
                tag: "EUF",
                persistent_sat_field: persistent_sat,
                create_theory: {
                    // The post-SAT Bool-arg congruence guard stays at its EUF
                    // default (ON via `AY_EUF_BOOL_ARG_VALIDATE`) in both
                    // incremental and non-incremental mode — it only downgrades
                    // Sat -> Unknown, never asserts UNSAT.
                    EufSolver::new(&this.ctx.terms)
                },
                extract_models: |theory| {
                    theory.scope_model_to_roots(&this.ctx.assertions);
                    let euf = theory.extract_model();
                    theory.clear_model_scope();
                    TheoryModels {
                        euf: Some(euf),
                        ..TheoryModels::default()
                    }
                },
                max_splits: 1,
                pre_theory_import: |_theory, _lc, _hc, _ds| {},
                post_theory_export: |_theory| {
                    (vec![], Default::default(), Default::default())
                },
                eager_extension: true,
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.expired()
                },
                // #6812 sound relaxation (QF_ALIA M3): accept a post-expression-split
                // propositional UNSAT ONLY when a FRESH UF+LIA combiner re-derives
                // UNSAT from the ORIGINAL `ctx.assertions` (verify-before-accept via
                // `verify_post_split_unsat_via_fresh_solve`). Non-optimistic: any
                // fresh verdict other than Unsat escalates to Unknown as before.
                // Rescues Ackermannized array-UNSAT cores (e.g. pp-bloaddata) that
                // solve_euf refutes only after expression splits.
                verify_unsat_after_splits: true
            )
        })
    }
}
