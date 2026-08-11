// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native finite-set theory solving (QF_SET / QF_SETLIA).
//!
//! Sets are modelled on the membership carrier `Set(T) = Array(T → Bool)`. The
//! array solver decides membership (`select` read-through) and set equality
//! (extensionality); the native [`ay_set::SetSolver`] adds cardinality and
//! subset reasoning; LIA decides the integer arithmetic of `set.card` terms.
//!
//! ## Card-axiom injection (the seq.len pattern)
//!
//! Because a `TheorySolver` only holds an immutable `&TermStore` during
//! `check()`, the ground cardinality axioms are injected here (where
//! `&mut TermStore` is available) before solving, exactly as `seq.len` axioms
//! are injected for QF_SEQLIA:
//!
//! - `card(s) ≥ 0` for **every** `set.card` term (the sound card↔LIA bridge —
//!   asserted for every card, never selectively).
//! - `card((as set.empty (Set T))) = 0`.
//! - the definitional recurrence over an empty-rooted (covered) store chain.
//! - for any other carrier — a bare set variable, or a chain rooted at one —
//!   the **membership lower bound** `card(s) ≥ #{distinct probed members of s}`.
//!   Without it membership and cardinality were decoupled and
//!   `(set.member 1 s) ∧ (= 0 (set.card s))` was wrongly SAT.
//!
//! ## Fail-closed contract
//!
//! Out-of-fragment set operators (polymorphic / higher-order image:
//! `set.map`, `set.filter`, `set.fold`, `set.comprehension`, `set.choose`,
//! `set.complement`, `set.universe`) are **not** decided. Their presence yields
//! `Unknown` (incomplete) rather than a guessed SAT/UNSAT verdict.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use num_bigint::BigInt;
use num_traits::Zero;

use super::super::Executor;
use super::solve_harness::TheoryModels;
use super::MAX_SPLITS_LIA;
use crate::combined_solvers::UfSetLiaSolver;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use ay_core::term::{Symbol, TermData, TermId};
use ay_set::{OP_CARD, OP_EMPTY, OP_SUBSET, OUT_OF_FRAGMENT_OPS};

impl Executor {
    /// Solve the native finite-set theory (QF_SET / QF_SETLIA).
    ///
    /// Injects ground cardinality axioms, then solves with [`UfSetLiaSolver`].
    /// Returns `Unknown` (fail-closed) when any out-of-fragment set operator is
    /// present.
    pub(in crate::executor) fn solve_set_lia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // SOUNDNESS (#dt-set-ite-lift wrong-sat): Shannon-expand `(select (ite c A
        // B) i)` -> `(ite c (select A i) (select B i))` so the inner
        // `select`-over-`store` reaches the ROW axioms. The QF_UF/AUFLIA routes
        // already lift; the set/Bool-array route did not, so
        // `(not (select (ite c k (store k 0 true)) 0)) ∧ (not c)` was wrongly SAT.
        self.ctx.assertions = self.ctx.terms.lift_arithmetic_ite_all(&self.ctx.assertions);

        // Fail-closed guard: out-of-fragment set operators are not decided.
        if self.assertions_contain_out_of_fragment_set_ops() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        // Fail-closed guard (#set-card-underconstrained): a `set.card` applied to
        // a store-chain set (the elaborated form of `set.singleton`/`set.insert`)
        // is structurally decided only when the chain is rooted at the empty set
        // (const-false carrier); the recurrence `card(insert(s,e)) = card(s) +
        // ite(member(s,e), 0, 1)` plus `card(empty)=0` is injected below for those
        // covered shapes. Chains rooted at an opaque set variable have no
        // structural count and are bounded only by the `card >= 0` bridge, which
        // admits a wrong `sat`; demote those to Unknown (sound).
        if self.set_card_has_uncovered_store_chain_arg() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        // Fail-closed guard (#set-subset-aliased-wrong-sat): a `set.subset` atom
        // whose operands are set VARIABLES aliased via `(= v <set-expr>)` is not
        // tied to the alias's structure by the witness-based subset saturation in
        // `ay_set` (which only fires on present `member` atoms — absent here). The
        // empty-resolved / covered-store-chain resolutions ARE structurally
        // decidable and are tied below via `collect_set_subset_axioms`; an aliased
        // subset whose operand resolves to something not structurally decidable
        // (variable-rooted / symbolic chain) is demoted to Unknown here (sound).
        if self.set_subset_has_undecidable_aliased_arg() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        // Inject ground cardinality axioms (card >= 0 for every card; card(empty)=0;
        // structural insert/remove recurrence for empty-rooted store chains).
        let card_axioms = self.collect_set_card_axioms();
        if !card_axioms.is_empty() {
            // The card axioms carry `ite(member, .., ..)` in ARITHMETIC position
            // (the store-chain recurrence and the membership lower bound). The
            // whole-assertion lift above ran before this injection, so lift the
            // axioms too — otherwise the `ite` never reaches LIA and a formula
            // the bound refutes comes back `unknown` instead of `unsat`.
            let card_axioms = self.ctx.terms.lift_arithmetic_ite_all(&card_axioms);
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx
                .assertions
                .extend(card_axioms.into_iter().filter(|axiom| seen.insert(*axiom)));
        }

        // Inject structural subset axioms (#set-subset-aliased-wrong-sat): for a
        // `set.subset` atom with an aliased operand whose resolution is
        // structurally decided (empty subset, reflexive, or both sides
        // empty-or-covered), tie the opaque atom to that Boolean constant so the
        // witness saturation no longer has to discover it (and so the aliased
        // empty / disjoint cases decide correctly).
        let subset_axioms = self.collect_set_subset_axioms();
        if !subset_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                subset_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Skolem witnesses for subset atoms (#set-subset-transitivity-wrong-sat):
        // hand the member-monotonicity saturation the `w∈X`, `w∉Y` atoms a NEGATED
        // subset implies, so e.g. `A⊆B ∧ B⊆C ∧ ¬(A⊆C)` closes to UNSAT instead of
        // a spurious empty-set `sat`. Sound (Skolemization, equisatisfiable;
        // vacuous when the subset atom is true).
        let subset_witnesses = self.collect_negated_subset_witnesses();
        if !subset_witnesses.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                subset_witnesses
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Inject restricted array-extensionality for set equality / subset over
        // store-chains (#set-route-extensionality): the native SetLIA route lacks
        // the extensionality the QF_AUFLIA route uses, so `{0}={1}` / `{0}⊆{1}`
        // were wrongly SAT.
        let ext_axioms = self.collect_set_extensionality_axioms();
        if !ext_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx
                .assertions
                .extend(ext_axioms.into_iter().filter(|axiom| seen.insert(*axiom)));
        }

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        solve_incremental_split_loop_pipeline!(self,
            tag: "SetLIA",
            persistent_sat_field: lia_persistent_sat,
            create_theory: UfSetLiaSolver::new(&self.ctx.terms),
            extract_models: |theory| {
                let (euf_model, array_model, lia_model) = theory.extract_models();
                TheoryModels {
                    euf: Some(euf_model),
                    array: Some(array_model),
                    lia: lia_model,
                    ..TheoryModels::default()
                }
            },
            max_splits: MAX_SPLITS_LIA,
            pre_theory_import: |theory, lc, hc, ds| {
                theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                theory.import_dioph_state(std::mem::take(ds));
            },
            post_theory_export: |_theory| {
                let (lc, hc) = _theory.take_learned_state();
                let ds = _theory.take_dioph_state();
                (lc, hc, ds)
            },
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                    || solve_deadline.expired()
            }
        )
    }

    /// Solve QF_SET / QF_SETLIA with check-sat-assuming.
    ///
    /// Mirrors [`solve_set_lia`](Self::solve_set_lia) but temporarily adds
    /// assumptions to the assertion set under an isolated incremental scope.
    pub(in crate::executor) fn solve_set_lia_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let mut scoped_assertions = Vec::with_capacity(assertions.len() + assumptions.len());
        scoped_assertions.extend(assertions.iter().copied());
        scoped_assertions.extend(assumptions.iter().copied());

        let result =
            self.with_isolated_incremental_state(Some(scoped_assertions), Self::solve_set_lia);

        match result {
            Ok(SolveResult::Unsat(_)) => {
                self.last_assumption_core = Some(assumptions.to_vec());
                Ok(SolveResult::unsat())
            }
            Ok(SolveResult::Sat) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Unknown) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Unknown)
            }
            Err(err) => {
                self.last_assumption_core = None;
                Err(err)
            }
        }
    }

    /// Whether any assertion references an out-of-fragment set operator.
    ///
    /// These polymorphic / higher-order image operators fall outside the sound
    /// saturatable fragment; their presence forces a fail-closed `Unknown`.
    fn assertions_contain_out_of_fragment_set_ops(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if OUT_OF_FRAGMENT_OPS.contains(&name.as_str()) {
                        return true;
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::App(_, args) => {
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        false
    }

    /// True when `t` is `store(...)`, the elaborated form of
    /// `set.singleton`/`set.insert`/`set.remove`.
    fn is_set_store_term(&self, t: TermId) -> bool {
        matches!(
            self.ctx.terms.get(t),
            TermData::App(Symbol::Named(n), a) if n == "store" && a.len() == 3
        )
    }

    /// True when `t` is a set-sorted term (the membership carrier `Array(T→Bool)`).
    fn is_set_sorted(&self, t: TermId) -> bool {
        let sort = self.ctx.terms.sort(t);
        sort.is_array() && sort.array_element() == Some(&ay_core::Sort::Bool)
    }

    /// Build the set-variable alias map from top-level `(= v expr)` equalities
    /// where `v` is a set-sorted variable. Both orientations are recorded. This
    /// captures the four aliasing shapes that under-constrain `set.card`:
    ///   - `(= s (as set.empty (Set T)))`  → const-false empty carrier
    ///   - `(= s (set.remove .. (set.singleton ..)))` → covered store chain
    ///   - `(= s (set.insert e t))` over a set variable `t` → uncovered chain
    ///   - `(= s t)` chained var-to-var aliases
    ///
    /// A variable may have several recorded aliases (multiple equalities); the
    /// first non-self alias is used by [`resolve_set_alias`](Self::resolve_set_alias).
    fn build_set_alias_map(&self) -> Vec<(TermId, TermId)> {
        let mut aliases: Vec<(TermId, TermId)> = Vec::new();
        for &a in &self.ctx.assertions {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(a) {
                if name == "=" && args.len() == 2 {
                    let (l, r) = (args[0], args[1]);
                    let l_var = matches!(self.ctx.terms.get(l), TermData::Var(..));
                    let r_var = matches!(self.ctx.terms.get(r), TermData::Var(..));
                    // Only set-sorted equalities can be set aliases.
                    if !self.is_set_sorted(l) {
                        continue;
                    }
                    if l_var && l != r {
                        aliases.push((l, r));
                    }
                    if r_var && r != l {
                        aliases.push((r, l));
                    }
                }
            }
        }
        aliases
    }

    /// Resolve a set term through the alias map to its defining set expression.
    ///
    /// If `start` is a set **variable** aliased (possibly transitively) to a
    /// concrete set expression (empty carrier or store chain), returns that
    /// expression. If `start` is already a non-variable set term it is returned
    /// unchanged. If a variable has no resolving alias (or only resolves to
    /// another bare variable), the final variable is returned — so the caller
    /// sees a variable-rooted (uncovered) term and fails closed. Cycle-safe.
    fn resolve_set_alias(&self, start: TermId, aliases: &[(TermId, TermId)]) -> TermId {
        let mut cur = start;
        let mut seen: HashSet<TermId> = HashSet::default();
        loop {
            // Non-variable terms are already resolved set expressions.
            if !matches!(self.ctx.terms.get(cur), TermData::Var(..)) {
                return cur;
            }
            if !seen.insert(cur) {
                // Cycle (e.g. `(= s t)(= t s)`) — return the current variable;
                // a variable-rooted term is uncovered and fails closed.
                return cur;
            }
            // Prefer an alias to a concrete (non-variable) set expression so a
            // chained alias like `(= s t)(= t empty)` resolves `s → empty`
            // instead of getting trapped in the `s ⇄ t` reverse-equality cycle.
            // Only follow a variable→variable edge when no concrete alias exists.
            let concrete = aliases.iter().find(|(v, target)| {
                *v == cur && !matches!(self.ctx.terms.get(*target), TermData::Var(..))
            });
            let next = concrete.or_else(|| aliases.iter().find(|(v, _)| *v == cur));
            match next {
                Some((_, target)) => cur = *target,
                None => return cur,
            }
        }
    }

    /// True when `t` is the elaborated empty set: the constant-false array.
    fn is_empty_carrier(&self, t: TermId) -> bool {
        self.ctx.terms.get_const_array(t) == Some(self.ctx.terms.false_term())
    }

    /// True when `t` is a **structurally covered** store chain: a chain of
    /// `store(_, e, v)` writes with `v ∈ {true, false}` bottoming out at the
    /// constant-false empty-set carrier, AND every per-level membership test
    /// `member(inner, e) = select(inner, e)` rewrites to a Boolean *constant*.
    /// For exactly these shapes the definitional cardinality recurrence
    ///   `card(store(s,e,true))  = card(s) + ite(member(s,e), 0, 1)`   (insert)
    ///   `card(store(s,e,false)) = card(s) − ite(member(s,e), 1, 0)`   (remove)
    /// with base `card(const-false) = 0` is injected (see
    /// [`collect_set_card_axioms`](Self::collect_set_card_axioms)) and the verdict
    /// is fully decided.
    ///
    /// The constant-membership requirement is what makes coverage match the
    /// underlying SetLIA solver's actual decision power. A `set.singleton`/single
    /// `set.insert`/`set.remove` over the empty set folds `select(const-false, e)`
    /// to `false`; nested chains with concrete distinct/equal indices fold via
    /// read-over-write. A nested chain with *symbolic* indices leaves a residual
    /// `select(store(...), e)` that the combined array+LIA bridge does not decide,
    /// so it stays uncovered (fail-closed) rather than risk an `unknown` from a
    /// formula we claimed to cover.
    ///
    /// Chains rooted at a set **variable** (e.g. `(set.insert e s)` over a
    /// declared `(Set T)` variable `s`) are *not* covered: `card(s)` would then be
    /// an opaque term bounded only by `card(s) ≥ 0`, and combining that with the
    /// recurrence admits a wrong model (e.g. picking `member(s,e)=true` with
    /// `card(s)=0`, giving `card(insert(s,e))=0`). Such shapes remain fail-closed
    /// `Unknown`.
    fn is_covered_store_chain(&mut self, t: TermId) -> bool {
        let true_t = self.ctx.terms.true_term();
        let false_t = self.ctx.terms.false_term();
        let mut cur = t;
        loop {
            if self.is_empty_carrier(cur) {
                return true;
            }
            let (inner, elem, v) = match self.ctx.terms.get(cur) {
                TermData::App(Symbol::Named(n), a) if n == "store" && a.len() == 3 => {
                    (a[0], a[1], a[2])
                }
                // Anything other than a store node or the const-false base
                // (a set variable, an opaque combinator app, etc.) is not
                // covered by the structural recurrence.
                _ => return false,
            };
            if v != true_t && v != false_t {
                // A non-boolean-literal stored value is not a set-membership
                // write we can count structurally.
                return false;
            }
            // Require the membership test against the inner set to fold to a
            // Boolean constant; otherwise the residual `select` is not bridged
            // to LIA by the combined solver and the count cannot be decided.
            let member = self.ctx.terms.mk_select(inner, elem);
            if member != true_t && member != false_t {
                return false;
            }
            cur = inner;
        }
    }

    /// True when some `set.card` argument is a `store(...)` chain that is *not*
    /// structurally covered by the cardinality recurrence
    /// ([`is_covered_store_chain`](Self::is_covered_store_chain)) — i.e. a chain
    /// rooted at a set variable or otherwise out of the counted fragment. Such a
    /// cardinality is bounded only by the `card ≥ 0` bridge (no structural count),
    /// so it is not soundly decided and the caller fails closed to `Unknown`.
    ///
    /// Store chains that *are* covered (rooted at the const-false empty set) are
    /// not flagged here: their structural axioms are injected and they decide
    /// soundly.
    fn set_card_has_uncovered_store_chain_arg(&mut self) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        // A `set.card` over a set **variable** that is aliased by a top-level
        // `(= v <set-expr>)` equality is as constrained as `card` applied to the
        // resolved set expression. Resolve through the alias chain
        // (var→var→…→expr) and judge coverage on the resolved term:
        //   - resolves to the empty carrier or a COVERED store chain → decided
        //     (card(v) tied to the structural count in `collect_set_card_axioms`).
        //   - resolves to an UNCOVERED store chain (variable-rooted / symbolic
        //     non-folding) or to a bare variable that is itself aliased → no
        //     structural count exists, so fail closed here.
        // A `card` over a bare, UNALIASED set variable stays sound under the
        // `card >= 0` bridge (a free set may have any non-negative size), so it
        // is never flagged.
        let aliases = self.build_set_alias_map();

        // Collect every `set.card` argument without holding a borrow across the
        // &mut coverage check below.
        let mut card_args: Vec<TermId> = Vec::new();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == OP_CARD && args.len() == 1 {
                        card_args.push(args[0]);
                    }
                    for arg in args.clone() {
                        stack.push(arg);
                    }
                }
                TermData::App(_, args) => {
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        for arg in card_args {
            let arg_is_var = matches!(self.ctx.terms.get(arg), TermData::Var(..));
            let effective = self.resolve_set_alias(arg, &aliases);
            let aliased = arg_is_var && effective != arg;

            // A direct (non-aliased) store-chain argument: covered chains decide,
            // uncovered ones fail closed — unchanged from before.
            if self.is_set_store_term(arg) && !self.is_covered_store_chain(arg) {
                return true;
            }
            // An aliased variable whose resolved expression is not decidable:
            // the empty carrier and covered store chains are decided (tied in
            // `collect_set_card_axioms`); everything else (uncovered store chain
            // or a still-variable resolution) fails closed.
            if aliased {
                let decided =
                    self.is_empty_carrier(effective) || self.is_covered_store_chain(effective);
                if !decided {
                    return true;
                }
            }
        }
        false
    }

    /// Collect every `(set.subset sub sup)` atom in the assertion DAG as
    /// `(atom, sub, sup)` triples (deduplicated by atom term).
    fn collect_subset_atoms(&self) -> Vec<(TermId, TermId, TermId)> {
        let mut out: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut seen_atoms: HashSet<TermId> = HashSet::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == OP_SUBSET && args.len() == 2 && seen_atoms.insert(term) {
                        out.push((term, args[0], args[1]));
                    }
                    for arg in args.clone() {
                        stack.push(arg);
                    }
                }
                TermData::App(_, args) => {
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        out
    }

    /// Structural membership of `elem` in a set term `t` that is empty or a
    /// **covered** store chain (caller guarantees `is_empty_carrier(t)` or
    /// `is_covered_store_chain(t)`). Returns `Some(true/false)` when
    /// `mk_select(t, elem)` folds (read-over-write / read-over-const-false) to a
    /// Boolean literal, or `None` when it does not. The own-element memberships
    /// of a covered chain always fold, but a *cross-chain* probe (an element of
    /// the superset selected from the subset, or vice-versa) over symbolic,
    /// not-provably-distinct indices may leave a residual `select`; that yields
    /// `None`, on which the subset decision conservatively fails closed.
    fn structural_member(&mut self, t: TermId, elem: TermId) -> Option<bool> {
        let true_t = self.ctx.terms.true_term();
        let false_t = self.ctx.terms.false_term();
        let m = self.ctx.terms.mk_select(t, elem);
        if m == true_t {
            Some(true)
        } else if m == false_t {
            Some(false)
        } else {
            None
        }
    }

    /// Collect the elements written by a covered store chain (the `e` in each
    /// `store(_, e, _)` write). Caller guarantees `is_covered_store_chain(t)`.
    /// Elements may repeat / be later removed; the actual membership is decided
    /// by [`structural_member`](Self::structural_member).
    fn store_chain_elements(&self, t: TermId, out: &mut Vec<TermId>) {
        let mut cur = t;
        loop {
            match self.ctx.terms.get(cur) {
                TermData::App(Symbol::Named(n), a) if n == "store" && a.len() == 3 => {
                    out.push(a[1]);
                    cur = a[0];
                }
                _ => return,
            }
        }
    }

    /// True when `raw` is a set **variable** aliased via `(= v <set-expr>)` to a
    /// different (resolved) set term — the under-constrained shape this fix
    /// targets. A bare unaliased variable resolves to itself (not aliased).
    fn is_aliased_set_var(&self, raw: TermId, aliases: &[(TermId, TermId)]) -> bool {
        matches!(self.ctx.terms.get(raw), TermData::Var(..))
            && self.resolve_set_alias(raw, aliases) != raw
    }

    /// Structural truth value of `subset(sub_r, sup_r)` over *resolved* operands,
    /// or `None` when not structurally decided (caller fails closed).
    ///
    /// Sound cases (everything else → `None`):
    ///   - `sub_r` empty                         → `true`  (∅ ⊆ anything).
    ///   - `sub_r == sup_r`                       → `true`  (reflexive).
    ///   - both `sub_r`, `sup_r` empty-or-covered → membership scan: `subset` is
    ///     *false* iff some element written by either chain is in `sub_r` but not
    ///     in `sup_r` (all other elements are absent from both — const-false
    ///     base). A non-empty covered `sub_r` against an empty `sup_r` is `false`.
    ///     If any cross-membership fails to fold to a constant, returns `None`.
    fn subset_structural_value(&mut self, sub_r: TermId, sup_r: TermId) -> Option<bool> {
        // ∅ ⊆ anything — decided regardless of `sup_r`'s shape.
        if self.is_empty_carrier(sub_r) {
            return Some(true);
        }
        // Reflexive subset over identical resolved operands.
        if sub_r == sup_r {
            return Some(true);
        }
        // Full structural decision requires both sides empty-or-covered.
        let sub_ok = self.is_covered_store_chain(sub_r);
        let sup_ok = self.is_empty_carrier(sup_r) || self.is_covered_store_chain(sup_r);
        if !(sub_ok && sup_ok) {
            return None;
        }
        let mut elems: Vec<TermId> = Vec::new();
        self.store_chain_elements(sub_r, &mut elems);
        if !self.is_empty_carrier(sup_r) {
            self.store_chain_elements(sup_r, &mut elems);
        }
        for elem in elems {
            let in_sub = self.structural_member(sub_r, elem)?;
            let in_sup = self.structural_member(sup_r, elem)?;
            if in_sub && !in_sup {
                return Some(false);
            }
        }
        Some(true)
    }

    /// True when some `set.subset` atom has an aliased set-variable operand,
    /// is NOT structurally decided
    /// ([`subset_structural_value`](Self::subset_structural_value) → `None`),
    /// AND its resolved **superset** is *bounded* (the empty set or a covered
    /// store chain). Such a subset risks a wrong `sat`: the bounded superset can
    /// force the predicate false (so a positive `subset` is UNSAT), yet the
    /// witness saturation misses it (no `member` atoms are present). It is
    /// therefore demoted to a fail-closed `Unknown` here.
    ///
    /// When the superset resolves to an UNbounded shape (a free/variable-rooted
    /// set), the predicate is satisfiable in either polarity (pick a superset
    /// that contains / fails to contain the subset), so the saturation's `sat`
    /// is correct and the atom is *not* flagged — preserving genuinely-sat
    /// problems like `subset({1}, t)` over a free `t`.
    ///
    /// Subset atoms over bare UNALIASED variables (e.g. `(set.subset a b)`) have
    /// no aliased operand and are never flagged — they stay in the
    /// witness-saturation fragment, matching pre-existing behaviour.
    fn set_subset_has_undecidable_aliased_arg(&mut self) -> bool {
        let aliases = self.build_set_alias_map();
        let atoms = self.collect_subset_atoms();
        for (_atom, sub, sup) in atoms {
            let has_aliased =
                self.is_aliased_set_var(sub, &aliases) || self.is_aliased_set_var(sup, &aliases);
            if !has_aliased {
                continue;
            }
            let sub_r = self.resolve_set_alias(sub, &aliases);
            let sup_r = self.resolve_set_alias(sup, &aliases);
            if self.subset_structural_value(sub_r, sup_r).is_some() {
                continue;
            }
            // Undecided. Only a *bounded* superset can force the verdict (and so
            // mask a wrong `sat`); an unbounded superset leaves the predicate
            // satisfiable, so saturation's `sat` is sound and we do not fail-close.
            let sup_bounded = self.is_empty_carrier(sup_r) || self.is_covered_store_chain(sup_r);
            if sup_bounded {
                return true;
            }
        }
        false
    }

    /// Build structural subset axioms (#set-subset-aliased-wrong-sat).
    ///
    /// For each `(set.subset sub sup)` atom that has an aliased set-variable
    /// operand and whose truth value is *structurally determined* after alias
    /// resolution ([`subset_structural_value`](Self::subset_structural_value)),
    /// tie the opaque atom to that Boolean constant via `(= atom true)` /
    /// `(= atom false)`. This decides the alias-bound empty / covered cases that
    /// the witness saturation cannot reach (no `member` atoms are present):
    ///   - `subset(empty_alias, t)`            → `true`  (∅ ⊆ anything),
    ///   - `subset(singleton_alias, empty_alias)` → `false` (non-empty ⊄ ∅),
    ///   - `subset({1}_alias, {2}_alias)`       → `false`.
    ///
    /// Atoms with an aliased operand that are NOT structurally decided are
    /// filtered out earlier by
    /// [`set_subset_has_undecidable_aliased_arg`](Self::set_subset_has_undecidable_aliased_arg)
    /// (the whole solve fails closed), so this never produces an unsound tie.
    /// Atoms with no aliased operand are left to the existing witness path.
    fn collect_set_subset_axioms(&mut self) -> Vec<TermId> {
        let aliases = self.build_set_alias_map();
        let atoms = self.collect_subset_atoms();
        let true_t = self.ctx.terms.true_term();
        let false_t = self.ctx.terms.false_term();
        let mut axioms = Vec::new();
        for (atom, raw_sub, raw_sup) in atoms {
            // The `has_aliased` gate was REMOVED here. `subset_structural_value`
            // is a *complete & sound* decision over the empty / covered-store-chain
            // fragment: it folds every relevant membership probe to a Boolean
            // constant, so whenever it returns `Some(b)` we may soundly tie
            // `(= atom b)` regardless of whether either operand is an aliased set
            // variable or a fully-concrete literal. Previously only atoms with an
            // aliased operand were tied, leaving a negated genuinely-true CONCRETE
            // atom (e.g. `(not (set.subset {1} {0,1}))`) unrefuted: the
            // one-directional extensionality axiom is vacuously satisfied when the
            // atom is forced FALSE, so nothing contradicted the wrong `sat`. Tying
            // a structurally-decided constant can only CONSTRAIN, never refute, a
            // genuine model — so this cannot introduce a false-UNSAT.
            let sub = self.resolve_set_alias(raw_sub, &aliases);
            let sup = self.resolve_set_alias(raw_sup, &aliases);
            match self.subset_structural_value(sub, sup) {
                Some(true) => axioms.push(self.ctx.terms.mk_eq(atom, true_t)),
                Some(false) => axioms.push(self.ctx.terms.mk_eq(atom, false_t)),
                None => {}
            }
        }
        axioms
    }

    /// Skolem witnesses for subset atoms (#set-subset-transitivity-wrong-sat,
    /// 2026-06-24).
    ///
    /// `(set.subset X Y)` over bare unaliased set variables stays in the
    /// witness-saturation fragment, but that saturation only fires on `member`
    /// atoms already present in the problem — so a NEGATED subset over symbolic
    /// sets (e.g. `¬(A ⊆ C)` in the transitivity conflict `A⊆B ∧ B⊆C ∧ ¬(A⊆C)`)
    /// has no witness to propagate, and the solver wrongly returned `sat` with the
    /// spurious empty model `A=B=C=∅` (where `¬(A⊆C)` is actually FALSE).
    ///
    /// Fix: for each subset atom `s = (subset X Y)`, inject the Skolem clauses
    ///   `(s ∨ (member w X))`   and   `(s ∨ ¬(member w Y))`
    /// for a FRESH witness element `w`. These encode `¬s → (w∈X ∧ w∉Y)`, the
    /// Skolemization of `¬(X⊆Y) ≡ ∃v(v∈X ∧ v∉Y)` — EQUISATISFIABLE (sound: any
    /// model extends to interpret the fresh `w` as the witness; adding clauses
    /// never turns unsat into sat). When `s` is true the clauses are vacuous (so a
    /// genuinely-true asserted subset is never falsely refuted — no false-UNSAT).
    /// When `s` is false they hand the existing member-monotonicity saturation the
    /// `w∈X`, `w∉Y` atoms it needs, so transitivity (`w∈A → w∈B → w∈C` against
    /// `w∉C`) closes to UNSAT, and a genuinely-SAT negated subset keeps a real
    /// witness model instead of the spurious empty one.
    fn collect_negated_subset_witnesses(&mut self) -> Vec<TermId> {
        let atoms = self.collect_subset_atoms();
        // One fresh witness element per subset atom.
        let mut wits: Vec<(TermId, TermId, TermId, TermId)> = Vec::new(); // (w, atom, sub, sup)
        for &(atom, sub, sup) in &atoms {
            let Some(elem_sort) = self.ctx.terms.sort(sub).array_index().cloned() else {
                continue;
            };
            let w = self.ctx.terms.mk_fresh_var("set_subset_witness", elem_sort);
            wits.push((w, atom, sub, sup));
        }
        let mut out = Vec::new();
        // (a) Negated-subset Skolem clauses: `¬atom → (w ∈ sub ∧ w ∉ sup)`.
        for &(w, atom, sub, sup) in &wits {
            let in_sub = self.ctx.terms.mk_select(sub, w);
            let in_sup = self.ctx.terms.mk_select(sup, w);
            let not_in_sup = self.ctx.terms.mk_not(in_sup);
            out.push(self.ctx.terms.mk_or(vec![atom, in_sub]));
            out.push(self.ctx.terms.mk_or(vec![atom, not_in_sup]));
        }
        // (b) Subset DEFINITION instantiated at every witness for every subset
        // atom: `s_j → (w ∈ X_j → w ∈ Y_j)`, i.e.
        // `¬s_j ∨ ¬(w ∈ X_j) ∨ (w ∈ Y_j)`. This lets a witness propagate through
        // INTERMEDIATE subsets (the transitivity chain `w∈A → w∈B → w∈C`); without
        // it the saturation never introduces the intermediate membership. Sound:
        // it is the subset definition instantiated at `w` (entailed by `s_j`).
        for &(w, _, _, _) in &wits {
            for &(atom_j, sub_j, sup_j) in &atoms {
                let in_sub_j = self.ctx.terms.mk_select(sub_j, w);
                let in_sup_j = self.ctx.terms.mk_select(sup_j, w);
                let not_atom_j = self.ctx.terms.mk_not(atom_j);
                let not_in_sub_j = self.ctx.terms.mk_not(in_sub_j);
                out.push(
                    self.ctx
                        .terms
                        .mk_or(vec![not_atom_j, not_in_sub_j, in_sup_j]),
                );
            }
        }
        out
    }

    /// (#set-route-extensionality) The native SetLIA route (`UfSetLiaSolver`) lacks
    /// the array extensionality the QF_AUFLIA array route uses, so set EQUALITY and
    /// `set.subset` over the elaborated store-chains were wrongly SAT (e.g.
    /// `{0} = {1}`, `{0} ⊆ {1}`). Restore the SOUND necessary conditions, restricted
    /// to the syntactically-present element indices (a finite, sound restriction —
    /// these implications can only constrain, never refute a real model):
    ///   `(= a b)          => (= (select a e) (select b e))`   per relevant `e`
    ///   `(set.subset a b) => (=> (select a e) (select b e))`  per relevant `e`
    /// where `e` ranges over the store indices in `a`'s and `b`'s chains. `mk_select`
    /// folds `select(store-chain, const)` to a Boolean constant (see
    /// [`is_covered_store_chain`](Self::is_covered_store_chain)), so `{0}={1}`
    /// collapses to `(= a b) => (= true false)`, i.e. `(not (= a b))` → unsat.
    fn collect_set_extensionality_axioms(&mut self) -> Vec<TermId> {
        // (atom, a, b, is_subset)
        let mut pairs: Vec<(TermId, TermId, TermId, bool)> = Vec::new();
        for (atom, sub, sup) in self.collect_subset_atoms() {
            pairs.push((atom, sub, sup, true));
        }
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    let set_eq = name == "=" && args.len() == 2 && self.is_set_sorted_term(args[0]);
                    let eq_pair = if set_eq {
                        Some((term, args[0], args[1]))
                    } else {
                        None
                    };
                    let children: Vec<TermId> = args.clone();
                    if let Some((atom, a, b)) = eq_pair {
                        pairs.push((atom, a, b, false));
                    }
                    for arg in children {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }

        let mut axioms = Vec::new();
        for (atom, a, b, is_subset) in pairs {
            let mut elems: Vec<TermId> = Vec::new();
            self.collect_store_chain_indices(a, &mut elems);
            self.collect_store_chain_indices(b, &mut elems);
            elems.sort_unstable();
            elems.dedup();
            for e in elems {
                let sel_a = self.ctx.terms.mk_select(a, e);
                let sel_b = self.ctx.terms.mk_select(b, e);
                let consequent = if is_subset {
                    // member(a,e) => member(b,e)
                    self.ctx.terms.mk_implies(sel_a, sel_b)
                } else {
                    self.ctx.terms.mk_eq(sel_a, sel_b)
                };
                axioms.push(self.ctx.terms.mk_implies(atom, consequent));
            }
        }
        axioms
    }

    /// Collect the store indices along a `store(...)` chain (the elaborated form of
    /// `set.singleton`/`set.insert`/`set.remove`), stopping at the const-false empty
    /// carrier or any non-store node.
    fn collect_store_chain_indices(&self, t: TermId, out: &mut Vec<TermId>) {
        let mut cur = t;
        for _ in 0..100_000 {
            match self.ctx.terms.get(cur) {
                TermData::App(Symbol::Named(n), a) if n == "store" && a.len() == 3 => {
                    out.push(a[1]);
                    cur = a[0];
                }
                _ => return,
            }
        }
    }

    /// True when `t` is set-sorted, i.e. an `(Array Elem Bool)` carrier.
    fn is_set_sorted_term(&self, t: TermId) -> bool {
        self.ctx.terms.sort(t).array_element() == Some(&ay_core::Sort::Bool)
    }

    fn collect_set_card_axioms(&mut self) -> Vec<TermId> {
        // Discover (card_term, set_arg) pairs over the term DAG, plus every
        // `select(array, index)` — the membership probes the lower bound below
        // needs. Collected in this ONE walk so the cost stays linear in the DAG
        // rather than re-walking it per card term.
        let mut card_pairs: Vec<(TermId, TermId)> = Vec::new();
        let mut selects: Vec<(TermId, TermId)> = Vec::new();
        let mut named_empty_terms: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == OP_CARD && args.len() == 1 {
                        card_pairs.push((term, args[0]));
                    } else if name == OP_EMPTY && args.is_empty() {
                        named_empty_terms.insert(term);
                    } else if name == "select" && args.len() == 2 {
                        selects.push((args[0], args[1]));
                    }
                    for arg in args.clone() {
                        stack.push(arg);
                    }
                }
                TermData::App(_, args) => {
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }

        if card_pairs.is_empty() {
            return Vec::new();
        }

        let aliases = self.build_set_alias_map();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let false_t = self.ctx.terms.false_term();
        let mut axioms = Vec::new();
        for (card_term, raw_set_arg) in card_pairs {
            // card(s) >= 0 — asserted for EVERY card term (sound bridge).
            axioms.push(self.ctx.terms.mk_ge(card_term, zero));
            // Resolve a card argument that is a set VARIABLE through its defining
            // equality `(= s <set-expr>)` (following var→var→…→expr chains). The
            // structural cardinality of an aliased `s` is the cardinality of the
            // resolved expression, so `card_term` is tied directly to that
            // expression's structure below. A non-variable / unaliased arg
            // resolves to itself (no change in behaviour).
            let set_arg = self.resolve_set_alias(raw_set_arg, &aliases);
            // card(empty) = 0. The empty set is either a residual `set.empty`
            // named app or — after elaboration — the constant-false array.
            let is_empty = named_empty_terms.contains(&set_arg)
                || self.ctx.terms.get_const_array(set_arg) == Some(false_t);
            if is_empty {
                axioms.push(self.ctx.terms.mk_eq(card_term, zero));
            } else if self.is_set_store_term(set_arg) && self.is_covered_store_chain(set_arg) {
                // Structural cardinality recurrence over an empty-rooted store
                // chain (the elaborated form of set.singleton / set.insert /
                // set.remove). Definitional:
                //   card(store(s,e,true))  = card(s) + ite(member(s,e), 0, 1)
                //   card(store(s,e,false)) = card(s) − ite(member(s,e), 1, 0)
                // with the chain bottoming out at card(const-false) = 0. The
                // membership test `member(s,e) = select(s,e)` is over the INNER
                // set s (before this write), so it is decided correctly by the
                // array solver (so inserting a present element does not grow the
                // count; removing an absent element does not shrink it).
                self.emit_store_chain_card_axioms(card_term, set_arg, &mut axioms);
            } else {
                // UNDER-CONSTRAINED (#set-card-wrong-sat): a bare set variable or
                // an uncovered store chain. Before this branch existed the only
                // axiom for such a set was `card >= 0`, which leaves membership
                // and cardinality completely decoupled — so
                //   `(set.member 1 s) ∧ (= 0 (set.card s))`
                // was wrongly SAT (with a model that even falsified its own second
                // assertion). Tie the two together with the membership lower bound.
                self.emit_membership_card_lower_bound(
                    card_term,
                    set_arg,
                    &aliases,
                    &selects,
                    &mut axioms,
                );
            }
        }
        axioms
    }

    /// Sound membership → cardinality lower bound for a set whose structure the
    /// store-chain recurrence does not cover (a bare set variable, or a chain
    /// rooted at one rather than at the empty carrier).
    ///
    /// Let `E = [e_0 .. e_{k-1}]` be the elements probed for membership in this
    /// same set anywhere in the assertions — the entries of `selects` (collected
    /// by the caller's single DAG walk) whose array resolves to `set_arg`. Then
    ///
    /// ```text
    ///   card(s) >= Σ_i ite(member(s, e_i) ∧ ⋀_{j<i} e_i ≠ e_j, 1, 0)
    /// ```
    ///
    /// The `⋀_{j<i} e_i ≠ e_j` guard makes each *value* contribute at most once:
    /// a repeated element is counted only at its first index, so the sum is a
    /// count of DISTINCT members and can never exceed the true cardinality. That
    /// keeps the bound sound even when the probed indices are symbolic and not
    /// provably distinct — the case a naive `Σ ite(member, 1, 0)` gets wrong.
    ///
    /// This is a lower bound only, so it is deliberately incomplete: it refutes
    /// `1 ∈ s ∧ |s| = 0` and `1 ∈ s ∧ 2 ∈ s ∧ |s| = 1`, but says nothing about
    /// an upper bound, so `|s| = 0 ∧ s ≠ ∅` stays `unknown` rather than becoming
    /// unsat. Incomplete is sound; wrong-SAT is not.
    fn emit_membership_card_lower_bound(
        &mut self,
        card_term: TermId,
        set_arg: TermId,
        aliases: &[(TermId, TermId)],
        selects: &[(TermId, TermId)],
        axioms: &mut Vec<TermId>,
    ) {
        // Keep the probes against THIS set, de-duplicated by index term.
        let mut elems: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for &(array, index) in selects {
            if self.resolve_set_alias(array, aliases) == set_arg && seen.insert(index) {
                elems.push(index);
            }
        }
        if elems.is_empty() {
            return;
        }

        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let one = self.ctx.terms.mk_int(BigInt::from(1));
        let mut contributions: Vec<TermId> = Vec::with_capacity(elems.len());
        for i in 0..elems.len() {
            let elem = elems[i];
            // Guard: `elem` is in the set AND is not a repeat of an earlier probe.
            let mut guard = vec![self.ctx.terms.mk_select(set_arg, elem)];
            for j in 0..i {
                let same = self.ctx.terms.mk_eq(elem, elems[j]);
                let distinct = self.ctx.terms.mk_not(same);
                guard.push(distinct);
            }
            let cond = if guard.len() == 1 {
                guard[0]
            } else {
                self.ctx.terms.mk_and(guard)
            };
            contributions.push(self.ctx.terms.mk_ite(cond, one, zero));
        }
        let lower_bound = if contributions.len() == 1 {
            contributions[0]
        } else {
            self.ctx.terms.mk_add(contributions)
        };
        axioms.push(self.ctx.terms.mk_ge(card_term, lower_bound));
    }

    /// Emit the definitional cardinality recurrence for a covered (empty-rooted)
    /// store chain. `card_term` is the `set.card` application over `set_arg`, the
    /// outermost `store(...)` node. Appends to `axioms`:
    ///
    /// - For each `store(s, e, v)` write in the chain: a fresh inner `card(s)`
    ///   term (`>= 0`) and the recurrence equation relating `card(store)` to
    ///   `card(s)` and the membership of `e` in `s`.
    /// - The base equation `card(const-false) = 0`.
    ///
    /// Caller must have verified [`is_covered_store_chain`](Self::is_covered_store_chain).
    fn emit_store_chain_card_axioms(
        &mut self,
        card_term: TermId,
        set_arg: TermId,
        axioms: &mut Vec<TermId>,
    ) {
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let one = self.ctx.terms.mk_int(BigInt::from(1));
        let true_t = self.ctx.terms.true_term();

        let mut outer_card = card_term;
        let mut cur = set_arg;
        loop {
            // Base: card(const-false) = 0. `outer_card` is the card term over the
            // empty carrier (created on the previous iteration, or `card_term`
            // for a directly-empty chain — handled by the caller's empty branch).
            if self.is_empty_carrier(cur) {
                axioms.push(self.ctx.terms.mk_eq(outer_card, zero));
                return;
            }
            let (inner, elem, value) = match self.ctx.terms.get(cur) {
                TermData::App(Symbol::Named(n), a) if n == "store" && a.len() == 3 => {
                    (a[0], a[1], a[2])
                }
                // Unreachable for a covered chain, but fail safe: stop emitting.
                _ => return,
            };
            // card(inner) — interned, so it coincides with any pre-existing
            // card term over the same set; the LIA solver ties them together.
            let inner_card =
                self.ctx
                    .terms
                    .mk_app(Symbol::named(OP_CARD), [inner], ay_core::Sort::Int);
            axioms.push(self.ctx.terms.mk_ge(inner_card, zero));
            // member(inner, elem) = select(inner, elem). Over the INNER set so
            // dedup/no-op removal is decided correctly.
            let member = self.ctx.terms.mk_select(inner, elem);
            if value == true_t {
                // insert: card(store) = card(inner) + ite(member, 0, 1)
                let delta = self.ctx.terms.mk_ite(member, zero, one);
                let rhs = self.ctx.terms.mk_add(vec![inner_card, delta]);
                axioms.push(self.ctx.terms.mk_eq(outer_card, rhs));
            } else {
                // remove (value == false): card(store) = card(inner) − ite(member, 1, 0)
                let delta = self.ctx.terms.mk_ite(member, one, zero);
                let rhs = self.ctx.terms.mk_sub(vec![inner_card, delta]);
                axioms.push(self.ctx.terms.mk_eq(outer_card, rhs));
            }
            outer_card = inner_card;
            cur = inner;
        }
    }
}
