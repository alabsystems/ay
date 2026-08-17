// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native multiset theory solving (QF_MULTISET / QF_MSLIA).
//!
//! Multisets are modelled on the count carrier `Multiset(T) = Array(T → Int)`.
//! The array solver decides the count carrier (`select` read-through) and
//! multiset equality (extensionality); the native
//! [`ay_multiset::MultisetSolver`] adds subset reflexivity reasoning; LIA
//! decides the integer arithmetic of `multiset.count` terms.
//!
//! ## Count-axiom injection (the seq.len / set.card pattern)
//!
//! Because a `TheorySolver` only holds an immutable `&TermStore` during
//! `check()`, the ground count axioms are injected here (where
//! `&mut TermStore` is available) before solving, exactly as `seq.len` /
//! `set.card` axioms are injected for QF_SEQLIA / QF_SETLIA:
//!
//! - `count(m, e) ≥ 0` for **every** count term (the sound count↔LIA bridge —
//!   asserted for every count, never selectively; multiplicities are never
//!   negative).
//! - `subset(m, n) ⇒ count(m, e) ≤ count(n, e)` for every present
//!   `multiset.subset` atom and every ground element `e` whose count atoms are
//!   present for both `m` and `n` (a sound *implication* restricted to present
//!   witnesses — never asserts subset positively).
//!
//! The insert/remove/empty count equations (`count(insert(m,e),e)=count(m,e)+1`,
//! `count(remove(m,e),e)=max(count(m,e)-1,0)`, `count(empty,e)=0`) are decided
//! directly by the array solver via `store`/const-array read-through — `count`
//! IS `select`, so no separate axiom is needed for them.
//!
//! ## Fail-closed contract
//!
//! Out-of-fragment multiset operators (polymorphic / higher-order image:
//! `multiset.map`, `multiset.filter`, `multiset.fold`,
//! `multiset.comprehension`, `multiset.sum`, `multiset.choose`; pointwise
//! combinators `multiset.union` / `multiset.inter` / `multiset.diff` whose
//! count semantics need a domain comprehension) are **not** decided. Their
//! presence yields `Unknown` (incomplete) rather than a guessed SAT/UNSAT
//! verdict.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use num_bigint::BigInt;
use num_traits::Zero;

use super::super::Executor;
use super::solve_harness::TheoryModels;
use super::MAX_SPLITS_LIA;
use crate::combined_solvers::UfMultisetLiaSolver;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use ay_core::term::{Symbol, TermData, TermId};
use ay_core::Sort;
use ay_multiset::{OP_COUNT, OP_SUBSET, OUT_OF_FRAGMENT_OPS};

impl Executor {
    /// Solve the native multiset theory (QF_MULTISET / QF_MSLIA).
    ///
    /// Injects ground count axioms, then solves with [`UfMultisetLiaSolver`].
    /// Returns `Unknown` (fail-closed) when any out-of-fragment multiset
    /// operator is present.
    pub(in crate::executor) fn solve_multiset_lia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // Fail-closed guard: out-of-fragment multiset operators are not decided.
        if self.assertions_contain_out_of_fragment_multiset_ops() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        // Fail-closed guard (#multiset-alias-underconstrained): a
        // `multiset.count` / `multiset.subset` whose collection argument is a
        // VARIABLE aliased via `(= v <multiset-expr>)` is bounded only by the
        // loose ground bridge (count >= 0) unless the alias is resolved and tied
        // to its defining expression. When the resolved expression is a COVERED
        // (empty-rooted, concretely indexed) insert/remove/singleton chain, the
        // deciding ties are injected below (`collect_multiset_count_axioms`).
        // When it is UNCOVERED (variable-rooted / symbolic), no sound tie exists
        // and leaving the loose bridge admits a wrong `sat`; demote those to
        // Unknown (sound).
        if self.multiset_has_uncovered_aliased_count_or_subset() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        // Inject ground count axioms (count >= 0 for every count; subset->count;
        // alias-resolved count ties and covered-chain subset biconditionals).
        let count_axioms = self.collect_multiset_count_axioms();
        if !count_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx
                .assertions
                .extend(count_axioms.into_iter().filter(|axiom| seen.insert(*axiom)));
        }

        // Multiset count carriers are arrays; enumerate finite-index
        // equalities only after all route-local count/subset ties are present.
        let _ = self.add_finite_index_array_closure();

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        solve_incremental_split_loop_pipeline!(self,
            tag: "MultisetLIA",
            persistent_sat_field: lia_persistent_sat,
            create_theory: UfMultisetLiaSolver::new(&self.ctx.terms),
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

    /// Solve QF_MULTISET / QF_MSLIA with check-sat-assuming.
    ///
    /// Mirrors [`solve_multiset_lia`](Self::solve_multiset_lia) but temporarily
    /// adds assumptions to the assertion set under an isolated incremental scope.
    pub(in crate::executor) fn solve_multiset_lia_with_assumptions(
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
            self.with_isolated_incremental_state(Some(scoped_assertions), Self::solve_multiset_lia);

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

    /// Whether any assertion references an out-of-fragment multiset operator.
    ///
    /// These polymorphic / higher-order image operators (and the pointwise
    /// union/inter/diff combinators) fall outside the sound saturatable
    /// fragment; their presence forces a fail-closed `Unknown`.
    fn assertions_contain_out_of_fragment_multiset_ops(&self) -> bool {
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

    /// Collect ground count axioms for the multiset theory.
    ///
    /// - `count(m, e) ≥ 0` for every count term — both residual
    ///   `multiset.count` named apps and the elaborated `(select m e)` reads
    ///   over a `Multiset(T) = Array(T → Int)` carrier (sound count↔LIA
    ///   non-negativity bridge; multiplicities are never negative).
    /// - `subset(m, n) ⇒ count(m, e) ≤ count(n, e)` for every present subset
    ///   atom and every ground element `e` whose count reads are present for
    ///   both operands (sound implication restricted to present witnesses).
    fn collect_multiset_count_axioms(&mut self) -> Vec<TermId> {
        // Discover count reads (multiset, elem, count_term) and subset atoms.
        let mut count_reads: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut subset_atoms: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == OP_COUNT && args.len() == 2 {
                        // (multiset.count elem multiset) — element-first.
                        count_reads.push((args[1], args[0], term));
                    } else if name == OP_SUBSET && args.len() == 2 {
                        subset_atoms.push((term, args[0], args[1]));
                    } else if name == "select"
                        && args.len() == 2
                        && self.is_multiset_carrier(args[0])
                    {
                        // Elaborated count read: (select multiset elem) where
                        // the multiset carrier is Array(_ -> Int).
                        count_reads.push((args[0], args[1], term));
                    }
                    for arg in args.clone() {
                        stack.push(arg);
                    }
                }
                TermData::App(_, args) => {
                    for arg in args.clone() {
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

        if count_reads.is_empty() && subset_atoms.is_empty() {
            return Vec::new();
        }

        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let mut axioms = Vec::new();

        // count(m, e) >= 0 for every count read.
        for (_m, _e, count_term) in &count_reads {
            axioms.push(self.ctx.terms.mk_ge(*count_term, zero));
        }

        // subset(m, n) => count(m, e) <= count(n, e) over present witnesses.
        for (subset_atom, sub, sup) in &subset_atoms {
            // Collect distinct ground elements with count reads on BOTH operands.
            let mut witnesses: Vec<(TermId, TermId, TermId)> = Vec::new();
            for (m, e, cm) in &count_reads {
                if *m != *sub {
                    continue;
                }
                if let Some(cn) = count_reads
                    .iter()
                    .find(|(n, e2, _)| *n == *sup && *e2 == *e)
                    .map(|(_, _, cn)| *cn)
                {
                    witnesses.push((*e, *cm, cn));
                }
            }
            for (_e, cm, cn) in witnesses {
                let le = self.ctx.terms.mk_le(cm, cn);
                // subset_atom => (count(m,e) <= count(n,e)), i.e. (not subset) or le.
                let not_subset = self.ctx.terms.mk_not(*subset_atom);
                let implication = self.ctx.terms.mk_or(vec![not_subset, le]);
                axioms.push(implication);
            }
        }

        // Alias-resolved count ties. A `count(v, e) = (select v e)` over a
        // VARIABLE `v` aliased by `(= v <multiset-expr>)` is otherwise bounded
        // only by the loose `count >= 0` bridge (the array solver does not always
        // propagate `select(v,e) = select(expr,e)` through the equality on its
        // own). Resolve the alias and tie the count read to the read over the
        // defining expression: `(select v e) = (select expr e)`. This equality
        // is sound unconditionally (`v = expr` is asserted, so the reads are
        // congruent). When `expr` is a covered (empty-rooted, concretely indexed)
        // chain, `mk_select` folds `(select expr e)` to a concrete count and the
        // case is DECIDED. Uncovered shapes were already demoted to Unknown by
        // the fail-closed guard, so they never reach here.
        //
        // The tie must thread through EVERY aliased variable reachable along the
        // chain at element `e`: tying only the outer variable leaves an inner
        // `(select w e)` (over an aliased inner `w`, e.g. the empty base in
        // `(= m empty)(= m2 (insert 1 m))`) residual, which the array solver does
        // not always fold on its own. So for the outer count read and for every
        // aliased multiset variable that appears as an inner of the resolved
        // chain, inject `(select w e) = (select alias_target(w) e)`.
        let count_reads_snapshot = count_reads.clone();
        for (m, e, _count_term) in &count_reads_snapshot {
            self.emit_alias_count_ties(*m, *e, &mut axioms);
        }

        // Covered-chain subset decisions. For `subset(sub, sup)` where BOTH
        // operands resolve (through aliases) to covered, empty-rooted multiset
        // chains, the count function of each operand is fully determined and is
        // nonzero only at its explicitly stored elements. Hence
        //   subset(sub, sup) <=> AND_{e in U} count(sub,e) <= count(sup,e)
        // where `U` is the union of the stored elements of both chains (for any
        // e ∉ U, count(sub,e) = 0 <= count(sup,e), so U is a complete witness
        // universe). This biconditional DECIDES the subset atom (both polarities)
        // and is sound because the universe is exhaustive for covered chains.
        let subset_atoms_snapshot = subset_atoms.clone();
        for (subset_atom, sub, sup) in &subset_atoms_snapshot {
            // Both operands must resolve to covered, empty-rooted chains.
            if !self.multiset_resolves_to_covered_chain(*sub)
                || !self.multiset_resolves_to_covered_chain(*sup)
            {
                continue;
            }
            // Witness universe: union of explicitly stored elements of both
            // (alias-resolved) covered chains.
            let mut elems: Vec<TermId> = Vec::new();
            self.collect_multiset_chain_elems(*sub, &mut elems);
            self.collect_multiset_chain_elems(*sup, &mut elems);
            let mut conjuncts: Vec<TermId> = Vec::new();
            for e in &elems {
                // Tie both operands' counts at `e` to their concrete chain values
                // (threading through any aliased inner variables), then compare
                // the operand count reads.
                self.emit_alias_count_ties(*sub, *e, &mut axioms);
                self.emit_alias_count_ties(*sup, *e, &mut axioms);
                let cm = self.ctx.terms.mk_select(*sub, *e);
                let cn = self.ctx.terms.mk_select(*sup, *e);
                conjuncts.push(self.ctx.terms.mk_le(cm, cn));
            }
            // AND over an empty universe is `true` (both empty chains): subset
            // holds. mk_and over a single conjunct returns it directly.
            let body = if conjuncts.is_empty() {
                self.ctx.terms.true_term()
            } else {
                self.ctx.terms.mk_and(conjuncts)
            };
            // subset_atom <=> body, encoded as the two implications.
            let not_subset = self.ctx.terms.mk_not(*subset_atom);
            let not_body = self.ctx.terms.mk_not(body);
            // subset => body
            axioms.push(self.ctx.terms.mk_or(vec![not_subset, body]));
            // body => subset
            axioms.push(self.ctx.terms.mk_or(vec![not_body, *subset_atom]));
        }

        axioms
    }

    /// Resolve a multiset VARIABLE `v` to its defining multiset expression
    /// through top-level `(= v expr)` alias equalities, following alias chains
    /// (`v = w`, `w = expr`). Returns the first non-variable multiset-sorted
    /// expression reached, or `None` when `v` is not a variable, has no defining
    /// equality, or the chain does not bottom out at a concrete expression.
    ///
    /// Only top-level conjunctive equalities are followed (the assertion list),
    /// which is exactly where elaborated `(= v <chain>)` definitions live. The
    /// returned expression is congruent to `v` (the equality is asserted), so
    /// tying `count(v)` / `subset(v, ..)` to reads over it is sound.
    fn multiset_alias_target(&self, v: TermId) -> Option<TermId> {
        if !matches!(self.ctx.terms.get(v), TermData::Var(..)) {
            return None;
        }
        let mut cur = v;
        let mut guard = 0usize;
        loop {
            guard += 1;
            if guard > 64 {
                // Defensive cap against pathological alias cycles.
                return None;
            }
            let mut next: Option<TermId> = None;
            for &a in &self.ctx.assertions {
                if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(a) {
                    if name == "=" && args.len() == 2 {
                        let (lhs, rhs) = (args[0], args[1]);
                        if lhs == cur && rhs != cur {
                            next = Some(rhs);
                            break;
                        }
                        if rhs == cur && lhs != cur {
                            next = Some(lhs);
                            break;
                        }
                    }
                }
            }
            match next {
                Some(t) if matches!(self.ctx.terms.get(t), TermData::Var(..)) => {
                    cur = t;
                }
                Some(t) => return Some(t),
                None => return None,
            }
        }
    }

    /// True when `t` resolves (directly, or as a VARIABLE through its alias) to a
    /// covered, empty-rooted multiset chain
    /// ([`is_covered_multiset_chain`](Self::is_covered_multiset_chain)).
    fn multiset_resolves_to_covered_chain(&mut self, t: TermId) -> bool {
        let target = if matches!(self.ctx.terms.get(t), TermData::Var(..)) {
            match self.multiset_alias_target(t) {
                Some(e) => e,
                None => return false,
            }
        } else {
            t
        };
        self.is_covered_multiset_chain(target)
    }

    /// Emit count ties `(select w e) = (select alias_target(w) e)` for the count
    /// at element `e` of multiset term `m` and for every aliased multiset
    /// variable threaded through `m`'s (alias-resolved) store chain.
    ///
    /// Each tie is sound: `w = alias_target(w)` is an asserted equality, so the
    /// two reads are congruent. Tying every aliased variable at `e` lets the
    /// array read-over-write + LIA fold the whole chain to a concrete count
    /// (`(select empty e) = 0`, propagated up through each insert/remove level),
    /// deciding `count(m, e)`.
    fn emit_alias_count_ties(&mut self, m: TermId, e: TermId, axioms: &mut Vec<TermId>) {
        let mut cur = m;
        let mut guard = 0usize;
        loop {
            guard += 1;
            if guard > 256 {
                return;
            }
            // If `cur` is an aliased variable, tie its count at `e` to the read
            // over its defining expression, then continue resolving into it.
            if matches!(self.ctx.terms.get(cur), TermData::Var(..)) {
                let Some(target) = self.multiset_alias_target(cur) else {
                    return;
                };
                let lhs = self.ctx.terms.mk_select(cur, e);
                let rhs = self.ctx.terms.mk_select(target, e);
                if lhs != rhs {
                    let tie = self.ctx.terms.mk_eq(lhs, rhs);
                    axioms.push(tie);
                }
                cur = target;
                continue;
            }
            // Descend a store level into its inner multiset (whose count at `e`
            // the outer level's value depends on); stop at the empty carrier or
            // any non-store leaf.
            match self.ctx.terms.get(cur) {
                TermData::App(Symbol::Named(n), a) if n == "store" && a.len() == 3 => {
                    cur = a[0];
                }
                _ => return,
            }
        }
    }

    /// True when `t` is a **structurally covered** multiset chain: a chain of
    /// `store(inner, e, v)` writes (the elaborated form of
    /// `multiset.singleton` / `multiset.insert` / `multiset.remove`), with every
    /// stored element `e` an interpreted constant, bottoming out at the
    /// empty-multiset carrier (the constant-0 array). Variable nodes (root and
    /// inners) are resolved through their `(= v expr)` aliases first, so a chain
    /// rooted/threaded through `(= m empty)` / `(= m2 (insert 1 m))` definitions
    /// counts as covered.
    ///
    /// The constant-element requirement matches the underlying array+LIA decision
    /// power: with concrete indices the read-over-write rule resolves
    /// `count(., e)` among the chain levels, and the alias count ties
    /// (`emit_alias_count_ties`) thread `count(empty, e) = 0` up through every
    /// insert/remove level, so the LIA bridge decides each count to a concrete
    /// value. A chain with *symbolic* indices leaves a residual `select` whose
    /// count is not pinned, so it stays uncovered (fail-closed) rather than admit
    /// a loose-bridge wrong `sat`.
    ///
    /// Chains rooted at an UNALIASED multiset **variable** (e.g.
    /// `(multiset.insert e t)` over a declared, undefined `(Multiset T)` variable
    /// `t`) are *not* covered: the count at the root is opaque and bounded only by
    /// `count >= 0`. Such shapes remain fail-closed `Unknown`.
    fn is_covered_multiset_chain(&self, t: TermId) -> bool {
        let mut cur = t;
        let mut guard = 0usize;
        loop {
            guard += 1;
            if guard > 256 {
                // Defensive cap against pathological chain depth.
                return false;
            }
            // Resolve a variable node through its alias so a chain rooted /
            // threaded through `(= v empty)` / `(= v <chain>)` definitions is
            // recognised as covered.
            if matches!(self.ctx.terms.get(cur), TermData::Var(..)) {
                match self.multiset_alias_target(cur) {
                    Some(target) => {
                        cur = target;
                        continue;
                    }
                    // An unaliased multiset variable: a genuinely free multiset
                    // (variable-rooted), not covered by the structural count
                    // recurrence.
                    None => return false,
                }
            }
            if self.is_empty_multiset_carrier(cur) {
                return true;
            }
            let (inner, elem) = match self.ctx.terms.get(cur) {
                TermData::App(Symbol::Named(n), a) if n == "store" && a.len() == 3 => (a[0], a[1]),
                // Anything other than a store node or the const-0 base
                // (an opaque combinator app, etc.) is not covered.
                _ => return false,
            };
            // Require the stored element to be an interpreted constant. With
            // constant indices the array read-over-write folds the count tie
            // ladder among levels (same/distinct index resolution), so every
            // `count(., elem)` collapses to a concrete value the LIA bridge
            // decides. A symbolic index leaves a residual `select` whose count is
            // not pinned, so such chains stay uncovered (fail-closed) rather than
            // admit a loose-bridge wrong `sat`.
            if !matches!(self.ctx.terms.get(elem), TermData::Const(_)) {
                return false;
            }
            cur = inner;
        }
    }

    /// True when `t` is the empty-multiset carrier: the constant-0 array
    /// (`(as multiset.empty (Multiset T))` and the base of `multiset.singleton`).
    fn is_empty_multiset_carrier(&self, t: TermId) -> bool {
        match self.ctx.terms.get_const_array(t) {
            Some(default) => matches!(
                self.ctx.terms.get(default),
                TermData::Const(ay_core::term::Constant::Int(v)) if v.is_zero()
            ),
            None => false,
        }
    }

    /// Append the explicitly stored elements of an (alias-resolved) covered
    /// multiset chain to `out` (deduplicated), threading through aliased variable
    /// inners. Caller must have verified
    /// [`multiset_resolves_to_covered_chain`](Self::multiset_resolves_to_covered_chain).
    fn collect_multiset_chain_elems(&self, chain: TermId, out: &mut Vec<TermId>) {
        let mut cur = chain;
        let mut guard = 0usize;
        loop {
            guard += 1;
            if guard > 256 {
                return;
            }
            // Resolve aliased variables to their defining expression so inner
            // chains contribute their stored elements to the universe.
            if matches!(self.ctx.terms.get(cur), TermData::Var(..)) {
                match self.multiset_alias_target(cur) {
                    Some(t) => {
                        cur = t;
                        continue;
                    }
                    None => return,
                }
            }
            match self.ctx.terms.get(cur) {
                TermData::App(Symbol::Named(n), a) if n == "store" && a.len() == 3 => {
                    let elem = a[1];
                    if !out.contains(&elem) {
                        out.push(elem);
                    }
                    cur = a[0];
                }
                _ => return,
            }
        }
    }

    /// Whether any `multiset.count` / `multiset.subset` argument is a VARIABLE
    /// aliased (through `(= v expr)`) to a multiset expression that is NOT a
    /// covered chain — i.e. variable-rooted / symbolic. Such a count/subset is
    /// bounded only by the loose `count >= 0` bridge with no sound deciding tie,
    /// so the caller fails closed to `Unknown`.
    ///
    /// Aliases to COVERED chains are not flagged: their deciding ties /
    /// biconditionals are injected by
    /// [`collect_multiset_count_axioms`](Self::collect_multiset_count_axioms) and
    /// they decide soundly. Non-variable (direct) arguments are not flagged here
    /// either — a direct `select(store(...), e)` is decided by the array solver's
    /// read-over-write, and the existing subset witness obligation is sound.
    fn multiset_has_uncovered_aliased_count_or_subset(&mut self) -> bool {
        // Collect every multiset collection argument that is a VARIABLE: the
        // multiset of a count read and both operands of a subset atom.
        let mut collection_vars: Vec<TermId> = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    let mut candidates: Vec<TermId> = Vec::new();
                    if name == OP_COUNT && args.len() == 2 {
                        candidates.push(args[1]);
                    } else if name == OP_SUBSET && args.len() == 2 {
                        candidates.push(args[0]);
                        candidates.push(args[1]);
                    } else if name == "select"
                        && args.len() == 2
                        && self.is_multiset_carrier(args[0])
                    {
                        candidates.push(args[0]);
                    }
                    for c in candidates {
                        if matches!(self.ctx.terms.get(c), TermData::Var(..))
                            && !collection_vars.contains(&c)
                        {
                            collection_vars.push(c);
                        }
                    }
                    for arg in args.clone() {
                        stack.push(arg);
                    }
                }
                TermData::App(_, args) => {
                    for arg in args.clone() {
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
        for v in collection_vars {
            // Only flag variables that ARE aliased to a multiset expression: an
            // unaliased declared multiset variable is a genuinely free multiset
            // (no defining equality), which the count >= 0 bridge models soundly
            // (every nonnegative count is a legitimate model). The wrong-sat gap
            // is specifically a variable PINNED to a concrete expression by an
            // equality whose count we then fail to tie to the expression.
            if let Some(expr) = self.multiset_alias_target(v) {
                if !self.is_covered_multiset_chain(expr) {
                    return true;
                }
            }
        }
        false
    }

    /// Whether `term` is a Multiset carrier, i.e. an `Array(_ -> Int)`.
    fn is_multiset_carrier(&self, term: TermId) -> bool {
        matches!(self.ctx.terms.sort(term), Sort::Array(arr) if matches!(arr.element_sort, Sort::Int))
    }
}
