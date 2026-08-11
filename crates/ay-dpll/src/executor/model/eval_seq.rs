// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence evaluation helpers for model evaluation.
//!
//! Extracted from `mod.rs` to reduce file size (Wave C2 of #2998 module splits).

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};

use super::{EvalValue, Executor, Model};

/// Maximum concrete sequence length materialized for a gate-checked model
/// witness. This is intentionally larger than the sequence theory's 64-element
/// ground-reasoning cap: witness completion is linear output work and does not
/// synthesize solver terms. Matching the string witness cap keeps model memory
/// bounded while covering ordinary unbounded-length constraints.
const MAX_SEQ_MODEL_WITNESS_LEN: usize = 4096;

/// Outcome of resolving a `(seq.nth s i)` witness element during len/nth
/// reconstruction (`reconstruct_seq_from_len_nth`).
enum NthOutcome {
    /// The element value is determined.
    Value(EvalValue),
    /// No `(seq.nth s i)` term exists: the position is free, any value is sound.
    Unconstrained,
    /// A `(seq.nth s i)` term exists but its value cannot be recovered soundly.
    Unrecoverable,
}

impl Executor {
    /// Reconstruct a sequence-variable witness from its `(seq.len s) = N` and
    /// `(seq.nth s i) = v` constraints, for the model-output path only
    /// (#model-seq-witness).
    ///
    /// Used when a Seq-sorted variable has no direct seq-theory model entry and
    /// no defining `(= s (seq.++ ...))` equality, so [`Self::evaluate_term`] and
    /// the asserted-equality scan both yield `Unknown`. The bare default in that
    /// case is `(as seq.empty ...)` — length 0 — which VIOLATES any
    /// `(seq.len s) = N > 0` constraint (re-feeds to `unsat`).
    ///
    /// Returns `Some(EvalValue::Seq([..]))` when the length resolves to a
    /// concrete `N` (from the model value of some `(seq.len s)` term) AND every
    /// position is either unconstrained or has a soundly-recoverable value:
    ///
    /// * a `(seq.nth s i)` term that exists is resolved from an asserted
    ///   `(= (seq.nth s i) v)` equality, a bare top-level Bool assertion
    ///   `(seq.nth s i)` / `(not (seq.nth s i))` (the form `(= (seq.nth s i) true)`
    ///   simplifies to), or the theory model — whichever determines it;
    /// * a position with no `(seq.nth s i)` term is genuinely unconstrained, so
    ///   the element is COMPLETED here with the element sort's canonical default
    ///   (a sound arbitrary choice) — the produced sequence contains only
    ///   concrete elements, never `Unknown` (the printers refuse to fabricate a
    ///   value for `Unknown`, #no-fabricated-model-values).
    ///
    /// Returns `None` (degrade to the empty `(as seq.empty ...)` default — a
    /// documented, sound gap rather than a wrong witness) when a `(seq.len s)`
    /// term exists but no concrete length is available, `N` exceeds a sanity
    /// cap, or a referenced `(seq.nth s i)` term's value cannot be recovered.
    /// The verdict and theory solver are never consulted/changed — this only
    /// shapes the printed witness.
    ///
    /// LENGTH-UNCONSTRAINED problems (#7656 nth-only witnesses): when NO
    /// `(seq.len s)` application exists anywhere in the term store, the length
    /// is syntactically unconstrained — no assertion can distinguish lengths
    /// beyond what the `(seq.nth s k)` constraints require — so ANY length
    /// covering every constrained constant index is sound. We infer the
    /// MINIMAL such length, `1 + max k` over the existing `(seq.nth s k)`
    /// terms. This only shapes the candidate witness; downstream the strict +
    /// independent model-check gates re-validate it, so a wrong inference can
    /// only remain `Unknown`, never mint a wrong `sat`. When a `seq.len` term
    /// EXISTS but does not resolve, we keep returning `None` (fail-closed):
    /// guessing against an unresolved length constraint could re-feed to
    /// `unsat`.
    /// Length-PINNED witness for a Seq variable, for the sequence-carrier
    /// completion pass.
    ///
    /// Returns a witness ONLY when the model already DETERMINES the length —
    /// exactly the situation in which that pass's arbitrary "next unused
    /// length" would CONTRADICT the model it is completing. Two such cases:
    ///
    /// * a `(seq.len v)` term exists AND the model resolves it; or
    /// * NO `(seq.len v)` term exists, but a constant `(seq.nth v k)` does —
    ///   a read at index `k` forces `len > k`, so the "next unused length"
    ///   (frequently 0) puts the read out of range (#7656).
    ///
    /// `None` (no length term AND no constant read, or an unresolved length)
    /// leaves the existing distinct-length class materialization untouched, so
    /// equality-only classes keep their distinctness witness.
    ///
    /// WHY THIS EXISTS. `complete_uninterpreted_sort_model` assigns Seq classes
    /// distinct lengths 0,1,2,… ignoring `(seq.len v)` entirely, and commits
    /// them. Once committed, `evaluate_term(v)` is no longer `Unknown`, so `v`
    /// is never treated as a gap and the gap path that would call
    /// `reconstruct_seq_from_len_nth` never runs. The published witness then
    /// falsifies the very `(= (seq.len v) N)` in the problem, and the strict
    /// `sequences` oracle CORRECTLY refutes it — a computed `sat` published as
    /// `unknown`. Measured: `t` committed as `[]` where the model pinned
    /// `(seq.len t) = 3`.
    ///
    /// CANDIDATE ONLY, exactly the status of `reconstruct_seq_from_len_nth`:
    /// the strict and independent gates re-validate whatever this shapes, so a
    /// wrong inference can only remain `unknown`, never mint a wrong `sat`.
    pub(super) fn length_pinned_seq_witness(
        &self,
        model: &Model,
        seq_var: TermId,
    ) -> Option<EvalValue> {
        if !matches!(self.ctx.terms.get(seq_var), TermData::Var(..)) {
            return None;
        }
        // A POINT-READ-REDUCED variable carries its length in the fresh
        // `__ay_plen!<v>` symbol, never in the `(seq.len v)` term the
        // preconditions below consult. Under `--self-check` the ORIGINAL
        // assertion window is restored (see the QF_Seq deferral in
        // `check_sat`), so `(seq.len v)` exists in the term store again while
        // the model still pins only the proxy: `seq_len_term_exists` says
        // "true", `seq_len_model_value` says "None", and the precondition
        // bails — dropping the class to completion's arbitrary "next unused
        // length" of 0. The published witness is then the EMPTY sequence and
        // the strict `sequences` oracle rejects the very assertion the real
        // witness satisfies (`seq.len(a) > 100` => unknown under self-check
        // while the default mode emits a correct 101-element model).
        //
        // Try the reduced reconstruction FIRST. This is not a new inference:
        // it is the identical call `reconstruct_seq_from_len_nth` already
        // makes as its own first step, so a variable that passes the
        // preconditions reaches exactly the value it reached before. It
        // returns `None` for any variable that was not point-read-reduced (no
        // such fresh symbols exist), so every ordinary class is still governed
        // by the preconditions, and it stays fail-closed when the proxy length
        // is unpinned. Candidate only — both gates re-validate it.
        if let Some(v) = self.reconstruct_point_read_seq(model, seq_var) {
            return Some(v);
        }
        if self.seq_len_term_exists(seq_var) {
            // A length constraint exists: it must RESOLVE, else stay
            // fail-closed (guessing against it could re-feed to `unsat`).
            self.seq_len_model_value(model, seq_var)?;
        } else {
            // Length syntactically unconstrained. A constant `(seq.nth v k)`
            // still forces `len > k`, so the arbitrary "next unused length"
            // contradicts the model here exactly as a resolved `seq.len` would.
            // `reconstruct_seq_from_len_nth` then takes its own minimal
            // covering length `1 + max k`. With NO constant read either, the
            // length really is free — return `None` so equality-only classes
            // keep their distinct-length distinctness witness.
            self.max_constant_seq_nth_index(seq_var)?;
        }
        self.reconstruct_seq_from_len_nth(model, seq_var)
    }

    pub(super) fn reconstruct_seq_from_len_nth(
        &self,
        model: &Model,
        seq_var: TermId,
    ) -> Option<EvalValue> {
        // Only meaningful for an actual Seq-sorted variable.
        if !matches!(self.ctx.terms.get(seq_var), TermData::Var(..)) {
            return None;
        }
        // P0.1 phase-2a: a point-read-reduced variable has NO `seq.nth`/`seq.len`
        // terms of its own left in the assertions — it was rewritten to fresh
        // `__ay_pnth!<v>` / `__ay_plen!<v>` symbols. Rebuild it from those.
        if let Some(v) = self.reconstruct_point_read_seq(model, seq_var) {
            return Some(v);
        }
        // Guard: only reconstruct for a Seq-sorted variable. Element values are
        // rendered in their element sort by the caller's `format_seq_value`.
        let elem_sort = self.ctx.terms.sort(seq_var).seq_element()?.clone();

        let n = match self.seq_len_model_value(model, seq_var) {
            Some(n) => n,
            // A `(seq.len s)` term exists but its value cannot be pinned down:
            // stay fail-closed (empty-default documented gap).
            None if self.seq_len_term_exists(seq_var) => return None,
            // Length syntactically unconstrained: minimal covering length.
            None => self
                .max_constant_seq_nth_index(seq_var)
                .map_or(0, |k| k + 1),
        };
        // Keep witness materialization bounded independently of the sequence
        // theory's much smaller ground-reasoning cap. A witness at this stage is
        // re-checked by both model gates before it can authorize SAT.
        if n > MAX_SEQ_MODEL_WITNESS_LEN {
            return None;
        }
        if n == 0 {
            return Some(EvalValue::Seq(Vec::new()));
        }

        let mut elems = Vec::with_capacity(n);
        for i in 0..n {
            match self.seq_nth_outcome(model, seq_var, i) {
                // An element resolved from the EUF model arrives as an opaque
                // `Element("#x…")` canonical token even for an interpreted
                // element sort; re-parse it into the element sort's native
                // value so the independent gate can compare it against BV/Int
                // literals (same value, faithful representation).
                NthOutcome::Value(v) => {
                    let v = self.coerce_element_to_sort(v, &elem_sort);
                    elems.push(v);
                }
                // Unconstrained position: any element is sound — complete it
                // with the element sort's canonical default HERE so the
                // sequence value contains only concrete elements
                // (#no-fabricated-model-values). An element sort with no
                // canonical default (exotic nesting) degrades to the
                // documented empty-default gap below rather than guessing.
                NthOutcome::Unconstrained => {
                    let v = self.unconstrained_default_value(&elem_sort)?;
                    elems.push(v)
                }
                // A referenced `(seq.nth s i)` whose value we cannot pin down:
                // emitting a guessed element could re-feed to `unsat`, so bail to
                // the empty default (documented gap) instead.
                NthOutcome::Unrecoverable => return None,
            }
        }
        Some(EvalValue::Seq(elems))
    }

    /// Reconstruct a point-read-reduced sequence variable (P0.1 phase-2a) from
    /// its fresh `__ay_pnth!<v>` element function and `__ay_plen!<v>` length
    /// constant. Returns `None` when `seq_var` was NOT reduced (no such symbols
    /// in the term store), so the caller falls through to the ordinary
    /// `(seq.nth s i)` / `(seq.len s)` reconstruction.
    ///
    /// The emitted witness is SOUND: length is the reduced `__ay_plen!<v>` model
    /// value when a `(seq.len s)` constraint drove one (so the emitted `seq.len`
    /// matches exactly), else the minimal length covering the constrained reads.
    /// A read at an index `>= len` is simply not emitted — it is an
    /// out-of-bounds `seq.nth`, whose value is underspecified, so any covering
    /// length keeps the witness valid.
    fn reconstruct_point_read_seq(&self, model: &Model, seq_var: TermId) -> Option<EvalValue> {
        let elem_sort = self.ctx.terms.sort(seq_var).seq_element()?.clone();
        let pnth_prefix = format!("__ay_pnth!{}!", seq_var.0);
        let plen_name = format!("__ay_plen!{}", seq_var.0);

        let mut by_index: ay_core::kani_compat::DetHashMap<usize, TermId> = Default::default();
        let mut plen_term: Option<TermId> = None;
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::Var(name, _) = self.ctx.terms.get(tid) {
                if *name == plen_name {
                    plen_term = Some(tid);
                } else if let Some(k_str) = name.strip_prefix(pnth_prefix.as_str()) {
                    if let Ok(k) = k_str.parse::<usize>() {
                        by_index.entry(k).or_insert(tid);
                    }
                }
            }
        }
        // Not a reduced variable: no fresh symbols exist for it.
        if by_index.is_empty() && plen_term.is_none() {
            return None;
        }

        let n = if let Some(pt) = plen_term {
            match self.lookup_term_value(model, pt) {
                EvalValue::Rational(r)
                    if r.is_integer() && r.numer().sign() != num_bigint::Sign::Minus =>
                {
                    r.numer().to_usize()?
                }
                // A `(seq.len s)` constraint exists but its reduced length is not
                // pinned: stay fail-closed (empty-default documented gap).
                _ => return None,
            }
        } else {
            by_index.keys().map(|k| k + 1).max().unwrap_or(0)
        };
        // Point-read reduction must use the same bounded model-witness budget
        // as the ordinary len/nth reconstruction above.  Keeping the obsolete
        // 64-element ground-reasoning cap here makes this earlier path reject
        // otherwise small, independently validated witnesses (for example,
        // `seq.len(s) > 100`) before the ordinary path can recover them.
        if n > MAX_SEQ_MODEL_WITNESS_LEN {
            return None;
        }
        if n == 0 {
            return Some(EvalValue::Seq(Vec::new()));
        }

        let mut elems = Vec::with_capacity(n);
        for i in 0..n {
            match by_index.get(&i) {
                Some(&t) => {
                    let v = self.lookup_term_value(model, t);
                    if matches!(v, EvalValue::Unknown) {
                        elems.push(self.unconstrained_default_value(&elem_sort)?);
                    } else {
                        elems.push(self.coerce_element_to_sort(v, &elem_sort));
                    }
                }
                None => elems.push(self.unconstrained_default_value(&elem_sort)?),
            }
        }
        Some(EvalValue::Seq(elems))
    }

    /// Concrete model length of `seq_var`: the non-negative integer value of some
    /// `(seq.len seq_var)` term, read non-circularly via
    /// [`Self::lookup_term_value`] (theory models + asserted `(= (seq.len s) c)`
    /// equalities). `None` when no such term resolves to a concrete length.
    fn seq_len_model_value(&self, model: &Model, seq_var: TermId) -> Option<usize> {
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(tid) {
                if name == "seq.len" && args.len() == 1 && args[0] == seq_var {
                    if let EvalValue::Rational(r) = self.lookup_term_value(model, tid) {
                        if r.is_integer() && r.numer().sign() != num_bigint::Sign::Minus {
                            if let Some(n) = r.numer().to_usize() {
                                return Some(n);
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// Re-parse an opaque `EvalValue::Element` canonical token (as stored by
    /// e.g. the EUF term-value model) into `sort`'s native `EvalValue` when
    /// the token is a literal of that sort; every other value passes through
    /// unchanged. Never fabricates: the token and the parsed value denote the
    /// same constant.
    fn coerce_element_to_sort(&self, v: EvalValue, sort: &ay_core::Sort) -> EvalValue {
        let EvalValue::Element(ref s) = v else {
            return v;
        };
        let parsed = self.parse_model_value_string(s, &Some(sort.clone()));
        if matches!(parsed, EvalValue::Unknown | EvalValue::Element(_)) {
            v
        } else {
            parsed
        }
    }

    /// Whether any `(seq.len seq_var)` application exists in the term store.
    /// When none does, the sequence's length is syntactically unconstrained.
    fn seq_len_term_exists(&self, seq_var: TermId) -> bool {
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(tid) {
                if name == "seq.len" && args.len() == 1 && args[0] == seq_var {
                    return true;
                }
            }
        }
        false
    }

    /// Largest constant index `k` over the existing `(seq.nth seq_var k)`
    /// applications, or `None` when there is no such application.
    fn max_constant_seq_nth_index(&self, seq_var: TermId) -> Option<usize> {
        let mut max: Option<usize> = None;
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(tid) {
                if name == "seq.nth" && args.len() == 2 && args[0] == seq_var {
                    if let TermData::Const(Constant::Int(ci)) = self.ctx.terms.get(args[1]) {
                        if let Some(k) = ci.to_usize() {
                            max = Some(max.map_or(k, |m| m.max(k)));
                        }
                    }
                }
            }
        }
        max
    }

    /// Resolve the witness element at index `i` of `seq_var` (see
    /// [`NthOutcome`]).
    ///
    /// An asserted `(= (seq.nth s i) v)` and a bare top-level Bool assertion are
    /// preferred over the raw theory model: they are exactly the constraints the
    /// witness must satisfy. In particular a Bool-element `(seq.nth s i)` carries
    /// only a don't-care value in the SAT model (the constraint is enforced by the
    /// seq theory, not the propositional layer), and `(= (seq.nth s i) true)`
    /// simplifies to the bare atom `(seq.nth s i)` — so without the bare-assertion
    /// recovery the element would default to `false` and the witness would re-feed
    /// to `unsat`.
    fn seq_nth_outcome(&self, model: &Model, seq_var: TermId, i: usize) -> NthOutcome {
        let Some(tid) = self.find_seq_nth_term(seq_var, i) else {
            return NthOutcome::Unconstrained;
        };
        // Asserted `(= (seq.nth s i) v)` is authoritative.
        if let Some(v) = self.extract_value_from_asserted_equalities(model, tid) {
            if !matches!(v, EvalValue::Unknown) {
                return NthOutcome::Value(v);
            }
        }
        // Bool element pinned by a bare top-level assertion / negation.
        if matches!(self.ctx.terms.sort(tid), ay_core::Sort::Bool) {
            if let Some(b) = self.bool_atom_asserted_value(tid) {
                return NthOutcome::Value(EvalValue::Bool(b));
            }
        }
        // Otherwise read the term's value from the theory models (non-circular).
        let v = self.lookup_term_value(model, tid);
        if !matches!(v, EvalValue::Unknown) {
            return NthOutcome::Value(v);
        }
        // Element with no direct value: constrained only through asserted
        // (dis)equalities with OTHER terms (e.g. `(not (= (seq.nth s 0) v))`,
        // or `(= (seq.nth s 0) (seq.nth t 0))` chains). Complete it from the
        // equality class: honor a pinned value when one side of the class
        // resolves, otherwise choose a value avoiding every resolvable
        // disequality. The choice only shapes the candidate witness — the
        // strict + independent model-check gates re-validate it downstream,
        // so a wrong choice can only remain `Unknown`, never mint a wrong
        // `sat` (#7656).
        if let Some(v) = self.seq_nth_class_completion_value(model, tid) {
            return NthOutcome::Value(v);
        }
        NthOutcome::Unrecoverable
    }

    /// Completion value for a `(seq.nth s i)` term `tid` that has no direct
    /// model value: walk the asserted-equality class of `seq.nth` terms
    /// containing `tid` (top-level assertions, descending through `and`),
    /// collecting
    ///
    /// * PINNED values — an equality between a class member and a term that
    ///   evaluates concretely, and
    /// * AVOID values — a disequality (`(not (= …))` / binary `distinct`)
    ///   between a class member and a term that evaluates concretely.
    ///
    /// All pinned values must agree and not collide with an avoid value
    /// (otherwise `None` — the constraints are beyond this completion, stay
    /// fail-closed). With no pinned value, the smallest element-sort value
    /// outside the avoid set is chosen. DETERMINISTIC: every class member
    /// recomputes the same class and the same choice, so linked cells across
    /// different sequence variables (`(= (seq.nth s0 0) (seq.nth s1 0))`)
    /// complete to the same value.
    fn seq_nth_class_completion_value(&self, model: &Model, tid: TermId) -> Option<EvalValue> {
        let is_seq_nth = |t: TermId| {
            matches!(self.ctx.terms.get(t),
                TermData::App(Symbol::Named(name), args) if name == "seq.nth" && args.len() == 2)
        };
        let mut class: Vec<TermId> = vec![tid];
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        seen.insert(tid);
        let mut pinned: Vec<EvalValue> = Vec::new();
        let mut avoid: Vec<EvalValue> = Vec::new();
        // Top-level assertions (descending through `and`) are unconditionally
        // true in every model, so their (dis)equalities are forced.
        let mut atoms: Vec<TermId> = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        while let Some(a) = stack.pop() {
            if !visited.insert(a) {
                continue;
            }
            match self.ctx.terms.get(a) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    stack.extend(args.iter().copied());
                }
                _ => atoms.push(a),
            }
        }
        // Fixpoint over the class: equalities between two seq.nth terms merge
        // them; (dis)equalities against other terms contribute values.
        let mut cursor = 0;
        while cursor < class.len() {
            let member = class[cursor];
            cursor += 1;
            for &atom in &atoms {
                // Positive equality on the member.
                if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(atom) {
                    if name == "=" && args.len() == 2 && (args[0] == member || args[1] == member) {
                        let other = if args[0] == member { args[1] } else { args[0] };
                        if is_seq_nth(other) {
                            if seen.insert(other) {
                                class.push(other);
                            }
                        } else {
                            let v = self.evaluate_term(model, other);
                            if !matches!(v, EvalValue::Unknown) {
                                pinned.push(v);
                            }
                        }
                        continue;
                    }
                    // Binary distinct is a disequality.
                    if name == "distinct"
                        && args.len() == 2
                        && (args[0] == member || args[1] == member)
                    {
                        let other = if args[0] == member { args[1] } else { args[0] };
                        let v = self.evaluate_term(model, other);
                        if !matches!(v, EvalValue::Unknown) {
                            avoid.push(v);
                        }
                        continue;
                    }
                }
                // Negated equality on the member.
                if let TermData::Not(inner) = self.ctx.terms.get(atom) {
                    if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(*inner) {
                        if name == "="
                            && args.len() == 2
                            && (args[0] == member || args[1] == member)
                        {
                            let other = if args[0] == member { args[1] } else { args[0] };
                            let v = self.evaluate_term(model, other);
                            if !matches!(v, EvalValue::Unknown) {
                                avoid.push(v);
                            }
                        }
                    }
                }
            }
        }
        if let Some(first) = pinned.first() {
            // All pinned values must agree and dodge every avoid value; a
            // conflict is beyond this completion (likely unsat anyway).
            if pinned.iter().any(|p| p != first) || avoid.iter().any(|a| a == first) {
                return None;
            }
            return Some(first.clone());
        }
        let elem_sort = self.ctx.terms.sort(tid).clone();
        Self::smallest_value_avoiding(&elem_sort, &avoid)
    }

    /// Smallest value of `sort` not contained in `avoid` (Bool/Int/BitVec
    /// only — the sorts a completed nth-cell witness can safely enumerate).
    fn smallest_value_avoiding(sort: &ay_core::Sort, avoid: &[EvalValue]) -> Option<EvalValue> {
        match sort {
            ay_core::Sort::Bool => [false, true]
                .into_iter()
                .map(EvalValue::Bool)
                .find(|v| !avoid.contains(v)),
            ay_core::Sort::Int => (0..=avoid.len() as u64)
                .map(|k| EvalValue::Rational(BigRational::from(BigInt::from(k))))
                .find(|v| !avoid.contains(v)),
            ay_core::Sort::BitVec(bv) => {
                let width = bv.width;
                let max = if width >= 64 {
                    u64::MAX
                } else {
                    (1u64 << width) - 1
                };
                (0..=(avoid.len() as u64).min(max)).find_map(|k| {
                    let v = EvalValue::BitVec {
                        value: BigInt::from(k),
                        width,
                    };
                    (!avoid.contains(&v)).then_some(v)
                })
            }
            _ => None,
        }
    }

    /// Find a `(seq.nth seq_var i)` term with a constant index equal to `i`.
    fn find_seq_nth_term(&self, seq_var: TermId, i: usize) -> Option<TermId> {
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(tid) {
                if name == "seq.nth" && args.len() == 2 && args[0] == seq_var {
                    if let TermData::Const(Constant::Int(ci)) = self.ctx.terms.get(args[1]) {
                        if ci.to_usize() == Some(i) {
                            return Some(tid);
                        }
                    }
                }
            }
        }
        None
    }

    /// Truth value of a Bool `atom` forced by a bare top-level assertion: `Some(true)`
    /// if the atom is asserted directly, `Some(false)` if its negation is, else
    /// `None`. Descends through a top-level `and` (assertions may be un-split at
    /// model time). Sound: a top-level assertion holds in every model, so the
    /// reflected element value is forced.
    fn bool_atom_asserted_value(&self, atom: TermId) -> Option<bool> {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        while let Some(a) = stack.pop() {
            if !seen.insert(a) {
                continue;
            }
            if a == atom {
                return Some(true);
            }
            match self.ctx.terms.get(a) {
                TermData::Not(inner) if *inner == atom => return Some(false),
                TermData::App(Symbol::Named(name), args) => match name.as_str() {
                    "and" => stack.extend(args.iter().copied()),
                    "not" if args.len() == 1 && args[0] == atom => return Some(false),
                    _ => {}
                },
                _ => {}
            }
        }
        None
    }

    /// Evaluate a sequence application term.
    ///
    /// Handles all `seq.*` operations including construction,
    /// indexing, slicing, search, and replacement.
    pub(super) fn evaluate_seq_app(&self, model: &Model, name: &str, args: &[TermId]) -> EvalValue {
        match name {
            // === Sequence operations (ground evaluation, #5997) ===
            "seq.unit" if args.len() == 1 => {
                let elem = self.evaluate_term(model, args[0]);
                match elem {
                    EvalValue::Unknown => EvalValue::Unknown,
                    v => EvalValue::Seq(vec![v]),
                }
            }
            "seq.empty" => EvalValue::Seq(vec![]),
            "seq.++" => {
                let mut result = Vec::new();
                for &arg in args {
                    match self.evaluate_term(model, arg) {
                        EvalValue::Seq(elems) => result.extend(elems),
                        _ => return EvalValue::Unknown,
                    }
                }
                EvalValue::Seq(result)
            }
            "seq.len" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Seq(elems) => {
                    EvalValue::Rational(BigRational::from(BigInt::from(elems.len())))
                }
                _ => EvalValue::Unknown,
            },
            "seq.nth" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Seq(elems), EvalValue::Rational(i_rat)) => {
                        if let Some(i) = i_rat.to_integer().to_usize() {
                            if i < elems.len() {
                                elems.into_iter().nth(i).unwrap_or(EvalValue::Unknown)
                            } else {
                                // Out of bounds: unspecified per SMT-LIB
                                EvalValue::Unknown
                            }
                        } else {
                            EvalValue::Unknown
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.extract" if args.len() == 3 => {
                let src_val = self.evaluate_term(model, args[0]);
                // SMT-LIB: extracting from the EMPTY sequence yields the empty
                // sequence for ANY offset and length (there is nothing to
                // extract). Decide this even when the offset/length operands are
                // Unknown (e.g. a `(seq.nth ...)` out-of-bounds offset), since
                // the result is genuinely empty regardless (#seq-extract-empty).
                if let EvalValue::Seq(ref elems) = src_val {
                    if elems.is_empty() {
                        return EvalValue::Seq(vec![]);
                    }
                }
                match (
                    src_val,
                    self.evaluate_term(model, args[1]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (
                        EvalValue::Seq(elems),
                        EvalValue::Rational(i_rat),
                        EvalValue::Rational(n_rat),
                    ) => {
                        let i = i_rat.to_integer();
                        let n = n_rat.to_integer();
                        let len = BigInt::from(elems.len());
                        // SMT-LIB: out-of-bounds returns empty
                        if i < BigInt::zero() || n <= BigInt::zero() || i >= len {
                            EvalValue::Seq(vec![])
                        } else if let (Some(start), Some(count)) = (i.to_usize(), n.to_usize()) {
                            let end = std::cmp::min(start + count, elems.len());
                            EvalValue::Seq(elems[start..end].to_vec())
                        } else {
                            EvalValue::Unknown
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.contains" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Seq(haystack), EvalValue::Seq(needle)) => {
                        if needle.is_empty() {
                            EvalValue::Bool(true)
                        } else if needle.len() > haystack.len() {
                            EvalValue::Bool(false)
                        } else {
                            let found = haystack
                                .windows(needle.len())
                                .any(|w| w == needle.as_slice());
                            EvalValue::Bool(found)
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.prefixof" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Seq(prefix), EvalValue::Seq(s)) => {
                        EvalValue::Bool(s.starts_with(prefix.as_slice()))
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.suffixof" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Seq(suffix), EvalValue::Seq(s)) => {
                        EvalValue::Bool(s.ends_with(suffix.as_slice()))
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.indexof" if args.len() == 3 => {
                let s_val = self.evaluate_term(model, args[0]);
                let t_val = self.evaluate_term(model, args[1]);
                // Offset-independent case: when the needle `t` is non-empty and
                // strictly longer than the haystack `s`, it cannot occur at ANY
                // (in-range) start position, so seq.indexof is -1 for every
                // offset (offset < 0 -> -1; offset >= 0 -> not found -> -1).
                // Decide this even when the offset operand is Unknown — the
                // result is genuinely the SMT-LIB value -1 regardless. This lets
                // model validation reject e.g.
                //   (< 2 (seq.indexof empty (seq.unit 8) <symbolic-offset>))
                // whose offset is an unresolved (seq.nth ...) (#seq-indexof-empty).
                if let (EvalValue::Seq(ref s), EvalValue::Seq(ref t)) = (&s_val, &t_val) {
                    if !t.is_empty() && t.len() > s.len() {
                        return EvalValue::Rational(BigRational::from(BigInt::from(-1)));
                    }
                }
                match (s_val, t_val, self.evaluate_term(model, args[2])) {
                    (EvalValue::Seq(s), EvalValue::Seq(t), EvalValue::Rational(offset_rat)) => {
                        let offset = offset_rat.to_integer();
                        if offset < BigInt::zero() || offset > BigInt::from(s.len()) {
                            EvalValue::Rational(BigRational::from(BigInt::from(-1)))
                        } else if t.is_empty() {
                            // Empty needle: return offset (clamped to len)
                            let o = std::cmp::min(offset.to_usize().unwrap_or(s.len()), s.len());
                            EvalValue::Rational(BigRational::from(BigInt::from(o)))
                        } else if let Some(start) = offset.to_usize() {
                            let mut result = -1i64;
                            if start + t.len() <= s.len() {
                                for i in start..=(s.len() - t.len()) {
                                    if s[i..i + t.len()] == *t.as_slice() {
                                        result = i as i64;
                                        break;
                                    }
                                }
                            }
                            EvalValue::Rational(BigRational::from(BigInt::from(result)))
                        } else {
                            EvalValue::Rational(BigRational::from(BigInt::from(-1)))
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.last_indexof" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Seq(haystack), EvalValue::Seq(needle)) => {
                        if needle.is_empty() {
                            // Empty needle: return len(haystack)
                            EvalValue::Rational(BigRational::from(BigInt::from(haystack.len())))
                        } else if needle.len() > haystack.len() {
                            EvalValue::Rational(BigRational::from(BigInt::from(-1)))
                        } else {
                            // Scan from right to left
                            let mut result = -1i64;
                            for i in (0..=(haystack.len() - needle.len())).rev() {
                                if haystack[i..i + needle.len()] == *needle.as_slice() {
                                    result = i as i64;
                                    break;
                                }
                            }
                            EvalValue::Rational(BigRational::from(BigInt::from(result)))
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.replace" if args.len() == 3 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (EvalValue::Seq(s), EvalValue::Seq(src), EvalValue::Seq(dst)) => {
                        if src.is_empty() {
                            // Replace empty: prepend dst
                            let mut result = dst;
                            result.extend(s);
                            EvalValue::Seq(result)
                        } else if let Some(pos) =
                            s.windows(src.len()).position(|w| w == src.as_slice())
                        {
                            let mut result = s[..pos].to_vec();
                            result.extend(dst);
                            result.extend(s[pos + src.len()..].to_vec());
                            EvalValue::Seq(result)
                        } else {
                            // Not found: return original
                            EvalValue::Seq(s)
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.replace_all" if args.len() == 3 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (EvalValue::Seq(s), EvalValue::Seq(src), EvalValue::Seq(dst)) => {
                        if src.is_empty() {
                            // Replace empty with all: unchanged
                            EvalValue::Seq(s)
                        } else {
                            // Replace all non-overlapping occurrences left to right
                            let mut result = Vec::new();
                            let mut i = 0;
                            while i < s.len() {
                                if i + src.len() <= s.len()
                                    && s[i..i + src.len()] == *src.as_slice()
                                {
                                    result.extend_from_slice(&dst);
                                    i += src.len();
                                } else {
                                    result.push(s[i].clone());
                                    i += 1;
                                }
                            }
                            EvalValue::Seq(result)
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            _ => EvalValue::Unknown,
        }
    }
}
