// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! GROUND + BOUNDED-UNFOLDING evaluation of the higher-order sequence
//! combinators `seq.map` / `seq.mapi` / `seq.foldl` / `seq.foldli` (#ho-seq).
//!
//! The combinators are deliberately OUTSIDE `SUPPORTED_SEQ_OPS`: with no
//! semantics they would become uninterpreted functions and produce false SAT,
//! so the allowlist guard fails any assertion set containing them closed to
//! `unknown`. This pass runs BEFORE that guard and ELIMINATES the combinators
//! whenever they can be finitely unfolded; whatever it cannot eliminate is
//! left intact for the guard (honest `unknown`, never a wrong verdict).
//!
//! Three sound unfolding modes:
//!
//! 1. STRUCTURAL — the sequence argument is built from `seq.empty` /
//!    `seq.unit` / `seq.++`, so its elements are syntactically known:
//!    `(seq.map f (seq.++ (seq.unit a) (seq.unit b)))` rewrites to
//!    `(seq.++ (seq.unit (select f a)) (seq.unit (select f b)))`, and
//!    `(seq.foldl f z ...)` to the nested `(select (select f ...) ...)`
//!    accumulator chain. A pure term-level equality (function-as-array
//!    application IS `select`), valid at any polarity and position.
//!
//! 2. PINNED-LENGTH — a top-level conjunct pins `(seq.len s)` to a concrete
//!    `n ≤ MAX_HO_SEQ_UNFOLD_LEN`; the elements are then `(seq.nth s j)` for
//!    `j < n`. The rewrite is equality-preserving in every model of the
//!    asserted length pin, hence equisatisfiable for the whole conjunction.
//!
//! 3. EQUATION BOUNDING — an equality ATOM `(= (seq.map f s) K)` whose other
//!    side `K` has structurally-known elements `k_0..k_{n-1}` is EQUIVALENT to
//!    `(and (= (seq.len s) n) (= (select f (seq.nth s j)) k_j) ...)`
//!    (`seq.map` preserves length; element-wise images determine the map).
//!    Being an equivalence — no fresh Skolems — the atom rewrite is sound
//!    under negation and arbitrary Boolean structure. The behavior-probe goal
//!    `(= (seq.map f s) (as seq.empty (Seq Int))) ∧ (seq.len s) > 0` reduces
//!    to `(= (seq.len s) 0) ∧ (seq.len s) > 0` — refuted by LIA.
//!
//! Function-as-array conventions (libz3-cross-checked in `ay-ffi/mk_ext.rs`):
//! `seq.map f : (Array E R)`, `seq.mapi f : (Array Int (Array E R))` (curried,
//! index first), `seq.foldl f : (Array A (Array E A))` (accumulator first),
//! `seq.foldli f : (Array Int (Array A (Array E A)))`. Every unfolding is
//! gated on the full sort shape; any mismatch leaves the term alone (the
//! guard then yields `unknown` — sort confusion can never build a mis-sorted
//! `select`).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::Sort;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use super::super::super::Executor;

/// Largest concrete unfolding length (elements per combinator). Beyond this
/// the pass leaves the term intact (honest `unknown`) instead of exploding
/// the assertion set.
const MAX_HO_SEQ_UNFOLD_LEN: usize = 32;

/// Fixpoint rounds: nested combinators (`seq.map g (seq.map f s)`) become
/// unfoldable only after the inner one is rewritten, so iterate a few times.
const MAX_HO_SEQ_UNFOLD_ROUNDS: usize = 3;

/// The higher-order sequence combinators this pass eliminates.
const HO_SEQ_OPS: &[&str] = &["seq.map", "seq.mapi", "seq.foldl", "seq.foldli"];

impl Executor {
    /// Eliminate finitely-unfoldable higher-order seq combinators from the
    /// live assertions (see module docs). Runs before the
    /// `SUPPORTED_SEQ_OPS` allowlist guard; leaves non-unfoldable
    /// occurrences untouched so the guard still fails closed to `unknown`.
    pub(in crate::executor) fn unfold_ho_seq_ops(&mut self) {
        if !self.assertions_contain_ho_seq_ops() {
            return;
        }
        for _ in 0..MAX_HO_SEQ_UNFOLD_ROUNDS {
            let subst = self.collect_ho_seq_unfoldings();
            if subst.is_empty() {
                break;
            }
            for i in 0..self.ctx.assertions.len() {
                let assertion = self.ctx.assertions[i];
                self.ctx.assertions[i] = self.ctx.terms.substitute_terms(assertion, &subst);
            }
        }
    }

    /// Quick token scan: does any live assertion contain a higher-order seq
    /// combinator (outside quantifier bodies — this pass never rewrites under
    /// a binder, so it does not look there either)?
    fn assertions_contain_ho_seq_ops(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if HO_SEQ_OPS.contains(&name.as_str()) {
                        return true;
                    }
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

    /// One round of unfolding: map each eliminable combinator term (or
    /// equality atom over one) to its finite rewrite.
    fn collect_ho_seq_unfoldings(&mut self) -> HashMap<TermId, TermId> {
        let pinned = self.collect_pinned_seq_lens();

        // Immutable walk first (term construction below needs &mut).
        let mut ho_terms: Vec<TermId> = Vec::new();
        let mut eq_atoms: Vec<TermId> = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if HO_SEQ_OPS.contains(&name.as_str()) {
                        ho_terms.push(term);
                    }
                    if name == "=" && args.len() == 2 {
                        let is_ho_map = |t: TermId| {
                            matches!(
                                self.ctx.terms.get(t),
                                TermData::App(Symbol::Named(n), _)
                                    if n == "seq.map" || n == "seq.mapi"
                            )
                        };
                        if is_ho_map(args[0]) || is_ho_map(args[1]) {
                            eq_atoms.push(term);
                        }
                    }
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
        // Deterministic order: visitation order depends on DFS over interned
        // ids; sort so rewrites are stable run-to-run.
        ho_terms.sort_unstable();
        eq_atoms.sort_unstable();

        let mut subst: HashMap<TermId, TermId> = HashMap::default();
        for term in ho_terms {
            if let Some(unfolded) = self.try_unfold_ho_term(term, &pinned) {
                subst.insert(term, unfolded);
            }
        }
        // Equality-atom bounding runs for every `(= map K)` atom — the atom
        // key takes precedence over the combinator-term key at the atom node
        // (`substitute_terms` checks the map before recursing), and the
        // element-wise form is deliberately preferred: it feeds LIA/EUF
        // directly instead of producing a structured-concat equality the
        // word-equation lane may not decide.
        for atom in eq_atoms {
            if let Some(rewritten) = self.try_bound_ho_map_equation(atom, &pinned) {
                subst.insert(atom, rewritten);
            }
        }
        subst
    }

    /// Concrete `(seq.len s) = n` pins from top-level conjuncts
    /// (`0 ≤ n ≤ MAX_HO_SEQ_UNFOLD_LEN`). Conflicting pins keep the first —
    /// the pin atoms themselves stay asserted, so a length contradiction is
    /// still refuted by LIA regardless of which pin the unfolding uses.
    fn collect_pinned_seq_lens(&self) -> HashMap<TermId, usize> {
        let mut pinned: HashMap<TermId, usize> = HashMap::default();
        for &assertion in &self.ctx.assertions {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            for (len_side, num_side) in [(args[0], args[1]), (args[1], args[0])] {
                let TermData::App(Symbol::Named(op), len_args) = self.ctx.terms.get(len_side)
                else {
                    continue;
                };
                if op != "seq.len" || len_args.len() != 1 {
                    continue;
                }
                let TermData::Const(Constant::Int(n)) = self.ctx.terms.get(num_side) else {
                    continue;
                };
                let Some(n) = n.to_usize() else { continue };
                if n > MAX_HO_SEQ_UNFOLD_LEN {
                    continue;
                }
                pinned.entry(len_args[0]).or_insert(n);
            }
        }
        pinned
    }

    /// Structurally-known elements of a sequence term: built entirely from
    /// `seq.empty` / `seq.unit` / `seq.++`. Elements themselves may be
    /// arbitrary (non-ground) terms.
    fn try_extract_seq_elements(&self, term: TermId) -> Option<Vec<TermId>> {
        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "seq.empty" if args.is_empty() => Some(Vec::new()),
                "seq.unit" if args.len() == 1 => Some(vec![args[0]]),
                "seq.++" if !args.is_empty() => {
                    let parts = args.clone();
                    let mut elems = Vec::new();
                    for part in parts {
                        elems.extend(self.try_extract_seq_elements(part)?);
                        if elems.len() > MAX_HO_SEQ_UNFOLD_LEN {
                            return None;
                        }
                    }
                    Some(elems)
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Elements of the combinator's sequence argument: structural if
    /// possible, else `(seq.nth s j)` under a top-level length pin.
    fn ho_seq_arg_elements(
        &mut self,
        s: TermId,
        pinned: &HashMap<TermId, usize>,
    ) -> Option<Vec<TermId>> {
        if let Some(elems) = self.try_extract_seq_elements(s) {
            return Some(elems);
        }
        let n = *pinned.get(&s)?;
        let elem_sort = self.ctx.terms.sort(s).seq_element()?.clone();
        Some(
            (0..n)
                .map(|j| {
                    let idx = self.ctx.terms.mk_int(BigInt::from(j));
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("seq.nth"), vec![s, idx], elem_sort.clone())
                })
                .collect(),
        )
    }

    /// `base + j`, constant-folded when `base` is a literal.
    fn ho_offset_index(&mut self, base: TermId, j: usize) -> TermId {
        if j == 0 {
            return base;
        }
        if let TermData::Const(Constant::Int(v)) = self.ctx.terms.get(base) {
            let sum = v + BigInt::from(j);
            return self.ctx.terms.mk_int(sum);
        }
        let j_term = self.ctx.terms.mk_int(BigInt::from(j));
        self.ctx
            .terms
            .mk_app(Symbol::named("+"), vec![base, j_term], Sort::Int)
    }

    /// Try to finitely unfold one combinator term. `None` leaves it for the
    /// allowlist guard.
    fn try_unfold_ho_term(
        &mut self,
        term: TermId,
        pinned: &HashMap<TermId, usize>,
    ) -> Option<TermId> {
        let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(term) else {
            return None;
        };
        let op = op.clone();
        let args = args.clone();
        match (op.as_str(), args.as_slice()) {
            ("seq.map", &[f, s]) => {
                let elems = self.ho_seq_arg_elements(s, pinned)?;
                self.build_map_unfold(term, f, None, &elems)
            }
            ("seq.mapi", &[f, i, s]) => {
                let elems = self.ho_seq_arg_elements(s, pinned)?;
                self.build_map_unfold(term, f, Some(i), &elems)
            }
            ("seq.foldl", &[f, a, s]) => {
                let elems = self.ho_seq_arg_elements(s, pinned)?;
                self.build_fold_unfold(term, f, None, a, &elems)
            }
            ("seq.foldli", &[f, i, a, s]) => {
                let elems = self.ho_seq_arg_elements(s, pinned)?;
                self.build_fold_unfold(term, f, Some(i), a, &elems)
            }
            _ => None,
        }
    }

    /// `(seq.map f s)` / `(seq.mapi f i s)` over known elements →
    /// concatenation of per-element `seq.unit (select … e)` images.
    /// Sort-shape gated; `index` is `Some(i)` for `seq.mapi`.
    fn build_map_unfold(
        &mut self,
        term: TermId,
        f: TermId,
        index: Option<TermId>,
        elems: &[TermId],
    ) -> Option<TermId> {
        let result_sort = self.ctx.terms.sort(term).clone();
        let range_sort = result_sort.seq_element()?.clone();
        let elem_sort = self.ho_map_elem_sort(f, index, &range_sort)?;
        if elems.iter().any(|&e| self.ctx.terms.sort(e) != &elem_sort) {
            return None;
        }
        if elems.is_empty() {
            return Some(self.ctx.terms.mk_app(
                Symbol::named("seq.empty"),
                Vec::<TermId>::new(),
                result_sort,
            ));
        }
        let mut units = Vec::with_capacity(elems.len());
        for (j, &e) in elems.iter().enumerate() {
            let image = match index {
                None => self.ctx.terms.mk_select(f, e),
                Some(i) => {
                    let idx = self.ho_offset_index(i, j);
                    let curried = self.ctx.terms.mk_select(f, idx);
                    self.ctx.terms.mk_select(curried, e)
                }
            };
            units.push(self.ctx.terms.mk_app(
                Symbol::named("seq.unit"),
                vec![image],
                result_sort.clone(),
            ));
        }
        Some(if units.len() == 1 {
            units[0]
        } else {
            self.ctx
                .terms
                .mk_app(Symbol::named("seq.++"), units, result_sort)
        })
    }

    /// The element sort a map/mapi function-as-array consumes, gated on the
    /// full expected array shape (`Array E R`, or `Array Int (Array E R)`
    /// for the indexed variant).
    fn ho_map_elem_sort(
        &self,
        f: TermId,
        index: Option<TermId>,
        range_sort: &Sort,
    ) -> Option<Sort> {
        let f_sort = self.ctx.terms.sort(f).clone();
        let Sort::Array(outer) = f_sort else {
            return None;
        };
        match index {
            None => (outer.element_sort == *range_sort).then(|| outer.index_sort.clone()),
            Some(i) => {
                if outer.index_sort != Sort::Int || self.ctx.terms.sort(i) != &Sort::Int {
                    return None;
                }
                let Sort::Array(inner) = &outer.element_sort else {
                    return None;
                };
                (inner.element_sort == *range_sort).then(|| inner.index_sort.clone())
            }
        }
    }

    /// `(seq.foldl f a s)` / `(seq.foldli f i a s)` over known elements →
    /// the nested `select` accumulator chain. Sort-shape gated.
    fn build_fold_unfold(
        &mut self,
        term: TermId,
        f: TermId,
        index: Option<TermId>,
        a: TermId,
        elems: &[TermId],
    ) -> Option<TermId> {
        let acc_sort = self.ctx.terms.sort(a).clone();
        if self.ctx.terms.sort(term) != &acc_sort {
            return None;
        }
        // Peel the expected function-as-array shape down to the element sort.
        let f_sort = self.ctx.terms.sort(f).clone();
        let mut layer = f_sort;
        if index.is_some() {
            let Sort::Array(outer) = layer else {
                return None;
            };
            if outer.index_sort != Sort::Int {
                return None;
            }
            if let Some(i) = index {
                if self.ctx.terms.sort(i) != &Sort::Int {
                    return None;
                }
            }
            layer = outer.element_sort;
        }
        let Sort::Array(acc_layer) = layer else {
            return None;
        };
        if acc_layer.index_sort != acc_sort {
            return None;
        }
        let Sort::Array(elem_layer) = &acc_layer.element_sort else {
            return None;
        };
        if elem_layer.element_sort != acc_sort {
            return None;
        }
        let elem_sort = elem_layer.index_sort.clone();
        if elems.iter().any(|&e| self.ctx.terms.sort(e) != &elem_sort) {
            return None;
        }
        let mut acc = a;
        for (j, &e) in elems.iter().enumerate() {
            let step = match index {
                None => self.ctx.terms.mk_select(f, acc),
                Some(i) => {
                    let idx = self.ho_offset_index(i, j);
                    let curried = self.ctx.terms.mk_select(f, idx);
                    self.ctx.terms.mk_select(curried, acc)
                }
            };
            acc = self.ctx.terms.mk_select(step, e);
        }
        Some(acc)
    }

    /// EQUATION BOUNDING: rewrite the equality ATOM
    /// `(= (seq.map f s) K)` (or the `seq.mapi` variant), where `K` has
    /// structurally-known elements `k_0..k_{n-1}`, to an equivalent
    /// element-wise form:
    ///
    /// * `s` structurally known too — a length mismatch is plain `false`;
    ///   otherwise `(and (= (select f e_j) k_j) …)` over the actual elements
    ///   (`true` for the empty case: `(seq.map f empty) = empty` is valid);
    /// * `s` opaque — `(and (= (seq.len s) n) (= (select f (seq.nth s j)) k_j) …)`.
    ///
    /// Both directions of each rewrite hold (`seq.map` preserves length, and
    /// equal lengths + equal element images determine the map), so this is an
    /// EQUIVALENCE — sound at ANY polarity, no fresh Skolems.
    fn try_bound_ho_map_equation(
        &mut self,
        atom: TermId,
        pinned: &HashMap<TermId, usize>,
    ) -> Option<TermId> {
        let TermData::App(sym, args) = self.ctx.terms.get(atom) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        let (lhs, rhs) = (args[0], args[1]);
        for (map_side, known_side) in [(lhs, rhs), (rhs, lhs)] {
            let TermData::App(Symbol::Named(op), margs) = self.ctx.terms.get(map_side) else {
                continue;
            };
            let (f, index, s) = match (op.as_str(), margs.as_slice()) {
                ("seq.map", &[f, s]) => (f, None, s),
                ("seq.mapi", &[f, i, s]) => (f, Some(i), s),
                _ => continue,
            };
            let Some(known_elems) = self.try_extract_seq_elements(known_side) else {
                continue;
            };
            let result_sort = self.ctx.terms.sort(map_side).clone();
            let Some(range_sort) = result_sort.seq_element().cloned() else {
                continue;
            };
            let Some(elem_sort) = self.ho_map_elem_sort(f, index, &range_sort) else {
                continue;
            };
            if self.ctx.terms.sort(s).seq_element() != Some(&elem_sort) {
                continue;
            }
            if known_elems
                .iter()
                .any(|&k| self.ctx.terms.sort(k) != &range_sort)
            {
                continue;
            }

            let n = known_elems.len();

            // Structural `s`: compare element-wise against the actual
            // elements — no seq machinery left in the rewrite at all.
            let s_elems = self.try_extract_seq_elements(s).or_else(|| {
                // A pinned length-0 `s` is exactly the empty sequence.
                (pinned.get(&s) == Some(&0)).then(Vec::new)
            });
            if let Some(s_elems) = s_elems {
                if s_elems
                    .iter()
                    .any(|&e| self.ctx.terms.sort(e) != &elem_sort)
                {
                    continue;
                }
                if s_elems.len() != n {
                    return Some(self.ctx.terms.mk_bool(false));
                }
                let mut conjuncts = Vec::with_capacity(n);
                for (j, (&e, &k)) in s_elems.iter().zip(known_elems.iter()).enumerate() {
                    let image = match index {
                        None => self.ctx.terms.mk_select(f, e),
                        Some(i) => {
                            let idx = self.ho_offset_index(i, j);
                            let curried = self.ctx.terms.mk_select(f, idx);
                            self.ctx.terms.mk_select(curried, e)
                        }
                    };
                    conjuncts.push(self.ctx.terms.mk_app(
                        Symbol::named("="),
                        vec![image, k],
                        Sort::Bool,
                    ));
                }
                return Some(match conjuncts.len() {
                    0 => self.ctx.terms.mk_bool(true),
                    1 => conjuncts[0],
                    _ => self
                        .ctx
                        .terms
                        .mk_app(Symbol::named("and"), conjuncts, Sort::Bool),
                });
            }

            // Opaque `s`: pin its length and constrain the `seq.nth` images.
            let len_s = self
                .ctx
                .terms
                .mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);
            let n_term = self.ctx.terms.mk_int(BigInt::from(n));
            let len_eq = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), vec![len_s, n_term], Sort::Bool);
            let mut conjuncts = vec![len_eq];
            for (j, &k) in known_elems.iter().enumerate() {
                let j_term = self.ctx.terms.mk_int(BigInt::from(j));
                let nth = self.ctx.terms.mk_app(
                    Symbol::named("seq.nth"),
                    vec![s, j_term],
                    elem_sort.clone(),
                );
                let image = match index {
                    None => self.ctx.terms.mk_select(f, nth),
                    Some(i) => {
                        let idx = self.ho_offset_index(i, j);
                        let curried = self.ctx.terms.mk_select(f, idx);
                        self.ctx.terms.mk_select(curried, nth)
                    }
                };
                conjuncts.push(self.ctx.terms.mk_app(
                    Symbol::named("="),
                    vec![image, k],
                    Sort::Bool,
                ));
            }
            return Some(if conjuncts.len() == 1 {
                conjuncts[0]
            } else {
                self.ctx
                    .terms
                    .mk_app(Symbol::named("and"), conjuncts, Sort::Bool)
            });
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn exec() -> Executor {
        Executor::new()
    }

    fn seq_int() -> Sort {
        Sort::seq(Sort::Int)
    }

    fn int_arr() -> Sort {
        Sort::array(Sort::Int, Sort::Int)
    }

    /// `seq.++ (seq.unit a) (seq.unit b)` over Int elements.
    fn ground_seq2(e: &mut Executor, a: TermId, b: TermId) -> TermId {
        let ua = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![a], seq_int());
        let ub = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![b], seq_int());
        e.ctx
            .terms
            .mk_app(Symbol::named("seq.++"), vec![ua, ub], seq_int())
    }

    fn mk_eq(e: &mut Executor, a: TermId, b: TermId) -> TermId {
        e.ctx
            .terms
            .mk_app(Symbol::named("="), vec![a, b], Sort::Bool)
    }

    #[test]
    fn structural_map_unfolds_to_selected_units() {
        let mut e = exec();
        let f = e.ctx.terms.mk_var("f", int_arr());
        let x = e.ctx.terms.mk_var("x", Sort::Int);
        let y = e.ctx.terms.mk_var("y", Sort::Int);
        let s = ground_seq2(&mut e, x, y);
        let map = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.map"), vec![f, s], seq_int());
        let k = e.ctx.terms.mk_var("k", seq_int());
        let atom = mk_eq(&mut e, map, k);
        e.ctx.assertions.push(atom);

        e.unfold_ho_seq_ops();
        assert!(
            !e.assertions_contain_ho_seq_ops(),
            "structural map must be eliminated"
        );
        // The rewritten equality's lhs is a concat of units of selects.
        let TermData::App(sym, args) = e.ctx.terms.get(e.ctx.assertions[0]) else {
            panic!("assertion must stay an equality");
        };
        assert_eq!(sym.name(), "=");
        let TermData::App(concat, units) = e.ctx.terms.get(args[0]) else {
            panic!("lhs must be an app");
        };
        assert_eq!(concat.name(), "seq.++");
        assert_eq!(units.len(), 2);
        for (&unit, &elem) in units.clone().iter().zip([x, y].iter()) {
            let TermData::App(u, uargs) = e.ctx.terms.get(unit) else {
                panic!("unit expected");
            };
            assert_eq!(u.name(), "seq.unit");
            let TermData::App(sel, sargs) = e.ctx.terms.get(uargs[0]) else {
                panic!("select expected");
            };
            assert_eq!(sel.name(), "select");
            assert_eq!(sargs, &vec![f, elem]);
        }
    }

    #[test]
    fn probe_shape_reduces_to_length_pin() {
        // (= (seq.map f s) ε) over an OPAQUE s ⟺ (= (seq.len s) 0).
        let mut e = exec();
        let f = e.ctx.terms.mk_var("f", int_arr());
        let s = e.ctx.terms.mk_var("s", seq_int());
        let map = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.map"), vec![f, s], seq_int());
        let empty = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.empty"), Vec::<TermId>::new(), seq_int());
        let atom = mk_eq(&mut e, map, empty);
        e.ctx.assertions.push(atom);

        e.unfold_ho_seq_ops();
        assert!(!e.assertions_contain_ho_seq_ops());
        let len_s = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);
        let zero = e.ctx.terms.mk_int(BigInt::from(0));
        let expected = mk_eq(&mut e, len_s, zero);
        assert_eq!(
            e.ctx.assertions[0], expected,
            "the probe atom must become the length pin"
        );
    }

    #[test]
    fn equation_bounding_length_mismatch_is_false() {
        // (= (seq.map f (unit x)) ε): both sides structural, 1 ≠ 0 → false.
        let mut e = exec();
        let f = e.ctx.terms.mk_var("f", int_arr());
        let x = e.ctx.terms.mk_var("x", Sort::Int);
        let ux = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![x], seq_int());
        let map = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.map"), vec![f, ux], seq_int());
        let empty = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.empty"), Vec::<TermId>::new(), seq_int());
        let atom = mk_eq(&mut e, map, empty);
        e.ctx.assertions.push(atom);

        e.unfold_ho_seq_ops();
        let false_t = e.ctx.terms.mk_bool(false);
        assert_eq!(
            e.ctx.assertions[0], false_t,
            "a structural length mismatch is plain false"
        );
    }

    #[test]
    fn fold_unfolds_to_accumulator_chain() {
        // foldl f a (unit x ++ unit y) → select(select(f, select(select(f,a),x)), y).
        let mut e = exec();
        let f = e.ctx.terms.mk_var("f", Sort::array(Sort::Int, int_arr()));
        let a = e.ctx.terms.mk_var("a", Sort::Int);
        let x = e.ctx.terms.mk_var("x", Sort::Int);
        let y = e.ctx.terms.mk_var("y", Sort::Int);
        let s = ground_seq2(&mut e, x, y);
        let fold = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.foldl"), vec![f, a, s], Sort::Int);
        let r = e.ctx.terms.mk_var("r", Sort::Int);
        let atom = mk_eq(&mut e, fold, r);
        e.ctx.assertions.push(atom);

        e.unfold_ho_seq_ops();
        assert!(!e.assertions_contain_ho_seq_ops());
        let step1 = e.ctx.terms.mk_select(f, a);
        let acc1 = e.ctx.terms.mk_select(step1, x);
        let step2 = e.ctx.terms.mk_select(f, acc1);
        let acc2 = e.ctx.terms.mk_select(step2, y);
        let expected = mk_eq(&mut e, acc2, r);
        assert_eq!(e.ctx.assertions[0], expected);
    }

    #[test]
    fn fold_over_empty_is_the_accumulator() {
        let mut e = exec();
        let f = e.ctx.terms.mk_var("f", Sort::array(Sort::Int, int_arr()));
        let a = e.ctx.terms.mk_var("a", Sort::Int);
        let empty = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.empty"), Vec::<TermId>::new(), seq_int());
        let fold = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.foldl"), vec![f, a, empty], Sort::Int);
        let r = e.ctx.terms.mk_var("r", Sort::Int);
        let atom = mk_eq(&mut e, fold, r);
        e.ctx.assertions.push(atom);

        e.unfold_ho_seq_ops();
        let expected = mk_eq(&mut e, a, r);
        assert_eq!(e.ctx.assertions[0], expected);
    }

    #[test]
    fn pinned_length_unfolds_nth_elements() {
        // (= (seq.len s) 2) pins s; (seq.map f s) unfolds over seq.nth.
        let mut e = exec();
        let f = e.ctx.terms.mk_var("f", int_arr());
        let s = e.ctx.terms.mk_var("s", seq_int());
        let len_s = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);
        let two = e.ctx.terms.mk_int(BigInt::from(2));
        let pin = mk_eq(&mut e, len_s, two);
        let map = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.map"), vec![f, s], seq_int());
        let k = e.ctx.terms.mk_var("k", seq_int());
        let atom = mk_eq(&mut e, map, k);
        e.ctx.assertions.push(pin);
        e.ctx.assertions.push(atom);

        e.unfold_ho_seq_ops();
        assert!(
            !e.assertions_contain_ho_seq_ops(),
            "a pinned-length map must unfold over seq.nth"
        );
    }

    #[test]
    fn mapi_offsets_the_index_per_element() {
        // (seq.mapi f 5 (unit x ++ unit y)) images at indices 5 and 6.
        let mut e = exec();
        let f = e.ctx.terms.mk_var("f", Sort::array(Sort::Int, int_arr()));
        let five = e.ctx.terms.mk_int(BigInt::from(5));
        let x = e.ctx.terms.mk_var("x", Sort::Int);
        let y = e.ctx.terms.mk_var("y", Sort::Int);
        let s = ground_seq2(&mut e, x, y);
        let mapi = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.mapi"), vec![f, five, s], seq_int());
        let k = e.ctx.terms.mk_var("k", seq_int());
        let atom = mk_eq(&mut e, mapi, k);
        e.ctx.assertions.push(atom);

        e.unfold_ho_seq_ops();
        assert!(!e.assertions_contain_ho_seq_ops());
        let six = e.ctx.terms.mk_int(BigInt::from(6));
        let f5 = e.ctx.terms.mk_select(f, five);
        let img0 = e.ctx.terms.mk_select(f5, x);
        let f6 = e.ctx.terms.mk_select(f, six);
        let img1 = e.ctx.terms.mk_select(f6, y);
        let u0 = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![img0], seq_int());
        let u1 = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![img1], seq_int());
        let concat = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.++"), vec![u0, u1], seq_int());
        let expected = mk_eq(&mut e, concat, k);
        assert_eq!(e.ctx.assertions[0], expected);
    }

    #[test]
    fn unboundable_map_stays_for_the_guard() {
        // (= (seq.map f s) (seq.map g t)) — nothing is ground or bounded.
        let mut e = exec();
        let f = e.ctx.terms.mk_var("f", int_arr());
        let g = e.ctx.terms.mk_var("g", int_arr());
        let s = e.ctx.terms.mk_var("s", seq_int());
        let t = e.ctx.terms.mk_var("t", seq_int());
        let map_f = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.map"), vec![f, s], seq_int());
        let map_g = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.map"), vec![g, t], seq_int());
        let atom = mk_eq(&mut e, map_f, map_g);
        e.ctx.assertions.push(atom);

        e.unfold_ho_seq_ops();
        assert!(
            e.assertions_contain_ho_seq_ops(),
            "unboundable combinators must remain for the allowlist guard"
        );
        assert!(
            e.assertions_contain_unsupported_seq_ops(),
            "the guard must still fail closed to Unknown"
        );
    }

    #[test]
    fn sort_shape_mismatch_leaves_the_term() {
        // f : (Array Bool Int) cannot map a (Seq Int) — no unfold, guard holds.
        let mut e = exec();
        let f = e.ctx.terms.mk_var("f", Sort::array(Sort::Bool, Sort::Int));
        let x = e.ctx.terms.mk_var("x", Sort::Int);
        let ux = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![x], seq_int());
        let map = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.map"), vec![f, ux], seq_int());
        let k = e.ctx.terms.mk_var("k", seq_int());
        let atom = mk_eq(&mut e, map, k);
        e.ctx.assertions.push(atom);

        e.unfold_ho_seq_ops();
        assert!(
            e.assertions_contain_ho_seq_ops(),
            "a sort-shape mismatch must never be unfolded"
        );
    }

    #[test]
    fn oversized_pin_is_not_unfolded() {
        let mut e = exec();
        let f = e.ctx.terms.mk_var("f", int_arr());
        let s = e.ctx.terms.mk_var("s", seq_int());
        let len_s = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);
        let big = e
            .ctx
            .terms
            .mk_int(BigInt::from(MAX_HO_SEQ_UNFOLD_LEN as u64 + 1));
        let pin = mk_eq(&mut e, len_s, big);
        let map = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.map"), vec![f, s], seq_int());
        let k = e.ctx.terms.mk_var("k", seq_int());
        let atom = mk_eq(&mut e, map, k);
        e.ctx.assertions.push(pin);
        e.ctx.assertions.push(atom);

        e.unfold_ho_seq_ops();
        assert!(
            e.assertions_contain_ho_seq_ops(),
            "an over-budget length pin must not explode the assertion set"
        );
    }

    #[test]
    fn nested_maps_unfold_via_fixpoint_rounds() {
        // seq.map g (seq.map f (unit x)) needs two rounds.
        let mut e = exec();
        let f = e.ctx.terms.mk_var("f", int_arr());
        let g = e.ctx.terms.mk_var("g", int_arr());
        let x = e.ctx.terms.mk_var("x", Sort::Int);
        let ux = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![x], seq_int());
        let inner = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.map"), vec![f, ux], seq_int());
        let outer = e
            .ctx
            .terms
            .mk_app(Symbol::named("seq.map"), vec![g, inner], seq_int());
        let k = e.ctx.terms.mk_var("k", seq_int());
        let atom = mk_eq(&mut e, outer, k);
        e.ctx.assertions.push(atom);

        e.unfold_ho_seq_ops();
        assert!(
            !e.assertions_contain_ho_seq_ops(),
            "nested combinators must unfold to a fixpoint"
        );
    }
}
