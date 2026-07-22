// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ground sequence reconstruction and evaluation helpers.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use num_traits::ToPrimitive;

use ay_core::term::{Constant, Symbol, TermData, TermId};

use super::super::super::Executor;

/// Three-valued result of evaluating a search predicate over a
/// partially-determined sequence (#seq-partial-pred).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum SeqTri {
    /// Holds in every model.
    True,
    /// Fails in every model (a pinned element makes the predicate impossible).
    False,
    /// Underdetermined — neither forced.
    Unknown,
}

impl Executor {
    /// Build a map from variables to ground sequence expressions from equality
    /// assertions. When we see `(= x EXPR)` or `(= EXPR x)` where `x` is a
    /// variable and `EXPR` is a ground sequence (composed of seq.unit/seq.++/
    /// seq.empty over constants), record the mapping.
    ///
    /// Also reconstructs ground sequences from nth constraints (#6028):
    /// when a variable `s` has `(= (seq.len s) n)` and all `n` elements
    /// defined via `(= (seq.nth s 0) c0) ... (= (seq.nth s (n-1)) c_{n-1})`,
    /// synthesizes `seq.++(seq.unit(c0), ...)` and adds it to the map.
    ///
    /// Used by `generate_seq_contains_axioms` to evaluate ground contains
    /// and fix false-SAT (#6024, #6028).
    pub(super) fn build_ground_seq_map(&mut self) -> HashMap<TermId, TermId> {
        let mut map = HashMap::default();

        // Pass 1: direct variable-to-ground-seq equalities
        for &assertion in &self.ctx.assertions {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name == "=" && args.len() == 2 {
                    let (a, b) = (args[0], args[1]);
                    if matches!(self.ctx.terms.get(a), TermData::Var(..))
                        && self.try_extract_ground_seq(b).is_some()
                    {
                        map.insert(a, b);
                    } else if matches!(self.ctx.terms.get(b), TermData::Var(..))
                        && self.try_extract_ground_seq(a).is_some()
                    {
                        map.insert(b, a);
                    }
                }
            }
        }

        // Pass 1b: transitive variable-to-ground-seq equalities (#seq-indexof-alias).
        //
        // A direct `(= var GROUND)` is captured above, but a seq variable equated
        // to a ground sequence only through a variable→variable chain
        // (e.g. `(= v "cba") (= v t)` ⊢ `t = "cba"`) is missed by the syntactic
        // Pass 1. Resolve each seq variable through the transitive equality closure
        // (reusing `build_seq_alias_map` + `resolve_seq_alias`, the same BFS the
        // structural-nth path uses) and, if its class reaches a concrete ground
        // sequence, record `var -> ground`.
        //
        // Sound: top-level `(= a b)` over seq-sorted operands are exactly the
        // equality-class edges the solver enforces, so any ground sequence reached
        // through that closure is genuinely equal to the variable. This only adds
        // mappings (never removes), so it can only tighten ground evaluation.
        let aliases = self.build_seq_alias_map();
        if !aliases.is_empty() {
            // Collect the seq variables appearing as alias sources.
            let mut seq_vars: Vec<TermId> = Vec::new();
            for (v, _) in &aliases {
                if !seq_vars.contains(v) {
                    seq_vars.push(*v);
                }
            }
            for var in seq_vars {
                if map.contains_key(&var) {
                    continue;
                }
                let resolved = self.resolve_seq_alias(var, &aliases);
                if resolved != var && self.try_extract_ground_seq(resolved).is_some() {
                    map.insert(var, resolved);
                }
            }
        }

        // Pass 2: reconstruct ground sequences from nth + len constraints (#6028).
        let mut len_map: HashMap<TermId, usize> = HashMap::default();
        let mut nth_map: HashMap<TermId, Vec<(usize, TermId)>> = HashMap::default();

        // Bool-element nth constraints survive only as `(seq.nth s i)` /
        // `(not (seq.nth s i))` (the equality simplifier rewrites
        // `(= b true) -> b` and `(= b false) -> (not b)`), so precompute the
        // canonical Bool constants to record as the element values (#seq-bool-nth).
        let true_t = self.ctx.terms.mk_bool(true);
        let false_t = self.ctx.terms.mk_bool(false);

        for &assertion in &self.ctx.assertions {
            Self::try_extract_bool_nth_constraint(
                &self.ctx.terms,
                assertion,
                true_t,
                false_t,
                &mut nth_map,
            );
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name != "=" || args.len() != 2 {
                    continue;
                }
                let (a, b) = (args[0], args[1]);

                Self::try_extract_len_constraint(&self.ctx.terms, a, b, &mut len_map);
                Self::try_extract_len_constraint(&self.ctx.terms, b, a, &mut len_map);

                Self::try_extract_nth_constraint(&self.ctx.terms, a, b, &mut nth_map);
                Self::try_extract_nth_constraint(&self.ctx.terms, b, a, &mut nth_map);
            }
        }

        // For each variable with known length and all elements defined,
        // synthesize a ground sequence and add to the map.
        for (var, len) in &len_map {
            if map.contains_key(var) {
                continue;
            }
            // Cap at 64 elements to avoid blowup
            if *len > 64 {
                continue;
            }
            if let Some(elements) = nth_map.get(var) {
                let mut index_vals: Vec<Option<TermId>> = vec![None; *len];
                for &(idx, val) in elements {
                    if idx < *len {
                        index_vals[idx] = Some(val);
                    }
                }
                if index_vals.iter().all(Option::is_some) {
                    if let Some(ground_term) = self.synthesize_ground_seq(*var, &index_vals) {
                        map.insert(*var, ground_term);
                    }
                }
            }
        }

        map
    }

    /// Build a PARTIAL element map for seq variables: for each seq variable with a
    /// definite length `(= (seq.len s) N)`, a `Vec<Option<elem_const>>` of length
    /// `N` whose entry `i` is `Some(c)` iff `(= (seq.nth s i) c)` is a
    /// definitely-true top-level fact (including the Bool-rewritten
    /// `(seq.nth s i)` / `(not (seq.nth s i))` forms), else `None`.
    ///
    /// Unlike `build_ground_seq_map` (which only reconstructs FULLY-determined
    /// sequences), this keeps the per-index info even when some elements are
    /// undetermined, enabling a sound three-valued evaluation of search predicates
    /// over partially-determined sequences (#seq-partial-pred). Element values are
    /// interned constant `TermId`s, so equality of values is `TermId` equality.
    pub(super) fn build_partial_seq_element_map(&mut self) -> HashMap<TermId, Vec<Option<TermId>>> {
        let mut len_map: HashMap<TermId, usize> = HashMap::default();
        let mut nth_map: HashMap<TermId, Vec<(usize, TermId)>> = HashMap::default();
        let true_t = self.ctx.terms.mk_bool(true);
        let false_t = self.ctx.terms.mk_bool(false);

        for &assertion in &self.ctx.assertions {
            Self::try_extract_bool_nth_constraint(
                &self.ctx.terms,
                assertion,
                true_t,
                false_t,
                &mut nth_map,
            );
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name != "=" || args.len() != 2 {
                    continue;
                }
                let (a, b) = (args[0], args[1]);
                Self::try_extract_len_constraint(&self.ctx.terms, a, b, &mut len_map);
                Self::try_extract_len_constraint(&self.ctx.terms, b, a, &mut len_map);
                Self::try_extract_nth_constraint(&self.ctx.terms, a, b, &mut nth_map);
                Self::try_extract_nth_constraint(&self.ctx.terms, b, a, &mut nth_map);
            }
        }

        // Fold in element pins implied by ASSERTED-TRUE ground prefixof/suffixof
        // atoms (#seq-pairwise-compat): a top-level `(seq.prefixof p s)` with a
        // ground p definitely pins `s[i] = p[i]` for `i < len(p)`; a top-level
        // `(seq.suffixof p s)` (with a definite length N for s) pins the tail
        // `s[N-len(p)+i] = p[i]`. These are sound DEFINITE facts (they hold in every
        // model where the assertion holds, i.e. every model), so the three-valued
        // partial-predicate pass can use them to refute a contradictory
        // contains/prefixof/suffixof over an s whose elements are otherwise only
        // constrained by these endpoint predicates plus a length.
        self.fold_asserted_endpoint_pins(&len_map, &mut nth_map);

        let mut out: HashMap<TermId, Vec<Option<TermId>>> = HashMap::default();
        for (var, len) in &len_map {
            if *len > 64 {
                continue;
            }
            let mut index_vals: Vec<Option<TermId>> = vec![None; *len];
            if let Some(elements) = nth_map.get(var) {
                for &(idx, val) in elements {
                    if idx < *len {
                        index_vals[idx] = Some(val);
                    }
                }
            }
            out.insert(*var, index_vals);
        }
        out
    }

    /// Fold pins implied by ASSERTED-TRUE ground `prefixof`/`suffixof` atoms into
    /// `nth_map` (#seq-pairwise-compat). Only DIRECT top-level positive assertions
    /// `(seq.prefixof p s)` / `(seq.suffixof p s)` with a ground p and a variable s
    /// are used — never an atom nested under `and`/`or`/`not` (which would not be
    /// definitely true). Suffix pins require a definite length `N` for `s`.
    ///
    /// SOUND: an asserted `prefixof(p, s)` makes `s[i] = p[i]` true in every model
    /// (`i < len(p) <= len(s)`); an asserted `suffixof(p, s)` with `len(s)=N` makes
    /// `s[N-len(p)+i] = p[i]` true in every model. Adding these definite facts can
    /// only sharpen the three-valued evaluation, never falsify a real model.
    fn fold_asserted_endpoint_pins(
        &self,
        len_map: &HashMap<TermId, usize>,
        nth_map: &mut HashMap<TermId, Vec<(usize, TermId)>>,
    ) {
        for &assertion in &self.ctx.assertions {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            let is_prefix = name == "seq.prefixof";
            let is_suffix = name == "seq.suffixof";
            if (!is_prefix && !is_suffix) || args.len() != 2 {
                continue;
            }
            let needle = args[0];
            let s = args[1];
            if !matches!(self.ctx.terms.get(s), TermData::Var(..)) {
                continue;
            }
            let Some(units) = self.try_extract_ground_seq(needle) else {
                continue;
            };
            let Some(consts) = units
                .iter()
                .map(|&u| self.seq_unit_inner_const(u))
                .collect::<Option<Vec<TermId>>>()
            else {
                continue;
            };
            let lp = consts.len();
            if is_prefix {
                for (i, &c) in consts.iter().enumerate() {
                    nth_map.entry(s).or_default().push((i, c));
                }
            } else if let Some(&n) = len_map.get(&s) {
                // suffixof: tail-aligned, needs the definite length to index.
                if lp <= n {
                    for (i, &c) in consts.iter().enumerate() {
                        nth_map.entry(s).or_default().push((n - lp + i, c));
                    }
                }
            }
        }
    }

    /// Extract `(= (seq.len s) n)`: lhs is `seq.len(var)`, rhs is int constant.
    fn try_extract_len_constraint(
        terms: &ay_core::term::TermStore,
        lhs: TermId,
        rhs: TermId,
        len_map: &mut HashMap<TermId, usize>,
    ) {
        if let TermData::App(Symbol::Named(name), args) = terms.get(lhs) {
            if name == "seq.len" && args.len() == 1 {
                let seq_var = args[0];
                if matches!(terms.get(seq_var), TermData::Var(..)) {
                    if let TermData::Const(Constant::Int(n)) = terms.get(rhs) {
                        if let Some(len) = n.to_usize() {
                            len_map.insert(seq_var, len);
                        }
                    }
                }
            }
        }
    }

    /// Extract `(= (seq.nth s i) c)`: lhs is `seq.nth(var, int_const)`, rhs is constant.
    fn try_extract_nth_constraint(
        terms: &ay_core::term::TermStore,
        lhs: TermId,
        rhs: TermId,
        nth_map: &mut HashMap<TermId, Vec<(usize, TermId)>>,
    ) {
        if let TermData::App(Symbol::Named(name), args) = terms.get(lhs) {
            if name == "seq.nth" && args.len() == 2 {
                let seq_var = args[0];
                let idx_term = args[1];
                if matches!(terms.get(seq_var), TermData::Var(..)) {
                    if let TermData::Const(Constant::Int(idx_val)) = terms.get(idx_term) {
                        if let Some(idx) = idx_val.to_usize() {
                            if matches!(terms.get(rhs), TermData::Const(..)) {
                                nth_map.entry(seq_var).or_default().push((idx, rhs));
                            }
                        }
                    }
                }
            }
        }
    }

    /// Extract a Bool-element nth constraint from a definitely-true assertion.
    ///
    /// The equality simplifier rewrites `(= (seq.nth s i) true) -> (seq.nth s i)`
    /// and `(= (seq.nth s i) false) -> (not (seq.nth s i))` (boolean_eq.rs), so a
    /// `(Seq Bool)` element constraint never survives as an `=` for the Pass-2 nth
    /// extractor to see. This recovers it:
    ///   * `(seq.nth s i)`       => element `i` is `true`
    ///   * `(not (seq.nth s i))` => element `i` is `false`
    ///
    /// `assertion` is a top-level (definitely-true) assertion; `seq_var` must be a
    /// variable and `i` an int constant, mirroring `try_extract_nth_constraint`.
    /// Sound: a top-level `(seq.nth s i)` / `(not (seq.nth s i))` fixes element `i`
    /// of `s` in every model, exactly as an `(= (seq.nth s i) c)` does (#seq-bool-nth).
    fn try_extract_bool_nth_constraint(
        terms: &ay_core::term::TermStore,
        assertion: TermId,
        true_t: TermId,
        false_t: TermId,
        nth_map: &mut HashMap<TermId, Vec<(usize, TermId)>>,
    ) {
        let (nth_term, val) = match terms.get(assertion) {
            TermData::Not(inner) => (*inner, false_t),
            _ => (assertion, true_t),
        };
        if let TermData::App(Symbol::Named(name), args) = terms.get(nth_term) {
            if name == "seq.nth" && args.len() == 2 {
                let seq_var = args[0];
                let idx_term = args[1];
                if matches!(terms.get(seq_var), TermData::Var(..)) {
                    if let TermData::Const(Constant::Int(idx_val)) = terms.get(idx_term) {
                        if let Some(idx) = idx_val.to_usize() {
                            nth_map.entry(seq_var).or_default().push((idx, val));
                        }
                    }
                }
            }
        }
    }

    /// Synthesize a ground sequence term from element constants.
    /// Returns `None` if the variable's sort is not `Seq(T)`.
    fn synthesize_ground_seq(
        &mut self,
        var: TermId,
        elements: &[Option<TermId>],
    ) -> Option<TermId> {
        let seq_sort = self.ctx.terms.sort(var).clone();
        let _elem_sort = seq_sort.seq_element()?;

        if elements.is_empty() {
            return Some(self.mk_seq_empty(&seq_sort));
        }

        // Build right-to-left: seq.++(seq.unit(c_last), seq.empty), then prepend each.
        let empty = self.mk_seq_empty(&seq_sort);

        let mut result = empty;
        for elem_const in elements.iter().rev() {
            let c = (*elem_const)?;
            let unit = self
                .ctx
                .terms
                .mk_app(Symbol::named("seq.unit"), vec![c], seq_sort.clone());
            result = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![unit, result],
                seq_sort.clone(),
            );
        }

        Some(result)
    }

    /// Generate equality axioms for nth-reconstructed ground sequences (#6036).
    ///
    /// For each variable `s` where `(= (seq.len s) n)` and all `n` elements
    /// are defined via `(= (seq.nth s i) ci)`, inject `(= s ground_seq)`.
    /// This makes ALL axiom generators (extract, prefixof, etc.) benefit from
    /// nth ground reconstruction, not just `contains` (#6028).
    pub(super) fn generate_nth_ground_equality_axioms(&mut self) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let mut len_map: HashMap<TermId, usize> = HashMap::default();
        let mut nth_map: HashMap<TermId, Vec<(usize, TermId)>> = HashMap::default();

        // Check for variables already equated to ground seqs (skip those).
        let mut already_ground = HashSet::default();
        for &assertion in &self.ctx.assertions {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name == "=" && args.len() == 2 {
                    let (a, b) = (args[0], args[1]);
                    if matches!(self.ctx.terms.get(a), TermData::Var(..))
                        && self.try_extract_ground_seq(b).is_some()
                    {
                        already_ground.insert(a);
                    } else if matches!(self.ctx.terms.get(b), TermData::Var(..))
                        && self.try_extract_ground_seq(a).is_some()
                    {
                        already_ground.insert(b);
                    }
                }
            }
        }

        // Bool-element nth constraints survive only as `(seq.nth s i)` /
        // `(not (seq.nth s i))` after equality simplification (#seq-bool-nth).
        let true_t = self.ctx.terms.mk_bool(true);
        let false_t = self.ctx.terms.mk_bool(false);

        for &assertion in &self.ctx.assertions {
            Self::try_extract_bool_nth_constraint(
                &self.ctx.terms,
                assertion,
                true_t,
                false_t,
                &mut nth_map,
            );
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name != "=" || args.len() != 2 {
                    continue;
                }
                let (a, b) = (args[0], args[1]);
                Self::try_extract_len_constraint(&self.ctx.terms, a, b, &mut len_map);
                Self::try_extract_len_constraint(&self.ctx.terms, b, a, &mut len_map);
                Self::try_extract_nth_constraint(&self.ctx.terms, a, b, &mut nth_map);
                Self::try_extract_nth_constraint(&self.ctx.terms, b, a, &mut nth_map);
            }
        }

        for (var, len) in &len_map {
            if already_ground.contains(var) || *len > 64 {
                continue;
            }
            if let Some(elements) = nth_map.get(var) {
                let mut index_vals: Vec<Option<TermId>> = vec![None; *len];
                for &(idx, val) in elements {
                    if idx < *len {
                        index_vals[idx] = Some(val);
                    }
                }
                if index_vals.iter().all(Option::is_some) {
                    if let Some(ground_term) = self.synthesize_ground_seq(*var, &index_vals) {
                        axioms.push(self.ctx.terms.mk_eq(*var, ground_term));
                    }
                }
            }
        }

        axioms
    }

    /// Try to extract a ground (fully concrete) sequence as a list of element TermIds.
    ///
    /// Returns `Some(elements)` if the term is a ground sequence composed entirely
    /// of `seq.unit(constant)`, `seq.++`, and `seq.empty`. Each element in the
    /// returned Vec is a `seq.unit(constant)` TermId.
    ///
    /// Returns `None` if the term contains variables, uninterpreted functions,
    /// or other non-ground subterms.
    pub(super) fn try_extract_ground_seq(&self, term: TermId) -> Option<Vec<TermId>> {
        let mut elements = Vec::new();
        let mut stack = vec![term];

        while let Some(t) = stack.pop() {
            match self.ctx.terms.get(t) {
                TermData::App(Symbol::Named(name), args) => match name.as_str() {
                    "seq.unit" if args.len() == 1 => {
                        // Check that the argument is a constant
                        match self.ctx.terms.get(args[0]) {
                            TermData::Const(_) => elements.push(t),
                            _ => return None,
                        }
                    }
                    "seq.++" if args.len() >= 2 => {
                        // Push arguments in reverse order so they come out in order
                        for arg in args.iter().rev() {
                            stack.push(*arg);
                        }
                    }
                    "seq.empty" if args.is_empty() => {
                        // Empty sequence contributes no elements
                    }
                    _ => return None, // Non-ground
                },
                _ => return None, // Variable or non-App
            }
        }

        Some(elements)
    }

    /// Evaluate ground `seq.contains(s, t)` by checking if the element sequence
    /// of `t` appears as a contiguous subsequence of `s`.
    ///
    /// Both `s_elems` and `t_elems` are lists of `seq.unit(constant)` TermIds.
    /// Two elements match if their underlying constants are equal.
    pub(super) fn ground_seq_contains(&self, s_elems: &[TermId], t_elems: &[TermId]) -> bool {
        if t_elems.is_empty() {
            return true;
        }
        if t_elems.len() > s_elems.len() {
            return false;
        }
        // Sliding window search
        'outer: for i in 0..=(s_elems.len() - t_elems.len()) {
            for j in 0..t_elems.len() {
                if !self.ground_seq_elem_eq(s_elems[i + j], t_elems[j]) {
                    continue 'outer;
                }
            }
            return true;
        }
        false
    }

    /// If `elem` is `(seq.unit c)` with a constant `c`, return `Some(c)` (the
    /// interned constant `TermId`); otherwise `None`. Used to compare a ground
    /// needle's elements against a partial seq's pinned element constants by
    /// `TermId` equality (constants are interned, so value equality == id equality).
    pub(super) fn seq_unit_inner_const(&self, elem: TermId) -> Option<TermId> {
        if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(elem) {
            if name == "seq.unit"
                && args.len() == 1
                && matches!(self.ctx.terms.get(args[0]), TermData::Const(_))
            {
                return Some(args[0]);
            }
        }
        None
    }

    /// Three-valued match of a ground `needle` (list of element constants) against
    /// a partially-determined sequence window starting at `start`:
    ///   * `True`    — every covered element is pinned and equals the needle;
    ///   * `False`   — some pinned element disagrees (match impossible in any model);
    ///   * `Unknown` — no disagreement, but some covered element is undetermined.
    /// `partial[i]` is `Some(c)` when index `i` is pinned to constant `c`. The
    /// caller guarantees `start + needle.len() <= partial.len()`.
    ///
    /// SOUND: `False` is returned ONLY on a pinned (definitely-true) mismatch, so
    /// it holds in every model; `True` ONLY when every covered element is pinned
    /// and matches.
    pub(super) fn seq_window_tri(
        partial: &[Option<TermId>],
        needle: &[TermId],
        start: usize,
    ) -> SeqTri {
        let mut any_unknown = false;
        for (j, &nc) in needle.iter().enumerate() {
            match partial.get(start + j) {
                Some(Some(pc)) => {
                    if *pc != nc {
                        return SeqTri::False;
                    }
                }
                Some(None) => any_unknown = true,
                None => return SeqTri::False, // out of range: window cannot fit
            }
        }
        if any_unknown {
            SeqTri::Unknown
        } else {
            SeqTri::True
        }
    }

    /// Check if two `seq.unit(constant)` elements have equal underlying constants.
    pub(super) fn ground_seq_elem_eq(&self, a: TermId, b: TermId) -> bool {
        match (self.ctx.terms.get(a), self.ctx.terms.get(b)) {
            (
                TermData::App(Symbol::Named(na), args_a),
                TermData::App(Symbol::Named(nb), args_b),
            ) if na == "seq.unit" && nb == "seq.unit" && args_a.len() == 1 && args_b.len() == 1 => {
                match (self.ctx.terms.get(args_a[0]), self.ctx.terms.get(args_b[0])) {
                    (TermData::Const(ca), TermData::Const(cb)) => ca == cb,
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// Evaluate ground `seq.indexof(s, t, offset)`: the first position `>= offset`
    /// at which `t` occurs in `s`, or `-1` if not found / offset out of range.
    ///
    /// Matches the SMT-LIB 2.6 / z3 semantics exactly (mirrors the model
    /// evaluator in `eval_seq.rs`):
    ///   * `offset < 0`            => -1
    ///   * `offset > len(s)`       => -1
    ///   * `t = ""` (in range)     => offset (the empty needle is found at the start)
    ///   * otherwise scan `[offset, len(s) - len(t)]`; -1 if no match fits.
    ///
    /// Both `s_elems` and `t_elems` are lists of `seq.unit(constant)` TermIds.
    pub(super) fn ground_seq_indexof(
        &self,
        s_elems: &[TermId],
        t_elems: &[TermId],
        offset: &num_bigint::BigInt,
    ) -> i64 {
        use num_traits::Signed;
        let len_s = s_elems.len() as i64;
        if offset.is_negative() {
            return -1;
        }
        let off = match offset.to_i64() {
            Some(o) if o <= len_s => o,
            _ => return -1, // offset > len(s) (or unrepresentable) => -1
        };
        if t_elems.is_empty() {
            // Empty needle is found at the search start (offset is in [0, len(s)]).
            return off;
        }
        let lt = t_elems.len() as i64;
        if off + lt > len_s {
            return -1; // no room for t at or after offset
        }
        let last = (len_s - lt) as usize;
        for i in (off as usize)..=last {
            if (0..t_elems.len()).all(|j| self.ground_seq_elem_eq(s_elems[i + j], t_elems[j])) {
                return i as i64;
            }
        }
        -1
    }

    /// Evaluate ground `seq.last_indexof(t, s)` by finding the rightmost
    /// position where `s` occurs as a contiguous subsequence of `t`.
    ///
    /// Returns the index of the last occurrence, or -1 if not found.
    /// When `s` is empty, returns `len(t)` per SMT-LIB semantics.
    ///
    /// Both `t_elems` and `s_elems` are lists of `seq.unit(constant)` TermIds.
    pub(super) fn ground_seq_last_indexof(&self, t_elems: &[TermId], s_elems: &[TermId]) -> i64 {
        if s_elems.is_empty() {
            return t_elems.len() as i64;
        }
        if s_elems.len() > t_elems.len() {
            return -1;
        }
        // Reverse sliding window: search from rightmost position
        let mut last_pos: i64 = -1;
        'outer: for i in 0..=(t_elems.len() - s_elems.len()) {
            for j in 0..s_elems.len() {
                if !self.ground_seq_elem_eq(t_elems[i + j], s_elems[j]) {
                    continue 'outer;
                }
            }
            last_pos = i as i64;
        }
        last_pos
    }

    /// Create the canonical empty sequence term for the given sequence sort.
    ///
    /// String axioms use `""` so they share a TermId with parsed string literals.
    /// Other sequence sorts have no string-literal encoding, so use `seq.empty`.
    pub(super) fn mk_seq_empty(&mut self, seq_sort: &ay_core::Sort) -> TermId {
        if *seq_sort == ay_core::Sort::String {
            self.ctx.terms.mk_string(String::new())
        } else {
            self.ctx
                .terms
                .mk_app(Symbol::named("seq.empty"), vec![], seq_sort.clone())
        }
    }

    /// Create a `seq.len(t)` term node.
    pub(super) fn mk_seq_len(&mut self, seq_term: TermId) -> TermId {
        self.ctx
            .terms
            .mk_app(Symbol::named("seq.len"), vec![seq_term], ay_core::Sort::Int)
    }

    /// Build an alias map of seq-sorted variable equalities from assertions.
    ///
    /// For each top-level `(= a b)` over Seq-sorted operands, records the edges
    /// `var → other` for whichever side(s) are variables. Used to resolve a
    /// `seq.nth`/structural argument that is a variable transitively equated to a
    /// concrete sequence expression (e.g. `(= sq2 sq)(= sq (seq.unit 1))`), so
    /// the structural axioms still fire and the wrong value is rejected (#seq-nth-alias).
    pub(super) fn build_seq_alias_map(&self) -> Vec<(TermId, TermId)> {
        let mut aliases: Vec<(TermId, TermId)> = Vec::new();
        // Walk each assertion, descending through a top-level `and` so an alias
        // `(= (seq.unit 3) s1)` nested in `(and (= (seq.unit 3) s1) ...)` is still
        // collected (this path runs before FlattenAnd splits conjunctions, so an
        // un-split `(and ...)` is common — #seq-unit-contains and-wrapped).
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        while let Some(assertion) = stack.pop() {
            if !seen.insert(assertion) {
                continue;
            }
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name == "and" {
                    stack.extend(args.iter().copied());
                    continue;
                }
                if name == "=" && args.len() == 2 {
                    let (l, r) = (args[0], args[1]);
                    // Only seq-sorted equalities can be sequence aliases.
                    if !self.ctx.terms.sort(l).is_seq() {
                        continue;
                    }
                    let l_var = matches!(self.ctx.terms.get(l), TermData::Var(..));
                    let r_var = matches!(self.ctx.terms.get(r), TermData::Var(..));
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

    /// Build a map from integer **variables** to the literal integer constant
    /// they are (transitively) pinned to by top-level equality assertions, e.g.
    /// `(= n0 1)` or a chain `(= n0 m)(= m 1)`. Mirrors `build_seq_alias_map`
    /// but for the Int sort, descending through a top-level `and`.
    ///
    /// Used to let the ground-evaluation path of index-reading seq ops
    /// (`seq.at`/`seq.extract`, `seq.nth`) fire when the index is a symbolic
    /// variable provably equal to a constant. Resolving `i -> 1` and asserting
    /// the structural axiom on the ORIGINAL term `(seq.extract s i 1)` is a
    /// sound congruence consequence of the user's `(= i 1)` assertion
    /// (#seq-at-index-alias).
    pub(super) fn build_int_const_alias_map(&self) -> HashMap<TermId, TermId> {
        // First collect raw var<->var and var->const equality edges.
        let mut const_of: HashMap<TermId, TermId> = HashMap::default();
        let mut var_edges: Vec<(TermId, TermId)> = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(assertion) = stack.pop() {
            if !seen.insert(assertion) {
                continue;
            }
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name == "and" {
                    stack.extend(args.iter().copied());
                    continue;
                }
                if name == "=" && args.len() == 2 {
                    let (l, r) = (args[0], args[1]);
                    let l_var = matches!(self.ctx.terms.get(l), TermData::Var(..));
                    let r_var = matches!(self.ctx.terms.get(r), TermData::Var(..));
                    let l_int_const =
                        matches!(self.ctx.terms.get(l), TermData::Const(Constant::Int(_)));
                    let r_int_const =
                        matches!(self.ctx.terms.get(r), TermData::Const(Constant::Int(_)));
                    if l_var && r_int_const {
                        const_of.entry(l).or_insert(r);
                    } else if r_var && l_int_const {
                        const_of.entry(r).or_insert(l);
                    } else if l_var && r_var && l != r {
                        var_edges.push((l, r));
                        var_edges.push((r, l));
                    }
                }
            }
        }
        // Propagate constants across var<->var edges to a fixpoint so a chain
        // like `(= a b)(= b 1)` resolves `a -> 1`. Edge count is small.
        let mut changed = true;
        while changed {
            changed = false;
            for &(v, w) in &var_edges {
                if let Some(&c) = const_of.get(&w) {
                    if !const_of.contains_key(&v) {
                        const_of.insert(v, c);
                        changed = true;
                    }
                }
            }
        }
        const_of
    }

    /// Resolve an integer term to a literal constant `TermId` using the
    /// var->const alias map. A term that is already an `Int` constant is
    /// returned unchanged; a variable pinned to a constant resolves to that
    /// constant; anything else is returned unchanged (fail-closed). Sound:
    /// only used to fire EXISTING structural axioms keyed on the original
    /// term, never to assert an equality that the alias map didn't justify.
    pub(super) fn resolve_int_const(
        &self,
        t: TermId,
        const_aliases: &HashMap<TermId, TermId>,
    ) -> TermId {
        if matches!(self.ctx.terms.get(t), TermData::Const(Constant::Int(_))) {
            return t;
        }
        if matches!(self.ctx.terms.get(t), TermData::Var(..)) {
            if let Some(&c) = const_aliases.get(&t) {
                return c;
            }
        }
        t
    }

    /// Resolve a seq term through the alias map to its defining sequence
    /// expression. Mirrors the set-theory `resolve_set_alias` discipline
    /// (#seq-nth-alias).
    ///
    /// If `start` is a seq **variable** aliased (possibly transitively) to a
    /// concrete sequence expression, returns that expression. A non-variable
    /// term is returned unchanged. A variable with no resolving alias (or one
    /// whose equivalence class contains only bare variables) yields `start`
    /// itself — callers then see a variable-rooted (uncovered) term and fail
    /// closed. Cycle-safe.
    ///
    /// Performs a breadth-first search over the (symmetric) equality graph so an
    /// arbitrarily long variable→variable chain like `(= a b)(= b c)(= c expr)`
    /// reaches the concrete `expr` regardless of edge ordering or reverse-edge
    /// cycles. If several distinct concrete expressions are reachable the
    /// equality assertions already force them equal, so returning any one of them
    /// is sound.
    pub(super) fn resolve_seq_alias(&self, start: TermId, aliases: &[(TermId, TermId)]) -> TermId {
        // Non-variable terms are already resolved sequence expressions.
        if !matches!(self.ctx.terms.get(start), TermData::Var(..)) {
            return start;
        }
        let mut seen: HashSet<TermId> = HashSet::default();
        seen.insert(start);
        let mut queue: Vec<TermId> = vec![start];
        while let Some(cur) = queue.pop() {
            for (v, target) in aliases {
                if *v != cur {
                    continue;
                }
                if !matches!(self.ctx.terms.get(*target), TermData::Var(..)) {
                    // Reached a concrete sequence expression in `start`'s class.
                    return *target;
                }
                if seen.insert(*target) {
                    queue.push(*target);
                }
            }
        }
        // No concrete expression reachable — stays variable-rooted (fail-closed).
        start
    }
}
