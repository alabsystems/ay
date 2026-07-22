// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
//! AY Map — native finite-map (dictionary) theory solver.
//!
//! Implements a **sound, fail-closed** decision procedure for the
//! quantifier-free theory of finite maps with a value carrier and a domain
//! carrier. A `Map(K, V)` is modelled on **two** parallel arrays:
//!
//! - the **value** carrier `Array(K → V)` where `get(m, k) ≡ select(value, k)`
//!   (gated by the domain), and
//! - the **domain** carrier `dom = Array(K → Bool)` where
//!   `contains_key(m, k) ≡ select(dom, k)`.
//!
//! Map is the *(value carrier + domain carrier)* analogue of the native
//! finite-set theory (`ay-set`, a single `Array(K → Bool)` membership carrier)
//! and the native multiset theory (`ay-multiset`, a single `Array(K → Int)`
//! count carrier). The Map carrier is the **value array** `Array(K → V)`; the
//! domain array travels alongside it as `(map.dom m)`, and the frontend pushes
//! the readers (`map.get`, `map.contains_key`, `map.dom`) through the map
//! constructors so both carriers update in lockstep via `store` read-through.
//!
//! ## Sound rules (this crate + frontend store/const read-through)
//!
//! - `dom(empty) = const-false` (the empty map has empty domain).
//! - `get(insert(m, k, v), k) = v` and `dom(insert(m, k, v))[k] = true`
//!   (decided by `store` read-through over both carriers — ROW2).
//! - `dom(remove(m, k))[k] = false` (the `store … false` read-through).
//! - `contains_key(m, k) = select(dom, k)` and `get(m, k) = select(value, k)`,
//!   decided by the array solver via select/store read-through.
//! - **subset** (`m ⊑ n`, every present key of `m` is a present key of `n`
//!   with the same value) is *refuted* structurally only by **reflexivity**:
//!   `subset(m, m)` is a tautology, so `¬subset(m, m)` is an immediate conflict.
//!   The per-key obligations (`dom(m)[k] ⇒ dom(n)[k] ∧ get(m,k)=get(n,k)`) are
//!   ground and injected by the executor over **present key atoms** only.
//!
//! Saturation ranges **only** over the ground key atoms actually present in the
//! formula. This is what keeps the procedure inside a decidable fragment.
//!
//! The map *equation* axioms (`dom(empty)=const-false`, the insert/remove
//! read-throughs) are decided directly by the array solver. The domain/value
//! relations that need theory reasoning (subset reflexivity) live here; the
//! ground subset↔key obligations are injected by the executor (the same
//! mechanism used for `set.card` and `multiset.count`).
//!
//! ## Fail-closed contract (NON-NEGOTIABLE)
//!
//! A native procedure that returns SAT/UNSAT **outside** its proven-sound
//! fragment is a *critical* soundness bug — worse than `Unknown`. Therefore,
//! when a map obligation falls outside the saturatable ground fragment
//! (`map.values` / `map.entries` / `map.filter_keys` / `map.fold` /
//! `map.comprehension` / `map.map_values` and similar polymorphic / higher-order
//! image operations, whose semantics need a comprehension over the key domain
//! the carriers do not yet provide), this solver returns
//! [`TheoryResult::Unknown`] rather than guessing a verdict.
#![warn(missing_docs)]
#![warn(clippy::all)]

mod theory_impl;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{TermData, TermId, TermStore};
use ay_core::{
    DiscoveredEquality, EqualityPropagationResult, TheoryLit, TheoryPropagation, TheoryResult,
    TheorySolver,
};

/// SMT-LIB operator name for map value lookup (`(map.get m k)`), gated by dom.
pub const OP_GET: &str = "map.get";
/// SMT-LIB operator name for the key-membership predicate
/// (`(map.contains_key m k)`).
pub const OP_CONTAINS_KEY: &str = "map.contains_key";
/// SMT-LIB operator name for the domain projection (`(map.dom m)` :
/// `Array(K → Bool)`).
pub const OP_DOM: &str = "map.dom";
/// SMT-LIB operator name for the empty map (`(as map.empty (Map K V))`).
pub const OP_EMPTY: &str = "map.empty";
/// SMT-LIB operator name for map insertion (`(map.insert m k v)`).
pub const OP_INSERT: &str = "map.insert";
/// SMT-LIB operator name for map removal (`(map.remove m k)`).
pub const OP_REMOVE: &str = "map.remove";
/// SMT-LIB operator name for the submap predicate (`(map.subset m n)`).
pub const OP_SUBSET: &str = "map.subset";

/// Operators that fall **outside** the currently-sound saturatable fragment.
/// Their presence forces a fail-closed `Unknown` (never a guessed verdict).
///
/// These polymorphic / higher-order image operations require reasoning about an
/// image map / comprehension over the key domain the carriers cannot enumerate:
/// `map.values`, `map.entries`, `map.filter_keys`, `map.fold`,
/// `map.comprehension`, `map.map_values`, `map.choose`. Treating them as opaque
/// carriers would make get/dom queries falsely SAT, so they are fail-closed
/// here until the comprehension read-through is landed.
pub const OUT_OF_FRAGMENT_OPS: &[&str] = &[
    "map.values",
    "map.entries",
    "map.filter_keys",
    "map.fold",
    "map.comprehension",
    "map.map_values",
    "map.choose",
];

/// Classification of a map-related application term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MapOp {
    /// `map.get m k` — a value lookup term (sort V).
    Get,
    /// `map.contains_key m k` — key membership (Bool).
    ContainsKey,
    /// `map.dom m` — the domain projection (`Array(K → Bool)`).
    Dom,
    /// `map.empty` — the empty map constructor.
    Empty,
    /// `map.insert m k v`.
    Insert,
    /// `map.remove m k`.
    Remove,
    /// `map.subset m n` — submap predicate (Bool).
    Subset,
}

impl MapOp {
    /// Classify a symbol name into a [`MapOp`], if it is a supported op.
    ///
    /// Out-of-fragment combinators (`map.values`/`map.fold`/…) are intercepted
    /// earlier in [`MapSolver::classify_app`] and never reach here.
    fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            OP_GET => Self::Get,
            OP_CONTAINS_KEY => Self::ContainsKey,
            OP_DOM => Self::Dom,
            OP_EMPTY => Self::Empty,
            OP_INSERT => Self::Insert,
            OP_REMOVE => Self::Remove,
            OP_SUBSET => Self::Subset,
            _ => return None,
        })
    }
}

/// A subset atom: `subset_term ⇔ subset(sub, sup)`.
#[derive(Debug, Clone, Copy)]
struct SubsetAtom {
    /// The `map.subset` application term (the Bool atom).
    atom: TermId,
    /// The candidate sub-map.
    sub: TermId,
    /// The candidate super-map.
    sup: TermId,
}

/// A domain read: `contains_term = contains_key(map, key) = select(dom, key)`.
///
/// `dom` is the domain carrier `(map.dom map)` (an `Array(K → Bool)`) on which
/// the key membership reads; recorded so the executor's subset↔key obligations
/// can range over present key atoms.
#[derive(Debug, Clone, Copy)]
struct DomAtom {
    /// The `contains_key` / domain-select term (the Bool term).
    term: TermId,
    /// The map being queried (the value carrier).
    map: TermId,
    /// The key being queried.
    key: TermId,
}

/// A value read: `get_term = get(map, key) = select(value, key)`.
#[derive(Debug, Clone, Copy)]
struct GetAtom {
    /// The `map.get` / value-select term (the V term).
    term: TermId,
    /// The map being queried (the value carrier).
    map: TermId,
    /// The key being queried.
    key: TermId,
}

/// Native map theory solver (get/dom + subset).
///
/// Fail-closed: returns [`TheoryResult::Unknown`] for any obligation outside
/// the saturatable ground fragment rather than guessing a verdict.
pub struct MapSolver<'a> {
    terms: &'a TermStore,
    /// Current Boolean assignments: atom → value (subset / contains_key atoms).
    assigns: HashMap<TermId, bool>,
    /// Trail for backtracking: (atom, previous_value).
    trail: Vec<(TermId, Option<bool>)>,
    /// Scope markers (trail positions for push/pop).
    scopes: Vec<usize>,
    /// Domain (contains_key) reads registered in the formula.
    dom_atoms: Vec<DomAtom>,
    /// Value (get) reads registered in the formula.
    get_atoms: Vec<GetAtom>,
    /// Subset atoms registered in the formula.
    subset_atoms: Vec<SubsetAtom>,
    /// `map.empty` constructor terms.
    empty_terms: HashSet<TermId>,
    /// Whether any out-of-fragment (polymorphic/higher-order) op was seen.
    out_of_fragment: bool,
    /// Pending Nelson-Oppen equalities (e.g. value/key-bridge equalities).
    pending_equalities: Vec<DiscoveredEquality>,
    /// Shared equalities received from Nelson-Oppen (e.g. EUF → Map).
    shared_equalities: Vec<(TermId, TermId, Vec<TheoryLit>)>,
    /// Trail of shared equality counts for backtracking.
    shared_eq_scopes: Vec<usize>,
    /// Dirty flag: need to re-check.
    dirty: bool,
}

impl<'a> MapSolver<'a> {
    /// Create a new map solver with a reference to the term store.
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            assigns: HashMap::default(),
            trail: Vec::new(),
            scopes: Vec::new(),
            dom_atoms: Vec::new(),
            get_atoms: Vec::new(),
            subset_atoms: Vec::new(),
            empty_terms: HashSet::default(),
            out_of_fragment: false,
            pending_equalities: Vec::new(),
            shared_equalities: Vec::new(),
            shared_eq_scopes: Vec::new(),
            dirty: false,
        }
    }

    /// All registered value-read (`map.get`) term ids.
    pub fn get_terms(&self) -> impl Iterator<Item = TermId> + '_ {
        self.get_atoms.iter().map(|g| g.term)
    }

    /// The map argument of a `map.get` term, if registered.
    #[must_use]
    pub fn get_map(&self, get_term: TermId) -> Option<TermId> {
        self.get_atoms
            .iter()
            .find(|g| g.term == get_term)
            .map(|g| g.map)
    }

    /// The map argument of a `map.contains_key` / domain-read term, if
    /// registered. Exposes the domain carrier read so the executor's subset↔key
    /// witness obligations can recover the map whose key membership this Bool
    /// atom queries.
    #[must_use]
    pub fn dom_map(&self, contains_term: TermId) -> Option<TermId> {
        self.dom_atoms
            .iter()
            .find(|d| d.term == contains_term)
            .map(|d| d.map)
    }

    /// Whether any out-of-fragment map op has been registered. When true, the
    /// solver must fail closed (return `Unknown`) rather than decide.
    #[must_use]
    pub fn is_out_of_fragment(&self) -> bool {
        self.out_of_fragment
    }

    /// Register a term and its map-relevant subterms in the solver's caches.
    ///
    /// Walks the full subterm DAG so that out-of-fragment operators and empty
    /// constructors are detected wherever they appear (including as arguments of
    /// a `map.get` / `map.subset` atom), not only at the top level.
    fn cache_term(&mut self, term: TermId) {
        let mut stack = vec![term];
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.terms.get(t) {
                TermData::App(_, args) => {
                    self.classify_app(t);
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, e) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*e);
                }
                _ => {}
            }
        }
    }

    /// Classify a single application term (no recursion).
    fn classify_app(&mut self, term: TermId) {
        let TermData::App(sym, args) = self.terms.get(term) else {
            return;
        };
        let name = sym.name();
        if OUT_OF_FRAGMENT_OPS.contains(&name) {
            self.out_of_fragment = true;
            return;
        }

        // Value read over the carrier: `(select value k)` where `value` is an
        // `Array(K → V)` (the Map value carrier) and the element sort is not
        // Bool. Frontend elaboration reduces `map.get` to `select`, so this is
        // the real value-read shape the solver sees.
        //
        // Domain read: `(select dom k)` where `dom = (map.dom m)` is an
        // `Array(K → Bool)`. The elaborated `contains_key` reduces to this.
        if name == "select" && args.len() == 2 {
            let array = args[0];
            let key = args[1];
            if self.is_dom_carrier(array) {
                // contains_key(m, k) = select((map.dom m), k).
                if let Some(map) = self.dom_carrier_map(array) {
                    if !self.dom_atoms.iter().any(|d| d.term == term) {
                        self.dom_atoms.push(DomAtom { term, map, key });
                    }
                }
            } else if self.is_value_carrier(array) && !self.get_atoms.iter().any(|g| g.term == term)
            {
                self.get_atoms.push(GetAtom {
                    term,
                    map: array,
                    key,
                });
            }
            return;
        }

        let Some(op) = MapOp::from_name(name) else {
            return;
        };
        match op {
            MapOp::Get if args.len() == 2 => {
                // Retained for callers that assert raw `map.get` terms directly
                // (tests, and any frontend that does not pre-reduce to `select`).
                let map = args[0];
                let key = args[1];
                if !self.get_atoms.iter().any(|g| g.term == term) {
                    self.get_atoms.push(GetAtom { term, map, key });
                }
            }
            MapOp::ContainsKey if args.len() == 2 => {
                let map = args[0];
                let key = args[1];
                if !self.dom_atoms.iter().any(|d| d.term == term) {
                    self.dom_atoms.push(DomAtom { term, map, key });
                }
            }
            MapOp::Empty if args.is_empty() => {
                self.empty_terms.insert(term);
            }
            MapOp::Subset
                if args.len() == 2 && !self.subset_atoms.iter().any(|s| s.atom == term) =>
            {
                self.subset_atoms.push(SubsetAtom {
                    atom: term,
                    sub: args[0],
                    sup: args[1],
                });
            }
            // Constructors (insert/remove) and the opaque `map.dom` projection
            // are decided by the array solver via select/store read-through plus
            // the executor-injected ground axioms; no separate caches needed
            // here. Malformed arities are ignored (the executor's allowlist
            // guards real out-of-fragment ops).
            _ => {}
        }
    }

    /// Whether `term` is a Map value carrier, i.e. an `Array(_ → V)` with a
    /// non-Bool element sort. (A Bool element sort is the domain carrier, not a
    /// value carrier.)
    fn is_value_carrier(&self, term: TermId) -> bool {
        self.terms
            .sort(term)
            .array_element()
            .is_some_and(|e| !e.is_bool())
    }

    /// Whether `term` is a Map domain carrier `(map.dom m)`, i.e. an
    /// `Array(_ → Bool)` produced by the `map.dom` projection.
    fn is_dom_carrier(&self, term: TermId) -> bool {
        matches!(self.terms.get(term), TermData::App(sym, _) if sym.name() == OP_DOM)
    }

    /// The map argument of a domain carrier `(map.dom m)`, if it is one.
    fn dom_carrier_map(&self, term: TermId) -> Option<TermId> {
        match self.terms.get(term) {
            TermData::App(sym, args) if sym.name() == OP_DOM && args.len() == 1 => Some(args[0]),
            _ => None,
        }
    }

    /// All distinct ground keys that appear in any domain or value read (the
    /// witness universe for subset↔key obligations; kept sound by ranging only
    /// over present reads).
    #[must_use]
    pub fn ground_keys(&self) -> Vec<TermId> {
        let mut seen = HashSet::default();
        let mut out = Vec::new();
        for d in &self.dom_atoms {
            if seen.insert(d.key) {
                out.push(d.key);
            }
        }
        for g in &self.get_atoms {
            if seen.insert(g.key) {
                out.push(g.key);
            }
        }
        out
    }

    /// Subset saturation. Only the **reflexivity** rule is decidable purely
    /// structurally here:
    ///
    /// - **Reflexivity is valid.** `subset(m, m)` is a tautology, so asserting
    ///   `¬subset(m, m)` is an immediate conflict.
    ///
    /// Ground-witness refutation of an asserted-true `subset(m, n)` requires the
    /// per-key obligations (`dom(m)[k] ⇒ dom(n)[k] ∧ get(m,k)=get(n,k)`), which
    /// are decided by the array/EUF/LIA combination via the executor-injected
    /// implications, **not** by Boolean assignments visible to this solver. We
    /// never *assert* `subset` true from saturation over an unbounded domain
    /// (that would be unsound: ground witnesses cannot certify a universally
    /// quantified submap). Positive subset that no ground witness settles is
    /// left `Unknown` by the combined solver rather than guessed.
    fn check_subset_saturation(&self) -> Option<Vec<TheoryLit>> {
        // Rule: reflexivity. ¬subset(m, m) is unsatisfiable.
        for s in &self.subset_atoms {
            if s.sub == s.sup && self.assigns.get(&s.atom) == Some(&false) {
                return Some(vec![TheoryLit::new(s.atom, false)]);
            }
        }
        None
    }

    /// Number of registered domain (contains_key) reads (diagnostics / tests).
    #[must_use]
    pub fn dom_atom_count(&self) -> usize {
        self.dom_atoms.len()
    }

    /// Number of registered value (get) reads (diagnostics / tests).
    #[must_use]
    pub fn get_atom_count(&self) -> usize {
        self.get_atoms.len()
    }

    /// Number of registered subset atoms (diagnostics / tests).
    #[must_use]
    pub fn subset_atom_count(&self) -> usize {
        self.subset_atoms.len()
    }
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
