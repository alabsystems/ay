// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
//! AY Multiset — native multiset (bag) theory solver.
//!
//! Implements a **sound, fail-closed** decision procedure for the
//! quantifier-free theory of multisets with element counts, modelled on the
//! count carrier `Multiset(T) = Array(T → Int)` where
//! `count(m, e) ≡ select(m, e)` (ROW2 read-through). The array solver decides
//! the count carrier and multiset equality (extensionality); LIA decides the
//! integer arithmetic of `multiset.count` terms; this crate adds the
//! **non-negativity** and **subset** reasoning that the array/LIA solvers
//! cannot express on their own.
//!
//! Multiset is the *count analogue* of the native finite-set theory
//! (`ay-set`): where a set carries `Array(T → Bool)` membership, a multiset
//! carries `Array(T → Int)` element multiplicities.
//!
//! ## Sound rules (this crate + executor-injected ground axioms)
//!
//! - `count(empty) = 0` (the empty multiset is the constant-0 array).
//! - `count(m, e) ≥ 0` for **every** count term (the Nelson-Oppen count↔LIA
//!   bridge asserts non-negativity for every count atom — a *sound*
//!   combination; multiplicities are never negative).
//! - `count(insert(m, e), e) = count(m, e) + 1`.
//! - `count(remove(m, e), e) = max(count(m, e) − 1, 0)` (clamped at 0).
//! - **subset** by ground-witness saturation: `subset(m, n)` is *refuted*
//!   exactly when there is a present ground element `e` whose count atoms
//!   witness `count(m, e) > count(n, e)`; `subset(m, m)` is reflexively true.
//!
//! Saturation ranges **only** over the ground count atoms actually present in
//! the formula. This is what keeps the procedure inside a decidable fragment.
//!
//! The count *equation* axioms (`count(empty)=0`, the insert/remove rules) and
//! the per-count non-negativity bound are ground and are injected as ordinary
//! assertions by the executor before solving (the same mechanism used for
//! `seq.len` and `set.card`). The count comparisons themselves are Int-valued
//! and decided by LIA; this crate enforces the structural empty-count conflict
//! and the subset ground-witness refutation that need theory reasoning.
//!
//! ## Fail-closed contract (NON-NEGOTIABLE)
//!
//! A native procedure that returns SAT/UNSAT **outside** its proven-sound
//! fragment is a *critical* soundness bug — worse than `Unknown`. Therefore,
//! when a multiset obligation falls outside the saturatable ground fragment
//! (polymorphic / higher-order image operations such as `multiset.map` /
//! `multiset.filter` / `multiset.fold`, comprehension/sum/union-as-max
//! combinators whose pointwise count semantics need a comprehension over the
//! element domain the carrier does not yet provide), this solver returns
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

/// SMT-LIB operator name for multiset element count (`(multiset.count e m)`).
pub const OP_COUNT: &str = "multiset.count";
/// SMT-LIB operator name for the empty multiset (`(as multiset.empty (Multiset T))`).
pub const OP_EMPTY: &str = "multiset.empty";
/// SMT-LIB operator name for a singleton multiset (`(multiset.singleton e)`).
pub const OP_SINGLETON: &str = "multiset.singleton";
/// SMT-LIB operator name for multiset insertion (`(multiset.insert e m)`).
pub const OP_INSERT: &str = "multiset.insert";
/// SMT-LIB operator name for multiset removal (`(multiset.remove e m)`).
pub const OP_REMOVE: &str = "multiset.remove";
/// SMT-LIB operator name for the subset predicate (`(multiset.subset m n)`).
pub const OP_SUBSET: &str = "multiset.subset";

/// Operators that fall **outside** the currently-sound saturatable fragment.
/// Their presence forces a fail-closed `Unknown` (never a guessed verdict).
///
/// Two groups, both unsound to decide today and therefore fail-closed:
///
/// 1. Higher-order / polymorphic image: `multiset.map`, `multiset.filter`,
///    `multiset.fold`, `multiset.comprehension`, `multiset.sum`,
///    `multiset.choose`. These require reasoning about an image multiset ay
///    cannot enumerate.
/// 2. Domain-pointwise binary/unary combinators whose count semantics
///    (`count(union(m,n),e) = max(count(m,e),count(n,e))`,
///    `count(inter(m,n),e) = min(count(m,e),count(n,e))`, etc.) need a
///    comprehension/lambda over the element domain that the count carrier does
///    not yet provide. Treating `union`/`inter`/`diff` as opaque arrays would
///    make count queries falsely SAT, so they are fail-closed here until the
///    pointwise read-through is landed.
pub const OUT_OF_FRAGMENT_OPS: &[&str] = &[
    "multiset.map",
    "multiset.filter",
    "multiset.fold",
    "multiset.comprehension",
    "multiset.sum",
    "multiset.choose",
    "multiset.union",
    "multiset.inter",
    "multiset.diff",
];

/// Classification of a multiset-related application term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MultisetOp {
    /// `multiset.count e m` — a count term (Int).
    Count,
    /// `multiset.empty` — the empty multiset constructor.
    Empty,
    /// `multiset.singleton e` — a singleton.
    Singleton,
    /// `multiset.insert e m`.
    Insert,
    /// `multiset.remove e m`.
    Remove,
    /// `multiset.subset m n` — subset predicate (Bool).
    Subset,
}

impl MultisetOp {
    /// Classify a symbol name into a [`MultisetOp`], if it is a supported op.
    ///
    /// Out-of-fragment combinators (`multiset.union`/`multiset.inter`/…) are
    /// intercepted earlier in [`MultisetSolver::classify_app`] and never reach
    /// here.
    fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            OP_COUNT => Self::Count,
            OP_EMPTY => Self::Empty,
            OP_SINGLETON => Self::Singleton,
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
    /// The `multiset.subset` application term (the Bool atom).
    atom: TermId,
    /// The candidate sub-multiset.
    sub: TermId,
    /// The candidate super-multiset.
    sup: TermId,
}

/// A count term: `count_term = count(multiset, elem) = select(multiset, elem)`.
#[derive(Debug, Clone, Copy)]
struct CountAtom {
    /// The count application term (the Int term).
    term: TermId,
    /// The multiset being queried.
    multiset: TermId,
    /// The element being queried.
    elem: TermId,
}

/// Native multiset theory solver (count + subset).
///
/// Fail-closed: returns [`TheoryResult::Unknown`] for any obligation outside
/// the saturatable ground fragment rather than guessing a verdict.
pub struct MultisetSolver<'a> {
    terms: &'a TermStore,
    /// Current Boolean assignments: atom → value (subset atoms only).
    assigns: HashMap<TermId, bool>,
    /// Trail for backtracking: (atom, previous_value).
    trail: Vec<(TermId, Option<bool>)>,
    /// Scope markers (trail positions for push/pop).
    scopes: Vec<usize>,
    /// Count atoms registered in the formula.
    count_atoms: Vec<CountAtom>,
    /// Subset atoms registered in the formula.
    subset_atoms: Vec<SubsetAtom>,
    /// `multiset.empty` constructor terms.
    empty_terms: HashSet<TermId>,
    /// Whether any out-of-fragment (polymorphic/higher-order) op was seen.
    out_of_fragment: bool,
    /// Pending Nelson-Oppen equalities (e.g. count-bridge equalities).
    pending_equalities: Vec<DiscoveredEquality>,
    /// Shared equalities received from Nelson-Oppen (e.g. EUF → Multiset).
    shared_equalities: Vec<(TermId, TermId, Vec<TheoryLit>)>,
    /// Trail of shared equality counts for backtracking.
    shared_eq_scopes: Vec<usize>,
    /// Dirty flag: need to re-check.
    dirty: bool,
}

impl<'a> MultisetSolver<'a> {
    /// Create a new multiset solver with a reference to the term store.
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            assigns: HashMap::default(),
            trail: Vec::new(),
            scopes: Vec::new(),
            count_atoms: Vec::new(),
            subset_atoms: Vec::new(),
            empty_terms: HashSet::default(),
            out_of_fragment: false,
            pending_equalities: Vec::new(),
            shared_equalities: Vec::new(),
            shared_eq_scopes: Vec::new(),
            dirty: false,
        }
    }

    /// All registered `multiset.count` term ids.
    pub fn count_terms(&self) -> impl Iterator<Item = TermId> + '_ {
        self.count_atoms.iter().map(|c| c.term)
    }

    /// The multiset argument of a `multiset.count` term, if registered.
    #[must_use]
    pub fn count_multiset(&self, count_term: TermId) -> Option<TermId> {
        self.count_atoms
            .iter()
            .find(|c| c.term == count_term)
            .map(|c| c.multiset)
    }

    /// Whether any out-of-fragment multiset op has been registered. When true,
    /// the solver must fail closed (return `Unknown`) rather than decide.
    #[must_use]
    pub fn is_out_of_fragment(&self) -> bool {
        self.out_of_fragment
    }

    /// Register a term and its multiset-relevant subterms in the solver's caches.
    ///
    /// Walks the full subterm DAG so that out-of-fragment operators and empty
    /// constructors are detected wherever they appear (including as arguments
    /// of a `multiset.count` / `multiset.subset` atom), not only at the top
    /// level.
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

        // Count atom over the carrier: `(select multiset elem)` where `multiset`
        // is an `Array(_ -> Int)` (a Multiset). Frontend elaboration reduces
        // `multiset.count` to `select`, so this is the real count shape the
        // solver sees. An Int-valued select whose array operand is a Multiset
        // carrier is exactly `count(multiset, elem)`.
        if name == "select" && args.len() == 2 {
            let multiset = args[0];
            let elem = args[1];
            if self.is_multiset_carrier(multiset)
                && !self.count_atoms.iter().any(|c| c.term == term)
            {
                self.count_atoms.push(CountAtom {
                    term,
                    multiset,
                    elem,
                });
            }
            return;
        }

        let Some(op) = MultisetOp::from_name(name) else {
            return;
        };
        match op {
            MultisetOp::Count if args.len() == 2 => {
                // SMT-LIB convention: (multiset.count element multiset). Retained
                // for callers that assert raw `multiset.count` terms directly
                // (tests, and any frontend that does not pre-reduce to `select`).
                let elem = args[0];
                let multiset = args[1];
                if !self.count_atoms.iter().any(|c| c.term == term) {
                    self.count_atoms.push(CountAtom {
                        term,
                        multiset,
                        elem,
                    });
                }
            }
            MultisetOp::Empty if args.is_empty() => {
                self.empty_terms.insert(term);
            }
            MultisetOp::Subset
                if args.len() == 2 && !self.subset_atoms.iter().any(|s| s.atom == term) =>
            {
                self.subset_atoms.push(SubsetAtom {
                    atom: term,
                    sub: args[0],
                    sup: args[1],
                });
            }
            // Constructors (singleton/insert/remove) are count-equivalent under
            // the Array(T→Int) carrier; their semantics are decided by the array
            // solver via select read-through plus the executor-injected ground
            // count axioms. We do not need separate caches for them here;
            // malformed arities are ignored (the executor's allowlist guards
            // real out-of-fragment ops).
            _ => {}
        }
    }

    /// Whether `term` is a Multiset carrier, i.e. an `Array(_ -> Int)`.
    fn is_multiset_carrier(&self, term: TermId) -> bool {
        self.terms
            .sort(term)
            .array_element()
            .is_some_and(ay_core::Sort::is_int)
    }

    /// The count term for `(multiset, elem)`, if registered. Exposes the count
    /// carrier read so the executor's subset↔count witness obligations and any
    /// future ground saturation can recover the Int count atom for a witness.
    #[must_use]
    pub fn count_term(&self, multiset: TermId, elem: TermId) -> Option<TermId> {
        self.count_atoms
            .iter()
            .find(|c| c.multiset == multiset && c.elem == elem)
            .map(|c| c.term)
    }

    /// All distinct ground elements that appear in any count atom (the witness
    /// universe for subset↔count obligations; kept sound by ranging only over
    /// present count reads).
    #[must_use]
    pub fn ground_elements(&self) -> Vec<TermId> {
        let mut seen = HashSet::default();
        let mut out = Vec::new();
        for c in &self.count_atoms {
            if seen.insert(c.elem) {
                out.push(c.elem);
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
    /// Ground-witness refutation of an asserted-true `subset(m, n)` requires a
    /// comparison `count(m, e) > count(n, e)`, which is Int-valued and decided
    /// by LIA via the executor-injected subset↔count obligations, **not** by
    /// Boolean assignments visible to this solver. We never *assert* `subset`
    /// true from saturation over an unbounded domain (that would be unsound:
    /// ground witnesses cannot certify a universally quantified subset).
    /// Positive subset that no ground witness settles is left to LIA / left
    /// `Unknown` by the combined solver rather than guessed.
    fn check_subset_saturation(&self) -> Option<Vec<TheoryLit>> {
        // Rule: reflexivity. ¬subset(m, m) is unsatisfiable.
        for s in &self.subset_atoms {
            if s.sub == s.sup && self.assigns.get(&s.atom) == Some(&false) {
                return Some(vec![TheoryLit::new(s.atom, false)]);
            }
        }
        None
    }

    /// Number of registered count atoms (diagnostics / tests).
    #[must_use]
    pub fn count_atom_count(&self) -> usize {
        self.count_atoms.len()
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
