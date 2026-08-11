// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
//! AY Set — native finite-set theory solver.
//!
//! Implements a **sound, fail-closed** decision procedure for the
//! quantifier-free theory of finite sets with cardinality, modelled on the
//! membership carrier `Set(T) = Array(T → Bool)` where
//! `member(s, e) ≡ select(s, e)` (ROW2 read-through). The array solver decides
//! membership/equality; this crate adds the **cardinality** and **subset**
//! reasoning that the array solver cannot express.
//!
//! ## Sound rules (this crate)
//!
//! - `card(empty) = 0`
//! - `card(s) ≥ 0` for **every** card term (the Nelson-Oppen card↔LIA bridge
//!   asserts non-negativity for every card symbol — a *sound* combination).
//! - `card(insert(s, e)) = card(s) + ite(member(s, e), 0, 1)`
//! - `card(remove(s, e)) = card(s) − ite(member(s, e), 1, 0)`
//! - inclusion–exclusion: `card(union(s,t)) = card(s) + card(t) − card(inter(s,t))`,
//!   `card(diff(s,t)) = card(s) − card(inter(s,t))`
//! - **subset** by ground-witness saturation: `subset(s, t)` is *refuted* exactly
//!   when there is a present ground element `e` with `member(s, e) ∧ ¬member(t, e)`;
//!   `subset(s, s)` is reflexively true.
//!
//! Saturation ranges **only** over the ground member literals actually present in
//! the formula. This is what keeps the procedure inside a decidable fragment.
//!
//! ## Fail-closed contract (NON-NEGOTIABLE)
//!
//! A native procedure that returns SAT/UNSAT **outside** its proven-sound
//! fragment is a *critical* soundness bug — worse than `Unknown`. Therefore, when
//! a set obligation falls outside the saturatable ground fragment (unbounded
//! element domain with a positive-subset goal that no ground witness can settle,
//! polymorphic/higher-order image operations such as `set.map` / `set.filter`),
//! this solver returns [`TheoryResult::Unknown`] rather than guessing a verdict.
//!
//! The card *equation* axioms (`card(empty)=0`, the insert/remove/union/inter/diff
//! rules) are ground and are injected as ordinary assertions by the executor
//! before solving (the same mechanism used for `seq.len`). This crate enforces the
//! parts that require theory reasoning: subset saturation, structural cardinality
//! conflicts over present ground witnesses, and the card↔LIA non-negativity bridge.
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

/// SMT-LIB operator name for set membership (`(set.member e s)`).
pub const OP_MEMBER: &str = "set.member";
/// SMT-LIB operator name for set cardinality (`(set.card s)`).
pub const OP_CARD: &str = "set.card";
/// SMT-LIB operator name for the empty set (`(as set.empty (Set T))`).
pub const OP_EMPTY: &str = "set.empty";
/// SMT-LIB operator name for a singleton set (`(set.singleton e)`).
pub const OP_SINGLETON: &str = "set.singleton";
/// SMT-LIB operator name for set insertion (`(set.insert e s)`).
pub const OP_INSERT: &str = "set.insert";
/// SMT-LIB operator name for set removal (`(set.remove e s)`).
pub const OP_REMOVE: &str = "set.remove";
/// SMT-LIB operator name for the subset predicate (`(set.subset s t)`).
pub const OP_SUBSET: &str = "set.subset";

/// Operators that fall **outside** the currently-sound saturatable fragment.
/// Their presence forces a fail-closed `Unknown` (never a guessed verdict).
///
/// Two groups, both unsound to decide today and therefore fail-closed:
///
/// 1. Higher-order / polymorphic image: `set.map`, `set.filter`, `set.fold`,
///    `set.comprehension`, `set.choose`. These require reasoning about an
///    image set ay cannot enumerate.
/// 2. Domain-pointwise binary/unary combinators whose membership semantics
///    (`member(union(s,t),e) = member(s,e) ∨ member(t,e)`, etc.) need a
///    comprehension/lambda over the element domain that the array carrier does
///    not yet provide. Treating `union`/`inter`/`minus`/`complement`/`universe`
///    as opaque arrays would make membership queries falsely SAT, so they are
///    fail-closed here until the pointwise read-through is landed. The
///    cardinality inclusion–exclusion identities are sound in isolation but are
///    only safe to assert once membership is sound, so they are deferred with
///    these ops.
pub const OUT_OF_FRAGMENT_OPS: &[&str] = &[
    "set.map",
    "set.filter",
    "set.range",
    "set.fold",
    "set.comprehension",
    "set.choose",
    "set.universe",
    "set.complement",
    "set.union",
    "set.inter",
    "set.intersect",
    "set.minus",
    "set.difference",
];

/// Classification of a set-related application term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SetOp {
    /// `set.member e s` — a membership atom (Bool).
    Member,
    /// `set.card s` — a cardinality term (Int).
    Card,
    /// `set.empty` — the empty set constructor.
    Empty,
    /// `set.singleton e` — a singleton.
    Singleton,
    /// `set.insert e s`.
    Insert,
    /// `set.remove e s`.
    Remove,
    /// `set.subset s t` — subset predicate (Bool).
    Subset,
}

impl SetOp {
    /// Classify a symbol name into a [`SetOp`], if it is a supported set op.
    ///
    /// Out-of-fragment combinators (`set.union`/`set.inter`/`set.minus`/…) are
    /// intercepted earlier in [`SetSolver::classify_app`] and never reach here.
    fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            OP_MEMBER => Self::Member,
            OP_CARD => Self::Card,
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
    /// The `set.subset` application term (the Bool atom).
    atom: TermId,
    /// The candidate subset.
    sub: TermId,
    /// The candidate superset.
    sup: TermId,
}

/// A membership atom: `member_term ⇔ member(set, elem)` (i.e. `select(set, elem)`).
#[derive(Debug, Clone, Copy)]
struct MemberAtom {
    /// The membership application term (the Bool atom).
    atom: TermId,
    /// The set being queried.
    set: TermId,
    /// The element being queried.
    elem: TermId,
}

/// Native finite-set theory solver (card + subset).
///
/// Fail-closed: returns [`TheoryResult::Unknown`] for any obligation outside the
/// saturatable ground fragment rather than guessing a verdict.
pub struct SetSolver<'a> {
    terms: &'a TermStore,
    /// Current Boolean assignments: atom → value.
    assigns: HashMap<TermId, bool>,
    /// Trail for backtracking: (atom, previous_value).
    trail: Vec<(TermId, Option<bool>)>,
    /// Scope markers (trail positions for push/pop).
    scopes: Vec<usize>,
    /// Membership atoms registered in the formula.
    member_atoms: Vec<MemberAtom>,
    /// Subset atoms registered in the formula.
    subset_atoms: Vec<SubsetAtom>,
    /// `set.card` terms: card_term → set_arg.
    card_terms: HashMap<TermId, TermId>,
    /// `set.empty` constructor terms.
    empty_terms: HashSet<TermId>,
    /// Whether any out-of-fragment (polymorphic/higher-order) op was seen.
    out_of_fragment: bool,
    /// Pending Nelson-Oppen equalities (e.g. card-bridge equalities).
    pending_equalities: Vec<DiscoveredEquality>,
    /// Shared equalities received from Nelson-Oppen (e.g. EUF → Set).
    shared_equalities: Vec<(TermId, TermId, Vec<TheoryLit>)>,
    /// Trail of shared equality counts for backtracking.
    shared_eq_scopes: Vec<usize>,
    /// Dirty flag: need to re-check.
    dirty: bool,
}

impl<'a> SetSolver<'a> {
    /// Create a new set solver with a reference to the term store.
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            assigns: HashMap::default(),
            trail: Vec::new(),
            scopes: Vec::new(),
            member_atoms: Vec::new(),
            subset_atoms: Vec::new(),
            card_terms: HashMap::default(),
            empty_terms: HashSet::default(),
            out_of_fragment: false,
            pending_equalities: Vec::new(),
            shared_equalities: Vec::new(),
            shared_eq_scopes: Vec::new(),
            dirty: false,
        }
    }

    /// All registered `set.card` term ids.
    pub fn card_terms(&self) -> impl Iterator<Item = TermId> + '_ {
        self.card_terms.keys().copied()
    }

    /// The set argument of a `set.card` term, if registered.
    #[must_use]
    pub fn card_set(&self, card_term: TermId) -> Option<TermId> {
        self.card_terms.get(&card_term).copied()
    }

    /// Whether any out-of-fragment set op has been registered. When true, the
    /// solver must fail closed (return `Unknown`) rather than decide.
    #[must_use]
    pub fn is_out_of_fragment(&self) -> bool {
        self.out_of_fragment
    }

    /// Register a term and its set-relevant subterms in the solver's caches.
    ///
    /// Walks the full subterm DAG so that out-of-fragment operators and empty-set
    /// constructors are detected wherever they appear (including as arguments of
    /// a `set.member` / `set.subset` atom), not only at the top level.
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

        // Membership atom over the carrier: `(select set elem)` where `set` is
        // an `Array(_ -> Bool)` (a Set). Frontend elaboration reduces
        // `set.member` to `select`, so this is the real membership shape the
        // solver sees. A Bool-valued select whose array operand is a Set carrier
        // is exactly `elem ∈ set`.
        if name == "select" && args.len() == 2 {
            let set = args[0];
            let elem = args[1];
            if self.is_set_carrier(set) && !self.member_atoms.iter().any(|m| m.atom == term) {
                self.member_atoms.push(MemberAtom {
                    atom: term,
                    set,
                    elem,
                });
            }
            return;
        }

        let Some(op) = SetOp::from_name(name) else {
            return;
        };
        match op {
            SetOp::Member if args.len() == 2 => {
                // SMT-LIB convention: (set.member element set). Retained for
                // callers that assert raw `set.member` atoms directly (tests,
                // and any frontend that does not pre-reduce to `select`).
                let elem = args[0];
                let set = args[1];
                if !self.member_atoms.iter().any(|m| m.atom == term) {
                    self.member_atoms.push(MemberAtom {
                        atom: term,
                        set,
                        elem,
                    });
                }
            }
            SetOp::Card if args.len() == 1 => {
                self.card_terms.insert(term, args[0]);
            }
            SetOp::Empty if args.is_empty() => {
                self.empty_terms.insert(term);
            }
            SetOp::Subset
                if args.len() == 2 && !self.subset_atoms.iter().any(|s| s.atom == term) =>
            {
                self.subset_atoms.push(SubsetAtom {
                    atom: term,
                    sub: args[0],
                    sup: args[1],
                });
            }
            // Constructors (singleton/insert/remove/union/inter/minus) are
            // membership-equivalent under the Array(T→Bool) carrier; their
            // semantics are decided by the array solver via select read-through
            // plus the executor-injected ground card/membership axioms. We do
            // not need separate caches for them here, but malformed arities are
            // ignored (the executor's allowlist guards real out-of-fragment ops).
            _ => {}
        }
    }

    /// Whether `term` is a Set carrier, i.e. an `Array(_ -> Bool)`.
    fn is_set_carrier(&self, term: TermId) -> bool {
        self.terms
            .sort(term)
            .array_element()
            .is_some_and(ay_core::Sort::is_bool)
    }

    /// Value of a membership atom for `(set, elem)` under the current
    /// assignment, if a corresponding ground member atom is asserted.
    fn member_value(&self, set: TermId, elem: TermId) -> Option<bool> {
        for m in &self.member_atoms {
            if m.set == set && m.elem == elem {
                if let Some(&v) = self.assigns.get(&m.atom) {
                    return Some(v);
                }
            }
        }
        None
    }

    /// The membership atom term for `(set, elem)`, if registered.
    fn member_atom(&self, set: TermId, elem: TermId) -> Option<TermId> {
        self.member_atoms
            .iter()
            .find(|m| m.set == set && m.elem == elem)
            .map(|m| m.atom)
    }

    /// All distinct ground elements that appear in any membership atom.
    fn ground_elements(&self) -> Vec<TermId> {
        let mut seen = HashSet::default();
        let mut out = Vec::new();
        for m in &self.member_atoms {
            if seen.insert(m.elem) {
                out.push(m.elem);
            }
        }
        out
    }

    /// Subset saturation with two sound rules:
    ///
    /// 1. **Reflexivity is valid.** `subset(s, s)` is a tautology, so asserting
    ///    `¬subset(s, s)` is an immediate conflict.
    /// 2. **Ground-witness refutation.** For an asserted-true `subset(s, t)` and
    ///    any present ground element `e`, if `member(s, e)` is true and
    ///    `member(t, e)` is false the formula is unsatisfiable.
    ///
    /// We never *assert* `subset` true from saturation over an unbounded domain
    /// (that would be unsound: ground witnesses cannot certify a universally
    /// quantified subset). Positive subset that no ground witness settles is
    /// left `Unknown` by the combined solver rather than guessed.
    fn check_subset_saturation(&self) -> Option<Vec<TheoryLit>> {
        // Rule 1: reflexivity. ¬subset(s, s) is unsatisfiable.
        for s in &self.subset_atoms {
            if s.sub == s.sup && self.assigns.get(&s.atom) == Some(&false) {
                return Some(vec![TheoryLit::new(s.atom, false)]);
            }
        }

        // Rule 2: ground-witness refutation of asserted-true subset.
        for s in &self.subset_atoms {
            // Only saturate asserted-true subset atoms.
            if self.assigns.get(&s.atom) != Some(&true) {
                continue;
            }
            // Reflexivity: subset(s, s) is trivially satisfiable.
            if s.sub == s.sup {
                continue;
            }
            // Membership in a registered empty superset is *definitionally*
            // false for every element, with no member atom required. Without
            // this, `subset(A, empty) ∧ member(A, e)` was missed because the
            // witness rule below only fired on a registered `member(sup, e)`
            // atom valued false — which never exists for the empty set — so the
            // implicit `e ∉ empty` fact never connected. See the `subset` →
            // `setminus(A,B)=empty` rewrite in z3's array_rewriter.
            let sup_is_empty = self.set_is_empty(s.sup);
            for &elem in &self.ground_elements() {
                let in_sub = self.member_value(s.sub, elem);
                let in_sup = if sup_is_empty {
                    Some(false)
                } else {
                    self.member_value(s.sup, elem)
                };
                if in_sub == Some(true) && in_sup == Some(false) {
                    // Witness e: e ∈ sub, e ∉ sup, yet subset(sub, sup) asserted.
                    let mut reason = vec![TheoryLit::new(s.atom, true)];
                    if let Some(a) = self.member_atom(s.sub, elem) {
                        reason.push(TheoryLit::new(a, true));
                    }
                    if let Some(a) = self.member_atom(s.sup, elem) {
                        reason.push(TheoryLit::new(a, false));
                    }
                    return Some(reason);
                }
            }
        }
        None
    }

    /// Card structural conflict over present ground witnesses: a `set.card`
    /// term whose set is a *registered empty* set must be `0`. If a distinct
    /// ground element is asserted a member of an empty set, that is an
    /// immediate membership contradiction (e ∈ empty).
    ///
    /// The richer card equations (insert/union/…) are injected as ground
    /// assertions by the executor and decided by LIA; here we only catch the
    /// purely structural empty-membership contradiction that needs no LIA.
    fn check_empty_membership(&self) -> Option<Vec<TheoryLit>> {
        for m in &self.member_atoms {
            if self.set_is_empty(m.set) && self.assigns.get(&m.atom) == Some(&true) {
                return Some(vec![TheoryLit::new(m.atom, true)]);
            }
        }
        None
    }

    /// True when `term` denotes the empty set — either a registered `set.empty`
    /// op, or its elaborated form, the constant-`false` array
    /// `(as const (Array T Bool)) false`. The frontend lowers
    /// `(as set.empty (Set T))` to the latter, which is NOT a `set.empty` op and
    /// so was missing from `empty_terms`; without recognizing it, the
    /// `subset(A, empty) ∧ member(x, A)` contradiction was never detected
    /// (wrong `sat`). (#set-empty-const-array)
    fn set_is_empty(&self, term: TermId) -> bool {
        self.empty_terms.contains(&term)
            || self.terms.get_const_array(term) == Some(self.terms.false_term())
    }

    /// Number of registered membership atoms (diagnostics / tests).
    #[must_use]
    pub fn member_atom_count(&self) -> usize {
        self.member_atoms.len()
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
