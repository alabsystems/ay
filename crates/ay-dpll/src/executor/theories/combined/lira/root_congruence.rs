// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The AUFLIRA assertion window written over the representatives of its
//! root-level congruence classes.
//!
//! The lazy split loop hands the theory a complete Boolean assignment and
//! gets one small lemma back per round. Two atoms about the same quantity
//! written with two terms the window already equates, such as
//! `(< (unbox (box 4)) hi)` next to `(< 4 hi)` under the asserted
//! `(= 4 (unbox (box 4)))`, are two free Boolean variables to the SAT solver,
//! and every disagreement between them costs a round. This pass rewrites the
//! window so that such a pair is one atom.
//!
//! One round of the pass:
//!
//! 1. Split the window into its top-level conjuncts.
//! 2. The conjuncts that are equalities between non-Boolean terms are the
//!    *root equalities*. Close them under congruence over every ground term
//!    of the window.
//! 3. Pick one representative term per class (a value, else an arithmetic
//!    term, else the smallest term) and replace every term by the
//!    representative of its class, bottom up, through the folding
//!    constructors.
//! 4. A conjunct that is a literal over a theory atom fixes that atom:
//!    wherever the atom stands as a term, below a connective or as the
//!    Boolean argument of a function, step 3 writes its truth value. The
//!    literal itself stays in the window, its atom written over the
//!    representatives of the atom's arguments.
//! 5. Restate the root equalities: for every term `t` of a joined class, the
//!    equality between `t` written over the representatives of its arguments
//!    and the representative of the class. These *defining equalities* and
//!    the literals generate the same congruence as the root equalities and
//!    the literals as written (by induction on the size of a term, every
//!    term equals what step 3 writes for it under them), so the rewritten
//!    window has exactly the models of the original one. They also keep
//!    each joined term in the window once, where the root equalities as
//!    written would keep a second copy of every term built over a
//!    non-representative.
//!
//! Step 4 can turn a guarded equality into a root equality, and a value that
//! reaches an arithmetic atom can fold it, so the rounds repeat until the
//! window stops changing or [`MAX_ROUNDS`] is reached. Every round is an
//! equivalence, so stopping early costs sharing, never a model.
//!
//! Quantified and `let` terms are leaves: nothing inside them is read or
//! rewritten.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use crate::preprocess::PropagateValues;

mod closure;
use closure::Closure;

/// Rounds of the pass on one window. A round that changes nothing ends the
/// loop, so the bound only matters for windows where each round opens new
/// root equalities (a chain of values, each fixed through the one before).
const MAX_ROUNDS: usize = 32;

/// Stack red zone and segment for the recursive rebuild of deep terms.
const STACK_RED_ZONE: usize = 32 * 1024;
const STACK_SIZE: usize = 1024 * 1024;

/// The result of [`canonicalize_window`].
pub(super) struct CanonicalWindow {
    /// The conjuncts of the rewritten window.
    pub(super) assertions: Vec<TermId>,
    /// Rounds that changed the window.
    pub(super) rounds: usize,
    /// Root equalities that joined two classes, summed over the rounds.
    pub(super) merges: usize,
}

/// Rewrite `assertions` to an equivalent window in which every ground term
/// is the representative of its root-level congruence class.
pub(super) fn canonicalize_window(
    terms: &mut TermStore,
    assertions: Vec<TermId>,
) -> CanonicalWindow {
    let mut result = CanonicalWindow {
        assertions: flatten_conjunctions(terms, &assertions),
        rounds: 0,
        merges: 0,
    };
    for _ in 0..MAX_ROUNDS {
        let mut round = Round::new(terms, &result.assertions);
        if round.merges == 0 && round.fixed.is_empty() {
            break;
        }
        let next = round.rewrite_window(terms, &result.assertions);
        let next = flatten_conjunctions(terms, &next);
        if next == result.assertions {
            break;
        }
        result.rounds += 1;
        result.merges += round.merges;
        result.assertions = next;
        if result.assertions == [terms.false_term()] {
            break;
        }
    }
    result
}

/// The top-level conjuncts of `assertions`, in order, without repeats and
/// without `true`. A `false` conjunct makes the window `[false]`.
fn flatten_conjunctions(terms: &TermStore, assertions: &[TermId]) -> Vec<TermId> {
    let true_term = terms.true_term();
    let false_term = terms.false_term();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut out = Vec::with_capacity(assertions.len());
    let mut stack: Vec<TermId> = Vec::new();
    for &assertion in assertions {
        stack.push(assertion);
        while let Some(term) = stack.pop() {
            if term == true_term || !seen.insert(term) {
                continue;
            }
            if term == false_term {
                return vec![false_term];
            }
            match terms.get(term) {
                TermData::App(sym, args) if sym.name() == "and" => {
                    // Reverse keeps the conjuncts in their written order.
                    stack.extend(args.iter().rev().copied());
                }
                _ => out.push(term),
            }
        }
    }
    out
}

/// How a conjunct stands in the window.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Standing {
    /// An equality between non-Boolean terms that joined its two sides (or
    /// found them joined): restated by the defining equalities.
    RootEquality,
    /// A literal over a theory atom (node of the atom, its truth value).
    Literal(u32, bool),
    /// Anything else, an equality between two different values included.
    Formula,
}

/// One round: the congruence closure of the window's root equalities and the
/// rewriting it licenses.
struct Round {
    closure: Closure,
    standing: Vec<Standing>,
    /// Root equalities that joined two classes.
    merges: usize,
    /// Per class root: the representative node.
    rep: Vec<u32>,
    /// Per class root: the smallest node, used where a representative
    /// would have to be rebuilt from itself.
    smallest: Vec<u32>,
    /// Class root of a fixed atom to its truth value.
    fixed: HashMap<u32, bool>,
    /// Per class root: the term its members are rewritten to.
    memo: Vec<Option<TermId>>,
    in_progress: Vec<bool>,
}

impl Round {
    fn new(terms: &TermStore, window: &[TermId]) -> Self {
        let mut closure = Closure::new(terms, window);
        // Root equalities first, so that a literal's atom is classified in
        // the finished closure.
        let mut merges = 0;
        let mut standing = Vec::with_capacity(window.len());
        for &conjunct in window {
            let joined = match root_equality_sides(terms, conjunct) {
                Some((a, b)) => {
                    let (a, b) = (closure.node(a), closure.node(b));
                    merges += usize::from(closure.assert_equal(a, b));
                    closure.find(a) == closure.find(b)
                }
                None => false,
            };
            standing.push(if joined {
                Standing::RootEquality
            } else {
                Standing::Formula
            });
        }
        let mut fixed = HashMap::default();
        for (slot, &conjunct) in standing.iter_mut().zip(window) {
            if *slot == Standing::RootEquality {
                continue;
            }
            let (atom, value) = match terms.get(conjunct) {
                TermData::Not(inner) => (*inner, false),
                _ => (conjunct, true),
            };
            if is_theory_atom_shape(terms, atom) {
                let node = closure.node(atom);
                fixed.entry(closure.find(node)).or_insert(value);
                *slot = Standing::Literal(node, value);
            }
        }
        let nodes = closure.len();
        let mut round = Self {
            closure,
            standing,
            merges,
            rep: Vec::new(),
            smallest: Vec::new(),
            fixed,
            memo: vec![None; nodes],
            in_progress: vec![false; nodes],
        };
        round.pick_representatives(terms);
        round
    }

    /// A value constant stands for its class; else an arithmetic term (`+`,
    /// `-`, `*`), so that an uninterpreted application the window defines by
    /// arithmetic is read as that arithmetic and its atoms share their
    /// linear form with the other atoms over the same quantities; else the
    /// smallest term. Ties go to the older term.
    fn pick_representatives(&mut self, terms: &TermStore) {
        let nodes = self.closure.len();
        self.rep = (0..nodes as u32).collect();
        self.smallest = (0..nodes as u32).collect();
        let mut best: Vec<Option<(u8, u64, TermId)>> = vec![None; nodes];
        let mut best_small: Vec<Option<(u64, TermId)>> = vec![None; nodes];
        for node in 0..nodes as u32 {
            let class = self.closure.find(node) as usize;
            let term = self.closure.term(node);
            let rank = match terms.get(term) {
                TermData::Const(_) => 0,
                TermData::App(sym, _)
                    if matches!(sym.name(), "+" | "-" | "*")
                        && matches!(terms.sort(term), Sort::Int | Sort::Real) =>
                {
                    1
                }
                _ => 2,
            };
            let size = self.closure.size(node);
            if best[class].is_none_or(|current| (rank, size, term) < current) {
                best[class] = Some((rank, size, term));
                self.rep[class] = node;
            }
            if best_small[class].is_none_or(|current| (size, term) < current) {
                best_small[class] = Some((size, term));
                self.smallest[class] = node;
            }
        }
    }

    /// The term every member of `class` is rewritten to: the truth value of
    /// a fixed atom, else the representative over the canonical terms of its
    /// arguments.
    fn canonical(&mut self, terms: &mut TermStore, class: u32) -> TermId {
        if let Some(done) = self.memo[class as usize] {
            return done;
        }
        if let Some(&value) = self.fixed.get(&class) {
            let constant = if value {
                terms.true_term()
            } else {
                terms.false_term()
            };
            self.memo[class as usize] = Some(constant);
            return constant;
        }
        if self.in_progress[class as usize] {
            // The representative contains a member of its own class. Any
            // member is equal to the class under the root equalities, and
            // the smallest one contains none.
            return self.closure.term(self.smallest[class as usize]);
        }
        self.in_progress[class as usize] = true;
        let rep = self.rep[class as usize];
        let rebuilt = stacker::maybe_grow(STACK_RED_ZONE, STACK_SIZE, || {
            self.over_representatives(terms, rep)
        });
        self.in_progress[class as usize] = false;
        self.memo[class as usize] = Some(rebuilt);
        rebuilt
    }

    /// `node`'s term with every argument replaced by the canonical term of
    /// the argument's class.
    fn over_representatives(&mut self, terms: &mut TermStore, node: u32) -> TermId {
        let term = self.closure.term(node);
        let kids = self.closure.children(node).to_vec();
        if kids.is_empty() {
            return term;
        }
        let mut new_kids = Vec::with_capacity(kids.len());
        for kid in kids {
            let class = self.closure.find(kid);
            new_kids.push(self.canonical(terms, class));
        }
        match terms.get(term).clone() {
            TermData::App(sym, args) => {
                if args == new_kids {
                    term
                } else {
                    PropagateValues::fold_rebuild(terms, sym, term, new_kids)
                }
            }
            TermData::Not(_) => terms.mk_not(new_kids[0]),
            TermData::Ite(..) => terms.mk_ite(new_kids[0], new_kids[1], new_kids[2]),
            _ => term,
        }
    }

    /// The rewritten window: every conjunct over representatives, then the
    /// defining equalities.
    fn rewrite_window(&mut self, terms: &mut TermStore, window: &[TermId]) -> Vec<TermId> {
        let mut out = Vec::with_capacity(window.len());
        for (index, &conjunct) in window.iter().enumerate() {
            match self.standing[index] {
                Standing::RootEquality => {}
                Standing::Literal(atom, value) => {
                    // The atom itself, not the truth value its class is
                    // rewritten to everywhere else.
                    let atom = self.over_representatives(terms, atom);
                    out.push(if value { atom } else { terms.mk_not(atom) });
                }
                Standing::Formula => {
                    let class = self.closure.find(self.closure.node(conjunct));
                    out.push(self.canonical(terms, class));
                }
            }
        }
        let mut definitions = Vec::new();
        for node in 0..self.closure.len() as u32 {
            if let Some((written, representative)) = self.definition(terms, node) {
                definitions.push(terms.mk_eq_coerce(written, representative));
            }
        }
        // The same order whatever order the nodes were met in, so that a
        // window the pass has finished is a fixpoint.
        definitions.sort();
        definitions.dedup();
        out.extend(definitions);
        out
    }

    /// For a non-Boolean term of a joined class that is not the class
    /// representative once written over the representatives of its
    /// arguments: that writing, and the representative.
    fn definition(&mut self, terms: &mut TermStore, node: u32) -> Option<(TermId, TermId)> {
        if *terms.sort(self.closure.term(node)) == Sort::Bool {
            return None;
        }
        let class = self.closure.find(node);
        if self.closure.class_size(class) < 2 {
            return None;
        }
        let written = self.over_representatives(terms, node);
        let representative = self.canonical(terms, class);
        (written != representative).then_some((written, representative))
    }
}

/// The two sides of `conjunct` when it is an equality between non-Boolean
/// terms.
fn root_equality_sides(terms: &TermStore, conjunct: TermId) -> Option<(TermId, TermId)> {
    match terms.get(conjunct) {
        TermData::App(sym, args)
            if sym.name() == "=" && args.len() == 2 && *terms.sort(args[0]) != Sort::Bool =>
        {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// `true` for a Boolean term that is not built by a Boolean connective: a
/// free Boolean symbol or a predicate application, equalities between
/// non-Boolean terms included.
fn is_theory_atom_shape(terms: &TermStore, term: TermId) -> bool {
    if *terms.sort(term) != Sort::Bool {
        return false;
    }
    match terms.get(term) {
        TermData::Var(..) => true,
        TermData::App(sym, args) => match sym.name() {
            "and" | "or" | "=>" | "xor" => false,
            "=" | "distinct" => args.iter().all(|&arg| *terms.sort(arg) != Sort::Bool),
            _ => true,
        },
        _ => false,
    }
}

#[cfg(test)]
#[path = "root_congruence_tests.rs"]
mod tests;
