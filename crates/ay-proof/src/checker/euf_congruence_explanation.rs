// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict validation of a packed EUF **congruence-closure explanation**
//! ([`ay_core::TheoryLemmaKind::EufCongruenceExplanation`]).
//!
//! # The clause
//!
//! ```text
//! (cl (not (= a_1 b_1)) .. (not (= a_n b_n)) (= s t))
//! ```
//!
//! — with the positive equality at ANY position, and equally in the packed
//! single-literal form `(cl (or L_1 .. L_m))` the lazy-EUF / array-lemma lanes
//! emit. The clause is accepted exactly when
//!
//! ```text
//!     { a_1 = b_1, .., a_n = b_n }  |=_EUF  s = t
//! ```
//!
//! i.e. when `s` and `t` fall in the same class of the congruence closure of
//! the hypothesis equalities over the clause's own sub-term DAG.
//!
//! # Why this is not [`super::euf`]'s `validate_euf_transitive`
//!
//! `eq_transitive` needs the hypotheses to form a syntactic PATH from `s` to
//! `t`, with every hypothesis on it, and it fixes the conclusion LAST. A
//! congruence-closure explanation generally does neither: the connecting link
//! may be produced by congruence rather than stated, as in the measured QF_AX
//! shape
//!
//! ```text
//! (or (= (select (store C i2 v) i0) (select C i0))
//!     (not (= i0 i3))
//!     (not (= e (select (store C i2 v) i3)))
//!     (not (= e (select C i0))))
//! ```
//!
//! where nothing at all is stated about `(select (store C i2 v) i0)` — it is
//! reached from `(select (store C i2 v) i3)` by congruence on the index
//! position under the hypothesis `i0 = i3`.
//!
//! # Soundness
//!
//! Let `H` be the hypothesis equalities and `M` any structure interpreting
//! every symbol of the clause. If `M |/= H` then some literal
//! `(not (= a_i b_i))` is true in `M` and the clause holds outright, so assume
//! `M |= H`. The routine only ever merges two nodes when
//!
//! * **(hypothesis)** they are the two sides of some `(not (= a b))` literal —
//!   sound because `M |= a = b`; or
//! * **(congruence)** they are two nodes that agree on head (function symbol
//!   AND result sort, or the `not` / `ite` former) and whose children are
//!   pairwise already merged — sound because each of those formers denotes a
//!   FUNCTION in `M`, so equal arguments give equal results.
//!
//! By induction over the merge sequence every merged pair is equal in `M`. The
//! clause is accepted only when the conclusion's two sides are merged, hence
//! `M |= s = t` and the positive literal is true. The clause is therefore true
//! in every `M`: it is valid. Nothing about the conflict that produced it, and
//! no problem context, is taken on trust — the clause structure IS the whole
//! certificate, exactly as for the other three EUF rules.
//!
//! Completeness (ground EUF entailment IS decided by congruence closure) is
//! neither claimed nor needed: a clause the closure does not settle is
//! REJECTED, which is the fail-closed direction. The same goes for both
//! resource bounds below — exceeding either rejects.
//!
//! # Metering
//!
//! The validator debits its ACTUAL work through the strict checker's progress
//! callback — the `(0, 0)`-precharge-then-debit-actual pattern
//! `ArrayRowChain` / `ArrayStorePermutation` use — rather than taking the
//! `General` semantic precharge. That precharge is the SQUARE of the
//! tree-unfolded payload, and this population's packed clauses are exactly the
//! heavily-shared `store` chains where tree unfolding is astronomically bigger
//! than the DAG: taking it would convert a typed `TrustStep` refusal into a
//! `ResourceLimit` one, which is strictly worse (it bypasses the rescue lane).
//! Every interned node and every fixpoint node-visit is debited instead, so an
//! adversarially wide clause still fails closed.
//!
//! # What is deliberately NOT decomposed
//!
//! Congruence is applied only to a node that is a total function of its
//! recorded children. `Forall` / `Exists` / `Let` are opaque LEAVES: their
//! children live under a binder, where replacing a sub-term by an equal one is
//! not licensed (`x = c` does not make `(forall x. p x)` equal to
//! `(forall x. p c)`). Treating them as leaves is the sound direction — such a
//! node can still be merged by an explicit hypothesis, never by congruence.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{ProofId, Sort, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

/// Largest sub-term DAG this validator closes over; larger clauses are REJECTED.
const MAX_NODES: usize = 4096;

/// Largest number of fixpoint rounds. Every round that changes anything merges
/// at least one pair, so a run needs at most `MAX_NODES` of them; this cap
/// bounds the work at `MAX_NODES * MAX_ROUNDS` signature computations for an
/// adversarially wide clause and, like `MAX_NODES`, only ever REJECTS.
const MAX_ROUNDS: usize = 256;

/// The `head` slot reserved for `TermData::Not`.
const HEAD_NOT: usize = 0;
/// The `head` slot reserved for `TermData::Ite`.
const HEAD_ITE: usize = 1;
/// First `head` slot handed out to an `(symbol, result sort)` pair.
const HEAD_APP_BASE: usize = 2;

/// Work debited per node visit — one intern, plus one canonicalisation per
/// fixpoint round. Sixteen covers the hash lookup, the union-find walk and the
/// signature key for a node of any arity this validator admits.
const NODE_WORK: usize = 16;
/// Bytes debited per interned node: the union-find slots, the signature entry
/// and the child-pool entries.
const NODE_BYTES: usize = 8 * size_of::<TermId>();

/// Fail-closed rejection for a clause whose sub-term graph is too large.
fn oversize(step_id: ProofId) -> ProofCheckError {
    ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "EufCongruenceExplanation: clause sub-term graph exceeds the validation bound"
            .to_string(),
    }
}

pub(super) struct CongruenceClosure {
    /// Number of interned nodes.
    node_count: usize,
    /// Term -> node id.
    index: HashMap<TermId, usize>,
    /// Union-find parent per node id.
    parent: Vec<usize>,
    /// Union-by-size weight.
    weight: Vec<usize>,
    /// `None` for an opaque leaf; otherwise the node's head slot.
    head: Vec<Option<usize>>,
    /// `(start, len)` of the node's children inside `child_pool`.
    child_span: Vec<(usize, usize)>,
    /// Flat child storage, so the fixpoint never allocates per node.
    child_pool: Vec<usize>,
    /// Interned `(symbol, result sort)` pairs, so the fixpoint never clones a
    /// symbol name. The result SORT is part of the head on purpose:
    /// `TermStore::mk_app` takes the sort as a separate argument, so the same
    /// `(symbol, arguments)` pair can in principle name two differently-sorted
    /// nodes, and separating them can only ever REDUCE the merges — the safe
    /// direction.
    heads: HashMap<(Symbol, Sort), usize>,
}

/// The formers congruence is licensed for. Each denotes a TOTAL FUNCTION of
/// its recorded children in every structure, which is exactly what makes
/// "equal children => equal results" sound.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Former {
    App,
    Not,
    Ite,
}

/// The former and children of a node congruence may descend through, or `None`
/// for a node this validator treats as an OPAQUE LEAF.
///
/// THE single decision point for what congruence reaches. `Var`/`Const`
/// genuinely have no children. `Forall`/`Exists`/`Let` DO have children, but
/// they live under a binder, where replacing a sub-term by an equal one is not
/// licensed (`x = c` does not make `(forall x. p x)` equal to
/// `(forall x. p c)`) — so they are leaves here. `TermData` is
/// `#[non_exhaustive]`, and a former this validator has never seen is a leaf
/// too: the SOUND default, since congruence never fires on a leaf and the
/// worst outcome is a clause declined.
fn functional_form(terms: &TermStore, term: TermId) -> Option<(Former, Vec<TermId>)> {
    match terms.get(term) {
        TermData::App(_, args) => Some((Former::App, args.clone())),
        TermData::Not(inner) => Some((Former::Not, vec![*inner])),
        TermData::Ite(cond, then_branch, else_branch) => {
            Some((Former::Ite, vec![*cond, *then_branch, *else_branch]))
        }
        TermData::Var(..) | TermData::Const(_) => None,
        TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => None,
        _ => None,
    }
}

impl CongruenceClosure {
    pub(super) fn new() -> Self {
        Self {
            node_count: 0,
            index: HashMap::default(),
            parent: Vec::new(),
            weight: Vec::new(),
            head: Vec::new(),
            child_span: Vec::new(),
            child_pool: Vec::new(),
            heads: HashMap::default(),
        }
    }

    fn head_slot(&mut self, symbol: &Symbol, sort: &Sort) -> usize {
        let next = self.heads.len() + HEAD_APP_BASE;
        *self
            .heads
            .entry((symbol.clone(), sort.clone()))
            .or_insert(next)
    }

    /// The head slot of a node, given its former.
    ///
    /// `HEAD_NOT`/`HEAD_ITE` are RESERVED and disjoint from every application
    /// slot (`HEAD_APP_BASE`), so `(not p)` can never share a congruence head
    /// with a unary application.
    fn head_of(&mut self, terms: &TermStore, term: TermId, former: Former) -> usize {
        match former {
            Former::Not => HEAD_NOT,
            Former::Ite => HEAD_ITE,
            Former::App => match terms.get(term) {
                TermData::App(symbol, _) => {
                    let symbol = symbol.clone();
                    let sort = terms.sort(term).clone();
                    self.head_slot(&symbol, &sort)
                }
                // Unreachable: `Former::App` is produced only for an `App`
                // node. Falling back to a FRESH slot (never equal to any
                // interned one) keeps the impossible case fail-closed.
                _ => self.heads.len() + HEAD_APP_BASE + self.node_count,
            },
        }
    }

    /// Intern `term` and every sub-term reachable through a node that is a
    /// total function of its children. Fails closed once `MAX_NODES` is
    /// exceeded or the caller's envelope cannot absorb the walk.
    ///
    /// ITERATIVE on purpose: recursing here would make the checker's stack
    /// depth a function of the ADVERSARY's term depth, and the measured QF_AX
    /// population already carries `store` chains a dozen deep.
    pub(super) fn add(
        &mut self,
        terms: &TermStore,
        root: TermId,
        step_id: ProofId,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<usize, ProofCheckError> {
        if let Some(&id) = self.index.get(&root) {
            return Ok(id);
        }
        let mut expanded: HashMap<TermId, ()> = HashMap::default();
        let mut stack: Vec<(TermId, bool)> = vec![(root, false)];
        while let Some((term, ready)) = stack.pop() {
            if self.index.contains_key(&term) {
                continue;
            }
            let form = functional_form(terms, term);
            if !ready {
                if expanded.insert(term, ()).is_some() {
                    continue;
                }
                // Debit the visit BEFORE descending.
                if !progress(NODE_WORK, NODE_BYTES) {
                    return Err(ProofCheckError::ResourceLimit);
                }
                stack.push((term, true));
                if let Some((_, children)) = &form {
                    for &child in children {
                        if !self.index.contains_key(&child) {
                            stack.push((child, false));
                        }
                    }
                }
                if stack.len() > MAX_NODES.saturating_mul(4) {
                    return Err(oversize(step_id));
                }
                continue;
            }
            if self.node_count >= MAX_NODES {
                return Err(oversize(step_id));
            }
            let id = self.node_count;
            self.node_count += 1;
            self.index.insert(term, id);
            self.parent.push(id);
            self.weight.push(1);
            match form {
                Some((former, children)) => {
                    let head = self.head_of(terms, term, former);
                    let start = self.child_pool.len();
                    for child in &children {
                        // Every child was interned before this node was
                        // re-visited in `ready` state. `expanded` skips a
                        // re-push, and the only window in which a node could be
                        // queued-but-not-yet-interned when a PARENT of it is
                        // expanded is while that node's own sub-tree is being
                        // resolved — which would make the parent a descendant
                        // of its own child, i.e. a CYCLE. The interned term DAG
                        // is acyclic, so the lookup cannot miss; a miss would
                        // mean the traversal is wrong, and failing closed is
                        // the only safe answer.
                        let child_id = *self.index.get(child).ok_or_else(|| oversize(step_id))?;
                        self.child_pool.push(child_id);
                    }
                    self.head.push(Some(head));
                    self.child_span.push((start, children.len()));
                }
                None => {
                    self.head.push(None);
                    self.child_span.push((0, 0));
                }
            }
        }
        self.index
            .get(&root)
            .copied()
            .ok_or_else(|| oversize(step_id))
    }

    pub(super) fn find(&mut self, mut id: usize) -> usize {
        while self.parent[id] != id {
            self.parent[id] = self.parent[self.parent[id]];
            id = self.parent[id];
        }
        id
    }

    /// Merge two classes. Returns `true` when they were distinct.
    pub(super) fn union(&mut self, a: usize, b: usize) -> bool {
        let (mut ra, mut rb) = (self.find(a), self.find(b));
        if ra == rb {
            return false;
        }
        if self.weight[ra] > self.weight[rb] {
            std::mem::swap(&mut ra, &mut rb);
        }
        self.parent[ra] = rb;
        self.weight[rb] += self.weight[ra];
        true
    }

    /// Close the current classes under congruence.
    ///
    /// A round re-canonicalises every node and merges any two whose canonical
    /// signatures COINCIDE. That is sound even though classes move during a
    /// round: union-find representatives only coarsen, so a representative
    /// recorded earlier in a round is still a representative when a later node
    /// matches it, and the two signatures therefore still agree at the END of
    /// the round.
    pub(super) fn close(
        &mut self,
        step_id: ProofId,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<(), ProofCheckError> {
        let mut canonical: Vec<usize> = Vec::new();
        for _round in 0..MAX_ROUNDS {
            let mut table: HashMap<(usize, Vec<usize>), usize> = HashMap::default();
            let mut changed = false;
            for id in 0..self.node_count {
                let Some(head) = self.head[id] else {
                    continue;
                };
                if !progress(NODE_WORK, 0) {
                    return Err(ProofCheckError::ResourceLimit);
                }
                let (start, len) = self.child_span[id];
                canonical.clear();
                for offset in 0..len {
                    let child = self.child_pool[start + offset];
                    canonical.push(self.find(child));
                }
                let key = (head, canonical.clone());
                match table.get(&key) {
                    Some(&other) => {
                        if self.union(id, other) {
                            changed = true;
                        }
                    }
                    None => {
                        table.insert(key, id);
                    }
                }
            }
            if !changed {
                return Ok(());
            }
        }
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruenceExplanation: congruence closure did not converge within the \
                     validation bound"
                .to_string(),
        })
    }
}

/// Decode a term as an equality `(= lhs rhs)`.
fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Validate one congruence-closure explanation clause. See the module docs for
/// the schema and the soundness argument.
pub(crate) fn validate_euf_congruence_explanation(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let reject = |reason: &str| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("EufCongruenceExplanation: {reason}"),
    };
    let flattened = super::euf::flatten_or_clause(terms, clause);
    let literals = flattened.as_slice();
    if literals.len() < 2 {
        return Err(reject("clause must have at least 2 literals"));
    }

    // Partition into hypothesis equalities and the single conclusion.
    //
    // The POLARITY split is the load-bearing part of the schema: a hypothesis
    // is read from a NEGATED equality only. Reading a positive equality as a
    // hypothesis would accept `(cl (= a b) (= (f a) (f b)))`, which is FALSE
    // under `a := 0, b := 1, f(0) := 2, f(1) := 3`. `strip_not` counts the
    // negation PARITY, so `(not (not (= a b)))` is a positive literal and not
    // a hypothesis — the same clause with the same falsifying assignment.
    let mut hypotheses: Vec<(TermId, TermId)> = Vec::with_capacity(literals.len());
    let mut conclusion: Option<(TermId, TermId)> = None;
    for &literal in literals {
        let (inner, negated) = super::euf::strip_not(terms, literal);
        let Some((lhs, rhs)) = decode_eq(terms, inner) else {
            return Err(reject(
                "every literal must be a (possibly negated) equality",
            ));
        };
        if negated {
            hypotheses.push((lhs, rhs));
        } else if conclusion.replace((lhs, rhs)).is_some() {
            return Err(reject("clause must have exactly one positive equality"));
        }
    }
    let Some((goal_lhs, goal_rhs)) = conclusion else {
        return Err(reject("clause has no positive equality to conclude"));
    };
    if hypotheses.is_empty() {
        return Err(reject("clause has no hypothesis equality"));
    }

    let mut closure = CongruenceClosure::new();
    let goal_lhs = closure.add(terms, goal_lhs, step_id, progress)?;
    let goal_rhs = closure.add(terms, goal_rhs, step_id, progress)?;
    let mut edges = Vec::with_capacity(hypotheses.len());
    for (lhs, rhs) in hypotheses {
        let lhs = closure.add(terms, lhs, step_id, progress)?;
        let rhs = closure.add(terms, rhs, step_id, progress)?;
        edges.push((lhs, rhs));
    }
    for (lhs, rhs) in edges {
        closure.union(lhs, rhs);
    }
    closure.close(step_id, progress)?;

    if closure.find(goal_lhs) == closure.find(goal_rhs) {
        Ok(())
    } else {
        Err(reject(
            "the hypothesis equalities do not entail the conclusion by congruence closure",
        ))
    }
}

/// Recognize the exact congruence-closure explanation shape
/// `validate_euf_congruence_explanation` accepts.
///
/// Like the other EUF recognizers, recognition IS the strict validator run on
/// the clause exactly as recorded, so classifier and checker cannot drift and
/// a clause is only ever labelled with a kind whose validator has already
/// accepted it (fail-closed). Unlike `eq_transitive` / `eq_congruent` this
/// schema is ORDER-FREE, so a caller may relabel a leaf IN PLACE without
/// touching the clause its consumers already reference.
///
/// The recognizer runs the validator with an UNLIMITED meter. That is the
/// right envelope for a classifier: the intrinsic bounds (`MAX_NODES`,
/// `MAX_ROUNDS`) still apply, and the strict checker re-runs the same
/// validation under the caller's real envelope, so the checker — not this
/// classifier — remains the only authority on whether the work fits.
#[must_use]
pub fn recognize_euf_congruence_explanation(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_euf_congruence_explanation(terms, ProofId(0), clause, &mut |_, _| true).is_ok()
}

#[cfg(test)]
#[path = "euf_congruence_explanation_tests.rs"]
mod tests;
