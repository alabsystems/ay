// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A bit-vector lemma decided by its CLOSED atoms, re-derived from the text.
//!
//! WHAT IT LOWERS. A `BvBitBlast` theory lemma that AY's strict checker has
//! already validated, whose PRINTED clause is a propositional consequence of
//! the values of its closed atoms. The motivating shape is a ground guarded
//! quantifier instance: `forall_inst` of
//! `(forall ((i (_ BitVec 64))) (=> (and (bvsge i #x..fe) (bvslt i #x..02)) (= (select a i) #x07)))`
//! at `i = #xff..ff`, and the lemma
//!
//! ```text
//! (cl (= #b00000111 (select a #b1..1)) (not (=> (and (bvsge #b1..1 #x..fe) (bvslt #b1..1 #x..02)) (= (select a #b1..1) #x07))))
//! ```
//!
//! which holds because the guard is TRUE. No other lowering could print it:
//! pinned carcara 1.1.0 has no `bitblast_*` rule for `bvsge`, its
//! `bitblast_slt` states only a unit equivalence, the complete bit-blast
//! lowering takes only `(cl (not A))`, and its `evaluate` reads a negative
//! signed operand as its magnitude (see [`atoms`]). So the lemma shipped as
//! `hole` and the model-checker-consumer `signed_range64_*` corpus rows were `holey`.
//!
//! HOW. Everything below reads the printed clause and nothing else:
//!
//! 1. [`skeleton`] parses each literal's `not`/`and`/`or`/`=>` structure down
//!    to atoms and states every connective's Tseitin clauses with the stock
//!    tautology rules (`and_pos`, `implies_pos`, …), plus `eq_symmetric`
//!    bridges between the two printed orientations of one equality;
//! 2. [`atoms`] decides each closed atom by value and PROVES its unit clause
//!    (pseudo-Boolean blasting plus `la_generic`, `eq_reflexive`,
//!    `arrays_idx`/`arrays_row`). A `select` from a nullary `define-fun` is
//!    read through the problem's own premise `(= a body)`: AY's term store
//!    has already expanded the macro, the printed clause names it, and that
//!    premise is exactly the bridge pinned carcara (without
//!    `--apply-function-defs`) holds;
//! 3. the negated clause is unit-propagated over those clauses, and the
//!    conflict is transported as a chain of BINARY resolutions whose final
//!    clause is a sub-multiset of the printed clause, closed by `weakening`
//!    and `reordering`.
//!
//! FAIL CLOSED. No conflict, an unparsed shape, a shell count the checker
//! would not resolve, or a budget overrun returns `None`, and the honest
//! `hole` stays. The printed clause is never assumed; a clause that is not
//! valid has no conflict to transport, so no document can claim it.

use super::*;

mod atoms;
mod emit;
mod skeleton;
#[cfg(test)]
mod tests;

use emit::Emitter;
use skeleton::{Clause, Kind, Lit, NodeId, Origin, Skeleton};

/// Largest printed clause this lowering reads.
const MAX_CLAUSE_BYTES: usize = 64 * 1024;
/// Largest document it emits.
const MAX_OUTPUT_BYTES: usize = 4 * 1024 * 1024;
/// Most skeleton nodes (connectives and atoms).
const MAX_NODES: usize = 256;
/// Deepest connective nesting.
const MAX_DEPTH: usize = 32;
/// Most literals in the printed clause.
const MAX_LITERALS: usize = 64;
/// Widest bit-vector literal an atom may compare.
const MAX_WIDTH: u32 = 128;
/// Longest store chain (and macro unfolding) one `select` may read through.
const MAX_READ_DEPTH: usize = 64;
/// Most atoms decided per clause.
const MAX_DECIDED_ATOMS: usize = 64;

/// Why a node holds its value on the propagation trail.
#[derive(Clone, Copy)]
enum Reason {
    /// The negation of a printed clause literal.
    Goal,
    /// Unit propagation over this clause.
    Clause(usize),
}

/// The propagation state over one clause set.
struct Trail {
    value: Vec<Option<bool>>,
    reason: Vec<Option<Reason>>,
    position: Vec<usize>,
    assigned: usize,
}

impl Trail {
    fn assign(&mut self, node: NodeId, value: bool, reason: Reason) -> Option<()> {
        match self.value[node] {
            Some(existing) => (existing == value).then_some(()),
            None => {
                self.value[node] = Some(value);
                self.reason[node] = Some(reason);
                self.position[node] = self.assigned;
                self.assigned += 1;
                Some(())
            }
        }
    }
}

impl<'a> AlethePrinter<'a> {
    /// Attach the problem's nullary `define-fun` premises: printed symbol to
    /// the printed body of `(define-fun a () S body)`.
    #[must_use]
    pub(crate) fn with_nullary_definitions(
        mut self,
        definitions: Option<&'a HashMap<String, String>>,
    ) -> Self {
        self.nullary_definitions = definitions;
        self
    }

    /// The last lowering before a theory lemma prints as `hole`, and only for
    /// a lemma AY's bit-blast checker validated: see
    /// [`Self::lower_closed_guard_clause`].
    pub(super) fn lower_closed_guard_lemma(
        &self,
        kind: &ay_core::TheoryLemmaKind,
        id: ProofId,
        clause: &str,
    ) -> Option<String> {
        let validated = matches!(
            kind,
            ay_core::TheoryLemmaKind::BvBitBlast | ay_core::TheoryLemmaKind::BvBitBlastGate { .. }
        );
        validated.then(|| self.lower_closed_guard_clause(id, clause))?
    }

    /// Lower a validated bit-vector lemma, given as its PRINTED clause, whose
    /// clause is decided by its closed atoms; `None` keeps the honest `hole`.
    pub(super) fn lower_closed_guard_clause(&self, id: ProofId, clause: &str) -> Option<String> {
        if clause.len() > MAX_CLAUSE_BYTES || self.work_budget_exhausted() {
            return None;
        }
        // Without a bit-vector literal no atom can be closed; this lowering is
        // not a general propositional prover, so it stops before parsing.
        if !["#b", "#x", "(_ bv"]
            .iter()
            .any(|marker| clause.contains(marker))
        {
            return None;
        }
        self.charge(clause.len() as u64);
        let goal = split_application(clause, "cl")?;
        if goal.is_empty() || goal.len() > MAX_LITERALS {
            return None;
        }
        let mut skeleton = Skeleton::default();
        let goal_lits = goal
            .iter()
            .map(|literal| skeleton.literal(literal, 0))
            .collect::<Option<Vec<_>>>()?;
        let mut clauses = skeleton.structural_clauses()?;
        let decided = self.decide_closed_atoms(id, &skeleton, &mut clauses)?;
        let (trail, conflict) = refute(&skeleton, &clauses, &goal_lits)?;
        let (chain, remaining) = analyze(&trail, &clauses, conflict)?;
        if remaining.iter().any(|lit| !goal_lits.contains(lit)) {
            return None;
        }
        let mut writer = Writer {
            emitter: Emitter::new(self, format!("{id}.cg")),
            skeleton: &skeleton,
            clauses: &clauses,
            decided: &decided,
            labels: HashMap::default(),
            symmetric: HashMap::default(),
        };
        let (label, printed) = writer.chain(conflict, &chain, &goal_lits)?;
        writer.conclude(&id.to_string(), &goal, &goal_lits, &label, &printed)?;
        let mut out = writer.emitter.out;
        if out.ends_with('\n') {
            out.pop();
        }
        (!self.work_budget_exhausted()).then_some(out)
    }

    /// Decide every closed atom of the skeleton and add its unit clause.
    fn decide_closed_atoms(
        &self,
        id: ProofId,
        skeleton: &Skeleton,
        clauses: &mut Vec<Clause>,
    ) -> Option<HashMap<NodeId, atoms::Decided>> {
        let mut decided = HashMap::default();
        for (node, entry) in skeleton.nodes.iter().enumerate() {
            if !matches!(entry.kind, Kind::Atom) {
                continue;
            }
            let prefix = format!("{id}.cga{node}.");
            let Some(atom) = atoms::decide(self, prefix, &entry.text, self.nullary_definitions)
            else {
                continue;
            };
            if decided.len() >= MAX_DECIDED_ATOMS {
                return None;
            }
            let unit = Lit {
                node,
                nots: u8::from(!atom.value),
            };
            clauses.push(Clause {
                lits: vec![unit],
                origin: Origin::Decided(node),
            });
            decided.insert(node, atom);
        }
        Some(decided)
    }
}

/// Assume every printed literal false and unit-propagate to a conflict.
fn refute(skeleton: &Skeleton, clauses: &[Clause], goal: &[Lit]) -> Option<(Trail, usize)> {
    let nodes = skeleton.nodes.len();
    let mut trail = Trail {
        value: vec![None; nodes],
        reason: vec![None; nodes],
        position: vec![0; nodes],
        assigned: 0,
    };
    for lit in goal {
        // A clause stating both `p` and `(not p)` is not this lowering's shape.
        trail.assign(lit.node, lit.nots % 2 == 1, Reason::Goal)?;
    }
    for _round in 0..=nodes {
        let mut progressed = false;
        for (index, clause) in clauses.iter().enumerate() {
            let mut open = None;
            let mut open_count = 0usize;
            let mut satisfied = false;
            for lit in &clause.lits {
                match trail.value[lit.node] {
                    Some(value) if lit.holds_when(value) => satisfied = true,
                    Some(_) => {}
                    None => {
                        open_count += 1;
                        open = Some(*lit);
                    }
                }
            }
            match (satisfied, open_count, open) {
                (true, _, _) => {}
                (false, 0, _) => return Some((trail, index)),
                (false, 1, Some(lit)) => {
                    trail.assign(lit.node, lit.nots % 2 == 0, Reason::Clause(index))?;
                    progressed = true;
                }
                _ => {}
            }
        }
        if !progressed {
            return None;
        }
    }
    None
}

/// A resolution chain: each entry is the reason clause resolved in and the
/// resolvent it produces.
type Chain = Vec<(usize, Vec<Lit>)>;

/// Resolve the conflict back to the printed literals; returns the chain and
/// the literals it leaves.
fn analyze(trail: &Trail, clauses: &[Clause], conflict: usize) -> Option<(Chain, Vec<Lit>)> {
    let mut resolvent = distinct(&clauses[conflict].lits);
    let mut chain = Vec::new();
    loop {
        let pivot = resolvent
            .iter()
            .filter(|lit| matches!(trail.reason[lit.node], Some(Reason::Clause(_))))
            .max_by_key(|lit| trail.position[lit.node])
            .copied();
        let Some(pivot) = pivot else {
            return Some((chain, resolvent));
        };
        let Some(Reason::Clause(reason)) = trail.reason[pivot.node] else {
            return None;
        };
        let reason_lits = distinct(&clauses[reason].lits);
        let mut on_pivot = reason_lits.iter().filter(|lit| lit.node == pivot.node);
        let (Some(implied), None) = (on_pivot.next(), on_pivot.next()) else {
            return None;
        };
        // One literal per side on the pivot, one `not` shell apart: the only
        // binary resolution pinned carcara replays without its RUP fallback.
        let pivots = resolvent
            .iter()
            .filter(|lit| lit.node == pivot.node)
            .count();
        if pivots != 1 || pivot.nots.abs_diff(implied.nots) != 1 {
            return None;
        }
        let mut next: Vec<Lit> = resolvent
            .iter()
            .filter(|lit| lit.node != pivot.node)
            .copied()
            .collect();
        for lit in reason_lits {
            if lit.node != pivot.node && !next.contains(&lit) {
                next.push(lit);
            }
        }
        if chain.len() > MAX_NODES {
            return None;
        }
        chain.push((reason, next.clone()));
        resolvent = next;
    }
}

fn distinct(lits: &[Lit]) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::with_capacity(lits.len());
    for lit in lits {
        if !out.contains(lit) {
            out.push(*lit);
        }
    }
    out
}

/// Emits the clauses a refutation uses, each once, and the chain over them.
struct Writer<'s, 'p, 'a> {
    emitter: Emitter<'p, 'a>,
    skeleton: &'s Skeleton,
    clauses: &'s [Clause],
    decided: &'s HashMap<NodeId, atoms::Decided>,
    labels: HashMap<usize, String>,
    symmetric: HashMap<(NodeId, NodeId), String>,
}

impl Writer<'_, '_, '_> {
    fn texts(&self, lits: &[Lit]) -> Vec<String> {
        lits.iter().map(|lit| self.skeleton.text(*lit)).collect()
    }

    /// The label of `index`'s clause, emitting its derivation on first use.
    fn ensure(&mut self, index: usize) -> Option<String> {
        if let Some(label) = self.labels.get(&index) {
            return Some(label.clone());
        }
        let clause = &self.clauses[index];
        let texts = self.texts(&clause.lits);
        let label = match clause.origin {
            Origin::Tautology(rule, index) => {
                let index = index.map(|index| index.to_string());
                self.emitter.step(&texts, rule, &[], index.as_deref())?
            }
            Origin::Decided(node) => {
                let atom = self.decided.get(&node)?;
                self.emitter.append(&atom.derivation)?;
                atom.label.clone()
            }
            Origin::Symmetry {
                equality,
                flipped,
                forward,
            } => {
                let swap = self.symmetry(equality, flipped)?;
                let rule = if forward { "equiv1" } else { "equiv2" };
                self.emitter.step(&texts, rule, &[&swap], None)?
            }
        };
        self.labels.insert(index, label.clone());
        Some(label)
    }

    /// `(cl (= E F))` by `eq_symmetric`, once per pair.
    fn symmetry(&mut self, equality: NodeId, flipped: NodeId) -> Option<String> {
        if let Some(label) = self.symmetric.get(&(equality, flipped)) {
            return Some(label.clone());
        }
        let statement = format!(
            "(= {} {})",
            self.skeleton.nodes[equality].text, self.skeleton.nodes[flipped].text
        );
        let label = self.emitter.step(&[statement], "eq_symmetric", &[], None)?;
        self.symmetric.insert((equality, flipped), label.clone());
        Some(label)
    }

    /// Print the resolution chain; returns the last label and its literals
    /// in printed order.
    fn chain(
        &mut self,
        conflict: usize,
        chain: &[(usize, Vec<Lit>)],
        goal: &[Lit],
    ) -> Option<(String, Vec<Lit>)> {
        let mut label = self.ensure(conflict)?;
        let mut printed = distinct(&self.clauses[conflict].lits);
        if printed.len() != self.clauses[conflict].lits.len() {
            // A clause with a repeated literal prints it twice; resolve on.
            return None;
        }
        for (reason, resolvent) in chain {
            let reason_label = self.ensure(*reason)?;
            let mut ordered = resolvent.clone();
            ordered.sort_by_key(|lit| goal.iter().position(|g| g == lit).unwrap_or(usize::MAX));
            let texts = self.texts(&ordered);
            label = self
                .emitter
                .step(&texts, "resolution", &[&label, &reason_label], None)?;
            printed = ordered;
        }
        Some((label, printed))
    }

    /// Close the last clause (a sub-multiset of the goal) to the printed goal.
    fn conclude(
        &mut self,
        id: &str,
        goal_texts: &[String],
        goal: &[Lit],
        label: &str,
        printed: &[Lit],
    ) -> Option<()> {
        let mut widened: Vec<Lit> = printed.to_vec();
        let mut available: Vec<Lit> = printed.to_vec();
        for lit in goal {
            if let Some(at) = available.iter().position(|seen| seen == lit) {
                available.swap_remove(at);
            } else {
                widened.push(*lit);
            }
        }
        if !available.is_empty() {
            return None;
        }
        if widened.len() == printed.len() {
            return self
                .emitter
                .command(id, goal_texts, "reordering", &[label], None);
        }
        if widened == goal {
            return self
                .emitter
                .command(id, goal_texts, "weakening", &[label], None);
        }
        let texts = self.texts(&widened);
        let weakened = self.emitter.step(&texts, "weakening", &[label], None)?;
        self.emitter
            .command(id, goal_texts, "reordering", &[&weakened], None)
    }
}
