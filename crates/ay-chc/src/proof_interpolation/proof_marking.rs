// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof node marking and atom collection.

use super::*;

pub(super) fn atom_of_literal(terms: &TermStore, mut lit: TermId) -> TermId {
    loop {
        match terms.get(lit) {
            TermData::Not(inner) => lit = *inner,
            _ => return lit,
        }
    }
}

pub(super) fn collect_theory_atoms(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
    out: &mut FxHashSet<TermId>,
) {
    let mut stack: Vec<TermId> = roots.into_iter().collect();
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        if is_theory_atom(terms, t) {
            out.insert(t);
            continue;
        }
        match terms.get(t) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            // Unknown TermData variant; skip (#6091).
            _ => {}
        }
    }
}

#[cfg(test)]
pub(super) fn and_with_tail(head: ChcExpr, tail: &[ChcExpr]) -> ChcExpr {
    if tail.is_empty() {
        return head;
    }

    let mut conjuncts = Vec::with_capacity(1 + tail.len());
    conjuncts.push(head);
    conjuncts.extend(tail.iter().cloned());
    ChcExpr::and_all(conjuncts)
}

pub(super) fn and_slice(conjuncts: &[ChcExpr]) -> ChcExpr {
    ChcExpr::and_all(conjuncts.iter().cloned())
}

fn mark_atom(
    atom: TermId,
    a_atoms: &FxHashSet<TermId>,
    b_atoms: &FxHashSet<TermId>,
) -> DependencyMark {
    match (a_atoms.contains(&atom), b_atoms.contains(&atom)) {
        (false, false) => DependencyMark::None,
        (true, false) => DependencyMark::A,
        (false, true) => DependencyMark::B,
        (true, true) => DependencyMark::AB,
    }
}

fn mark_literal(
    terms: &TermStore,
    lit: TermId,
    a_atoms: &FxHashSet<TermId>,
    b_atoms: &FxHashSet<TermId>,
) -> DependencyMark {
    let atom = atom_of_literal(terms, lit);
    mark_atom(atom, a_atoms, b_atoms)
}

/// Mark proof steps by their A/B dependency.
///
/// For now, we compute a conservative mark based on the term IDs occurring in each step.
///
/// REQUIRES: `proof` steps are in topological order (premises precede dependents)
/// ENSURES: returned vec has same length as `proof.len()`
/// ENSURES: Resolution marks are union of their premise marks
pub(crate) fn mark_proof_nodes(
    proof: &Proof,
    terms: &TermStore,
    a_atoms: &FxHashSet<TermId>,
    b_atoms: &FxHashSet<TermId>,
) -> Vec<DependencyMark> {
    let mut marks: Vec<DependencyMark> = vec![DependencyMark::None; proof.len()];

    for (idx, step) in proof.steps.iter().enumerate() {
        let id = ProofId(idx as u32);
        let mark = match step {
            ProofStep::Assume(t) => mark_literal(terms, *t, a_atoms, b_atoms),
            ProofStep::TheoryLemma { clause, .. } => clause
                .iter()
                .copied()
                .map(|t| mark_literal(terms, t, a_atoms, b_atoms))
                .fold(DependencyMark::None, DependencyMark::union),
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                debug_assert!(
                    (clause1.0 as usize) < proof.len(),
                    "BUG: Resolution clause1 index {} out of bounds (proof len {})",
                    clause1.0,
                    proof.len()
                );
                debug_assert!(
                    (clause2.0 as usize) < proof.len(),
                    "BUG: Resolution clause2 index {} out of bounds (proof len {})",
                    clause2.0,
                    proof.len()
                );
                let m1 = marks
                    .get(clause1.0 as usize)
                    .copied()
                    .unwrap_or(DependencyMark::None);
                let m2 = marks
                    .get(clause2.0 as usize)
                    .copied()
                    .unwrap_or(DependencyMark::None);
                m1.union(m2)
            }
            ProofStep::Step { premises, args, .. } => {
                let prem_mark = premises
                    .iter()
                    .copied()
                    .map(|p| {
                        debug_assert!(
                            (p.0 as usize) < proof.len(),
                            "BUG: Step premise index {} out of bounds (proof len {})",
                            p.0,
                            proof.len()
                        );
                        marks
                            .get(p.0 as usize)
                            .copied()
                            .unwrap_or(DependencyMark::None)
                    })
                    .fold(DependencyMark::None, DependencyMark::union);
                let args_mark = args
                    .iter()
                    .copied()
                    .map(|t| mark_literal(terms, t, a_atoms, b_atoms))
                    .fold(DependencyMark::None, DependencyMark::union);
                prem_mark.union(args_mark)
            }
            ProofStep::Anchor { end_step, .. } => marks
                .get(end_step.0 as usize)
                .copied()
                .unwrap_or(DependencyMark::None),
            // Unknown ProofStep variant; mark as None (#6091).
            _ => DependencyMark::None,
        };
        marks[id.0 as usize] = mark;
    }

    debug_assert_eq!(
        marks.len(),
        proof.len(),
        "BUG: marks length {} != proof length {}",
        marks.len(),
        proof.len()
    );
    marks
}

pub(crate) fn collect_farkas_lemmas(proof: &Proof) -> Vec<ProofId> {
    proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(idx, step)| match step {
            ProofStep::TheoryLemma {
                farkas: Some(_), ..
            } => Some(ProofId(idx as u32)),
            _ => None,
        })
        .collect()
}
