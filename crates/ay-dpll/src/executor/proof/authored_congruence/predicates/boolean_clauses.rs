// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded binary resolution over exact authored clauses and checked UF schemas.
//! Unsupported roots are unused premises, never strengthened or normalized.

use super::*;
use ay_core::{AletheRule, TermStore};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Literal {
    atom: usize,
    positive: bool,
}

impl Literal {
    fn opposite(self) -> Self {
        Self {
            atom: self.atom,
            positive: !self.positive,
        }
    }
}

struct InputClause {
    root: TermId,
    children: [TermId; 2],
    literals: [Literal; 2],
}

struct Inputs {
    atoms: Vec<TermId>,
    clauses: Vec<InputClause>,
}

// Only one syntactic Not is admitted. This agrees with the checker's parity
// keys without silently assuming a normalized or doubly-negated source root.
fn literal(terms: &TermStore, term: TermId) -> Option<(TermId, bool)> {
    if terms.sort(term) != &Sort::Bool {
        return None;
    }
    let (atom, positive) = match terms.get(term) {
        TermData::Not(atom) => (*atom, false),
        _ => (term, true),
    };
    if terms.sort(atom) != &Sort::Bool {
        return None;
    }
    match terms.get(atom) {
        TermData::Var(..) => Some((atom, positive)),
        TermData::App(Symbol::Named(name), _)
            if !matches!(
                name.as_str(),
                "and" | "or" | "not" | "=>" | "implies" | "xor" | "ite"
            ) =>
        {
            Some((atom, positive))
        }
        _ => None,
    }
}

fn atom_index(atoms: &[TermId], term: TermId, attempt: &mut Attempt) -> Option<Option<usize>> {
    for (index, &atom) in atoms.iter().enumerate() {
        spend(&mut attempt.work)?;
        if atom == term {
            return Some(Some(index));
        }
    }
    Some(None)
}

impl Inputs {
    fn collect(
        executor: &mut Executor,
        authored: &[TermId],
        attempt: &mut Attempt,
    ) -> Option<Self> {
        if authored.len() > MAX_ROOTS {
            return None;
        }
        // At most two literal slots per admitted root. No source subtree is
        // copied; subsequent retained entries each consume the shared budget.
        let mut inputs = Self {
            atoms: Vec::new(),
            clauses: Vec::new(),
        };
        for &root in authored {
            attempt.tick(executor)?;
            let children = match executor.ctx.terms.get(root) {
                TermData::App(Symbol::Named(name), children)
                    if name == "or"
                        && children.len() == 2
                        && executor.ctx.terms.sort(root) == &Sort::Bool =>
                {
                    [children[0], children[1]]
                }
                _ => continue,
            };
            charge(&mut attempt.work, 2)?;
            let Some(left) = literal(&executor.ctx.terms, children[0]) else {
                continue;
            };
            let Some(right) = literal(&executor.ctx.terms, children[1]) else {
                continue;
            };
            // Duplicate and tautological clauses need no special normalization
            // rule in this slice. Skip them BEFORE adding either atom.
            if left.0 == right.0 {
                continue;
            }
            let mut keys = [Literal {
                atom: 0,
                positive: true,
            }; 2];
            for (slot, (atom, positive)) in [left, right].into_iter().enumerate() {
                attempt.tick(executor)?;
                let index = match atom_index(&inputs.atoms, atom, attempt)? {
                    Some(index) => index,
                    None => {
                        spend(&mut attempt.work)?;
                        let index = inputs.atoms.len();
                        inputs.atoms.push(atom);
                        index
                    }
                };
                keys[slot] = Literal {
                    atom: index,
                    positive,
                };
            }
            spend(&mut attempt.work)?;
            inputs.clauses.push(InputClause {
                root,
                children,
                literals: keys,
            });
        }
        Some(inputs)
    }
}

struct Evidence {
    literals: Vec<Literal>,
    step: ProofId,
}

struct Closure {
    atoms: Vec<TermId>,
    clauses: Vec<Evidence>,
    // Indexed by 2 * atom + polarity; insertion and traversal are metered.
    postings: Vec<Vec<usize>>,
}

impl Closure {
    fn new(atoms: &[TermId], attempt: &mut Attempt) -> Option<Self> {
        if atoms.len() > MAX_ROOTS.checked_mul(2)? {
            return None;
        }
        charge(&mut attempt.work, atoms.len().checked_mul(3)?)?;
        let slots = atoms.len().checked_mul(2)?;
        Some(Self {
            atoms: atoms.to_vec(),
            clauses: Vec::new(),
            postings: (0..slots).map(|_| Vec::new()).collect(),
        })
    }

    fn posting(literal: Literal) -> usize {
        2 * literal.atom + usize::from(literal.positive)
    }

    fn insert(
        &mut self,
        mut literals: Vec<Literal>,
        step: ProofId,
        attempt: &mut Attempt,
    ) -> Option<()> {
        // All vectors here have at most two entries. The original Or step
        // retains its exact children; only this internal lookup key is sorted.
        charge(&mut attempt.work, literals.len().checked_add(1)?)?;
        if literals.len() > 2 {
            return None;
        }
        literals.sort_unstable();
        for existing in &self.clauses {
            charge(&mut attempt.work, 3)?;
            if existing.literals == literals {
                return Some(());
            }
        }
        for &literal in &literals {
            spend(&mut attempt.work)?;
            self.postings
                .get_mut(Self::posting(literal))?
                .push(self.clauses.len());
        }
        spend(&mut attempt.work)?;
        self.clauses.push(Evidence { literals, step });
        Some(())
    }

    fn terms(
        &self,
        executor: &mut Executor,
        literals: &[Literal],
        attempt: &mut Attempt,
    ) -> Option<Vec<TermId>> {
        let mut terms = Vec::new();
        for &literal in literals {
            attempt.tick(executor)?;
            let atom = *self.atoms.get(literal.atom)?;
            terms.push(if literal.positive {
                atom
            } else {
                executor.ctx.terms.mk_not_raw(atom)
            });
        }
        Some(terms)
    }

    fn resolve(
        &self,
        left: usize,
        right: usize,
        pivot: Literal,
        attempt: &mut Attempt,
    ) -> Option<Option<Vec<Literal>>> {
        let mut result: Vec<Literal> = Vec::new();
        for (clause, removed) in [(left, pivot), (right, pivot.opposite())] {
            for &literal in &self.clauses.get(clause)?.literals {
                spend(&mut attempt.work)?;
                if literal == removed {
                    continue;
                }
                let mut duplicate = false;
                for &previous in &result {
                    spend(&mut attempt.work)?;
                    if previous == literal.opposite() {
                        return Some(None);
                    }
                    duplicate |= previous == literal;
                }
                if !duplicate {
                    spend(&mut attempt.work)?;
                    result.push(literal);
                }
            }
        }
        Some(Some(result))
    }

    fn close(
        &mut self,
        executor: &mut Executor,
        proof: &mut Proof,
        attempt: &mut Attempt,
    ) -> Option<bool> {
        let mut cursor = 0;
        while cursor < self.clauses.len() {
            attempt.tick(executor)?;
            charge(&mut attempt.work, self.clauses[cursor].literals.len())?;
            let current = self.clauses[cursor].literals.clone();
            for pivot in current {
                attempt.tick(executor)?;
                let posting = Self::posting(pivot.opposite());
                let count = self.postings.get(posting)?.len();
                for offset in 0..count {
                    attempt.tick(executor)?;
                    let other = self.postings[posting][offset];
                    // Each unordered clause pair/pivot is visited from its
                    // later insertion. Appended clauses get their own turn.
                    if other >= cursor {
                        continue;
                    }
                    let Some(literals) = self.resolve(cursor, other, pivot, attempt)? else {
                        continue;
                    };
                    let terms = self.terms(executor, &literals, attempt)?;
                    attempt.tick(executor)?;
                    let id = proof.add_resolution(
                        terms,
                        self.atoms[pivot.atom],
                        self.clauses[cursor].step,
                        self.clauses[other].step,
                    );
                    if literals.is_empty() {
                        return Some(true);
                    }
                    self.insert(literals, id, attempt)?;
                }
            }
            cursor += 1;
        }
        Some(false)
    }
}

impl Executor {
    pub(super) fn try_authored_binary_predicates(
        &mut self,
        proof: &mut Proof,
        authored: &[TermId],
        equalities: &[(TermId, TermId, TermId)],
        nans: &[NanPremise],
        attempt: &mut Attempt,
    ) -> Outcome {
        let Some(inputs) = Inputs::collect(self, authored, attempt) else {
            return declined(self);
        };
        // Only atoms in supported OR roots participate. In the 65-application
        // fixture the 63 unrelated positive units never enter this pair scan
        // or the resolution pool. All unsuccessful inspections still debit.
        for (index, &left) in inputs.atoms.iter().enumerate() {
            for &right in inputs.atoms.iter().skip(index + 1) {
                if attempt.tick(self).is_none() {
                    return declined(self);
                }
                let compatible = match (self.ctx.terms.get(left), self.ctx.terms.get(right)) {
                    (TermData::App(Symbol::Named(a), x), TermData::App(Symbol::Named(b), y)) => {
                        a.len() <= MAX_IDENTITY_BYTES
                            && b.len() <= MAX_IDENTITY_BYTES
                            && a == b
                            && !x.is_empty()
                            && x.len() <= MAX_ARITY
                            && x.len() == y.len()
                    }
                    _ => false,
                };
                if !compatible {
                    continue;
                }
                let negative = self.ctx.terms.mk_not_raw(right);
                let Some(pair) = self.authored_predicate_pair(
                    left,
                    negative,
                    right,
                    equalities,
                    nans,
                    &mut attempt.work,
                ) else {
                    if attempt.work == 0 {
                        return declined(self);
                    }
                    continue;
                };
                let candidate =
                    match self.binary_predicate_candidate(&inputs, &pair, authored, attempt) {
                        Some(Some(candidate)) => candidate,
                        Some(None) => continue,
                        None => return declined(self),
                    };
                let outcome =
                    self.commit_predicate_candidate(proof, candidate, authored, &pair, attempt);
                if outcome != Outcome::Declined {
                    return outcome;
                }
                if attempt.work == 0 || attempt.checks == MAX_COMMIT_ATTEMPTS {
                    return declined(self);
                }
            }
        }
        declined(self)
    }

    fn binary_predicate_candidate(
        &mut self,
        inputs: &Inputs,
        pair: &Pair,
        authored: &[TermId],
        attempt: &mut Attempt,
    ) -> Option<Option<Proof>> {
        let mut proof = Proof::new();
        let mut closure = Closure::new(&inputs.atoms, attempt)?;
        for input in &inputs.clauses {
            attempt.tick(self)?;
            charge(&mut attempt.work, 4)?;
            let root = proof.add_assume(input.root, None);
            let id = proof.add_rule_step(
                AletheRule::Or,
                input.children.to_vec(),
                vec![root],
                Vec::new(),
            );
            closure.insert(input.literals.to_vec(), id, attempt)?;
        }
        for &root in authored {
            attempt.tick(self)?;
            let Some((atom, positive)) = literal(&self.ctx.terms, root) else {
                continue;
            };
            let Some(atom) = atom_index(&inputs.atoms, atom, attempt)? else {
                continue;
            };
            spend(&mut attempt.work)?;
            let id = proof.add_assume(root, None);
            closure.insert(vec![Literal { atom, positive }], id, attempt)?;
        }
        for (left, right) in [
            (pair.positive, pair.negative_atom),
            (pair.negative_atom, pair.positive),
        ] {
            attempt.tick(self)?;
            let (_, id) =
                self.emit_predicate_implication(pair, left, right, &mut proof, &mut attempt.work)?;
            let left = atom_index(&inputs.atoms, left, attempt)??;
            let right = atom_index(&inputs.atoms, right, attempt)??;
            closure.insert(
                vec![
                    Literal {
                        atom: left,
                        positive: false,
                    },
                    Literal {
                        atom: right,
                        positive: true,
                    },
                ],
                id,
                attempt,
            )?;
        }
        if closure.close(self, &mut proof, attempt)? {
            Some(Some(proof))
        } else {
            Some(None)
        }
    }
}

#[cfg(test)]
#[path = "boolean_clauses/tests.rs"]
mod tests;
