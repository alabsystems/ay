// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact conditional identities under the complete original conjunction.

use super::*;
use std::collections::BTreeSet;

mod validate;

pub(crate) struct ContextIdentity {
    pub(crate) root: TermId,
    pub(crate) equality: TermId,
    pub(crate) negated_equality: TermId,
    pub(crate) left: TermId,
    pub(crate) right: TermId,
    pub(crate) width: u32,
}

struct Reducer<'a> {
    terms: &'a TermStore,
    width: u32,
    mask: u128,
    nodes: usize,
    facts: BTreeSet<TermId>,
}

#[derive(PartialEq, Eq)]
enum Word {
    Literal(u128),
    Atom(TermId),
    Add(Box<Word>, Box<Word>),
}

pub(crate) fn context_identity(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Option<ContextIdentity>, ProofCheckError> {
    let [negated] = clause else {
        return Ok(None);
    };
    if terms.entry_stamp(*negated).is_none() {
        return Ok(None);
    }
    let TermData::Not(root) = terms.get(*negated) else {
        return Ok(None);
    };
    if terms.entry_stamp(*root).is_none() {
        return Ok(None);
    }
    let TermData::App(Symbol::Named(op), args) = terms.get(*root) else {
        return Ok(None);
    };
    if op != "and" || args.len() != 2 || terms.sort(*negated) != &Sort::Bool {
        return Ok(None);
    }
    if !progress(MAX_WORK, MAX_ALLOCATION) {
        return Err(ProofCheckError::ResourceLimit);
    }
    let result = (|| {
        let mut stack = vec![(*root, 0usize)];
        let mut facts = BTreeSet::new();
        let mut found = None;
        let mut nodes = 0;
        while let Some((term, depth)) = stack.pop() {
            nodes += 1;
            if nodes > MAX_NODES || depth > MAX_DEPTH {
                return None;
            }
            terms.entry_stamp(term)?;
            match terms.get(term) {
                TermData::App(Symbol::Named(op), args) if op == "and" && args.len() == 2 => {
                    facts.insert(term);
                    stack.extend(args.iter().map(|&arg| (arg, depth + 1)));
                }
                TermData::Not(eq) if equality(terms, &[*eq]).is_some() => {
                    if found.is_some() {
                        return None;
                    }
                    found = Some((term, *eq));
                }
                _ => {
                    facts.insert(term);
                }
            }
        }
        let (negated_equality, eq) = found?;
        let (left, right, width) = equality(terms, &[eq])?;
        let mut reducer = Reducer {
            terms,
            width,
            mask: u128::MAX >> (128 - width),
            nodes,
            facts,
        };
        reducer.validate(*root, 0)?;
        if reducer.word(left, 0)? != reducer.word(right, 0)? || reducer.nodes > MAX_NODES {
            return None;
        }
        Some(ContextIdentity {
            root: *root,
            equality: eq,
            negated_equality,
            left,
            right,
            width,
        })
    })();
    Ok(result)
}

impl Reducer<'_> {
    fn visit(&mut self, term: TermId, depth: usize) -> Option<()> {
        self.terms.entry_stamp(term)?;
        self.nodes = self.nodes.checked_add(1)?;
        (self.nodes <= MAX_NODES && depth <= MAX_DEPTH).then_some(())
    }

    fn boolean(&mut self, term: TermId, depth: usize) -> Option<bool> {
        self.visit(term, depth)?;
        if self.facts.contains(&term) {
            return Some(true);
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Bool(value)) => Some(*value),
            TermData::Not(inner) => Some(!self.boolean(*inner, depth + 1)?),
            TermData::App(Symbol::Named(op), args) => {
                let [a, b] = args.as_slice() else {
                    return None;
                };
                match op.as_str() {
                    "and" | "or" => {
                        let a = self.boolean(*a, depth + 1);
                        let b = self.boolean(*b, depth + 1);
                        match (op.as_str(), a, b) {
                            ("and", Some(false), _) | ("and", _, Some(false)) => Some(false),
                            ("and", Some(true), Some(true)) => Some(true),
                            ("or", Some(true), _) | ("or", _, Some(true)) => Some(true),
                            ("or", Some(false), Some(false)) => Some(false),
                            _ => None,
                        }
                    }
                    "=" | "bvule" | "bvuge" | "bvsle" | "bvsge" if a == b => Some(true),
                    "bvult" | "bvugt" | "bvslt" | "bvsgt" if a == b => Some(false),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn word(&mut self, term: TermId, depth: usize) -> Option<Word> {
        self.visit(term, depth)?;
        if let Some((condition, yes, no)) = context_conditional(self.terms, term) {
            let chosen = if yes == no {
                yes
            } else {
                match self.boolean(condition, depth + 1) {
                    Some(true) => yes,
                    Some(false) => no,
                    None => return Some(Word::Atom(term)),
                }
            };
            return self.word(chosen, depth + 1);
        }
        match self.terms.get(term) {
            TermData::Const(Constant::BitVec { value, .. }) => {
                Some(Word::Literal(value.to_u128()?))
            }
            TermData::App(Symbol::Named(op), args) if op == "bvadd" => {
                let [a, b] = args.as_slice() else {
                    return None;
                };
                let a = self.word(*a, depth + 1)?;
                let b = self.word(*b, depth + 1)?;
                match (a, b) {
                    (Word::Literal(0), b) => Some(b),
                    (a, Word::Literal(0)) => Some(a),
                    (Word::Literal(a), Word::Literal(b)) => {
                        Some(Word::Literal(a.wrapping_add(b) & self.mask))
                    }
                    (a, b) => Some(Word::Add(Box::new(a), Box::new(b))),
                }
            }
            _ => Some(Word::Atom(term)),
        }
    }
}

// Raw source applications and dedicated ITE nodes have identical typed
// semantics after validation; callers may supply either representation.
pub(crate) fn context_conditional(
    terms: &TermStore,
    term: TermId,
) -> Option<(TermId, TermId, TermId)> {
    match terms.get(term) {
        TermData::Ite(c, y, n) => Some((*c, *y, *n)),
        TermData::App(Symbol::Named(op), args) if op == "ite" => {
            let [c, y, n] = args.as_slice() else {
                return None;
            };
            Some((*c, *y, *n))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests;

// Partition checking validates the complete original Boolean/BV tree before
// selecting any intervals or simplifying any affine endpoint.
pub(super) fn validate_source(terms: &TermStore, root: TermId, width: u32) -> Option<()> {
    if !(1..=128).contains(&width) {
        return None;
    }
    let mut reducer = Reducer {
        terms,
        width,
        mask: u128::MAX >> (128 - width),
        nodes: 0,
        facts: BTreeSet::new(),
    };
    reducer.validate(root, 0)
}
