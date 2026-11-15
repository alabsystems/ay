// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Producer-only constant-offset cuts. Every rewrite is recorded as a checked
//! affine equality, then lifted through the unchanged source by congruence.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Constant, Proof, ProofId, Sort, Symbol, TermData, TermId, TermStore};

/// Derive a structurally preserved root whose nested constant additions have
/// their constant outside. `unit` must prove `root`; the returned unit proves
/// the returned root, without assuming that normalized root.
///
/// This is a bounded proof producer, not proof authority. The caller must
/// strictly replay the complete proof and validate its authored assumptions.
/// A refusal can leave a partial derivation in `proof`; discard that candidate.
pub fn derive_bv_offset_normalization(
    terms: &mut TermStore,
    proof: &mut Proof,
    root: TermId,
    unit: ProofId,
) -> Option<(TermId, ProofId)> {
    if terms.sort(root) != &Sort::Bool {
        return None;
    }
    let (normalized, equality) = Builder {
        terms,
        proof,
        memo: DetHashMap::default(),
        visits: 0,
    }
    .rewrite(root, 0)?;
    let Some(equality_unit) = equality else {
        return Some((root, unit));
    };
    let eq = terms.mk_app(Symbol::named("="), [root, normalized], Sort::Bool);
    let not_eq = terms.mk_not_raw(eq);
    let not_root = terms.mk_not_raw(root);
    let implication = proof.add_rule_step(
        AletheRule::EquivPos2,
        vec![not_eq, not_root, normalized],
        vec![],
        vec![],
    );
    let implication =
        proof.add_resolution(vec![not_root, normalized], eq, implication, equality_unit);
    let derived = proof.add_resolution(vec![normalized], root, implication, unit);
    Some((normalized, derived))
}

struct Builder<'a> {
    terms: &'a mut TermStore,
    proof: &'a mut Proof,
    memo: DetHashMap<TermId, (TermId, Option<ProofId>)>,
    visits: usize,
}

impl Builder<'_> {
    fn equality(&mut self, left: TermId, right: TermId) -> TermId {
        self.terms
            .mk_app(Symbol::named("="), [left, right], Sort::Bool)
    }

    fn rewrite(&mut self, term: TermId, depth: usize) -> Option<(TermId, Option<ProofId>)> {
        self.visits = self.visits.checked_add(1)?;
        if depth > 64 || self.visits > 2048 || self.memo.len() >= 512 {
            return None;
        }
        self.terms.entry_stamp(term)?;
        if let Some(&result) = self.memo.get(&term) {
            return Some(result);
        }
        let children = match self.terms.get(term) {
            TermData::App(_, args) if args.len() <= 64 => args.clone(),
            TermData::Not(inner) => vec![*inner],
            TermData::Ite(c, t, e) => vec![*c, *t, *e],
            TermData::Const(_) | TermData::Var(_, _) => Vec::new(),
            _ => return None,
        };
        let mut rewritten = Vec::with_capacity(children.len());
        let mut premises = Vec::new();
        for &child in &children {
            let (next, equality) = self.rewrite(child, depth + 1)?;
            rewritten.push(next);
            premises.extend(equality);
        }
        let rebuilt = if children == rewritten {
            term
        } else {
            match self.terms.get(term).clone() {
                TermData::App(op, _) => {
                    self.terms
                        .mk_app(op, &rewritten, self.terms.sort(term).clone())
                }
                TermData::Not(_) => self.terms.mk_not_raw(rewritten[0]),
                TermData::Ite(..) => {
                    if self.terms.sort(rewritten[0]) != &Sort::Bool
                        || self.terms.sort(rewritten[1]) != self.terms.sort(rewritten[2])
                    {
                        return None;
                    }
                    self.terms
                        .mk_ite_raw(rewritten[0], rewritten[1], rewritten[2])
                }
                _ => return None,
            }
        };
        let congruence = if term == rebuilt {
            None
        } else {
            let eq = self.equality(term, rebuilt);
            Some(
                self.proof
                    .add_rule_step(AletheRule::Cong, vec![eq], premises, vec![]),
            )
        };
        let (normalized, offset) = self.offset(rebuilt)?;
        let equality = match (congruence, offset) {
            (Some(first), Some(second)) => {
                let eq = self.equality(term, normalized);
                Some(self.proof.add_rule_step(
                    AletheRule::Trans,
                    vec![eq],
                    vec![first, second],
                    vec![],
                ))
            }
            (first, second) => first.or(second),
        };
        let result = (normalized, equality);
        self.memo.insert(term, result);
        Some(result)
    }

    fn offset(&mut self, term: TermId) -> Option<(TermId, Option<ProofId>)> {
        let Sort::BitVec(width) = self.terms.sort(term) else {
            return Some((term, None));
        };
        let width = width.width;
        let TermData::App(Symbol::Named(op), args) = self.terms.get(term) else {
            return Some((term, None));
        };
        if op != "bvadd" || args.len() != 2 || !(1..=128).contains(&width) {
            return Some((term, None));
        }
        let (left, right) = (args[0], args[1]);
        let TermData::App(Symbol::Named(inner), operands) = self.terms.get(left) else {
            return Some((term, None));
        };
        if inner != "bvadd" || operands.len() != 2 {
            return Some((term, None));
        }
        let (constant, variable) = match (self.terms.get(operands[0]), self.terms.get(operands[1]))
        {
            (TermData::Const(Constant::BitVec { .. }), _) => (operands[0], operands[1]),
            (_, TermData::Const(Constant::BitVec { .. })) => (operands[1], operands[0]),
            _ => return Some((term, None)),
        };
        if [left, right, constant, variable]
            .iter()
            .any(|&part| self.terms.sort(part) != &Sort::bitvec(width))
        {
            return None;
        }
        let sum = self.terms.mk_app(
            Symbol::named("bvadd"),
            [variable, right],
            Sort::bitvec(width),
        );
        let normalized =
            self.terms
                .mk_app(Symbol::named("bvadd"), [sum, constant], Sort::bitvec(width));
        let eq = self.equality(term, normalized);
        if !crate::recognize_arith_clause_tautology(self.terms, &[eq]) {
            return None;
        }
        let step = self.proof.add_theory_lemma_with_kind(
            "bv",
            vec![eq],
            ay_core::TheoryLemmaKind::ArithClauseTautology,
        );
        Some((normalized, Some(step)))
    }
}
