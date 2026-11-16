// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A lemma's own variable definitions, used as substitutions.
//!
//! A clause `(cl .. (not (= v t)) ..)` — or `(cl (not (and .. (= v t) ..)))`,
//! the same disjunction — whose hypothesis equates a free bit-vector variable
//! `v` with a term `t` is valid exactly when the clause with every other
//! occurrence of `v` read as `t` is valid. An assignment that falsifies the
//! hypothesis satisfies the clause through it; under any other, `v` and `t`
//! have one value, so reading an occurrence of `v` as `t` changes nothing.
//! (That holds occurrence by occurrence and substitution by substitution, so
//! it stays sound when some occurrences were lowered before the substitution,
//! or when a later `t` mentions an earlier `v`.)
//!
//! The lowering therefore memoizes each such `v` as `t`'s lowering before the
//! clause is lowered. Two circuits that were equal only BECAUSE `v = t` become
//! one circuit, which the bit-blaster's structural sharing merges outright.
//! Measured 2026-09-30 on external-codegen's `LDP` row: `(= ldp_base seed_base)`
//! guards sixty-four byte selections comparing `(bvadd (bvadd 3 4) ldp_base)`
//! with `(bvadd 7 seed_base)`, and the monolithic refutation of the unshared
//! adders exceeded the 4,000,000 resolution hints the checker replays, while
//! the sweep ran out of conflicts merging circuits that are equal only under
//! the hypothesis.
//!
//! A definition is a leaf, or a well-typed zero extension of one leaf. The
//! latter is bounded wiring rather than an arbitrary compound expression.
//! Its actual copies and census walks retain the existing lowering charges;
//! no construction or replay allowance is added. Only an
//! array-free clause is read this way: admitting more array lemmas lets a
//! strict but hole-printing array repair preempt a complete proof in the
//! printer's presentation cascade (`bv_blast_solver/sweep.rs` scopes the
//! checker's sweep the same way).
//!
//! The same entry point installs a case of `case_split.rs`: its variable read
//! as its literal (a binding like the ones above), or its condition read as
//! `false`. Every binding's definition is declared to the lowering census
//! (`lowering_share.rs`) with the clause, before anything is lowered.

use super::case_split::Case;
use super::lowering_share::Request;
use super::*;

/// Source nodes walked looking for hypotheses.
const MAX_VISITS: usize = 4_096;

/// What one lowering of a clause may read besides the clause itself.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Reading<'c> {
    /// Read the clause's own bounded leaf-wiring hypotheses as substitutions.
    pub(super) hypotheses: bool,
    /// Read the clause under this case of a split.
    pub(super) case: Option<&'c Case>,
}

/// Equations necessarily true under a counterexample to this clause.
/// Every literal must be false. Only connectives whose selected polarity
/// determines ALL selected children are followed; a branch grants nothing.
/// Thus a nested implication and a negated conjunction have the same premise
/// authority, without inventing or assuming any equation outside the clause.
fn hypothesis_equalities(terms: &TermStore, clause: &[TermId]) -> Vec<(TermId, TermId)> {
    let mut out = Vec::new();
    let mut visits = 0_usize;
    for &literal in clause {
        if visits >= MAX_VISITS {
            return out;
        }
        let mut stack = vec![(literal, false)];
        while let Some((term, truth)) = stack.pop() {
            visits += 1;
            if visits > MAX_VISITS {
                return out;
            }
            if terms.entry_stamp(term).is_none() || terms.sort(term) != &Sort::Bool {
                continue;
            }
            // Bound pending edges BEFORE allocating them as well as bounding
            // visited nodes. A prefix of necessary premises stays sound.
            let room = MAX_VISITS
                .saturating_sub(visits)
                .saturating_sub(stack.len());
            match terms.get(term) {
                TermData::Not(inner) if room > 0 => stack.push((*inner, !truth)),
                TermData::App(Symbol::Named(name), args)
                    if (name == "and" && truth) || (name == "or" && !truth) =>
                {
                    stack.extend(args.iter().take(room).rev().map(|&child| (child, truth)));
                }
                TermData::App(Symbol::Named(name), args)
                    if name == "not" && args.len() == 1 && room > 0 =>
                {
                    stack.push((args[0], !truth));
                }
                TermData::App(Symbol::Named(name), args)
                    if name == "=>" && !truth && args.len() >= 2 =>
                {
                    // SMT-LIB implication associates to the right. Falsity
                    // requires every antecedent true and the last term false.
                    let last = args.len() - 1;
                    stack.extend(
                        args.iter()
                            .enumerate()
                            .take(room)
                            .rev()
                            .map(|(index, &child)| (child, index != last)),
                    );
                }
                TermData::App(Symbol::Named(name), args) if name == "=" && truth => {
                    if let [left, right] = args.as_slice() {
                        if let Some(pair) = definition(terms, *left, *right) {
                            out.push(pair);
                        }
                    }
                }
                _ => {}
            }
        }
    }
    out
}

/// `(v, t)` when one side of `(= left right)` is a free bit-vector variable
/// and the other bounded, well-typed leaf wiring.
fn definition(terms: &TermStore, left: TermId, right: TermId) -> Option<(TermId, TermId)> {
    if left == right
        || terms.entry_stamp(left).is_none()
        || terms.entry_stamp(right).is_none()
        || terms.sort(left) != terms.sort(right)
    {
        return None;
    }
    let width = word_width(terms, left)?;
    let is_var = |term: TermId| matches!(terms.get(term), TermData::Var(..));
    if is_var(left) && leaf_wiring(terms, right, width) {
        Some((left, right))
    } else if is_var(right) && leaf_wiring(terms, left, width) {
        Some((right, left))
    } else {
        None
    }
}

fn word_width(terms: &TermStore, term: TermId) -> Option<u32> {
    terms.entry_stamp(term)?;
    let Sort::BitVec(word) = terms.sort(term) else {
        return None;
    };
    (1..=MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH)
        .contains(&word.width)
        .then_some(word.width)
}

fn word_leaf(terms: &TermStore, term: TermId, width: u32) -> bool {
    if word_width(terms, term) != Some(width) {
        return false;
    }
    match terms.get(term) {
        TermData::Var(..) => true,
        TermData::Const(Constant::BitVec {
            value,
            width: declared,
        }) => *declared == width && value.to_u128().is_some() && value.bits() <= u64::from(width),
        _ => false,
    }
}

fn leaf_wiring(terms: &TermStore, term: TermId, width: u32) -> bool {
    if word_leaf(terms, term, width) {
        return true;
    }
    let TermData::App(Symbol::Indexed(name, indices), args) = terms.get(term) else {
        return false;
    };
    let ([extra], [inner]) = (indices.as_slice(), args.as_slice()) else {
        return false;
    };
    let Some(inner_width) = word_width(terms, *inner) else {
        return false;
    };
    name == "zero_extend"
        && inner.index() < term.index()
        && inner_width.checked_add(*extra) == Some(width)
        && word_leaf(terms, *inner, inner_width)
}

impl ProofProducingLowerer<'_, '_> {
    /// Lower every literal of `clause` as `reading` says (see the module
    /// documentation).
    pub(super) fn lower_clause_read(
        &mut self,
        clause: &[TermId],
        reading: Reading<'_>,
    ) -> Result<Vec<BvExpr>, String> {
        let (mut bindings, refuted) = match reading.case {
            Some(case) => match case.binding() {
                Ok(binding) => (vec![binding], None),
                Err(condition) => (Vec::new(), Some(condition)),
            },
            None => (Vec::new(), None),
        };
        if reading.hypotheses {
            for (variable, value) in hypothesis_equalities(self.terms, clause) {
                if !bindings.iter().any(|&(bound, _)| bound == variable) {
                    bindings.push((variable, value));
                }
            }
        }
        if bindings.is_empty() && refuted.is_none() {
            return self.lower_bool_terms(clause);
        }
        // A refuted condition is answered from the memo entry installed
        // below, so it requests nothing; each definition is one top-level
        // request, made before the clause's.
        if let Some(condition) = refuted {
            self.census_opaque.insert(condition);
        }
        self.census_requests(
            bindings
                .iter()
                .map(|&(_, value)| Request::Lower(value))
                .chain(clause.iter().map(|&literal| Request::Lower(literal))),
        )?;
        if let Some(condition) = refuted {
            self.memo_node_counts.insert(condition, 1);
            self.memo
                .insert(condition, ProofProducingExpr::Bool(BvExpr::const_val(0, 1)));
        }
        for (variable, value) in bindings {
            self.read_as(variable, value)?;
        }
        let mut lowered = Vec::with_capacity(clause.len());
        for &literal in clause {
            lowered.push(self.lower_bool(literal)?);
        }
        Ok(lowered)
    }

    /// Lower every occurrence of `variable` as `value`'s lowering, and let
    /// closed evaluation read it as `value` when that is closed.
    fn read_as(&mut self, variable: TermId, value: TermId) -> Result<(), String> {
        let lowered = self.lower(value)?;
        let nodes = self.count_proof_nodes(&lowered)?;
        self.charge_constructed_expr_nodes(nodes)?;
        self.memo_node_counts.insert(variable, nodes);
        self.memo.insert(variable, lowered);
        if let (Some(constant), Sort::BitVec(sort)) = (
            bounded_eval::closed_bv_in(self.terms, value, &self.constants),
            self.terms.sort(variable),
        ) {
            self.constants.push((
                variable,
                EvalValue::BitVec {
                    value: constant,
                    width: sort.width,
                },
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bv(terms: &mut TermStore, name: &str) -> TermId {
        terms.mk_var(name.to_string(), Sort::bitvec(8))
    }

    #[test]
    fn a_negated_conjunction_yields_its_leaf_definitions_in_order() {
        let mut terms = TermStore::new();
        let (a, b, c) = (
            bv(&mut terms, "a"),
            bv(&mut terms, "b"),
            bv(&mut terms, "c"),
        );
        let seven = terms.mk_bitvec(num_bigint::BigInt::from(7), 8);
        let sum = terms.mk_app(Symbol::named("bvadd"), [b, seven], Sort::bitvec(8));
        let first = terms.mk_app(Symbol::named("="), [a, b], Sort::Bool);
        let second = terms.mk_app(Symbol::named("="), [seven, c], Sort::Bool);
        // A compound definition is not a substitution: it would be copied.
        let third = terms.mk_app(Symbol::named("="), [a, sum], Sort::Bool);
        let goal = terms.mk_app(Symbol::named("="), [a, c], Sort::Bool);
        let not_goal = terms.mk_not_raw(goal);
        let conjunction = terms.mk_app(
            Symbol::named("and"),
            [first, second, third, not_goal],
            Sort::Bool,
        );
        let clause = [terms.mk_not_raw(conjunction)];
        assert_eq!(
            hypothesis_equalities(&terms, &clause),
            vec![(a, b), (c, seven)]
        );
    }

    #[test]
    fn a_positive_equality_is_not_a_hypothesis() {
        let mut terms = TermStore::new();
        let (a, b) = (bv(&mut terms, "a"), bv(&mut terms, "b"));
        let equality = terms.mk_app(Symbol::named("="), [a, b], Sort::Bool);
        assert_eq!(hypothesis_equalities(&terms, &[equality]), []);
        let negated = terms.mk_not_raw(equality);
        assert_eq!(hypothesis_equalities(&terms, &[negated]), vec![(a, b)]);
    }
}

#[cfg(test)]
#[path = "hypotheses_wiring_tests.rs"]
mod wiring_tests;
