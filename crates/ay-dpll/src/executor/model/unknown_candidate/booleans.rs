// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reading a candidate's Boolean constants the way `(get-model)` prints them,
//! a three-valued evaluation of assertions over a candidate, and the pass that
//! leaves unneeded Boolean constants false.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::Constant;
use ay_core::{Sort, TermData, TermId};

use crate::executor::{Executor, EXECUTOR_STACK_RED_ZONE, EXECUTOR_STACK_SIZE};

use super::super::{EvalValue, Model};

/// Upper bound on root evaluations spent by
/// [`Executor::prefer_false_booleans`] on one candidate.
const PREFER_FALSE_EVALUATION_BUDGET: usize = 4096;

/// How [`Executor::ground_truth`] reads an atom that is not a Boolean
/// constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum AtomReading {
    /// Every such atom is unknown: only the Boolean constants, which come
    /// straight from the SAT assignment, decide the value.
    Skeleton,
    /// The search's own assignment decides each atom (a quantified subformula
    /// included) that has a SAT variable, and the model evaluator each other
    /// atom it can.
    Assigned,
}

/// A connective [`Executor::ground_truth`] evaluates from its operands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Connective {
    Not,
    And,
    Or,
    Implies,
    Iff,
    /// A Boolean `ite`: operands condition, then, else.
    Ite,
}

impl Connective {
    /// The strong Kleene value of the connective over its operands' values:
    /// a false conjunct makes a conjunction false whatever its unknown
    /// conjuncts are.
    fn value(self, operands: &[Option<bool>]) -> Option<bool> {
        match (self, operands) {
            (Self::Not, [inner]) => inner.map(|b| !b),
            (Self::And, _) => {
                if operands.contains(&Some(false)) {
                    Some(false)
                } else {
                    operands.iter().all(Option::is_some).then_some(true)
                }
            }
            (Self::Or, _) => {
                if operands.contains(&Some(true)) {
                    Some(true)
                } else {
                    operands.iter().all(Option::is_some).then_some(false)
                }
            }
            (Self::Implies, [premise, conclusion]) => match (premise, conclusion) {
                (Some(false), _) | (_, Some(true)) => Some(true),
                (Some(true), Some(false)) => Some(false),
                _ => None,
            },
            (Self::Iff, [left, right]) => Some((*left)? == (*right)?),
            (Self::Ite, [cond, then_value, else_value]) => match cond {
                Some(true) => *then_value,
                Some(false) => *else_value,
                None => then_value.filter(|_| then_value == else_value),
            },
            _ => None,
        }
    }
}

/// Where the Boolean constants of interest occur in one root.
#[derive(Debug, Default)]
struct Occurrences {
    /// Reached from the root through connectives only, so a new value for the
    /// constant reaches the root's value through [`Executor::ground_truth`].
    propositional: Vec<TermId>,
    /// Inside a quantified subformula or an atom, whose value under
    /// [`AtomReading::Assigned`] is the search's and would not follow a new
    /// value for the constant.
    opaque: Vec<TermId>,
}

impl Executor {
    /// `candidate` with each Boolean constant it sets true, but that no root
    /// needs true, set to false.
    ///
    /// z3 leaves a Boolean false unless its search needed it true; ay's search
    /// may leave an unneeded one true, and on Verus queries it leaves every
    /// `%%location_label%%` true. Clients read Boolean markers from the
    /// candidate (AIR takes the first true `%%location_label%%` as the
    /// assertion that failed), so an unneeded `true` names an assertion that
    /// did not fail.
    ///
    /// Need is judged on the search's own assignment
    /// ([`AtomReading::Assigned`]). A constant is set false when every root
    /// that mentions it either keeps its value whatever the constant is (read
    /// with the constant, and every atom the assignment leaves unknown,
    /// unknown), or is true before and after. A guard `L` of `(=> L P)` is so
    /// set false when the search made `P` true, and kept when `P` is false or
    /// unknown there: `L` is then what the search used to violate the root.
    /// A constant is kept as the search left it when
    ///
    /// * it occurs inside a quantified subformula or an atom of a root, whose
    ///   value the evaluation reads from the search and would not change with
    ///   it: a guard under a `forall` may be the only witness of the negated
    ///   quantifier;
    /// * its SAT variable is shared with another term.
    ///
    /// A constant is also kept when setting it false makes a root false with
    /// every atom read as unknown ([`AtomReading::Skeleton`]). The published
    /// candidate therefore keeps the property [`Self::publishable_candidate`]
    /// demands of it, that its Boolean constants falsify no assertion, even
    /// where the assignment and the evaluator disagree about the atoms (a
    /// rejected candidate can read a Verus root false under them, and every
    /// guard in it then looks unneeded).
    ///
    /// So no root the search made true is made false or unknown, and a Verus
    /// query root, whose Boolean constants falsify it once no label is true,
    /// keeps a true label: the label of the assertion the search violated
    /// where the assignment shows it, and in any case the last true one.
    /// Constants are tried latest declared first, so when several could each
    /// carry a violation the earliest declared one stays true.
    pub(super) fn prefer_false_booleans(&self, candidate: &Model, roots: &[TermId]) -> Model {
        let mut model = candidate.clone();
        let mut constants: Vec<TermId> = self
            .ctx
            .symbol_iter()
            .filter(|(name, info)| {
                info.arg_sorts.is_empty()
                    && info.sort == Sort::Bool
                    && !self.ctx.is_internal_symbol(name)
                    && !self.ctx.is_defined_fun(name)
            })
            .filter_map(|(_, info)| info.term)
            .filter(|&term| self.printed_bool(&model, term) == Some(true))
            .collect();
        if constants.is_empty() {
            return model;
        }
        constants.sort_unstable_by(|a, b| b.cmp(a));
        constants.dedup();

        // A SAT variable shared with another term cannot be flipped alone.
        let mut terms_per_var: HashMap<u32, usize> = HashMap::default();
        for &var in model.term_to_var.values() {
            *terms_per_var.entry(var).or_default() += 1;
        }

        let wanted: HashSet<TermId> = constants.iter().copied().collect();
        let mut mentions: HashMap<TermId, Vec<TermId>> = HashMap::default();
        let mut pinned: HashSet<TermId> = HashSet::default();
        for &root in roots {
            let occurrences = self.constant_occurrences(root, &wanted);
            pinned.extend(occurrences.opaque);
            for constant in occurrences.propositional {
                mentions.entry(constant).or_default().push(root);
            }
        }

        let mut budget = PREFER_FALSE_EVALUATION_BUDGET;
        for constant in constants {
            if pinned.contains(&constant) {
                continue;
            }
            let Some(&var) = model.term_to_var.get(&constant) else {
                continue;
            };
            if terms_per_var.get(&var) != Some(&1) {
                continue;
            }
            let affected = mentions.get(&constant).map_or(&[][..], Vec::as_slice);
            if 4 * affected.len() > budget || self.poll_evaluation_stop().is_err() {
                break;
            }
            budget -= 4 * affected.len();
            let mut dependence_memo = HashMap::default();
            let mut before_memo = HashMap::default();
            let dependent: Vec<TermId> = affected
                .iter()
                .copied()
                .filter(|&root| {
                    self.depends_on_constant(&model, root, constant, &mut dependence_memo)
                        .1
                })
                .collect();
            if !dependent.iter().all(|&root| {
                self.ground_truth(&model, root, AtomReading::Assigned, &mut before_memo)
                    == Some(true)
            }) {
                continue;
            }
            set_bool_constant(&mut model, constant, var, false);
            let mut after_memo = HashMap::default();
            let mut skeleton_memo = HashMap::default();
            let keeps = dependent.iter().all(|&root| {
                self.ground_truth(&model, root, AtomReading::Assigned, &mut after_memo)
                    == Some(true)
            }) && affected.iter().all(|&root| {
                self.ground_truth(&model, root, AtomReading::Skeleton, &mut skeleton_memo)
                    != Some(false)
            });
            if !keeps {
                set_bool_constant(&mut model, constant, var, true);
            }
        }
        model
    }

    /// The truth value of the Boolean `term` under `model`, with other atoms
    /// read as `reading` says and connectives evaluated by
    /// [`Connective::value`].
    pub(super) fn ground_truth(
        &self,
        model: &Model,
        term: TermId,
        reading: AtomReading,
        memo: &mut HashMap<TermId, Option<bool>>,
    ) -> Option<bool> {
        if let Some(&value) = memo.get(&term) {
            return value;
        }
        let value = stacker::maybe_grow(EXECUTOR_STACK_RED_ZONE, EXECUTOR_STACK_SIZE, || {
            if let Some((connective, operands)) = self.connective(term) {
                let values: Vec<Option<bool>> = operands
                    .iter()
                    .map(|&operand| self.ground_truth(model, operand, reading, memo))
                    .collect();
                return connective.value(&values);
            }
            self.ground_leaf(model, term, reading)
        });
        memo.insert(term, value);
        value
    }

    /// `term`'s value under [`AtomReading::Assigned`] with `constant` read as
    /// unknown, and whether `term`'s value can change with `constant` for some
    /// value of the atoms that reading leaves unknown.
    ///
    /// A connective whose value is known with `constant` unknown has that
    /// value whatever `constant` and the unknown atoms are (strong Kleene
    /// logic is monotone), so it does not depend on `constant`; one whose
    /// value is unknown depends on it when an operand does.
    fn depends_on_constant(
        &self,
        model: &Model,
        term: TermId,
        constant: TermId,
        memo: &mut HashMap<TermId, (Option<bool>, bool)>,
    ) -> (Option<bool>, bool) {
        if term == constant {
            return (None, true);
        }
        if let Some(&known) = memo.get(&term) {
            return known;
        }
        let result = stacker::maybe_grow(EXECUTOR_STACK_RED_ZONE, EXECUTOR_STACK_SIZE, || {
            let Some((connective, operands)) = self.connective(term) else {
                return (self.ground_leaf(model, term, AtomReading::Assigned), false);
            };
            let mut values = Vec::with_capacity(operands.len());
            let mut dependent = false;
            for operand in operands {
                let (value, operand_dependent) =
                    self.depends_on_constant(model, operand, constant, memo);
                values.push(value);
                dependent |= operand_dependent;
            }
            let value = connective.value(&values);
            (value, value.is_none() && dependent)
        });
        memo.insert(term, result);
        result
    }

    /// The connective [`Self::ground_truth`] evaluates `term` by, with its
    /// operands, or `None` when it reads `term` as a leaf.
    fn connective(&self, term: TermId) -> Option<(Connective, Vec<TermId>)> {
        match self.ctx.terms.get(term) {
            TermData::Not(inner) => Some((Connective::Not, vec![*inner])),
            TermData::Ite(cond, then_term, else_term)
                if *self.ctx.terms.sort(term) == Sort::Bool =>
            {
                Some((Connective::Ite, vec![*cond, *then_term, *else_term]))
            }
            TermData::App(symbol, args) => match (symbol.name(), args.as_slice()) {
                ("and", _) => Some((Connective::And, args.clone())),
                ("or", _) => Some((Connective::Or, args.clone())),
                ("=>", [_, _]) => Some((Connective::Implies, args.clone())),
                ("=", [left, _]) if *self.ctx.terms.sort(*left) == Sort::Bool => {
                    Some((Connective::Iff, args.clone()))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// The value of `term`, which [`Self::connective`] does not decompose:
    /// a Boolean literal, a Boolean constant as `(get-model)` prints it, a
    /// quantified subformula, or an atom read as `reading` says.
    fn ground_leaf(&self, model: &Model, term: TermId, reading: AtomReading) -> Option<bool> {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::Bool(value)) => Some(*value),
            TermData::Var(..) if *self.ctx.terms.sort(term) == Sort::Bool => {
                self.printed_bool(model, term)
            }
            TermData::Forall(..) | TermData::Exists(..) => match reading {
                AtomReading::Skeleton => None,
                AtomReading::Assigned => {
                    self.term_value(&model.sat_model, &model.term_to_var, term)
                }
            },
            _ => match reading {
                AtomReading::Skeleton => None,
                AtomReading::Assigned => self
                    .term_value(&model.sat_model, &model.term_to_var, term)
                    .or_else(|| match self.evaluate_term(model, term) {
                        EvalValue::Bool(value) => Some(value),
                        _ => None,
                    }),
            },
        }
    }

    /// The value `(get-model)` prints for the Boolean constant `term`, read in
    /// the printer's order: the EUF value, then a recovered value when the SAT
    /// assignment has none, then the SAT assignment, then the evaluator.
    pub(super) fn printed_bool(&self, model: &Model, term: TermId) -> Option<bool> {
        let euf_value = model
            .euf_model
            .as_ref()
            .and_then(|euf| euf.term_values.get(&term));
        match euf_value.map(String::as_str) {
            Some("true") => return Some(true),
            Some("false") => return Some(false),
            _ => {}
        }
        let sat_value = self.term_value(&model.sat_model, &model.term_to_var, term);
        if sat_value.is_none() {
            let recovered = model.bool_overrides.get(&term).copied().or_else(|| {
                model
                    .bv_model
                    .as_ref()
                    .and_then(|bv| bv.bool_overrides.get(&term).copied())
            });
            if recovered.is_some() {
                return recovered;
            }
        }
        sat_value.or_else(|| match self.evaluate_term(model, term) {
            EvalValue::Bool(value) => Some(value),
            _ => None,
        })
    }

    /// Where the members of `wanted` occur in `root`: through
    /// [`Self::connective`]s only, or inside a leaf.
    fn constant_occurrences(&self, root: TermId, wanted: &HashSet<TermId>) -> Occurrences {
        let mut occurrences = Occurrences::default();
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();
        let mut stack = vec![(root, true)];
        while let Some((term, propositional)) = stack.pop() {
            if !seen.insert((term, propositional)) {
                continue;
            }
            if wanted.contains(&term) {
                if propositional {
                    occurrences.propositional.push(term);
                } else {
                    occurrences.opaque.push(term);
                }
                continue;
            }
            match self.connective(term).filter(|_| propositional) {
                Some((_, operands)) => stack.extend(operands.into_iter().map(|t| (t, true))),
                None => stack.extend(
                    self.ctx
                        .terms
                        .children(term)
                        .into_iter()
                        .map(|t| (t, false)),
                ),
            }
        }
        occurrences
    }
}

/// Give the Boolean constant `term` (SAT variable `var`) the value `value` in
/// every place `model` may record it, so the printer and the evaluator agree.
pub(super) fn set_bool_constant(model: &mut Model, term: TermId, var: u32, value: bool) {
    if let Some(slot) = model.sat_model.get_mut(var as usize) {
        *slot = value;
    }
    if let Some(slot) = model.bool_overrides.get_mut(&term) {
        *slot = value;
    }
    if let Some(slot) = model
        .bv_model
        .as_mut()
        .and_then(|bv| bv.bool_overrides.get_mut(&term))
    {
        *slot = value;
    }
    if let Some(slot) = model
        .euf_model
        .as_mut()
        .and_then(|euf| euf.term_values.get_mut(&term))
    {
        if slot == "true" || slot == "false" {
            *slot = value.to_string();
        }
    }
    for slot in [
        model.completed_values.get_mut(&term),
        model.dt_pins.get_mut(&term),
        model
            .certified_total_ufs
            .ground_pins
            .get_mut(&term)
            .map(|pin| &mut pin.value),
    ]
    .into_iter()
    .flatten()
    {
        if matches!(slot, EvalValue::Bool(_)) {
            *slot = EvalValue::Bool(value);
        }
    }
    super::super::eval_memo_clear();
}
