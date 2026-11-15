// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Positional sequence witness construction (#seq-witness-completion).
//!
//! The QF_SEQLIA route decides a sequence problem through EUF, LIA over
//! `seq.len` terms, and axioms that decompose `seq.replace`, `seq.contains`,
//! `seq.extract`, `seq.nth` and friends into word equations over skolems
//! (`u = x ++ src ++ y`, `(seq.replace u src dst) = x ++ dst ++ y`, ...). Its
//! SAT model therefore fixes, for every sequence term, an equality class and
//! a length, but the sequence theory extracts a concrete value only for a
//! variable equal to a ground term. Phase 3 of completion fills every other
//! variable on its own, as its pinned length of default elements. That
//! ignores concatenation: `r = (seq.replace u src dst)` with `u = [0,0]`,
//! `src = [0]` and `r = [0,0,0]` cannot hold, so on its own a satisfiable
//! problem ends `unknown`.
//!
//! This is the sequence analogue of a strings solver's normal-form model
//! construction, done positionally. Every class with a known length `L` owns
//! `L` cells. A committed `c = a1 ++ ... ++ ak` identifies each cell of `c`
//! with the matching cell of some `ai`; `(seq.extract s i n)` and `(seq.at s
//! i)` identify their cells with a window of `s`; `(seq.unit e)` and
//! `(seq.nth s k)` bind a cell to the model value of `e` or of the read; a
//! term the model already values binds all of its cells. Cells no constraint
//! binds get fresh, pairwise-distinct elements, so an unconstrained leaf does
//! not accidentally contain, equal or occur inside another one. A cell of a
//! `(seq.unit e)` whose `e` has no value yet belongs to whatever value a later
//! phase gives `e`, so no class that shares that cell is emitted.
//!
//! SOUNDNESS. Only the outer SAT model is read, never a sub-solve. Two
//! different values forced onto one cell, or a length the positional
//! semantics contradicts, abandon the whole construction. The result is a
//! candidate only (see "ADOPTION"); the strict oracles and the independent
//! gate re-check every original assertion, so a wrong construction degrades
//! to `unknown`, never to a wrong `sat`.
//!
//! ADOPTION. The candidate is computed before Phase 3 (it must not read the
//! per-carrier values Phase 3 writes), and Phase 3 and the later phases then
//! run exactly as before. At the end of completion the per-carrier model is
//! kept unless the strict oracles or the independent gate REFUTE it (an
//! assertion evaluates to false); only then is it replaced by the positional
//! values, which are kept only if they are not refuted in turn. Refutation,
//! not confirmation, is the test because later passes still pin leaves
//! (measured: an unconstrained `(Seq Bool)` constant the preprocessed window
//! dropped), so an unconfirmed model is not yet a rejected one. The
//! construction satisfies the committed word equations, not the negative
//! constraints (a disequality, a false `seq.contains` or `seq.suffixof`), so
//! it can fail where the all-default witness happens to succeed; this order
//! keeps such a case at the per-carrier `sat` instead of `unknown`.
//!
//! Every loop is bounded by a counted cap (terms, reads, cells, passes and
//! arithmetic depth); no wall clock is consulted.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

use super::super::evaluation_copies::{self, EvaluationCopyScope};
use super::{EvalValue, Model};
use crate::executor::Executor;
use crate::executor_types::SolveResult;

mod cells;
mod lengths;
mod relevant;
#[cfg(test)]
mod tests;

/// Sequence-sorted terms, and separately `seq.len`/`seq.nth` reads, indexed.
const MAX_WITNESS_TERMS: usize = 4_096;
/// Positional cells over all classes, and cloned cells in the result.
const MAX_WITNESS_CELLS: usize = 4_096;
/// Nesting depth for the index and length arithmetic that is evaluated.
const MAX_WITNESS_ARITH_DEPTH: usize = 16;

/// Positional values for carriers that had no value before Phase 3, in term
/// order.
pub(super) struct PositionalSeqCandidate {
    values: Vec<(TermId, Vec<EvalValue>)>,
}

/// How one sequence term's value follows from the values of other terms.
enum Shape {
    Empty,
    Unit(TermId),
    Concat(Vec<usize>),
    /// `(seq.extract s i n)`, or `(seq.at s i)` when `count` is `None`.
    Extract {
        src: usize,
        start: TermId,
        count: Option<TermId>,
    },
    Opaque,
}

/// The committed sequence structure reachable from the roots.
struct SeqStructure<'a> {
    exec: &'a Executor,
    model: &'a Model,
    terms: Vec<TermId>,
    index: HashMap<TermId, usize>,
    shapes: Vec<Shape>,
    /// Dense class id of every term, numbered by first member.
    class_of: Vec<usize>,
    class_count: usize,
    /// `(seq.len s)` reads as `(read, s)`.
    len_reads: Vec<(TermId, TermId)>,
    /// `(seq.nth s i)` reads as `(read, s, i)`.
    nth_reads: Vec<(TermId, TermId, TermId)>,
    /// The value the model already gives each opaque term, if concrete.
    concrete: Vec<Option<Vec<EvalValue>>>,
    /// Largest absolute integer literal reachable from the roots.
    max_int_literal: BigInt,
}

impl Executor {
    /// Complete internal word-equation leaves after public carriers have
    /// concrete values. A decomposition skolem is not a public declaration,
    /// so ordinary declaration completion intentionally leaves it alone.
    /// Derive its segment from a relevant equality instead of trusting a
    /// default length chosen by the arithmetic abstraction. The result is a
    /// model choice; all original and generated assertions still replay.
    pub(super) fn complete_internal_seq_equations(
        &mut self,
        model: &mut Model,
        extra_roots: &[TermId],
    ) {
        let root_count = self.ctx.assertions.len().saturating_add(extra_roots.len());
        if model.seq_model.is_none() || root_count > MAX_WITNESS_TERMS {
            return;
        }
        let Ok(_copies) = EvaluationCopyScope::enter(self) else {
            return;
        };
        // Earlier completion phases may have observed abstract Boolean
        // fallback values. Read the now-completed carriers afresh.
        super::super::eval_memo_clear();
        // Preflight all bounded graph/map/vector metadata before collecting
        // roots. This uses the same evaluation attempt and its existing limit.
        // Root copies are separate from unique graph nodes: repeated roots
        // can have a large input vector over a very small DAG. The factor of
        // two covers vector growth when the extra roots are appended.
        let Some(metadata_bytes) = self
            .ctx
            .terms
            .len()
            .min(MAX_WITNESS_TERMS)
            .checked_mul(256)
            .and_then(|nodes| {
                root_count
                    .checked_mul(2 * std::mem::size_of::<TermId>())?
                    .checked_add(nodes)
            })
        else {
            return;
        };
        if !evaluation_copies::pay(root_count, metadata_bytes) || !evaluation_copies::validate(self)
        {
            return;
        }
        let mut roots = self.ctx.assertions.clone();
        roots.extend_from_slice(extra_roots);
        let Some(equations) = self.required_completed_seq_equations(model, roots) else {
            return;
        };
        if equations.len() > MAX_WITNESS_TERMS {
            return;
        }
        if super::super::debug_model() {
            safe_eprintln!("[sequence-completion] required-equations={equations:?}");
        }
        let mut completed = 0usize;
        let mut retained_cells = 0usize;
        for (left, right) in equations {
            if self.poll_evaluation_stop().is_err() {
                break;
            }
            for (whole, expression) in [(left, right), (right, left)] {
                if self.ctx.terms.sort(whole) != self.ctx.terms.sort(expression)
                    || !matches!(self.ctx.terms.sort(expression), Sort::Seq(_))
                {
                    continue;
                }
                let EvalValue::Seq(whole) = self.evaluate_term(model, whole) else {
                    continue;
                };
                if whole.len() > MAX_WITNESS_CELLS {
                    continue;
                }
                let TermData::App(symbol, parts) = self.ctx.terms.get(expression) else {
                    continue;
                };
                if symbol.name() != "seq.++" || parts.len() > MAX_WITNESS_TERMS {
                    continue;
                }
                let mut missing = None;
                let mut prefix = Vec::new();
                let mut suffix = Vec::new();
                let mut valid = true;
                for &part in parts {
                    if self.ctx.terms.sort(part) != self.ctx.terms.sort(expression) {
                        valid = false;
                        break;
                    }
                    let internal_leaf = matches!(self.ctx.terms.get(part), TermData::Var(name, _)
                        if self.ctx.symbol_info_by_identity(name).is_none())
                        && !model.completed_values.contains_key(&part)
                        && !model
                            .seq_model
                            .as_ref()
                            .is_some_and(|seq| seq.values.contains_key(&part));
                    if internal_leaf {
                        if missing.replace(part).is_some() {
                            valid = false;
                            break;
                        }
                        continue;
                    }
                    let EvalValue::Seq(value) = self.evaluate_term(model, part) else {
                        valid = false;
                        break;
                    };
                    let target = if missing.is_some() {
                        &mut suffix
                    } else {
                        &mut prefix
                    };
                    if target.len().saturating_add(value.len()) > MAX_WITNESS_CELLS {
                        valid = false;
                        break;
                    }
                    if !evaluation_copies::cells(target.len().saturating_add(value.len()))
                        || !evaluation_copies::validate(self)
                    {
                        return;
                    }
                    target.extend(value);
                }
                let Some(missing) = missing.filter(|_| valid) else {
                    continue;
                };
                if prefix.len().saturating_add(suffix.len()) > whole.len() {
                    continue;
                }
                let prefix_matches =
                    evaluation_copies::equal_slice(&whole[..prefix.len()], &prefix);
                if !evaluation_copies::validate(self) {
                    return;
                }
                if prefix_matches != Some(true) {
                    continue;
                }
                let suffix_matches =
                    evaluation_copies::equal_slice(&whole[whole.len() - suffix.len()..], &suffix);
                if !evaluation_copies::validate(self) {
                    return;
                }
                if suffix_matches != Some(true) {
                    continue;
                }
                let segment = &whole[prefix.len()..whole.len() - suffix.len()];
                let Some(next_cells) = retained_cells
                    .checked_add(segment.len())
                    .filter(|&cells| cells <= MAX_WITNESS_CELLS)
                else {
                    return;
                };
                let Some(segment) = evaluation_copies::copy_slice(segment) else {
                    return;
                };
                // The completion slot clones the value. Admit that second
                // owned copy before mutation, including deep element payloads.
                if !evaluation_copies::admit_slice(&segment) {
                    return;
                }
                if model.completed_values.len() == model.completed_values.capacity() {
                    let Some(bytes) =
                        model
                            .completed_values
                            .len()
                            .checked_add(1)
                            .and_then(|entries| {
                                entries.checked_mul(
                                    4 * (std::mem::size_of::<(TermId, EvalValue)>() + 16),
                                )
                            })
                    else {
                        self.record_evaluation_stop(
                            crate::executor_types::UnknownOrigin::MemoryBudget,
                        );
                        return;
                    };
                    if !evaluation_copies::pay(1, bytes) || !evaluation_copies::validate(self) {
                        return;
                    }
                    if model.completed_values.try_reserve(1).is_err() {
                        self.record_evaluation_stop(
                            crate::executor_types::UnknownOrigin::MemoryBudget,
                        );
                        return;
                    }
                }
                if !evaluation_copies::validate(self) {
                    return;
                }
                let value = EvalValue::Seq(segment);
                if Self::insert_completed_value(&self.ctx.terms, model, missing, &value) {
                    if super::super::debug_model() {
                        safe_eprintln!(
                            "[sequence-completion] installed={missing:?} cells={}",
                            next_cells - retained_cells
                        );
                    }
                    completed += 1;
                    retained_cells = next_cells;
                }
            }
        }
        if completed > 0 {
            self.last_statistics.set_int(
                "model_completion.internal_sequence_equations",
                completed as u64,
            );
        }
    }

    /// A completed public sequence can make a predicate true even when its
    /// former abstract SAT atom was false. In that case its decomposition is
    /// now needed. Use concrete connective values here, not SAT relevancy.
    /// If an unsatisfied disjunction has exactly one sequence equality and
    /// all its other children are false, that equation is its only repair.
    fn required_completed_seq_equations(
        &self,
        model: &Model,
        mut pending: Vec<TermId>,
    ) -> Option<Vec<(TermId, TermId)>> {
        let mut seen = HashSet::default();
        let mut equations = Vec::new();
        while let Some(term) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_WITNESS_TERMS || self.poll_evaluation_stop().is_err() {
                return None;
            }
            match self.ctx.terms.get(term) {
                TermData::App(symbol, args) if symbol.name() == "and" => {
                    if pending.len().saturating_add(args.len()) > MAX_WITNESS_TERMS {
                        return None;
                    }
                    let bytes = pending
                        .len()
                        .checked_add(args.len())?
                        .checked_mul(2 * std::mem::size_of::<TermId>())?;
                    if !evaluation_copies::pay(args.len(), bytes)
                        || !evaluation_copies::validate(self)
                    {
                        return None;
                    }
                    pending.extend_from_slice(args);
                }
                TermData::App(symbol, args) if symbol.name() == "or" => {
                    let mut candidate = None;
                    let mut required = true;
                    for &arg in args {
                        let sequence_equality = matches!(self.ctx.terms.get(arg),
                            TermData::App(symbol, sides) if symbol.name() == "="
                                && sides.len() == 2
                                && matches!(self.ctx.terms.sort(sides[0]), Sort::Seq(_)));
                        if sequence_equality {
                            // Abstract truth is not a concrete word witness.
                            // Derive its missing segment when all other
                            // disjuncts are false, even if this atom was true.
                            if candidate.replace(arg).is_some() {
                                required = false;
                                break;
                            }
                        } else if !matches!(self.evaluate_term(model, arg), EvalValue::Bool(false))
                        {
                            required = false;
                            break;
                        }
                    }
                    if let Some(candidate) = candidate.filter(|_| required) {
                        pending.push(candidate);
                    }
                }
                TermData::App(symbol, args) if symbol.name() == "=>" && args.len() == 2 => {
                    if matches!(self.evaluate_term(model, args[0]), EvalValue::Bool(true)) {
                        pending.push(args[1]);
                    }
                }
                TermData::App(symbol, args)
                    if symbol.name() == "="
                        && args.len() == 2
                        && matches!(self.ctx.terms.sort(args[0]), Sort::Seq(_)) =>
                {
                    equations.push((args[0], args[1]));
                }
                _ => {}
            }
        }
        Some(equations)
    }

    /// Build concrete values for the sequence terms reachable from `roots`,
    /// keyed by every non-builtin term (declared constants and UF
    /// applications) of a fully constructed class. `None` when the model's
    /// sequence structure is contradictory or over budget.
    pub(super) fn positional_seq_witness(
        &self,
        model: &Model,
        roots: &[TermId],
    ) -> Option<HashMap<TermId, Vec<EvalValue>>> {
        let structure = SeqStructure::collect(self, model, roots)?;
        let lengths = structure.class_lengths()?;
        structure.construct(&lengths)
    }

    /// Phase 3a (#seq-witness-completion): the joint positional witness of
    /// every opaque sequence carrier the model does not value yet. Computed
    /// before Phase 3 and not committed; `None` without a sequence-theory
    /// model or when there is nothing to offer.
    pub(super) fn positional_seq_candidate(
        &self,
        model: &Model,
        extra_roots: &[TermId],
    ) -> Option<PositionalSeqCandidate> {
        model.seq_model.as_ref()?;
        let mut roots = self.ctx.assertions.clone();
        roots.extend_from_slice(extra_roots);
        if let Some(authored) = self.self_check_authored_assertions.as_ref() {
            roots.extend_from_slice(authored);
        }
        let mut values: Vec<(TermId, Vec<EvalValue>)> = self
            .positional_seq_witness(model, &roots)?
            .into_iter()
            .filter(|&(t, _)| !matches!(self.evaluate_term(model, t), EvalValue::Seq(_)))
            .collect();
        values.sort_by_key(|(t, _)| t.index());
        (!values.is_empty()).then_some(PositionalSeqCandidate { values })
    }

    /// Final completion step: replace the per-carrier sequence values with the
    /// positional `candidate` only when the gates refute the model as it is,
    /// and keep the replacement only when they do not refute it; otherwise the
    /// semantic completion slots are restored on rejection. Exact-model seals
    /// revoked by a trial stay revoked. Returns the number of carriers replaced.
    pub(super) fn adopt_positional_seq_candidate(
        &mut self,
        model: &mut Model,
        candidate: Option<PositionalSeqCandidate>,
        extra_roots: &[TermId],
    ) -> usize {
        if model.seq_model.is_none() {
            return 0;
        }
        // Both alternatives belong to one optional evaluation attempt. Nested
        // witness completion must not renew its cumulative copy allowance.
        let Ok(_copies) = EvaluationCopyScope::enter(self) else {
            return 0;
        };
        let Some(PositionalSeqCandidate { values }) = candidate else {
            self.complete_internal_seq_equations(model, extra_roots);
            return 0;
        };
        // Keep the pre-completion model for the alternative: witnesses derived
        // from the per-carrier values cannot be reused after those values move.
        let Some(snapshot) = self.copy_seq_completion_slots(model) else {
            return 0;
        };
        self.complete_internal_seq_equations(model, extra_roots);
        if !evaluation_copies::validate(self) {
            model.completed_values = snapshot;
            model.revoke_all_quantified_model_seals();
            super::super::eval_memo_clear();
            return 0;
        }
        let baseline_refuted = self.completed_model_refuted(model);
        if !evaluation_copies::validate(self) {
            model.completed_values = snapshot;
            model.revoke_all_quantified_model_seals();
            super::super::eval_memo_clear();
            return 0;
        }
        if !baseline_refuted {
            return 0;
        }
        let repaired_per_carrier = std::mem::replace(&mut model.completed_values, snapshot);
        model.revoke_all_quantified_model_seals();
        super::super::eval_memo_clear();
        let mut replaced = 0usize;
        for (t, elems) in values {
            if !evaluation_copies::admit_slice(&elems) {
                model.completed_values = repaired_per_carrier;
                super::super::eval_memo_clear();
                return 0;
            }
            if !model.completed_values.contains_key(&t)
                && model.completed_values.len() == model.completed_values.capacity()
            {
                let bytes = model
                    .completed_values
                    .len()
                    .checked_add(1)
                    .and_then(|entries| {
                        entries.checked_mul(4 * (std::mem::size_of::<(TermId, EvalValue)>() + 16))
                    });
                let Some(bytes) = bytes else {
                    self.record_evaluation_stop(crate::executor_types::UnknownOrigin::MemoryBudget);
                    model.completed_values = repaired_per_carrier;
                    super::super::eval_memo_clear();
                    return 0;
                };
                if !evaluation_copies::pay(1, bytes) || !evaluation_copies::validate(self) {
                    model.completed_values = repaired_per_carrier;
                    super::super::eval_memo_clear();
                    return 0;
                }
                if model.completed_values.try_reserve(1).is_err() {
                    self.record_evaluation_stop(crate::executor_types::UnknownOrigin::MemoryBudget);
                    model.completed_values = repaired_per_carrier;
                    super::super::eval_memo_clear();
                    return 0;
                }
            }
            if !evaluation_copies::validate(self) {
                model.completed_values = repaired_per_carrier;
                super::super::eval_memo_clear();
                return 0;
            }
            if Self::insert_completed_value(&self.ctx.terms, model, t, &EvalValue::Seq(elems)) {
                replaced += 1;
            }
        }
        self.complete_internal_seq_equations(model, extra_roots);
        let candidate_refuted = if evaluation_copies::validate(self) {
            self.completed_model_refuted(model)
        } else {
            true
        };
        if replaced > 0 && !candidate_refuted && evaluation_copies::validate(self) {
            self.last_statistics
                .set_int("model_completion.positional_sequences", replaced as u64);
            return replaced;
        }
        model.completed_values = repaired_per_carrier;
        model.revoke_all_quantified_model_seals();
        super::super::eval_memo_clear();
        0
    }

    /// Sequence completion changes only completion slots and revokes theorem
    /// seals. Snapshot those slots under the original allowance, rather than
    /// cloning unrelated theory models and their potentially unbounded payloads.
    fn copy_seq_completion_slots(&self, model: &Model) -> Option<HashMap<TermId, EvalValue>> {
        let count = model.completed_values.len();
        let bytes = count
            .checked_add(1)?
            .checked_mul(4 * (std::mem::size_of::<(TermId, EvalValue)>() + 16))?;
        if !evaluation_copies::pay(count, bytes) || !evaluation_copies::validate(self) {
            return None;
        }
        let mut snapshot = HashMap::default();
        if snapshot.try_reserve(count).is_err() {
            self.record_evaluation_stop(crate::executor_types::UnknownOrigin::MemoryBudget);
            return None;
        }
        for (&term, value) in &model.completed_values {
            let value = evaluation_copies::copy(value);
            if !evaluation_copies::validate(self) {
                return None;
            }
            snapshot.insert(term, value);
        }
        Some(snapshot)
    }

    /// Whether the strict oracles or the independent gate find an assertion
    /// the completed `model` makes false. Installs the model temporarily, as
    /// `completed_gap_model_accepted` does, and restores it.
    fn completed_model_refuted(&mut self, model: &mut Model) -> bool {
        self.last_model = Some(std::mem::replace(model, Model::empty()));
        let prev_result = self.last_result.replace(SolveResult::Sat);
        let refuted = self.verify_model_strict().is_some()
            || matches!(
                self.confirm_sat_with_independent_gate(),
                ay_model_check::GateVerdict::ModelViolates { .. }
            );
        self.last_result = prev_result;
        if let Some(installed) = self.last_model.take() {
            *model = installed;
        }
        refuted
    }

    /// A sequence term completion may give a value: a declared constant, or
    /// an application of a declared function that is neither defined nor an
    /// adopted macro. Native theory applications can anchor a class but never
    /// receive a completion value.
    pub(super) fn is_opaque_seq_carrier(&self, term: TermId) -> bool {
        if !matches!(self.ctx.terms.sort(term), Sort::Seq(_)) {
            return false;
        }
        match self.ctx.terms.get(term) {
            // Internal variables are model points only when the declaration
            // registry owns their identity.
            TermData::Var(name, _) => self.ctx.symbol_info_by_identity(name).is_some(),
            TermData::App(sym, args) => {
                !args.is_empty()
                    && !crate::features::is_builtin_symbol_name(sym.name())
                    && self.ctx.symbol_info_by_identity(sym.name()).is_some()
                    && !self.ctx.is_defined_fun(sym.name())
                    && self.ctx.adopted_macro_interp(sym.name()).is_none()
            }
            _ => false,
        }
    }
}

impl<'a> SeqStructure<'a> {
    fn collect(exec: &'a Executor, model: &'a Model, roots: &[TermId]) -> Option<Self> {
        let terms_store = &exec.ctx.terms;
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots.to_vec();
        let mut terms = Vec::new();
        let mut lens = Vec::new();
        let mut nths = Vec::new();
        let mut max_int_literal = BigInt::zero();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if matches!(terms_store.sort(t), Sort::Seq(_)) {
                terms.push(t);
            }
            match terms_store.get(t) {
                TermData::Const(Constant::Int(n)) if n.abs() > max_int_literal => {
                    max_int_literal = n.abs();
                }
                TermData::App(sym, args) => {
                    match (sym.name(), args.as_slice()) {
                        ("seq.len", [s]) => lens.push((t, *s)),
                        ("seq.nth", [s, i]) => nths.push((t, *s, *i)),
                        _ => {}
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                // Quantifier and let bodies bind variables that are not model
                // points; the other completion collectors skip them too.
                _ => {}
            }
            if terms.len() > MAX_WITNESS_TERMS
                || lens.len() > MAX_WITNESS_TERMS
                || nths.len() > MAX_WITNESS_TERMS
            {
                return None;
            }
        }
        if terms.is_empty() {
            return None;
        }
        terms.sort_by_key(|t| t.index());
        let index: HashMap<TermId, usize> =
            terms.iter().enumerate().map(|(i, &t)| (t, i)).collect();
        let shapes: Vec<Shape> = terms
            .iter()
            .map(|&t| Self::shape(exec, &index, t))
            .collect();
        let concrete = terms
            .iter()
            .zip(&shapes)
            .map(|(&t, shape)| match shape {
                Shape::Opaque => match exec.evaluate_term(model, t) {
                    EvalValue::Seq(elems) => Some(elems),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        // Classes come from the relevant true equalities only. EUF's internal
        // class labels are not used: EUF also merged every don't-care atom
        // the SAT solver happened to set true.
        let mut parent: Vec<usize> = (0..terms.len()).collect();
        for (a, b) in exec.relevant_seq_equalities(model, roots)? {
            if let (Some(&ia), Some(&ib)) = (index.get(&a), index.get(&b)) {
                cells::union(&mut parent, ia, ib);
            }
        }
        let (class_of, class_count) = cells::dense_classes(&mut parent);
        Some(Self {
            exec,
            model,
            terms,
            index,
            shapes,
            class_of,
            class_count,
            len_reads: lens,
            nth_reads: nths,
            concrete,
            max_int_literal,
        })
    }

    fn shape(exec: &Executor, index: &HashMap<TermId, usize>, t: TermId) -> Shape {
        let TermData::App(sym, args) = exec.ctx.terms.get(t) else {
            return Shape::Opaque;
        };
        let idx = |s: &TermId| index.get(s).copied();
        match (sym.name(), args.as_slice()) {
            ("seq.empty", []) => Shape::Empty,
            ("seq.unit", [e]) => Shape::Unit(*e),
            ("seq.++", parts) if !parts.is_empty() => {
                match parts.iter().map(idx).collect::<Option<Vec<_>>>() {
                    Some(parts) => Shape::Concat(parts),
                    None => Shape::Opaque,
                }
            }
            ("seq.extract", [s, i, n]) => match idx(s) {
                Some(src) => Shape::Extract {
                    src,
                    start: *i,
                    count: Some(*n),
                },
                None => Shape::Opaque,
            },
            ("seq.at", [s, i]) => match idx(s) {
                Some(src) => Shape::Extract {
                    src,
                    start: *i,
                    count: None,
                },
                None => Shape::Opaque,
            },
            _ => Shape::Opaque,
        }
    }

    /// The integer the model gives `t` directly: a literal or an arithmetic
    /// model row. Never evaluates through a sequence value.
    fn raw_int(&self, t: TermId) -> Option<BigInt> {
        if let TermData::Const(Constant::Int(n)) = self.exec.ctx.terms.get(t) {
            return Some(n.clone());
        }
        if let Some(v) = self.model.lia_model.as_ref().and_then(|m| m.values.get(&t)) {
            return Some(v.clone());
        }
        self.model
            .lra_model
            .as_ref()
            .and_then(|m| m.values.get(&t))
            .filter(|r| r.is_integer())
            .map(|r| r.to_integer())
    }

    /// Integer value of an index or length expression over model rows,
    /// literals, `+`/`-`/`*` and `seq.len` of a class whose length is known.
    fn int_value(&self, lengths: &[Option<usize>], t: TermId, depth: usize) -> Option<BigInt> {
        if let Some(v) = self.raw_int(t) {
            return Some(v);
        }
        if depth >= MAX_WITNESS_ARITH_DEPTH {
            return None;
        }
        let TermData::App(sym, args) = self.exec.ctx.terms.get(t) else {
            return None;
        };
        let mut vals = args.iter().map(|&a| self.int_value(lengths, a, depth + 1));
        match (sym.name(), args.len()) {
            ("seq.len", 1) => {
                let class = self.class_of[*self.index.get(&args[0])?];
                lengths[class].map(BigInt::from)
            }
            ("+", _) => vals.try_fold(BigInt::zero(), |acc, v| Some(acc + v?)),
            ("-", 1) => vals.next()?.map(|v| -v),
            ("-", n) if n > 1 => {
                let first = vals.next()??;
                vals.try_fold(first, |acc, v| Some(acc - v?))
            }
            ("*", _) => vals.try_fold(BigInt::from(1), |acc, v| Some(acc * v?)),
            _ => None,
        }
    }

    /// `(offset, length)` of `(seq.extract s start count)` over a source of
    /// length `src_len`, with SMT-LIB's empty result out of range.
    fn extract_window(
        &self,
        lengths: &[Option<usize>],
        start: TermId,
        count: Option<TermId>,
        src_len: usize,
    ) -> Option<(usize, usize)> {
        let start = self.int_value(lengths, start, 0)?;
        let count = match count {
            Some(n) => self.int_value(lengths, n, 0)?,
            None => BigInt::from(1),
        };
        if start.is_negative() || !count.is_positive() || start >= BigInt::from(src_len) {
            return Some((0, 0));
        }
        let offset = start.to_usize()?;
        let n = count.to_usize().unwrap_or(usize::MAX).min(src_len - offset);
        Some((offset, n))
    }
}
