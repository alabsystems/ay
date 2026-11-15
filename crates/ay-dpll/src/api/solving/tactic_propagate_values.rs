// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conjunction-preserving value propagation under the original tactic owner.
//! As in the maintained goal pass, rewrite before harvesting each assertion,
//! and use fresh facts in each forward/backward sweep. A defining assertion
//! cannot erase itself. Binders remain opaque; no new variable is introduced.
use super::field_to_bv::Borrowed;
use super::tactic_solve_eqs::{children, reachable};
use super::tactics::TacticFailure;
use super::{tactic_bool_rewrite::ConjunctionMode, tactic_parameters::Steps};
use ay_core::kani_compat::DetHashMap as Map;
use ay_core::term::{
    reserve_counted, reserve_map_counted, CountedBuiltin as Op, CountedTermBuilder,
    TermConstructionAdmission,
};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};

fn failed() -> TacticFailure {
    TacticFailure::new("propagate-values original admission stopped or source graph invalid")
}
fn pay(owner: &dyn TermConstructionAdmission, work: usize) -> Result<(), TacticFailure> {
    owner.admit(work, 0).map_err(|_| failed())
}

pub(super) struct Closed<'a>(pub(super) &'a dyn TermConstructionAdmission);
impl ay_model_check::ModelView for Closed<'_> {
    fn has_evaluation_admission(&self) -> bool {
        true
    }
    fn admit_evaluation_work(&self, work: usize, bytes: usize) -> Result<(), String> {
        self.0.admit(work, bytes).map_err(|e| e.to_string())
    }
    fn refuse_evaluation_work(&self, _: &str) {
        ay_core::render_admission::invalid(Some(self.0));
    }
    fn functional_array_interrupted(&self) -> bool {
        self.0.check().is_err()
    }
    fn charge_functional_array_work(&self, work: usize) -> Result<(), String> {
        self.admit_evaluation_work(work, 0)
    }
    fn admit_exact_fp_work(&self, work: usize, bytes: usize) -> Result<(), String> {
        // Both hooks name this exact borrowed owner, not distinct ledgers.
        // The evaluator still applies its separate local work/storage ceilings.
        self.admit_evaluation_work(work, bytes)
    }
    fn leaf_value(&self, _: TermId) -> Option<ay_model_check::ModelValue> {
        None
    }
}

// Evaluation under one model is not by itself an equivalence proof. Only
// closed expressions made of these total, deterministic operators may fold.
// In particular div/mod, under-specified operations, UFs and binders are opaque.
fn pure(
    term: &TermData,
    store: &TermStore,
    owner: &dyn TermConstructionAdmission,
) -> Result<bool, TacticFailure> {
    Ok(match term {
        TermData::Const(
            Constant::Bool(_)
            | Constant::Int(_)
            | Constant::Rational(_)
            | Constant::BitVec { .. }
            | Constant::String(_)
            | Constant::FiniteField { .. },
        ) => true,
        TermData::Not(_) | TermData::Ite(..) => true,
        TermData::App(Symbol::Named(name), _) => {
            pay(owner, name.len())?;
            !store.is_declared_function(name)
                && matches!(
                    name.as_str(),
                    "and"
                        | "RNE"
                        | "RNA"
                        | "RTP"
                        | "RTN"
                        | "RTZ"
                        | "roundNearestTiesToEven"
                        | "roundNearestTiesToAway"
                        | "roundTowardPositive"
                        | "roundTowardNegative"
                        | "roundTowardZero"
                        | "or"
                        | "not"
                        | "=>"
                        | "xor"
                        | "ite"
                        | "="
                        | "distinct"
                        | "+"
                        | "-"
                        | "*"
                        | "<"
                        | "<="
                        | ">"
                        | ">="
                        | "to_real"
                        | "to_int"
                        | "is_int"
                        | "ff.add"
                        | "ff.mul"
                        | "ff.neg"
                        | "ff.bitsum"
                        | "const"
                        | "select"
                        | "store"
                        | "bvadd"
                        | "bvudiv"
                        | "bvurem"
                        | "bvsdiv"
                        | "bvsrem"
                        | "bvsmod"
                        | "bvsub"
                        | "bvmul"
                        | "bvand"
                        | "bvor"
                        | "bvxor"
                        | "bvnand"
                        | "bvnor"
                        | "bvxnor"
                        | "bvnot"
                        | "bvneg"
                        | "bvshl"
                        | "bvlshr"
                        | "bvashr"
                        | "bvult"
                        | "bvule"
                        | "bvugt"
                        | "bvuge"
                        | "bvslt"
                        | "bvsle"
                        | "bvsgt"
                        | "bvsge"
                        | "concat"
                        | "bvcomp"
                        | "fp"
                        | "fp.abs"
                        | "fp.neg"
                        | "fp.add"
                        | "fp.sub"
                        | "fp.mul"
                        | "fp.div"
                        | "fp.fma"
                        | "fp.sqrt"
                        | "fp.rem"
                        | "fp.roundToIntegral"
                        // Closed NaN encodings remain unfurled: the evaluator
                        // refuses their unspecified value without a model.
                        | "fp.to_ieee_bv"
                        | "fp.eq"
                        | "fp.lt"
                        | "fp.leq"
                        | "fp.gt"
                        | "fp.geq"
                        | "fp.isNaN"
                        | "fp.isInfinite"
                        | "fp.isZero"
                        | "fp.isNormal"
                        | "fp.isSubnormal"
                        | "fp.isNegative"
                        | "fp.isPositive"
                        | "str.++"
                        | "str.len"
                        | "str.at"
                        | "str.substr"
                        | "str.contains"
                        | "str.prefixof"
                        | "str.suffixof"
                        | "str.indexof"
                        | "str.replace"
                        | "str.replace_all"
                        | "str.to_int"
                        | "str.from_int"
                        | "str.to_code"
                        | "str.from_code"
                        | "seq.++"
                        | "seq.len"
                        | "seq.unit"
                        | "seq.empty"
                        | "seq.extract"
                        | "seq.at"
                        | "seq.contains"
                        | "seq.prefixof"
                        | "seq.suffixof"
                )
        }
        TermData::App(Symbol::Indexed(name, _), _) => {
            pay(owner, name.len())?;
            !store.is_declared_function(name)
                && matches!(
                    name.as_str(),
                    "const"
                        | "extract"
                        | "zero_extend"
                        | "sign_extend"
                        | "rotate_left"
                        | "rotate_right"
                        | "repeat"
                        | "to_fp"
                        | "to_fp_unsigned"
                        | "+zero"
                        | "-zero"
                        | "+oo"
                        | "-oo"
                        | "NaN"
                )
        }
        _ => false,
    })
}

fn negate(
    builder: &mut CountedTermBuilder<'_, '_, Borrowed<'_>>,
    id: TermId,
    owner: &dyn TermConstructionAdmission,
) -> Result<TermId, TacticFailure> {
    pay(owner, 1)?;
    match builder.terms().get(id) {
        TermData::Const(Constant::Bool(value)) => {
            let value = !*value;
            builder.boolean(value).map_err(|_| failed())
        }
        TermData::Not(child) if builder.terms().sort(*child) == &Sort::Bool => Ok(*child),
        _ => builder.apply(Op::Not, &[id]).map_err(|_| failed()),
    }
}

fn boolean_fold(
    builder: &mut CountedTermBuilder<'_, '_, Borrowed<'_>>,
    source: TermId,
    args: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<Option<TermId>, TacticFailure> {
    if builder.terms().sort(source) != &Sort::Bool {
        return Ok(None);
    }
    let op = match builder.terms().get(source) {
        TermData::Not(_) => Op::Not,
        TermData::Ite(..) => Op::Ite,
        TermData::App(Symbol::Named(name), _) => {
            pay(owner, name.len())?;
            if builder.terms().is_declared_function(name) {
                return Ok(None);
            }
            match name.as_str() {
                "and" => Op::And,
                "or" => Op::Or,
                "not" => Op::Not,
                "=>" => Op::Implies,
                "xor" => Op::Xor,
                "=" => Op::Eq,
                "ite" => Op::Ite,
                _ => return Ok(None),
            }
        }
        _ => return Ok(None),
    };
    pay(owner, args.len())?;
    if args
        .iter()
        .any(|&id| builder.terms().sort(id) != &Sort::Bool)
    {
        return Ok(None);
    }
    let literal = |id| match builder.terms().get(id) {
        TermData::Const(Constant::Bool(value)) => Some(*value),
        _ => None,
    };
    let folded = match (op, args) {
        (Op::Not, [arg]) => negate(builder, *arg, owner)?,
        (Op::Ite, [condition, yes, no]) => match literal(*condition) {
            Some(true) => *yes,
            Some(false) => *no,
            None if yes == no => *yes,
            None => return Ok(None),
        },
        (Op::And | Op::Or, _) => {
            let conjunction = op == Op::And;
            let mut retained = Vec::new();
            for &arg in args {
                pay(owner, 1)?;
                match literal(arg) {
                    Some(value) if value != conjunction => {
                        return builder.boolean(value).map(Some).map_err(|_| failed());
                    }
                    Some(_) => {}
                    None => {
                        reserve_counted(&mut retained, 1, owner).map_err(|_| failed())?;
                        retained.push(arg);
                    }
                }
            }
            match retained.as_slice() {
                [] => builder.boolean(conjunction).map_err(|_| failed())?,
                [single] => *single,
                _ if retained.len() == args.len() => return Ok(None),
                _ => builder.apply(op, &retained).map_err(|_| failed())?,
            }
        }
        (Op::Implies, [left, right]) => match (literal(*left), literal(*right)) {
            (Some(false), _) | (_, Some(true)) => builder.boolean(true).map_err(|_| failed())?,
            (Some(true), _) => *right,
            (_, Some(false)) => negate(builder, *left, owner)?,
            _ if left == right => builder.boolean(true).map_err(|_| failed())?,
            _ => return Ok(None),
        },
        (Op::Eq | Op::Xor, [left, right]) => {
            let equal = op == Op::Eq;
            if left == right {
                builder.boolean(equal).map_err(|_| failed())?
            } else {
                match (literal(*left), literal(*right)) {
                    (Some(value), _) if value == equal => *right,
                    (Some(_), _) => negate(builder, *right, owner)?,
                    (_, Some(value)) if value == equal => *left,
                    (_, Some(_)) => negate(builder, *left, owner)?,
                    _ => return Ok(None),
                }
            }
        }
        _ => return Ok(None),
    };
    Ok(Some(folded))
}

fn rewrite(
    builder: &mut CountedTermBuilder<'_, '_, Borrowed<'_>>,
    root: TermId,
    facts: &Map<TermId, TermId>,
    conjunctions: ConjunctionMode,
    steps: &mut Steps,
    owner: &dyn TermConstructionAdmission,
) -> Result<TermId, TacticFailure> {
    let marked = reachable(builder.terms(), &[root], owner)?;
    let mut mapped = Vec::new();
    let mut closed = Vec::new();
    reserve_counted(&mut mapped, marked.len(), owner).map_err(|_| failed())?;
    reserve_counted(&mut closed, marked.len(), owner).map_err(|_| failed())?;
    pay(owner, marked.len())?;
    mapped.resize(marked.len(), None);
    closed.resize(marked.len(), false);
    let mut args = Vec::new();
    for (index, present) in marked.iter().enumerate() {
        pay(owner, 1)?;
        if !present {
            continue;
        }
        let id = TermId(index as u32);
        steps.visit(owner)?;
        if let Some(&value) = facts.get(&id) {
            mapped[index] = Some(value);
            closed[index] = true; // Harvest accepts concrete constants only.
            continue;
        }
        // Existing literal payloads already belong to this source store.
        // Reusing them avoids cloning and normalizing them on every sweep.
        if matches!(builder.terms().get(id), TermData::Const(_)) {
            mapped[index] = Some(id);
            closed[index] = pure(builder.terms().get(id), builder.terms(), owner)?;
            continue;
        }
        if matches!(
            builder.terms().get(id),
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..)
        ) {
            mapped[index] = Some(id);
            continue;
        }
        args.clear();
        children(builder.terms().get(id), &mut args, owner)?;
        let mut is_closed = pure(builder.terms().get(id), builder.terms(), owner)?;
        for child in &mut args {
            pay(owner, 1)?;
            is_closed &= closed[child.index()];
            *child = mapped[child.index()].ok_or_else(failed)?;
        }
        let rebuilt = builder.rebuild_existing(id, &args).map_err(|_| failed())?;
        let eliminate = if conjunctions == ConjunctionMode::Eliminate
            && builder.terms().sort(id) == &Sort::Bool
        {
            match builder.terms().get(id) {
                TermData::App(Symbol::Named(name), _) => {
                    pay(owner, name.len())?;
                    name == "and" && !builder.terms().is_declared_function(name)
                }
                _ => false,
            }
        } else {
            false
        };
        let result = if eliminate {
            super::tactic_bool_rewrite::eliminate_and(builder, &mut args)?
        } else if let Some(folded) = boolean_fold(builder, id, &args, owner)? {
            folded
        } else if is_closed {
            let evaluated = ay_model_check::evaluate_term(builder.terms(), &Closed(owner), rebuilt);
            owner.check().map_err(|_| failed())?;
            match (builder.terms().sort(rebuilt), evaluated) {
                (
                    Sort::Bool,
                    ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Bool(value)),
                ) => builder.boolean(value).map_err(|_| failed())?,
                (
                    Sort::Int,
                    ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Int(value)),
                ) => builder.integer(&value).map_err(|_| failed())?,
                (
                    Sort::Real,
                    ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Real(value)),
                ) => builder.rational(&value).map_err(|_| failed())?,
                (
                    Sort::BitVec(expected),
                    ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::BitVec {
                        width,
                        value,
                    }),
                ) if expected.width == width => {
                    builder.bitvector(&value, width).map_err(|_| failed())?
                }
                (
                    Sort::FiniteField(field),
                    ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Int(value)),
                ) => {
                    use num_traits::ToPrimitive as _;
                    let field = *field;
                    pay(owner, 1)?;
                    let value = value
                        .to_u32()
                        .filter(|v| *v < field.modulus())
                        .ok_or_else(failed)?;
                    builder.finite_field(value, field).map_err(|_| failed())?
                }
                (
                    Sort::String,
                    ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Str(value)),
                ) => builder.string(&value).map_err(|_| failed())?,
                (Sort::FloatingPoint(_, _), ay_model_check::EvalOutcome::Value(value)) => {
                    super::term_simplifier::fp_literal(builder, rebuilt, &value, owner)?
                        .unwrap_or(rebuilt)
                }
                _ => rebuilt,
            }
        } else {
            rebuilt
        };
        mapped[index] = Some(result);
        closed[index] = is_closed || matches!(builder.terms().get(result), TermData::Const(_));
    }
    owner.check().map_err(|_| failed())?;
    mapped[root.index()].ok_or_else(failed)
}

/// A term request is not a conjunction/goal: do not harvest definitions,
/// split roots or discard Boolean constants. Reuse the SAME paid worker.
pub(super) fn simplify_term(
    store: &mut TermStore,
    source: TermId,
    conjunctions: ConjunctionMode,
    steps: &mut Steps,
    owner: &dyn TermConstructionAdmission,
) -> Result<TermId, TacticFailure> {
    let borrowed = Borrowed(owner);
    let mut builder = CountedTermBuilder::with_admission(store, &borrowed).map_err(|_| failed())?;
    let result = rewrite(
        &mut builder,
        source,
        &Map::default(),
        conjunctions,
        steps,
        owner,
    )?;
    builder.finish().map_err(|_| failed())?;
    Ok(result)
}

fn insert(
    facts: &mut Map<TermId, TermId>,
    source: TermId,
    value: TermId,
    store: &TermStore,
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    pay(owner, 1)?;
    if concrete(store, source, owner)? {
        return Ok(());
    }
    // Existing nodes supply sort identity, but arbitrary nested sort equality
    // is not unpriced. Restrict harvesting to the concrete scalar carriers.
    let compatible = match (store.sort(source), store.sort(value)) {
        (Sort::Bool, Sort::Bool)
        | (Sort::Int, Sort::Int)
        | (Sort::Real, Sort::Real)
        | (Sort::String, Sort::String) => true,
        (Sort::BitVec(a), Sort::BitVec(b)) => a == b,
        (Sort::FiniteField(a), Sort::FiniteField(b)) => a == b,
        (Sort::FloatingPoint(ae, as_), Sort::FloatingPoint(be, bs)) => ae == be && as_ == bs,
        (Sort::Uninterpreted(a), Sort::Uninterpreted(b)) => {
            a == "RoundingMode" && b == "RoundingMode"
        }
        _ => false,
    };
    if compatible && concrete(store, value, owner)? {
        reserve_map_counted(facts, 1, owner).map_err(|_| failed())?;
        facts.insert(source, value);
    }
    Ok(())
}

fn concrete(
    store: &TermStore,
    term: TermId,
    owner: &dyn TermConstructionAdmission,
) -> Result<bool, TacticFailure> {
    pay(owner, 1)?;
    if matches!(store.sort(term), Sort::FloatingPoint(..))
        || matches!(store.sort(term), Sort::Uninterpreted(name) if name == "RoundingMode")
    {
        return crate::preprocess::fp_literal::is_value(store, term, owner).map_err(|_| failed());
    }
    Ok(matches!(store.get(term), TermData::Const(_)))
}

fn harvest(
    builder: &mut CountedTermBuilder<'_, '_, Borrowed<'_>>,
    root: TermId,
    facts: &mut Map<TermId, TermId>,
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    pay(owner, 1)?;
    if matches!(builder.terms().get(root), TermData::Const(_)) {
        return Ok(());
    }
    if let TermData::App(Symbol::Named(name), args) = builder.terms().get(root) {
        pay(owner, name.len())?;
        if name == "=" && args.len() == 2 && !builder.terms().is_declared_function(name) {
            let (left, right) = (args[0], args[1]);
            match (
                concrete(builder.terms(), left, owner)?,
                concrete(builder.terms(), right, owner)?,
            ) {
                (false, true) => return insert(facts, left, right, builder.terms(), owner),
                (true, false) => return insert(facts, right, left, builder.terms(), owner),
                _ => {}
            }
        }
    }
    let source = match builder.terms().get(root) {
        TermData::Not(child) => Some(*child),
        TermData::App(Symbol::Named(name), args)
            if name == "not" && args.len() == 1 && !builder.terms().is_declared_function(name) =>
        {
            Some(args[0])
        }
        _ => None,
    };
    let value = builder.boolean(source.is_none()).map_err(|_| failed())?;
    insert(facts, source.unwrap_or(root), value, builder.terms(), owner)
}

pub(super) fn apply(
    store: &mut TermStore,
    mut roots: Vec<TermId>,
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<TermId>, TacticFailure> {
    reachable(store, &roots, owner)?;
    let borrowed = Borrowed(owner);
    let mut builder = CountedTermBuilder::with_admission(store, &borrowed).map_err(|_| failed())?;
    let mut steps = Steps::new(None);
    loop {
        let mut changed = false;
        for forward in [true, false] {
            let mut facts = Map::default();
            for step in 0..roots.len() {
                pay(owner, 1)?;
                let index = if forward {
                    step
                } else {
                    roots.len() - 1 - step
                };
                if builder.terms().sort(roots[index]) != &Sort::Bool {
                    return Err(failed());
                }
                let result = rewrite(
                    &mut builder,
                    roots[index],
                    &facts,
                    ConjunctionMode::Retain,
                    &mut steps,
                    owner,
                )?;
                changed |= result != roots[index];
                roots[index] = result;
                harvest(&mut builder, result, &mut facts, owner)?;
            }
        }
        if !changed {
            break;
        }
    }
    let mut output = Vec::new();
    for root in roots {
        pay(owner, 1)?;
        match builder.terms().get(root) {
            TermData::Const(Constant::Bool(true)) => {}
            TermData::Const(Constant::Bool(false)) => {
                output.clear();
                reserve_counted(&mut output, 1, owner).map_err(|_| failed())?;
                output.push(root);
                break;
            }
            _ => {
                reserve_counted(&mut output, 1, owner).map_err(|_| failed())?;
                output.push(root);
            }
        }
    }
    builder.finish().map_err(|_| failed())?;
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::{Logic, Solver, Tactic, Term};
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    };

    fn original(stop: Arc<AtomicBool>) -> CountedAdmission {
        CountedAdmission::new(
            FiniteAdmissionGrant::new(20_000_000, 64 << 20),
            None,
            Arc::new(move || stop.load(Ordering::Relaxed)),
        )
        .unwrap()
    }

    fn equivalent_under_fp_binding(
        terms: &TermStore,
        left: &[Term],
        right: &[Term],
        binding: Option<TermId>,
    ) {
        let mut store = terms.clone();
        for (premises, conclusions) in [(left, right), (right, left)] {
            let mut negated: Vec<_> = premises
                .iter()
                .map(|term| store.mk_not_raw(term.id()))
                .collect();
            if let Some(binding) = binding {
                negated.push(store.mk_not_raw(binding));
            }
            for conclusion in conclusions {
                let mut clause = negated.clone();
                clause.push(conclusion.id());
                clause.sort_unstable();
                clause.dedup();
                let counterexample: Vec<_> = clause
                    .iter()
                    .map(|&literal| store.mk_not_raw(literal))
                    .collect();
                // Ask the strict independent evaluator, including for a
                // retained RM-only definition. Refute the actual negation of
                // the implication; a valid proof must end in the empty clause.
                let mut proof = ay_core::Proof::new();
                let lemma = proof.add_theory_lemma_with_kind(
                    "FP",
                    clause,
                    ay_core::TheoryLemmaKind::FpGroundEval,
                );
                let mut premises = vec![lemma];
                for literal in counterexample {
                    premises.push(proof.add_assume(literal, None));
                }
                proof.add_rule_step(
                    ay_core::AletheRule::Resolution,
                    Vec::new(),
                    premises,
                    Vec::new(),
                );
                assert!(ay_proof::check_proof_strict(&proof, &store).is_ok());
            }
        }
    }

    #[test]
    fn admitted_fp_rounding_definitions_fold_without_guessing_free_modes() {
        for (defined, rounded_up) in [(true, true), (true, false), (false, true), (false, false)] {
            let mut solver = Solver::new(Logic::All);
            let mode = solver.declare_const("mode", Sort::Uninterpreted("RoundingMode".into()));
            let rtp = solver.fp_rounding_mode("RTP");
            let one = solver.fp_const_from_bits(0x3ff0000000000000, 11, 53);
            let tiny = solver.fp_const_from_bits(0x3c90000000000000, 11, 53); // 2^-54
            let expected =
                solver.fp_const_from_bits(0x3ff0000000000000 + u64::from(rounded_up), 11, 53);
            let sum = solver.fp_add(mode, one, tiny);
            let definition = solver.eq(mode, rtp);
            let claim = solver.eq(sum, expected);
            let originals = if defined {
                vec![definition, claim]
            } else {
                vec![claim]
            };
            let mut roots = originals.clone();
            solver
                .apply_tactic_to_goal(&Tactic::PropagateValues, &mut roots)
                .unwrap();
            if defined && !rounded_up {
                assert_eq!(roots.len(), 1);
                assert_eq!(
                    solver.terms().get(roots[0].id()),
                    &TermData::Const(Constant::Bool(false))
                );
            } else if defined {
                assert!(!roots.is_empty());
                equivalent_under_fp_binding(solver.terms(), &originals, &roots, None);
            } else {
                assert!(
                    !roots.is_empty(),
                    "a free mode does not license a rounding choice"
                );
                // Exhaust the five semantic RM values with the independent
                // arithmetic kernel, rather than guessing one for the tactic.
                for name in ["RNE", "RNA", "RTP", "RTN", "RTZ"] {
                    let literal = solver.fp_rounding_mode(name);
                    let binding = solver.eq(mode, literal);
                    equivalent_under_fp_binding(
                        solver.terms(),
                        &originals,
                        &roots,
                        Some(binding.id()),
                    );
                }
            }
        }
    }

    #[test]
    fn admitted_fp_literal_propagation_folds_wide_remainder_and_preserves_definitions() {
        use num_bigint::BigInt;
        for wrong in [false, true] {
            let mut solver = Solver::new(Logic::All);
            let x = solver.declare_const("wide_propagation_x", Sort::FloatingPoint(8, 200));
            let five_bits = (BigInt::from(129) << 199usize) | (BigInt::from(1) << 197usize);
            let three_bits = (BigInt::from(128) << 199usize) | (BigInt::from(1) << 198usize);
            let minus_one_bits = (BigInt::from(1) << 207usize) | (BigInt::from(127) << 199usize);
            let five = solver
                .try_fp_const_from_bits_bigint(&five_bits, 8, 200)
                .unwrap();
            let three = solver
                .try_fp_const_from_bits_bigint(&three_bits, 8, 200)
                .unwrap();
            let expected = solver
                .try_fp_const_from_bits_bigint(
                    &if wrong {
                        BigInt::from(0)
                    } else {
                        minus_one_bits
                    },
                    8,
                    200,
                )
                .unwrap();
            let remainder = solver.fp_rem(x, three);
            let definition = solver.eq(x, five);
            let consequence = solver.eq(remainder, expected);
            let originals = [definition, consequence];
            let mut roots = originals.to_vec();
            solver
                .apply_tactic_to_goal(&Tactic::PropagateValues, &mut roots)
                .unwrap();
            if wrong {
                assert_eq!(roots.len(), 1);
                assert_eq!(
                    solver.terms().get(roots[0].id()),
                    &TermData::Const(Constant::Bool(false))
                );
            } else {
                assert!(
                    !roots.is_empty(),
                    "a defining assertion cannot erase itself"
                );
                // Independently check both directions of conjunction equivalence.
                // This checks IEEE meaning, not a particular numeral AST spelling.
                equivalent_under_fp_binding(solver.terms(), &originals, &roots, None);
            }
        }
    }

    #[test]
    fn admitted_fp_propagation_distinguishes_ieee_and_structural_zero_equality() {
        for ieee in [false, true] {
            let mut solver = Solver::new(Logic::All);
            let x = solver.declare_const("signed_zero_x", Sort::FloatingPoint(8, 200));
            let positive = solver.fp_plus_zero(8, 200);
            let negative = solver.fp_minus_zero(8, 200);
            let definition = solver.eq(x, positive);
            let claim = if ieee {
                solver.fp_eq(x, negative)
            } else {
                solver.eq(x, negative)
            };
            let mut roots = vec![definition, claim];
            solver
                .apply_tactic_to_goal(&Tactic::PropagateValues, &mut roots)
                .unwrap();
            if ieee {
                assert!(!roots.is_empty());
                assert!(roots
                    .iter()
                    .all(|term| solver.terms().get(term.id())
                        != &TermData::Const(Constant::Bool(false))));
            } else {
                assert_eq!(roots.len(), 1);
                assert_eq!(
                    solver.terms().get(roots[0].id()),
                    &TermData::Const(Constant::Bool(false))
                );
            }
        }
    }

    #[test]
    fn admitted_value_sweeps_keep_definitions_fold_consequences_and_find_conflicts() {
        for reverse in [false, true] {
            let mut solver = Solver::new(Logic::All);
            let x = solver.int_var("propagation_x");
            let one = solver.int_const(1);
            let two = solver.int_const(2);
            let sum = solver.add(x, one);
            let definition = solver.eq(x, one);
            let consequence = solver.eq(sum, two);
            let mut roots = if reverse {
                vec![consequence, definition]
            } else {
                vec![definition, consequence]
            };
            assert!(solver
                .apply_tactic_to_goal(&Tactic::PropagateValues, &mut roots)
                .unwrap());
            assert_eq!(roots, [definition]);
            let conflict = solver.eq(x, two);
            let mut roots = vec![definition, conflict];
            solver
                .apply_tactic_to_goal(&Tactic::PropagateValues, &mut roots)
                .unwrap();
            assert_eq!(roots.len(), 1);
            assert_eq!(
                solver.terms().get(roots[0].id()),
                &TermData::Const(Constant::Bool(false))
            );
        }
        #[cfg(any(target_os = "macos", all(target_os = "linux", not(target_env = "uclibc"))))]
        if let Some(reference) = super::super::tactic_model::bounded_reference(
            "(set-logic QF_LIA)\n(declare-const propagation_x Int)\n(assert (= propagation_x 1))\n(assert (= (+ propagation_x 1) 2))\n(check-sat-using (then propagate-values smt))\n(get-value (propagation_x))\n(push 1)\n(assert (= propagation_x 2))\n(check-sat-using (then propagate-values smt))\n(pop 1)\n",
            "owned value propagation") {
            assert_eq!(reference, "sat ((propagation_x 1)) unsat");
        }
    }

    #[test]
    fn admitted_propagation_preserves_opaque_functions_binders_and_under_specified_terms() {
        let mut store = TermStore::new();
        store.register_declared_function("*");
        let x = store.mk_var("x", Sort::Int);
        let one = store.mk_int(1.into());
        let zero = store.mk_int(0.into());
        let definition = store.mk_app_structural(Symbol::named("="), &[x, one], Sort::Bool);
        let opaque = store.mk_app_structural(Symbol::named("*"), &[x, x], Sort::Int);
        let predicate = store.mk_app_structural(Symbol::named("="), &[opaque, zero], Sort::Bool);
        let division = store.mk_app_structural(Symbol::named("div"), &[one, zero], Sort::Int);
        let unspecified =
            store.mk_app_structural(Symbol::named("="), &[division, zero], Sort::Bool);
        let quantified = store.mk_forall(vec![("x".into(), Sort::Int)], definition);
        let owner = original(Arc::new(AtomicBool::new(false)));
        let result = apply(
            &mut store,
            vec![definition, predicate, unspecified, quantified],
            &owner,
        )
        .unwrap();
        assert!(result.contains(&definition));
        assert!(result.contains(&quantified));
        assert!(result.contains(&unspecified));
        let rebuilt = result
            .iter()
            .copied()
            .find(|&id| ![definition, quantified, unspecified].contains(&id))
            .unwrap();
        let TermData::App(_, args) = store.get(rebuilt) else {
            panic!("retained equality");
        };
        assert_eq!(
            store.get(args[0]),
            &TermData::App(Symbol::named("*"), vec![one, one])
        );
        assert!(!result
            .iter()
            .any(|&id| matches!(store.get(id), TermData::Const(Constant::Bool(false)))));
    }

    #[test]
    fn admitted_solve_eqs_then_propagation_keeps_reverse_model_reconstruction() {
        let mut solver = Solver::new(Logic::All);
        let x = solver.int_var("propagation_x");
        let one = solver.int_const(1);
        let sum = solver.add(x, one);
        let two = solver.int_const(2);
        let roots = [solver.eq(x, one), solver.eq(sum, two)];
        let result = solver
            .apply_tactic_subgoals_converted(
                &Tactic::SolveEqs.then(Tactic::PropagateValues),
                &roots,
                0,
                None,
            )
            .unwrap();
        assert!(result[0].formulas.is_empty());
        let model = solver
            .convert_tactic_model(
                result[0].model_converter.as_ref().unwrap(),
                &crate::api::Model::empty(),
            )
            .unwrap();
        assert_eq!(model.int_val("propagation_x"), Some(&1.into()));
    }

    #[test]
    fn admitted_propagation_cannot_retry_away_original_cancellation() {
        let mut store = TermStore::new();
        let p = store.mk_var("p", Sort::Bool);
        let stop = Arc::new(AtomicBool::new(false));
        let owner = original(Arc::clone(&stop));
        stop.store(true, Ordering::Relaxed);
        let count = store.len();
        assert!(apply(&mut store, vec![p], &owner).is_err());
        stop.store(false, Ordering::Relaxed);
        assert!(apply(&mut store, vec![p], &owner).is_err());
        assert_eq!(store.len(), count);
        assert_eq!(
            apply(&mut store, vec![p], &original(Arc::clone(&stop))).unwrap(),
            [p]
        );
    }

    #[test]
    fn admitted_propagation_folds_exact_rational_definers_and_consequences() {
        let mut solver = Solver::new(Logic::All);
        let x = solver.real_var("rational_x");
        let y = solver.real_var("rational_y");
        let third = solver.rational_const(1, 3);
        let sixth = solver.rational_const(1, 6);
        let half = solver.rational_const(1, 2);
        let sum = solver.add(third, sixth);
        let definition = solver.eq(x, sum);
        let dependent = solver.eq(y, x);
        let consequence = solver.eq(y, half);
        let mut roots = vec![definition, dependent, consequence];
        solver
            .apply_tactic_to_goal(&Tactic::PropagateValues, &mut roots)
            .unwrap();
        assert_eq!(roots.len(), 2);
        for (root, variable) in roots.iter().zip([x, y]) {
            let TermData::App(Symbol::Named(name), args) = solver.terms().get(root.id()) else {
                panic!("expected a retained rational defining equality");
            };
            assert_eq!(name, "=");
            assert!(args == &[variable.id(), half.id()] || args == &[half.id(), variable.id()]);
        }
        let contradictory = solver.neq(y, half);
        roots.push(contradictory);
        solver
            .apply_tactic_to_goal(&Tactic::PropagateValues, &mut roots)
            .unwrap();
        assert_eq!(roots.len(), 1);
        assert_eq!(
            solver.terms().get(roots[0].id()),
            &TermData::Const(Constant::Bool(false))
        );
        #[cfg(any(target_os = "macos", all(target_os = "linux", not(target_env = "uclibc"))))]
        if let Some(reference) = super::super::tactic_model::bounded_reference(
            "(set-logic QF_LRA)\n(declare-const rational_x Real)\n(declare-const rational_y Real)\n(assert (= rational_x (+ (/ 1 3) (/ 1 6))))\n(assert (= rational_y rational_x))\n(check-sat-using (then propagate-values smt))\n(push 1)\n(assert (distinct rational_y (/ 1 2)))\n(check-sat-using (then propagate-values smt))\n(pop 1)\n",
            "owned exact rational value propagation") {
            assert_eq!(reference, "sat unsat");
        }
    }

    #[test]
    fn admitted_propagation_folds_integer_definers_before_harvesting() {
        let mut solver = Solver::new(Logic::All);
        let x = solver.int_var("folded_x");
        let y = solver.int_var("folded_y");
        let one = solver.int_const(1);
        let two = solver.int_const(2);
        let sum = solver.add(one, one);
        let definition = solver.eq(x, sum);
        let dependent = solver.eq(y, x);
        let mut roots = vec![definition, dependent];
        solver
            .apply_tactic_to_goal(&Tactic::PropagateValues, &mut roots)
            .unwrap();
        assert_eq!(roots.len(), 2);
        // Counted rebuilding preserves the source argument order; the native
        // convenience equality constructor instead sorts its arguments.
        for (root, variable) in roots.iter().zip([x, y]) {
            let TermData::App(Symbol::Named(name), args) = solver.terms().get(root.id()) else {
                panic!("expected a retained defining equality");
            };
            assert_eq!(name, "=");
            assert!(args == &[variable.id(), two.id()] || args == &[two.id(), variable.id()]);
        }
    }

    #[test]
    fn admitted_literal_propagation_may_replace_a_whole_binder_without_rewriting_inside_it() {
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::Int);
        store.register_declared_function("predicate");
        let predicate = store.mk_app_structural(Symbol::named("predicate"), &[x], Sort::Bool);
        let quantified = store.mk_forall(vec![("x".into(), Sort::Int)], predicate);
        let opposite = store.mk_not(quantified);
        let owner = original(Arc::new(AtomicBool::new(false)));
        let result = apply(&mut store, vec![quantified, opposite], &owner).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(
            store.get(result[0]),
            &TermData::Const(Constant::Bool(false))
        );
        assert!(
            matches!(store.get(quantified), TermData::Forall(_, body, _) if *body == predicate)
        );
        assert_eq!(
            store.get(predicate),
            &TermData::App(Symbol::named("predicate"), vec![x])
        );
    }
}
