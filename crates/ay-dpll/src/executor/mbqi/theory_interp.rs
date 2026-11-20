// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One typed native-theory interpretation proposal, never verdict authority.
//!
//! Signatures select elementary sequence operations. Authored equalities can
//! nominate scalar constants, sequence lengths and argument order. Every guess
//! still needs the caller's complete original-assertion validity check.

use super::super::model::{evaluation_copies, CertifiedExpressionBody};
use super::*;
use ay_frontend::CheckedProjectionBinding;
use num_traits::ToPrimitive;
use std::sync::Arc;

pub(super) struct Proposal {
    pub(super) assignment: HashMap<String, ConstInterpCandidate>,
    pub(super) witness: Vec<(CheckedProjectionBinding, CertifiedConstInterpWitness)>,
}

impl Executor {
    /// Check one complete program after the legacy candidate passes decline.
    /// There is no enlarged Cartesian family: all original obligations share
    /// one interpretation and one conjunction refutation under the same slice.
    pub(super) fn theory_program_interp_certificate(
        &mut self,
        snapshot: &[TermId],
        category: LogicCategory,
        mode: ConstInterpCertMode,
        deadline: ay_core::time::Instant,
        discharged: &mut HashMap<TermId, Option<super::super::unsat_cert::ProbeUnsatAuthority>>,
    ) -> Option<()> {
        let mut work = MAX_CONST_INTERP_SCAN_WORK;
        let partition = flatten_quantified_and_roots(&self.ctx.terms, snapshot);
        charge(self, &mut work, partition.len(), deadline)?;
        if partition.is_empty() {
            return None;
        }
        let mut heads = HashMap::default();
        let mut sources = Vec::new();
        let mut quantified = false;
        for &root in &partition {
            charge(self, &mut work, 1, deadline)?;
            let (body, binders) = match self.ctx.terms.get(root) {
                TermData::Forall(binders, body, _)
                    if !binders.is_empty()
                        && binders.len() <= MAX_CONST_INTERP_BINDERS
                        && binders.iter().all(|(_, sort)| {
                            matches!(sort, Sort::Int | Sort::Bool) || is_sequence(sort)
                        }) =>
                {
                    quantified = true;
                    (*body, binders.clone())
                }
                TermData::Forall(..) | TermData::Exists(..) => return None,
                _ => (root, Vec::new()),
            };
            if self.ctx.terms.sort(body) != &Sort::Bool
                || contains_quantifier(&self.ctx.terms, body)
            {
                return None;
            }
            let names: HashSet<_> = binders.iter().map(|(name, _)| name.clone()).collect();
            if names.len() != binders.len() {
                return None;
            }
            self.const_interp_scan_body(body, &names, &mut heads, &mut work)?;
            sources.push((body, binders));
        }
        if !quantified {
            return None;
        }
        const_interp_note(
            mode,
            &format!(
                "theory-program: scanned {} original conjuncts and {} heads",
                sources.len(),
                heads.len()
            ),
        );
        let mut heads: Vec<_> = heads.into_iter().collect();
        heads.sort_by(|left, right| left.0.cmp(&right.0));
        let declarations = self.ctx.bounded_projection_declaration_inventory_size()?;
        charge(self, &mut work, declarations, deadline)?;
        let mut bindings = Vec::new();
        for (name, (sort, arity)) in heads {
            charge(self, &mut work, arity.checked_add(name.len())?, deadline)?;
            let info = self.ctx.symbol_info_by_identity(&name)?;
            if arity > MAX_CONST_INTERP_BINDERS
                || info
                    .arg_sorts
                    .iter()
                    .any(|sort| !matches!(sort, Sort::Int | Sort::Bool) && !is_sequence(sort))
                || !matches!(&sort, Sort::Int | Sort::Bool)
                    && !is_sequence(&sort)
                    && !matches!(&sort, Sort::Array(array) if array.index_sort == Sort::Int && array.element_sort == Sort::Int)
            {
                return None;
            }
            let parameters = self.const_interp_witness_shape(&name, &sort, arity)?;
            bindings.push(
                self.ctx
                    .check_projection_declaration(&ay_frontend::ProjectionBindingRequest {
                        symbol: Symbol::named(name),
                        parameter_sorts: parameters.into_iter().map(|(_, sort)| sort).collect(),
                        result_sort: sort,
                    })
                    .ok()?,
            );
        }
        let proposal = build(self, &partition, bindings, &mut work, deadline)?;
        const_interp_note(
            mode,
            &format!(
                "theory-program: proposed {} model entries",
                proposal.witness.len()
            ),
        );
        let mut obligations = Vec::new();
        for (body, binders) in sources {
            charge(self, &mut work, binders.len().checked_add(1)?, deadline)?;
            let fresh: HashMap<_, _> = binders
                .into_iter()
                .map(|(name, sort)| {
                    let term = self.ctx.terms.mk_fresh_var("__ay_theory_validity", sort);
                    (name, term)
                })
                .collect();
            let instance = self.const_interp_beta_instance(body, &fresh, &proposal.assignment)?;
            match self.ctx.terms.get(instance) {
                TermData::Const(Constant::Bool(true)) => {}
                TermData::Const(Constant::Bool(false)) => return None,
                _ => obligations.push(instance),
            }
        }
        let conjunction = self.ctx.terms.mk_and(obligations);
        const_interp_note(
            mode,
            &format!("theory-program: checking complete obligation {conjunction:?}"),
        );
        if !matches!(
            self.ctx.terms.get(conjunction),
            TermData::Const(Constant::Bool(true))
        ) {
            charge(self, &mut work, 1, deadline)?;
            let class = match discharged.get(&conjunction) {
                Some(&cached) => cached,
                None => {
                    // Preserve the exact theorem as one complementary proof
                    // literal. The smart constructor applies De Morgan and
                    // would erase this root before the strict proof factory
                    // can bind its Assume to the complete source conjunction.
                    let negated = self.ctx.terms.mk_not_raw(conjunction);
                    let class = self.sat_authority_refutes(vec![negated], category, 2_000);
                    discharged.insert(conjunction, class);
                    class
                }
            }?;
            // The new sequence family must not turn a previously refused WP
            // model into a weaker discharged-trust grant. Existing candidate
            // families keep their original rigor policy unchanged.
            if class == super::super::unsat_cert::ProbeUnsatAuthority::DischargedTrust {
                return None;
            }
            const_interp_note(mode, "theory-program: complete obligation checked");
        }
        charge(self, &mut work, 1, deadline)?;
        match mode {
            ConstInterpCertMode::On => {
                self.install_const_interp_cert_witness(snapshot, proposal.witness, mode)?;
                self.book_trust_resting_certificate(false);
                Some(())
            }
            ConstInterpCertMode::Off | ConstInterpCertMode::Shadow => None,
        }
    }
}

fn charge(
    exec: &Executor,
    work: &mut u32,
    amount: usize,
    deadline: ay_core::time::Instant,
) -> Option<()> {
    if exec.external_stop_reason().is_some()
        || exec.poll_evaluation_stop().is_err()
        || exec.w4_budget_exhausted()
        || ay_core::time::Instant::now() >= deadline
        || !evaluation_copies::cells(amount)
    {
        return None;
    }
    *work = work.checked_sub(u32::try_from(amount).ok()?)?;
    Some(())
}

fn copy_integer(
    exec: &Executor,
    work: &mut u32,
    value: &num_bigint::BigInt,
    deadline: ay_core::time::Instant,
) -> Option<num_bigint::BigInt> {
    let bytes = usize::try_from(value.bits().div_ceil(64))
        .ok()?
        .checked_mul(8)?
        .checked_add(1)?;
    charge(exec, work, bytes, deadline)?;
    Some(value.clone())
}

pub(super) fn build(
    exec: &mut Executor,
    partition: &[TermId],
    heads: Vec<CheckedProjectionBinding>,
    work: &mut u32,
    deadline: ay_core::time::Instant,
) -> Option<Proposal> {
    charge(exec, work, heads.len().checked_mul(8)?, deadline)?;
    // This pass is for native sequence programs, not a wider Cartesian search.
    if !heads.iter().any(|head| {
        is_sequence(head.result_sort()) || head.parameter_sorts().iter().any(is_sequence)
    }) {
        return None;
    }
    let mut equations = Vec::new();
    for &root in partition {
        charge(exec, work, 1, deadline)?;
        if let TermData::App(operator, arguments) = exec.ctx.terms.get(root) {
            if operator.name() == "=" && arguments.len() == 2 {
                equations.push((arguments[0], arguments[1]));
            }
        }
    }
    // Only ground equalities nominate values. Inconsistency rejects this one
    // constant-function guess; it never establishes source infeasibility.
    let mut values = HashMap::default();
    for &(left, right) in &equations {
        for term in [left, right] {
            if let TermData::Const(Constant::Int(value)) = exec.ctx.terms.get(term) {
                values.insert(term, copy_integer(exec, work, value, deadline)?);
            }
        }
    }
    for _ in 0..=equations.len() {
        let mut changed = false;
        for &(left, right) in &equations {
            charge(exec, work, 2, deadline)?;
            let left_value = match values.get(&left) {
                Some(value) => Some(copy_integer(exec, work, value, deadline)?),
                None => None,
            };
            let right_value = match values.get(&right) {
                Some(value) => Some(copy_integer(exec, work, value, deadline)?),
                None => None,
            };
            match (left_value, right_value) {
                (Some(a), Some(b)) if a != b => return None,
                (Some(value), None) => {
                    values.insert(right, value);
                    changed = true;
                }
                (None, Some(value)) => {
                    values.insert(left, value);
                    changed = true;
                }
                _ => {}
            }
        }
        if !changed {
            break;
        }
    }
    let mut constants = HashMap::default();
    let mut lengths = HashMap::default();
    for (term, value) in values {
        charge(exec, work, 1, deadline)?;
        let (name, arguments): (&str, &[TermId]) = match exec.ctx.terms.get(term) {
            TermData::Var(name, _) => (name, &[]),
            TermData::App(Symbol::Named(name), arguments) => (name, arguments),
            _ => continue,
        };
        let Some(head) = heads.iter().find(|head| head.symbol().name() == name) else {
            continue;
        };
        if head.result_sort() != &Sort::Int {
            continue;
        }
        if matches!(head.parameter_sorts(), [sort] if is_sequence(sort)) {
            if let [argument] = arguments {
                if let TermData::Var(sequence, _) = exec.ctx.terms.get(*argument) {
                    let length = value.to_usize()?;
                    if lengths
                        .insert(sequence.to_string(), length)
                        .is_some_and(|old| old != length)
                    {
                        return None;
                    }
                }
            }
        } else {
            if constants.get(name).is_some_and(|old| old != &value) {
                return None;
            }
            charge(exec, work, name.len(), deadline)?;
            constants.insert(name.to_string(), value);
        }
    }
    let mut assignment = HashMap::default();
    let mut witness = Vec::new();
    for head in heads {
        charge(
            exec,
            work,
            head.parameter_sorts()
                .len()
                .checked_add(head.symbol().name().len())?,
            deadline,
        )?;
        let name = head.symbol().name().to_string();
        let result = head.result_sort().clone();
        let sorts = head.parameter_sorts();
        let candidate = if is_sequence(&result)
            || matches!((sorts, &result), ([s], Sort::Int) if is_sequence(s))
            || matches!((sorts, &result), ([s, element], Sort::Bool)
                if matches!(s, Sort::Seq(inner) if inner.as_ref() == element))
        {
            let parameters: Vec<_> = sorts
                .iter()
                .enumerate()
                .map(|(index, sort)| {
                    exec.ctx
                        .terms
                        .mk_fresh_var(&format!("__ay_theory_body!{index}"), sort.clone())
                })
                .collect();
            let body = match (sorts, &result) {
                ([a, b], Sort::Seq(_)) if a == &result && b == &result => exec.ctx.terms.mk_app(
                    Symbol::named("seq.++"),
                    [parameters[0], parameters[1]],
                    result.clone(),
                ),
                ([element], Sort::Seq(inner)) if element == inner.as_ref() => exec
                    .ctx
                    .terms
                    .mk_app(Symbol::named("seq.unit"), [parameters[0]], result.clone()),
                ([s, element], Sort::Seq(inner)) if s == &result && element == inner.as_ref() => {
                    let singleton = exec.ctx.terms.mk_app(
                        Symbol::named("seq.unit"),
                        [parameters[1]],
                        result.clone(),
                    );
                    let order = if front_definition(exec, partition, &name, work, deadline)? {
                        [singleton, parameters[0]]
                    } else {
                        [parameters[0], singleton]
                    };
                    exec.ctx
                        .terms
                        .mk_app(Symbol::named("seq.++"), order, result.clone())
                }
                ([s], Sort::Int) if is_sequence(s) => {
                    exec.ctx
                        .terms
                        .mk_app(Symbol::named("seq.len"), [parameters[0]], Sort::Int)
                }
                ([s, element], Sort::Bool) if matches!(s, Sort::Seq(inner) if inner.as_ref() == element) =>
                {
                    let singleton = exec.ctx.terms.mk_app(
                        Symbol::named("seq.unit"),
                        [parameters[1]],
                        s.clone(),
                    );
                    exec.ctx.terms.mk_app(
                        Symbol::named("seq.contains"),
                        [parameters[0], singleton],
                        Sort::Bool,
                    )
                }
                ([], Sort::Seq(element)) => {
                    let length = lengths.get(&name).copied().unwrap_or(0);
                    charge(exec, work, length, deadline)?;
                    let value = match element.as_ref() {
                        Sort::Int => exec.ctx.terms.mk_int(0.into()),
                        Sort::Bool => exec.ctx.terms.mk_bool(false),
                        _ => return None,
                    };
                    if length == 0 {
                        exec.ctx
                            .terms
                            .mk_app(Symbol::named("seq.empty"), [], result.clone())
                    } else {
                        let singleton = exec.ctx.terms.mk_app(
                            Symbol::named("seq.unit"),
                            [value],
                            result.clone(),
                        );
                        if length == 1 {
                            singleton
                        } else {
                            exec.ctx.terms.mk_app(
                                Symbol::named("seq.++"),
                                vec![singleton; length],
                                result.clone(),
                            )
                        }
                    }
                }
                _ => return None,
            };
            ConstInterpCandidate::Expression(Arc::new(CertifiedExpressionBody::capture(
                &exec.ctx, parameters, body,
            )?))
        } else {
            let value = if result == Sort::Int {
                exec.ctx
                    .terms
                    .mk_int(constants.remove(&name).unwrap_or_else(|| 0.into()))
            } else {
                *exec.const_interp_candidates(&result, 0)?.first()?
            };
            ConstInterpCandidate::Constant(value)
        };
        let body = match &candidate {
            ConstInterpCandidate::Constant(value) => CertifiedConstInterpWitness::Constant(*value),
            ConstInterpCandidate::Expression(body) => {
                CertifiedConstInterpWitness::Expression(Arc::clone(body))
            }
            ConstInterpCandidate::LinearInt(_) => return None,
        };
        assignment.insert(name, candidate);
        witness.push((head, body));
    }
    Some(Proposal {
        assignment,
        witness,
    })
}

fn is_sequence(sort: &Sort) -> bool {
    matches!(sort, Sort::Seq(element) if matches!(element.as_ref(), Sort::Int | Sort::Bool))
}

fn front_definition(
    exec: &Executor,
    partition: &[TermId],
    head: &str,
    work: &mut u32,
    deadline: ay_core::time::Instant,
) -> Option<bool> {
    for &root in partition {
        charge(exec, work, 1, deadline)?;
        let body = match exec.ctx.terms.get(root) {
            TermData::Forall(_, body, _) => *body,
            _ => continue,
        };
        let TermData::App(eq, sides) = exec.ctx.terms.get(body) else {
            continue;
        };
        if eq.name() != "=" || sides.len() != 2 {
            continue;
        }
        for (left, right) in [(sides[0], sides[1]), (sides[1], sides[0])] {
            let TermData::App(target, args) = exec.ctx.terms.get(left) else {
                continue;
            };
            if target.name() != head || args.len() != 2 {
                continue;
            }
            let TermData::App(_, parts) = exec.ctx.terms.get(right) else {
                continue;
            };
            if parts.len() != 2 || parts[1] != args[0] {
                continue;
            }
            let TermData::App(_, singleton) = exec.ctx.terms.get(parts[0]) else {
                continue;
            };
            if singleton.as_slice() == [args[1]] {
                return Some(true);
            }
        }
    }
    Some(false)
}

#[cfg(test)]
mod tests;
