// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A separate original-sort query, copied once modulo injective Bool renaming.
//! No transformed arithmetic or circuit clause is a source proof premise.

use super::*;

pub(super) struct SourceQuery {
    pub(super) solver: Solver,
    mapping: Vec<Option<Term>>,
}

impl SourceQuery {
    /// Exactly one independent checked original-sort decision after circuit exhaustion.
    pub(super) fn finish(
        &mut self,
        owner: &CountedAdmission,
        report: &mut EnumerationCommon,
    ) -> Result<()> {
        owner.check()?;
        if report.statistics.final_source_solve_calls != 0 {
            return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
        }
        report.statistics.final_source_solve_calls = 1;
        let started = Instant::now();
        let decision = self.solver.try_check_sat();
        let proof = if decision.as_ref().is_ok_and(|result| result.is_unsat()) {
            match self.solver.export_last_unsat_artifact() {
                Some(proof) => match proof.accept_for_consumer(ProofAcceptanceMode::Strict) {
                    Ok(()) => Some(proof),
                    Err(error) => {
                        report.diagnostic = Some(error.to_string());
                        None
                    }
                },
                None => {
                    report.diagnostic = Some(
                        "terminal source solve supplied no strict completeness artifact".into(),
                    );
                    None
                }
            }
        } else {
            None
        };
        report.statistics.final_source_work = self.solver.executor.rlimit_work_total();
        report.statistics.final_source_micros =
            u64::try_from(started.elapsed().as_micros()).unwrap_or(u64::MAX);
        owner.check()?;
        if let Some(proof) = proof {
            report.completeness_proof = Some(proof);
            report.outcome = Outcome::Exhaustive;
        } else if decision.as_ref().is_ok_and(|result| result.is_sat()) {
            report.diagnostic = Some("candidate circuit exhausted while the original source plus projection blockers remains satisfiable".into());
            report.outcome = Outcome::Incomplete(UnknownReason::SelfCheckRejected);
        } else {
            if let Err(error) = &decision {
                report.diagnostic = Some(error.to_string());
            } else if let Some(detail) = self.solver.executor.unknown_detail() {
                report.diagnostic = Some(detail.to_owned());
            }
            report.outcome = Outcome::Incomplete(self.solver.unknown_reason().unwrap_or(
                if decision.is_err() {
                    UnknownReason::InternalError
                } else {
                    UnknownReason::ProofTrusted
                },
            ));
        }
        Ok(())
    }

    pub(super) fn block(
        &mut self,
        projection: &[TermId],
        values: &[Scalar],
        owner: &CountedAdmission,
    ) -> Result<()> {
        if projection.len() != values.len() {
            return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
        }
        let mut disjunction = Vec::new();
        reserve(&mut disjunction, projection.len(), owner)?;
        for (&original, value) in projection.iter().zip(values) {
            owner.admit(1, std::mem::size_of::<TermData>())?;
            let copied = self
                .mapping
                .get(original.index())
                .copied()
                .flatten()
                .ok_or(Failure::Incomplete(UnknownReason::SelfCheckRejected))?;
            let excluded = match value {
                Scalar::Bool(value) if self.solver.terms().sort(copied.id()) == &Sort::Bool => {
                    if *value {
                        self.solver.try_not(copied)?
                    } else {
                        copied
                    }
                }
                Scalar::Int(value) if self.solver.terms().sort(copied.id()) == &Sort::Int => {
                    let bytes = usize::try_from(value.bits().div_ceil(8))
                        .ok()
                        .and_then(|bytes| bytes.checked_add(std::mem::size_of::<TermData>() * 3))
                        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
                    owner.admit(bytes, bytes)?;
                    let literal = self.solver.int_const_bigint(value);
                    let equal = self.solver.try_eq(copied, literal)?;
                    self.solver.try_not(equal)?
                }
                _ => return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected)),
            };
            disjunction.push(excluded);
        }
        owner.admit(
            disjunction.len().saturating_add(1),
            std::mem::size_of::<TermData>(),
        )?;
        let blocker = self.solver.try_or_many(&disjunction)?;
        self.solver.try_assert_term(blocker)?;
        owner.check()?;
        Ok(())
    }
}

pub(super) fn copy(
    original: &TermStore,
    roots: &[TermId],
    compiled: &Compiled,
    owner: &CountedAdmission,
) -> Result<SourceQuery> {
    if !compiled.matches_source(original, roots) {
        return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
    }
    owner.admit(1, std::mem::size_of::<Solver>())?;
    let mut solver = Solver::try_new(Logic::All)?;
    let mut mapping = Vec::new();
    reserve(&mut mapping, original.len(), owner)?;
    mapping.resize(original.len(), None);
    for &id in &compiled.source_order {
        owner.admit(1, std::mem::size_of::<TermData>())?;
        let mapped = |child: TermId| -> Result<Term> {
            mapping
                .get(child.index())
                .copied()
                .flatten()
                .ok_or(Failure::Incomplete(UnknownReason::SelfCheckRejected))
        };
        let copied = match original.get(id) {
            TermData::Const(Constant::Bool(value)) => solver.bool_const(*value),
            TermData::Const(Constant::Int(value)) => {
                let bytes = usize::try_from(value.bits().div_ceil(8))
                    .ok()
                    .and_then(|bytes| bytes.checked_add(std::mem::size_of_val(value)))
                    .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
                owner.admit(bytes, bytes)?;
                solver.int_const_bigint(value)
            }
            TermData::Var(_, _) if matches!(original.sort(id), Sort::Bool | Sort::Int) => {
                // One private declaration per original node. Original source
                // spelling is irrelevant; this is an injective alpha-renaming.
                let name = ay_core::render_admission::format(
                    Some(owner),
                    format_args!("enum_source_{}", id.0),
                );
                owner.check()?;
                solver.try_declare_const(&name, original.sort(id).clone())?
            }
            TermData::Not(child) => {
                let copied = solver.terms_mut().mk_not_raw(mapped(*child)?.id());
                solver.wrap_term(copied)
            }
            TermData::Ite(condition, yes, no) => {
                let copied = solver.terms_mut().mk_ite_raw(
                    mapped(*condition)?.id(),
                    mapped(*yes)?.id(),
                    mapped(*no)?.id(),
                );
                solver.wrap_term(copied)
            }
            TermData::App(Symbol::Named(name), arguments)
                if !original.is_declared_function(name) =>
            {
                // The compiler has already checked this closed vocabulary's
                // exact scalar signatures. Preserve the ORIGINAL operator,
                // sort, arity and child order, not its finite-width lowering.
                let mut children = Vec::new();
                reserve(&mut children, arguments.len(), owner)?;
                for &child in arguments {
                    owner.admit(1, 0)?;
                    children.push(mapped(child)?.id());
                }
                owner.admit(name.len(), name.len())?;
                let copied = solver.terms_mut().mk_app(
                    Symbol::named(name.as_str()),
                    children,
                    original.sort(id).clone(),
                );
                solver.wrap_term(copied)
            }
            _ => return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected)),
        };
        if solver.terms().sort(copied.id()) != original.sort(id) {
            return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
        }
        mapping[id.index()] = Some(copied);
    }
    for &root in roots {
        owner.admit(1, 0)?;
        let copied = mapping
            .get(root.index())
            .copied()
            .flatten()
            .ok_or(Failure::Incomplete(UnknownReason::SelfCheckRejected))?;
        solver.try_assert_term(copied)?;
    }
    authenticate_copy(original, roots, compiled, &solver, &mapping, owner)?;
    owner.check()?;
    Ok(SourceQuery { solver, mapping })
}

/// Check the original-sort alpha-renaming independently of its construction.
/// No transformed finite-width term is a premise of the terminal source proof.
fn authenticate_copy(
    original: &TermStore,
    roots: &[TermId],
    compiled: &Compiled,
    solver: &Solver,
    mapping: &[Option<Term>],
    owner: &CountedAdmission,
) -> Result<()> {
    let rejected = || Failure::Incomplete(UnknownReason::SelfCheckRejected);
    let mapped = |id: TermId| -> Result<TermId> {
        let term = mapping
            .get(id.index())
            .copied()
            .flatten()
            .ok_or_else(rejected)?;
        solver.resolve_term(OPERATION, term).map_err(Failure::Api)
    };
    for &id in &compiled.source_order {
        owner.admit(1, 0)?;
        let copied = mapped(id)?;
        if original.sort(id) != solver.terms().sort(copied) {
            return Err(rejected());
        }
        let same = match (original.get(id), solver.terms().get(copied)) {
            (TermData::Const(Constant::Bool(a)), TermData::Const(Constant::Bool(b))) => a == b,
            (TermData::Const(Constant::Int(a)), TermData::Const(Constant::Int(b))) => {
                owner.admit(
                    usize::try_from(a.bits().max(b.bits()).div_ceil(64)).map_err(|_| rejected())?,
                    0,
                )?;
                a == b
            }
            (TermData::Var(..), TermData::Var(name, _)) => {
                let expected = ay_core::render_admission::format(
                    Some(owner),
                    format_args!("enum_source_{}", id.0),
                );
                owner.check()?;
                matches!(original.sort(id), Sort::Bool | Sort::Int) && *name == expected
            }
            (TermData::Not(a), TermData::Not(b)) => mapped(*a)? == *b,
            (TermData::Ite(a, b, c), TermData::Ite(x, y, z)) => {
                mapped(*a)? == *x && mapped(*b)? == *y && mapped(*c)? == *z
            }
            (TermData::App(a, args), TermData::App(b, copied_args)) => {
                owner.admit(args.len(), 0)?;
                if a != b || args.len() != copied_args.len() {
                    false
                } else {
                    let mut equal = true;
                    for (&argument, &copied_arg) in args.iter().zip(copied_args) {
                        equal &= mapped(argument)? == copied_arg;
                    }
                    equal
                }
            }
            _ => false,
        };
        if !same {
            return Err(rejected());
        }
    }
    if roots.len() != solver.executor.ctx.assertions.len() {
        return Err(rejected());
    }
    for (&root, &assertion) in roots.iter().zip(&solver.executor.ctx.assertions) {
        owner.admit(1, 0)?;
        if mapped(root)? != assertion {
            return Err(rejected());
        }
    }
    owner.check()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn original_source_copy_preserves_raw_nodes_and_rejects_alias_or_missing_assertion() {
        let mut original = Solver::try_new(Logic::QfUf).unwrap();
        let p = original.try_declare_const("p", Sort::Bool).unwrap();
        let q = original.try_declare_const("q", Sort::Bool).unwrap();
        let negative = original.terms_mut().mk_not_raw(p.id());
        let double = original.terms_mut().mk_not_raw(negative);
        let truth = original.bool_const(true);
        let expression = original
            .terms_mut()
            .mk_ite_raw(truth.id(), p.id(), negative);
        let double = original.wrap_term(double);
        original.try_assert_term(double).unwrap();
        original.try_assert_term(q).unwrap();
        let roots = original.executor.ctx.assertions.clone();
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 1 << 30),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        let compiled =
            finite_bool::compile(original.terms(), &roots, &[expression], &owner).unwrap();
        let mut source = copy(original.terms(), &roots, &compiled, &owner).unwrap();
        let copied_expression = source.mapping[expression.index()].unwrap();
        assert!(matches!(
            source.solver.terms().get(copied_expression.id()),
            TermData::Ite(..)
        ));
        let copied_double = source.mapping[double.id().index()].unwrap();
        assert!(matches!(
            source.solver.terms().get(copied_double.id()),
            TermData::Not(_)
        ));
        let saved_q = source.mapping[q.id().index()];
        source.mapping[q.id().index()] = source.mapping[p.id().index()];
        assert!(matches!(
            authenticate_copy(
                original.terms(),
                &roots,
                &compiled,
                &source.solver,
                &source.mapping,
                &owner
            ),
            Err(Failure::Incomplete(UnknownReason::SelfCheckRejected))
        ));
        source.mapping[q.id().index()] = saved_q;
        source.solver.executor.ctx.assertions.pop();
        assert!(matches!(
            authenticate_copy(
                original.terms(),
                &roots,
                &compiled,
                &source.solver,
                &source.mapping,
                &owner
            ),
            Err(Failure::Incomplete(UnknownReason::SelfCheckRejected))
        ));
    }
}
