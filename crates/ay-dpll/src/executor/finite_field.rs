// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Bounded exact prime-field solving, before any theory abstraction.
mod frontend;
mod ideal;
mod linear;
mod quadratic;
mod univariate;
use super::{
    model::{EvalValue, FieldScalar, Model},
    Executor,
};
use crate::executor_types::{SolveResult, UnknownOrigin, UnknownReason};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, Proof, ProofStep, Sort, Symbol, TermData, TermId, TheoryLemmaKind};

// Private candidate plumbing for an already-owned tactic; no solve attempt.
pub(crate) use ideal::Candidate as TacticFieldCandidate;
pub(crate) fn tactic_ideal_candidate(
    terms: &ay_core::TermStore,
    roots: &[TermId],
    seen: &HashSet<TermId>,
    owner: &dyn ay_core::term::TermConstructionAdmission,
) -> Option<TacticFieldCandidate> {
    ideal::witness_admitted(terms, roots, seen, owner)
}

enum FieldCertificate {
    Linear(Vec<u32>),
    Quadratic,
    Univariate,
    Ideal,
    Exhaustive,
}

impl Executor {
    pub(super) fn evaluate_field_application(
        &self,
        model: &Model,
        term: TermId,
        name: &str,
        args: &[TermId],
    ) -> EvalValue {
        let Sort::FiniteField(field) = self.ctx.terms.sort(term) else {
            return EvalValue::Unknown;
        };
        if (name == "ff.neg" && args.len() != 1) || (name != "ff.neg" && args.len() < 2) {
            return EvalValue::Unknown;
        }
        let p = u64::from(field.modulus());
        let mut value = u64::from(name == "ff.mul");
        let mut weight = 1u64;
        for &a in args {
            if self.ctx.terms.sort(a) != self.ctx.terms.sort(term) {
                return EvalValue::Unknown;
            }
            let EvalValue::FiniteField { value: n, field: q } = self.evaluate_term(model, a) else {
                return EvalValue::Unknown;
            };
            let n = u64::from(n);
            if q != *field || n >= p {
                return EvalValue::Unknown;
            }
            value = match name {
                "ff.mul" => value * n % p,
                "ff.neg" => (p - n) % p,
                "ff.bitsum" => (value + weight * n) % p,
                "ff.add" => (value + n) % p,
                _ => return EvalValue::Unknown,
            };
            weight = weight * 2 % p;
        }
        let Ok(value) = u32::try_from(value) else {
            return EvalValue::Unknown;
        };
        EvalValue::FiniteField {
            value,
            field: *field,
        }
    }

    pub(in crate::executor) fn paid_public_problem_roots(
        &self,
    ) -> Result<frontend::ProblemRoots, UnknownOrigin> {
        frontend::public_problem_roots(self)
    }

    /// `None` means no field content. Any field-bearing unsupported query is
    /// intercepted and declined, never sent through the UF fallback.
    pub(super) fn try_finite_field(&mut self, roots: &[TermId]) -> Option<SolveResult> {
        let fence = frontend::Fence::capture(self);
        let available = ay_core::resource::current_guard().and_then(|guard| guard.remaining());
        let attempt = self.evaluation_attempt();
        let mut field_work = match attempt.borrow_field_work(available) {
            Ok(work) => work,
            Err(origin) => {
                self.last_model = None;
                self.record_unknown_from_origin(origin);
                return Some(SolveResult::Unknown);
            }
        };
        let mut owner = match super::model::CandidateOwner::capture(self) {
            Ok(owner) => owner,
            Err(origin) => {
                self.last_model = None;
                self.record_unknown_from_origin(origin);
                return Some(SolveResult::Unknown);
            }
        };
        // Nested completion/checker facilities inherit the same sticky
        // original callback; a consumed one-shot stop cannot revive fallback.
        let _nested = owner.enter_nested();
        let mut budget = field_work.budget();
        let plan = match frontend::inspect(self, roots, &fence, &mut owner, &mut budget) {
            Ok(frontend::Inspection::Free) => return None,
            Ok(frontend::Inspection::Field(plan)) => plan,
            Ok(frontend::Inspection::Unsupported) => {
                self.last_model = None;
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                return Some(SolveResult::Unknown);
            }
            Err(origin) => {
                self.last_model = None;
                self.record_unknown_from_origin(origin);
                return Some(SolveResult::Unknown);
            }
        };
        let frontend::Plan { seen, vars, count } = plan;
        self.last_model = None;
        self.last_unknown_reason = Some(UnknownReason::Incomplete);
        // Exact algebra precedes enumeration: a linear witness must not cost
        // one freshly prepared candidate per field element. Structural refusal
        // may still use the bounded exhaustive lane on the SAME remainder.
        'algebra: {
            let attempt = self.evaluation_attempt();
            let arena = match attempt.temporary_arena() {
                Ok(arena) => arena,
                Err(origin) => {
                    self.record_unknown_from_origin(origin);
                    return Some(SolveResult::Unknown);
                }
            };
            let mut ideal_bytes = 0usize;
            let candidate = linear::witness_with_progress(
                &self.ctx.terms,
                roots,
                &seen,
                &mut budget,
                &mut |work, bytes| {
                    owner.pay(work, 0).is_ok()
                        && self.poll_evaluation_stop().is_ok()
                        && arena
                            .check_usage(
                                self.ctx.terms.true_memory_bytes(),
                                bytes,
                                self.evaluation_term_memory_limit(),
                            )
                            .is_ok()
                },
            );
            if self.should_abort_theory_loop() {
                return Some(SolveResult::Unknown);
            }
            let candidate = match candidate {
                Some(linear::Candidate::Model(model)) => model,
                Some(linear::Candidate::Contradiction(multipliers)) => {
                    return Some(
                        self.check_field_refutation(
                            roots,
                            FieldCertificate::Linear(multipliers),
                            &mut budget,
                            &arena,
                            &mut owner,
                        )
                        .unwrap_or_else(|| {
                            let _ = self.should_abort_theory_loop();
                            SolveResult::Unknown
                        }),
                    );
                }
                None => {
                    // Structural affine refusal may reach the degree-two
                    // lane. Fuel, cancellation and arena refusals are sticky;
                    // this borrows the SAME counter and retained arena.
                    match quadratic::witness_with_progress(
                        &self.ctx.terms,
                        roots,
                        &seen,
                        &mut budget,
                        &mut |work, bytes| {
                            owner.pay(work, 0).is_ok()
                                && self.poll_evaluation_stop().is_ok()
                                && arena
                                    .check_usage(
                                        self.ctx.terms.true_memory_bytes(),
                                        bytes,
                                        self.evaluation_term_memory_limit(),
                                    )
                                    .is_ok()
                        },
                    ) {
                        Some(quadratic::Candidate::Model(model)) => model,
                        Some(quadratic::Candidate::Contradiction) => {
                            return Some(
                                self.check_field_refutation(
                                    roots,
                                    FieldCertificate::Quadratic,
                                    &mut budget,
                                    &arena,
                                    &mut owner,
                                )
                                .unwrap_or_else(|| {
                                    let _ = self.should_abort_theory_loop();
                                    SolveResult::Unknown
                                }),
                            )
                        }
                        None => match univariate::witness_with_progress(
                            &self.ctx.terms,
                            roots,
                            &seen,
                            &mut budget,
                            &mut |work, bytes| {
                                owner.pay(work, 0).is_ok()
                                    && self.poll_evaluation_stop().is_ok()
                                    && arena
                                        .check_usage(
                                            self.ctx.terms.true_memory_bytes(),
                                            bytes,
                                            self.evaluation_term_memory_limit(),
                                        )
                                        .is_ok()
                            },
                        ) {
                            Some(univariate::Candidate::Model(model)) => model,
                            Some(univariate::Candidate::Contradiction) => {
                                return Some(
                                    self.check_field_refutation(
                                        roots,
                                        FieldCertificate::Univariate,
                                        &mut budget,
                                        &arena,
                                        &mut owner,
                                    )
                                    .unwrap_or_else(|| {
                                        let _ = self.should_abort_theory_loop();
                                        SolveResult::Unknown
                                    }),
                                );
                            }
                            None => match ideal::witness_with_progress(
                                &self.ctx.terms,
                                roots,
                                &seen,
                                &mut budget,
                                &mut |work, bytes| {
                                    let Some(total) = ideal_bytes.checked_add(bytes) else {
                                        owner.refuse(UnknownOrigin::DeterministicResourceBudget);
                                        return false;
                                    };
                                    ideal_bytes = total;
                                    owner.pay(work, 0).is_ok()
                                        && self.poll_evaluation_stop().is_ok()
                                        && arena
                                            .check_usage(
                                                self.ctx.terms.true_memory_bytes(),
                                                ideal_bytes,
                                                self.evaluation_term_memory_limit(),
                                            )
                                            .is_ok()
                                },
                            ) {
                                Some(ideal::Candidate::Model(model)) => model,
                                Some(ideal::Candidate::Contradiction) => {
                                    return Some(
                                        self.check_field_refutation(
                                            roots,
                                            FieldCertificate::Ideal,
                                            &mut budget,
                                            &arena,
                                            &mut owner,
                                        )
                                        .unwrap_or_else(
                                            || {
                                                let _ = self.should_abort_theory_loop();
                                                SolveResult::Unknown
                                            },
                                        ),
                                    )
                                }
                                None => {
                                    if *budget == 0 {
                                        let origin = owner
                                            .refuse(UnknownOrigin::DeterministicResourceBudget);
                                        self.record_unknown_from_origin(origin);
                                    }
                                    if owner.poll().is_err() || count > 65536 {
                                        let _ = self.should_abort_theory_loop();
                                        return Some(SolveResult::Unknown);
                                    }
                                    break 'algebra;
                                }
                            },
                        },
                    }
                }
            };
            let mut rows = Vec::new();
            if frontend::reserve(&mut rows, candidate.len(), &mut owner, &mut budget).is_err() {
                let _ = self.should_abort_theory_loop();
                return Some(SolveResult::Unknown);
            }
            for (term, value, field) in candidate {
                if frontend::pay(&mut owner, &mut budget, 1, 0).is_err() {
                    let _ = self.should_abort_theory_loop();
                    return Some(SolveResult::Unknown);
                }
                rows.push((term, FieldScalar::Field { value, field }));
            }
            let Some(model) = self.make_field_model(&rows, &mut budget, &mut owner) else {
                let _ = self.should_abort_theory_loop();
                return Some(SolveResult::Unknown);
            };
            return Some(
                self.check_field_candidate(model, roots, &mut budget, &mut owner)
                    .unwrap_or_else(|| {
                        let _ = self.should_abort_theory_loop();
                        SolveResult::Unknown
                    }),
            );
        }
        for mut index in 0..count {
            if self.should_abort_theory_loop() {
                return Some(SolveResult::Unknown);
            }
            let mut rows = Vec::new();
            if frontend::reserve(&mut rows, vars.len(), &mut owner, &mut budget).is_err() {
                let _ = self.should_abort_theory_loop();
                return Some(SolveResult::Unknown);
            }
            for &(t, p) in &vars {
                if frontend::pay(&mut owner, &mut budget, 1, 0).is_err() {
                    let _ = self.should_abort_theory_loop();
                    return Some(SolveResult::Unknown);
                }
                let value = (index % p as usize) as u32;
                index /= p as usize;
                let scalar = if let Sort::FiniteField(field) = self.ctx.terms.sort(t) {
                    FieldScalar::Field {
                        value,
                        field: *field,
                    }
                } else {
                    FieldScalar::Bool(value != 0)
                };
                rows.push((t, scalar));
            }
            let Some(model) = self.make_field_model(&rows, &mut budget, &mut owner) else {
                let _ = self.should_abort_theory_loop();
                return Some(SolveResult::Unknown);
            };
            if let Some(result) = self.check_field_candidate(model, roots, &mut budget, &mut owner)
            {
                return Some(result);
            }
        }
        if self.should_abort_theory_loop() {
            return Some(SolveResult::Unknown);
        }
        let arena = match attempt.temporary_arena() {
            Ok(arena) => arena,
            Err(origin) => {
                self.record_unknown_from_origin(origin);
                return Some(SolveResult::Unknown);
            }
        };
        Some(
            self.check_field_refutation(
                roots,
                FieldCertificate::Exhaustive,
                &mut budget,
                &arena,
                &mut owner,
            )
            .unwrap_or_else(|| {
                let _ = self.should_abort_theory_loop();
                SolveResult::Unknown
            }),
        )
    }

    fn make_field_model(
        &self,
        rows: &[(TermId, FieldScalar)],
        budget: &mut usize,
        owner: &mut super::model::CandidateOwner,
    ) -> Option<Model> {
        let mut model = Model::empty();
        model.install_field_assignments(self, rows, &mut |work, bytes| {
            frontend::pay(owner, budget, work, bytes).is_ok()
        })?;
        Some(model)
    }

    fn field_refutation_from_literals(
        roots: &[TermId],
        clause: Vec<TermId>,
        kind: TheoryLemmaKind,
    ) -> Proof {
        Self::field_refutation_from_builder(roots, clause, |clause| ProofStep::TheoryLemma {
            theory: "FiniteField".into(),
            clause,
            farkas: None,
            kind,
            lia: None,
        })
    }

    fn field_refutation_from_builder(
        roots: &[TermId],
        clause: Vec<TermId>,
        initial: impl FnOnce(Vec<TermId>) -> ProofStep,
    ) -> Proof {
        let mut proof = Proof::new();
        proof.steps.reserve_exact(roots.len() * 2 + 1);
        let mut remaining = clause.clone();
        let mut prior = proof.add_step(initial(clause));
        for &root in roots {
            let assume = proof.add_assume(root, None);
            let _ = remaining.remove(0);
            prior = proof.add_resolution(remaining.clone(), root, assume, prior);
        }
        proof
    }

    fn check_field_refutation(
        &mut self,
        roots: &[TermId],
        certificate: FieldCertificate,
        budget: &mut usize,
        arena: &super::model::EvaluationArena,
        owner: &mut super::model::CandidateOwner,
    ) -> Option<SolveResult> {
        let pairs = roots.len().checked_mul(roots.len())?;
        frontend::pay(owner, budget, pairs, 0).ok()?;
        // Price the exact proof step vector and the bounded clause copies
        // before construction. Literal interning has its own priced growth.
        let n = roots.len();
        if matches!(&certificate, FieldCertificate::Linear(multipliers) if multipliers.len() != n)
            || u32::try_from(n).is_err()
        {
            return None;
        }
        let step_count = n.checked_mul(2)?.checked_add(1)?;
        u32::try_from(step_count).ok()?;
        let steps = step_count.checked_mul(std::mem::size_of::<ay_core::ProofStep>())?;
        let clauses = pairs
            .checked_add(n.checked_mul(2)?)?
            .checked_mul(std::mem::size_of::<TermId>())?;
        let mut retained = steps
            .checked_add(clauses)?
            .checked_add(match &certificate {
                FieldCertificate::Linear(_) => n.checked_mul(std::mem::size_of::<u32>())?,
                FieldCertificate::Quadratic
                | FieldCertificate::Univariate
                | FieldCertificate::Ideal
                | FieldCertificate::Exhaustive => 0,
            })?
            .checked_add("FiniteField".len())?;
        let source_bytes = self.ctx.terms.true_memory_bytes();
        let memory_limit = self.evaluation_term_memory_limit();
        arena
            .check_usage(source_bytes, retained, memory_limit)
            .ok()?;
        let attempt = self.evaluation_attempt();
        let stop = super::theories::FpStop::from_executor_for_term_construction(self);
        let mut clause = Vec::with_capacity(n);
        for &root in roots {
            let literal = self
                .ctx
                .terms
                .try_intern_with_progress(&TermData::Not(root), &Sort::Bool, &mut |work, bytes| {
                    if let Err(origin) = stop.check() {
                        attempt.record_stop(origin);
                        return false;
                    }
                    let Some(left) = budget.checked_sub(work) else {
                        *budget = 0;
                        owner.refuse(UnknownOrigin::DeterministicResourceBudget);
                        return false;
                    };
                    let Some(total) = retained.checked_add(bytes) else {
                        return false;
                    };
                    *budget = left;
                    retained = total;
                    if owner.pay(work, 0).is_err() {
                        return false;
                    }
                    arena
                        .check_usage(source_bytes, retained, memory_limit)
                        .is_ok()
                })
                .ok()?;
            clause.push(literal);
        }
        let proof = match certificate {
            FieldCertificate::Exhaustive => Self::field_refutation_from_literals(
                roots,
                clause,
                TheoryLemmaKind::FiniteFieldExhaustive,
            ),
            FieldCertificate::Ideal => Self::field_refutation_from_literals(
                roots,
                clause,
                TheoryLemmaKind::FiniteFieldIdeal,
            ),
            FieldCertificate::Univariate => Self::field_refutation_from_literals(
                roots,
                clause,
                TheoryLemmaKind::FiniteFieldUnivariate,
            ),
            FieldCertificate::Quadratic => Self::field_refutation_from_literals(
                roots,
                clause,
                TheoryLemmaKind::FiniteFieldQuadratic,
            ),
            FieldCertificate::Linear(multipliers)
                if n <= TheoryLemmaKind::MAX_FINITE_FIELD_LINEAR_ROWS =>
            {
                let mut wide = [0u32; TheoryLemmaKind::MAX_FINITE_FIELD_LINEAR_ROWS];
                wide[..n].copy_from_slice(&multipliers);
                let mut compact = [0u8; TheoryLemmaKind::MAX_FINITE_FIELD_LINEAR_ROWS];
                let compact_fits = compact.iter_mut().zip(wide).all(|(out, value)| {
                    if let Ok(value) = u8::try_from(value) {
                        *out = value;
                        true
                    } else {
                        false
                    }
                });
                let kind = if compact_fits {
                    TheoryLemmaKind::FiniteFieldLinear(compact)
                } else {
                    TheoryLemmaKind::FiniteFieldLinearWide(wide)
                };
                Self::field_refutation_from_literals(roots, clause, kind)
            }
            FieldCertificate::Linear(multipliers) => {
                Self::field_refutation_from_builder(roots, clause, |clause| {
                    ProofStep::FiniteFieldLinear {
                        clause,
                        multipliers,
                    }
                })
            }
        };
        let quality = ay_proof::check_proof_strict_with_context_and_progress(
            &proof,
            &self.ctx.terms,
            None,
            None,
            Some(roots),
            &mut |work, bytes| {
                let Some(left) = budget.checked_sub(work) else {
                    *budget = 0;
                    owner.refuse(UnknownOrigin::DeterministicResourceBudget);
                    return false;
                };
                let Some(total) = retained.checked_add(bytes) else {
                    return false;
                };
                *budget = left;
                retained = total;
                owner.pay(work, 0).is_ok()
                    && self.poll_evaluation_stop().is_ok()
                    && arena
                        .check_usage(source_bytes, retained, self.evaluation_term_memory_limit())
                        .is_ok()
            },
        )
        .ok()?;
        if !quality.is_complete() || self.should_abort_theory_loop() {
            return None;
        }
        self.last_proof = Some(proof);
        self.last_unknown_reason = None;
        Some(SolveResult::unsat())
    }
    // Both algorithms must reevaluate ORIGINAL roots before the unchanged
    // independent original-model gate can accept a SAT result.
    fn check_field_candidate(
        &mut self,
        mut model: Model,
        roots: &[TermId],
        budget: &mut usize,
        owner: &mut super::model::CandidateOwner,
    ) -> Option<SolveResult> {
        // Memoized producer arithmetic has its own cumulative visit budget.
        // SAT still passes the separate original-input BigInt model gate.
        let attempt = self.evaluation_attempt();
        let mut values = HashMap::default();
        model
            .visit_field_assignments(self, &mut |term, value| {
                if eval_pay(
                    budget,
                    &mut |work, bytes| owner.pay(work, bytes).is_ok(),
                    1,
                    0,
                )
                .is_none()
                    || reserve_eval_values(&mut values, budget, &attempt, &mut |work, bytes| {
                        owner.pay(work, bytes).is_ok()
                    })
                    .is_none()
                {
                    return false;
                }
                values.insert(term, value);
                true
            })
            .ok()?;
        let mut satisfied = true;
        for &root in roots {
            match eval(
                &self.ctx.terms,
                root,
                &mut values,
                budget,
                &attempt,
                &mut |work, bytes| owner.pay(work, bytes).is_ok(),
                0,
            ) {
                Some(EvalValue::Bool(true)) => {}
                Some(EvalValue::Bool(false)) => satisfied = false,
                _ => {
                    if *budget == 0 {
                        let origin = owner.refuse(UnknownOrigin::DeterministicResourceBudget);
                        self.record_unknown_from_origin(origin);
                    }
                    let _ = self.should_abort_theory_loop();
                    return Some(SolveResult::Unknown);
                }
            }
        }
        if self.should_abort_theory_loop() {
            return Some(SolveResult::Unknown);
        }
        if satisfied {
            // Reuse the source-bound completion planner for declarations
            // absent from these exact roots, before publishing the model.
            // Present search assignments are never overwritten.
            if !self.complete_field_output_model_before_seal(
                &mut model,
                roots,
                // Output-only declaration/default DATA is ordinary native
                // completion work, not the field algorithm's scalar ceiling.
                // It still polls/debits the SAME original Guard and arena.
                &mut |work, bytes| owner.pay(work, bytes).is_ok(),
            ) {
                let _ = self.should_abort_theory_loop();
                return Some(SolveResult::Unknown);
            }
            self.last_model = Some(model);
            self.last_unknown_reason = None;
            return Some(SolveResult::Sat);
        }
        None
    }
}

fn eval_pay(
    work: &mut usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
    amount: usize,
    bytes: usize,
) -> Option<()> {
    let Some(left) = work.checked_sub(amount) else {
        *work = 0;
        return None;
    };
    *work = left;
    progress(amount, bytes).then_some(())
}

fn reserve_eval_values(
    values: &mut HashMap<TermId, EvalValue>,
    work: &mut usize,
    attempt: &super::model::EvaluationAttempt,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<()> {
    if values.len() < values.capacity() {
        return Some(());
    }
    let target = values.capacity().checked_mul(2)?.max(8);
    let width = std::mem::size_of::<(TermId, EvalValue)>().checked_mul(8)?;
    let bytes = target.checked_mul(width)?.checked_add(4096)?;
    eval_pay(work, progress, values.len().checked_add(target)?, bytes)?;
    values
        .try_reserve(target.checked_sub(values.len())?)
        .map_err(|_| attempt.record_stop(UnknownOrigin::MemoryBudget))
        .ok()?;
    if values.capacity() > target {
        eval_pay(
            work,
            progress,
            0,
            (values.capacity() - target).checked_mul(width)?,
        )?;
    }
    Some(())
}

// Producer evaluator memoizes the immutable assignment and charges actual
// visits, including cache hits. Independent proof/model evaluators do not call it.
fn eval(
    terms: &ay_core::TermStore,
    t: TermId,
    values: &mut HashMap<TermId, EvalValue>,
    work: &mut usize,
    attempt: &super::model::EvaluationAttempt,
    poll: &mut dyn FnMut(usize, usize) -> bool,
    depth: usize,
) -> Option<EvalValue> {
    if depth > 128 {
        return None;
    }
    eval_pay(work, poll, 1, 0)?;
    if let Some(v) = values.get(&t) {
        return Some(v.clone());
    }
    // Borrow the already validated schema; never allocate an unpriced child-ID
    // vector merely to discover a wide application's arity.
    let small;
    let args: &[TermId] = match terms.get(t) {
        TermData::App(_, args) => args,
        TermData::Not(a) => std::slice::from_ref(a),
        TermData::Ite(c, a, b) => {
            small = [*c, *a, *b];
            &small
        }
        TermData::Const(_) | TermData::Var(..) => &[],
        _ => return None,
    };
    let bytes = args.len().checked_mul(std::mem::size_of::<EvalValue>())?;
    eval_pay(work, poll, args.len(), bytes)?;
    let mut children = Vec::new();
    children
        .try_reserve_exact(args.len())
        .map_err(|_| attempt.record_stop(UnknownOrigin::MemoryBudget))
        .ok()?;
    let excess = children
        .capacity()
        .checked_sub(args.len())?
        .checked_mul(std::mem::size_of::<EvalValue>())?;
    eval_pay(work, poll, 0, excess)?;
    for &a in args {
        children.push(eval(terms, a, values, work, attempt, poll, depth + 1)?);
    }
    fn boolean(v: &EvalValue) -> Option<bool> {
        if let EvalValue::Bool(b) = v {
            Some(*b)
        } else {
            None
        }
    }
    let value = match terms.get(t) {
        TermData::Const(Constant::Bool(b)) => EvalValue::Bool(*b),
        TermData::Const(Constant::FiniteField { value, field }) => EvalValue::FiniteField {
            value: *value,
            field: *field,
        },
        TermData::Not(_) => EvalValue::Bool(!boolean(&children[0])?),
        TermData::Ite(..) => {
            if boolean(&children[0])? {
                children[1].clone()
            } else {
                children[2].clone()
            }
        }
        TermData::App(Symbol::Named(n), _) => match n.as_str() {
            "not" => EvalValue::Bool(!boolean(&children[0])?),
            "and" | "or" | "xor" => {
                eval_pay(work, poll, children.len(), 0)?;
                let mut b = n == "and";
                for v in &children {
                    eval_pay(work, poll, 0, 0)?;
                    let v = boolean(v)?;
                    b = match n.as_str() {
                        "and" => b && v,
                        "or" => b || v,
                        _ => b ^ v,
                    };
                }
                EvalValue::Bool(b)
            }
            "=>" => EvalValue::Bool(!boolean(&children[0])? || boolean(&children[1])?),
            "=" => {
                eval_pay(work, poll, children.len(), 0)?;
                let first = children.first()?;
                let mut equal = true;
                for value in &children {
                    eval_pay(work, poll, 0, 0)?;
                    if value != first {
                        equal = false;
                        break;
                    }
                }
                EvalValue::Bool(equal)
            }
            "distinct" => {
                let comparisons = children.len().checked_mul(children.len().checked_sub(1)?)? / 2;
                eval_pay(work, poll, comparisons, 0)?;
                let mut distinct = true;
                'pairs: for i in 0..children.len() {
                    for j in 0..i {
                        eval_pay(work, poll, 0, 0)?;
                        if children[i] == children[j] {
                            distinct = false;
                            break 'pairs;
                        }
                    }
                }
                EvalValue::Bool(distinct)
            }
            "ff.add" | "ff.mul" | "ff.neg" | "ff.bitsum" => {
                eval_pay(work, poll, children.len(), 0)?;
                let Sort::FiniteField(field) = terms.sort(t) else {
                    return None;
                };
                let p = u64::from(field.modulus());
                let mut result = u64::from(n == "ff.mul");
                let mut weight = 1u64;
                for v in children {
                    eval_pay(work, poll, 0, 0)?;
                    let EvalValue::FiniteField { value, field: q } = v else {
                        return None;
                    };
                    let value = u64::from(value);
                    if q != *field || value >= p {
                        return None;
                    }
                    result = match n.as_str() {
                        "ff.mul" => result * value % p,
                        "ff.neg" => (p - value) % p,
                        "ff.bitsum" => (result + weight * value) % p,
                        _ => (result + value) % p,
                    };
                    weight = weight * 2 % p;
                }
                EvalValue::FiniteField {
                    value: u32::try_from(result).ok()?,
                    field: *field,
                }
            }
            _ => return None,
        },
        _ => return None,
    };
    reserve_eval_values(values, work, attempt, poll)?;
    values.insert(t, value.clone());
    Some(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn finite_field_admission_pays_wide_edges_and_skips_large_field_free_dags() {
        let mut executor = Executor::new();
        let t = executor.ctx.terms.mk_bool(true);
        let mut plain = t;
        for _ in 0..2048 {
            plain = executor
                .ctx
                .terms
                .mk_app(Symbol::named("and"), &[plain, t], Sort::Bool);
        }
        assert_eq!(executor.ctx.terms.finite_field_presence(plain), Some(false));
        assert!(executor.try_finite_field(&[plain]).is_none());
        let field = ay_core::FiniteFieldSort::new(7).unwrap();
        let x = executor.ctx.terms.mk_var("x", Sort::FiniteField(field));
        let args = vec![x; 5001];
        let sum = executor.ctx.terms.mk_ff_app("ff.add", &args).unwrap();
        let root = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), &[sum, x], Sort::Bool);
        assert_eq!(executor.try_finite_field(&[root]), Some(SolveResult::Sat));
        let model = executor.last_model.as_ref().unwrap();
        assert_eq!(executor.evaluate_term(model, root), EvalValue::Bool(true));
    }

    #[test]
    fn field_frontend_pays_many_equations_and_active_nodes_before_allocation() {
        let mut executor = Executor::new();
        let field = ay_core::FiniteFieldSort::new(65537).unwrap();
        let mut roots = Vec::new();
        for i in 0..350u32 {
            let x = executor
                .ctx
                .terms
                .mk_var(&format!("x{i}"), Sort::FiniteField(field));
            let value = executor.ctx.terms.mk_finite_field(i, field);
            roots.push(
                executor
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), &[x, value], Sort::Bool),
            );
        }
        assert_eq!(executor.try_finite_field(&roots), Some(SolveResult::Sat));
        let model = executor.last_model.as_ref().unwrap();
        for &root in &roots {
            assert_eq!(executor.evaluate_term(model, root), EvalValue::Bool(true));
        }
    }

    fn field_leaf_query(exec: &mut Executor) -> TermId {
        let field = ay_core::FiniteFieldSort::new(65537).unwrap();
        let x = exec.ctx.terms.mk_var("x", Sort::FiniteField(field));
        let zero = exec.ctx.terms.mk_finite_field(0, field);
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), &[x, zero], Sort::Bool)
    }

    #[test]
    fn field_frontend_original_stop_is_sticky_before_any_source_growth() {
        use std::sync::{
            atomic::{AtomicBool, Ordering},
            Arc,
        };
        let mut executor = Executor::new();
        let root = field_leaf_query(&mut executor);
        let stamp = executor.ctx.terms.snapshot_stamp();
        let stop = Arc::new(AtomicBool::new(true));
        let observed = Arc::clone(&stop);
        let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
            observed.swap(false, Ordering::SeqCst)
        }));
        assert!(executor.try_finite_field(&[root]).unwrap().is_unknown());
        assert!(!stop.load(Ordering::SeqCst));
        assert!(executor.try_finite_field(&[root]).unwrap().is_unknown());
        assert_eq!(executor.ctx.terms.snapshot_stamp(), stamp);
        assert!(executor.last_model.is_none());
        let mut fresh = Executor::new();
        let root = field_leaf_query(&mut fresh);
        assert_eq!(fresh.try_finite_field(&[root]), Some(SolveResult::Sat));
    }

    #[test]
    fn cheap_field_query_borrows_a_small_original_count_without_reserving_four_million() {
        let mut executor = Executor::new();
        let root = field_leaf_query(&mut executor);
        let guard = ay_core::resource::Guard::root_child(
            ay_core::resource::ChildSpec::new(ay_core::resource::NodeLabel::Check)
                .with_rlimit(Some(50_000)),
        );
        let _scope = guard.enter();
        assert_eq!(executor.try_finite_field(&[root]), Some(SolveResult::Sat));
        let left = guard.remaining().unwrap();
        assert!(left > 0 && left < 50_000);
    }

    #[test]
    fn field_frontend_original_memory_refusal_precedes_graph_allocation() {
        let mut executor = Executor::new();
        let root = field_leaf_query(&mut executor);
        let before = executor.ctx.terms.snapshot_stamp();
        executor.term_memory_limit = Some(0);
        assert!(executor.try_finite_field(&[root]).unwrap().is_unknown());
        executor.term_memory_limit = None;
        assert!(executor.try_finite_field(&[root]).unwrap().is_unknown());
        assert_eq!(executor.ctx.terms.snapshot_stamp(), before);
        assert!(executor.last_model.is_none());
    }

    #[test]
    fn field_frontend_rejects_mixed_domain_relations_and_arithmetic() {
        for arithmetic in [false, true] {
            let mut executor = Executor::new();
            let field = ay_core::FiniteFieldSort::new(7).unwrap();
            let other = ay_core::FiniteFieldSort::new(11).unwrap();
            let x = executor.ctx.terms.mk_var("x", Sort::FiniteField(field));
            let y = executor.ctx.terms.mk_var("y", Sort::FiniteField(other));
            let root = if arithmetic {
                let malformed = executor.ctx.terms.mk_app(
                    Symbol::named("ff.add"),
                    &[x, y],
                    Sort::FiniteField(field),
                );
                executor
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), &[malformed, x], Sort::Bool)
            } else {
                executor
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), &[x, y], Sort::Bool)
            };
            let before = executor.ctx.terms.snapshot_stamp();
            assert!(executor.try_finite_field(&[root]).unwrap().is_unknown());
            assert!(executor.last_model.is_none());
            assert_eq!(executor.ctx.terms.snapshot_stamp(), before);
        }
    }

    #[test]
    fn field_frontend_reader_cannot_authorize_mutating_proof_or_uf_fallback() {
        let mut executor = Executor::new();
        let root = field_leaf_query(&mut executor);
        executor.ctx.terms =
            ay_core::TermStore::from_entries(executor.ctx.terms.entries_snapshot(), None, None, 1);
        let before = executor.ctx.terms.snapshot_stamp();
        assert!(executor.try_finite_field(&[root]).unwrap().is_unknown());
        assert_eq!(executor.ctx.terms.snapshot_stamp(), before);
        assert!(executor.last_model.is_none());
    }
}
