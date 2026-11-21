// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked consequences of exact native ITE assertions. Preprocessing hints
//! select no authority: the existing ITE/EUF/Boolean emitter must derive the
//! complete target unit, and the ordinary strict scope check commits the proof.

use super::*;
use ay_proof::{ProofCheckError, ProofQuality};

mod budget;
mod conjunct_leaves;
mod failure;
mod integer_leaves;
mod projection;

use budget::RepairBudget;

const MAX_NATIVE_ROOTS: usize = 64;
const MAX_NATIVE_ATTEMPTS: usize = 8;
const MAX_NATIVE_TERM_OCCURRENCES: usize = 4096;
const MAX_NATIVE_DEPTH: usize = 64;
const MAX_NATIVE_PAYLOAD: usize = 65_536;
// One shared attempt counter admits at most eight emitter invocations across
// every source/target pair. Each closer receives at most 20k steps, so the
// cumulative closer allowance is at most 160k, never reset per source.
const MAX_NATIVE_CLOSURE_STEPS: u64 = 20_000;
const MAX_NATIVE_TOTAL_CLOSURE_STEPS: u64 = 160_000;

/// Diagnostic-only, bounded independently of producer-owned error strings.
/// Never format the complete error, a rule payload, or any proof term.
fn strict_result_note(checked: &Result<ProofQuality, ProofCheckError>) -> String {
    match checked {
        Ok(quality) => format!(
            "strict_result=quality total={} assume={} resolution={} theory={} trust={} \
             trust_fallback={} hole={} drup={} th_resolution={} other={}",
            quality.total_steps,
            quality.assume_count,
            quality.resolution_count,
            quality.theory_lemma_count,
            quality.trust_count,
            quality.trust_fallback_count,
            quality.hole_count,
            quality.drup_count,
            quality.th_resolution_count,
            quality.other_rule_count,
        ),
        Err(error) => {
            use ProofCheckError::*;
            let (kind, step, premise, term, detail) = match error {
                ResourceLimit => ("resource-limit", None, None, None, ""),
                Cancelled => ("cancelled", None, None, None, ""),
                EmptyProof => ("empty-proof", None, None, None, ""),
                BundleSchemaMismatch { .. } => ("bundle-schema", None, None, None, ""),
                MalformedProofBundle { reason } => {
                    ("malformed-bundle", None, None, None, reason.as_str())
                }
                InvalidDatatypeSignatureContext { reason } => {
                    ("datatype-signature", None, None, None, reason.as_str())
                }
                UnauthorizedAssumption { step, term } => {
                    ("unauthorized-assume", Some(*step), None, Some(*term), "")
                }
                NoClauseProducingSteps => ("no-clause", None, None, None, ""),
                MissingPremise { step, premise } => {
                    ("missing-premise", Some(*step), Some(*premise), None, "")
                }
                NonPriorPremise { step, premise } => {
                    ("non-prior-premise", Some(*step), Some(*premise), None, "")
                }
                PremiseHasNoClause { step, premise } => (
                    "premise-without-clause",
                    Some(*step),
                    Some(*premise),
                    None,
                    "",
                ),
                InvalidResolution { step, rule } => {
                    ("invalid-resolution", Some(*step), None, None, rule.as_str())
                }
                InvalidDrup { step } => ("invalid-drup", Some(*step), None, None, ""),
                HoleStep { step } => ("hole", Some(*step), None, None, ""),
                UnsupportedResolutionArity { step, rule, .. } => {
                    ("resolution-arity", Some(*step), None, None, rule.as_str())
                }
                MalformedResolutionArgs { step, rule, .. } => {
                    ("resolution-args", Some(*step), None, None, rule.as_str())
                }
                FinalClauseNotEmpty { step } => ("nonempty-final", Some(*step), None, None, ""),
                TrustStep { step } => ("trust", Some(*step), None, None, ""),
                UnvalidatedRule { step, rule } => {
                    ("unvalidated-rule", Some(*step), None, None, rule.as_str())
                }
                UnsupportedTheoryLemmaKind { step, .. } => {
                    ("unsupported-theory", Some(*step), None, None, "")
                }
                InvalidTheoryLemma { step, reason } => {
                    ("invalid-theory", Some(*step), None, None, reason.as_str())
                }
                InvalidBooleanRule { step, reason, .. } => {
                    ("invalid-boolean", Some(*step), None, None, reason.as_str())
                }
                StrictProofModeTrust { reason } => {
                    ("strict-trust", None, None, None, reason.as_str())
                }
                _ => ("unrecognized-error", None, None, None, ""),
            };
            // Back up at most three bytes; no scan or copy of the omitted
            // suffix. Debug quoting escapes newlines within the fixed prefix.
            let mut end = detail.len().min(160);
            while !detail.is_char_boundary(end) {
                end -= 1;
            }
            format!(
                "strict_result=error kind={kind} step={step:?} premise={premise:?} \
                 term={term:?} detail={:?} detail_truncated={}",
                &detail[..end],
                end < detail.len(),
            )
        }
    }
}

/// Preflight before any recursive substitution, constructor normalization,
/// payload clone, or canonical rendering. Count occurrences, not unique IDs:
/// forged cyclic and exponentially shared public DAGs cannot evade the bound.
#[cfg(test)]
fn admit_terms(exec: &Executor, roots: &[TermId]) -> Option<()> {
    let mut remaining = MAX_NATIVE_TERM_OCCURRENCES;
    admit_terms_with_remaining(exec, roots, &mut remaining, None).map(|_| ())
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AdmittedItes {
    Absent,
    BooleanOnly,
    Term,
}

fn admit_terms_with_remaining(
    exec: &Executor,
    roots: &[TermId],
    remaining: &mut usize,
    budget: Option<&RepairBudget>,
) -> Option<AdmittedItes> {
    if roots.len() > *remaining {
        *remaining = 0;
        return None;
    }
    let terms = &exec.ctx.terms;
    let mut stack = Vec::new();
    if let Some(budget) = budget {
        budget.reserve(&mut stack, roots.len())?;
    }
    stack.extend(roots.iter().map(|&term| (term, 0usize)));
    let mut has_ite = false;
    let mut has_term_ite = false;
    while let Some((term, depth)) = stack.pop() {
        *remaining = remaining.checked_sub(1)?;
        if budget.is_some_and(|budget| !budget.pay(1, 0)) {
            return None;
        }
        if depth > MAX_NATIVE_DEPTH || terms.entry_stamp(term).is_none() {
            return None;
        }
        match terms.sort(term) {
            Sort::Bool | Sort::Int => {}
            Sort::Uninterpreted(name) if name.len() <= 256 => {}
            _ => return None,
        }
        let children: &[TermId] = match terms.get(term) {
            TermData::Const(Constant::Bool(_)) => &[],
            TermData::Const(Constant::Int(value)) if value.bits() <= 128 => &[],
            TermData::Var(name, _) if name.len() <= 256 => &[],
            TermData::Not(inner) if terms.sort(term) == &Sort::Bool => {
                if inner.0 >= term.0
                    || terms.entry_stamp(*inner).is_none()
                    || terms.sort(*inner) != &Sort::Bool
                {
                    return None;
                }
                std::slice::from_ref(inner)
            }
            TermData::Ite(cond, left, right) => {
                has_ite = true;
                has_term_ite |= terms.sort(term) != &Sort::Bool;
                for child in [cond, left, right] {
                    if child.0 >= term.0 {
                        return None;
                    }
                    terms.entry_stamp(*child)?;
                }
                if terms.sort(*cond) != &Sort::Bool
                    || terms.sort(*left) != terms.sort(term)
                    || terms.sort(*right) != terms.sort(term)
                {
                    return None;
                }
                if stack.len().checked_add(3)? > *remaining {
                    *remaining = 0;
                    return None;
                }
                if let Some(budget) = budget {
                    budget.reserve(&mut stack, 3)?;
                }
                stack.extend([(*cond, depth + 1), (*left, depth + 1), (*right, depth + 1)]);
                continue;
            }
            TermData::App(Symbol::Named(name), args) if name.len() <= 256 && args.len() <= 64 => {
                if budget.is_some_and(|budget| !budget.pay(args.len(), 0)) {
                    return None;
                }
                for &arg in args {
                    if arg.0 >= term.0 {
                        return None;
                    }
                    terms.entry_stamp(arg)?;
                    // Unknown-function signature lookup below copies Sorts.
                    // Admit every raw sort before that first owned copy.
                    match terms.sort(arg) {
                        Sort::Bool | Sort::Int => {}
                        Sort::Uninterpreted(name) if name.len() <= 256 => {}
                        _ => return None,
                    }
                }
                let all = |sort: &Sort| args.iter().all(|&arg| terms.sort(arg) == sort);
                let typed = match name.as_str() {
                    "and" | "or" => {
                        terms.sort(term) == &Sort::Bool && !args.is_empty() && all(&Sort::Bool)
                    }
                    "=" => {
                        args.len() == 2
                            && terms.sort(term) == &Sort::Bool
                            && terms.sort(args[0]) == terms.sort(args[1])
                    }
                    "+" | "*" => {
                        terms.sort(term) == &Sort::Int && !args.is_empty() && all(&Sort::Int)
                    }
                    "-" => {
                        terms.sort(term) == &Sort::Int
                            && matches!(args.len(), 1 | 2)
                            && all(&Sort::Int)
                    }
                    "<" | "<=" | ">" | ">=" => {
                        terms.sort(term) == &Sort::Bool && args.len() == 2 && all(&Sort::Int)
                    }
                    _ => {
                        if let Some(budget) = budget {
                            let bytes =
                                args.len().checked_mul(std::mem::size_of::<Sort>() + 256)?;
                            if !budget.pay(args.len(), bytes) {
                                return None;
                            }
                        }
                        let sorts: Vec<_> =
                            args.iter().map(|&arg| terms.sort(arg).clone()).collect();
                        exec.ctx
                            .has_symbol_with_signature(name, &sorts, terms.sort(term))
                    }
                };
                if !typed {
                    return None;
                }
                args
            }
            _ => return None,
        };
        if stack.len().checked_add(children.len())? > *remaining {
            *remaining = 0;
            return None;
        }
        if let Some(budget) = budget {
            budget.reserve(&mut stack, children.len())?;
        }
        stack.extend(children.iter().map(|&child| (child, depth + 1)));
    }
    Some(if has_term_ite {
        AdmittedItes::Term
    } else if has_ite {
        AdmittedItes::BooleanOnly
    } else {
        AdmittedItes::Absent
    })
}

/// Only the exact original ground DAGs passed to the emitter need its grammar.
/// Other original roots still belong to the frozen authority window. Share the
/// existing occurrence allowance across every scan, including declined roots,
/// and retain only the first occurrence of each exact source TermId.
struct NativeIteSource {
    plan: LiftPlan,
    contents: AdmittedItes,
}

fn select_ite_sources(
    exec: &Executor,
    roots: &[TermId],
    budget: &RepairBudget,
) -> Option<Vec<NativeIteSource>> {
    let mut remaining = MAX_NATIVE_TERM_OCCURRENCES;
    let mut seen = Vec::new();
    let mut sources = Vec::new();
    let mut path = Vec::new();
    budget.reserve(&mut path, MAX_NATIVE_DEPTH)?;
    for &root in roots {
        select_ite_descendants(
            exec,
            root,
            root,
            &mut path,
            &mut seen,
            &mut sources,
            &mut remaining,
            budget,
        )?;
    }
    Some(sources)
}

/// Wide positive Boolean conjunctions are structural source containers, not
/// emitter operands. Admit their physical edges before visiting children; a
/// selected child is reached ONLY by checked AndPos/resolution from its exact
/// immutable root. The emitter's existing arity/grammar bounds stay unchanged.
fn select_ite_descendants(
    exec: &Executor,
    root: TermId,
    current: TermId,
    path: &mut Vec<conjunct_leaves::Edge>,
    seen: &mut Vec<TermId>,
    sources: &mut Vec<NativeIteSource>,
    remaining: &mut usize,
    budget: &RepairBudget,
) -> Option<()> {
    *remaining = remaining.checked_sub(1)?;
    if !budget.pay(1, 0)
        || path.len() > MAX_NATIVE_DEPTH
        || exec.ctx.terms.entry_stamp(current).is_none()
        || exec.ctx.terms.sort(current) != &Sort::Bool
    {
        return None;
    }
    if let TermData::App(Symbol::Named(name), children) = exec.ctx.terms.get(current) {
        if name == "and" && !children.is_empty() {
            if children.len() > *remaining || !budget.pay(children.len(), 0) {
                return None;
            }
            for &child in children {
                if child.0 >= current.0
                    || exec.ctx.terms.entry_stamp(child).is_none()
                    || exec.ctx.terms.sort(child) != &Sort::Bool
                {
                    return None;
                }
            }
            for (position, &child) in children.iter().enumerate() {
                if path.len() == MAX_NATIVE_DEPTH {
                    return None;
                }
                path.push((current, u32::try_from(position).ok()?, child));
                select_ite_descendants(exec, root, child, path, seen, sources, remaining, budget)?;
                path.pop();
            }
            return Some(());
        }
    }
    if !budget.pay(seen.len(), 0) {
        return None;
    }
    if seen.contains(&current) {
        return Some(());
    }
    budget.reserve(seen, 1)?;
    seen.push(current);
    let admitted = admit_terms_with_remaining(exec, &[current], remaining, Some(budget));
    if let Some(contents @ (AdmittedItes::BooleanOnly | AdmittedItes::Term)) = admitted {
        if sources.len() == MAX_NATIVE_ATTEMPTS {
            return None;
        }
        budget.reserve(sources, 1)?;
        if !budget.pay(
            path.len(),
            path.len()
                .checked_mul(std::mem::size_of::<conjunct_leaves::Edge>())?,
        ) {
            return None;
        }
        sources.push(NativeIteSource {
            plan: LiftPlan {
                root,
                path: path.clone(),
                source: current,
            },
            contents,
        });
    } else if *remaining == 0 || !budget.pay(0, 0) {
        return None;
    }
    Some(())
}

/// Candidate routing only: a pure Boolean source has exactly the standard
/// branch-clause targets. The emitter and whole strict checker still derive
/// every rule independently. Do not spend the shared closer attempts proving
/// an unrelated theory leaf from this source before later sources are tried.
fn boolean_branch_target(
    exec: &Executor,
    source: TermId,
    target: TermId,
    contents: AdmittedItes,
    budget: &RepairBudget,
) -> Option<bool> {
    if !budget.pay(1, 0)
        || exec.ctx.terms.entry_stamp(source).is_none()
        || exec.ctx.terms.entry_stamp(target).is_none()
    {
        return None;
    }
    let terms = &exec.ctx.terms;
    let TermData::Ite(condition, then_value, else_value) = terms.get(source) else {
        return Some(true);
    };
    if contents != AdmittedItes::BooleanOnly {
        return Some(true);
    }
    let TermData::App(Symbol::Named(name), literals) = terms.get(target) else {
        return Some(false);
    };
    if name != "or" || literals.len() != 2 {
        return Some(false);
    }
    if !budget.pay(literals.len(), 0) {
        return None;
    }
    let is_not_condition = |literal| {
        terms.entry_stamp(literal).is_some()
            && matches!(terms.get(literal), TermData::Not(inner) if inner == condition)
    };
    let a = literals[0];
    let b = literals[1];
    Some(
        (a == *then_value && is_not_condition(b))
            || (b == *then_value && is_not_condition(a))
            || (a == *else_value && b == *condition)
            || (b == *else_value && a == *condition),
    )
}

/// Bound the complete owned proof copy, including annotations unused by the
/// semantic checker. Counts are bounded owned slots, not a byte estimate:
/// Farkas and cutting-plane coefficients are Rational64 (two inline i64s),
/// so their magnitude cannot hide heap-owned numerator/denominator limbs.
/// Unknown payload variants decline this optional producer.
fn admit_proof_copy(proof: &Proof) -> Option<()> {
    use crate::executor::proof::rule_owned_payload::{rule_owned_payload, RuleOwnedPayload};
    let mut left = MAX_NATIVE_PAYLOAD;
    let mut charge = |n| {
        left = left.checked_sub(n)?;
        Some(())
    };
    charge(proof.steps.len())?;
    charge(proof.named_steps.capacity())?;
    for name in proof.named_steps.keys() {
        charge(name.len())?;
    }
    for step in &proof.steps {
        match step {
            ProofStep::Assume(_) => charge(1)?,
            ProofStep::Resolution { clause, .. } => charge(clause.len())?,
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => {
                if let RuleOwnedPayload::Text(name) = rule_owned_payload(rule)? {
                    charge(name.len())?;
                }
                charge(clause.len())?;
                charge(premises.len())?;
                charge(args.len())?;
            }
            ProofStep::TheoryLemma {
                theory,
                clause,
                farkas,
                lia,
                ..
            } => {
                charge(theory.len())?;
                charge(clause.len())?;
                if let Some(hint) = farkas {
                    charge(hint.coefficients.len())?;
                }
                match lia {
                    Some(ay_core::LiaAnnotation::CuttingPlane(hint)) => {
                        charge(hint.farkas.coefficients.len())?
                    }
                    Some(
                        ay_core::LiaAnnotation::BoundsGap
                        | ay_core::LiaAnnotation::Divisibility
                        | ay_core::LiaAnnotation::LinearIdentity,
                    )
                    | None => {}
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
    Some(())
}

impl Executor {
    pub(in crate::executor) fn try_rebuild_native_ite_clausification(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        if self.should_abort_theory_loop() {
            replay_note(|| "native-ite-clausification: original search stop".to_owned());
            return false;
        }
        let Some((epoch, source_context, window)) =
            self.bounded_plain_unsat_query_scope(MAX_NATIVE_ROOTS)
        else {
            replay_note(|| "native-ite-clausification: no current plain query epoch".to_owned());
            return false;
        };
        let epoch = epoch.clone();
        let source_context = source_context.clone();
        if !self
            .ctx
            .native_authored_originals_match_bounded(window, MAX_NATIVE_ROOTS)
        {
            replay_note(|| {
                "native-ite-clausification: no positive native source window".to_owned()
            });
            return false;
        }
        // The opaque current epoch supplies the immutable original window;
        // insertion provenance above authenticates every ordered occurrence.
        // Neither the rewritten working stack nor a parsed marker supplies it.
        let roots = window.to_vec();
        if roots != self.proof_original_problem_assertions_slice()
            || roots.iter().any(|&root| {
                self.ctx.terms.entry_stamp(root).is_none()
                    || self.ctx.terms.sort(root) != &Sort::Bool
            })
        {
            return false;
        }
        if ay_core::misc_cli_flags().debug_cert {
            ay_core::safe_eprintln!(
                "c source-origin native-ite exec={:p} immutable={} proof-original={} native=true",
                self,
                roots.len(),
                self.proof_original_problem_assertions_slice().len(),
            );
            // Fixed diagnostic output only: no term rendering, copies, source
            // selection, or authority is obtained from these numeric identities.
            for (row, &root) in roots.iter().take(64).enumerate() {
                ay_core::safe_eprintln!(
                    "c source-origin immutable row={row} root={root:?} stamp={:?}",
                    self.ctx.terms.entry_stamp(root),
                );
            }
            for (row, &root) in self
                .proof_original_problem_assertions_slice()
                .iter()
                .take(64)
                .enumerate()
            {
                ay_core::safe_eprintln!(
                    "c source-origin proof-original row={row} root={root:?} stamp={:?}",
                    self.ctx.terms.entry_stamp(root),
                );
            }
        }
        let budget = RepairBudget::new(self);
        let Some(sources) = select_ite_sources(self, &roots, &budget) else {
            replay_note(|| "native-ite-clausification: source admission exhausted".to_owned());
            return false;
        };
        replay_note(|| {
            format!(
                "native-ite-clausification: roots={} ITE_sources={}",
                roots.len(),
                sources.len()
            )
        });
        let has_conjunct_source = roots.iter().any(|&root| {
            matches!(self.ctx.terms.get(root), TermData::App(Symbol::Named(name), _) if name == "and")
        });
        if sources.len() > MAX_NATIVE_ATTEMPTS || (sources.is_empty() && !has_conjunct_source) {
            return false;
        }
        let prefix = self.ctx.terms.snapshot_stamp();
        let metadata_generation = self.ctx.terms.checker_visible_metadata_generation();
        let mut attempts = MAX_NATIVE_ATTEMPTS;
        let mut closure_budget = LiftClosureBudget {
            remaining: self
                .proof_reconstruction_step_budget
                .map_or(MAX_NATIVE_TOTAL_CLOSURE_STEPS, |caller| {
                    caller.min(MAX_NATIVE_TOTAL_CLOSURE_STEPS)
                }),
            per_attempt: MAX_NATIVE_CLOSURE_STEPS,
        };
        let Some(mut candidate) = projection::copy(self, proof, &roots, &budget) else {
            return false;
        };
        let Some(mut promoted) = self.stage_native_conjunct_leaves(&mut candidate, &roots, &budget)
        else {
            return false;
        };
        for selected in sources {
            let source_plan = selected.plan;
            if self.should_abort_theory_loop() || attempts == 0 {
                break;
            }
            let mut plans = Vec::new();
            if budget.reserve(&mut plans, candidate.steps.len()).is_none() {
                return false;
            }
            plans.resize_with(candidate.steps.len(), || None);
            let mut planned = false;
            for (index, step) in candidate.steps.iter().enumerate() {
                if !budget.pay(1, 0) {
                    return false;
                }
                let ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    ..
                } = step
                else {
                    continue;
                };
                let [target] = clause.as_slice() else {
                    continue;
                };
                if attempts == 0 {
                    break;
                }
                if !premises.is_empty() || roots.contains(target) {
                    continue;
                }
                match boolean_branch_target(
                    self,
                    source_plan.source,
                    *target,
                    selected.contents,
                    &budget,
                ) {
                    Some(true) => {}
                    Some(false) => continue,
                    None => return false,
                }
                // The shared counter includes failed raw-input admission.
                // Malformed late targets cannot reset the bounded walk.
                attempts -= 1;
                let mut target_work = MAX_NATIVE_TERM_OCCURRENCES;
                if admit_terms_with_remaining(self, &[*target], &mut target_work, Some(&budget))
                    .is_none()
                {
                    continue;
                }
                if !budget.pay(
                    source_plan.path.len().saturating_mul(9).saturating_add(1),
                    source_plan
                        .path
                        .len()
                        .saturating_mul(std::mem::size_of::<conjunct_leaves::Edge>() + 512)
                        .saturating_add(256),
                ) {
                    return false;
                }
                plans[index] = Some(source_plan.clone());
                planned = true;
            }
            if !planned {
                continue;
            }
            if projection::admit_rebuild_copy(&candidate, &budget).is_none() {
                return false;
            }
            promoted += self.promote_planned_ite_lift_units(
                &mut candidate,
                &plans,
                Some(&mut closure_budget),
            );
            if candidate.steps.len() > MAX_PROBE_PROOF_STEPS
                || admit_proof_copy(&candidate).is_none()
            {
                return false;
            }
        }
        if promoted == 0 || self.should_abort_theory_loop() {
            replay_note(|| {
                format!(
                    "native-ite-clausification: no complete scoped candidate; promoted={promoted}"
                )
            });
            return false;
        }
        // Stage independently derivable arithmetic and EUF leaves in the same
        // candidate. Their premise-free clauses keep all existing consumers.
        // The exact-source and whole-proof checks below still commit once.
        if self
            .stage_checked_integer_and_euf_leaves(&mut candidate, &budget)
            .is_none()
        {
            return false;
        }
        if candidate.steps.len() > MAX_PROBE_PROOF_STEPS
            || admit_proof_copy(&candidate).is_none()
            || self.should_abort_theory_loop()
            || ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &roots).is_err()
        {
            return false;
        }
        let checked = self.check_proof_strict_with_datatypes(&candidate);
        let complete = checked.as_ref().is_ok_and(|quality| quality.is_complete());
        replay_note(|| {
            format!(
                "native-ite-clausification: promoted={promoted} strict_complete={complete} {}",
                strict_result_note(&checked),
            )
        });
        if let Err(error) = &checked {
            replay_note(|| {
                failure::arithmetic_step_note(&self.ctx.terms, &candidate, error, &budget)
            });
        }
        let current = self
            .bounded_plain_unsat_query_scope(MAX_NATIVE_ROOTS)
            .is_some_and(|(now_epoch, now_context, now_roots)| {
                now_epoch.is_same_epoch(&epoch)
                    && now_context == source_context
                    && now_roots == roots
                    && self
                        .ctx
                        .native_authored_originals_match_bounded(now_roots, MAX_NATIVE_ROOTS)
            });
        if !complete
            || !current
            || self.should_abort_theory_loop()
            || !prefix.is_append_only_prefix_of(&self.ctx.terms)
            || metadata_generation != self.ctx.terms.checker_visible_metadata_generation()
        {
            return false;
        }
        *proof = candidate;
        true
    }
}

#[cfg(test)]
mod tests;
