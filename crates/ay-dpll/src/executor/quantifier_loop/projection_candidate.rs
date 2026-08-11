// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Untrusted candidate production for quantified projection certificates.
//!
//! This module may use source spellings as hints.  It has no SAT authority:
//! every returned candidate must be accepted by `ay-model-check`'s independent
//! projection checker and by `ay-frontend`'s positive, scope-stable declaration
//! binding checker. Even the resulting opaque value is not SAT authority: it
//! must be combined with a non-cloneable authored-query permit at the sealed
//! emission boundary.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};
use ay_frontend::{
    CheckedProjectionBindings, Context, ProjectionBindingRejection, ProjectionBindingRequest,
    SourceContextStamp,
};
use ay_model_check::{
    check_projection_implication_with_stop, CheckedProjectionImplication,
    ProjectionCertificateRejection, ProjectionImplicationCandidate, ProjectionUfCandidate,
};

/// Maximum deterministic work charged to the untrusted candidate producer.
///
/// The two independent checkers have their own 10M-step limits.  Candidate
/// production gets the same envelope, but exhausting it is only a local
/// decline: the ordinary solver may still answer the query.  External
/// interrupt/deadline/memory stops remain distinguishable and stop the whole
/// solve.
const MAX_PROJECTION_PRODUCER_STEPS: usize = 10_000_000;

/// Opaque conjunction of independent semantic and positive source-binding
/// evidence for one exact root snapshot.
///
/// This type is deliberately non-`Clone`, has no public constructor, and is
/// still insufficient to emit SAT without an authored-query permit.
#[derive(Debug)]
pub(in crate::executor) struct CheckedProjectionSourceEvidence {
    semantics: CheckedProjectionImplication,
    bindings: CheckedProjectionBindings,
}

impl CheckedProjectionSourceEvidence {
    /// Semantically checked total projection definitions.
    pub(in crate::executor) fn semantics(&self) -> &CheckedProjectionImplication {
        &self.semantics
    }

    /// Source context/scope snapshot independently captured by the binding
    /// checker.
    pub(in crate::executor) fn source_context_stamp(&self) -> &SourceContextStamp {
        self.bindings.source_context_stamp()
    }

    /// Exact ordered roots independently frozen by both checker layers.
    pub(in crate::executor) fn roots(&self) -> &[TermId] {
        self.semantics.assertions()
    }

    /// Whether both independently frozen views still describe the exact live
    /// roots, term graph, declaration identities, kinds, signatures, and scope
    /// epoch.
    pub(in crate::executor) fn is_current(&self, ctx: &Context, roots: &[TermId]) -> bool {
        self.semantics.matches_snapshot(&ctx.terms, roots)
            && ctx.projection_bindings_still_current(&self.bindings, roots)
            && checked_layers_agree(&self.semantics, &self.bindings)
    }

    /// Number of total UF definitions carried by this checked model.
    #[cfg(test)]
    fn definition_count(&self) -> usize {
        self.semantics.definitions().len()
    }
}

/// Result of the production-safe semantic/source certificate attempt.
pub(in crate::executor) enum ProjectionSourceOutcome {
    /// The caller's interrupt, deadline, or memory envelope fired.
    Stopped,
    /// The deterministic budget of the untrusted producer was exhausted.
    ///
    /// This is a local decline, not an external solve stop.  Callers must fall
    /// back to the ordinary solver path rather than report a resource-out
    /// verdict for the query.
    ResourceLimit,
    /// The untrusted producer did not recognize the restricted fragment.
    NoCandidate,
    /// An independent checker rejected the candidate or its source binding.
    Rejected(ProjectionSourceRejection),
    /// Both independent checkers accepted one exact frozen query snapshot.
    Checked(CheckedProjectionSourceEvidence),
}

/// Fail-closed reason retained for diagnostics and audit tests.
#[derive(Debug, thiserror::Error)]
pub(in crate::executor) enum ProjectionSourceRejection {
    #[error("semantic projection checker rejected the candidate: {0}")]
    Semantic(#[source] ProjectionCertificateRejection),
    #[error("source projection binding rejected the candidate: {0}")]
    Source(#[source] ProjectionBindingRejection),
    #[error("semantic and source projection evidence disagree")]
    LayerMismatch,
    #[error("projection evidence no longer matches its source snapshot")]
    StaleSnapshot,
}

fn checked_layers_agree(
    semantics: &CheckedProjectionImplication,
    bindings: &CheckedProjectionBindings,
) -> bool {
    let same_roots = semantics.assertions() == bindings.roots();
    same_roots
        && semantics.checked_term_count() == bindings.checked_term_count()
        && semantics.definitions().len() == bindings.bindings().len()
        && semantics
            .definitions()
            .iter()
            .zip(bindings.bindings())
            .all(|(definition, binding)| {
                definition.symbol() == binding.symbol()
                    && definition.parameter_sorts() == binding.parameter_sorts()
                    && definition.result_sort() == binding.result_sort()
            })
}

/// Produce an untrusted candidate, independently prove its semantics, and
/// independently bind every selected head to a live ordinary free declaration.
///
/// Nothing returned here can emit SAT by itself. The accepted value must still
/// be combined with the exact authored-query capability immediately before the
/// model is installed and the public SAT certificate is minted.
pub(in crate::executor) fn check_projection_source(
    ctx: &Context,
    roots: &[TermId],
    should_stop: impl FnMut() -> bool,
) -> ProjectionSourceOutcome {
    check_projection_source_with_budget(ctx, roots, should_stop, MAX_PROJECTION_PRODUCER_STEPS)
}

fn check_projection_source_with_budget(
    ctx: &Context,
    roots: &[TermId],
    mut should_stop: impl FnMut() -> bool,
    producer_steps: usize,
) -> ProjectionSourceOutcome {
    let mut stop = ProjectionStop::with_budget(&mut should_stop, producer_steps);
    if stop.requested() {
        return stop.source_outcome();
    }
    let Some(candidate) = propose_projection_implication(ctx, roots, &mut stop) else {
        return if stop.requested() {
            stop.source_outcome()
        } else {
            ProjectionSourceOutcome::NoCandidate
        };
    };
    if stop.requested() {
        return stop.source_outcome();
    }
    // Only the untrusted proposal is charged to this local budget.  The
    // independent semantic and source-binding checkers enforce separate
    // deterministic limits, while this object continues to propagate the
    // sticky external stop state through both callbacks.
    stop.finish_producer();

    let semantics =
        match check_projection_implication_with_stop(&ctx.terms, roots, &candidate, || {
            stop.requested()
        }) {
            Ok(checked) => checked,
            Err(ProjectionCertificateRejection::Stopped) => {
                return ProjectionSourceOutcome::Stopped;
            }
            Err(rejection) => {
                return ProjectionSourceOutcome::Rejected(ProjectionSourceRejection::Semantic(
                    rejection,
                ));
            }
        };
    if stop.requested() {
        return ProjectionSourceOutcome::Stopped;
    }

    let mut requests = Vec::with_capacity(semantics.definitions().len());
    for definition in semantics.definitions() {
        if stop.requested() {
            return ProjectionSourceOutcome::Stopped;
        }
        requests.push(ProjectionBindingRequest {
            symbol: definition.symbol().clone(),
            parameter_sorts: definition.parameter_sorts().to_vec(),
            result_sort: definition.result_sort().clone(),
        });
    }
    let bindings = match ctx
        .check_projection_bindings_with_stop(roots, &requests, || stop.requested())
    {
        Ok(checked) => checked,
        Err(ProjectionBindingRejection::Stopped) => return ProjectionSourceOutcome::Stopped,
        Err(rejection) => {
            return ProjectionSourceOutcome::Rejected(ProjectionSourceRejection::Source(rejection));
        }
    };
    if stop.requested() {
        return ProjectionSourceOutcome::Stopped;
    }
    if !checked_layers_agree(&semantics, &bindings) {
        return ProjectionSourceOutcome::Rejected(ProjectionSourceRejection::LayerMismatch);
    }
    let checked = CheckedProjectionSourceEvidence {
        semantics,
        bindings,
    };
    if !checked.is_current(ctx, roots) {
        return ProjectionSourceOutcome::Rejected(ProjectionSourceRejection::StaleSnapshot);
    }
    ProjectionSourceOutcome::Checked(checked)
}

/// Observation-only result of candidate production plus independent checking.
#[cfg(test)]
pub(in crate::executor) enum ProjectionShadowOutcome {
    /// An external interrupt or solve deadline stopped observation.  No
    /// telemetry from a partial producer/checker run may be published.
    Stopped,
    /// Candidate production exhausted its deterministic local budget.
    ResourceLimit,
    /// The exact initial fragment or the untrusted producer did not apply.
    NoCandidate,
    /// A candidate was produced but the independent checker rejected it.
    Rejected,
    /// The checker accepted a snapshot-bound certificate.  The certificate is
    /// deliberately dropped by the shadow lane and has no verdict read site.
    Accepted { definitions: usize },
}

/// Run the projection certificate pipeline without changing solver state.
///
/// This is the offline audit's shadow pipeline. Keeping proposal, checking, and
/// outcome construction in one function makes it easy to demonstrate that it
/// has no model or verdict output.
#[cfg(test)]
pub(in crate::executor) fn check_projection_shadow(
    ctx: &Context,
    roots: &[TermId],
    should_stop: impl FnMut() -> bool,
) -> ProjectionShadowOutcome {
    match check_projection_source(ctx, roots, should_stop) {
        ProjectionSourceOutcome::Stopped => ProjectionShadowOutcome::Stopped,
        ProjectionSourceOutcome::ResourceLimit => ProjectionShadowOutcome::ResourceLimit,
        ProjectionSourceOutcome::NoCandidate => ProjectionShadowOutcome::NoCandidate,
        ProjectionSourceOutcome::Rejected(_) => ProjectionShadowOutcome::Rejected,
        ProjectionSourceOutcome::Checked(checked) => ProjectionShadowOutcome::Accepted {
            definitions: checked.definition_count(),
        },
    }
}

/// Sticky cooperative-stop and deterministic-budget state for the untrusted
/// producer.
///
/// Producer helpers still return `Option` for ordinary shape rejection.  The
/// sticky status distinguishes that benign decline from both an externally
/// stopped traversal and deterministic local exhaustion at the pipeline
/// boundary.
struct ProjectionStop<'a> {
    should_stop: &'a mut dyn FnMut() -> bool,
    halt: ProjectionProducerHalt,
    remaining_steps: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProjectionProducerHalt {
    Running,
    Stopped,
    ResourceLimit,
}

impl<'a> ProjectionStop<'a> {
    #[cfg(test)]
    fn new(should_stop: &'a mut dyn FnMut() -> bool) -> Self {
        Self::with_budget(should_stop, MAX_PROJECTION_PRODUCER_STEPS)
    }

    fn with_budget(should_stop: &'a mut dyn FnMut() -> bool, steps: usize) -> Self {
        Self {
            should_stop,
            halt: ProjectionProducerHalt::Running,
            remaining_steps: Some(steps),
        }
    }

    fn requested(&mut self) -> bool {
        if self.halt != ProjectionProducerHalt::Running {
            return true;
        }
        // External authority wins when it arrives on the same poll that would
        // otherwise consume the final local step.
        if (self.should_stop)() {
            self.halt = ProjectionProducerHalt::Stopped;
            return true;
        }
        if let Some(remaining) = &mut self.remaining_steps {
            let Some(next) = remaining.checked_sub(1) else {
                self.halt = ProjectionProducerHalt::ResourceLimit;
                return true;
            };
            *remaining = next;
        }
        false
    }

    /// Charge a bulk operation before it copies or allocates `steps` items.
    fn requested_bulk(&mut self, steps: usize) -> bool {
        if self.halt != ProjectionProducerHalt::Running {
            return true;
        }
        if (self.should_stop)() {
            self.halt = ProjectionProducerHalt::Stopped;
            return true;
        }
        if let Some(remaining) = &mut self.remaining_steps {
            if *remaining < steps {
                self.halt = ProjectionProducerHalt::ResourceLimit;
                return true;
            }
            *remaining -= steps;
        }
        false
    }

    fn finish_producer(&mut self) {
        self.remaining_steps = None;
    }

    fn source_outcome(&self) -> ProjectionSourceOutcome {
        match self.halt {
            ProjectionProducerHalt::Stopped => ProjectionSourceOutcome::Stopped,
            ProjectionProducerHalt::ResourceLimit => ProjectionSourceOutcome::ResourceLimit,
            ProjectionProducerHalt::Running => {
                debug_assert!(false, "requested() returned true without a halt reason");
                ProjectionSourceOutcome::ResourceLimit
            }
        }
    }
}

/// Propose one projection for every declared UF occurring in the single-root
/// quantified formula understood by the certificate checker.
///
/// The producer uses two hints, in priority order:
///
/// 1. a direct top-level conclusion bridge `binder = f(args)`; and
/// 2. the benchmark producer's `<binder>_39_!<serial>` declaration spelling.
///
/// Neither hint is evidence.  The independent checker re-derives the exact
/// quantifier/application shape, beta-reduces the proposed total functions,
/// and proves the complete implication before accepting it.
fn propose_projection_implication(
    ctx: &Context,
    roots: &[TermId],
    stop: &mut ProjectionStop<'_>,
) -> Option<ProjectionImplicationCandidate> {
    if stop.requested() {
        return None;
    }
    let [root] = roots else {
        return None;
    };
    let (binders, body, triggers) = match ctx.terms.get(*root) {
        TermData::Forall(binders, body, triggers) => (binders, *body, triggers),
        _ => return None,
    };
    if !triggers.is_empty() || binders.is_empty() {
        return None;
    }
    for (_, sort) in binders {
        if stop.requested() || !matches!(sort, Sort::Bool | Sort::BitVec(_)) {
            return None;
        }
    }

    let uf_uses = collect_declared_uf_uses(ctx, body, stop)?;
    if uf_uses.is_empty() {
        return None;
    }
    let binder_terms = collect_binder_terms(&ctx.terms, body, binders, stop)?;
    let conclusion = implication_conclusion(ctx, body, stop)?;
    let bridge_hints = direct_bridge_hints(&ctx.terms, conclusion, &binder_terms, stop);
    if stop.requested() {
        return None;
    }

    if stop.requested_bulk(uf_uses.len()) {
        return None;
    }
    let mut definitions = Vec::with_capacity(uf_uses.len());
    for uf_use in uf_uses {
        if stop.requested() {
            return None;
        }
        if stop.requested_bulk(uf_use.symbol.name().len().saturating_mul(8)) {
            return None;
        }
        let info = ctx.symbol_info_by_identity(uf_use.symbol.name())?;
        if !info.is_direct_source_declaration()
            || ctx.overloaded_surface_name(uf_use.symbol.name()).is_some()
            || ctx.is_internal_symbol(uf_use.symbol.name())
            || ctx.is_defined_fun(uf_use.symbol.name())
            || ctx.adopted_macro_interp(uf_use.symbol.name()).is_some()
            || ctx.is_datatype_member_name(uf_use.symbol.name())
            || crate::features::is_builtin_symbol_name(uf_use.symbol.name())
        {
            return None;
        }

        let projected_parameter =
            if let Some(parameter) = unique_bridge_parameter(&bridge_hints, &uf_use.symbol, stop) {
                parameter
            } else {
                if stop.requested() {
                    return None;
                }
                let binder_name = generated_head_binder_name(uf_use.symbol.name(), stop)?;
                let binder_term =
                    unique_freshened_binder_term(&ctx.terms, &binder_terms, binder_name, stop)?;
                unique_argument_position(&uf_use.first_args, binder_term, stop)?
            };

        if projected_parameter >= info.arg_sorts.len()
            || uf_use.first_args.len() != info.arg_sorts.len()
            || info.arg_sorts[projected_parameter] != info.sort
        {
            return None;
        }
        if stop.requested_bulk(info.arg_sorts.len()) {
            return None;
        }
        definitions.push(ProjectionUfCandidate {
            symbol: uf_use.symbol,
            parameter_sorts: info.arg_sorts.clone(),
            result_sort: info.sort.clone(),
            projected_parameter,
        });
    }

    Some(ProjectionImplicationCandidate {
        conclusion,
        definitions,
    })
}

struct UfUse {
    symbol: Symbol,
    first_args: Vec<TermId>,
}

fn collect_declared_uf_uses(
    ctx: &Context,
    root: TermId,
    stop: &mut ProjectionStop<'_>,
) -> Option<Vec<UfUse>> {
    let mut seen_terms = HashSet::default();
    let mut uses: Vec<UfUse> = Vec::new();
    let mut use_indices: HashMap<&str, usize> = HashMap::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if stop.requested() {
            return None;
        }
        if !seen_terms.insert(term) {
            continue;
        }
        match ctx.terms.get(term) {
            TermData::App(symbol, args) => {
                if stop.requested_bulk(args.len()) {
                    return None;
                }
                stack.extend(args.iter().copied());
                if stop.requested_bulk(symbol.name().len().saturating_mul(2)) {
                    return None;
                }
                let Some(info) = ctx.symbol_info_by_identity(symbol.name()) else {
                    continue;
                };
                if info.arg_sorts.is_empty() {
                    return None;
                }
                if !matches!(symbol, Symbol::Named(_))
                    || args.len() != info.arg_sorts.len()
                    || ctx.terms.sort(term) != &info.sort
                {
                    return None;
                }
                if let Some(previous) = use_indices
                    .get(symbol.name())
                    .and_then(|index| uses.get(*index))
                {
                    if previous.first_args.len() != args.len() {
                        return None;
                    }
                } else {
                    if stop.requested_bulk(args.len()) {
                        return None;
                    }
                    use_indices.insert(symbol.name(), uses.len());
                    uses.push(UfUse {
                        symbol: symbol.clone(),
                        first_args: args.clone(),
                    });
                }
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.push(*condition);
                stack.push(*then_term);
                stack.push(*else_term);
            }
            TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                return None;
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => return None,
        }
    }
    Some(uses)
}

fn collect_binder_terms(
    terms: &TermStore,
    body: TermId,
    binders: &[(String, Sort)],
    stop: &mut ProjectionStop<'_>,
) -> Option<Vec<((String, Sort), TermId)>> {
    if stop.requested_bulk(binders.len()) {
        return None;
    }
    let mut found = vec![None; binders.len()];
    let mut binder_indices: HashMap<&str, usize> = HashMap::default();
    for (index, (name, _)) in binders.iter().enumerate() {
        if stop.requested() || stop.requested_bulk(name.len()) {
            return None;
        }
        if binder_indices.insert(name.as_str(), index).is_some() {
            return None;
        }
    }
    let mut seen = HashSet::default();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if stop.requested() {
            return None;
        }
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Var(name, _) => {
                if stop.requested_bulk(name.len()) {
                    return None;
                }
                if let Some(index) = binder_indices.get(name.as_str()).copied() {
                    let binder_sort = &binders[index].1;
                    if terms.sort(term) != binder_sort {
                        return None;
                    }
                    if let Some(prior) = found[index] {
                        if prior != term {
                            return None;
                        }
                    } else {
                        found[index] = Some(term);
                    }
                }
            }
            TermData::App(_, args) => {
                if stop.requested_bulk(args.len()) {
                    return None;
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.push(*condition);
                stack.push(*then_term);
                stack.push(*else_term);
            }
            TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                return None;
            }
            TermData::Const(_) => {}
            _ => return None,
        }
    }
    if stop.requested_bulk(binders.len()) {
        return None;
    }
    let mut ordered = Vec::with_capacity(binders.len());
    for ((name, sort), term) in binders.iter().zip(found) {
        if stop.requested() {
            return None;
        }
        ordered.push(((name.clone(), sort.clone()), term?));
    }
    Some(ordered)
}

fn implication_conclusion(
    ctx: &Context,
    body: TermId,
    stop: &mut ProjectionStop<'_>,
) -> Option<TermId> {
    if stop.requested() {
        return None;
    }
    let TermData::App(symbol, operands) = ctx.terms.get(body) else {
        return None;
    };
    match symbol.name() {
        "=>" if operands.len() == 2 => Some(operands[1]),
        "or" => {
            let mut conclusion = None;
            for operand in operands {
                if stop.requested() {
                    return None;
                }
                if !term_contains_declared_uf(ctx, *operand, stop) {
                    continue;
                }
                if conclusion.replace(*operand).is_some() {
                    return None;
                }
            }
            conclusion
        }
        _ => None,
    }
}

fn term_contains_declared_uf(ctx: &Context, root: TermId, stop: &mut ProjectionStop<'_>) -> bool {
    let mut seen = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if stop.requested() {
            return false;
        }
        if !seen.insert(term) {
            continue;
        }
        match ctx.terms.get(term) {
            TermData::App(symbol, args) => {
                if stop.requested_bulk(symbol.name().len()) {
                    return false;
                }
                if ctx
                    .symbol_info_by_identity(symbol.name())
                    .is_some_and(|info| !info.arg_sorts.is_empty())
                {
                    return true;
                }
                if stop.requested_bulk(args.len()) {
                    return false;
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.push(*condition);
                stack.push(*then_term);
                stack.push(*else_term);
            }
            TermData::Let(bindings, inner) => {
                if stop.requested_bulk(bindings.len().saturating_add(1)) {
                    return false;
                }
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*inner);
            }
            TermData::Forall(_, inner, _) | TermData::Exists(_, inner, _) => stack.push(*inner),
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => return false,
        }
    }
    false
}

fn direct_bridge_hints(
    terms: &TermStore,
    conclusion: TermId,
    binders: &[((String, Sort), TermId)],
    stop: &mut ProjectionStop<'_>,
) -> Vec<(Symbol, usize)> {
    let conjuncts = match terms.get(conclusion) {
        TermData::App(symbol, args) if symbol.name() == "and" => args.as_slice(),
        _ => std::slice::from_ref(&conclusion),
    };
    let mut hints = Vec::new();
    for conjunct in conjuncts {
        if stop.requested() {
            return hints;
        }
        let TermData::App(equals, sides) = terms.get(*conjunct) else {
            continue;
        };
        if stop.requested_bulk(equals.name().len()) {
            return hints;
        }
        if equals.name() != "=" || sides.len() != 2 {
            continue;
        }
        for (binder_side, app_side) in [(sides[0], sides[1]), (sides[1], sides[0])] {
            let mut is_binder = false;
            for (_, binder) in binders {
                if stop.requested() {
                    return hints;
                }
                if *binder == binder_side {
                    is_binder = true;
                    break;
                }
            }
            if !is_binder {
                continue;
            }
            let TermData::App(symbol, args) = terms.get(app_side) else {
                continue;
            };
            if let Some(position) = unique_argument_position(args, binder_side, stop) {
                if stop.requested_bulk(symbol.name().len()) {
                    return hints;
                }
                hints.push((symbol.clone(), position));
            }
        }
    }
    hints
}

fn unique_bridge_parameter(
    hints: &[(Symbol, usize)],
    symbol: &Symbol,
    stop: &mut ProjectionStop<'_>,
) -> Option<usize> {
    let mut selected = None;
    for (head, parameter) in hints {
        if stop.requested()
            || stop.requested_bulk(head.name().len().saturating_add(symbol.name().len()))
        {
            return None;
        }
        if head != symbol {
            continue;
        }
        match selected {
            None => selected = Some(*parameter),
            Some(previous) if previous == *parameter => {}
            Some(_) => return None,
        }
    }
    selected
}

fn unique_argument_position(
    args: &[TermId],
    needle: TermId,
    stop: &mut ProjectionStop<'_>,
) -> Option<usize> {
    let mut selected = None;
    for (index, argument) in args.iter().enumerate() {
        if stop.requested() {
            return None;
        }
        if *argument != needle {
            continue;
        }
        if selected.replace(index).is_some() {
            return None;
        }
    }
    selected
}

fn generated_head_binder_name<'a>(
    symbol: &'a str,
    stop: &mut ProjectionStop<'_>,
) -> Option<&'a str> {
    if stop.requested_bulk(symbol.len()) {
        return None;
    }
    let (binder, serial) = symbol.rsplit_once("_39_!")?;
    (!binder.is_empty() && !serial.is_empty() && serial.bytes().all(|byte| byte.is_ascii_digit()))
        .then_some(binder)
}

/// Recover the one quantified variable created by `TermStore::mk_fresh_var`
/// from the original binder spelling embedded in a generated UF head.
///
/// Quantifier elaboration stores a source binder as `<source-name>_<var-id>`.
/// Checking both that suffix and the `Var` identity rejects textual
/// lookalikes. This remains only a producer-side hint; the independent
/// projection checker validates every proposed definition.
fn unique_freshened_binder_term(
    terms: &TermStore,
    binders: &[((String, Sort), TermId)],
    source_name: &str,
    stop: &mut ProjectionStop<'_>,
) -> Option<TermId> {
    let mut selected = None;
    for ((fresh_name, _), term) in binders {
        if stop.requested()
            || stop.requested_bulk(
                fresh_name
                    .len()
                    .saturating_add(source_name.len().saturating_mul(2)),
            )
        {
            return None;
        }
        let TermData::Var(term_name, var_id) = terms.get(*term) else {
            continue;
        };
        if !(fresh_name == term_name
            && term_name
                .strip_prefix(source_name)
                .is_some_and(|suffix| suffix == format!("_{var_id}")))
        {
            continue;
        }
        if selected.replace(*term).is_some() {
            return None;
        }
    }
    selected
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::Executor;
    use ay_frontend::parse;

    fn shadow_outcome(script: &str) -> ProjectionShadowOutcome {
        let commands = parse(script).expect("valid projection test script");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("declarations and assertion execute");
        check_projection_shadow(&executor.ctx, &executor.ctx.assertions, || false)
    }

    fn accepted_fixture_executor() -> Executor {
        let commands = parse(
            r#"
            (set-logic UFBV)
            (declare-fun x_39_!0 ((_ BitVec 8)) (_ BitVec 8))
            (assert
              (forall ((x (_ BitVec 8)))
                (=> (= x #x00) (= (x_39_!0 x) #x00))))
            "#,
        )
        .expect("valid projection test script");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("declarations and assertion execute");
        executor
    }

    #[test]
    fn builtin_colliding_private_source_head_reaches_positive_checkers() {
        let outcome = shadow_outcome(
            r#"
            (set-logic ALL)
            (declare-fun not (Bool) Bool)
            (assert
              (forall ((x Bool))
                (=> (= x false) (= x (not x)))))
            "#,
        );
        assert!(matches!(
            outcome,
            ProjectionShadowOutcome::Accepted { definitions: 1 }
        ));
    }

    #[test]
    fn exhausted_local_producer_budget_is_not_an_external_stop() {
        let executor = accepted_fixture_executor();
        let mut polls = 0usize;
        let outcome = check_projection_source_with_budget(
            &executor.ctx,
            &executor.ctx.assertions,
            || {
                polls += 1;
                false
            },
            0,
        );
        assert!(matches!(outcome, ProjectionSourceOutcome::ResourceLimit));
        assert_eq!(polls, 1, "zero work must still poll external authority");
    }

    #[test]
    fn external_stop_wins_at_the_local_budget_boundary() {
        let executor = accepted_fixture_executor();
        let mut polls = 0usize;
        let outcome = check_projection_source_with_budget(
            &executor.ctx,
            &executor.ctx.assertions,
            || {
                polls += 1;
                true
            },
            0,
        );
        assert!(matches!(outcome, ProjectionSourceOutcome::Stopped));
        assert_eq!(polls, 1);
    }

    #[test]
    fn adversarially_small_budget_declines_with_bounded_polling() {
        let executor = accepted_fixture_executor();
        const STEPS: usize = 8;

        for _ in 0..2 {
            let mut polls = 0usize;
            let outcome = check_projection_source_with_budget(
                &executor.ctx,
                &executor.ctx.assertions,
                || {
                    polls += 1;
                    false
                },
                STEPS,
            );
            assert!(matches!(outcome, ProjectionSourceOutcome::ResourceLimit));
            assert!(
                polls <= STEPS + 1,
                "bulk work must be charged before it is performed: polls={polls}"
            );
        }
    }

    /// Build a small, repository-owned analogue of the rotation fixpoints in
    /// the optional benchmark campaign.
    ///
    /// `cycle_len` distinct initial values rotate once per depth. Every UF is
    /// named for, and applied to, one quantified state binder, but the final
    /// disjunction only permits equality with an earlier depth. The proposed
    /// projections therefore prove the implication exactly when a complete
    /// rotation has returned every lane to its initial value. This exercises
    /// the candidate producer and the independent checker together; it is not
    /// copied from, or claimed equivalent to, any corpus input.
    fn compact_rotation_fixpoint_script(cycle_len: usize, depth: usize) -> String {
        assert!(cycle_len >= 2);
        assert!((1..=cycle_len).contains(&depth));

        let binders: Vec<String> = (0..=depth)
            .flat_map(|time| (0..cycle_len).map(move |lane| format!("state_{lane}_{time}")))
            .collect();
        let binder_declarations = binders
            .iter()
            .map(|binder| format!("({binder} (_ BitVec 4))"))
            .collect::<Vec<_>>()
            .join(" ");
        // A fixed reverse permutation makes the selected parameter differ for
        // every depth as arity grows. All uses of one head retain this exact
        // permutation, as required by the certificate fragment.
        let arguments = binders.iter().rev().cloned().collect::<Vec<_>>().join(" ");
        let argument_sorts = vec!["(_ BitVec 4)"; binders.len()].join(" ");
        let application = |lane: usize, time: usize| {
            let serial = time * cycle_len + lane;
            format!("(state_{lane}_{time}_39_!{serial} {arguments})")
        };

        let mut script = String::from("(set-logic UFBV)\n");
        for time in 0..depth {
            for lane in 0..cycle_len {
                let serial = time * cycle_len + lane;
                script.push_str(&format!(
                    "(declare-fun state_{lane}_{time}_39_!{serial} ({argument_sorts}) (_ BitVec 4))\n"
                ));
            }
        }

        let mut premise = Vec::new();
        for lane in 0..cycle_len {
            premise.push(format!("(= state_{lane}_0 (_ bv{} 4))", lane + 1));
        }
        for time in 1..=depth {
            for lane in 0..cycle_len {
                let source = (lane + 1) % cycle_len;
                premise.push(format!(
                    "(= state_{lane}_{time} state_{source}_{})",
                    time - 1
                ));
            }
        }

        let mut conclusion = Vec::new();
        for lane in 0..cycle_len {
            conclusion.push(format!("(= {} (_ bv{} 4))", application(lane, 0), lane + 1));
        }
        for time in 1..depth {
            for lane in 0..cycle_len {
                let source = (lane + 1) % cycle_len;
                conclusion.push(format!(
                    "(= {} {})",
                    application(lane, time),
                    application(source, time - 1)
                ));
            }
        }
        let final_branches = (0..depth)
            .map(|prior_time| {
                let equalities = (0..cycle_len)
                    .map(|lane| {
                        format!("(= state_{lane}_{depth} {})", application(lane, prior_time))
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("(and {equalities})")
            })
            .collect::<Vec<_>>();
        let final_choice = match final_branches.as_slice() {
            [only] => only.clone(),
            several => format!("(or {})", several.join(" ")),
        };
        conclusion.push(final_choice);

        script.push_str(&format!(
            "(assert (forall ({binder_declarations}) (=> (and {}) (and {}))))\n",
            premise.join(" "),
            conclusion.join(" ")
        ));
        script
    }

    #[test]
    fn immediate_external_stop_skips_candidate_work() {
        let executor = accepted_fixture_executor();
        let mut polls = 0;
        let outcome = check_projection_shadow(&executor.ctx, &executor.ctx.assertions, || {
            polls += 1;
            true
        });
        assert!(matches!(outcome, ProjectionShadowOutcome::Stopped));
        assert_eq!(polls, 1, "entry stop must avoid all producer/checker work");
    }

    #[test]
    fn producer_traversal_honors_a_later_external_stop() {
        let executor = accepted_fixture_executor();
        let mut polls = 0;
        let outcome = check_projection_shadow(&executor.ctx, &executor.ctx.assertions, || {
            polls += 1;
            polls >= 4
        });
        assert!(matches!(outcome, ProjectionShadowOutcome::Stopped));
        assert_eq!(polls, 4, "producer must poll while traversing the term DAG");
    }

    #[test]
    fn stop_arriving_at_no_candidate_proposal_boundary_is_stopped() {
        let commands = parse(
            r#"
            (set-logic UFBV)
            (assert (forall ((x Bool)) x))
            "#,
        )
        .expect("valid no-candidate projection script");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("no-candidate assertion executes");

        // Measure producer polls without the shadow entry/post-proposal polls,
        // then fire exactly at the latter. The former `was_requested()` check
        // did not poll here and incorrectly returned NoCandidate.
        let producer_polls = {
            let mut producer_polls = 0usize;
            {
                let mut never_stop = || {
                    producer_polls += 1;
                    false
                };
                let mut producer_stop = ProjectionStop::new(&mut never_stop);
                assert!(propose_projection_implication(
                    &executor.ctx,
                    &executor.ctx.assertions,
                    &mut producer_stop,
                )
                .is_none());
            }
            producer_polls
        };
        let stop_at_poll = producer_polls + 2;

        let mut polls = 0usize;
        let outcome = check_projection_shadow(&executor.ctx, &executor.ctx.assertions, || {
            polls += 1;
            polls == stop_at_poll
        });
        assert!(matches!(outcome, ProjectionShadowOutcome::Stopped));
        assert_eq!(polls, stop_at_poll);
    }

    #[test]
    fn generated_head_suffix_is_only_a_well_formed_hint() {
        let mut should_stop = || false;
        let mut stop = ProjectionStop::new(&mut should_stop);
        assert_eq!(
            generated_head_binder_name("state_64_3_39_!17", &mut stop),
            Some("state_64_3")
        );
        assert_eq!(generated_head_binder_name("state_64_3", &mut stop), None);
        assert_eq!(
            generated_head_binder_name("state_64_3_39_!", &mut stop),
            None
        );
        assert_eq!(
            generated_head_binder_name("state_64_3_39_!x", &mut stop),
            None
        );
    }

    #[test]
    fn generated_head_prefix_recovers_exact_freshened_binder() {
        let mut terms = TermStore::new();
        let fresh = terms.mk_fresh_var("state_64_3", Sort::Bool);
        let fresh_name = match terms.get(fresh) {
            TermData::Var(name, _) => name.clone(),
            other => panic!("fresh term was not a variable: {other:?}"),
        };
        assert_ne!(fresh_name, "state_64_3");

        let binders = vec![((fresh_name.clone(), Sort::Bool), fresh)];
        let mut should_stop = || false;
        let mut stop = ProjectionStop::new(&mut should_stop);
        assert_eq!(
            unique_freshened_binder_term(&terms, &binders, "state_64_3", &mut stop),
            Some(fresh)
        );
        assert_eq!(
            unique_freshened_binder_term(&terms, &binders, "state_64", &mut stop),
            None,
            "a shorter textual prefix must not impersonate the source binder"
        );

        let lookalike = terms.mk_fresh_named_var(fresh_name.clone(), Sort::Bool);
        let lookalike_binders = vec![((fresh_name, Sort::Bool), lookalike)];
        assert_eq!(
            unique_freshened_binder_term(&terms, &lookalike_binders, "state_64_3", &mut stop,),
            None,
            "the suffix must equal the variable's actual identity"
        );
    }

    #[test]
    fn repeated_argument_is_not_a_projection_hint() {
        let needle = TermId::new(7);
        let mut should_stop = || false;
        let mut stop = ProjectionStop::new(&mut should_stop);
        assert_eq!(
            unique_argument_position(&[TermId::new(1), needle], needle, &mut stop),
            Some(1)
        );
        assert_eq!(
            unique_argument_position(&[needle, needle], needle, &mut stop),
            None
        );
    }

    #[test]
    fn live_frontend_generated_name_candidate_is_independently_accepted() {
        let script = r#"
            (set-logic UFBV)
            (declare-fun x_39_!0 ((_ BitVec 8)) (_ BitVec 8))
            (assert
              (forall ((x (_ BitVec 8)))
                (=> (= x #x00) (= (x_39_!0 x) #x00))))
            "#;
        let commands = parse(script).expect("valid projection test script");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("declarations and assertion execute");
        let [root] = executor.ctx.assertions.as_slice() else {
            panic!("expected exactly one assertion");
        };
        let TermData::Forall(binders, _, _) = executor.ctx.terms.get(*root) else {
            panic!("expected an elaborated forall");
        };
        assert_eq!(binders.len(), 1);
        assert_ne!(binders[0].0, "x");
        assert!(binders[0]
            .0
            .strip_prefix("x_")
            .is_some_and(|suffix| suffix.bytes().all(|byte| byte.is_ascii_digit())));

        let outcome = check_projection_shadow(&executor.ctx, &executor.ctx.assertions, || false);
        assert!(matches!(
            outcome,
            ProjectionShadowOutcome::Accepted { definitions: 1, .. }
        ));
    }

    #[test]
    fn direct_bridge_can_propose_projection_without_a_name_match() {
        let outcome = shadow_outcome(
            r#"
            (set-logic UFBV)
            (declare-fun unrelated_39_!0
              ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
            (assert
              (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
                (=> (= y #x00)
                    (and (= (unrelated_39_!0 y x) #x00)
                         (= y (unrelated_39_!0 y x))))))
            "#,
        );
        assert!(matches!(
            outcome,
            ProjectionShadowOutcome::Accepted { definitions: 1, .. }
        ));
    }

    /// Always-on classification gate independent of the unvendored ~1 GiB
    /// SMT-LIB corpus. These nine generated cases pin the same meaningful
    /// depth boundary for two-, three-, and four-state rotations: every proper
    /// prefix is rejected, while one full period is accepted.
    #[test]
    fn compact_rotation_fixpoint_shadow_classification() {
        let mut accepted = 0usize;
        let mut rejected = 0usize;
        for cycle_len in 2..=4 {
            for depth in 1..=cycle_len {
                let script = compact_rotation_fixpoint_script(cycle_len, depth);
                let outcome = shadow_outcome(&script);
                if depth == cycle_len {
                    assert!(
                        matches!(
                            outcome,
                            ProjectionShadowOutcome::Accepted { definitions }
                                if definitions == cycle_len * depth
                        ),
                        "full rotation must be accepted: cycle={cycle_len} depth={depth}"
                    );
                    accepted += 1;
                } else {
                    assert!(
                        matches!(outcome, ProjectionShadowOutcome::Rejected),
                        "proper rotation prefix must be independently rejected: cycle={cycle_len} depth={depth}"
                    );
                    rejected += 1;
                }
            }
        }
        assert_eq!((accepted, rejected), (3, 6));
    }

    // The exact 121-file production gate intentionally lives outside `cargo test`:
    //
    //   python3 scripts/ufbv_fixpoint_audit.py OUT.json
    //
    // That harness runs every case in fresh default and `--self-check` child
    // processes, plans and enforces their memory envelope through `_oom_guard.py`,
    // excludes concurrent builds, and records binary/corpus/resource provenance.
    // Keep corpus execution there: an environment-gated Rust test is reported as
    // passed when it does no work, and an in-process cooperative limit is not an
    // enforceable per-child RSS boundary.
}
