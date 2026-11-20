// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assembling a planned congruence derivation: restoring the recorded clause,
//! and closing the fragment so the strict checker can replay it.
//!
//! Split out of `congruence_derivation` so each file stays inside the
//! repository's per-file line ceiling.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TermStore};

use super::{CongruenceDerivation, MAX_DERIVATION_STEPS};

/// Close a planned derivation into a self-contained refutation the strict
/// checker can replay, changing NOTHING about the derivation itself.
///
/// `check_proof_strict` demands a closed proof, so the fragment is closed over
/// the negation of each literal of its own conclusion: assume `¬l`, resolve it
/// away, finish on the empty clause. Every step of the DERIVATION is validated
/// on the way by exactly the validators the mandatory gate runs. Shared, so the
/// producer's admission gate and the tests' gate cannot drift.
#[must_use]
pub fn close_congruence_derivation(
    terms: &mut TermStore,
    derivation: &CongruenceDerivation,
) -> Proof {
    let mut proof = Proof::default();
    proof.steps.extend(derivation.steps.iter().cloned());
    let Some(last) = derivation.steps.len().checked_sub(1) else {
        return proof;
    };
    let mut current = derivation.clause.clone();
    let mut current_id = ProofId(u32::try_from(last).unwrap_or(u32::MAX));
    for &literal in &derivation.clause {
        let negated = complement_of(terms, literal);
        let assumed = ProofId(u32::try_from(proof.steps.len()).unwrap_or(u32::MAX));
        proof.steps.push(ProofStep::Assume(negated));
        current.retain(|other| *other != literal);
        let resolved = ProofId(u32::try_from(proof.steps.len()).unwrap_or(u32::MAX));
        proof.steps.push(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: current.clone(),
            premises: vec![current_id, assumed],
            args: Vec::new(),
        });
        current_id = resolved;
    }
    proof
}

/// The SYNTACTIC complement of `literal` — the term the closing resolution can
/// actually cancel it against.
///
/// `mk_not` is the right answer for the literal shapes this closer was written
/// for: it wraps a positive literal in one `Not` and cancels the wrapper off a
/// negative one, which is exactly the proof IR's Boolean normalization. It is
/// the WRONG answer for a literal that is itself an `and`/`or`/`ite`, because
/// it returns the De Morgan DUAL — Boolean-equivalent, but not a resolution
/// complement, so the closing step is refused and a perfectly good fragment is
/// declined. Measured on `soundness_qf_uf_incremental/clearsy_0000_00307`: the
/// unit `(cl (or (= (bool p) (bool q)) (not (= p q))))` closed against
/// `(and (= p q) (not (= (bool p) (bool q))))` and the strict checker answered
/// `invalid resolution derivation`.
///
/// So: take `mk_not`'s answer when it IS the complement, and the raw `Not`
/// wrapper otherwise. This only ever admits fragments the closer previously
/// refused for a reason that was not about the fragment; the closed proof is
/// still replayed in full by `check_proof_strict`, which remains the only
/// authority over what may be committed.
fn complement_of(terms: &mut TermStore, literal: TermId) -> TermId {
    let normalized = terms.mk_not(literal);
    let cancels = match terms.get(normalized) {
        ay_core::TermData::Not(inner) => *inner == literal,
        _ => matches!(terms.get(literal), ay_core::TermData::Not(inner) if *inner == normalized),
    };
    if cancels {
        normalized
    } else {
        terms.mk_not_raw(literal)
    }
}

/// Weaken the derived clause back to every recorded hypothesis and restore the
/// recorded literal order, so the replacement is invisible to every consumer.
pub(super) fn finish(
    steps: &mut Vec<ProofStep>,
    step: usize,
    clause: Vec<TermId>,
    literals: &[TermId],
) -> Option<CongruenceDerivation> {
    if !clause.iter().all(|literal| literals.contains(literal)) {
        return None;
    }
    let mut last = step;
    let mut current = clause;
    // A tautology step legitimately REPEATS a literal: `(= (g a b) (g b a))`
    // under `a = b` needs the same premise equality at both argument
    // positions, and `eq_congruent` consumes one premise per differing
    // position. `weakening`/`reordering` are multiset rules, so the repeat is
    // removed first — by `contraction`, whose validator decides exactly that.
    if current
        .iter()
        .enumerate()
        .any(|(position, literal)| current[..position].contains(literal))
    {
        let mut contracted: Vec<TermId> = Vec::with_capacity(current.len());
        for &literal in &current {
            if !contracted.contains(&literal) {
                contracted.push(literal);
            }
        }
        last = push_derived(steps, AletheRule::Contraction, contracted.clone(), last)?;
        current = contracted;
    }
    if current.len() != literals.len() {
        // `weakening` requires its premise to be a PREFIX of the result.
        let mut widened = current.clone();
        widened.extend(literals.iter().copied().filter(|l| !current.contains(l)));
        last = push_derived(steps, AletheRule::Weakening, widened.clone(), last)?;
        current = widened;
    }
    if current != literals {
        last = push_derived(steps, AletheRule::Reordering, literals.to_vec(), last)?;
    }
    if last + 1 != steps.len() {
        return None;
    }
    Some(CongruenceDerivation {
        steps: std::mem::take(steps),
        clause: literals.to_vec(),
    })
}

/// Push a one-premise step and return its index.
fn push_derived(
    steps: &mut Vec<ProofStep>,
    rule: AletheRule,
    clause: Vec<TermId>,
    premise: usize,
) -> Option<usize> {
    if steps.len() >= MAX_DERIVATION_STEPS {
        return None;
    }
    let id = steps.len();
    steps.push(ProofStep::Step {
        rule,
        clause,
        premises: vec![ProofId(u32::try_from(premise).ok()?)],
        args: Vec::new(),
    });
    Some(id)
}

/// Rendering work one renderability check may spend.
///
/// A planned fragment carries whole authored roots as literals, and the
/// printer streams every occurrence of a shared application again, so the
/// text a check writes grows with the root's TREE size, not its DAG size.
/// MEASURED on CHC-COMP 2026 LRA-Lin `oral_messages` (`ec4cd5b8abaf3a98`):
/// an authored root of 4,659 DAG nodes is 1.03e14 tree nodes, and the
/// unbounded check built one 1.3 GB `String` and ended the whole portfolio in
/// a 5 GB memout ~4 s in. Declining a fragment keeps its `trust` leaf, so the
/// proof is unchanged and nothing new is published.
///
/// # What the budget bounds
///
/// The check's printer charges every byte it writes into any `String`: a
/// streamed application its own syntax, a cached or override text its length
/// when copied, and an assembled `not`/`ite`/`let`/quantifier/constant array
/// its FULL length when built, on top of what its children charged (the
/// export's own counter, unchanged). So `work_used()` is at least the bytes of
/// every assembled `String` the check allocates, the ones `format_cache`
/// retains included. The check runs in
/// `AssembledRendering::CachedWithinBudget` mode, so nothing is assembled
/// once `work_used()` passes the budget `B`; the last thing built before that
/// is at most one assembly (whose children were already charged, so at most
/// `B` plus its own syntax), one cached copy (at most `B` plus syntax) or one
/// override's text. Hence `work_used() <= 2B + max(override text)`, and the
/// live strings (the cache, the children copies an assembly holds, the step
/// line) are at most three times that. For `B` = 32 MiB: at most 64 MiB
/// charged and 192 MiB of live strings per check, whatever the tree size.
///
/// MEASURED on the review probe (DR-PROOF-RENDER-BUDGET-20261118): the
/// conjunct fragment of `(and (= E_400 0) (= x0 1))`, `E_{i+1} = (ite p_i A_i
/// E_i)` over distinct 28 KB branches `A_i` (14.3 MB of text), is declined
/// after 33.7 MB of charged work with a 55.5 MB peak RSS for the whole test
/// process (4.9 MB for an empty test). The export's counter alone, still
/// assembling every level after exhaustion, charged 2.81 GB and peaked at
/// 3.73 GB; a counter of output bytes alone peaked at 3.73 GB too.
pub const DERIVATION_RENDER_WORK_BUDGET: u64 = 32 << 20;

/// The answer of one bounded renderability check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DerivationRender {
    /// Every step rendered within the budget.
    Renders,
    /// The printer refused a step for a reason other than the budget or a
    /// stop: the export would refuse it too.
    Unrenderable,
    /// The check ran out of its work budget, or the caller stopped it. Says
    /// nothing about a cheaper derivation over the same terms, but any
    /// derivation whose first steps are these exhausts the same way.
    OutOfBudget,
}

impl DerivationRender {
    /// Whether the derivation may be published.
    #[must_use]
    pub fn renders(self) -> bool {
        self == Self::Renders
    }
}

/// Whether every step of a planned derivation RENDERS under the same surface
/// overrides the exporter will use, within `max_work` of rendering work (see
/// [`DERIVATION_RENDER_WORK_BUDGET`] for what that bounds) and while
/// `keep_going` admits it.
///
/// The printer is fail-loud: a step it cannot render as a spec-valid Alethe
/// inference makes the whole export refuse to publish, which turns a published
/// `unsat` into no answer at all. Deciding that HERE, with the printer itself,
/// means the producer declines exactly the fragments the exporter would refuse
/// — no second opinion, no drift.
///
/// Running out of `max_work`, or `keep_going` answering `false` (the asking
/// solve's interrupt, deadline or memory limit), is
/// [`DerivationRender::OutOfBudget`], which every caller reads as a decline.
/// There is deliberately no unbounded twin.
#[must_use]
pub fn congruence_derivation_renders_within(
    terms: &TermStore,
    overrides: Option<&ay_core::kani_compat::DetHashMap<TermId, String>>,
    derivation: &CongruenceDerivation,
    max_work: u64,
    keep_going: &mut dyn FnMut() -> bool,
) -> DerivationRender {
    render_derivation_within(terms, overrides, derivation, max_work, keep_going).0
}

/// [`congruence_derivation_renders_within`], plus the rendering work the
/// check actually charged (the tests pin that it is bounded).
pub(crate) fn render_derivation_within(
    terms: &TermStore,
    overrides: Option<&ay_core::kani_compat::DetHashMap<TermId, String>>,
    derivation: &CongruenceDerivation,
    max_work: u64,
    keep_going: &mut dyn FnMut() -> bool,
) -> (DerivationRender, u64) {
    let printer = crate::alethe_printer::AlethePrinter::new_with_overrides_and_budget(
        terms,
        overrides,
        Some(max_work),
    )
    .with_assembled_rendering(crate::alethe_printer::AssembledRendering::CachedWithinBudget)
    .as_renderability_check()
    .with_emission_progress(keep_going);
    let mut verdict = DerivationRender::Renders;
    for (index, step) in derivation.steps.iter().enumerate() {
        if printer
            .format_step(step, ProofId(u32::try_from(index).unwrap_or(u32::MAX)))
            .is_err()
        {
            verdict = if printer.work_budget_exhausted() {
                DerivationRender::OutOfBudget
            } else {
                DerivationRender::Unrenderable
            };
            break;
        }
    }
    (verdict, printer.work_used())
}

#[cfg(test)]
#[path = "congruence_derivation_closer_tests.rs"]
mod closer_tests;

#[cfg(test)]
#[path = "congruence_derivation_render_budget_tests.rs"]
mod render_budget_tests;
