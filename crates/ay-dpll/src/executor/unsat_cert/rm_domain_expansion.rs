// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The exact RoundingMode finite-domain UNSAT theorem (#P0.2 Pass C
//! certification).
//!
//! The FP lane DECIDES a query whose declared `RoundingMode` constants reach an
//! FP rounding-op operand by carrying each mode as three bits in one circuit
//! (`ay-theories/fp/src/rm.rs`; before 2026-09-30 by case-splitting the five
//! modes, `theories/fp/rm_expand.rs`). Neither form says what it proved in a
//! form the mandatory certification funnel checks, so before this module two
//! correct refutations published as `unknown` in every certified mode while
//! `--competition` printed `unsat` for the same queries.
//!
//! This module is the independent derivation the funnel can consume. It reads
//! NOTHING from the FP lane — not its verdict, not its session — and re-expands
//! the immutable public-query roots itself.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData, TermEntryStamp, TermStoreSnapshotStamp};
use ay_core::{Sort as CoreSort, TermId, TermStore as CoreTermStore};
use ay_frontend::SourceContextStamp;
use std::cell::Cell;

use super::{CheckedExactClosedForallUnsat, ProbeUnsatAuthority, UnsatCertificateKind};
use crate::executor::rm_domain::{
    fp_rounding_mode_operand, is_rm_literal, is_rm_sort, rm_literal_mode, rm_literal_term, RM_MODES,
};
use crate::executor::{CorroborationSource, Executor, QueryAuthorityEpoch, UnsatEvidence};
use crate::executor_types::SolveResult;

thread_local! {
    /// Re-entrancy depth for the RoundingMode finite-domain theorem
    /// (#P0.2 Pass C certification).
    ///
    /// Its branch refutations are full nested solves. Substituting the RM
    /// constants away means a branch carries no symbolic mode and cannot
    /// re-enter this lane on its own, but the guard is kept so that stays a
    /// property of the code rather than of one scope predicate: depth 0 only,
    /// the same discipline as `TRUST_DISCHARGE_DEPTH` and
    /// `CLOSED_SENTENCE_REFUTATION_DEPTH` in the parent module.
    static RM_DOMAIN_EXPANSION_DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// RAII entry into [`RM_DOMAIN_EXPANSION_DEPTH`].
struct RmDomainExpansionDepth;

impl RmDomainExpansionDepth {
    fn enter() -> Self {
        RM_DOMAIN_EXPANSION_DEPTH.with(|depth| depth.set(depth.get() + 1));
        Self
    }
}

impl Drop for RmDomainExpansionDepth {
    fn drop(&mut self) {
        RM_DOMAIN_EXPANSION_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
    }
}
/// Enumeration width of the RoundingMode finite-domain theorem: at most three
/// RM constants, hence at most `5^3 = 125` branches.  The bound is what makes
/// exhaustiveness a property of the CONSTRUCTION rather than of a budget — the
/// token seals the complete cross product and the checker re-derives its size,
/// so a truncated enumeration cannot be presented as a complete one.
const RM_DOMAIN_EXPANSION_MAX_VARS: usize = 3;

/// Per-branch budget for the independent refutation probe.  Exhausting it
/// DECLINES the whole theorem (grant-only): a branch AY cannot certify leaves
/// the ordinary fail-closed path in charge.
const RM_DOMAIN_EXPANSION_BRANCH_BUDGET_MS: u64 = 2_000;

/// Work ceiling for the read-only structural re-check of one substitution
/// image.  Bounds the checker independently of the producer.
const RM_DOMAIN_EXPANSION_WORK_LIMIT: usize = 1 << 16;

/// How one branch of the expansion was refuted.
///
/// Both arms are re-validated at consumption time in their own way: the
/// elementary arm is re-read off the live term store (a literal `false`
/// conjunct is a complete refutation and needs no solver at all), and the
/// checked arm rests on the sealed branch roots, whose entry stamps and
/// whole-store snapshot pin the exact objects the probe decided.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RmDomainExpansionRefutation {
    /// The substituted-and-folded roots contain the Boolean constant `false` at
    /// this index. This is the RoundingMode-domain fact doing the work
    /// directly: an authored `(= rm roundTowardPositive)` under `rm := RTN`
    /// folds to `false` because the five modes are five distinct elements.
    FalseConjunct { index: usize },
    /// A disposable probe published UNSAT for the exact branch roots through
    /// the whole mandatory certification funnel, on a checked authority (a
    /// strict proof, an independently re-checked refutation, or an exact
    /// semantic theorem).
    CheckedProbe,
    /// A disposable probe published UNSAT for the exact branch roots, but on
    /// `discharged-trust`: its holes were discharged by a fresh-executor
    /// re-solve of the same code, which is not an independent check. A branch
    /// refuted this way makes the whole expansion a `discharged-trust`
    /// admission (see [`CheckedExactRmDomainExpansionUnsat::rests_on_discharged_trust`]).
    DischargedTrustProbe,
}

/// One enumerated RoundingMode assignment and the exact root vector the
/// expansion refuted for it.
#[derive(Debug)]
struct RmDomainExpansionBranch {
    /// The RM literal term assigned to each expansion variable, in the
    /// theorem's `rm_vars` order.
    modes: Box<[TermId]>,
    mode_entries: Box<[TermEntryStamp]>,
    /// The authored roots with those literals substituted for the variables and
    /// the exposed RM-literal equality atoms folded to their truth constants.
    roots: Box<[TermId]>,
    root_entries: Box<[TermEntryStamp]>,
    refutation: RmDomainExpansionRefutation,
    /// The branch refutation's evidence: checked for an elementary `false`
    /// conjunct, the probe's own (level and corroboration) otherwise.
    evidence: UnsatEvidence,
}

/// Sealed source theorem for one exact RoundingMode finite-domain expansion.
///
/// `RoundingMode` is the FIXED five-element SMT-LIB domain
/// {RNE, RNA, RTP, RTN, RTZ}, so for RM constants `v1 … vk` the disjunction
/// `OR over (m1 … mk) in RM^k of (v1 = m1 AND … AND vk = mk)` is VALID in every
/// model of the FP theory.  The authored query is therefore satisfiable exactly
/// when SOME branch `roots[v := m]` is satisfiable, and a refutation of every
/// branch refutes the query.  The five-distinct-elements fact is the ONLY
/// semantic input, and it is used twice — both uses re-checkable:
///
/// * as TOTALITY, making the `5^k` cross product exhaustive, and
/// * as DISTINCTNESS, folding each exposed `(= <mode> <mode>)` atom to its
///   truth constant, which turns a branch contradicting an authored mode pin
///   into a root vector containing the literal `false`.
///
/// A branch is then refuted either elementarily (that `false` conjunct — no
/// solver participates, and the checker re-reads it off the live store) or by
/// [`Executor::checked_exact_unsat_solve`], which admits a disposable probe's
/// UNSAT only when the probe published it through the whole mandatory
/// certification funnel carrying a checked exact-query token.
///
/// What the certificate SAYS, and what the checker re-validates:
///
/// * the expansion variables are exactly the RM-sorted non-literal terms of the
///   authored roots, every one of them a plain `Var` (re-derived);
/// * the branch count is exactly `5^k` and branch `i` carries the canonical
///   base-5 decoding of `i` over [`RM_MODES`] (re-derived);
/// * each sealed branch root is EXACTLY the substitute-then-fold image of the
///   corresponding authored root (re-verified structurally, without building a
///   single term);
/// * every `FalseConjunct` branch really does hold `false` at the sealed index.
///
/// The `CheckedProbe` refutations are NOT re-run at consumption time, exactly
/// like the closed-sentence theorem's `NestedRefuted` obligations: the branch
/// roots are pinned by individual entry stamps and by the whole-store snapshot,
/// so any change to the objects the probes decided makes the token stale.
///
/// It is a SEMANTIC certificate, not a translated `forall_inst` artifact, so
/// every explicit proof or proof-checking mode continues to fail closed.
#[derive(Debug)]
pub(in crate::executor) struct CheckedExactRmDomainExpansionUnsat {
    query_epoch: QueryAuthorityEpoch,
    source_declaration_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[TermEntryStamp]>,
    rm_vars: Box<[TermId]>,
    rm_var_entries: Box<[TermEntryStamp]>,
    branches: Box<[RmDomainExpansionBranch]>,
    term_snapshot: TermStoreSnapshotStamp,
}

/// The RoundingMode constants an exact finite-domain expansion may range over.
///
/// Read-only, total, and grant-only: `None` on every shape outside the
/// theorem's fragment.  Requiring at least one variable in an FP rounding-mode
/// OPERAND slot keeps this lane to the fragment the FP-lane enumeration owns;
/// pure-RM pigeonhole queries stay with the EUF domain axioms that already
/// decide them.
fn exact_rm_domain_expansion_variables(
    terms: &CoreTermStore,
    roots: &[TermId],
) -> Option<Vec<TermId>> {
    let mut remaining = RM_DOMAIN_EXPANSION_WORK_LIMIT;
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    let mut variables: Vec<TermId> = Vec::new();
    let mut occupies_mode_slot = false;
    while let Some(term) = stack.pop() {
        if remaining == 0 || terms.entry_stamp(term).is_none() {
            return None;
        }
        remaining -= 1;
        if !seen.insert(term) {
            continue;
        }
        if is_rm_sort(terms.sort(term)) && !is_rm_literal(terms, term) {
            // A non-`Var` symbolic mode (an RM `ite`, an RM-valued UF
            // application) has no finite carrier this expansion can enumerate.
            if !matches!(terms.get(term), TermData::Var(..)) {
                return None;
            }
            if !variables.contains(&term) {
                variables.push(term);
            }
        }
        match terms.get(term) {
            TermData::App(symbol, args) => {
                if let Some(slot) = fp_rounding_mode_operand(symbol.name(), args) {
                    if is_rm_sort(terms.sort(slot)) && !is_rm_literal(terms, slot) {
                        occupies_mode_slot = true;
                    }
                }
                stack.extend_from_slice(args);
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                stack.push(*condition);
                stack.push(*then_branch);
                stack.push(*else_branch);
            }
            TermData::Const(_) | TermData::Var(..) => {}
            // `let` and quantifiers are outside the fragment the structural
            // image checker below walks, so decline before enumerating.
            // `TermData` is `#[non_exhaustive]`: a future shape declines too.
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return None,
            _ => return None,
        }
    }
    if variables.is_empty() || variables.len() > RM_DOMAIN_EXPANSION_MAX_VARS || !occupies_mode_slot
    {
        return None;
    }
    variables.sort_unstable_by_key(|term| term.0);
    Some(variables)
}

/// Map every two-operand `=` over RM-sorted operands to its truth constant.
///
/// After substitution every RM-sorted term is a mode LITERAL (the carrier scan
/// admits no other symbolic RM shape), so this is decidable by identity: the
/// five modes are five distinct elements. Leaving these atoms unfolded would
/// hand the SAT layer a free variable — the false-`sat` hole #6189 — and it is
/// also what makes the domain fact VISIBLE in the certificate: an authored pin
/// `(= rm roundTowardPositive)` under `rm := RTN` becomes the constant `false`,
/// and the checker re-reads that.
fn rm_literal_atom_folds(terms: &CoreTermStore, roots: &[TermId]) -> HashMap<TermId, TermId> {
    let mut folds: HashMap<TermId, TermId> = HashMap::default();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(symbol, args) => {
                stack.extend_from_slice(args);
                if let Some(value) = rm_literal_equality_value(terms, symbol, args) {
                    let constant = if value {
                        terms.true_term()
                    } else {
                        terms.false_term()
                    };
                    folds.insert(term, constant);
                }
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                stack.push(*condition);
                stack.push(*then_branch);
                stack.push(*else_branch);
            }
            _ => {}
        }
    }
    folds
}

/// The truth value of `(= <rm-literal> <rm-literal>)`, if `symbol`/`args` are
/// exactly that.  Shared by the producer's fold and the checker's re-read so
/// the two cannot drift.
fn rm_literal_equality_value(
    terms: &CoreTermStore,
    symbol: &Symbol,
    args: &[TermId],
) -> Option<bool> {
    if !matches!(symbol, Symbol::Named(name) if name == "=" && !terms.is_declared_function(name))
        || args.len() != 2
    {
        return None;
    }
    // Both operands must retain their typed builtin literal identity; a
    // display name on a free variable never licenses a constant fold.
    if !is_rm_sort(terms.sort(args[0])) || !is_rm_sort(terms.sort(args[1])) {
        return None;
    }
    let left = rm_literal_mode(terms, args[0])?;
    let right = rm_literal_mode(terms, args[1])?;
    Some(left == right)
}

/// Whether `image` is EXACTLY the capture-free image of `source` under the
/// RM-variable replacement `map`.
///
/// Verified read-only against the live term store: no term is constructed, so
/// the checker can run behind `&Executor` and cannot perturb the very snapshot
/// stamp that authenticates the token.  Every shape outside `App`/`Not`/`Ite`
/// and matching leaves rejects.
fn rm_domain_expansion_image_is_exact(
    terms: &CoreTermStore,
    source: TermId,
    image: TermId,
    map: &HashMap<TermId, TermId>,
) -> bool {
    let mut remaining = RM_DOMAIN_EXPANSION_WORK_LIMIT;
    let mut seen: HashSet<(TermId, TermId)> = HashSet::default();
    let mut stack: Vec<(TermId, TermId)> = vec![(source, image)];
    while let Some((left, right)) = stack.pop() {
        if remaining == 0 || terms.entry_stamp(left).is_none() || terms.entry_stamp(right).is_none()
        {
            return false;
        }
        remaining -= 1;
        if let Some(&replacement) = map.get(&left) {
            if right != replacement {
                return false;
            }
            continue;
        }
        if !seen.insert((left, right)) {
            continue;
        }
        // FOLD RULE, checked before the structural rule. A source `=` whose two
        // operands both become mode literals under `map` must have folded to
        // the matching Boolean constant; anything else is not this image.
        if let TermData::App(symbol, args) = terms.get(left) {
            let substituted: Vec<TermId> = args
                .iter()
                .map(|arg| map.get(arg).copied().unwrap_or(*arg))
                .collect();
            if let Some(value) = rm_literal_equality_value(terms, symbol, &substituted) {
                let expected = if value {
                    terms.true_term()
                } else {
                    terms.false_term()
                };
                if right != expected {
                    return false;
                }
                continue;
            }
        }
        match (terms.get(left), terms.get(right)) {
            (TermData::App(left_symbol, left_args), TermData::App(right_symbol, right_args))
                if left_symbol == right_symbol && left_args.len() == right_args.len() =>
            {
                for (&left_arg, &right_arg) in left_args.iter().zip(right_args.iter()) {
                    stack.push((left_arg, right_arg));
                }
            }
            (TermData::Not(left_inner), TermData::Not(right_inner)) => {
                stack.push((*left_inner, *right_inner));
            }
            (
                TermData::Ite(left_condition, left_then, left_else),
                TermData::Ite(right_condition, right_then, right_else),
            ) => {
                stack.push((*left_condition, *right_condition));
                stack.push((*left_then, *right_then));
                stack.push((*left_else, *right_else));
            }
            (TermData::Var(..), _) | (TermData::Const(_), _) => {
                // An unmapped leaf must survive substitution untouched.
                if left != right {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

impl CheckedExactRmDomainExpansionUnsat {
    /// Whether any branch was refuted only on a `discharged-trust` admission.
    ///
    /// The theorem is then no stronger than that branch: a floating-point
    /// branch refuted by the bit-blaster publishes on `discharged-trust`
    /// (the FP lane records no derivation), and sealing it here must not turn
    /// it into a checked semantic certificate. This is the D7 evidence defect
    /// (2026-09-23 hunt): nine wrong `unsat` answers, each a branch the D7
    /// bit-blaster refuted wrongly, were published as
    /// `checked-exact-rm-domain-expansion`.
    pub(super) fn rests_on_discharged_trust(&self) -> bool {
        self.branches.iter().any(|branch| {
            matches!(
                branch.refutation,
                RmDomainExpansionRefutation::DischargedTrustProbe
            )
        })
    }

    /// The theorem's evidence: that of its weakest branch refutation.
    pub(super) fn nested_evidence(&self) -> UnsatEvidence {
        self.branches
            .iter()
            .fold(UnsatEvidence::CHECKED, |weakest, branch| {
                weakest.weakest(branch.evidence)
            })
            .nested(CorroborationSource::NestedRmDomainExpansion)
    }

    /// `(branches, false_conjunct, checked_probe, discharged_trust_probe)`,
    /// for the #semantic-token census line.
    pub(super) fn refutation_counts(&self) -> (u32, u32, u32, u32) {
        let count = |wanted: fn(&RmDomainExpansionRefutation) -> bool| {
            let n = self
                .branches
                .iter()
                .filter(|branch| wanted(&branch.refutation))
                .count();
            u32::try_from(n).unwrap_or(u32::MAX)
        };
        (
            u32::try_from(self.branches.len()).unwrap_or(u32::MAX),
            count(|r| matches!(r, RmDomainExpansionRefutation::FalseConjunct { .. })),
            count(|r| matches!(r, RmDomainExpansionRefutation::CheckedProbe)),
            count(|r| matches!(r, RmDomainExpansionRefutation::DischargedTrustProbe)),
        )
    }

    pub(super) fn is_current(&self, executor: &Executor) -> bool {
        if crate::executor::model::scoped_term_evaluation_override_active()
            || !self
                .query_epoch
                .is_same_epoch(&executor.query_authority_epoch)
            || self.source_declaration_stamp != executor.ctx.source_context_stamp()
            || self.roots.as_ref() != executor.ctx.assertions.as_slice()
            || self.term_snapshot != executor.ctx.terms.snapshot_stamp()
            || !CheckedExactClosedForallUnsat::entries_are_current(
                &executor.ctx.terms,
                &self.roots,
                &self.root_entries,
            )
            || !CheckedExactClosedForallUnsat::entries_are_current(
                &executor.ctx.terms,
                &self.rm_vars,
                &self.rm_var_entries,
            )
        {
            return false;
        }
        // The carrier must still be exactly the one the cross product covers. A
        // root DAG holding a FOURTH RM constant would leave the sealed
        // enumeration a proper subset of the domain, which is the one way a
        // complete-by-construction expansion could silently become partial.
        if exact_rm_domain_expansion_variables(&executor.ctx.terms, &self.roots).as_deref()
            != Some(self.rm_vars.as_ref())
        {
            return false;
        }
        let Ok(exponent) = u32::try_from(self.rm_vars.len()) else {
            return false;
        };
        let Some(total) = 5usize.checked_pow(exponent) else {
            return false;
        };
        if self.branches.len() != total {
            return false;
        }
        for (index, branch) in self.branches.iter().enumerate() {
            if branch.modes.len() != self.rm_vars.len()
                || branch.roots.len() != self.roots.len()
                || !CheckedExactClosedForallUnsat::entries_are_current(
                    &executor.ctx.terms,
                    &branch.modes,
                    &branch.mode_entries,
                )
                || !CheckedExactClosedForallUnsat::entries_are_current(
                    &executor.ctx.terms,
                    &branch.roots,
                    &branch.root_entries,
                )
            {
                return false;
            }
            let mut digits = index;
            let mut map: HashMap<TermId, TermId> = HashMap::default();
            for (position, &mode_term) in branch.modes.iter().enumerate() {
                let expected = RM_MODES[digits % RM_MODES.len()];
                digits /= RM_MODES.len();
                if rm_literal_mode(&executor.ctx.terms, mode_term) != Some(expected)
                    || map.insert(self.rm_vars[position], mode_term).is_some()
                {
                    return false;
                }
            }
            if digits != 0 {
                return false;
            }
            for (&source, &image) in self.roots.iter().zip(branch.roots.iter()) {
                if !rm_domain_expansion_image_is_exact(&executor.ctx.terms, source, image, &map) {
                    return false;
                }
            }
            // The elementary refutation is re-read here, from the live store,
            // and needs nothing else: a root vector containing the constant
            // `false` is unsatisfiable outright.
            if let RmDomainExpansionRefutation::FalseConjunct { index } = branch.refutation {
                if branch.roots.get(index).copied() != Some(executor.ctx.terms.false_term()) {
                    return false;
                }
            }
        }
        true
    }
}
impl Executor {
    /// Independently re-expand the RoundingMode carrier of the immutable public
    /// roots and require an independently CERTIFIED refutation of every branch.
    ///
    /// This is the FP-lane counterpart of
    /// [`Self::try_authorize_current_query_exact_finite_expansion_unsat`]: a
    /// bounded finite expansion that mints a checkable token instead of leaving
    /// a computed refutation with nothing to say for itself.  It takes NOTHING
    /// from the FP lane's own decision (the three-bit mode encoding,
    /// `ay-theories/fp/src/rm.rs`) — not its verdict, not its session. It
    /// re-derives the carrier from the epoch roots, rebuilds all `5^k` images
    /// itself, and accepts a branch only on its own elementary `false` conjunct
    /// or on a disposable probe that published UNSAT for it through the whole
    /// mandatory certification funnel.
    ///
    /// FAIL-CLOSED PERIMETER.  Grant-only: `None` on every doubt, leaving the
    /// caller's existing fail-closed path untouched.  Explicit proof, strict,
    /// and self-check modes decline before paying for a single probe — the
    /// common mint would reject a semantic-only theorem there anyway.
    pub(in crate::executor) fn try_authorize_current_query_exact_rm_domain_expansion_unsat(
        &mut self,
    ) -> Option<CheckedExactRmDomainExpansionUnsat> {
        if crate::executor::model::scoped_term_evaluation_override_active()
            || !self.exact_plain_hard_unsat_scope_is_current()
            || self.should_abort_theory_loop()
            || self.strict_unsat_presentation_required()
            || RM_DOMAIN_EXPANSION_DEPTH.with(|depth| depth.get()) > 0
        {
            return None;
        }
        let (roots, root_entries) = {
            let epoch = self.unsat_query_epoch.as_ref()?;
            (epoch.assertions.clone(), epoch.assertion_entries.clone())
        };
        if roots.is_empty()
            || roots
                .iter()
                .any(|&root| self.ctx.terms.sort(root) != &CoreSort::Bool)
        {
            return None;
        }
        let rm_vars = exact_rm_domain_expansion_variables(&self.ctx.terms, &roots)?;
        let rm_var_entries = rm_vars
            .iter()
            .map(|&variable| self.ctx.terms.entry_stamp(variable))
            .collect::<Option<Vec<_>>>()?;
        let exponent = u32::try_from(rm_vars.len()).ok()?;
        let total = 5usize.checked_pow(exponent)?;

        let images = self.rm_domain_expansion_images(&roots, &rm_vars, total);
        let branches = self.rm_domain_expansion_branches(images)?;
        let term_snapshot = self.ctx.terms.snapshot_stamp();

        // Recheck after the probes: a disposable probe cannot touch the outer
        // query, source epoch, or term store, so any drift here is disqualifying.
        if !self.exact_plain_hard_unsat_scope_is_current()
            || self.should_abort_theory_loop()
            || !self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
                epoch.assertions == roots && epoch.assertion_entries == root_entries
            })
            || term_snapshot != self.ctx.terms.snapshot_stamp()
        {
            return None;
        }

        Some(CheckedExactRmDomainExpansionUnsat {
            query_epoch: self.query_authority_epoch.clone(),
            source_declaration_stamp: self.ctx.source_context_stamp(),
            roots: roots.into_boxed_slice(),
            root_entries: root_entries.into_boxed_slice(),
            rm_vars: rm_vars.into_boxed_slice(),
            rm_var_entries: rm_var_entries.into_boxed_slice(),
            branches: branches.into_boxed_slice(),
            term_snapshot,
        })
    }

    /// Every branch image, built BEFORE any branch is refuted.
    ///
    /// The refutation probes seal a term-store snapshot around themselves, so
    /// all term creation has to finish first; interleaving would invalidate each
    /// probe's own scope check.
    ///
    /// One image is `fold(subst(root))`: the mode literals of branch `index`
    /// substituted for the expansion variables, then every exposed RM-literal
    /// equality atom folded to its truth constant.
    fn rm_domain_expansion_images(
        &mut self,
        roots: &[TermId],
        rm_vars: &[TermId],
        total: usize,
    ) -> Vec<(Vec<TermId>, Vec<TermId>)> {
        let mut images: Vec<(Vec<TermId>, Vec<TermId>)> = Vec::with_capacity(total);
        for branch in 0..total {
            let mut digits = branch;
            let mut modes = Vec::with_capacity(rm_vars.len());
            for _ in 0..rm_vars.len() {
                let mode = RM_MODES[digits % RM_MODES.len()];
                digits /= RM_MODES.len();
                modes.push(rm_literal_term(&mut self.ctx.terms, mode));
            }
            let mut map: HashMap<TermId, TermId> = HashMap::default();
            for (position, &variable) in rm_vars.iter().enumerate() {
                map.insert(variable, modes[position]);
            }
            let substituted: Vec<TermId> = roots
                .iter()
                .map(|&root| self.ctx.terms.substitute_terms(root, &map))
                .collect();
            let folds = rm_literal_atom_folds(&self.ctx.terms, &substituted);
            let image: Vec<TermId> = if folds.is_empty() {
                substituted
            } else {
                substituted
                    .iter()
                    .map(|&root| self.ctx.terms.substitute_terms(root, &folds))
                    .collect()
            };
            images.push((modes, image));
        }
        images
    }

    /// Refute every branch, or DECLINE the whole theorem.
    ///
    /// Elementary first: a root vector holding the constant `false` is refuted
    /// outright, with no solver in the loop at all. Otherwise the branch goes to
    /// a disposable probe whose UNSAT counts only if it published through the
    /// whole mandatory certification funnel with a checked exact-query token —
    /// and the branch records WHICH authority admitted it, so a
    /// `discharged-trust` admission is never sealed as a checked one.
    fn rm_domain_expansion_branches(
        &mut self,
        images: Vec<(Vec<TermId>, Vec<TermId>)>,
    ) -> Option<Vec<RmDomainExpansionBranch>> {
        let _depth = RmDomainExpansionDepth::enter();
        let mut branches: Vec<RmDomainExpansionBranch> = Vec::with_capacity(images.len());
        for (modes, image) in images {
            if self.should_abort_theory_loop() {
                return None;
            }
            let false_term = self.ctx.terms.false_term();
            let mut evidence = UnsatEvidence::CHECKED;
            let refutation = match image.iter().position(|&root| root == false_term) {
                Some(index) => RmDomainExpansionRefutation::FalseConjunct { index },
                None => {
                    let certified = self.checked_exact_unsat_solve(
                        image.clone(),
                        RM_DOMAIN_EXPANSION_BRANCH_BUDGET_MS,
                    )?;
                    let authority = certified.authority();
                    evidence = certified.evidence();
                    if !certified.consume(self, &image) {
                        return None;
                    }
                    match authority {
                        ProbeUnsatAuthority::Checked => RmDomainExpansionRefutation::CheckedProbe,
                        ProbeUnsatAuthority::DischargedTrust => {
                            RmDomainExpansionRefutation::DischargedTrustProbe
                        }
                    }
                }
            };
            let mode_entries = modes
                .iter()
                .map(|&mode| self.ctx.terms.entry_stamp(mode))
                .collect::<Option<Vec<_>>>()?;
            let image_entries = image
                .iter()
                .map(|&root| self.ctx.terms.entry_stamp(root))
                .collect::<Option<Vec<_>>>()?;
            branches.push(RmDomainExpansionBranch {
                modes: modes.into_boxed_slice(),
                mode_entries: mode_entries.into_boxed_slice(),
                roots: image.into_boxed_slice(),
                root_entries: image_entries.into_boxed_slice(),
                refutation,
                evidence,
            });
        }
        Some(branches)
    }

    /// Emit UNSAT from the exact RoundingMode finite-domain expansion plus one
    /// refutation per branch — elementary, or independently certified.  It is
    /// semantic authority, not a translated `forall_inst` artifact, so explicit
    /// proof modes continue to fail closed.
    pub(in crate::executor) fn emit_checked_exact_rm_domain_expansion_unsat(
        &mut self,
        evidence: CheckedExactRmDomainExpansionUnsat,
    ) -> SolveResult {
        self.emit_checked_exact_unsat(
            UnsatCertificateKind::CheckedExactRmDomainExpansion(evidence),
            "checked exact RoundingMode-expansion UNSAT evidence was stale at emission",
            "checked exact RoundingMode-expansion UNSAT has no translated authored-scope proof for the requested proof artifact",
            "verdict_certification.checked_exact_rm_domain_expansion",
        )
    }
}

#[cfg(test)]
mod tests {
    use super::super::CommandUnsatAdmission;
    use super::{CheckedExactRmDomainExpansionUnsat, Executor};

    /// Execute a whole SMT-LIB script through the ordinary text-command
    /// boundary — the SAME route `tests/group_fp/fp_symbolic_rm.rs` takes, so
    /// these tests observe the publication path the regression is about.
    fn execute_script(executor: &mut Executor, source: &str) -> Vec<String> {
        let commands =
            ay_frontend::parse(source).expect("RoundingMode expansion fixture must parse");
        executor
            .execute_all(&commands)
            .expect("RoundingMode expansion script must execute")
    }

    /// The two authored shapes the FP-lane RoundingMode enumeration decides and
    /// the certification funnel used to discard (#P0.2 Pass C certification).
    const RM_WRONG_PIN_UNSAT_SCRIPT: &str = "(declare-const rm RoundingMode) \
         (assert (= (fp.roundToIntegral rm ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 2.0))) \
         (assert (= rm roundTowardPositive))";

    const RM_EQUAL_PAIR_UNSAT_SCRIPT: &str = "(declare-const r1 RoundingMode) \
         (declare-const r2 RoundingMode) \
         (assert (= r1 r2)) \
         (assert (= (fp.roundToIntegral r1 ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 3.0))) \
         (assert (= (fp.roundToIntegral r2 ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 2.0)))";

    fn rm_domain_expansion_evidence(
        source: &str,
    ) -> (Executor, CheckedExactRmDomainExpansionUnsat) {
        let commands =
            ay_frontend::parse(source).expect("RoundingMode expansion fixture must parse");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("RoundingMode expansion fixture must elaborate");
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let evidence = executor
            .try_authorize_current_query_exact_rm_domain_expansion_unsat()
            .expect("the authored RoundingMode carrier must expand and refute every branch");
        (executor, evidence)
    }

    /// Integral rounding has an independent exact checker. Every branch must
    /// now carry checked evidence; a trusted branch would invalidate this
    /// stronger admission even if the solver's UNSAT result remained right.
    #[test]
    fn rm_domain_expansion_of_integral_rounding_has_checked_branches() {
        for source in [RM_WRONG_PIN_UNSAT_SCRIPT, RM_EQUAL_PAIR_UNSAT_SCRIPT] {
            let mut executor = Executor::new();
            let outputs = execute_script(&mut executor, &format!("{source} (check-sat)"));

            assert_eq!(outputs, vec!["unsat"], "{source}");
            assert_eq!(
                executor.last_command_unsat_admission,
                Some(CommandUnsatAdmission::CheckedExactRmDomainExpansion),
                "{source}"
            );
            assert!(
                executor.last_command_unsat_was_exact_semantically_verified(),
                "{source}"
            );
            let (_, evidence) = rm_domain_expansion_evidence(source);
            assert!(!evidence.rests_on_discharged_trust(), "{source}");
            let (branches, false_conjunct, checked, trust) = evidence.refutation_counts();
            assert_eq!(branches, false_conjunct + checked + trust, "{source}");
            assert_eq!(trust, 0, "{source}");
        }
    }

    /// Every branch folded to `false`: nothing but the five-distinct-modes fact
    /// did the work, the checker re-reads each `false` conjunct itself, and the
    /// lane's own checked class stands.
    #[test]
    fn rm_domain_expansion_of_false_conjuncts_alone_is_checked() {
        let source = "(declare-const rm RoundingMode) \
             (assert (fp.isNaN (fp.roundToIntegral rm ((_ to_fp 8 24) RNE 2.5)))) \
             (assert (= rm roundTowardPositive)) \
             (assert (= rm roundTowardNegative))";
        let mut executor = Executor::new();
        let outputs = execute_script(&mut executor, &format!("{source} (check-sat)"));
        assert_eq!(outputs, vec!["unsat"]);
        assert_eq!(
            executor.last_command_unsat_admission,
            Some(CommandUnsatAdmission::CheckedExactRmDomainExpansion)
        );
        let (_, evidence) = rm_domain_expansion_evidence(source);
        assert!(!evidence.rests_on_discharged_trust());
        let (branches, false_conjunct, _, trust) = evidence.refutation_counts();
        assert_eq!((branches, false_conjunct, trust), (5, 5, 0));
    }

    /// Every branch refuted by a STRICT proof: the lane's checked class
    /// stands, and each branch's derivation is trust-free.
    ///
    /// The 2026-09-23 fp-strings verifier (E1) read `unproved_steps=1` on each
    /// branch of this shape (its fresh `g5_00027`) as a hole in the branch's
    /// derivation. It is not one: the branch's FP lemma is `FpGroundEval`,
    /// which AY's strict checker validates with the exact IEEE-754 evaluator,
    /// and which the Alethe printer downgrades to `hole` only because no
    /// pinned external checker can spell it (`--debug-cert`: `c !! wire
    /// downgrade ... kind FpGroundEval prints as hole`). A checked admission
    /// may seal only branches like these, so this test fails if the lane is
    /// ever admitted as `checked-exact-rm-domain-expansion` over a branch whose
    /// derivation holds a `trust` or `hole` step.
    #[test]
    fn rm_domain_expansion_over_strict_checked_fp_branches_is_checked() {
        let source = "(declare-const r RoundingMode) \
             (declare-const q Real) \
             (declare-const x0 (_ FloatingPoint 3 5)) \
             (assert (= x0 ((_ to_fp 3 5) RTZ q))) \
             (assert (= q 1000.0)) \
             (assert (fp.isZero (fp.div r (fp #b1 #b110 #b0111) (_ +zero 3 5))))";
        let mut executor = Executor::new();
        let outputs = execute_script(&mut executor, &format!("{source} (check-sat)"));
        assert_eq!(outputs, vec!["unsat"]);
        assert_eq!(
            executor.last_command_unsat_admission,
            Some(CommandUnsatAdmission::CheckedExactRmDomainExpansion)
        );
        let (_, evidence) = rm_domain_expansion_evidence(source);
        assert!(!evidence.rests_on_discharged_trust());
        let (branches, false_conjunct, checked, trust) = evidence.refutation_counts();
        assert_eq!((branches, false_conjunct, checked, trust), (5, 0, 5, 0));

        for mode in ["RNE", "RNA", "RTP", "RTN", "RTZ"] {
            let branch = source
                .replace("(declare-const r RoundingMode) ", "")
                .replace("fp.div r ", &format!("fp.div {mode} "));
            let mut executor = Executor::new();
            let outputs = execute_script(&mut executor, &format!("{branch} (check-sat)"));
            assert_eq!(outputs, vec!["unsat"], "{mode}");
            assert_eq!(
                executor.last_command_unsat_admission,
                Some(CommandUnsatAdmission::StrictProof),
                "{mode}"
            );
            let proof = executor
                .last_proof
                .as_ref()
                .expect("a strict-proof branch retains its derivation");
            let report = ay_proof::terminal_trust_report(proof);
            assert!(
                report.is_trust_free(),
                "{mode}: the branch's derivation must reach the empty clause through \
                 no trust or hole step: {report:?}"
            );
        }
    }

    /// The fail-closed half is untouched: a semantic theorem is not a proof.
    ///
    /// Self-check promises an independently verified refutation, and this token
    /// is not one, so the mint declines before probing and the verdict stays
    /// `unknown`. If this ever publishes `unsat`, the exact-semantic lane has
    /// started answering a question it was never asked.
    #[test]
    fn rm_domain_expansion_stays_fail_closed_under_self_check() {
        for source in [RM_WRONG_PIN_UNSAT_SCRIPT, RM_EQUAL_PAIR_UNSAT_SCRIPT] {
            let mut executor = Executor::new();
            executor.set_self_check(true);
            let outputs = execute_script(&mut executor, &format!("{source} (check-sat)"));

            assert_eq!(outputs, vec!["unknown"], "{source}");
            assert_eq!(
                executor.last_command_unsat_admission, None,
                "no UNSAT admission may be recorded under a proof demand: {source}"
            );
        }
    }

    /// MUTATION: drop one branch of the cross product.
    ///
    /// Exhaustiveness is the whole theorem — `5^k` branches or nothing. A token
    /// that has certified only `5^k - 1` of them has proved the query unsat on
    /// a PROPER SUBSET of the RoundingMode domain, which is no theorem at all.
    #[test]
    fn rm_domain_expansion_token_rejects_a_truncated_cross_product() {
        for source in [RM_WRONG_PIN_UNSAT_SCRIPT, RM_EQUAL_PAIR_UNSAT_SCRIPT] {
            let (executor, evidence) = rm_domain_expansion_evidence(source);
            assert!(
                evidence.is_current(&executor),
                "the unmutated theorem must authenticate: {source}"
            );
            let expected = 5usize.pow(u32::try_from(evidence.rm_vars.len()).expect("k fits"));
            assert_eq!(evidence.branches.len(), expected, "{source}");

            let mut truncated = evidence;
            let mut branches = truncated.branches.into_vec();
            branches.pop().expect("the enumeration has branches");
            truncated.branches = branches.into_boxed_slice();
            assert!(
                !truncated.is_current(&executor),
                "a truncated RoundingMode cross product must not authenticate: {source}"
            );
        }
    }

    /// MUTATION: keep every branch, but retarget one branch's roots at another
    /// branch's image.
    ///
    /// The branch count still says `5^k` and every sealed term is still live and
    /// current, so only the structural substitution re-check can catch this. It
    /// is the shape a certificate that merely COUNTED its branches would admit:
    /// one mode of the domain certified twice and another not at all.
    #[test]
    fn rm_domain_expansion_token_rejects_a_forged_substitution_image() {
        for source in [RM_WRONG_PIN_UNSAT_SCRIPT, RM_EQUAL_PAIR_UNSAT_SCRIPT] {
            let (executor, mut evidence) = rm_domain_expansion_evidence(source);
            assert!(evidence.is_current(&executor), "{source}");

            let mut branches = evidence.branches.into_vec();
            let donor_roots = branches[0].roots.clone();
            let donor_entries = branches[0].root_entries.clone();
            branches[1].roots = donor_roots;
            branches[1].root_entries = donor_entries;
            evidence.branches = branches.into_boxed_slice();
            assert!(
                !evidence.is_current(&executor),
                "a branch whose roots are not its own substitution image must \
                 not authenticate: {source}"
            );
        }
    }

    /// MUTATION: relabel one branch's mode tuple.
    ///
    /// Index `i` must carry the canonical base-5 decoding of `i` over
    /// `RM_MODES`. Without that the sealed vector is an unordered bag and two
    /// branches could name the same assignment.
    #[test]
    fn rm_domain_expansion_token_rejects_a_permuted_mode_tuple() {
        let (executor, mut evidence) = rm_domain_expansion_evidence(RM_WRONG_PIN_UNSAT_SCRIPT);
        assert!(evidence.is_current(&executor));

        let mut branches = evidence.branches.into_vec();
        let donor_modes = branches[0].modes.clone();
        let donor_entries = branches[0].mode_entries.clone();
        branches[1].modes = donor_modes;
        branches[1].mode_entries = donor_entries;
        evidence.branches = branches.into_boxed_slice();
        assert!(
            !evidence.is_current(&executor),
            "branch i must carry the canonical decoding of i"
        );
    }
}
