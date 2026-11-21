// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The theory plug-in interface (design §5).
//!
//! A plug-in never returns a request for an outer loop. Everything it wants
//! the search to know goes through [`Ctx`]: propagations, lemmas and
//! conflicts. A lemma may name any Boolean term; the kernel gives a term
//! without a SAT variable a fresh one during the search (§3.3).

use ay_core::{
    AtomHandle, Effort, FarkasAnnotation, StrengthenId, TermId, TermStore, TheoryLemmaKind,
    TheoryLit,
};
use ay_sat::{SolverContext, Variable};

use crate::atoms::AtomTable;
use crate::hub::Hub;
use crate::kernel::Relevancy;

mod hub_view;
use crate::engine::Guard;
use crate::reserved::{AsyncJob, AtomSet, ConjCore, Share};

/// Ticks between two guard polls in [`Ctx::tick`].
const TICKS_PER_POLL: u64 = 64;

/// Index of a plug-in inside one engine.
pub type ThId = u8;

/// A plug-in-local theory variable attached to an e-graph node (design H1).
///
/// The hub stores `(plug-in, variable)` pairs on its nodes and raises
/// `new_eq` when two classes carrying variables of one plug-in merge.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ThVar(pub u32);

/// A plug-in could not decide; the check ends `unknown` with this reason and
/// never `sat` (design §3.6).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GiveUp {
    /// Human-readable reason, reported as the check's unknown reason.
    pub reason: String,
}

impl GiveUp {
    /// Create a give-up with a reason.
    pub fn new(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
        }
    }
}

/// Lifetime tier of a lemma (design K5).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LemmaTier {
    /// A re-derivable theory tautology: goes to ay-sat's deletable tier.
    Redundant,
    /// A definition of a kernel-introduced symbol, or anything nothing would
    /// re-derive: irredundant, through ay-sat G1 (never deleted, survives a
    /// destructive rebuild).
    Definitional,
}

/// What justifies a clause, recorded when the kernel makes it a SAT clause
/// (design P1). The kind is one of the checker's existing lemma kinds.
///
/// A clause no single kind states can be justified by `premises`: smaller
/// theory clauses, each with its own hint, from which the clause follows by
/// resolution (design §6: an explanation through a hub equality is two steps
/// joined by theory resolution). The proof assembler emits the premises and
/// derives the clause from them; `kind` then plays no part.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofHint {
    /// The lemma kind the independent checker validates.
    pub kind: TheoryLemmaKind,
    /// Farkas coefficients, when the plug-in has them and proofs are on,
    /// aligned with the clause the hint justifies. For an explanation that
    /// clause is `[lit, ¬reason₀, ¬reason₁, …]`, the reason clause the kernel
    /// records.
    pub farkas: Option<FarkasAnnotation>,
    /// Theory clauses the clause follows from by resolution (see above).
    pub premises: Vec<HintPremise>,
}

/// One theory clause a [`ProofHint`] derives its clause from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HintPremise {
    /// The premise clause; its atoms need no SAT variable.
    pub clause: Vec<TheoryLit>,
    /// Its own justification.
    pub hint: ProofHint,
}

impl ProofHint {
    /// A hint with a kind and no payload.
    pub const fn kind(kind: TheoryLemmaKind) -> Self {
        Self {
            kind,
            farkas: None,
            premises: Vec::new(),
        }
    }

    /// An `LraFarkas` hint carrying its certificate.
    pub const fn farkas(farkas: FarkasAnnotation) -> Self {
        Self {
            kind: TheoryLemmaKind::LraFarkas,
            farkas: Some(farkas),
            premises: Vec::new(),
        }
    }

    /// A clause justified by resolution from `premises`.
    pub const fn derived(premises: Vec<HintPremise>) -> Self {
        Self {
            kind: TheoryLemmaKind::Generic,
            farkas: None,
            premises,
        }
    }
}

/// A clause the plug-in asserts is T-valid (or, for `Definitional`, a
/// conservative definition). Design K4: no other kind of clause may be added.
#[derive(Debug, Clone)]
pub struct Lemma {
    /// The clause, as signed Boolean terms.
    pub clause: Vec<TheoryLit>,
    /// Deletable or irredundant.
    pub tier: LemmaTier,
    /// Proof hint.
    pub hint: ProofHint,
}

/// A set of currently TRUE literals the theory refutes.
#[derive(Debug, Clone)]
pub struct Conflict {
    /// Literals, each true under the current assignment.
    pub lits: Vec<TheoryLit>,
    /// Proof hint for the clause that negates them.
    pub hint: ProofHint,
}

/// Why a propagated literal holds.
#[derive(Debug, Clone)]
pub enum Justification {
    /// The antecedent literals (each currently true) and the proof hint.
    Eager(Explanation),
    /// A plug-in token; [`TheoryPlugin::explain`] materializes it on demand.
    Lazy(u64),
}

/// The answer to [`TheoryPlugin::explain`].
#[derive(Debug, Clone)]
pub struct Explanation {
    /// The antecedent literals, each true when the propagation was made.
    pub reason: Vec<TheoryLit>,
    /// Proof hint for the reason clause.
    pub hint: ProofHint,
}

/// Outcome of a final check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Final {
    /// The plug-in accepts the full assignment.
    Sat,
    /// The plug-in has emitted lemmas or a conflict through [`Ctx`].
    Continue,
}

/// A propagation as buffered by [`Ctx`], with the plug-in that made it.
#[derive(Debug, Clone)]
pub(crate) struct Propagation {
    pub(crate) plugin: ThId,
    pub(crate) lit: TheoryLit,
    pub(crate) why: Justification,
}

/// Effects a plug-in produced during one callback.
#[derive(Debug, Default)]
pub(crate) struct Effects {
    pub(crate) props: Vec<Propagation>,
    pub(crate) lemmas: Vec<Lemma>,
    pub(crate) conflict: Option<Conflict>,
    pub(crate) preferred: Vec<TheoryLit>,
    /// Work units the callback reported through [`Ctx::tick`].
    pub(crate) ticks: u64,
    /// Strengthenings the callback registered (KC26).
    pub(crate) sigma: Vec<StrengthenId>,
}

/// What a plug-in callback may see and do (design K3).
///
/// It lends the term store for the duration of one callback; a plug-in must
/// not keep a reference into it past the callback.
pub struct Ctx<'k> {
    terms: &'k mut TermStore,
    sat: Option<&'k dyn SolverContext>,
    atoms: &'k AtomTable,
    hub: Option<&'k Hub>,
    out: &'k mut Effects,
    plugin: ThId,
    proofs: bool,
    guard: Option<&'k Guard>,
    relevancy: Option<&'k Relevancy>,
}

impl<'k> Ctx<'k> {
    pub(crate) fn new(
        terms: &'k mut TermStore,
        sat: Option<&'k dyn SolverContext>,
        atoms: &'k AtomTable,
        hub: Option<&'k Hub>,
        out: &'k mut Effects,
        plugin: ThId,
        proofs: bool,
    ) -> Self {
        Self {
            terms,
            sat,
            atoms,
            hub,
            out,
            plugin,
            proofs,
            guard: None,
            relevancy: None,
        }
    }

    /// Let [`Ctx::is_relevant`] read the kernel's relevancy service.
    pub(crate) const fn with_relevancy(mut self, relevancy: Option<&'k Relevancy>) -> Self {
        self.relevancy = relevancy;
        self
    }

    /// Let [`Ctx::tick`] poll the check's guard.
    pub(crate) const fn with_guard(mut self, guard: Option<&'k Guard>) -> Self {
        self.guard = guard;
        self
    }

    /// Spend `cost` units on the original resource owner on EVERY call,
    /// including charges smaller than 64. Effects retain statistics only;
    /// kernel aggregation must not spend these ticks for a second time.
    /// External deadline/stop predicates keep their existing 64-unit poll.
    pub fn tick(&mut self, cost: u64) -> Result<(), GiveUp> {
        let before = self.out.ticks;
        self.out.ticks = before.saturating_add(cost);
        // Observe the existing external precedence before the debit can latch
        // a newly exhausted resource allowance. Still debit on that refusal.
        let external = (before / TICKS_PER_POLL != self.out.ticks / TICKS_PER_POLL)
            .then(|| self.guard.and_then(Guard::exhausted))
            .flatten();
        let charged = self.guard.map_or(Ok(()), |guard| guard.charge_ticks(cost));
        match external.or_else(|| charged.err()) {
            Some(why) => Err(GiveUp::new(why.reason())),
            None => Ok(()),
        }
    }

    /// Whether `term` is relevant to the current assignment (KC21): the
    /// kernel's justification-based relevancy over the Tseitin structure,
    /// when the engine runs it; otherwise every term is.
    pub fn is_relevant(&self, term: TermId) -> bool {
        self.relevancy.is_none_or(|r| r.is_relevant(term))
    }

    /// Register a strengthening this plug-in applied (KC26): the check
    /// reports it in its outcome's Σ.
    pub fn strengthen(&mut self, id: StrengthenId) {
        if !self.out.sigma.contains(&id) {
            self.out.sigma.push(id);
        }
    }

    /// Read the term store.
    pub fn terms(&self) -> &TermStore {
        self.terms
    }

    /// Intern terms (for example the atoms of a split) during the search.
    pub fn terms_mut(&mut self) -> &mut TermStore {
        self.terms
    }

    /// The current SAT value of an atom, if it has a variable and is assigned.
    pub fn value(&self, atom: TermId) -> Option<bool> {
        let var = self.atoms.var_of(atom)?;
        self.sat?.value(Variable::new(var))
    }

    /// The current decision level (0 outside the search).
    pub fn decision_level(&self) -> u32 {
        self.sat.map_or(0, SolverContext::decision_level)
    }

    /// Whether proof recording is on; payloads are computed only then.
    pub const fn proofs_on(&self) -> bool {
        self.proofs
    }

    /// Propagate a literal of an atom that already has a SAT variable.
    pub fn propagate(&mut self, lit: TheoryLit, why: Justification) {
        let plugin = self.plugin;
        self.out.props.push(Propagation { plugin, lit, why });
    }

    /// Add a lemma; its atoms are minted if they have no variable.
    pub fn lemma(&mut self, lemma: Lemma) {
        self.out.lemmas.push(lemma);
    }

    /// Ask the search to decide this literal first (model-based combination,
    /// design H3): a speculative model equality is a decision, never a clause.
    /// Its atom must have a variable or be named by a lemma of the same
    /// callback.
    pub fn prefer(&mut self, lit: TheoryLit) {
        self.out.preferred.push(lit);
    }

    /// Report a conflict. The first conflict of a callback wins.
    pub fn conflict(&mut self, conflict: Conflict) {
        if self.out.conflict.is_none() {
            self.out.conflict = Some(conflict);
        }
    }
}

/// A theory, as the kernel sees it (design §5).
///
/// Scopes follow SAT decision levels: `push_scope` once per level, `pop_scope`
/// on backjump. User-level push/pop needs no plug-in call, because every
/// kernel clause is T-valid or definitional (K4).
///
/// `Send` (KC7): an engine, with its plug-ins, may move to another worker
/// thread between checks. A plug-in keeps its state in owned fields (or
/// `Arc`), never in `Rc` or a thread-local; `tests/kc7_no_thread_local.rs`
/// fails if a thread-local appears in this crate.
pub trait TheoryPlugin: Send {
    /// Short name for statistics and give-up reasons.
    fn name(&self) -> &'static str;

    /// A Boolean atom this plug-in owns now has a SAT variable. The answer is
    /// the plug-in's dense handle for it (KC3), which [`Self::assign`]
    /// receives: typically the atom's index in the plug-in's own table. The
    /// kernel calls this once per atom and check.
    fn internalize_atom(&mut self, ctx: &mut Ctx<'_>, atom: TermId) -> Result<AtomHandle, GiveUp>;

    /// Attach a theory variable to a shared term (called by the hub, H1).
    fn attach_term(&mut self, _ctx: &mut Ctx<'_>, _term: TermId) -> Result<Option<ThVar>, GiveUp> {
        Ok(None)
    }

    /// An owned atom, named by the handle [`Self::internalize_atom`] gave it,
    /// was assigned.
    fn assign(&mut self, ctx: &mut Ctx<'_>, atom: AtomHandle, value: bool) -> Result<(), GiveUp>;

    /// Two terms carrying this plug-in's theory variables were merged (H1).
    fn new_eq(
        &mut self,
        _ctx: &mut Ctx<'_>,
        _a: ThVar,
        _b: ThVar,
        _why: &[TheoryLit],
    ) -> Result<(), GiveUp> {
        Ok(())
    }

    /// Two such terms were made distinct (H1).
    fn new_diseq(
        &mut self,
        _ctx: &mut Ctx<'_>,
        _a: ThVar,
        _b: ThVar,
        _why: &[TheoryLit],
    ) -> Result<(), GiveUp> {
        Ok(())
    }

    /// Cheap propagation: work proportional to the facts since the last call
    /// (K6). There is deliberately no default that runs the final check.
    fn propagate(&mut self, ctx: &mut Ctx<'_>) -> Result<(), GiveUp>;

    /// Whether `propagate` could do anything now (design §12, per-plug-in
    /// gating). `false` lets the kernel skip the call; the default is safe.
    fn can_propagate(&self) -> bool {
        true
    }

    /// Check a full assignment at one effort level (KC8). The kernel asks
    /// every level in [`Effort::ALL`] order and moves on only when every
    /// plug-in answers [`Final::Sat`] at the current one; a plug-in answers
    /// `Sat` at every level where it has nothing to do. Within a level the
    /// plug-ins take fair turns (`kernel/schedule.rs`).
    fn final_check(&mut self, ctx: &mut Ctx<'_>, effort: Effort) -> Result<Final, GiveUp>;

    /// Materialize a lazy propagation's reason during conflict analysis.
    fn explain(&mut self, ctx: &mut Ctx<'_>, lit: TheoryLit, token: u64) -> Option<Explanation>;

    /// Open a scope for a new decision level.
    fn push_scope(&mut self, ctx: &mut Ctx<'_>);

    /// Close `n` scopes on backjump.
    fn pop_scope(&mut self, ctx: &mut Ctx<'_>, n: u32);

    /// The search ended `sat` with this plug-in's state current: keep a model.
    fn on_sat(&mut self, _ctx: &mut Ctx<'_>) {}

    /// The value of a term in the kept model, as a value term.
    fn model_value(&mut self, _ctx: &mut Ctx<'_>, _term: TermId) -> Option<TermId> {
        None
    }

    /// Preferred phase for an owned atom.
    fn phase(&self, _atom: TermId) -> Option<bool> {
        None
    }

    /// A counter that changes whenever any [`TheoryPlugin::phase`] answer may
    /// have changed; `None` when the plug-in keeps none. Lets the kernel skip
    /// re-seeding phases that are already current.
    fn phase_epoch(&self) -> Option<u64> {
        None
    }

    /// An unassigned atom this plug-in would like decided next, with its
    /// phase: theory-aware branching (design §3.8), consulted only when the
    /// engine option is on.
    fn decision_hint(&self) -> Option<(TermId, bool)> {
        None
    }

    // Reserved slots (freeze v2, design §3.3 and §3.6): defaulted, and not
    // called by the kernel yet (see `reserved.rs`).

    /// The next decision this plug-in wants, as a literal (a case-split
    /// queue that follows theory activity, KC25).
    fn next_decision(&mut self, _ctx: &mut Ctx<'_>) -> Option<TheoryLit> {
        None
    }

    /// A conjunctive core of the literals asserted to this plug-in.
    fn conjunctive_core(&self, _ctx: &Ctx<'_>) -> Option<ConjCore> {
        None
    }

    /// Up to `k` terms worth splitting on (cube-and-conquer, partitioning).
    fn split_candidates(&self, _ctx: &Ctx<'_>, _k: usize) -> Vec<TermId> {
        Vec::new()
    }

    /// Drop state for every atom not in `live` (KC27's collection of minted
    /// symbols on pop).
    fn gc(&mut self, _ctx: &mut Ctx<'_>, _live: &AtomSet) {}

    /// Whether `lemma` may leave this worker.
    fn share_policy(&self, _lemma: &Lemma) -> Share {
        Share::Default
    }

    /// Expensive work to run off the search thread (KC14).
    fn async_job(&mut self, _ctx: &mut Ctx<'_>) -> Option<Box<dyn AsyncJob>> {
        None
    }
}

#[cfg(test)]
mod tick_tests;
