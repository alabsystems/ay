// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRA registered through the plug-in interface: the kernel's first real
//! theory (design §14; roadmap K).
//!
//! An adapter over the existing `LraSolver`. `LraSolver` keeps a raw
//! `*const TermStore`; under K3 that pointer is only valid inside one
//! callback, so every call is bracketed by `set_terms` / `unset_terms`.
//! Everything the lanes send out of the search as a request becomes a lemma
//! inside it (design §3.5): disequality and expression splits, model
//! equalities, the ITE link lemmas, and, in integer mode, branch and bound.
//!
//! `propagate` is the cheap BCP-time simplex (`check_during_propagate`, K6),
//! and it runs only when a bound changed since the last call. The full check
//! with disequalities and model equalities is `final_check`.

mod int;
mod shared;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{
    AtomHandle, DisequalitySplitRequest, Effort, TermId, TermStore, TheoryLemmaKind, TheoryLit,
    TheoryResult, TheorySolver,
};
use ay_lra::{LraModel, LraSolver};

use crate::arith_defs::{define_operators, gcd_refutes_equality};
use crate::linear::Linearizer;
use crate::lra_certify::certify_clause;
use crate::lra_lemmas::{
    bound_axiom, farkas_conflict, hints_exhausted, model_equality, term_split, value_split,
};
use crate::plugin::{
    Conflict, Ctx, Explanation, Final, GiveUp, Justification, Lemma, LemmaTier, ProofHint, ThVar,
    TheoryPlugin,
};
use crate::shared::SharedTerms;

/// The LRA plug-in, over reals or (integer mode) over integers.
pub struct LraPlugin {
    lra: LraSolver,
    integer: bool,
    /// The atom of each handle (KC3): the handle is the index.
    atom_terms: Vec<TermId>,
    /// `div`/`mod`/`abs` terms whose definitions are in the search
    /// (`arith_defs`).
    defined: HashSet<TermId>,
    lin: Linearizer,
    /// Final checks that found a fractional integer vertex.
    fractional_rounds: u64,
    /// Gomory cut lemmas added so far.
    cuts_added: usize,
    /// Xorshift state for the unboxed branch choice.
    branch_rng: u64,
    /// A bound was asserted or retracted since the last BCP-time check.
    dirty: bool,
    /// The atom index is sorted and the bound axioms are added (once, after
    /// the check's atoms are internalized).
    indexed: bool,
    model: Option<LraModel>,
    /// Terms the hub shares with this plug-in (design H1).
    shared: SharedTerms,
}

impl LraPlugin {
    /// A plug-in over a fresh `LraSolver` for real arithmetic.
    pub fn new(terms: &TermStore) -> Self {
        Self::build(terms, false)
    }

    /// A plug-in for integer arithmetic: the same simplex in integer mode
    /// (strict bounds tightened by one), with branch and bound as in-search
    /// lemmas `x ≤ ⌊v⌋ ∨ x ≥ ⌈v⌉` at the final check (design §3.5).
    pub fn new_integer(terms: &TermStore) -> Self {
        Self::build(terms, true)
    }

    /// Skip implied-bound derivation during BCP-time checks (direct bound
    /// propagation and the final-check cascade stay on). On integer checks
    /// the BCP-time pass is where the kernel's time goes (`sample`: 96% in
    /// `compute_implied_bounds`' BigRational arithmetic on a div/mod fuzz
    /// file); design K6 wants the BCP-time work cheap.
    pub fn set_bcp_implied_bounds(&mut self, on: bool) {
        self.lra.set_no_bcp_implied_bounds(!on);
    }

    fn build(terms: &TermStore, integer: bool) -> Self {
        let mut lra = LraSolver::new(terms);
        lra.set_integer_mode(integer);
        lra.set_defined_operators(true);
        lra.unset_terms();
        Self {
            lra,
            integer,
            atom_terms: Vec::new(),
            defined: HashSet::default(),
            lin: Linearizer::default(),
            fractional_rounds: 0,
            cuts_added: 0,
            branch_rng: 0x9E37_79B9_7F4A_7C15,
            dirty: true,
            indexed: false,
            model: None,
            shared: SharedTerms::default(),
        }
    }

    /// Run `f` with the term pointer valid for exactly this call (K3).
    fn bracket<R>(&mut self, terms: &TermStore, f: impl FnOnce(&mut LraSolver) -> R) -> R {
        self.lra.set_terms(terms);
        let result = f(&mut self.lra);
        self.lra.unset_terms();
        result
    }

    /// Once the check's atoms are internalized, do what the lanes do when
    /// they build their extension: sort LRA's atom index, which also links
    /// the negation partners its bound propagation reads, and add the bound
    /// axioms, the binary clauses ordering the bound atoms of one term (z3
    /// `mk_bound_axioms`; the lanes' `pipeline_inject_bound_axioms`). Every
    /// axiom is checked T-valid in a fresh simplex before it is added (K4):
    /// the generator once produced a non-tautology (#6242, seed 981).
    /// Atoms minted later join the index unsorted, as they do in the lanes.
    /// Returns the number of axioms added.
    fn index_atoms(&mut self, ctx: &mut Ctx<'_>) -> usize {
        if self.indexed {
            return 0;
        }
        self.indexed = true;
        let pairs = self.bracket(ctx.terms(), |lra| {
            lra.sort_atom_index();
            lra.generate_bound_axiom_terms()
        });
        let mut added = 0;
        for (t1, p1, t2, p2) in pairs {
            let clause = [TheoryLit::new(t1, p1), TheoryLit::new(t2, p2)];
            if let Some(lemma) = bound_axiom(ctx.terms(), clause) {
                ctx.lemma(lemma);
                added += 1;
            }
        }
        added
    }

    /// Conflicts go to the kernel; everything else is reported back.
    fn take_conflict(&self, ctx: &mut Ctx<'_>, result: TheoryResult) -> Option<TheoryResult> {
        let conflict = match result {
            TheoryResult::Unsat(lits) => Conflict {
                lits,
                hint: ProofHint::kind(TheoryLemmaKind::Generic),
            },
            TheoryResult::UnsatWithFarkas(conflict) => farkas_conflict(conflict),
            other => return Some(other),
        };
        let conflict = self.certify_conflict(ctx, conflict);
        ctx.conflict(conflict);
        None
    }

    /// A conflict without Farkas coefficients gets a checkable hint from the
    /// private simplex when proofs are on (design P1; see `lra_certify`).
    fn certify_conflict(&self, ctx: &mut Ctx<'_>, mut conflict: Conflict) -> Conflict {
        if !ctx.proofs_on() || self.integer || conflict.hint.farkas.is_some() {
            return conflict;
        }
        let clause: Vec<TheoryLit> = conflict
            .lits
            .iter()
            .map(|l| TheoryLit::new(l.term, !l.value))
            .collect();
        if let Some(hint) = certify_clause(ctx.terms_mut(), &clause) {
            conflict.hint = hint;
        }
        conflict
    }

    /// The hint for a propagation's reason clause `[lit, ¬r1, ..]` when proofs
    /// are on, computed by the private simplex (bound propagations carry no
    /// certificate of their own).
    fn reason_hint(&self, ctx: &mut Ctx<'_>, lit: TheoryLit, reason: &[TheoryLit]) -> ProofHint {
        if !ctx.proofs_on() || self.integer {
            return ProofHint::kind(TheoryLemmaKind::Generic);
        }
        let mut clause = Vec::with_capacity(reason.len() + 1);
        clause.push(lit);
        clause.extend(reason.iter().map(|r| TheoryLit::new(r.term, !r.value)));
        certify_clause(ctx.terms_mut(), &clause)
            .unwrap_or_else(|| ProofHint::kind(TheoryLemmaKind::Generic))
    }

    /// The full check, re-asked for the split when every guessed equality
    /// already has an assigned atom (the guess would carry no information;
    /// the rule the CHC `HornSmt` bridge measured).
    fn full_check(&mut self, ctx: &Ctx<'_>) -> TheoryResult {
        let result = self.bracket(ctx.terms(), TheorySolver::check);
        if !hints_exhausted(ctx, &result) {
            return result;
        }
        self.bracket(ctx.terms(), |lra| {
            lra.set_assume_eqs_over_split(false);
            let split = lra.check();
            lra.set_assume_eqs_over_split(true);
            split
        })
    }

    fn splits(
        &mut self,
        ctx: &mut Ctx<'_>,
        first: DisequalitySplitRequest,
    ) -> Result<Final, GiveUp> {
        let extra = self.lra.drain_pending_diseq_splits();
        for request in std::iter::once(first).chain(extra) {
            let lemma = value_split(ctx.terms_mut(), &request)?;
            ctx.lemma(lemma);
        }
        Ok(Final::Continue)
    }
}

impl TheoryPlugin for LraPlugin {
    fn name(&self) -> &'static str {
        if self.integer {
            "lia-on-lra"
        } else {
            "lra"
        }
    }

    fn internalize_atom(&mut self, ctx: &mut Ctx<'_>, atom: TermId) -> Result<AtomHandle, GiveUp> {
        let handle = u32::try_from(self.atom_terms.len())
            .map(AtomHandle)
            .map_err(|_| GiveUp::new("lra: atom handle space exhausted"))?;
        self.atom_terms.push(atom);
        self.bracket(ctx.terms(), |lra| lra.register_atom(atom));
        define_operators(ctx, atom, &mut self.defined);
        if self.integer {
            if let Some(lemma) = gcd_refutes_equality(ctx.terms(), &mut self.lin, atom) {
                ctx.lemma(lemma);
            }
        }
        Ok(handle)
    }

    /// A hub node of this plug-in's sort: a shared term (design H1).
    fn attach_term(&mut self, ctx: &mut Ctx<'_>, term: TermId) -> Result<Option<ThVar>, GiveUp> {
        self.attach_shared(ctx, term).map(Some)
    }

    /// The hub merged two shared terms: the tableau learns `a = b` through
    /// the atom, with the hub's reason as the premise (`shared.rs`).
    ///
    /// Not `LraSolver::assert_shared_equality` (z3's `new_eq_eh`, bounds
    /// whose premises are the reason): measured, it made the integer simplex
    /// answer `unsat` on a satisfiable QF_UFLIA file (Certora `65782_cd31…`,
    /// z3 `sat`), presumably a derivation that drops the bounds' premises;
    /// open in ay-lra.
    fn new_eq(
        &mut self,
        ctx: &mut Ctx<'_>,
        a: ThVar,
        b: ThVar,
        why: &[TheoryLit],
    ) -> Result<(), GiveUp> {
        self.shared.new_eq(ctx, a, b, why)
    }

    /// The hub made two shared terms distinct.
    fn new_diseq(
        &mut self,
        ctx: &mut Ctx<'_>,
        a: ThVar,
        b: ThVar,
        why: &[TheoryLit],
    ) -> Result<(), GiveUp> {
        self.shared.new_diseq(ctx, a, b, why)
    }

    fn assign(&mut self, ctx: &mut Ctx<'_>, atom: AtomHandle, value: bool) -> Result<(), GiveUp> {
        let atom = *self
            .atom_terms
            .get(atom.index())
            .ok_or_else(|| GiveUp::new("lra: an unknown atom handle was assigned"))?;
        self.dirty = true;
        self.bracket(ctx.terms(), |lra| lra.assert_literal(atom, value));
        Ok(())
    }

    /// As the lanes' eager extension gates its BCP-time check: a new bound,
    /// or propagations LRA still holds. Scope changes alone change nothing
    /// the check could find.
    fn can_propagate(&self) -> bool {
        !self.indexed || self.dirty || self.lra.has_pending_propagations()
    }

    fn propagate(&mut self, ctx: &mut Ctx<'_>) -> Result<(), GiveUp> {
        let _ = self.index_atoms(ctx);
        if !self.can_propagate() {
            return Ok(());
        }
        self.dirty = false;
        let (result, props) = self.bracket(ctx.terms(), |lra| {
            let result = lra.check_during_propagate();
            let props = if matches!(result, TheoryResult::Sat) {
                // Implied-bound refinements ask for new bound atoms; the kernel
                // does not mint them yet. Dropping one only weakens
                // propagation, and taking them keeps the queue bounded.
                let _ = lra.take_bound_refinements();
                lra.propagate()
            } else {
                Vec::new()
            };
            (result, props)
        });
        // Anything but a conflict is left to the final check: an `Unknown`
        // here is a label, not a verdict, and requests are final-check work.
        let _ = self.take_conflict(ctx, result);
        for prop in props {
            let why = match prop.reason_data {
                Some(token) => Justification::Lazy(token),
                None => {
                    let hint = self.reason_hint(ctx, prop.literal, &prop.reason);
                    Justification::Eager(Explanation {
                        reason: prop.reason,
                        hint,
                    })
                }
            };
            ctx.propagate(prop.literal, why);
        }
        Ok(())
    }

    /// Everything is [`Effort::Standard`] work: the simplex's full check,
    /// splits, cuts and branches.
    fn final_check(&mut self, ctx: &mut Ctx<'_>, effort: Effort) -> Result<Final, GiveUp> {
        if effort != Effort::Standard {
            return Ok(Final::Sat);
        }
        if self.index_atoms(ctx) > 0 {
            return Ok(Final::Continue);
        }
        let result = self.full_check(ctx);
        let Some(result) = self.take_conflict(ctx, result) else {
            return Ok(Final::Continue);
        };
        match result {
            TheoryResult::Sat if self.integer => {
                if let Some(reasons) = self.bracket(ctx.terms(), |lra| lra.gcd_test_term_conflict())
                {
                    ctx.conflict(Conflict {
                        lits: reasons
                            .into_iter()
                            .map(|(term, value)| TheoryLit::new(term, value))
                            .collect(),
                        hint: ProofHint::kind(TheoryLemmaKind::LiaGeneric),
                    });
                    return Ok(Final::Continue);
                }
                if let Some(cuts) = self.cuts(ctx) {
                    for cut in cuts {
                        ctx.lemma(cut);
                    }
                    return Ok(Final::Continue);
                }
                match self.branch(ctx) {
                    Some(lemma) => {
                        ctx.lemma(lemma);
                        Ok(Final::Continue)
                    }
                    None => Ok(Final::Sat),
                }
            }
            TheoryResult::Sat => Ok(Final::Sat),
            TheoryResult::NeedDisequalitySplit(first) => self.splits(ctx, first),
            TheoryResult::NeedExpressionSplit(request) => {
                let lemma = term_split(ctx.terms_mut(), request.disequality_term)?;
                ctx.lemma(lemma);
                Ok(Final::Continue)
            }
            TheoryResult::NeedExpressionSplits(requests) => {
                for request in requests {
                    let lemma = term_split(ctx.terms_mut(), request.disequality_term)?;
                    ctx.lemma(lemma);
                }
                Ok(Final::Continue)
            }
            TheoryResult::NeedModelEquality(request) => {
                model_equality(ctx, &request)?;
                Ok(Final::Continue)
            }
            TheoryResult::NeedModelEqualities(requests) => {
                for request in &requests {
                    model_equality(ctx, request)?;
                }
                Ok(Final::Continue)
            }
            TheoryResult::NeedLemmas(lemmas) => {
                for lemma in lemmas {
                    ctx.lemma(Lemma {
                        clause: lemma.clause,
                        tier: LemmaTier::Redundant,
                        hint: ProofHint::kind(TheoryLemmaKind::Generic),
                    });
                }
                Ok(Final::Continue)
            }
            TheoryResult::Unknown => Err(GiveUp::new(format!("{}: unknown", self.name()))),
            other => Err(GiveUp::new(format!(
                "{}: {} is not ported to the kernel",
                self.name(),
                request_name(&other)
            ))),
        }
    }

    fn explain(&mut self, ctx: &mut Ctx<'_>, lit: TheoryLit, token: u64) -> Option<Explanation> {
        let reason = self.bracket(ctx.terms(), |lra| lra.explain_propagation(lit.term, token))?;
        let hint = self.reason_hint(ctx, lit, &reason);
        Some(Explanation { reason, hint })
    }

    fn push_scope(&mut self, ctx: &mut Ctx<'_>) {
        self.bracket(ctx.terms(), TheorySolver::push);
    }

    fn pop_scope(&mut self, ctx: &mut Ctx<'_>, n: u32) {
        self.bracket(ctx.terms(), |lra| {
            for _ in 0..n {
                lra.pop();
            }
        });
    }

    fn on_sat(&mut self, ctx: &mut Ctx<'_>) {
        self.model = Some(self.bracket(ctx.terms(), |lra| lra.extract_model()));
    }

    fn model_value(&mut self, ctx: &mut Ctx<'_>, term: TermId) -> Option<TermId> {
        let value = self.value_of(ctx.terms(), term)?;
        let terms = ctx.terms_mut();
        if self.integer && value.is_integer() {
            return Some(terms.mk_int(value.to_integer()));
        }
        Some(terms.mk_rational(value))
    }

    fn phase(&self, atom: TermId) -> Option<bool> {
        self.lra.suggest_phase(atom)
    }

    fn phase_epoch(&self) -> Option<u64> {
        self.lra.phase_hint_epoch()
    }

    fn decision_hint(&self) -> Option<(TermId, bool)> {
        self.lra.suggest_decision_atom()
    }
}

const fn request_name(result: &TheoryResult) -> &'static str {
    match result {
        TheoryResult::NeedSplit(_) => "NeedSplit",
        TheoryResult::NeedStringLemma(_) => "NeedStringLemma",
        _ => "a theory request",
    }
}
