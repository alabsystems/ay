// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The n-guard `la_disequality` backbone for GUARDED EQUALITY leaves that AY
//! certifies internally but cannot spell on the pinned Alethe wire.
//!
//! # The gap this closes
//!
//! A theory solver that derives `x = 1 AND y = 0 AND z = 1 IMPLIES x + y = z`
//! records it as one blocking clause whose head is a POSITIVE equality:
//!
//! ```text
//! (cl (= (+ x y) z) (not (>= x 1.0)) (not (<= x 1.0)) (not (>= y 0.0))
//!     (not (<= y 0.0)) (not (>= z 1.0)) (not (<= z 1.0)))
//! ```
//!
//! The refutation of its negation needs a DISEQUALITY (`(+ x y) != z`), which
//! no single Farkas row can express, so `la_generic` structurally cannot carry
//! the clause. AY's own strict checker nevertheless ACCEPTS the lemma: it is
//! recorded as `TheoryLemmaKind::ArithClauseTautology` and re-derived by
//! `nia_linear_ideal`, whose order lane (`nia_fourier_motzkin`) case-splits the
//! disequality into `p < 0` and `p > 0` and refutes BOTH branches. That kind
//! has no rule name in the pinned calculus, so `alethe_wire_rule()` is `hole`:
//! the refutation is computed, checked, and then thrown away at print time.
//! MEASURED on the #6660 fixture — the leaf is `ArithClauseTautology`, the
//! whole 46-step document passes `check_proof_strict`, and step `t26` still
//! printed `:rule hole`.
//!
//! The pinned calculus already contains the rule for exactly this: the
//! three-literal `la_disequality` tautology
//! `(or (= s t) (not (<= s t)) (not (<= t s)))`. What was missing is the
//! BACKBONE that turns it into a derivation of an n-GUARD clause. The existing
//! backbone (`proof_trust_surgery::plan_trichotomy`) is pinned to the
//! Int-trichotomy shape: a UNIT clause holding a packed three-disjunct `or`,
//! whose two non-equality disjuncts are closed by `[1, 1]` two-literal
//! strengthening bridges. This module is the same skeleton with the guard
//! count freed:
//!
//! ```text
//! la_disequality (cl (or EQ (not (<= s t)) (not (<= t s))))
//! or             (cl EQ (not (<= s t)) (not (<= t s)))
//! la_generic     (cl (<= s t) G1 .. Gn)
//! resolution     (cl EQ (not (<= t s)) G1 .. Gn)
//! la_generic     (cl (<= t s) G1 .. Gn)
//! resolution     (cl EQ G1 .. Gn)              <- the original clause
//! ```
//!
//! The two `la_generic` legs ARE the two branches of the disequality split,
//! read off as ordinary Farkas conflicts: branch `p > 0` refuted means
//! `s <= t` follows from the guards, and branch `p < 0` refuted means
//! `t <= s` does.
//!
//! # Print fidelity is a HARD limit on this lane
//!
//! `la_disequality` is validated POSITIONALLY, and the two checkers read
//! different artifacts: AY's strict validator reads the term DAG, while the
//! exporter renders through the surface-override map. MEASURED on the #6660
//! fixture, those diverge — the DAG holds `(= z (+ x y))` and an override
//! prints it as the file's `(= (+ x y) z)` — so the DAG-ordered split prints
//! `(or (= A B) (not (<= B A)) (not (<= A B)))`, which AY accepts and the
//! pinned external checker REJECTS. No `or` term satisfies both orders at
//! once, and the override cannot be dropped without breaking the `assume`'s
//! match against the problem file, so a flipped head equality is NOT
//! expressible here and the lane fails closed on it: a holey document is
//! strictly better than a rejected one. That family belongs to the
//! whole-proof authored lane
//! ([`Executor::replace_with_exact_authored_guarded_linear_refutation`]),
//! which rebuilds from the SURFACE roots and so has no divergence to bridge.
//!
//! # Authority
//!
//! This module GRANTS NO AUTHORITY. Every leg's certificate is produced and
//! then re-verified by `proof_farkas::try_lra_farkas_reconstruction`, which
//! rebinds by literal identity and re-runs
//! `verify_farkas_conflict_lits_linear` against the exact clause that will be
//! printed; a leg without a re-verified certificate is not planned. The
//! spliced proof is then re-checked WHOLE by the untouched strict checker in
//! [`Executor::commit_bridge_fragments`], which reverts the entire rewrite
//! when the result does not check or would lose a certification the original
//! had. Fail-closed at every step: an unrecognized clause, a missing
//! certificate, or a constant-folding surprise in the synthesized `<=` atoms
//! leaves the leaf exactly as it is — an honest `hole`.

use super::*;

/// Guards admitted on one clause. The two legs re-run the LRA solver over
/// `guards + 1` literals each, so this bounds that work; a wider clause keeps
/// its hole.
const MAX_LA_DISEQUALITY_SPLIT_GUARDS: usize = 32;

/// Leaves rewritten in one pass. Each costs two LRA solves.
const MAX_LA_DISEQUALITY_SPLIT_LEAVES: usize = 64;

impl Executor {
    /// Replace every guarded-equality leaf whose KIND has no wire spelling
    /// with the n-guard `la_disequality` derivation of the SAME clause.
    /// Returns how many leaves were rewritten (0 leaves the proof
    /// byte-identical).
    ///
    /// The selector is exactly "this kind renders as the unproved rule": the
    /// internal certificate is real (the strict checker re-derives it) and the
    /// only thing missing is a spelling an external checker can re-run. A kind
    /// that already has one is never touched.
    pub(in crate::executor) fn derive_la_disequality_split_lemmas(
        &mut self,
        proof: &mut Proof,
    ) -> usize {
        let leaves: Vec<(usize, Vec<TermId>)> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| match step {
                ProofStep::TheoryLemma { clause, kind, .. }
                    if kind.alethe_wire_rule() == ay_core::UNPROVED_STEP_RULE =>
                {
                    Some((index, clause.clone()))
                }
                _ => None,
            })
            .take(MAX_LA_DISEQUALITY_SPLIT_LEAVES.saturating_add(1))
            .collect();
        if leaves.is_empty() || leaves.len() > MAX_LA_DISEQUALITY_SPLIT_LEAVES {
            return 0;
        }

        let mut plans: Vec<Option<Vec<ProofStep>>> = std::iter::repeat_with(|| None)
            .take(proof.steps.len())
            .collect();
        let mut planned = 0usize;
        for (index, clause) in leaves {
            let Some(fragment) = self.plan_la_disequality_split_fragment(&clause) else {
                continue;
            };
            plans[index] = Some(fragment);
            planned = planned.saturating_add(1);
        }
        if planned == 0 {
            return 0;
        }
        self.commit_bridge_fragments(proof, plans)
    }

    /// The head shape this backbone reproduces: a POSITIVE binary equality
    /// over two same-sorted `Int`/`Real` operands, followed by at least one
    /// and at most [`MAX_LA_DISEQUALITY_SPLIT_GUARDS`] guards that
    /// `la_generic` can read linearly.
    fn la_split_recognize_head<'c>(
        &self,
        clause: &'c [TermId],
    ) -> Option<(TermId, TermId, TermId, &'c [TermId])> {
        let (&equality, guards) = clause.split_first()?;
        if guards.is_empty() || guards.len() > MAX_LA_DISEQUALITY_SPLIT_GUARDS {
            return None;
        }
        let (s, t) = decode_eq_local(&self.ctx.terms, equality)?;
        if self.ctx.terms.sort(s) != self.ctx.terms.sort(t)
            || !matches!(self.ctx.terms.sort(s), Sort::Int | Sort::Real)
        {
            return None;
        }
        // `la_generic` performs no Boolean or congruence reasoning, so a guard
        // it cannot read linearly must never enter a leg.
        if !guards
            .iter()
            .all(|&guard| Self::la_split_guard_is_linear(&self.ctx.terms, guard))
        {
            return None;
        }
        // The head equality must not also appear among the guards: the two
        // resolutions pivot on the split literals, and a clause that already
        // carries `EQ` twice is not the shape this backbone reproduces.
        if guards.iter().any(|&guard| {
            guard == equality
                || matches!(self.ctx.terms.get(guard), TermData::Not(inner) if *inner == equality)
        }) {
            return None;
        }
        Some((equality, s, t, guards))
    }

    /// The four synthesized split terms, or `None` when the interned or
    /// PRINTED shape is not the rule's.
    fn la_split_terms(
        &mut self,
        equality: TermId,
        s: TermId,
        t: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId, TermId)> {
        // `mk_app` raw-interns, so the DAG operand order is exactly the
        // `(<= s t)` / `(<= t s)` pair `la_disequality` requires. Re-read the
        // interned shape anyway: a constant fold would break the rigid form.
        let le_st = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [s, t], Sort::Bool);
        let le_ts = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [t, s], Sort::Bool);
        if !Self::la_split_atom_is_binary(&self.ctx.terms, le_st, "<=")
            || !Self::la_split_atom_is_binary(&self.ctx.terms, le_ts, "<=")
        {
            return None;
        }
        let not_le_st = self.ctx.terms.mk_not_raw(le_st);
        let not_le_ts = self.ctx.terms.mk_not_raw(le_ts);
        let or_term = self.ctx.terms.mk_app(
            Symbol::named("or"),
            [equality, not_le_st, not_le_ts],
            Sort::Bool,
        );
        // The published `or` must hold exactly those three disjuncts in
        // exactly that order — the checker validates positionally.
        let TermData::App(Symbol::Named(or_name), or_args) = self.ctx.terms.get(or_term) else {
            return None;
        };
        if or_name != "or" || or_args.as_slice() != [equality, not_le_st, not_le_ts] {
            return None;
        }
        // PRINT-SHAPE AUTHENTICATION. `la_disequality` is validated
        // positionally by BOTH checkers, but AY's own strict validator reads
        // the term DAG while the exporter renders through the surface-override
        // map. Those diverge in practice: on the #6660 fixture the DAG holds
        // `(= z (+ x y))` and an override prints it `(= (+ x y) z)`, so a
        // DAG-ordered split prints `(or (= A B) (not (<= B A)) (not (<= A B)))`
        // — accepted internally and REJECTED by the pinned external checker.
        // A holey document is strictly better than a rejected one.
        self.la_split_prints_the_rigid_shape(equality, s, t, le_st, le_ts, or_term)
            .then_some((le_st, le_ts, not_le_st, not_le_ts, or_term))
    }

    /// The derivation for one guarded-equality leaf, or `None`.
    fn plan_la_disequality_split_fragment(&mut self, clause: &[TermId]) -> Option<Vec<ProofStep>> {
        let (equality, s, t, guards) = self.la_split_recognize_head(clause)?;
        let guards = guards.to_vec();
        let (le_st, le_ts, not_le_st, not_le_ts, or_term) = self.la_split_terms(equality, s, t)?;

        let (forward_clause, forward_farkas) = self.la_split_leg(le_st, &guards)?;
        let (reverse_clause, reverse_farkas) = self.la_split_leg(le_ts, &guards)?;

        let mut forward_residual: Vec<TermId> = vec![equality, not_le_ts];
        forward_residual.extend_from_slice(&guards);

        Some(vec![
            ProofStep::Step {
                rule: AletheRule::LaDisequality,
                clause: vec![or_term],
                premises: Vec::new(),
                args: Vec::new(),
            },
            ProofStep::Step {
                rule: AletheRule::Or,
                clause: vec![equality, not_le_st, not_le_ts],
                premises: vec![ProofId(0)],
                args: Vec::new(),
            },
            ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: forward_clause,
                farkas: Some(forward_farkas),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            },
            ProofStep::Step {
                rule: AletheRule::Resolution,
                clause: forward_residual,
                premises: vec![ProofId(1), ProofId(2)],
                args: Vec::new(),
            },
            ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: reverse_clause,
                farkas: Some(reverse_farkas),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            },
            ProofStep::Step {
                rule: AletheRule::Resolution,
                clause: clause.to_vec(),
                premises: vec![ProofId(3), ProofId(4)],
                args: Vec::new(),
            },
        ])
    }

    /// One branch of the split as a re-verified `la_generic` lemma:
    /// `(cl bound G1 .. Gn)`, whose negation is the guards plus the strict
    /// complement of `bound` — exactly one disequality-split branch.
    fn la_split_leg(
        &mut self,
        bound: TermId,
        guards: &[TermId],
    ) -> Option<(Vec<TermId>, FarkasAnnotation)> {
        let mut leg: Vec<TermId> = Vec::with_capacity(guards.len().saturating_add(1));
        leg.push(bound);
        leg.extend_from_slice(guards);
        let mut farkas = None;
        let mut inferred = TheoryLemmaKind::Generic;
        if !super::super::proof_farkas::try_lra_farkas_reconstruction(
            &self.ctx.terms,
            &leg,
            &mut farkas,
            &mut inferred,
        ) {
            return None;
        }
        Some((leg, farkas?))
    }

    /// Whether the exporter renders the whole split exactly as the rule's
    /// rigid shape over the DAG operand order.
    ///
    /// Every piece is rendered through the SAME override-aware printer the
    /// exporter uses, then the composite is rebuilt from those renderings and
    /// compared literally. An override that reorders, resugars, or renames any
    /// operand is therefore admitted only when the composite still reads as
    /// `(or (= s t) (not (<= s t)) (not (<= t s)))`.
    fn la_split_prints_the_rigid_shape(
        &self,
        equality: TermId,
        s: TermId,
        t: TermId,
        le_st: TermId,
        le_ts: TermId,
        or_term: TermId,
    ) -> bool {
        let overrides = self.proof_export_term_overrides();
        let render = |term: TermId| match overrides.as_ref() {
            Some(map) => ay_proof::format_term_alethe_with_overrides(&self.ctx.terms, term, map),
            None => ay_proof::format_term_alethe(&self.ctx.terms, term),
        };
        let left = render(s);
        let right = render(t);
        let want_equality = format!("(= {left} {right})");
        let want_forward = format!("(<= {left} {right})");
        let want_reverse = format!("(<= {right} {left})");
        let want_or = format!("(or {want_equality} (not {want_forward}) (not {want_reverse}))");
        render(equality) == want_equality
            && render(le_st) == want_forward
            && render(le_ts) == want_reverse
            && render(or_term) == want_or
    }

    fn la_split_atom_is_binary(terms: &TermStore, atom: TermId, operator: &str) -> bool {
        matches!(
            terms.get(atom),
            TermData::App(Symbol::Named(name), args) if name == operator && args.len() == 2
        )
    }

    /// A guard `la_generic` can read: a (possibly negated) binary `<`, `<=`,
    /// `>`, `>=` or `=` over two same-sorted Int/Real operands.
    fn la_split_guard_is_linear(terms: &TermStore, guard: TermId) -> bool {
        let atom = match terms.get(guard) {
            TermData::Not(inner) => *inner,
            _ => guard,
        };
        let TermData::App(Symbol::Named(operator), args) = terms.get(atom) else {
            return false;
        };
        args.len() == 2
            && matches!(operator.as_str(), "=" | "<" | "<=" | ">" | ">=")
            && args
                .iter()
                .all(|&arg| matches!(terms.sort(arg), Sort::Int | Sort::Real))
            && terms.sort(args[0]) == terms.sort(args[1])
    }
}

#[cfg(test)]
#[path = "la_disequality_split_tests.rs"]
mod tests;
