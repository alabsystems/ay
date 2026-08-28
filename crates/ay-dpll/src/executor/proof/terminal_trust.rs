// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Terminal proof-trust and premise-provenance gates.

mod constant_premise;

use ay_core::{Constant, Proof, ProofStep, Sort, TermData, TermId, TermStore};

use super::super::Executor;

/// Insert `root` and every nested `and`-conjunct beneath it into `set`.
///
/// Top-level `and`-flattening asserts each conjunct of an `(and ...)` problem
/// assertion as a separate `assume`, so the provenance set (leak-2) must
/// accept the conjuncts as well as the asserted conjunction itself. Iterative
/// to avoid deep recursion on wide/nested conjunctions; the `set.insert`
/// visited-guard makes it O(subterms) and cycle-safe.
fn add_term_with_and_conjuncts(
    terms: &TermStore,
    root: TermId,
    set: &mut ay_core::kani_compat::DetHashSet<TermId>,
) {
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !set.insert(term) {
            continue;
        }
        if let TermData::App(sym, args) = terms.get(term) {
            if sym.name() == "and" {
                for &arg in args {
                    stack.push(arg);
                }
            }
        }
    }
}

impl Executor {
    /// Whether one internally checked bit-blast theorem is also in the exact
    /// ground-constant subset the Alethe printer expands into
    /// `evaluate`/`equiv_pos2`/`false`/`resolution`.
    ///
    /// Keep this deliberately narrower than the printer: a surface override
    /// can change the bytes the external checker sees, so any override on the
    /// accepted shape remains a known gap. Certified authored replacements
    /// purge those overrides before publication. All other `BvBitBlast`
    /// clauses retain the honest `hole` classification.
    fn bv_constant_disequality_is_fixed_wire_evaluate(&self, clause: &[TermId]) -> bool {
        let [literal] = clause else {
            return false;
        };
        let TermData::Not(equality) = self.ctx.terms.get(*literal) else {
            return false;
        };
        let TermData::App(symbol, operands) = self.ctx.terms.get(*equality) else {
            return false;
        };
        if symbol.name() != "=" || operands.len() != 2 {
            return false;
        }
        let (left, right) = (operands[0], operands[1]);
        let (
            TermData::Const(Constant::BitVec {
                value: left_value,
                width: left_width,
            }),
            TermData::Const(Constant::BitVec {
                value: right_value,
                width: right_width,
            }),
        ) = (self.ctx.terms.get(left), self.ctx.terms.get(right))
        else {
            return false;
        };
        if left_width == &0
            || left_width != right_width
            || left_value == right_value
            || left_value.bits() > u64::from(*left_width)
            || right_value.bits() > u64::from(*right_width)
            || self.ctx.terms.sort(left) != &Sort::bitvec(*left_width)
            || self.ctx.terms.sort(right) != &Sort::bitvec(*right_width)
            || self.ctx.terms.sort(*equality) != &Sort::Bool
            || self.ctx.terms.sort(*literal) != &Sort::Bool
        {
            return false;
        }
        !self
            .last_proof_term_overrides
            .as_ref()
            .is_some_and(|overrides| {
                [*literal, *equality, left, right]
                    .iter()
                    .any(|term| overrides.contains_key(term))
            })
    }

    /// Whether a native Boolean-constant clausification step prints as one of
    /// Alethe's two fixed, premise-free axioms.
    ///
    /// The internal source term in `args` is positional reconstruction
    /// metadata; the printer deliberately omits it.  Any different shape or
    /// surface override stays a known wire gap rather than being inferred safe.
    fn bool_constant_step_is_fixed_wire_axiom(
        &self,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        premises: &[ay_core::ProofId],
        args: &[TermId],
    ) -> bool {
        if !premises.is_empty() || clause.len() != 1 {
            return false;
        }

        let literal = clause[0];
        let source = match rule {
            ay_core::AletheRule::True
                if matches!(
                    self.ctx.terms.get(literal),
                    TermData::Const(Constant::Bool(true))
                ) =>
            {
                literal
            }
            ay_core::AletheRule::False => {
                let TermData::Not(source) = self.ctx.terms.get(literal) else {
                    return false;
                };
                if !matches!(
                    self.ctx.terms.get(*source),
                    TermData::Const(Constant::Bool(false))
                ) {
                    return false;
                }
                *source
            }
            _ => return false,
        };

        if !args.is_empty() && args != [source] {
            return false;
        }
        !self
            .last_proof_term_overrides
            .as_ref()
            .is_some_and(|overrides| {
                overrides.contains_key(&literal) || overrides.contains_key(&source)
            })
    }

    /// Internal proof retained for terminal publication policy.
    ///
    /// Unlike [`Self::last_proof`], this deliberately does not require a
    /// user-facing artifact request: mandatory proof tracking also serves
    /// `:check-proofs-strict` when that option is enabled by itself. Explicit
    /// reconstruction suppression still hides the proof, and ordinary query
    /// invalidation clears the underlying slot before a later policy check.
    fn retained_unsat_proof_for_policy(&self) -> Option<&Proof> {
        if self.last_unsat_proof_reconstruction_suppressed {
            None
        } else {
            self.last_proof.as_ref()
        }
    }

    /// Build the set of `assume` terms an external checker may legitimately
    /// accept as free hypotheses for the last UNSAT proof (leak-2 provenance
    /// gate).
    ///
    /// A terminal-path `assume` is trustworthy ONLY when its term is one of:
    ///   (A) an original asserted formula — the parsed-prefix problem premises
    ///       and any provenance-tracked problem assertions (never the full
    ///       solver-time assertion stack, which may hold theory-injected
    ///       axioms) — plus their nested `and`-conjuncts (top-level
    ///       and-flattening asserts each conjunct as a separate `assume`) plus
    ///       any `check-sat-assuming` assumption literals; or
    ///   (B) a quantifier instantiation whose `QuantExpansionRecord.original`
    ///       traces back to an asserted `forall` in (A): the `forall` itself,
    ///       the merged ground `expanded` conjunction that replaced it, and
    ///       each per-instance folded term.
    ///
    /// Any reachable terminal `assume` OUTSIDE this set is a laundered axiom —
    /// the theory asserted a fact it never proved (e.g. an injected `seq.len`
    /// identity) and rode it to a "certified" empty clause. The strict-proofs
    /// and `--self-check` gates treat such an `assume` exactly like a `trust`
    /// fallback and downgrade the verdict to `unknown`.
    pub(in crate::executor) fn proof_legit_assume_set(
        &self,
    ) -> ay_core::kani_compat::DetHashSet<TermId> {
        let mut set: ay_core::kani_compat::DetHashSet<TermId> =
            ay_core::kani_compat::DetHashSet::default();

        // (A) Original problem premises + their nested and-conjuncts.
        for assertion in self.proof_original_problem_assertions() {
            add_term_with_and_conjuncts(&self.ctx.terms, assertion, &mut set);
        }
        for assertion in self.proof_problem_assertions() {
            add_term_with_and_conjuncts(&self.ctx.terms, assertion, &mut set);
        }
        // check-sat-assuming assumption literals are problem-supplied premises.
        if let Some(assumptions) = &self.last_assumptions {
            for &assumption in assumptions {
                add_term_with_and_conjuncts(&self.ctx.terms, assumption, &mut set);
            }
        }
        // Re-elaborated original terms captured by the proof rebuild. The
        // trust surgery inserts `assume` steps carrying these (alpha-renamed
        // `forall` premises have a canonical id distinct from `ctx.assertions`
        // — see `last_proof_rebuild_originals`), so they must count as (A).
        for &original in &self.last_proof_rebuild_originals {
            add_term_with_and_conjuncts(&self.ctx.terms, original, &mut set);
        }

        // (B) Quantifier instantiations rooted at an asserted `forall`.
        //
        // `expand_finite_domains` REPLACES a top-level asserted `forall` at
        // `ctx.assertions[idx]` with its ground expansion in place, so the
        // `forall` itself is no longer in (A) (that slot now holds `expanded`).
        // Each `QuantExpansionRecord` is created ONLY for such a replacement of
        // a top-level `forall` premise (see `expand_finite_domains`), so
        // `rec.original` IS a genuinely-asserted premise — accept it, plus the
        // ground `expanded` conjunction that replaced it and each per-instance
        // folded term (the terms a `forall_inst` derivation legitimately
        // introduces). The `TermData::Forall` guard re-checks the construction
        // invariant (an injected non-forall axiom never gets a record and so
        // never launders through here).
        for rec in &self.quant_expansion_records {
            if !matches!(self.ctx.terms.get(rec.original), TermData::Forall(..)) {
                continue;
            }
            add_term_with_and_conjuncts(&self.ctx.terms, rec.original, &mut set);
            // (#bv-forall-const-expansion) A record whose expansion collapsed to
            // a CONSTANT contributes no premise: whitelisting `true`/`false` here
            // would widen the foreign-assume detector's accept set for a term
            // that is not a problem premise at all. Records for such expansions
            // exist only to authenticate the replacement for the BV full-domain
            // SAT recognizer (see `expand_finite_domains`), so this keeps the
            // proof-provenance surface byte-identical to before that change.
            if !matches!(self.ctx.terms.get(rec.expanded), TermData::Const(_)) {
                add_term_with_and_conjuncts(&self.ctx.terms, rec.expanded, &mut set);
            }
            for (_binder_values, folded) in &rec.instances {
                add_term_with_and_conjuncts(&self.ctx.terms, *folded, &mut set);
            }
        }

        // #rewritten-constant-premise: authenticate constants only after every
        // provenance source has contributed to the finished set. See the
        // `constant_premise` module for rationale and incident evidence.
        let (authored_true, authored_false) = self.boolean_constant_premises_authored();
        if !authored_true {
            set.remove(&self.ctx.terms.true_term());
        }
        if !authored_false {
            set.remove(&self.ctx.terms.false_term());
        }

        set
    }

    /// Whether the last UNSAT proof has a reachable terminal `assume` NOT
    /// backed by the problem's provenance (leak-2). Consulted by both the
    /// `--strict-proofs` CLI gate and the `--self-check` self-certification
    /// gate; a `true` result downgrades the UNSAT to a sound `unknown`.
    #[must_use]
    pub fn unsat_proof_terminal_foreign_assume(&self) -> bool {
        let Some(proof) = self.retained_unsat_proof_for_policy() else {
            return false;
        };
        let legit: ay_core::kani_compat::DetHashSet<TermId> =
            self.finite_enum_scope_for_proof(proof).map_or_else(
                || self.proof_legit_assume_set(),
                |scope| scope.into_iter().collect(),
            );
        ay_proof::terminal_trust_report_with_provenance(proof, |t| legit.contains(&t))
            .foreign_assume_on_path
            > 0
    }

    /// Whether the last UNSAT proof references sequence-theory content — any
    /// `Seq`-sorted subterm anywhere in the emitted proof.
    ///
    /// Such a proof is NOT independently checkable and carries no separate
    /// certificate: carcara (our Alethe checker) hard-rejects the problem at
    /// parse time (`sort 'Seq' is not defined`), no firewall-Lean lemma exists
    /// for the sequence theory (the groundable set is datatypes / LIA / EUF /
    /// arrays-ROW2 / strings), and there is no DRAT lane. AY can still find a
    /// sound *internal* refutation — e.g. a `(seq.nth s 0)` term forced to two
    /// distinct integer constants collapses to a clean `la_generic` +
    /// `resolution` chain with zero `hole`/`trust` steps and no foreign
    /// `assume` — so neither the trust/hole gate nor the leak-2 provenance gate
    /// fires, and the UNSAT would ship *bare* under `--strict-proofs` with no
    /// checker able to confirm it. That is a §0-class certification leak: a
    /// strict gate that promises "only results AY can independently verify"
    /// must downgrade this to a sound `unknown`. Consulted by the
    /// `--strict-proofs` CLI gate and the `--self-check` self-certification
    /// gate alongside [`Self::unsat_proof_terminal_foreign_assume`].
    #[must_use]
    pub fn unsat_proof_references_uncheckable_seq_theory(&self) -> bool {
        let Some(proof) = self.retained_unsat_proof_for_policy() else {
            return false;
        };
        let mut stack: Vec<TermId> = Vec::new();
        for step in &proof.steps {
            match step {
                ProofStep::Assume(t) => stack.push(*t),
                ProofStep::Resolution { clause, pivot, .. } => {
                    stack.extend(clause.iter().copied());
                    stack.push(*pivot);
                }
                ProofStep::TheoryLemma { clause, .. } => stack.extend(clause.iter().copied()),
                ProofStep::Step { clause, args, .. } => {
                    stack.extend(clause.iter().copied());
                    stack.extend(args.iter().copied());
                }
                ProofStep::Anchor { .. } => {}
                _ => {}
            }
        }
        let mut visited: ay_core::kani_compat::DetHashSet<TermId> =
            ay_core::kani_compat::DetHashSet::default();
        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }
            if matches!(self.ctx.terms.sort(id), Sort::Seq(_)) {
                return true;
            }
            stack.extend(self.ctx.terms.children(id));
        }
        false
    }

    /// Whether the last UNSAT proof's terminal derivation chain is NOT
    /// trust-free — the deciding predicate of the #8759 strict-proof gate.
    ///
    /// Three independent ways an `unsat` can reach the empty clause without an
    /// end-to-end checkable derivation, any one of which disqualifies it:
    ///
    /// * a `:rule trust`/`hole` step or trust-kind theory lemma is reachable
    ///   from the empty clause;
    /// * an `assume` leaf on that path is not backed by the problem's
    ///   provenance ([`Self::unsat_proof_terminal_foreign_assume`], leak-2) — a
    ///   laundered free axiom is exactly as unverified as a `trust` step;
    /// * the proof references sequence-theory content no external checker can
    ///   parse ([`Self::unsat_proof_references_uncheckable_seq_theory`]).
    ///
    /// This is the ONE definition. It used to live in the `ay` binary
    /// (`crates/ay/src/run.rs::terminal_trust_detected`), which meant a library
    /// consumer of `ay-dpll` got no gate at all: on a clean-but-uncheckable
    /// `Seq` refutation the CLI printed `unknown (incomplete proof-trusted)`
    /// while the same solver returned `unsat` through `Solver::check_sat`. The
    /// CLI now delegates here, and `certify_unsat_for_publication` — the single
    /// public UNSAT funnel — enforces it on every public UNSAT, so both
    /// boundaries answer identically.
    #[must_use]
    pub fn unsat_proof_terminal_trust_detected(&self) -> bool {
        self.retained_unsat_proof_for_policy()
            .is_some_and(|proof| ay_proof::terminal_trust_report(proof).has_terminal_trust())
            || self.unsat_proof_terminal_foreign_assume()
            || self.unsat_proof_references_uncheckable_seq_theory()
    }

    /// Conservative screen for native steps whose effective Alethe spelling
    /// is known to require an honest unproved fallback.
    ///
    /// This is deliberately deny-only. It scans every stored step because the
    /// exporter emits the whole proof, not just the terminal cone, but it does
    /// not attempt to predict every clause-sensitive printer rewrite. The one
    /// evidence-sensitive exception is `LiaGeneric`, whose complete-step
    /// decision is shared with the printer. A known wire gap is sufficient to
    /// refuse `:check-proofs-strict`; absence of one is not advertised as
    /// external semantic validation.
    #[must_use]
    pub fn unsat_proof_has_known_wire_gap(&self) -> bool {
        let Some(proof) = self.retained_unsat_proof_for_policy() else {
            return false;
        };
        self.proof_has_known_wire_gap(proof)
    }

    /// Apply the wire-gap screen to a proof that has not yet been published
    /// into `last_proof`. Proof construction uses this so it never has to
    /// overwrite retained query state merely to inspect a candidate.
    pub(super) fn proof_has_known_wire_gap(&self, proof: &Proof) -> bool {
        // This is the same effective source-syntax channel handed to the
        // ordinary Alethe exporter. In particular, a `LiaGeneric` Farkas
        // certificate may not gain `la_generic` authority from the internal
        // term DAG while the printer is rendering different text.
        let term_overrides = self.proof_export_term_overrides();
        proof.steps.iter().any(|step| match step {
            ProofStep::Assume(term) => {
                matches!(self.ctx.terms.get(*term), TermData::Let(..))
                    || term_overrides
                        .as_ref()
                        .and_then(|overrides| overrides.get(term))
                        // Keep this predicate identical to the printer's let
                        // bridge trigger. `(` is a valid SMT-LIB token
                        // delimiter, so compact `(let((x true))x)` syntax must
                        // be screened as well as whitespace-separated syntax.
                        .is_some_and(|surface| surface.starts_with("(let"))
            }
            ProofStep::TheoryLemma {
                clause,
                farkas,
                kind,
                lia,
                ..
            } => {
                if matches!(
                    kind,
                    ay_core::TheoryLemmaKind::BvBitBlast
                        | ay_core::TheoryLemmaKind::BvBitBlastGate { .. }
                ) && self.bv_constant_disequality_is_fixed_wire_evaluate(clause)
                {
                    return false;
                }
                if ay_proof::lia_divisibility_lowering_supported(
                    &self.ctx.terms,
                    clause,
                    lia.as_ref(),
                    term_overrides.as_ref(),
                ) {
                    return false;
                }
                let wire = ay_proof::promoted_wire_rule(
                    &self.ctx.terms,
                    kind,
                    clause,
                    farkas.as_ref(),
                    term_overrides.as_ref(),
                );
                wire == ay_core::UNPROVED_STEP_RULE
                    || ay_core::alethe_rule_requires_premises_or_args(wire)
            }
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => {
                (matches!(rule, ay_core::AletheRule::True | ay_core::AletheRule::False)
                    && !self.bool_constant_step_is_fixed_wire_axiom(rule, clause, premises, args))
                    || rule.wire_name() == ay_core::UNPROVED_STEP_RULE
            }
            ProofStep::Resolution { .. } | ProofStep::Anchor { .. } => false,
            _ => true,
        })
    }
}
