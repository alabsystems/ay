// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground instances of authored universals, and distinct constant endpoints,
//! for the authored equality closure (#uf-quantified-rows).
//!
//! THE GAP THIS CLOSES, MEASURED (ad60a0707, 2026-09-25). Five MODEL_CHECKER_CONSUMER UF
//! controls (`model_checker_consumer_quantified_counterexample_uf_{false_matrix,false_query,
//! nullary_global}_unsat`, `model_checker_consumer_quantified_safety_uf_{nested,scalar}_unsat`)
//! answered `unknown (incomplete self-check-rejected)` under `:produce-proofs`
//! and `unsat` without it: the refutation reaching the strict gate ended in an
//! underived `trust` step (`strict UNSAT proof validation failed: step t1 uses
//! unverified trust rule`; t14 on `uf_nested`, t0 on `uf_scalar`). The lanes
//! that refute them record no derivation, and every authored cascade member
//! declined the result: none seeds a GUARDED instance, and the plain equality
//! closure has no closer for two distinct constants.
//!
//! Each refutation is small: at most one ground instance of an authored
//! guarded universal whose guards are authored roots or closed ground facts,
//! an equality chain over the authored roots, and either an authored
//! disequality or two distinct literal constants at the chain's ends. This
//! member adds exactly that to the closure:
//!
//! * SEEDS. For every authored universal `(forall (x..) (or E (not g1) ..))`
//!   whose body is quantifier-free and holds ONE positive equality `E`, the
//!   binder tuple is read off by matching an application of the body against
//!   a ground application of the authored roots (outside every binder). The
//!   instance is the exact raw substitution `subst_vars_exact_qf` — the
//!   counterpart of the checker's `forall_inst` matcher — and every disjunct
//!   other than `E` must be refuted by an exact authored conjunction leaf or by
//!   a closed comparison over LITERAL operands the checker's own `evaluate`
//!   recognizer re-derives (pinned carcara misevaluates `bvsub`, the signed
//!   operators and `extract`, so no nested closed operand is evaluated).
//!   Otherwise the tuple is dropped. A surviving instance seeds `E` with the
//!   recipe `assume F; forall_inst; or; resolution; or; resolution per guard`.
//! * CLOSER. A derived equality between two distinct constants is refuted by
//!   `evaluate` of `(= c d)` to `false`, admitted only when the checker's own
//!   ground evaluator (`recognize_ground_evaluate`) re-derives it. It has no
//!   width ceiling, so the 136-bit `nullary_global` pins close the same way
//!   the 1-bit ones do. Without an instance, the run proceeds only when two
//!   seeds end at distinct literals (the one thing it can add to the plain
//!   member's run).
//!
//! NOTHING IS TAKEN ON THE PRODUCER'S WORD. Matching and guard selection are
//! hints: `validate_forall_inst` re-derives the substitution and groundness,
//! `validate_ground_evaluate` the closed guard, `validate_euf_transitive` /
//! `validate_euf_congruent` every chain edge, and the endpoint recognizer the
//! constant disequality. The candidate replaces the proof only through the
//! closure's shared commit gate (reachable assumes inside the exact authored
//! scope, empty clause, plain strict check). A wrong hint costs a declined
//! candidate — the verdict stays the `unknown` it already was.
//!
//! WIRE SCREEN. The member exists to publish what pinned carcara checks, so
//! it also declines a candidate the cascade's own publishability screen
//! (`proof_has_known_wire_gap`) flags; the cascade would otherwise stop at
//! that candidate. Measured on e248547d5 with the member unscreened: a
//! `define-fun` in a closed guard turned a fail-closed `unknown` into `unsat`
//! whose export is refused (`evaluate conclusion changed under surface
//! rewriting`), and so did a Real endpoint respelling; a `let`-authored
//! universal published two `hole`s. Each stays `unknown` now.
//!
//! The screen runs before the authored surface is restored for export, so it
//! cannot see a gap the printer meets only after restoring it. The printer
//! closes the two it met: a universal whose authored body is not the internal
//! `or` (`(not (and g (not E)))`, `(=> G (or C R))`, a double negation, a
//! negated `distinct`) derives its canonical instance (`flattened_clause.rs`
//! and `negation.rs` under `surface_equivalence/`), and one inside a flat
//! authored `and` root derives its canonical conjunct under `bind`
//! (`surface_and_pos/quantified_body.rs`); at 938ec0327 they published a
//! `hole` at the `or` step and a refused export (`and_pos indexed conjunct is
//! absent`). A shape no bridge relates (a nested `and` root, a literal
//! elaboration simplified away) keeps that honest outcome, failing closed
//! under `--strict-proofs`.
//!
//! It is a SEPARATE cascade member placed after every member that can repair
//! a proof today, so every proof one of them publishes is byte-identical.

use super::*;

mod matching;
use crate::proof_tracker::guarded_instance::{
    closed_comparison_over_literals, emit_evaluated_unit,
};
use matching::{binder_tuples, harvest_ground_applications};

/// Instances proposed across all authored universals of one closure run.
const MAX_INSTANCES: usize = 16;
/// Ground applications harvested outside binders.
const MAX_GROUND_TERMS: usize = 256;
/// Binders per instantiated universal.
const MAX_BINDERS: usize = 4;
/// Disjuncts per instantiated body.
const MAX_DISJUNCTS: usize = 8;
/// Node visits for harvesting plus matching, per closure run.
const MAX_MATCH_WORK: usize = 50_000;

/// How one non-equality disjunct of an instance is refuted.
#[derive(Clone, Debug)]
enum GuardRefutation {
    /// Its complement is an exact authored conjunction leaf (leaf index).
    Leaf(usize),
    /// Its complement is a closed literal `evaluate` re-derives.
    Evaluated(TermId),
}

#[derive(Clone, Debug)]
struct GuardDischarge {
    /// The instance disjunct being removed.
    disjunct: TermId,
    /// Resolution pivot: the atom of `disjunct`.
    pivot: TermId,
    refutation: GuardRefutation,
}

/// One checked-by-construction ground instance of an authored universal.
#[derive(Clone, Debug)]
pub(super) struct AuthoredGroundInstance {
    /// Leaf index of the authored `forall`.
    forall_leaf: usize,
    /// Binder values in binding order (`forall_inst` `:args`).
    values: Vec<TermId>,
    /// The substituted body.
    instance: TermId,
    /// The instance's disjuncts, or the instance itself when not an `or`.
    disjuncts: Vec<TermId>,
    /// The one positive equality disjunct.
    equality: TermId,
    guards: Vec<GuardDischarge>,
}

/// A quantifier-free body read as one positive equality plus guard disjuncts.
struct GuardedBody {
    body: TermId,
    is_or: bool,
    width: usize,
    equality_at: usize,
}

impl GuardedBody {
    fn decode(terms: &TermStore, body: TermId) -> Option<Self> {
        let (is_or, disjuncts) = match terms.get(body) {
            TermData::App(Symbol::Named(name), args) if name == "or" => (true, args.clone()),
            _ => (false, vec![body]),
        };
        if disjuncts.is_empty() || disjuncts.len() > MAX_DISJUNCTS {
            return None;
        }
        let mut equalities = disjuncts
            .iter()
            .enumerate()
            .filter(|(_, disjunct)| decode_eq_local(terms, **disjunct).is_some());
        let (equality_at, _) = equalities.next()?;
        if equalities.next().is_some() {
            return None;
        }
        Some(Self {
            body,
            is_or,
            width: disjuncts.len(),
            equality_at,
        })
    }

    /// The instance's disjuncts, when it kept the body's `or` shape.
    fn instance_disjuncts(&self, terms: &TermStore, instance: TermId) -> Option<Vec<TermId>> {
        if !self.is_or {
            return Some(vec![instance]);
        }
        match terms.get(instance) {
            TermData::App(Symbol::Named(name), args)
                if name == "or" && args.len() == self.width =>
            {
                Some(args.clone())
            }
            _ => None,
        }
    }
}

impl Executor {
    /// Cascade member: the authored equality closure seeded with checked
    /// ground instances of authored universals and closed on distinct
    /// constant endpoints. See the module documentation.
    pub(in crate::executor::proof) fn replace_with_authored_instance_closure_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        let Some(leaves) = authored_closure_leaves(&self.ctx.terms, &authored) else {
            return;
        };
        let (mut derived, goals) = authored_closure_seeds(&self.ctx.terms, &leaves);
        let instance_roots = self.seed_authored_ground_instances(&leaves, &mut derived);
        // With no instance seeded, only the constant-endpoint closer can add
        // anything to the plain member's run, and it needs two seeds ending at
        // distinct literals of one sort: saturation joins existing endpoints
        // and applications, never constants. Otherwise decline before
        // repeating the plain member's saturation.
        if instance_roots.is_empty() && !seeds_reach_two_constants(&self.ctx.terms, &derived) {
            return;
        }
        let seeds = AuthoredClosureSeeds {
            leaves: &leaves,
            goals: &goals,
            instance_roots: &instance_roots,
            constant_endpoints: true,
            wire_clean_only: true,
        };
        self.close_authored_equalities(proof, &authored, seeds, derived);
    }

    /// Append the equality of every admissible ground instance to `derived`,
    /// returning those equalities for the congruence universe.
    fn seed_authored_ground_instances(
        &mut self,
        leaves: &[AuthoredLeaf],
        derived: &mut Vec<AuthoredDerivedEq>,
    ) -> Vec<TermId> {
        let mut work = 0usize;
        let ground = harvest_ground_applications(&self.ctx.terms, leaves, &mut work);
        let mut roots = Vec::new();
        let mut proposed = 0usize;
        for (forall_leaf, leaf) in leaves.iter().enumerate() {
            let TermData::Forall(bindings, body, _) = self.ctx.terms.get(leaf.term) else {
                continue;
            };
            let (bindings, body) = (bindings.clone(), *body);
            if bindings.is_empty()
                || bindings.len() > MAX_BINDERS
                || crate::ematching::contains_quantifier(&self.ctx.terms, body)
            {
                continue;
            }
            let Some(shape) = GuardedBody::decode(&self.ctx.terms, body) else {
                continue;
            };
            let names: Vec<String> = bindings.iter().map(|(name, _)| name.clone()).collect();
            for values in binder_tuples(&self.ctx.terms, &names, body, &ground, &mut work) {
                if proposed >= MAX_INSTANCES {
                    return roots;
                }
                proposed += 1;
                let Some(instance) =
                    self.ground_instance(leaves, forall_leaf, &names, &shape, values)
                else {
                    continue;
                };
                let Some((a, b)) = decode_eq_local(&self.ctx.terms, instance.equality) else {
                    continue;
                };
                if a == b {
                    continue;
                }
                let equality = instance.equality;
                let entry = AuthoredDerivedEq {
                    eq: equality,
                    a,
                    b,
                    derivation: AuthoredEqDerivation::Instance(Box::new(instance)),
                };
                if push_authored_derived_eq(derived, entry) {
                    roots.push(equality);
                }
            }
        }
        roots
    }

    /// Build the instance for one binder tuple, or `None` when some guard has
    /// no exact authored or closed-evaluation refutation.
    fn ground_instance(
        &mut self,
        leaves: &[AuthoredLeaf],
        forall_leaf: usize,
        names: &[String],
        shape: &GuardedBody,
        values: Vec<TermId>,
    ) -> Option<AuthoredGroundInstance> {
        let mut substitution = ay_core::kani_compat::DetHashMap::default();
        for (name, &value) in names.iter().zip(&values) {
            let _ = substitution.insert(name.clone(), value);
        }
        let instance =
            crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, shape.body, &substitution)?;
        let disjuncts = shape.instance_disjuncts(&self.ctx.terms, instance)?;
        let equality = *disjuncts.get(shape.equality_at)?;
        let mut guards = Vec::with_capacity(disjuncts.len().saturating_sub(1));
        for (position, &disjunct) in disjuncts.iter().enumerate() {
            if position == shape.equality_at {
                continue;
            }
            let atom = match self.ctx.terms.get(disjunct) {
                TermData::Not(atom) => Some(*atom),
                _ => None,
            };
            let (pivot, complement) = match atom {
                Some(atom) => (atom, atom),
                None => (disjunct, self.ctx.terms.mk_not_raw(disjunct)),
            };
            let refutation = if let Some(leaf) = leaves.iter().position(|l| l.term == complement) {
                GuardRefutation::Leaf(leaf)
            } else if closed_comparison_over_literals(&self.ctx.terms, complement)
                && ay_proof::recognize_ground_evaluate(&self.ctx.terms, complement)
            {
                GuardRefutation::Evaluated(complement)
            } else {
                return None;
            };
            guards.push(GuardDischarge {
                disjunct,
                pivot,
                refutation,
            });
        }
        Some(AuthoredGroundInstance {
            forall_leaf,
            values,
            instance,
            disjuncts,
            equality,
            guards,
        })
    }

    /// Closer: a derived equality between two distinct constants, refuted by
    /// a closed `evaluate` the checker's own ground evaluator re-derives.
    pub(super) fn build_constant_endpoint_candidate(
        &mut self,
        leaves: &[AuthoredLeaf],
        derived: &[AuthoredDerivedEq],
    ) -> Option<Proof> {
        for (index, entry) in derived.iter().enumerate() {
            let is_constant = |term| matches!(self.ctx.terms.get(term), TermData::Const(_));
            if !is_constant(entry.a) || !is_constant(entry.b) {
                continue;
            }
            let disequality = self.ctx.terms.mk_not_raw(entry.eq);
            if !ay_proof::recognize_ground_evaluate(&self.ctx.terms, disequality) {
                continue;
            }
            let mut builder = AuthoredEqProofBuilder::new(leaves, derived);
            let equality = builder.emit_derived(&mut self.ctx.terms, index)?;
            let mut candidate = builder.finish();
            let refuted = emit_evaluated_unit(&mut candidate, &mut self.ctx.terms, disequality);
            candidate.add_resolution(Vec::new(), entry.eq, equality, refuted);
            return Some(candidate);
        }
        None
    }
}

impl AuthoredEqProofBuilder<'_> {
    /// Derive an instance's equality disjunct as a UNIT clause.
    pub(super) fn emit_ground_instance(
        &mut self,
        terms: &mut TermStore,
        instance: &AuthoredGroundInstance,
    ) -> Option<ProofId> {
        let forall = self.leaves.get(instance.forall_leaf)?.term;
        let forall_unit = self.emit_leaf(terms, instance.forall_leaf)?;
        let not_forall = terms.mk_not_raw(forall);
        let implication = terms.mk_app(
            Symbol::named("or"),
            [not_forall, instance.instance],
            Sort::Bool,
        );
        let instantiated = self.proof.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            instance.values.clone(),
        );
        let clausified = self.proof.add_rule_step(
            AletheRule::Or,
            vec![not_forall, instance.instance],
            vec![instantiated],
            Vec::new(),
        );
        let mut current =
            self.proof
                .add_resolution(vec![instance.instance], forall, clausified, forall_unit);
        if instance.guards.is_empty() {
            return (instance.instance == instance.equality).then_some(current);
        }
        let mut residual = instance.disjuncts.clone();
        current =
            self.proof
                .add_rule_step(AletheRule::Or, residual.clone(), vec![current], Vec::new());
        for guard in &instance.guards {
            let unit = match guard.refutation {
                GuardRefutation::Leaf(leaf) => self.emit_leaf(terms, leaf)?,
                GuardRefutation::Evaluated(literal) => {
                    emit_evaluated_unit(&mut self.proof, terms, literal)
                }
            };
            let at = residual
                .iter()
                .position(|&literal| literal == guard.disjunct)?;
            let _ = residual.remove(at);
            current = self
                .proof
                .add_resolution(residual.clone(), guard.pivot, current, unit);
        }
        (residual == [instance.equality]).then_some(current)
    }
}

/// Whether two seeds end at distinct literal constants of one sort.
fn seeds_reach_two_constants(terms: &TermStore, derived: &[AuthoredDerivedEq]) -> bool {
    let mut constants: Vec<TermId> = Vec::new();
    for entry in derived {
        for side in [entry.a, entry.b] {
            if !matches!(terms.get(side), TermData::Const(_)) || constants.contains(&side) {
                continue;
            }
            if constants
                .iter()
                .any(|&constant| terms.sort(constant) == terms.sort(side))
            {
                return true;
            }
            constants.push(side);
        }
    }
    false
}

#[cfg(test)]
mod tests;
