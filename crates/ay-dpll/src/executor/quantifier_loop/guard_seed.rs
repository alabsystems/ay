// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guard-bound seed instances for entailed real universals
//! (#nra-guard-seed-instances).
//!
//! THE GAP THIS CLOSES. The KeYmaera NRA family states every verification
//! condition as one negated existential over a single `Real` time binder,
//!
//! ```smt2
//! (assert (not (exists ((s Real))
//!   (=> (and (=> (and (<= 0 s) (<= s T)) (P s)) (>= T 0) C1 ... Cn) G))))
//! ```
//!
//! i.e. the entailed universal `∀s. A(s) ∧ ¬G` whose body is a conjunction of
//! binder-free facts `Ci` and one interval-guarded obligation `0 ≤ s ≤ T ⇒
//! P(s)`. There is no ground assertion at all, so CEGQI's first ground solve
//! is the counterexample lemma alone over nonlinear arithmetic; measured on
//! the 2025 census, 184 of 194 gap files never complete a CEGQI round
//! (`cegqi.rounds = 0`), and the query times out with the refutation one
//! instance away: the binder-free conjuncts contradict each other, or the
//! obligation at the guard's end point `s := T` contradicts them.
//!
//! THE FIX IS UNIVERSAL INSTANTIATION AT TERMS THE GUARD NAMES. For every
//! universal the assertion set ENTAILS (the canonical
//! [`crate::ematching::entailed_forall_set`], the same gate CEGQI and the
//! enumerative lane conjoin instances under), each closed term `t` that a
//! comparison atom of the body bounds a binder by (`(<= t s)`, `(<= s t)`,
//! `(= s t)`, any polarity, any operator) is a seed, and the instance
//! `body[s := t]` is asserted. `∀s.φ ⊨ φ[t]` for every closed `t`, so each
//! instance is a consequence of the problem: the pass only ever adds facts
//! that hold in every model, so it can refute and can never wrongly refute,
//! and it removes nothing a `sat` model is checked against. The instance at
//! ANY seed carries every binder-free conjunct, which is the miniscoping
//! consequence (`∀s.(A(s) ∧ B) ⊨ B`) with no fresh symbol introduced.
//!
//! SCOPE. A universal is seeded only when it has one `Real` binder, a
//! quantifier-free body that applies nonlinear arithmetic, and at least one
//! guard bound. Linear quantified real arithmetic is decided by its own lanes
//! (`qlra_lane`) and stays byte-identical; so does every problem without such
//! a universal, which the read-only pre-check turns away before any NNF dual
//! is minted. The refutation itself is looked for first, counterexample-free,
//! by the seed presolve at the primary dispatch (`check_sat/guard_seed_presolve`).
//!
//! NOTHING IS TAKEN ON TRUST. Each instance goes through the same write-side
//! chokepoint the CEGQI instances use: the exact structural instance when
//! proofs are produced, the strict `forall_inst` provenance registration, and
//! the conflict-verification support set. The universal here is the
//! NNF-minted dual of the authored `(not (exists ...))`, not an authored node,
//! so its registration fails closed (`quantified_proof_translation_incomplete`)
//! and the live proof cannot publish on its own; the seed values are recorded
//! as witness hints, which the authored-scope negated-existential lane
//! (`authored_negated_exists_ground_inst`) proposes on the AUTHORED dual, where
//! `qnt_neg_exists` and `forall_inst` re-derive every step against the strict
//! checker. A wrong seed can cost a candidate, never a step.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId, TermStore};

use super::super::Executor;
use crate::ematching::{contains_quantifier, subst_vars};

/// Seeds proposed per universal.
const MAX_SEEDS_PER_QUANTIFIER: usize = 4;
/// Universals seeded per check-sat.
const MAX_SEEDED_QUANTIFIERS: usize = 8;
/// Node budget for one body scan.
const MAX_SCAN_WORK: usize = 20_000;

/// Kill switch (`--no-quantifier-guard-seeds`). Default ON; set, no seed
/// instance is asserted and the quantifier pipeline's assertion vector is
/// byte-identical to the pre-pass one. For A/B measurement.
pub(in crate::executor) fn guard_seed_instances_enabled() -> bool {
    !ay_core::misc_cli_flags().no_quantifier_guard_seeds
}

/// The comparison operators whose operands name a guard bound.
fn is_comparison(name: &str) -> bool {
    matches!(name, "<=" | "<" | ">=" | ">" | "=")
}

/// Whether `term` is a numeral (possibly negated or a numeral quotient).
fn is_numeral(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(_) => true,
        TermData::App(Symbol::Named(op), args) if matches!(op.as_str(), "-" | "/") => {
            args.iter().all(|&arg| is_numeral(terms, arg))
        }
        _ => false,
    }
}

/// SCOPE: whether `body` applies NONLINEAR real arithmetic — a product of two
/// or more non-numeral factors, or a division by a non-numeral. The pass is
/// scoped to these universals because the stall it closes is the ground NRA
/// search's (module docs); linear quantified arithmetic has its own decision
/// lanes (`qlra_lane`), which this pass leaves byte-identical. Bounded: an
/// exhausted scan answers `false` (no seeding), which only withholds
/// consequences.
fn applies_nonlinear_arithmetic(terms: &TermStore, body: TermId) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![body];
    while let Some(node) = stack.pop() {
        if !seen.insert(node) {
            continue;
        }
        if seen.len() > MAX_SCAN_WORK {
            return false;
        }
        match terms.get(node) {
            TermData::App(Symbol::Named(op), args) => {
                let nonlinear = match op.as_str() {
                    "*" => args.iter().filter(|&&arg| !is_numeral(terms, arg)).count() >= 2,
                    "/" => args.iter().skip(1).any(|&arg| !is_numeral(terms, arg)),
                    _ => false,
                };
                if nonlinear {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            _ => {}
        }
    }
    false
}

/// Whether `vars`/`body` is a universal this pass seeds: one `Real` binder, a
/// quantifier-free body that applies nonlinear arithmetic, and at least one
/// guard bound. Returns the seeds.
fn seedable(terms: &TermStore, vars: &[(String, Sort)], body: TermId) -> Vec<TermId> {
    let [(name, sort @ Sort::Real)] = vars else {
        return Vec::new();
    };
    if contains_quantifier(terms, body) || !applies_nonlinear_arithmetic(terms, body) {
        return Vec::new();
    }
    guard_bound_seeds(terms, body, name, sort)
}

/// Whether `term` mentions a variable named `name` (by name; a shadowing
/// inner binder counts, which can only reject a candidate). Bounded: an
/// exhausted scan answers `true`.
fn mentions_name(terms: &TermStore, term: TermId, name: &str) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![term];
    while let Some(node) = stack.pop() {
        if !seen.insert(node) {
            continue;
        }
        if seen.len() > MAX_SCAN_WORK {
            return true;
        }
        match terms.get(node) {
            TermData::Var(var, _) if var == name => return true,
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            // A binder or a `let` inside a seed is never a closed ground term
            // the proof validator would accept; refuse it outright.
            TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return true,
            _ => {}
        }
    }
    false
}

/// The closed terms that comparison atoms of `body` bound the binder `name`
/// by, in first-occurrence order, deduplicated and capped. Only the Boolean
/// skeleton is walked (connectives, `not`, `ite` conditions); the scan never
/// enters a nested binder.
pub(super) fn guard_bound_seeds(
    terms: &TermStore,
    body: TermId,
    name: &str,
    sort: &Sort,
) -> Vec<TermId> {
    let mut out: Vec<TermId> = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![body];
    while let Some(node) = stack.pop() {
        if out.len() >= MAX_SEEDS_PER_QUANTIFIER || seen.len() > MAX_SCAN_WORK {
            break;
        }
        if !seen.insert(node) {
            continue;
        }
        match terms.get(node) {
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) if *terms.sort(node) == Sort::Bool => {
                stack.extend([*e, *t, *c]);
            }
            TermData::App(Symbol::Named(op), args) if is_comparison(op) && args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);
                let is_binder =
                    |t: TermId| matches!(terms.get(t), TermData::Var(var, _) if var == name);
                let candidate = match (is_binder(lhs), is_binder(rhs)) {
                    (true, false) => Some(rhs),
                    (false, true) => Some(lhs),
                    _ => None,
                };
                if let Some(bound) = candidate {
                    if terms.sort(bound) == sort
                        && !out.contains(&bound)
                        && !mentions_name(terms, bound, name)
                    {
                        out.push(bound);
                    }
                } else if op == "=" && *terms.sort(lhs) == Sort::Bool {
                    // Boolean `=` is an iff: walk both sides.
                    stack.extend([rhs, lhs]);
                }
            }
            TermData::App(Symbol::Named(op), args)
                if matches!(op.as_str(), "and" | "or" | "=>" | "xor") =>
            {
                stack.extend(args.iter().rev().copied());
            }
            _ => {}
        }
    }
    out
}

/// Read-only pre-check: does `term` contain a quantifier this pass could seed?
/// Keeps every problem without one byte-identical (no NNF dual is minted).
fn has_seedable_quantifier(terms: &TermStore, term: TermId) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![term];
    while let Some(node) = stack.pop() {
        if !seen.insert(node) || seen.len() > MAX_SCAN_WORK {
            continue;
        }
        match terms.get(node) {
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                if !seedable(terms, vars, *body).is_empty() {
                    return true;
                }
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            _ => {}
        }
    }
    false
}

impl Executor {
    /// Assert the guard-bound seed instances of every entailed single-binder
    /// `Real` universal (module docs). Returns the number of instances added.
    pub(super) fn add_guard_bound_seed_instances(&mut self) -> usize {
        if !guard_seed_instances_enabled() {
            return 0;
        }
        let snapshot = self.ctx.assertions.clone();
        if !snapshot
            .iter()
            .any(|&a| has_seedable_quantifier(&self.ctx.terms, a))
        {
            return 0;
        }
        let entailed = crate::ematching::entailed_forall_set(&mut self.ctx.terms, &snapshot);
        self.record_entailed_forall_authority(&entailed);
        let mut quantifiers: Vec<TermId> = entailed.into_iter().collect();
        quantifiers.sort_unstable_by_key(|q| q.index());

        let mut records: Vec<crate::ematching::ForallInstantiationProvenance> = Vec::new();
        let mut seeded = 0usize;
        for quantifier in quantifiers {
            if seeded >= MAX_SEEDED_QUANTIFIERS {
                break;
            }
            if self.ctx.terms.is_no_mbqi(quantifier) {
                continue;
            }
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(quantifier).clone() else {
                continue;
            };
            let seeds = seedable(&self.ctx.terms, &vars, body);
            let [(name, sort)] = vars.as_slice() else {
                continue;
            };
            if seeds.is_empty() {
                continue;
            }
            seeded += 1;
            for seed in seeds {
                let mut subst: HashMap<String, TermId> = HashMap::default();
                subst.insert(name.clone(), seed);
                let instance = if self.produce_proofs_enabled() {
                    match self.exact_forall_instance(quantifier, &[seed]) {
                        Some(exact) => exact,
                        None => {
                            self.quantified_proof_translation_incomplete = true;
                            subst_vars(&mut self.ctx.terms, body, &subst)
                        }
                    }
                } else {
                    subst_vars(&mut self.ctx.terms, body, &subst)
                };
                if contains_quantifier(&self.ctx.terms, instance) {
                    continue;
                }
                self.note_cegqi_witness_hint(sort, seed);
                records.push(crate::ematching::ForallInstantiationProvenance {
                    quantifier,
                    binding: vec![seed],
                    instance,
                });
            }
        }
        if records.is_empty() {
            return 0;
        }
        self.register_ematching_proof_provenance(&records);
        let mut added = 0usize;
        for record in records {
            if !self.ctx.assertions.contains(&record.instance) {
                self.ctx.assertions.push(record.instance);
                added += 1;
            }
            self.push_active_support_axiom(record.instance);
        }
        tracing::debug!(
            target: "ay::cert::guard_seed",
            "seeded_quantifiers={seeded} instances_added={added}"
        );
        added
    }
}

#[cfg(test)]
#[path = "guard_seed_tests.rs"]
mod tests;
