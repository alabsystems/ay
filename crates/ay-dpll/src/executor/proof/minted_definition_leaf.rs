// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derive a premiseless `trust` leaf that is an AUTHORED assertion with one or
//! more sub-terms replaced by a FRESH symbol the proof never defines — by
//! MINTING the missing definition as a checked `fresh_def_eq` step.
//!
//! # The class, and the two corrections the measurement forces
//!
//! `purify_bool_args` replaces a COMPOUND Boolean argument `b` of an
//! uninterpreted `f` with a fresh Boolean `p` so EUF can congruence-close over
//! `f(p)`. The rewritten assertion is not authored, so it demotes to a
//! premiseless `trust` step. `proof_fresh_def` PROMOTES such a definition when
//! the proof already carries it as a leaf; the residual is the case where it
//! does NOT.
//!
//! Two things the census doc
//! (the development design notes) states about
//! this class are refuted by re-measurement, and both changed this lane's
//! design:
//!
//! 1. **"a candidate `(= p b)` that is in the handed `problem_assertions`"** —
//!    there is none. `purify_bool_args` APPENDS its definitions to
//!    `ctx.assertions`, and `check_sat` RESTORES that stack to the originals on
//!    every exit path, so the definitions are scope-transient and are gone long
//!    before this lane runs. Measured on `clearsy_0000_00307_falsesat13`:
//!    `boolarg_*` occurs in **0 of the 320** handed assertions and **0 of the
//!    208** strict-scope assertions. The definiens has to be RECOVERED, and the
//!    only place it survives is the AUTHORED assertion the leaf is a rewrite
//!    of.
//! 2. **"the whole-conjunction congruence route WORKS"** — for 6 of the 34
//!    `and`-headed leaves, not 34. The other 28 differ from their authored
//!    counterpart at a position underneath a `TermData::Not` node, and
//!    `ay_proof`'s proof-producing congruence forest deliberately descends only
//!    `TermData::App` (its module docs give the reason: `eq_congruent`'s
//!    validator requires both sides of its conclusion to be `App` with the same
//!    symbol, so a `Not` congruence could not be lowered). This lane declines
//!    those at the ALIGNMENT stage rather than planning a derivation that can
//!    never close.
//!
//! Measured population, all 639 `.smt2` under `benchmarks/`, by an INDEPENDENT
//! re-parse of the dumped canonical S-expressions:
//!
//! | leaves | file | verdict |
//! |---|---|---|
//! | 3 | `soundness_qf_uf_incremental/clearsy_0000_00307_falsesat13` | REACHABLE |
//! | 3 | `soundness_qf_uf_incremental/clearsy_0001_00310_falsesat44` | REACHABLE |
//! | 13 + 13 | the same two files | a differing position under a `not` |
//! | 1 | `soundness_fuzz_round2/seq_falsesat_iteofseq_eq_operand` | no same-arity authored root |
//! | 1 | `soundness_fuzz_round2/seq_falsesat_nth_ground_eval` | the differing position is not a fresh variable |
//!
//! # Authority — this is the ONE authority-shaped lane in the family
//!
//! Every other bridge lane only ever `assume`s an authored assertion. This one
//! additionally WRITES a definition the proof did not contain. Its soundness is
//! the conservative definitional-extension argument
//! [`ay_proof::FreshDefRegistry`] already carries, and the checker RE-DECIDES
//! every part of it over the finished proof:
//!
//! * **FRESH** — the definiendum occurs in no problem assertion (both scopes)
//!   and in no `assume` of the proof;
//! * **INDEPENDENT** — no definiendum occurs inside any definiens;
//! * **SORT** — definiendum and definiens have the same sort;
//! * **SINGLE DEFINIENS** — one definiens per symbol, across BOTH
//!   fresh-definition rules, which is why an EXISTING binding in the proof is
//!   ADOPTED rather than competed with.
//!
//! Note what the argument does NOT depend on: it does not depend on the minted
//! definiens being the one `purify_bool_args` chose. ANY conservative
//! extension is sound; a definiens that is not the producer's simply fails to
//! close the congruence and the leaf keeps its byte-identical `trust` step. The
//! alignment below is therefore a heuristic for CHOOSING a candidate, and the
//! four conditions above are the whole of the authority.
//!
//! # Ordering, and the fail-closed gate
//!
//! This lane runs AFTER `demote_non_problem_assumptions` and after every other
//! derivation lane, because the checker decides freshness against the FINISHED
//! proof's `assume` set — including the `assume`s the sibling lanes write. It
//! is the same ordering `promote_fresh_definitional_bounds` needs and for the
//! same reason.
//!
//! `commit_bridge_fragments`' whole-proof backstop reverts a rewrite that does
//! not `check_proof` or that costs a certification the original had, but that
//! is NOT sufficient here: a malformed or non-fresh definition turns a
//! RESCUABLE `TrustStep` rejection into a HARD `InvalidTheoryLemma` one, which
//! the backstop does not catch because the original did not certify either.
//! So this lane adds **Gate 2**: after the splice it re-runs the checker's own
//! [`ay_proof::FreshDefRegistry::collect`] over the whole proof, against the
//! UNION of both authored scopes, and reverts the entire rewrite on any
//! decline. A superset scope can only make the freshness test stricter, never
//! more permissive, so the union is the conservative choice.
//!
//! # Guards
//!
//! Each is mutation-checked in `minted_definition_leaf_tests.rs`.
//!
//! 1. **No `Anchor` steps.**
//! 2. **A premiseless, argument-free `trust` step with a unit clause that is
//!    NOT a binary `=`.**
//! 3. **The root is in BOTH authored scopes** — the sibling lanes' Guard 3.
//! 4. **The alignment descends only `App`**, exactly as the congruence forest
//!    does, and every differing position must be (fresh variable, term).
//! 5. **FRESH** — the definiendum's NAME occurs in neither authored scope nor
//!    any `assume` of the proof.
//! 6. **SINGLE DEFINIENS** — one definiens per name within the leaf, and
//!    consistent with every `fresh_def_eq` / `fresh_def_bound` binding already
//!    in the proof.
//! 7. **INDEPENDENT** — no minted or existing definiendum name occurs in any
//!    minted or existing definiens.
//! 8. **The checker's OWN recognizer admits the step** —
//!    `ay_core::proof_validation::recognize_fresh_def_eq` is asked for the
//!    exact `(clause, premises, args)` triple before the definition may enter
//!    the pool, and again at emission time.
//! 9. **The congruence derivation strict-checks** on its own, and the
//!    propositional step is chosen by the checker (the non-equality bridge's
//!    Guards 6 and 7, reused unchanged).
//! 10. **Gate 2** — the whole-proof `FreshDefRegistry::collect`, above.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::proof_validation::recognize_fresh_def_eq;
use ay_core::{AletheRule, Proof, ProofStep, TermData, TermId};

use super::super::Executor;
use super::rewritten_assertion_bridge::{is_binary_equality, HypothesisLeaf};

/// Largest number of `trust` leaves one call will plan for.
const MAX_MINTED_LEAVES: usize = 512;

/// Largest number of AUTHORED roots one leaf is tried against.
const MAX_MINTED_ROOTS_PER_LEAF: usize = 64;

/// Largest number of definitions one leaf may mint. The measured population
/// needs 1-4; the cap bounds an adversarial input.
pub(super) const MAX_MINTED_PER_LEAF: usize = 16;

/// Largest number of node pairs one alignment will visit.
pub(super) const MAX_ALIGN_NODES: usize = 4096;

/// Whether `step` is a leaf this lane may replace (Guard 2).
fn is_minted_candidate(terms: &ay_core::TermStore, step: &ProofStep) -> Option<TermId> {
    let ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises,
        args,
    } = step
    else {
        return None;
    };
    if !premises.is_empty() || !args.is_empty() || clause.len() != 1 {
        return None;
    }
    let atom = clause[0];
    (!is_binary_equality(terms, atom)).then_some(atom)
}

/// Align `leaf` against `root`, descending ONLY same-symbol, same-arity `App`
/// nodes — exactly what `ay_proof`'s congruence forest can explain (Guard 4).
///
/// Records one `(leaf sub-term, root sub-term)` pair per differing position.
/// Returns `false` when the budget is exhausted.
pub(super) fn align(
    terms: &ay_core::TermStore,
    leaf: TermId,
    root: TermId,
    out: &mut Vec<(TermId, TermId)>,
    budget: &mut usize,
) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    if leaf == root {
        return true;
    }
    if let (TermData::App(left_sym, left_args), TermData::App(right_sym, right_args)) =
        (terms.get(leaf), terms.get(root))
    {
        if left_sym == right_sym && left_args.len() == right_args.len() {
            let pairs: Vec<(TermId, TermId)> = left_args
                .iter()
                .copied()
                .zip(right_args.iter().copied())
                .collect();
            for (left, right) in pairs {
                if !align(terms, left, right, out, budget) {
                    return false;
                }
            }
            return true;
        }
    }
    out.push((leaf, root));
    true
}

/// Everything one leaf is planned against: the roots it may `assume`, the base
/// hypothesis pool, and the three vetting inputs. Bundled so the planner takes
/// one borrow rather than seven, which is also what keeps this file free of a
/// `too_many_arguments` waiver.
pub(super) struct MintContext<'a> {
    pub(super) roots: &'a DetHashMap<(String, usize), Vec<TermId>>,
    pub(super) base_pool: &'a [TermId],
    pub(super) base_leaf_of: &'a DetHashMap<TermId, HypothesisLeaf>,
    pub(super) constrained: &'a DetHashSet<String>,
    pub(super) existing: &'a DetHashMap<String, TermId>,
    pub(super) overrides: Option<&'a DetHashMap<TermId, String>>,
}

/// One definition this lane would write.
#[derive(Clone)]
pub(super) struct Minted {
    pub(super) definiendum: TermId,
    pub(super) definition: TermId,
}

impl Executor {
    /// Replace every premiseless `trust` step that is an AUTHORED assertion
    /// with fresh-symbol sub-terms substituted in, by MINTING the missing
    /// definitions and deriving the leaf by congruence. Returns the number of
    /// leaves replaced.
    pub(in crate::executor) fn derive_leaves_over_minted_definitions(
        &mut self,
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) -> usize {
        // Guard 1.
        if proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Anchor { .. }))
        {
            return 0;
        }
        let leaves: Vec<(usize, TermId)> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| {
                is_minted_candidate(&self.ctx.terms, step).map(|atom| (index, atom))
            })
            .take(MAX_MINTED_LEAVES.saturating_add(1))
            .collect();
        if leaves.is_empty() || leaves.len() > MAX_MINTED_LEAVES {
            return 0;
        }
        // Guard 3: the roots this lane may `assume`, and the base pool, are
        // the sibling lane's exactly.
        let roots = self.nonequality_roots(problem_assertions);
        if roots.is_empty() {
            return 0;
        }
        let (base_pool, base_leaf_of) = self.bridge_hypothesis_pool(proof, problem_assertions);
        // Guard 5: the names no minted definiendum may carry. This is the
        // checker's own FRESH condition, computed over the FINISHED proof.
        let constrained = self.minted_constrained_names(proof, problem_assertions);
        // Guard 6, first half: the bindings already in the proof, which a
        // minted definition must ADOPT rather than compete with.
        let existing = self.existing_fresh_definitions(proof);
        let overrides = self.last_proof_term_overrides.clone();
        let context = MintContext {
            roots: &roots,
            base_pool: &base_pool,
            base_leaf_of: &base_leaf_of,
            constrained: &constrained,
            existing: &existing,
            overrides: overrides.as_ref(),
        };

        let mut plans: Vec<Option<Vec<ProofStep>>> = std::iter::repeat_with(|| None)
            .take(proof.steps.len())
            .collect();
        let mut planned = 0usize;
        for (step, atom) in leaves {
            let Some(fragment) = self.plan_minted_fragment(atom, &context) else {
                continue;
            };
            plans[step] = Some(fragment);
            planned += 1;
        }
        if planned == 0 {
            return 0;
        }
        let original = proof.steps.clone();
        let original_named = proof.named_steps.clone();
        let derived = self.commit_bridge_fragments(proof, plans);
        if derived == 0 {
            return 0;
        }
        // GATE 2: the CHECKER's own whole-proof fresh-definition validation,
        // against the UNION of both authored scopes. A decline reverts every
        // splice, so a minted definition can never turn a rescuable trust
        // rejection into a hard `InvalidTheoryLemma` one.
        let mut scope: Vec<TermId> = problem_assertions.to_vec();
        let seen: DetHashSet<TermId> = scope.iter().copied().collect();
        for assertion in self.complete_problem_assertions_for_strict_proof() {
            if !seen.contains(&assertion) {
                scope.push(assertion);
            }
        }
        if ay_proof::FreshDefRegistry::collect(proof, &self.ctx.terms, Some(&scope)).is_err() {
            proof.steps = original;
            proof.named_steps = original_named;
            return 0;
        }
        derived
    }

    /// Plan the replacement fragment for one leaf, or `None`.
    fn plan_minted_fragment(
        &mut self,
        atom: TermId,
        context: &MintContext<'_>,
    ) -> Option<Vec<ProofStep>> {
        let MintContext {
            roots,
            base_pool,
            base_leaf_of,
            constrained,
            existing,
            overrides,
        } = context;
        let overrides = *overrides;
        let key = super::rewritten_nonequality_bridge::head_key(&self.ctx.terms, atom)?;
        let candidates = roots.get(&key)?;
        for &root in candidates.iter().take(MAX_MINTED_ROOTS_PER_LEAF) {
            if root == atom {
                continue;
            }
            let Some(minted) = self.mint_definitions_for(atom, root, constrained, existing) else {
                continue;
            };
            if minted.is_empty() {
                continue;
            }
            let mut pool = base_pool.to_vec();
            let mut leaf_of = (*base_leaf_of).clone();
            for entry in &minted {
                if leaf_of
                    .insert(
                        entry.definition,
                        HypothesisLeaf::Definition {
                            rule: AletheRule::FreshDefEq,
                            args: vec![entry.definiendum],
                        },
                    )
                    .is_none()
                {
                    pool.push(entry.definition);
                }
            }
            if pool.len() > ay_proof::MAX_BRIDGE_CANDIDATES {
                continue;
            }
            let Some(fragment) = self.plan_minted_congruence_fragment(atom, root, &pool, &leaf_of)
            else {
                continue;
            };
            // Guard 8, re-asked at EMISSION time: every `fresh_def_eq` step the
            // fragment carries must be one the CHECKER's own recognizer admits
            // for exactly that `(clause, premises, args)` triple.
            if !fragment.iter().all(|step| match step {
                ProofStep::Step {
                    rule: AletheRule::FreshDefEq,
                    clause,
                    premises,
                    args,
                } => {
                    premises.is_empty()
                        && recognize_fresh_def_eq(&self.ctx.terms, clause, 0, args).is_ok()
                }
                _ => true,
            }) {
                continue;
            }
            // Guard: the fragment must actually WRITE a minted definition, or
            // this leaf belonged to the sibling lane and is not this one's.
            if !fragment.iter().any(|step| {
                matches!(
                    step,
                    ProofStep::Step {
                        rule: AletheRule::FreshDefEq,
                        clause,
                        ..
                    } if clause.first().is_some_and(|&c| {
                        minted.iter().any(|entry| entry.definition == c)
                    })
                )
            }) {
                continue;
            }
            if self.bridge_fragment_is_unrenderable(&fragment, atom, overrides) {
                continue;
            }
            return Some(fragment);
        }
        None
    }
}

/// The SYNTACTIC complement of `literal` — the term a resolution can actually
/// cancel it against. `mk_not` returns the De Morgan DUAL for an `and`/`or`
/// literal, which is Boolean-equivalent but not a resolution complement. Same
/// discipline as `ay_proof`'s own `close_congruence_derivation`.
pub(super) fn syntactic_complement(terms: &mut ay_core::TermStore, literal: TermId) -> TermId {
    let normalized = terms.mk_not(literal);
    let cancels = match terms.get(normalized) {
        TermData::Not(inner) => *inner == literal,
        _ => matches!(terms.get(literal), TermData::Not(inner) if *inner == normalized),
    };
    if cancels {
        normalized
    } else {
        terms.mk_not_raw(literal)
    }
}

/// Collect every symbol NAME reachable from `root`. Names, not `TermId`s: two
/// entries can share a name at different sorts, and the freshness question is
/// about the SYMBOL. Mirrors `ay_proof`'s own traversal.
pub(super) fn collect_symbol_names(
    terms: &ay_core::TermStore,
    root: TermId,
    names: &mut DetHashSet<String>,
    visited: &mut DetHashSet<TermId>,
) {
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }
        match terms.get(id) {
            TermData::Var(name, _) => {
                names.insert(name.clone());
            }
            TermData::App(sym, args) => {
                names.insert(sym.name().to_string());
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                for (name, value) in bindings {
                    names.insert(name.clone());
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                for (name, _) in vars {
                    names.insert(name.clone());
                }
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            _ => {}
        }
    }
}

#[cfg(test)]
#[path = "minted_definition_leaf_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "minted_definition_leaf_negative_tests.rs"]
mod negative_tests;

#[cfg(test)]
#[path = "minted_definition_leaf_guard_tests.rs"]
mod guard_tests;

#[cfg(test)]
#[path = "minted_definition_leaf_sweep_tests.rs"]
mod sweep_tests;
