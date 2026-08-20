// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-relative universal check for binders over BIT-BLASTABLE FINITE sorts
//! (`FloatingPoint`, `BitVec`, `Bool`).
//!
//! # The gap this closes
//!
//! `(not (exists ((d Float32)) ...))` is a universal over a 2^32-element
//! domain. Every existing lane declines it:
//!
//! * finite-domain expansion (`skolemize/finite_domain.rs`) caps at
//!   `MAX_FINITE_DOMAIN_COMBOS = 256` and admits only `BitVec(w <= 8)` / bounded
//!   `Int`;
//! * arithmetic CEGQI (`cegqi/mod.rs`) admits only `Int` / `Real` binders;
//! * BV-MBQI (`executor/bv_mbqi.rs`) shuts non-BV binders out of both its
//!   enumeration and its symbolic-entailment lane;
//! * E-matching produces no instances (these bodies carry no ground trigger).
//!
//! So the quantifier is marked unhandled and the ground `Sat` fails closed to
//! `Unknown(QuantifierUnhandled)`.
//!
//! # Why not just widen BV-MBQI's entailment lane to admit FP
//!
//! [`Executor::bv_symbolic_entailment_check`] proves `G |= forall x. body` by
//! refuting `G AND NOT body[skolem]`. That is a strictly stronger fact than
//! satisfiability needs, and it is MEASURABLY FALSE on this class: building
//! that obligation by hand for a 40-index sample of the declined queries and
//! handing it to an external solver returned SAT on every well-formed one. The
//! ground slice entails the universal in NONE of them, so widening the sort
//! gate there decides nothing.
//!
//! What is true of these queries is the weaker fact: SOME model of the ground
//! slice also satisfies the universal. This module establishes exactly that.
//!
//! # The check
//!
//! Pick a set `P` of ground formulas ("pins") — equalities fixing the free
//! finite-sorted symbols of the quantifier bodies to their values in the
//! current candidate model. For each quantifier node `Q` in the AUTHORED root
//! window, establish the truth value `Q` has in EVERY model of `P`, using only
//! CHECKED UNSAT results:
//!
//! ```text
//!   P AND NOT matrix[sk]  UNSAT  =>  matrix holds everywhere  =>  forall TRUE,  exists TRUE
//!   P AND     matrix[sk]  UNSAT  =>  matrix holds nowhere     =>  forall FALSE, exists FALSE
//!   P AND NOT matrix[v]   UNSAT  =>  matrix holds at v        =>  exists TRUE
//!   P AND     matrix[v]   UNSAT  =>  matrix fails at v        =>  forall FALSE
//! ```
//!
//! `sk` are FRESH constants; `v` is a concrete point offered by a probe and
//! then certified by the corresponding UNSAT. Replace each `Q` by that constant
//! to get a quantifier-free RESIDUAL of the authored roots, and require
//!
//! ```text
//!   residual AND P   checked SAT
//! ```
//!
//! ## Soundness
//!
//! Let `A |= residual AND P`. Fix a node `Q`. Because `A |= P` and the value
//! substituted for `Q` was established for every model of `P`, `Q` evaluates in
//! `A` to exactly that constant — so `A` satisfies the authored roots, which
//! differ from the residual only at those nodes. The problem is SATISFIABLE.
//!
//! Transporting a counterexample into the skolemized obligation needs the
//! binder's carrier to be FIXED and denoted by literals, which is why the
//! admitted binder sorts are `Bool` / `BitVec` / `FloatingPoint` only.
//!
//! ## Why POSITION does not matter
//!
//! Every conclusion above is read off an UNSAT, which is a statement about all
//! structures at once, so the substituted constant is `Q`'s value wherever `Q`
//! occurs. A quantifier under `not (and ...)` — a disjunctive position, where
//! asserting an instance is the #quant-alternation wrong-UNSAT — is handled by
//! the same argument as a top-level conjunct. Position is tracked (`refinable`)
//! for exactly one purpose: only a conjunctive-position universal may have a
//! counterexample instance ASSERTED to drive the next refinement round. That
//! flag is set ONLY from the shared
//! [`Executor::forall_ids_in_conjunctive_position`]; a local re-derivation of
//! it is what put a wrong-UNSAT in this file once already (see
//! [`authored_universal_leaves_impl`]).
//!
//! ## Pins: partial is sound for the ANSWER, total is required for the MODEL
//!
//! The documented hazard for a model-relative check is that a partially-pinned
//! model can be reported to satisfy a quantifier it does not — the failure mode
//! of checking by EVALUATION, where an unpinned symbol yields `Unknown` and the
//! check must guess. This check never evaluates: `P` enters only as a PREMISE
//! of UNSAT obligations, so dropping a pin makes those refutations HARDER to
//! obtain, never easier, and can only cost a decision.
//!
//! Totality is nevertheless REQUIRED, for the emitted model rather than the
//! answer. The structure the argument exhibits need not be `last_model` unless
//! the pins fix every symbol the bodies read; with total pins, `last_model` is
//! itself a model of `P` and therefore one of the structures covered, so a
//! `(get-model)` after one of these `sat`s is sound too.
//!
//! ## Why RoundingMode binders are excluded
//!
//! AY carries `RoundingMode` as `Sort::Uninterpreted("RoundingMode")`. The
//! argument above needs the binder's carrier to be fixed and literal-denoted;
//! an uninterpreted carrier is not, so an RM binder is refused rather than
//! reasoned about.
//!
//! # Refinement
//!
//! When a universal's value is left undetermined by these pins, the candidate
//! point from [`Executor::probe_finite_witness_values`] becomes the ground
//! instance `matrix[v_bar]`, which is asserted before re-solving so the next
//! round sees a different candidate model. `forall x_bar. matrix |=
//! matrix(v_bar)` for EVERY ground `v_bar`, so this direction carries no
//! authority requirement at all: a stale or wrong witness costs a round, never
//! a wrong answer. It is restricted to conjunctive-position universals, where
//! the instance really is a conjunct of the problem. A re-solve that goes UNSAT
//! is a sound refutation, exactly as in BV-MBQI.
//!
//! The restriction is load-bearing and it is exactly ONE direction: `forall x.
//! matrix` must be a CONSEQUENCE. A universal reached through a `not` — the
//! problem asserting `¬forall x. matrix` — entails no instance at all, so
//! asserting `matrix[v_bar]` there and refuting the result proves nothing
//! about the query. `#quant-alternation`.
//!
//! Reference: Ge & de Moura, "Complete Instantiation for Quantified Formulas
//! in SMT" (CAV 2009); the synth/verify split is the CEGIS loop Bitwuzla's
//! quantifier module runs over bit-blasted binders.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;

use super::model::EvalValue;
use super::quantifier_loop::result_mapping::CheckedGroundDecision;
use super::Executor;
use crate::ematching::{contains_quantifier, subst_vars};
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::LogicCategory;

/// Maximum synth/verify refinement rounds before failing closed.
///
/// Each round costs one counterexample probe per universal plus one ground
/// re-solve. The declined queries converge in a handful of rounds (the pinned
/// counterexample search excludes one model value per round and the satisfying
/// region of these invariants is large), so a small cap buys the decisions
/// without letting a pathological instance burn the query budget.
const MAX_FINITE_MODEL_ROUNDS: usize = 12;

/// Per-sub-solve budget in milliseconds.
///
/// Both obligations are quantifier-free and mostly ground: `verify_i` has one
/// free constant per binder and `confirm` is `G` under a near-total pin set.
/// A short budget keeps a hard instance from consuming the enclosing query.
const FINITE_MODEL_PROBE_MS: u64 = 2_000;

/// Cap on pins so a huge ground slice cannot blow up the sub-queries.
const MAX_PINS: usize = 256;

/// `--debug-cert` trace for this lane. Every decline reports WHICH step
/// declined, so a measured null is attributable instead of anonymous.
fn trace(message: impl FnOnce() -> String) {
    if ay_core::misc_cli_flags().debug_cert {
        ay_core::safe_eprintln!("FMQ {}", message());
    }
}

/// One universal obligation read off an AUTHORED quantified leaf.
///
/// The lane deliberately works on the authored root window rather than on the
/// rewritten `Forall`s the quantifier loop hands it. Those are the terms the
/// publication gates (`model/independent_gate.rs`) check, and a universal
/// authored as `(not (exists ...))` is rewritten to a structurally DIFFERENT
/// `Forall` term — binding authority to the rewritten node leaves the gate
/// unable to match it, and the certified `Sat` publishes as `unknown`. Reading
/// the obligation straight off the authored term also removes any dependence on
/// the rewrite being faithful.
struct AuthoredUniversal {
    /// The quantifier node as it occurs in the authored root window: the
    /// `Forall` itself, or the `Exists` under the negation.
    node: TermId,
    vars: Vec<(String, Sort)>,
    /// The quantifier's body as authored.
    body: TermId,
    /// True when the leaf sits under a `not`, so the matrix is `not body`
    /// rather than `body`. Applying the negation needs `&mut TermStore`, so it
    /// is deferred to the caller and the classifier stays a pure read.
    negate_body: bool,
    /// True for `forall x. matrix`, false for `exists x. matrix`.
    universal: bool,
    /// True when this node is a `Forall` that really is a top-level CONJUNCT
    /// of an authored root — i.e. `forall x. body` is a CONSEQUENCE of the
    /// problem, so every ground instance `body[v]` is one too.
    ///
    /// Only then may a counterexample instance be asserted for refinement: an
    /// instance of a universal sitting in a disjunctive position — or under a
    /// `not`, where the problem asserts `¬forall x. body` and `body[v]` is
    /// emphatically NOT entailed — is not a consequence of the problem, and
    /// asserting one is the #quant-alternation wrong-UNSAT. Truth-value
    /// determination below needs no such guard: it substitutes a constant the
    /// pins already force, which is position-independent.
    ///
    /// Set ONLY from [`Executor::forall_ids_in_conjunctive_position`]; see
    /// [`authored_universal_leaves_impl`] for why a local walk got this wrong.
    refinable: bool,
}

/// What the pins force one quantifier's truth value to be.
enum TruthOutcome {
    /// Checked-UNSAT evidence fixes this value in EVERY model of the pins, so
    /// the constant may replace the quantifier wherever it occurs.
    Determined(bool),
    /// Not fixed by these pins; this ground instance of a conjunctive-position
    /// universal is offered to drive the next refinement round.
    Refine(TermId),
    /// Undecided — the caller must fail closed.
    Unknown,
}

/// Sorts whose carrier is fixed and exactly the set of their literal values, so
/// a fresh skolem constant of that sort ranges over precisely the binder's
/// domain and the counterexample argument above goes through.
fn is_pinnable_finite_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_) | Sort::FloatingPoint(..))
}

/// A universal this lane can attempt: every binder over a fixed finite carrier,
/// at least one of them a `FloatingPoint` binder, and a quantifier-free body.
///
/// The FP requirement keeps the blast radius on the class this lane exists for.
/// BV-only universals keep going to `bv_mbqi`, whose enumeration and
/// entailment behaviour is separately measured across the bitvector divisions;
/// this lane must not silently change those.
fn is_finite_model_candidate(terms: &TermStore, quant: TermId) -> bool {
    let TermData::Forall(vars, body, _) = terms.get(quant) else {
        return false;
    };
    !vars.is_empty()
        && vars.iter().all(|(_, sort)| is_pinnable_finite_sort(sort))
        && vars
            .iter()
            .any(|(_, sort)| matches!(sort, Sort::FloatingPoint(..)))
        && !contains_quantifier(terms, *body)
}

/// Read EVERY quantifier node of the authored root window, wherever it sits, or
/// fail closed.
///
/// Position does not matter here, and that is the point. The pass below fixes
/// each quantifier's truth value under the pins and substitutes a Boolean
/// CONSTANT for it, so a quantifier under a `not (and ...)` — a disjunctive
/// position, where instantiation is famously unsound — is handled by exactly
/// the same argument as a top-level conjunct. What position DOES control is
/// whether counterexample instances may be asserted for refinement; that is
/// recorded per node in `refinable` and enforced separately.
///
/// `None` means some quantifier is not one this lane can discharge (non-finite
/// binder, no FP binder, or a nested quantifier). Returning `None` there is what
/// keeps the authority honest: the token asserts that EVERY quantified
/// obligation in the window was discharged.
///
/// # `refinable`, and the wrong-UNSAT that lived here
///
/// `refinable` is decided by the SHARED
/// [`Executor::forall_ids_in_conjunctive_position`] rather than a local walk.
/// The local walk this replaced was the wrong-UNSAT: it matched
/// `Not(Forall | Exists)` and marked the INNER node conjunctive, so the bare
/// `Forall` of a top-level `(not (forall x. b))` — which
/// `classify_authored_universal` then reads as a positive universal, the
/// enclosing `not` being invisible to it — came back `refinable`, and `b[v]`
/// got asserted and refuted as if it were a consequence. It is not one.
///
/// The shared helper cannot make that mistake: it NNF-converts `Not(Forall)`
/// to a freshly built `Exists`, so the raw `Forall` id is never in its set.
/// It is also strictly more accurate than the local walk on the cases both
/// handle — De Morgan, double negation, `Not(=>)`, and the `#unit-conjunctive`
/// modulo-units refinement — and it is the predicate the rest of the engine's
/// alternation guards already share.
fn authored_universal_leaves_impl(
    executor: &mut Executor,
    roots: &[TermId],
) -> Option<Vec<AuthoredUniversal>> {
    let nodes = super::bv_mbqi::quantifier_nodes_in(&executor.ctx.terms, roots);
    if nodes.is_empty() {
        return None;
    }
    // Quantifier nodes that really are top-level CONJUNCTS of the authored
    // window, and so the only ones an asserted instance may refine.
    let refinable = executor.forall_ids_in_conjunctive_position(roots);
    let mut sorted: Vec<TermId> = nodes.into_iter().collect();
    sorted.sort_unstable();
    let mut leaves: Vec<AuthoredUniversal> = Vec::with_capacity(sorted.len());
    for node in sorted {
        let mut leaf = classify_authored_universal(&executor.ctx.terms, node)?;
        // Belt and braces: `refinable` may only ever be true for a node that
        // IS a `Forall` and IS in the shared conjunctive set. `Refine` is only
        // produced on the `universal` branch, so anything else being marked
        // refinable is dead at best and a wrong-UNSAT at worst.
        leaf.refinable = leaf.universal
            && matches!(executor.ctx.terms.get(node), TermData::Forall(..))
            && refinable.contains(&node);
        leaves.push(leaf);
    }
    // Census, so "which branch did the measured number come from" is a
    // READING rather than an inference. The universal branch and the
    // refinement loop are reached only by `universal`/`refinable` leaves; if
    // those stay 0 across a corpus, every decision on it came from the
    // existential path and the universal path is unmeasured.
    trace(|| {
        let universal = leaves.iter().filter(|l| l.universal).count();
        let refinable = leaves.iter().filter(|l| l.refinable).count();
        format!(
            "leaf-census: total={} universal={universal} refinable={refinable}",
            leaves.len()
        )
    });
    Some(leaves)
}

/// Classify one quantified leaf, or `None`.
///
/// All four polarity/quantifier combinations reduce to `Q x_bar. matrix`, where
/// `matrix` is the body or its negation:
///
/// ```text
///   forall x. b        universal,   matrix = b
///   not (exists x. b)  universal,   matrix = not b
///   exists x. b        existential, matrix = b
///   not (forall x. b)  existential, matrix = not b
/// ```
///
/// `node` is always the quantifier term itself, since that — not the enclosing
/// `not` — is what the root-window coverage check walks to.
///
/// Called on a bare quantifier node, so only the two unnegated rows apply; the
/// negated spellings are kept because the enclosing `not` is what the authored
/// text carries and the table is the contract this file reasons against.
fn classify_authored_universal(terms: &TermStore, leaf: TermId) -> Option<AuthoredUniversal> {
    let (node, vars, body, negate_body, universal) = match terms.get(leaf) {
        TermData::Forall(vars, body, _) => (leaf, vars.clone(), *body, false, true),
        TermData::Exists(vars, body, _) => (leaf, vars.clone(), *body, false, false),
        TermData::Not(inner) => match terms.get(*inner) {
            TermData::Exists(vars, body, _) => (*inner, vars.clone(), *body, true, true),
            TermData::Forall(vars, body, _) => (*inner, vars.clone(), *body, true, false),
            _ => return None,
        },
        _ => return None,
    };
    if vars.is_empty()
        || !vars.iter().all(|(_, sort)| is_pinnable_finite_sort(sort))
        || !vars
            .iter()
            .any(|(_, sort)| matches!(sort, Sort::FloatingPoint(..)))
        || contains_quantifier(terms, body)
    {
        return None;
    }
    Some(AuthoredUniversal {
        node,
        vars,
        body,
        negate_body,
        universal,
        refinable: false,
    })
}

/// Split `quants` into the ones this lane handles and the rest.
pub(in crate::executor) fn partition_finite_model_quantifiers(
    terms: &TermStore,
    quants: &[TermId],
) -> (Vec<TermId>, Vec<TermId>) {
    quants
        .iter()
        .copied()
        .partition(|&quant| is_finite_model_candidate(terms, quant))
}

/// Rebuild `term` with every key of `map` replaced by its value.
///
/// Used to splice the pin-determined Boolean constants in place of the
/// quantifier nodes, leaving a fully ground residual formula.
fn replace_subterms(
    terms: &mut TermStore,
    term: TermId,
    map: &HashMap<TermId, TermId>,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&replacement) = map.get(&term) {
        return replacement;
    }
    if let Some(&cached) = memo.get(&term) {
        return cached;
    }
    let rebuilt = match terms.get(term).clone() {
        TermData::App(sym, args) => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&arg| replace_subterms(terms, arg, map, memo))
                .collect();
            if new_args == args {
                term
            } else {
                let sort = terms.sort(term).clone();
                terms.mk_app(sym, new_args, sort)
            }
        }
        TermData::Not(inner) => {
            let new_inner = replace_subterms(terms, inner, map, memo);
            if new_inner == inner {
                term
            } else {
                terms.mk_not(new_inner)
            }
        }
        TermData::Ite(condition, then_term, else_term) => {
            let c = replace_subterms(terms, condition, map, memo);
            let t = replace_subterms(terms, then_term, map, memo);
            let e = replace_subterms(terms, else_term, map, memo);
            if (c, t, e) == (condition, then_term, else_term) {
                term
            } else {
                terms.mk_ite(c, t, e)
            }
        }
        // Quantifier nodes are all in `map` (the caller classified every one),
        // and a `Let` is expanded long before this point. Anything else is a
        // leaf. Returning `term` unchanged is safe in every case: an unreplaced
        // quantifier would leave the residual quantified, and the residual is
        // handed to `checked_ground_solve`, which REFUSES a quantified vector.
        _ => term,
    };
    memo.insert(term, rebuilt);
    rebuilt
}

/// Rebuild a concrete `EvalValue` as a term in `terms`.
///
/// Restricted to the fixed-carrier sorts this lane admits; anything else fails
/// closed so no symbolic residue can masquerade as a literal.
fn finite_value_term(terms: &mut TermStore, sort: &Sort, value: &EvalValue) -> Option<TermId> {
    match (sort, value) {
        (Sort::Bool, EvalValue::Bool(v)) => Some(terms.mk_bool(*v)),
        (Sort::BitVec(bv), EvalValue::BitVec { value, width }) if *width == bv.width => {
            Some(terms.mk_bitvec(value.clone(), *width))
        }
        (Sort::FloatingPoint(eb, sb), EvalValue::Fp(fp)) if fp.eb() == *eb && fp.sb() == *sb => {
            Some(fp_value_term(terms, fp))
        }
        _ => None,
    }
}

/// Rebuild an [`ay_fp::FpModelValue`] as its SMT-LIB literal term.
///
/// Mirrors `model/eval_fp.rs::clone_fp_value_term`; kept here as a free
/// function so it can write into `self.ctx.terms` while the executor is
/// mutably borrowed.
fn fp_value_term(terms: &mut TermStore, value: &ay_fp::FpModelValue) -> TermId {
    use num_traits::One;

    let (eb, sb) = (value.eb(), value.sb());
    let sort = Sort::FloatingPoint(eb, sb);
    let nullary = |terms: &mut TermStore, name: &str| {
        terms.mk_app(Symbol::indexed(name, vec![eb, sb]), vec![], sort.clone())
    };
    match value {
        ay_fp::FpModelValue::PosZero { .. } => nullary(terms, "+zero"),
        ay_fp::FpModelValue::NegZero { .. } => nullary(terms, "-zero"),
        ay_fp::FpModelValue::PosInf { .. } => nullary(terms, "+oo"),
        ay_fp::FpModelValue::NegInf { .. } => nullary(terms, "-oo"),
        ay_fp::FpModelValue::NaN { .. } => nullary(terms, "NaN"),
        ay_fp::FpModelValue::Fp { .. } => {
            let (bits, _) = value.to_ieee_bv();
            let sig_width = sb - 1;
            let sign = (&bits >> (eb + sig_width)) & BigInt::one();
            let exp_mask = (BigInt::one() << eb) - BigInt::one();
            let sig_mask = (BigInt::one() << sig_width) - BigInt::one();
            let exponent = (&bits >> sig_width) & exp_mask;
            let significand = bits & sig_mask;
            let sign_term = terms.mk_bitvec(sign, 1);
            let exp_term = terms.mk_bitvec(exponent, eb);
            let sig_term = terms.mk_bitvec(significand, sig_width);
            terms.mk_app(
                Symbol::named("fp"),
                vec![sign_term, exp_term, sig_term],
                sort,
            )
        }
    }
}

/// Collect the FREE finite-sorted `Var` leaves of `term`.
///
/// `bound` holds the binder names of the enclosing quantifiers. AY represents a
/// bound variable as an ordinary `TermData::Var` (substitution is by name), so
/// without this filter the binder itself is collected as a pin target, has no
/// model value, and the totality check fails on every single query.
fn collect_finite_var_leaves(
    terms: &TermStore,
    term: TermId,
    bound: &HashSet<String>,
    out: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
) {
    if !seen.insert(term) {
        return;
    }
    match terms.get(term) {
        TermData::Var(name, _) => {
            if !bound.contains(name) && is_pinnable_finite_sort(terms.sort(term)) {
                out.push(term);
            }
        }
        TermData::App(_, args) => {
            for &arg in args {
                collect_finite_var_leaves(terms, arg, bound, out, seen);
            }
        }
        TermData::Not(inner) => collect_finite_var_leaves(terms, *inner, bound, out, seen),
        TermData::Ite(condition, then_term, else_term) => {
            for sub in [*condition, *then_term, *else_term] {
                collect_finite_var_leaves(terms, sub, bound, out, seen);
            }
        }
        TermData::Let(bindings, body) => {
            let (bindings, body) = (bindings.clone(), *body);
            for (_, value) in &bindings {
                collect_finite_var_leaves(terms, *value, bound, out, seen);
            }
            collect_finite_var_leaves(terms, body, bound, out, seen);
        }
        // A nested quantifier cannot appear (candidates have QF bodies), and a
        // constant leaf needs no pin. Any future `TermData` variant is skipped
        // too: a missed pin only WEAKENS the obligation (module note), so
        // failing to descend is conservative rather than unsound.
        _ => {}
    }
}

impl Executor {
    /// Quantifier-free slice of the current assertions — the premise `G`.
    fn finite_model_ground_slice(&self) -> Vec<TermId> {
        self.ctx
            .assertions
            .iter()
            .copied()
            .filter(|&assertion| !contains_quantifier(&self.ctx.terms, assertion))
            .collect()
    }

    /// Ground equalities pinning the free finite-sorted symbols of `bodies` to
    /// their values in the current candidate model, plus whether EVERY such
    /// symbol was pinned.
    ///
    /// The answer this lane publishes is sound under a partial pin set (module
    /// note), but the EMITTED MODEL is not: the structure the proof exhibits
    /// need not be `last_model` unless the pins fix every symbol the leaf
    /// bodies read. Totality is therefore required by the caller, so that
    /// `last_model` — which is a model of its own pins by construction — is
    /// itself one of the structures the proof covers.
    fn finite_model_pins(&mut self, leaves_of: &[AuthoredUniversal]) -> (Vec<TermId>, bool) {
        let Some(model) = self.last_model.clone() else {
            return (Vec::new(), false);
        };
        let bound: HashSet<String> = leaves_of
            .iter()
            .flat_map(|leaf| leaf.vars.iter().map(|(name, _)| name.clone()))
            .collect();
        let mut leaves: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for leaf in leaves_of {
            collect_finite_var_leaves(&self.ctx.terms, leaf.body, &bound, &mut leaves, &mut seen);
        }
        leaves.sort_unstable();
        leaves.dedup();
        if leaves.len() > MAX_PINS {
            return (Vec::new(), false);
        }

        let mut pins: Vec<TermId> = Vec::new();
        let mut total = true;
        for leaf in leaves {
            let sort = self.ctx.terms.sort(leaf).clone();
            let value = self.evaluate_term(&model, leaf);
            if let Some(value_term) = finite_value_term(&mut self.ctx.terms, &sort, &value) {
                let pin = self.ctx.terms.mk_eq(leaf, value_term);
                pins.push(pin);
            } else {
                total = false;
            }
        }
        (pins, total)
    }

    /// `matrix[x_bar := fresh skolems]` for one leaf, with the skolems.
    ///
    /// Skolemization of a conjunctive-position `exists` is an EQUISATISFIABILITY
    /// (the constants are fresh), so a checked SAT of the ground slice extended
    /// with this term decides the existential exactly — no pins, no domain
    /// enumeration, no model evaluation.
    fn finite_model_skolemize(&mut self, leaf: &AuthoredUniversal) -> (TermId, Vec<TermId>) {
        let mut subst: HashMap<String, TermId> = HashMap::default();
        let mut skolems: Vec<TermId> = Vec::with_capacity(leaf.vars.len());
        for (name, sort) in &leaf.vars {
            let fresh = self
                .ctx
                .terms
                .mk_fresh_var(&format!("fmq!{name}"), sort.clone());
            subst.insert(name.clone(), fresh);
            skolems.push(fresh);
        }
        let body = subst_vars(&mut self.ctx.terms, leaf.body, &subst);
        let matrix = if leaf.negate_body {
            self.ctx.terms.mk_not(body)
        } else {
            body
        };
        (matrix, skolems)
    }

    /// Is `assertions` checked-UNSAT?
    fn finite_model_refutes(&mut self, assertions: Vec<TermId>) -> bool {
        self.checked_ground_solve(
            assertions.clone(),
            LogicCategory::Other,
            FINITE_MODEL_PROBE_MS,
        )
        .is_some_and(|decision| match decision {
            CheckedGroundDecision::Unsat(checked) => checked.consume(self, &assertions),
            CheckedGroundDecision::Sat(_) => false,
        })
    }

    /// `matrix[x_bar := v_bar]` for the concrete values `values`.
    fn finite_model_instance_at(
        &mut self,
        leaf: &AuthoredUniversal,
        values: &[EvalValue],
    ) -> Option<TermId> {
        if values.len() != leaf.vars.len() {
            return None;
        }
        let mut binding: Vec<TermId> = Vec::with_capacity(leaf.vars.len());
        for ((_, sort), value) in leaf.vars.iter().zip(values) {
            binding.push(finite_value_term(&mut self.ctx.terms, sort, value)?);
        }
        let subst: HashMap<String, TermId> = leaf
            .vars
            .iter()
            .map(|(name, _)| name.clone())
            .zip(binding)
            .collect();
        let body = subst_vars(&mut self.ctx.terms, leaf.body, &subst);
        Some(if leaf.negate_body {
            self.ctx.terms.mk_not(body)
        } else {
            body
        })
    }

    /// The truth value this quantifier has in EVERY model of `pins`.
    ///
    /// Every conclusion below is read off a checked UNSAT, which is a statement
    /// about all structures at once — never off a SAT or off evaluating the
    /// model. That is what makes the value substitutable at ANY position,
    /// including a disjunctive one where instantiation would be unsound.
    ///
    /// * `pins AND NOT matrix[sk]` UNSAT — matrix holds at every point, in
    ///   every model of the pins: `forall` TRUE, and `exists` TRUE too.
    /// * `pins AND matrix[sk]` UNSAT — matrix holds nowhere: both FALSE.
    /// * otherwise a single point decides it. Take a concrete `v` from a probe
    ///   (no authority needed — it is only a candidate) and CERTIFY it:
    ///   `pins AND NOT matrix[v]` UNSAT makes `exists` TRUE, `pins AND
    ///   matrix[v]` UNSAT makes `forall` FALSE.
    fn finite_model_truth_value(
        &mut self,
        leaf: &AuthoredUniversal,
        pins: &[TermId],
    ) -> TruthOutcome {
        let (matrix_sk, skolems) = self.finite_model_skolemize(leaf);
        let negated = self.ctx.terms.mk_not(matrix_sk);

        let with = |pins: &[TermId], extra: TermId| {
            let mut v: Vec<TermId> = Vec::with_capacity(pins.len() + 1);
            v.extend_from_slice(pins);
            v.push(extra);
            v
        };

        if leaf.universal {
            if self.finite_model_refutes(with(pins, negated)) {
                return TruthOutcome::Determined(true);
            }
            // A counterexample point exists somewhere. Pin one down and certify
            // that it falsifies the matrix in every model of the pins.
            let Some(values) = self.probe_finite_witness_values(
                with(pins, negated),
                &skolems,
                FINITE_MODEL_PROBE_MS,
            ) else {
                return TruthOutcome::Unknown;
            };
            let Some(instance) = self.finite_model_instance_at(leaf, &values) else {
                return TruthOutcome::Unknown;
            };
            if self.finite_model_refutes(with(pins, instance)) {
                return TruthOutcome::Determined(false);
            }
            // Undetermined under these pins: offer the instance for refinement.
            TruthOutcome::Refine(instance)
        } else {
            let Some(values) = self.probe_finite_witness_values(
                with(pins, matrix_sk),
                &skolems,
                FINITE_MODEL_PROBE_MS,
            ) else {
                // No witness point at all under the pins — if that is CERTIFIED,
                // the existential is false in every model of them.
                return if self.finite_model_refutes(with(pins, matrix_sk)) {
                    TruthOutcome::Determined(false)
                } else {
                    TruthOutcome::Unknown
                };
            };
            let Some(instance) = self.finite_model_instance_at(leaf, &values) else {
                return TruthOutcome::Unknown;
            };
            let negated_instance = self.ctx.terms.mk_not(instance);
            if self.finite_model_refutes(with(pins, negated_instance)) {
                TruthOutcome::Determined(true)
            } else {
                TruthOutcome::Unknown
            }
        }
    }

    /// ONE certificate pass over the authored leaves, with no state mutation.
    ///
    /// `Some(true)` installs nothing but reports that the pass certified the
    /// window (the caller mints and installs). `Some(false)` means the pass
    /// found counterexample instances, returned in `instances`. `None` is a
    /// decline.
    fn finite_model_certificate_pass(
        &mut self,
        round: usize,
        roots: &[TermId],
        universals: &[AuthoredUniversal],
        instances: &mut Vec<TermId>,
    ) -> Option<bool> {
        // ONE pin set shared by every leaf in the pass. Per-leaf pin sets
        // would fix each truth value in a DIFFERENT structure, and the residual
        // formula below needs them all true in the SAME one.
        let (pins, pins_total) = self.finite_model_pins(universals);
        trace(|| {
            format!(
                "round {round}: pins={} total={pins_total} model={}",
                pins.len(),
                self.last_model.is_some()
            )
        });
        if !pins_total {
            trace(|| format!("round {round}: pin set not total"));
            return None;
        }

        let mut values: HashMap<TermId, TermId> = HashMap::default();
        let mut refined = false;
        for leaf in universals {
            match self.finite_model_truth_value(leaf, &pins) {
                TruthOutcome::Determined(value) => {
                    let constant = self.ctx.terms.mk_bool(value);
                    values.insert(leaf.node, constant);
                }
                TruthOutcome::Refine(instance) => {
                    // An instance may only be ASSERTED for a universal that is a
                    // top-level conjunct; anywhere else it is not a consequence
                    // of the problem (#quant-alternation wrong-UNSAT).
                    if !leaf.refinable {
                        trace(|| format!("round {round}: undetermined non-conjunctive quantifier"));
                        return None;
                    }
                    instances.push(instance);
                    refined = true;
                }
                TruthOutcome::Unknown => {
                    trace(|| format!("round {round}: truth value undetermined"));
                    return None;
                }
            }
        }
        if refined {
            return Some(false);
        }

        // RESIDUAL: the authored roots with every quantifier replaced by the
        // constant the pins force it to. Any structure satisfying the residual
        // AND the pins satisfies the authored roots themselves, because on that
        // structure each replaced node evaluates to exactly its constant.
        //
        // Note this uses the AUTHORED roots, not the preprocessed ground slice,
        // so the conclusion is about the problem as written.
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        let mut confirm: Vec<TermId> = roots
            .iter()
            .map(|&root| replace_subterms(&mut self.ctx.terms, root, &values, &mut memo))
            .collect();
        confirm.extend_from_slice(&pins);
        let confirmed = self
            .checked_ground_solve(confirm.clone(), LogicCategory::Other, FINITE_MODEL_PROBE_MS)
            .is_some_and(|decision| match decision {
                CheckedGroundDecision::Sat(checked) => checked.consume(self, &confirm),
                CheckedGroundDecision::Unsat(_) => false,
            });
        trace(|| format!("round {round}: all determined; confirm={confirmed}"));
        confirmed.then_some(true)
    }

    /// Establish and INSTALL finite-sort quantified SAT authority for the
    /// current authored root window, in a single non-mutating pass.
    ///
    /// This is the hook for the shape the MBQI lane never sees: a positive,
    /// conjunctive-position `exists` over FP binders. The quantifier loop
    /// Skolemizes it, so it is neither uninstantiated nor unhandled and
    /// `try_mbqi_refinement` is never called — the ground `Sat` goes straight to
    /// the publication gates, which cannot evaluate the existential against a
    /// partially-pinned model and fail closed to `unknown`.
    ///
    /// Adds NO assertions and runs NO outer re-solve, so it is safe to call
    /// from inside the emission funnel.
    pub(in crate::executor) fn try_finite_model_sat_certificate(&mut self) -> bool {
        if self.should_abort_theory_loop() {
            return false;
        }
        let authority_roots = self.independent_gate_query_roots();
        let Some(universals) = authored_universal_leaves_impl(self, &authority_roots) else {
            return false;
        };
        let certified_nodes: Vec<TermId> = universals.iter().map(|u| u.node).collect();
        trace(|| {
            format!(
                "gate-hook: authored={} roots={:?}",
                universals.len(),
                authority_roots
            )
        });
        let mut instances = Vec::new();
        if self.finite_model_certificate_pass(0, &authority_roots, &universals, &mut instances)
            != Some(true)
        {
            return false;
        }
        let Some(evidence) = super::bv_mbqi::checked_full_domain_sat_authority(
            self,
            &authority_roots,
            &certified_nodes,
        ) else {
            trace(|| "gate-hook: authority roots do not cover".to_string());
            return false;
        };
        let installed = self.install_bv_full_domain_sat_authority(evidence);
        self.bv_quantifier_full_domain_proof = installed;
        trace(|| format!("gate-hook: installed={installed}"));
        installed
    }

    /// Model-relative refinement lane for finite-sort (FP-bearing) universals.
    ///
    /// `trigger_quants` are the rewritten `forall`s the quantifier loop left
    /// unhandled; they only decide WHETHER to engage. The obligations
    /// themselves are read off the AUTHORED root window, which is what the
    /// publication gates check and what the resulting authority is bound to.
    pub(in crate::executor) fn try_finite_model_forall_refinement(
        &mut self,
        trigger_quants: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        if trigger_quants.is_empty() {
            return None;
        }
        let authority_roots = self.independent_gate_query_roots();
        let Some(universals) = authored_universal_leaves_impl(self, &authority_roots) else {
            trace(|| "authored leaves not all finite-sort universals".to_string());
            return None;
        };
        trace(|| {
            format!(
                "enter triggers={} authored={} roots={:?}",
                trigger_quants.len(),
                universals.len(),
                authority_roots
            )
        });
        // Any Sat this lane's caller might otherwise inherit is a sample until
        // this pass proves otherwise.
        self.revoke_bv_full_domain_sat_authority();

        let certified_nodes: Vec<TermId> = universals.iter().map(|u| u.node).collect();

        for round in 0..MAX_FINITE_MODEL_ROUNDS {
            if self.should_abort_theory_loop() {
                trace(|| format!("round {round}: abort requested"));
                return None;
            }

            let mut new_instances: Vec<TermId> = Vec::new();
            match self.finite_model_certificate_pass(
                round,
                &authority_roots,
                &universals,
                &mut new_instances,
            ) {
                None => return None,
                Some(true) => {
                    let evidence = super::bv_mbqi::checked_full_domain_sat_authority(
                        self,
                        &authority_roots,
                        &certified_nodes,
                    );
                    if evidence.is_none() {
                        trace(|| format!("round {round}: authority roots do not cover"));
                        return None;
                    }
                    self.bv_quantifier_full_domain_proof = true;
                    self.bv_quantifier_full_domain_pending_evidence = evidence;
                    return Some(Ok(SolveResult::Sat));
                }
                Some(false) => {}
            }

            trace(|| format!("round {round}: {} new instance(s)", new_instances.len()));
            if new_instances.is_empty() {
                return None;
            }
            for instance in &new_instances {
                self.ctx.assertions.push(*instance);
            }
            let (detected_category, _) = self.detect_logic_category(&self.ctx.assertions);
            let re_category = if matches!(detected_category, LogicCategory::Other) {
                category
            } else {
                detected_category
            };
            match self.solve_for_category(re_category) {
                Ok(SolveResult::Sat) => {}
                Ok(SolveResult::Unsat(_)) => return Some(Ok(SolveResult::unsat())),
                other => return Some(other),
            }
        }
        None
    }
}

/// The `refinable` contract, driven DIRECTLY.
///
/// These tests do not go through the CLI on purpose. An authored assertion
/// containing a literal FP `forall` sets `has_unsafe_partial_quantifiers`
/// (`quantifier_loop/mod.rs`) and fails closed at `result_mapping.rs` BEFORE
/// this lane runs, so every end-to-end attempt at the wrong-UNSAT below comes
/// back `unknown` and proves nothing about this code. The defect is one
/// unrelated upstream guard away from firing, which is why the contract is
/// pinned here at the classifier instead.
#[cfg(test)]
mod refinable_contract_tests {
    use super::*;

    /// Float32 — an FP binder, which is what admits a leaf to this lane.
    fn f32_sort() -> Sort {
        Sort::FloatingPoint(8, 24)
    }

    /// A ground Bool atom to sit beside the quantifier in a root.
    fn atom(terms: &mut TermStore, name: &str) -> TermId {
        terms.mk_app(Symbol::named(name), [], Sort::Bool)
    }

    /// `forall x:Float32. P(x)`.
    ///
    /// The body is an uninterpreted `P : Float32 -> Bool`: admission reads the
    /// BINDER sorts, so this keeps the fixture off the FP term builders while
    /// still landing in the lane.
    fn forall_p(terms: &mut TermStore) -> TermId {
        let x = terms.mk_var("x", f32_sort());
        let body = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
        terms.mk_forall(vec![("x".to_string(), f32_sort())], body)
    }

    /// `exists x:Float32. P(x)`.
    fn exists_p(terms: &mut TermStore) -> TermId {
        let x = terms.mk_var("x", f32_sort());
        let body = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
        terms.mk_exists(vec![("x".to_string(), f32_sort())], body)
    }

    /// Classify `roots` and return `(universal, refinable)` for `node`.
    fn leaf_flags(executor: &mut Executor, roots: &[TermId], node: TermId) -> (bool, bool) {
        let leaves = authored_universal_leaves_impl(executor, roots)
            .expect("fixture leaves are all FP-binder finite quantifiers");
        let leaf = leaves
            .iter()
            .find(|leaf| leaf.node == node)
            .expect("the fixture's quantifier node is classified");
        (leaf.universal, leaf.refinable)
    }

    /// THE WRONG-UNSAT, pinned.
    ///
    /// The problem asserts `NOT forall x. P(x)`. That entails NO instance of
    /// `P` whatsoever — `P(v)` is not a consequence for any `v`. If this leaf
    /// comes back refinable, `finite_model_certificate_pass` takes the
    /// `TruthOutcome::Refine` arm, `try_finite_model_refinement` pushes
    /// `P(v)` onto `ctx.assertions`, and a re-solve that goes UNSAT is
    /// published as a definite `Unsat` of a query it does not refute.
    ///
    /// FAILS on the pre-fix lane: the local conjunct walk matched
    /// `Not(Forall | Exists)` and inserted the INNER node, marking exactly
    /// this `Forall` conjunctive.
    #[test]
    fn negated_universal_is_never_refinable() {
        let mut executor = Executor::new();
        let forall = forall_p(&mut executor.ctx.terms);
        let root = executor.ctx.terms.mk_not(forall);
        assert!(
            matches!(executor.ctx.terms.get(root), TermData::Not(inner) if *inner == forall),
            "fixture must stay a literal Not(Forall); mk_not folded it instead"
        );

        let (universal, refinable) = leaf_flags(&mut executor, &[root], forall);
        assert!(
            universal,
            "the bare Forall node still classifies as a universal — that is the trap"
        );
        assert!(
            !refinable,
            "#quant-alternation: an instance of a universal under a `not` is not a \
             consequence and must never be asserted"
        );
    }

    /// The same defect through the shape it actually reaches: De Morgan turns
    /// `not (or (forall ...) b)` into `and (not (forall ...)) (not b)`, so the
    /// negated universal arrives as a top-level CONJUNCT. Still not a
    /// consequence.
    ///
    /// FAILS on the pre-fix lane for the same reason.
    #[test]
    fn negated_universal_inside_a_conjunction_is_never_refinable() {
        let mut executor = Executor::new();
        let forall = forall_p(&mut executor.ctx.terms);
        let b = atom(&mut executor.ctx.terms, "b");
        let disjunction = executor.ctx.terms.mk_or(vec![forall, b]);
        let root = executor.ctx.terms.mk_not(disjunction);

        let (_, refinable) = leaf_flags(&mut executor, &[root], forall);
        assert!(
            !refinable,
            "a negated universal is not a consequence however it is spelled"
        );
    }

    /// POSITIVE CONTROL. Without this the fix could be "return false always",
    /// which is sound and useless — it would silently delete the refinement
    /// loop the lane's measured decisions depend on.
    #[test]
    fn top_level_universal_is_refinable() {
        let mut executor = Executor::new();
        let forall = forall_p(&mut executor.ctx.terms);

        let (universal, refinable) = leaf_flags(&mut executor, &[forall], forall);
        assert!(universal);
        assert!(
            refinable,
            "a top-level `forall` IS a consequence; its instances are sound to assert"
        );
    }

    /// POSITIVE CONTROL, one level in.
    #[test]
    fn universal_conjunct_is_refinable() {
        let mut executor = Executor::new();
        let forall = forall_p(&mut executor.ctx.terms);
        let b = atom(&mut executor.ctx.terms, "b");
        let root = executor.ctx.terms.mk_and(vec![forall, b]);

        let (_, refinable) = leaf_flags(&mut executor, &[root], forall);
        assert!(refinable, "a top-level conjunct is a consequence");
    }

    /// A universal in a DISJUNCTIVE position is not a consequence either.
    #[test]
    fn disjunctive_universal_is_not_refinable() {
        let mut executor = Executor::new();
        let forall = forall_p(&mut executor.ctx.terms);
        let b = atom(&mut executor.ctx.terms, "b");
        let root = executor.ctx.terms.mk_or(vec![forall, b]);

        let (_, refinable) = leaf_flags(&mut executor, &[root], forall);
        assert!(
            !refinable,
            "#quant-alternation: a disjunct is not a conjunct"
        );
    }

    /// Existential leaves never take the `Refine` arm at all — it is produced
    /// only on the `universal` branch — so they must never be marked
    /// refinable, in either polarity. `(not (exists ...))` is the shape the
    /// entire measured +713 is made of.
    #[test]
    fn existential_leaves_are_never_refinable() {
        for negated in [false, true] {
            let mut executor = Executor::new();
            let exists = exists_p(&mut executor.ctx.terms);
            let root = if negated {
                executor.ctx.terms.mk_not(exists)
            } else {
                exists
            };

            let (universal, refinable) = leaf_flags(&mut executor, &[root], exists);
            assert!(!universal, "a bare Exists node is not a universal leaf");
            assert!(!refinable, "negated={negated}");
        }
    }
}
