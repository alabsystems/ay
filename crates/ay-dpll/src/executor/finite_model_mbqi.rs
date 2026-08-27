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
//! The EMITTED MODEL is a separate obligation, and it is DISCHARGED BY CHECKING
//! rather than by an argument about totality. `last_model` satisfies the ground
//! ABSTRACTION, in which every quantifier node is an unconstrained Boolean, so
//! even a totally-pinned `last_model` may assign a node the opposite of the
//! value `P` forces and thus fail to satisfy the authored roots (measured, on
//! `rlim_invariant` index 88). [`Executor::finite_model_prepare_witness`]
//! therefore completes a semantic clone — with the invented pin values, then
//! with a witness probe of the residual — and REQUIRES every residual root and
//! every pin to evaluate to `true` under the result. The checked clone is only
//! published later by the atomic model-bound authority installer. A
//! `(get-model)` after one of these `sat`s is then sound because that exact
//! model was evaluated against the query, not because the pins were total.
//!
//! Totality of the pin set is still required, but only for what it always
//! really bought: a truth value that is fixed in every model of `P`. A leaf the
//! candidate model leaves UNASSIGNED is completed with
//! [`Executor::unconstrained_default_value`] rather than declining the pass —
//! `P` is an arbitrary ground premise as far as the argument is concerned.
//!
//! ## What this lane COSTS, and the budget that bounds it
//!
//! Reaching the pass is not free. One pass runs a refutation per universal, a
//! counterexample probe, the residual `confirm` solve and the witness probe,
//! each capped at [`FINITE_MODEL_PROBE_MS`]; and
//! [`Executor::try_finite_model_forall_refinement`] runs the whole thing up to
//! [`MAX_FINITE_MODEL_ROUNDS`] times, while
//! [`Executor::try_finite_model_sat_certificate`] runs another pass from the
//! publication gates and the last-chance hook. Per-sub-solve caps therefore
//! bound a check-sat's exposure at TENS OF SECONDS. That is invisible on a
//! ten-file FP corpus and fatal on an incremental trace with 1,645 check-sats:
//! sampling `exp_loop_true-unreach-call.c` (Inc Equality_MachineArith) put 64%
//! of the solve inside this lane, for 14 answers in 150s.
//!
//! Two limits bound it, and BOTH fail closed:
//!
//! * [`FINITE_MODEL_LANE_BUDGET_MS`] — what one invocation may spend across
//!   every sub-solve it runs;
//! * [`FINITE_MODEL_LANE_SEED_MS`] — what the lane may spend on DECLINES in a
//!   SESSION before it has to have paid for itself, after which it may spend
//!   on failures at most what it has already spent on successes.
//!
//! Neither touches the witness check, which is the only thing standing between
//! pin completion and a published wrong model and which runs in full on every
//! certified pass.
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
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;

use super::model::EvalValue;
use super::quantifier_loop::result_mapping::CheckedGroundDecision;
use super::Executor;
use crate::ematching::{contains_quantifier, subst_vars};
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::logic_detection::LogicCategory;

mod budget;
mod witness;
pub(in crate::executor) use budget::LaneAccount;
use budget::{
    LaneBudget, FINITE_MODEL_LANE_BUDGET_MS, FINITE_MODEL_LANE_SEED_MS, MAX_FINITE_MODEL_ROUNDS,
};
use witness::PassOutcome;

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

impl Executor {
    /// Whether the live query is exactly the hard/assumption SAT scope this
    /// certificate covers. Native API softs are installed into the frontend
    /// context for the duration of their executor transaction, so both parsed
    /// and native MaxSMT queries fail this same check.
    fn finite_model_plain_sat_scope(&self) -> bool {
        self.ctx.objectives().is_empty() && self.ctx.soft_constraints().is_empty()
    }

    /// Milliseconds one lane invocation may spend (#witness-check-cost).
    ///
    /// [`FINITE_MODEL_LANE_BUDGET_MS`] unless a caller has overridden it. The
    /// override exists so the barrier test can drive a SPENT account through
    /// the real lane on a fixture that certifies today — there is no way to
    /// reach a budget decline from outside otherwise, and a barrier that never
    /// runs is the vacuous kind this lane has already shipped once.
    fn finite_model_lane_budget_ms(&self) -> u64 {
        if let Some(override_ms) = self.finite_model_lane.budget_ms_override {
            return override_ms;
        }
        ay_core::misc_cli_flags()
            .fmq_lane_budget_ms
            .unwrap_or(FINITE_MODEL_LANE_BUDGET_MS)
    }

    /// Open an account for one lane invocation, or `None` if the lane has
    /// outrun what it has earned in this session (#witness-check-cost).
    ///
    /// See [`FINITE_MODEL_LANE_SEED_MS`] for the rule. Returning `None` is a
    /// decline, which is this lane's ordinary fail-closed outcome.
    fn finite_model_lane_open(&self) -> Option<LaneBudget> {
        let per_invocation = self.finite_model_lane_budget_ms();
        let seed = ay_core::misc_cli_flags()
            .fmq_seed_ms
            .unwrap_or(FINITE_MODEL_LANE_SEED_MS);
        let allowance = seed.saturating_add(self.finite_model_lane.certified_ms);
        let left = allowance.saturating_sub(self.finite_model_lane.declined_ms);
        if left == 0 {
            trace(|| {
                format!(
                    "lane closed: declined={}ms allowance={}ms certified={}ms certificates={}",
                    self.finite_model_lane.declined_ms,
                    allowance,
                    self.finite_model_lane.certified_ms,
                    self.finite_model_lane.certificates
                )
            });
            return None;
        }
        // Bounded by the DECLINE allowance as well as the per-invocation cap:
        // an invocation may not open a hole larger than the account can cover
        // if it turns out to be a decline. An override of 0 must still produce
        // a SPENT account, so the cap wins the `min` at zero.
        Some(LaneBudget::start(per_invocation.min(left)))
    }

    /// Book what one lane invocation cost and what it returned.
    ///
    /// Called on EVERY exit path of both entry points; a spend that is not
    /// booked is a spend the session rule cannot see.
    fn finite_model_lane_settle(&mut self, budget: LaneBudget, certified: bool) {
        let cost = budget.elapsed_ms();
        if certified {
            self.finite_model_lane.certified_ms =
                self.finite_model_lane.certified_ms.saturating_add(cost);
            self.finite_model_lane.certificates =
                self.finite_model_lane.certificates.saturating_add(1);
        } else {
            self.finite_model_lane.declined_ms =
                self.finite_model_lane.declined_ms.saturating_add(cost);
        }
        // The economics this rule is set from: what one invocation cost, what
        // it returned, and the running session totals. Choosing the constants
        // off anything else is guessing.
        trace(|| {
            format!(
                "lane settle: cost={cost}ms certified={certified} \
                 session_declined={}ms session_certified={}ms session_certificates={}",
                self.finite_model_lane.declined_ms,
                self.finite_model_lane.certified_ms,
                self.finite_model_lane.certificates
            )
        });
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

    /// Is `assertions` checked-UNSAT, within what the lane has left to spend?
    ///
    /// A budget-exhausted call answers "not refuted", which is the same shape
    /// as a sub-solve that ran out its own budget: the caller loses a decision,
    /// never gains one.
    fn finite_model_refutes(&mut self, assertions: Vec<TermId>, budget: LaneBudget) -> bool {
        self.checked_ground_solve(
            assertions.clone(),
            LogicCategory::Other,
            budget.sub_solve_ms(),
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
        budget: LaneBudget,
    ) -> TruthOutcome {
        if budget.spent() {
            trace(|| "truth value: lane budget spent".to_string());
            return TruthOutcome::Unknown;
        }
        let (matrix_sk, skolems) = self.finite_model_skolemize(leaf);
        let negated = self.ctx.terms.mk_not(matrix_sk);

        let with = |pins: &[TermId], extra: TermId| {
            let mut v: Vec<TermId> = Vec::with_capacity(pins.len() + 1);
            v.extend_from_slice(pins);
            v.push(extra);
            v
        };

        if leaf.universal {
            if self.finite_model_refutes(with(pins, negated), budget) {
                return TruthOutcome::Determined(true);
            }
            // A counterexample point exists somewhere. Pin one down and certify
            // that it falsifies the matrix in every model of the pins.
            let Some(values) = self.probe_finite_witness_values(
                with(pins, negated),
                &skolems,
                budget.sub_solve_ms(),
            ) else {
                return TruthOutcome::Unknown;
            };
            let Some(instance) = self.finite_model_instance_at(leaf, &values) else {
                return TruthOutcome::Unknown;
            };
            if self.finite_model_refutes(with(pins, instance), budget) {
                return TruthOutcome::Determined(false);
            }
            // Undetermined under these pins: offer the instance for refinement.
            TruthOutcome::Refine(instance)
        } else {
            let Some(values) = self.probe_finite_witness_values(
                with(pins, matrix_sk),
                &skolems,
                budget.sub_solve_ms(),
            ) else {
                // No witness point at all under the pins — if that is CERTIFIED,
                // the existential is false in every model of them.
                return if self.finite_model_refutes(with(pins, matrix_sk), budget) {
                    TruthOutcome::Determined(false)
                } else {
                    TruthOutcome::Unknown
                };
            };
            let Some(instance) = self.finite_model_instance_at(leaf, &values) else {
                return TruthOutcome::Unknown;
            };
            let negated_instance = self.ctx.terms.mk_not(instance);
            if self.finite_model_refutes(with(pins, negated_instance), budget) {
                TruthOutcome::Determined(true)
            } else {
                TruthOutcome::Unknown
            }
        }
    }

    /// ONE certificate pass over the authored leaves, with no installed-model
    /// mutation.
    ///
    /// The pass mints no authority and asserts nothing.
    /// [`PassOutcome::Certified`] reports that the window is satisfiable AND has
    /// returned a staged model verified against the residual (see
    /// [`Self::finite_model_prepare_witness`]) for the caller to seal;
    /// [`PassOutcome::Refined`] returns counterexample instances in `instances`;
    /// [`PassOutcome::Declined`] establishes nothing.
    fn finite_model_certificate_pass(
        &mut self,
        round: usize,
        roots: &[TermId],
        universals: &[AuthoredUniversal],
        instances: &mut Vec<TermId>,
        budget: LaneBudget,
    ) -> PassOutcome {
        if budget.spent() {
            trace(|| format!("round {round}: lane budget spent before the pass"));
            return PassOutcome::Declined;
        }
        // ONE pin set shared by every leaf in the pass. Per-leaf pin sets
        // would fix each truth value in a DIFFERENT structure, and the residual
        // formula below needs them all true in the SAME one.
        let mut completions: Vec<(TermId, EvalValue)> = Vec::new();
        let (pins, pins_total) = self.finite_model_pins(universals, &mut completions);
        trace(|| {
            format!(
                "round {round}: pins={} total={pins_total} completed={} model={}",
                pins.len(),
                completions.len(),
                self.last_model.is_some()
            )
        });
        if !pins_total {
            trace(|| format!("round {round}: pin set not total"));
            return PassOutcome::Declined;
        }

        let mut values: HashMap<TermId, TermId> = HashMap::default();
        let mut refined = false;
        for leaf in universals {
            match self.finite_model_truth_value(leaf, &pins, budget) {
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
                        return PassOutcome::Declined;
                    }
                    instances.push(instance);
                    refined = true;
                }
                TruthOutcome::Unknown => {
                    trace(|| format!("round {round}: truth value undetermined"));
                    return PassOutcome::Declined;
                }
            }
        }
        if refined {
            return PassOutcome::Refined;
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
        let decision =
            self.checked_ground_solve(confirm.clone(), LogicCategory::Other, budget.sub_solve_ms());
        let outcome = match decision {
            // The witness stage below is NOT budgeted away. It is the only
            // check standing between pin completion and a published wrong
            // model, so a spent account must never let a staged model through
            // unchecked — `finite_model_prepare_witness` returns `None` when it
            // cannot verify, and `None` declines. Its own gap-filling probe is
            // bounded by whatever the account has left, exactly like every
            // other sub-solve, and a probe that gets nothing simply fails the
            // re-check.
            Some(CheckedGroundDecision::Sat(checked)) => checked
                .consume(self, &confirm)
                .then(|| self.finite_model_prepare_witness(&confirm, &completions, budget))
                .flatten()
                .map_or(PassOutcome::Declined, PassOutcome::certified),
            // A refuted residual says only that no model of the PINS satisfies
            // the roots. The pins are an extra hypothesis nobody asserted, so
            // on its own that refutes nothing about the query. See the
            // `PassOutcome` doc for the dual that would, and why it is absent.
            Some(CheckedGroundDecision::Unsat(_)) | None => PassOutcome::Declined,
        };
        trace(|| format!("round {round}: all determined; confirm={}", outcome.label()));
        outcome
    }

    /// Establish and INSTALL finite-sort quantified SAT authority for the
    /// current authored root window, with one atomic model replacement.
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
        // This theorem covers only the exact hard/assumption root window. An
        // objective or soft constraint adds a public obligation outside that
        // window, so this producer must not mint authority for optimization.
        if self.should_abort_theory_loop() || !self.finite_model_plain_sat_scope() {
            return false;
        }
        // Opened BEFORE the root/leaf analysis. A closed lane must cost a
        // predicate, not a traversal of every authored root, on each of an
        // incremental trace's check-sats.
        let Some(budget) = self.finite_model_lane_open() else {
            return false;
        };
        let authority_roots = self.independent_gate_query_roots();
        let Some(universals) = authored_universal_leaves_impl(self, &authority_roots) else {
            self.finite_model_lane_settle(budget, false);
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
        let outcome = self.finite_model_certificate_pass(
            0,
            &authority_roots,
            &universals,
            &mut instances,
            budget,
        );
        self.finite_model_lane_settle(budget, matches!(outcome, PassOutcome::Certified(_)));
        match outcome {
            PassOutcome::Certified(model) => {
                let Some(evidence) = super::bv_mbqi::checked_full_domain_sat_authority(
                    self,
                    &authority_roots,
                    &certified_nodes,
                ) else {
                    trace(|| "gate-hook: authority roots do not cover".to_string());
                    return false;
                };
                let installed =
                    self.install_finite_model_full_domain_sat_authority(evidence, *model);
                trace(|| format!("gate-hook: installed={installed}"));
                installed
            }
            PassOutcome::Refined | PassOutcome::Declined => false,
        }
    }

    /// LAST-CHANCE consult of [`Self::try_finite_model_sat_certificate`] on an
    /// `Unknown(QuantifierUnhandled)` the quantifier loop already published.
    ///
    /// # The gap this closes (#inc-fparith-last-mile)
    ///
    /// MECHANISM, corrected by review — the original account here was refuted
    /// by tracing the code on the queries this hook actually gains.
    ///
    /// The tempting story is "the lane never gets that far". It is FALSE. On
    /// 8 of 8 sampled gained indices (103, 181, 209, 944, 1039, 1250, 1495,
    /// 1757) the pre-hook binary already prints 6-7 `FMQ` lines INCLUDING
    /// `FMQ enter`: `try_finite_model_forall_refinement` is entered, runs
    /// `finite_model_certificate_pass` round 0 to completion, and reports
    /// `round 0: all determined; confirm=false`. 11 of 12 randomly sampled
    /// still-missing indices also print `FMQ` lines.
    ///
    /// What this hook really does is RE-RUN the identical certificate pass a
    /// second time, in a different executor state. On idx 103 the same roots
    /// `[TermId(400), TermId(107), TermId(408)]` and the same
    /// `pins=1 total=true` yield `confirm=false` inside the loop and
    /// `confirm=true` at the return value. That is a legitimate rescue, but it
    /// is a state-dependence result, not a reachability one — and any residual
    /// analysis aimed by the old model (e.g. "the next lever is
    /// `finite_model_pins`") is aimed wrong.
    ///
    /// Also corrected: it is NOT true that all three call sites are downstream
    /// of MBQI having produced a verdict. `model/independent_gate.rs:4302` sits
    /// inside `apply_quantified_model_failclosed_gate`, a PUBLICATION gate in
    /// `emit_sat_verdict`, reached from a proposed ground `Sat`.
    ///
    /// # Why it cannot change a correct answer
    ///
    /// * It is consulted ONLY on `Unknown`, so no `Sat`/`Unsat` can be
    ///   reinterpreted; the sole reachable transition is `Unknown -> Sat`.
    /// * It is consulted only for `QuantifierUnhandled`, the reason that means
    ///   "a quantifier had no complete instantiation path" — never for a
    ///   timeout, memout, or a fragment the engine deliberately refuses.
    /// * The grant itself is [`Self::try_finite_model_sat_certificate`],
    ///   unchanged: it adds no assertions, runs no outer re-solve, reads every
    ///   quantifier's truth value off CHECKED UNSAT results, and only succeeds
    ///   when `checked_full_domain_sat_authority` confirms the certified nodes
    ///   are EXACTLY the quantifier nodes of the authored root window. A
    ///   ground SAT is never authority for a quantified formula here, which is
    ///   why the `has_unsafe_partial_quantifiers` hazard (ay #8729 / Z3 #6303)
    ///   does not reach it.
    /// * The resulting `Sat` still traverses the ordinary emission funnel and
    ///   its publication gates, exactly as it does from the other three call
    ///   sites.
    ///
    /// # Why it cannot recurse
    ///
    /// Every sub-solve this lane runs goes through `checked_ground_solve`,
    /// i.e. `checked_isolated_solve` in `CheckedIsolatedMode::GroundDecision`,
    /// which returns `None` for any assertion vector containing a quantifier.
    /// A quantifier-free probe cannot produce `QuantifierUnhandled`, so a
    /// nested `check_sat` can never re-enter this hook.
    ///
    /// The composition with [`Executor::cegar_refine_solve`] lives here rather
    /// than at the call site so the whole argument stays in one file.
    pub(in crate::executor) fn cegar_refine_solve_with_finite_model_last_chance(
        &mut self,
    ) -> Result<SolveResult> {
        let result = self.cegar_refine_solve()?;
        Ok(self.finite_model_last_chance(result))
    }

    /// NO DISCRIMINATING TEST EXISTS FOR THIS HOOK. Stated plainly rather than
    /// papered over, because review proved it: replacing this body with an
    /// unconditional `return result;` leaves the suite byte-identical at 6,902
    /// passed, and all four committed `fp_universal_lane` fixtures are
    /// answer-identical on main and branch.
    ///
    /// Why a unit fixture does not work: the promote direction needs the
    /// certificate to CONFIRM, which needs a candidate model with total pins.
    /// A synthetic `(not (exists ((x Float32)) (P x)))` executor has no model,
    /// so `try_finite_model_sat_certificate` declines and any assertion behind
    /// it is skipped. An `if confirmed { .. }` test therefore PASSES under the
    /// no-op mutation — that vacuous version was written here and deleted
    /// rather than shipped.
    ///
    /// What would discriminate, measured: the rlim_invariant slice at index
    /// 103 (pre-hook `unknown`, post-hook `sat`, both bitwuzla and z3 `sat`).
    /// A hand-minimised 8-line variant does NOT discriminate, so the
    /// surrounding assertion stack is load-bearing and any shrunk fixture must
    /// be re-validated against the PRE-HOOK binary before it is trusted.
    fn finite_model_last_chance(&mut self, result: SolveResult) -> SolveResult {
        if !matches!(result, SolveResult::Unknown)
            || !matches!(
                self.last_unknown_reason,
                Some(UnknownReason::QuantifierUnhandled)
            )
        {
            return result;
        }
        trace(|| "last-chance: consulting the finite-sort certificate".to_string());
        if !self.try_finite_model_sat_certificate() {
            return result;
        }
        self.defer_model_validation = false;
        self.last_model_validated = true;
        self.last_unknown_reason = None;
        SolveResult::Sat
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
        if trigger_quants.is_empty() || !self.finite_model_plain_sat_scope() {
            return None;
        }
        // Opened here, alongside the other reasons this lane declines to
        // engage at all, so a closed lane neither traverses the roots nor
        // revokes an authority it is not going to replace.
        let budget = self.finite_model_lane_open()?;
        let authority_roots = self.independent_gate_query_roots();
        let Some(universals) = authored_universal_leaves_impl(self, &authority_roots) else {
            trace(|| "authored leaves not all finite-sort universals".to_string());
            self.finite_model_lane_settle(budget, false);
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

        // ONE account for the whole refinement loop, not one per round: the
        // per-round cap is what let a single check-sat spend
        // `MAX_FINITE_MODEL_ROUNDS` times the intended amount.
        let mut certified = false;
        let outcome = self.finite_model_refinement_rounds(
            &authority_roots,
            &universals,
            &certified_nodes,
            category,
            budget,
            &mut certified,
        );
        // Settled on EVERY exit path, including the re-solve legs: a spend the
        // session rule cannot see is a spend that never stops.
        self.finite_model_lane_settle(budget, certified);
        outcome
    }

    /// The refinement rounds themselves, split out so the caller can settle the
    /// lane account exactly once however this returns.
    fn finite_model_refinement_rounds(
        &mut self,
        authority_roots: &[TermId],
        universals: &[AuthoredUniversal],
        certified_nodes: &[TermId],
        category: LogicCategory,
        budget: LaneBudget,
        certified: &mut bool,
    ) -> Option<Result<SolveResult>> {
        for round in 0..MAX_FINITE_MODEL_ROUNDS {
            if self.should_abort_theory_loop() {
                trace(|| format!("round {round}: abort requested"));
                return None;
            }

            let mut new_instances: Vec<TermId> = Vec::new();
            match self.finite_model_certificate_pass(
                round,
                authority_roots,
                universals,
                &mut new_instances,
                budget,
            ) {
                PassOutcome::Declined => return None,
                PassOutcome::Certified(model) => {
                    *certified = true;
                    let Some(evidence) = super::bv_mbqi::checked_full_domain_sat_authority(
                        self,
                        authority_roots,
                        certified_nodes,
                    ) else {
                        trace(|| format!("round {round}: authority roots do not cover"));
                        return None;
                    };
                    if !self.install_finite_model_full_domain_sat_authority(evidence, *model) {
                        trace(|| format!("round {round}: staged witness install declined"));
                        return None;
                    }
                    return Some(Ok(SolveResult::Sat));
                }
                PassOutcome::Refined => {}
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

/// The session yield rule (#witness-check-cost), driven at the accountant.
///
/// The end-to-end barrier for the budget lives in `witness.rs` (it drives a
/// SPENT account through a fixture that certifies today). These pin the rule
/// itself: seed capital, exhaustion, and the earning step.
#[cfg(test)]
mod lane_account_tests {
    use super::*;

    #[test]
    fn seed_capital_opens_the_lane_and_declines_beyond_it_close_it() {
        let mut executor = Executor::new();
        assert!(
            executor.finite_model_lane_open().is_some(),
            "a fresh session must have speculative capital"
        );

        executor.finite_model_lane.declined_ms = FINITE_MODEL_LANE_SEED_MS;
        assert!(
            executor.finite_model_lane_open().is_none(),
            "spending the seed on declines alone must close the lane"
        );

        executor.finite_model_lane.certified_ms = 1;
        assert!(
            executor.finite_model_lane_open().is_some(),
            "time spent on a certificate must buy back an equal time for declines"
        );

        executor.finite_model_lane.declined_ms = FINITE_MODEL_LANE_SEED_MS + 1;
        assert!(
            executor.finite_model_lane_open().is_none(),
            "and no more than an equal time"
        );

        // Success at scale is what keeps a paying session open: this is the
        // shape of the FP files (declines cost 0.16-0.34 of certificates).
        executor.finite_model_lane.certified_ms = 102_000;
        executor.finite_model_lane.declined_ms = 16_600;
        assert!(executor.finite_model_lane_open().is_some());
        // And this is the shape of `exp_loop` (declines cost 10.7x).
        executor.finite_model_lane.certified_ms = 33_500;
        executor.finite_model_lane.declined_ms = 359_400;
        assert!(executor.finite_model_lane_open().is_none());
    }

    #[test]
    fn settling_books_the_spend_on_the_side_that_earned_it() {
        let mut executor = Executor::new();
        let budget = LaneBudget::start(0);
        executor.finite_model_lane_settle(budget, true);
        assert_eq!(executor.finite_model_lane.certificates, 1);
        executor.finite_model_lane_settle(budget, false);
        assert_eq!(
            executor.finite_model_lane.certificates, 1,
            "a decline must not count as a certificate"
        );
        // A zero-cost account books zero on both sides; the split is what is
        // under test, not the clock.
        assert_eq!(executor.finite_model_lane.certified_ms, 0);
        assert_eq!(executor.finite_model_lane.declined_ms, 0);
    }

    /// A zero override must produce a SPENT account, not an unfunded-but-live
    /// one — this is what the end-to-end barrier depends on.
    #[test]
    fn a_zero_override_opens_an_already_spent_account() {
        let mut executor = Executor::new();
        executor.finite_model_lane.budget_ms_override = Some(0);
        let budget = executor
            .finite_model_lane_open()
            .expect("the session rule must still admit the invocation");
        assert!(budget.spent());
        assert_eq!(budget.sub_solve_ms(), 0);
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

    /// The last-chance hook's ENTRY CONDITION, pinned.
    ///
    /// The hook is the only thing standing between a published `Unknown` and a
    /// published `Sat` on this route, so the set of results it will even look
    /// at is a soundness-relevant contract, not a heuristic. It must decline —
    /// byte-identically, without consulting the certificate — for every result
    /// that is not `Unknown`, and for every `Unknown` whose reason is not
    /// `QuantifierUnhandled` (a timeout or a memout is not an unhandled
    /// quantifier, and re-deciding one would hide a budget failure as a
    /// capability).
    #[test]
    fn last_chance_only_fires_on_unknown_quantifier_unhandled() {
        let declines: Vec<(SolveResult, Option<UnknownReason>)> = vec![
            (SolveResult::Sat, None),
            (SolveResult::Sat, Some(UnknownReason::QuantifierUnhandled)),
            (
                SolveResult::unsat(),
                Some(UnknownReason::QuantifierUnhandled),
            ),
            (SolveResult::Unknown, None),
            (SolveResult::Unknown, Some(UnknownReason::Timeout)),
            (SolveResult::Unknown, Some(UnknownReason::MemoryLimit)),
            (SolveResult::Unknown, Some(UnknownReason::Incomplete)),
            (SolveResult::Unknown, Some(UnknownReason::SelfCheckRejected)),
            (
                SolveResult::Unknown,
                Some(UnknownReason::QuantifierRoundLimit),
            ),
        ];
        for (result, reason) in declines {
            let mut executor = Executor::new();
            executor.last_unknown_reason = reason;
            let before = result.clone();
            let after = executor.finite_model_last_chance(result);
            assert_eq!(
                format!("{after:?}"),
                format!("{before:?}"),
                "the hook must pass {before:?} / reason {reason:?} through untouched"
            );
            assert_eq!(
                executor.last_unknown_reason, reason,
                "a declined consult must not clear the reason"
            );
            assert!(
                !executor.last_model_validated,
                "a declined consult must not claim model validation"
            );
        }
    }

    /// The one admitted entry — and it still fails CLOSED.
    ///
    /// `Unknown(QuantifierUnhandled)` on an executor with no candidate model
    /// reaches the certificate and the certificate declines (`finite_model_pins`
    /// needs `last_model`), so the published result is unchanged. This pins
    /// that reaching the hook is not the same as being granted by it.
    #[test]
    fn last_chance_consults_but_fails_closed_without_a_model() {
        let mut executor = Executor::new();
        let exists = exists_p(&mut executor.ctx.terms);
        let root = executor.ctx.terms.mk_not(exists);
        executor.ctx.assertions.push(root);
        executor.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);

        let after = executor.finite_model_last_chance(SolveResult::Unknown);
        assert!(
            matches!(after, SolveResult::Unknown),
            "no candidate model means no pins, so the certificate must decline"
        );
        assert_eq!(
            executor.last_unknown_reason,
            Some(UnknownReason::QuantifierUnhandled),
            "a declined consult leaves the published reason exactly as it was"
        );
    }
}
