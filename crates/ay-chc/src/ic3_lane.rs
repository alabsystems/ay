// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Additive IC3 portfolio lane (#8211 wiring): lower a single-loop CHC into the
//! bit-level [`BitLevelTransitionSystem`], run the clause-level [`Ic3Solver`]
//! (with CTG generalization), and on `Safe` reconstruct a *candidate*
//! word-level [`InvariantModel`].
//!
//! SOUNDNESS CONTRACT: this lane is a *candidate generator only*. The returned
//! `InvariantModel` is NOT trusted. The caller MUST re-validate it through
//! [`crate::engines::validate_external_invariant_model`] (the unchanged
//! word-level trusted validator) before reporting `Safe`. A wrong invariant
//! (or a false loop), a wrong CFG linearization, or a too-narrow bit-blast all
//! fail that re-validation and the lane contributes nothing. This keeps the
//! verifier kernel untouched and cannot create a false proof.
//!
//! Three lowering stages (each *modelling-only*, all re-checked downstream):
//!
//! (a) LINEARIZE — a real targo-lowered loop is a multi-block CFG: one relation
//!     per basic block (`bb0`, `bb1`, ..., plus the `error` query), edges as
//!     linear Horn rules `bb_i(s) /\ guard -> bb_j(s')`. The loop body spans
//!     several blocks, so the whole loop is one strongly-connected component
//!     (SCC). [`linearize_to_single_loop`] performs proper Gaussian/unfold
//!     elimination: it repeatedly resolves away every predicate that is not
//!     *directly* self-recursive (entry blocks, body blocks, error). Each
//!     elimination resolves a predicate's definition clauses into its use sites
//!     (renaming the definition's variables fresh and linking head/use argument
//!     positions with equality constraints). Collapsing an `n`-block loop SCC
//!     leaves exactly one self-recursive predicate — the single-recursive-
//!     predicate form the rest of the lane drives. (NOT the prior
//!     clause_inlining/multi_def attempt that dropped a cycle endpoint: here the
//!     self-loop resolvent `R -> R` is created when the penultimate SCC member
//!     is eliminated, so no endpoint is lost.)
//!
//! (b) BIT-BLAST — each predicate argument sort becomes a fixed number of
//!     Boolean latches: `Bool` -> 1, `Int` -> [`INT_WIDTH`], `BitVec(w)` ->
//!     [`blast_width`]`(w)` (the natural bit-vector target; capped so the latch
//!     count and IC3 work stay small). Little-endian.
//!
//! (c) Bv* OPS — the transition/guard constraints encode word ops over those
//!     latches: `BvAdd`/`BvSub` as ripple-carry adders, `BvNeg`/`BvNot` and the
//!     bitwise family (`BvAnd`/`BvOr`/`BvXor`/`BvNand`/`BvNor`/`BvXnor`)
//!     per-bit, `BvULt`/`BvULe`/`BvUGt`/`BvUGe` as ripple comparators,
//!     `BvExtract`/`BvShl`/`BvLShr` by constant as bit slices, and bit-vector
//!     equality as a per-bit XNOR/AND tree. Integer `+`/`-`/`mod 2^k`/`div 2^k`
//!     are handled the same way at [`INT_WIDTH`].
//!
//! IC3 synthesises an invariant over the bits; the back-translation reconstructs
//! a word-level candidate (`Bool` bit -> the parameter; `Int` bit `i` ->
//! `(= (mod (div c 2^i) 2) 1)`; `BitVec` bit `i` -> `(= ((_ extract i i) c)
//! #b1)`), and the trusted word-level validator re-checks it against the REAL
//! unbounded transition. A blast/width/linearization mismatch can only make the
//! candidate fail re-validation; it can never manufacture a false proof.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::Duration;

use ay_sat::{Literal, Variable};

use crate::clause::{ClauseBody, ClauseHead, HornClause};
use crate::ic3::solver::{Ic3Result, Ic3Solver};
use crate::ic3::transition_system::BitLevelTransitionSystem;
use crate::pdr::model::{InvariantModel, PredicateInterpretation};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, PredicateId};

/// Bit-blast width for `Int` predicate arguments.
///
/// This is the (untrusted) modelling width used by the bit-level engine only.
/// It does NOT bound the loop iteration count — IC3 induction handles unbounded
/// loop *length*; the width is the integer type width for the blast. Any
/// candidate IC3 finds is re-checked word-level by the trusted validator, so a
/// too-narrow width can only cause a missed proof, never an unsound one. Kept
/// modest so the latch count (and IC3 work) stays small; parity-style bit-0
/// invariants are found at any width >= 1.
const INT_WIDTH: usize = 8;

/// Maximum number of latches used to model a `BitVec(w)` argument.
///
/// Real targo-lowered `u64` loops carry `BitVec(64)` state. Blasting the full
/// 64 bits is *sound* (a bit-vector is finite, so the bit-level model is exact)
/// but heavy. Because the lane is a candidate generator whose output is
/// re-validated word-level, we may model at a smaller width without risking a
/// false proof: a too-narrow blast can only miss a candidate. The cap keeps the
/// latch count and IC3 work small; bit-0 (parity) invariants are found at any
/// width >= 1.
const BV_BLAST_CAP: usize = 8;

/// Number of latches used to model a `BitVec(w)` value (see [`BV_BLAST_CAP`]).
fn blast_width(w: u32) -> usize {
    (w as usize).clamp(1, BV_BLAST_CAP)
}

/// Try to prove a single-loop CHC (Boolean, bit-blasted `Int`, and/or
/// `BitVec(w)` arguments; possibly a multi-block CFG that is first linearized to
/// one recursive predicate) with the bit-level IC3 engine. Returns a *candidate*
/// invariant model on `Safe`, or `None` if the problem is outside the mappable
/// fragment or IC3 did not converge to `Safe`.
///
/// The result is UNTRUSTED — the caller re-validates it via the word-level
/// validator. See the module docs.
pub fn try_prove_chc_loop(problem: &ChcProblem, _timeout: Duration) -> Option<InvariantModel> {
    let dbg = std::env::var_os("TRUST_IC3_LANE_DEBUG").is_some();
    if let Some(path) = std::env::var_os("TRUST_IC3_LANE_DUMP") {
        use std::io::Write as _;
        if let Ok(mut f) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
        {
            let _ = writeln!(
                f,
                "=== IC3_LANE_DUMP preds={} clauses={} ===\n{:#?}\n",
                problem.predicates().len(),
                problem.clauses().len(),
                problem
            );
        }
    }
    let low = lower_loop(problem);
    if dbg {
        eprintln!(
            "IC3_LANE: lower_loop={} (preds={})",
            if low.is_some() { "Some" } else { "None" },
            problem.predicates().len()
        );
    }
    let Lowering {
        ts,
        pred,
        params,
        latches,
        orig_header,
    } = low?;
    let mut solver = Ic3Solver::new(ts, false);
    let res = solver.solve();
    let safe = matches!(res, Ic3Result::Safe { .. });
    if dbg {
        eprintln!("IC3_LANE: solve_safe={safe}");
    }
    match res {
        Ic3Result::Safe { invariant_level } => {
            let clauses = solver.invariant_clauses(invariant_level);
            let bt = back_translate(pred, &params, &latches, &clauses);
            if dbg {
                eprintln!(
                    "IC3_LANE: back_translate={}",
                    if bt.is_some() { "Some" } else { "None" }
                );
            }
            let model = bt?;
            match orig_header {
                None => Some(model),
                Some(header) => {
                    // The CFG was collapsed by linearization: `model` is the loop
                    // header invariant expressed over the COLLAPSED predicate, but
                    // the trusted re-validator runs against the ORIGINAL
                    // multi-predicate problem and needs an interpretation for
                    // EVERY original predicate. Lift the header invariant onto all
                    // original predicates by forward-image propagation (the header
                    // keeps the IC3-found invariant; the other blocks get its image
                    // along each CFG edge). Still UNTRUSTED — the caller
                    // re-validates the full model on the original transition.
                    let interp = model.get(&pred)?;
                    let lifted = lift_header_to_full_model(
                        problem,
                        header,
                        &interp.vars,
                        &interp.formula,
                        _timeout,
                    );
                    if dbg {
                        eprintln!(
                            "IC3_LANE: lift_header_to_full_model={}",
                            if lifted.is_some() { "Some" } else { "None" }
                        );
                    }
                    lifted
                }
            }
        }
        _ => None,
    }
}

/// Lift a collapsed loop-header invariant onto EVERY original predicate of a
/// multi-block CFG, producing a full multi-predicate candidate model that the
/// trusted word-level validator can re-check against the ORIGINAL problem.
///
/// The bit-level IC3 lane collapses an `n`-block loop SCC down to one recursive
/// predicate (the header `header`) and finds the header invariant `h_formula`
/// over the header's positional parameters `h_vars`. That single interpretation
/// does NOT validate against the original problem, which still has one relation
/// per basic block: the validator requires an interpretation for every
/// predicate referenced in a clause.
///
/// We recover the remaining predicates' invariants by FORWARD-IMAGE propagation
/// of the header invariant through the CFG. Each non-header predicate's invariant
/// is the (exact) image of its predecessors' invariants across the connecting
/// edge: for an edge `Ptgt(headargs) <- Psrc(srcargs) /\ guard`, the image is
///
/// ```text
/// Inv_tgt(t) := exists clausevars. Inv_src[params->srcargs] /\ guard
///                                  /\ AND_i (t_i = headargs_i)
/// ```
///
/// computed by SUBSTITUTION: each `t_i = headargs_i` whose `headargs_i` is an
/// invertible function of one clause variable (identity, `not`, `+const`,
/// `-const`, `~`, unary `-`) yields a substitution for that variable; constant
/// head positions become literal equalities. Facts (`Ptgt(headargs) <- guard`,
/// no body predicate) give the entry image directly. We iterate to a fixpoint
/// over the (acyclic, since the header is pinned) body. The header itself keeps
/// the IC3-found `h_formula` and is never recomputed.
///
/// The forward image is the natural way to "rotate" the loop-head invariant to
/// each program point (e.g. just after `acc := !acc` the relation becomes
/// `acc <=> !count[0]`), which is exactly the per-block invariant the multi-
/// predicate validator needs.
///
/// SOUNDNESS: nothing here is trusted. The returned model is re-checked by
/// `validate_external_invariant_model` against the ORIGINAL (cyclic) transition
/// — including the header's back-edge consecution, which only holds because the
/// IC3-found header invariant is genuinely inductive over the full loop body. A
/// wrong header invariant or a wrong/imprecise image can only make that
/// re-validation FAIL (a missed proof), never forge one. If any predicate's
/// image cannot be computed (a non-invertible head argument, or a clause-local
/// variable that cannot be eliminated), we return `None` and contribute no
/// proof.
fn lift_header_to_full_model(
    original: &ChcProblem,
    header: PredicateId,
    h_vars: &[ChcVar],
    h_formula: &ChcExpr,
    _timeout: Duration,
) -> Option<InvariantModel> {
    let dbg = std::env::var_os("TRUST_IC3_LANE_DEBUG").is_some();
    if dbg {
        eprintln!(
            "IC3_LIFT: ===== begin lift, header pred#{} =====",
            header.index()
        );
        for p in original.predicates() {
            eprintln!(
                "IC3_LIFT: pred#{} name={} sorts={:?}",
                p.id.index(),
                p.name,
                p.arg_sorts
            );
        }
        for (ci, c) in original.clauses().iter().enumerate() {
            let head = match &c.head {
                ClauseHead::Predicate(h, a) => format!("pred#{}({:?})", h.index(), a),
                ClauseHead::False => "false".to_string(),
            };
            eprintln!(
                "IC3_LIFT: clause[{ci}] head={head} body_preds={:?} guard={:?}",
                c.body
                    .predicates
                    .iter()
                    .map(|(q, qa)| (q.index(), qa.clone()))
                    .collect::<Vec<_>>(),
                c.body.constraint
            );
        }
    }
    let hpred = original.get_predicate(header)?;
    if hpred.arg_sorts.len() != h_vars.len() {
        if dbg {
            eprintln!(
                "IC3_LIFT: header arg_sorts.len()={} != h_vars.len()={} -> None",
                hpred.arg_sorts.len(),
                h_vars.len()
            );
        }
        return None;
    }
    // Canonical parameter vars per predicate (`__lift_<pid>_<i>`), and the header
    // invariant expressed over the header's canonical params.
    let params_of = |pid: PredicateId, sorts: &[ChcSort]| -> Vec<ChcVar> {
        sorts
            .iter()
            .enumerate()
            .map(|(i, s)| ChcVar::new(format!("__lift_{}_{}", pid.index(), i), s.clone()))
            .collect()
    };
    let hparams = params_of(header, &hpred.arg_sorts);
    let header_subst: Vec<(ChcVar, ChcExpr)> = h_vars
        .iter()
        .cloned()
        .zip(hparams.iter().cloned().map(ChcExpr::var))
        .collect();
    let header_formula = h_formula.substitute(&header_subst);

    // interps[pid] = (params, formula). The header is pinned to the IC3 result.
    let mut interps: HashMap<PredicateId, (Vec<ChcVar>, ChcExpr)> = HashMap::new();
    interps.insert(header, (hparams.clone(), header_formula));

    // Bad/query predicates: any predicate appearing in the body of a `false :- ..`
    // clause (the bottom/query). Their interpretation is `false` (the bad state
    // must be unreachable). We do NOT forward-image into them — a query head like
    // `error()` has zero args to map body vars onto, so edge_image would fail —
    // instead we pin them to `false` and let the UNCHANGED
    // validate_external_invariant_model enforce safety: the defining clause
    // `error(..) :- body /\ guard` becomes `body_interp /\ guard |= false` (the
    // invariant must exclude the bad guard), and `false :- error(..)` is then
    // trivially satisfied. This is sound — pinning to `false` only makes the
    // safety obligation stricter, never forges a proof; the kernel re-checks it.
    //
    // We pin not just the direct query bodies but every DOOMED predicate: one
    // all of whose outgoing edges lead to `false` (a predicate `q` is doomed iff
    // it occurs in >=1 clause body and EVERY clause in which it occurs in the
    // body has a head that is `false` or an already-doomed predicate). The
    // assert-FAIL block (`bb3`, whose only successor is the `error` query) is
    // doomed; the loop header is NOT (it also flows to the good post-assert
    // block). Pinning a doomed predicate to `false` moves its bad-path
    // contradiction onto its DEFINING clause (`bb3 <- bb1 /\ assert-fail` becomes
    // `bb1_inv /\ assert-fail |= false`), which the validator discharges as a
    // transition body, instead of leaving a folded `bb3_interp |= false` query
    // the bounded case-split cannot close. Computed to a fixpoint; sound (pinning
    // to `false` only strengthens — if a pinned predicate is actually reachable
    // the kernel rejects the incoming transition).
    let mut doomed: HashSet<PredicateId> = HashSet::new();
    loop {
        let mut changed = false;
        for p in original.predicates() {
            if doomed.contains(&p.id) || p.id == header {
                continue;
            }
            let mut appears = false;
            let mut all_bad = true;
            for c in original.clauses() {
                if c.body.predicates.iter().any(|(q, _)| *q == p.id) {
                    appears = true;
                    let head_bad = match &c.head {
                        ClauseHead::False => true,
                        ClauseHead::Predicate(h, _) => doomed.contains(h),
                    };
                    if !head_bad {
                        all_bad = false;
                        break;
                    }
                }
            }
            if appears && all_bad {
                doomed.insert(p.id);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for p in original.predicates() {
        if doomed.contains(&p.id) && !interps.contains_key(&p.id) {
            let qparams = params_of(p.id, &p.arg_sorts);
            interps.insert(p.id, (qparams, ChcExpr::Bool(false)));
        }
    }

    let preds: Vec<_> = original.predicates().iter().collect();
    // Forward-image fixpoint: a predicate is finalized once EVERY one of its
    // defining clauses has all body predicates already interpreted (so the OR of
    // disjuncts is complete). The body is acyclic given the pinned header, so
    // this converges in at most `num_preds` rounds.
    let max_rounds = preds.len() + 2;
    for _ in 0..max_rounds {
        let mut progressed = false;
        for p in &preds {
            if interps.contains_key(&p.id) {
                continue;
            }
            let tparams = params_of(p.id, &p.arg_sorts);
            // Gather the defining clauses of p; require all body preds ready.
            let mut disjuncts: Vec<ChcExpr> = Vec::new();
            let mut all_ready = true;
            let mut any_clause = false;
            for c in original.clauses() {
                let ClauseHead::Predicate(h, headargs) = &c.head else {
                    continue;
                };
                if *h != p.id {
                    continue;
                }
                any_clause = true;
                if c.body
                    .predicates
                    .iter()
                    .any(|(q, _)| !interps.contains_key(q))
                {
                    all_ready = false;
                    break;
                }
                match edge_image(c, headargs, &tparams, &interps) {
                    Some(img) => disjuncts.push(img),
                    None => {
                        if dbg {
                            eprintln!(
                                "IC3_LIFT: edge_image=None for head pred#{} headargs={:?} body_preds={:?} guard={:?} -> lift None",
                                p.id.index(),
                                headargs,
                                c.body.predicates.iter().map(|(q, qa)| (q.index(), qa.clone())).collect::<Vec<_>>(),
                                c.body.constraint
                            );
                        }
                        return None; // non-invertible edge: incomplete lift
                    }
                }
            }
            if !any_clause {
                // A predicate with no definition (cannot be reached): leave it for
                // a later round; if it never gets one, the lift stays incomplete.
                continue;
            }
            if !all_ready {
                continue;
            }
            let formula = match disjuncts.len() {
                0 => ChcExpr::Bool(false),
                1 => disjuncts.pop().unwrap(),
                _ => ChcExpr::or_all(disjuncts),
            };
            interps.insert(p.id, (tparams, formula));
            progressed = true;
        }
        if !progressed {
            break;
        }
    }

    // Every predicate referenced in the problem must have an interpretation.
    let mut model = InvariantModel::new();
    for p in &preds {
        let Some((vars, formula)) = interps.get(&p.id) else {
            if dbg {
                eprintln!(
                    "IC3_LIFT: no interpretation produced for pred#{} (arity={}) -> lift None (incomplete fixpoint)",
                    p.id.index(),
                    p.arg_sorts.len()
                );
            }
            return None;
        };
        model.set(
            p.id,
            PredicateInterpretation::new(vars.clone(), formula.clone()),
        );
    }
    Some(model)
}

/// Forward image of a single defining clause `Ptgt(headargs) <- body /\ guard`
/// onto target parameters `tparams`, given interpretations for the body
/// predicates. Returns the image formula over `tparams`, or `None` if a head
/// argument is not an invertible function of a single clause variable (or a
/// clause-local variable cannot be eliminated).
fn edge_image(
    clause: &HornClause,
    headargs: &[ChcExpr],
    tparams: &[ChcVar],
    interps: &HashMap<PredicateId, (Vec<ChcVar>, ChcExpr)>,
) -> Option<ChcExpr> {
    let dbg = std::env::var_os("TRUST_IC3_LANE_DEBUG").is_some();
    if headargs.len() != tparams.len() {
        if dbg {
            eprintln!(
                "IC3_EDGE: headargs.len()={} != tparams.len()={} -> None",
                headargs.len(),
                tparams.len()
            );
        }
        return None;
    }
    // Body relation: AND of each body predicate's invariant instantiated at its
    // call args, plus the clause guard.
    let mut conj: Vec<ChcExpr> = Vec::new();
    for (q, qargs) in &clause.body.predicates {
        let Some((qparams, qformula)) = interps.get(q) else {
            if dbg {
                eprintln!("IC3_EDGE: body pred#{} not interpreted -> None", q.index());
            }
            return None;
        };
        if qparams.len() != qargs.len() {
            if dbg {
                eprintln!(
                    "IC3_EDGE: body pred#{} qparams.len()={} != qargs.len()={} -> None",
                    q.index(),
                    qparams.len(),
                    qargs.len()
                );
            }
            return None;
        }
        let subst: Vec<(ChcVar, ChcExpr)> =
            qparams.iter().cloned().zip(qargs.iter().cloned()).collect();
        conj.push(qformula.substitute(&subst));
    }
    if let Some(g) = &clause.body.constraint {
        conj.push(g.clone());
    }

    // Relate target params to head args:
    //  * invertible head arg  -> a substitution for its single clause variable;
    //  * clause-var-free head arg (a constant) -> a literal equality `t_i = harg`;
    //  * otherwise -> leave `t_i` UNCONSTRAINED. This is a sound over-
    //    approximation of the image (it only WEAKENS the target invariant). It is
    //    exactly what is needed for cone-of-influence-dead block-state arguments
    //    whose update is non-invertible (e.g. `d' = d + e`) but which the header
    //    invariant never reads: the dead param is simply left free. If such a
    //    clause variable also feeds the body relation (a LIVE position), it cannot
    //    be eliminated and the closed-over check below rejects the lift.
    let allowed: HashSet<ChcVar> = tparams.iter().cloned().collect();
    let mut sigma: Vec<(ChcVar, ChcExpr)> = Vec::new();
    // Non-invertible head-arg positions that still carry clause variables (e.g.
    // the MIR assert temp chain `_t = count & 1`, `_t2 = (_t == 1)`,
    // `_t3 = (acc == _t2)`): collected here and resolved AFTER the invertible
    // substitution `sigma` is complete, so each can be expressed over the other
    // (invertible) head-arg positions.
    let mut complex: Vec<(ChcExpr, ChcExpr)> = Vec::new();
    // A clause variable may appear invertibly in MORE THAN ONE head position
    // (e.g. `bb4(.., count+1, .., count)`: `count` at the `+1` position AND the
    // identity position). The FIRST occurrence supplies the substitution; each
    // FURTHER occurrence must emit the EQUALITY linking the two inverse
    // expressions (`t_i' - 1 == t_j'`), or the cross-position correlation
    // (`pos2 == pos4 + 1`) is silently dropped and a downstream consecution that
    // reads the duplicated state via either position fails.
    let mut seen: HashMap<ChcVar, ChcExpr> = HashMap::new();
    let mut link_eqs: Vec<ChcExpr> = Vec::new();
    for (t, harg) in tparams.iter().zip(headargs.iter()) {
        let t_expr = ChcExpr::var(t.clone());
        match invert_head_arg(harg, &t_expr) {
            Some((var, value)) => match seen.get(&var) {
                Some(prev) => link_eqs.push(ChcExpr::eq(prev.clone(), value.clone())),
                None => {
                    seen.insert(var.clone(), value.clone());
                    sigma.push((var, value));
                }
            },
            None if harg.vars().is_empty() => conj.push(ChcExpr::eq(t_expr, harg.clone())),
            None => complex.push((t_expr, harg.clone())),
        }
    }

    // Recover correlation for the non-invertible positions: keep the EXACT
    // equality `t_i = harg` with `sigma` applied IFF it then references only
    // target params (so e.g. `_t2 = ((count & 1) == 1)` stays correlated because
    // `count`/`acc` are themselves invertible head args mapped by `sigma`). If a
    // residual clause-local var remains, DROP it (leave `t_i` unconstrained) — a
    // sound over-approximation, exactly as for cone-of-influence-dead block state
    // (`d' = d + e`). This only ADDS true facts of the forward image (`t_i` does
    // equal `harg` in the image), so the candidate stays an over-approximation of
    // the image; the unchanged trusted validator re-checks init/consec/safety.
    let mut extras: Vec<ChcExpr> = Vec::new();
    for (t_expr, harg) in &complex {
        let eq_applied = ChcExpr::eq(t_expr.clone(), harg.clone()).substitute(&sigma);
        if eq_applied.vars().into_iter().all(|v| allowed.contains(&v)) {
            extras.push(eq_applied);
        }
    }

    // Apply `sigma` then FLATTEN the body relation into atomic conjuncts (descending
    // through `And` nodes), so a definition nested inside a body predicate's
    // interpretation is visible to the equality-elimination below.
    let mut atoms: Vec<ChcExpr> = Vec::new();
    for c in conj {
        flatten_conjuncts(&c.substitute(&sigma), &mut atoms);
    }

    // EQUALITY-ELIMINATION of leftover (non-target) clause variables that the body
    // relation already DEFINES. Head-arg inversion (`sigma`) maps each target param
    // back to a single body var, but an intermediate value can stay live as a
    // SEPARATE body var related to a target only through an equality in the body
    // invariant. Concretely, when `acc = f(acc, …)` is lowered with the call in one
    // block and its store in the next, the call-result value (a target/head arg) and
    // the OLD cell value (a body var) coexist in the call block's invariant as the
    // link equality `cell_old == not(call_result)`. `cell_old` is then a leftover the
    // head-arg inversion cannot reach. Here we eliminate any such leftover whose value
    // is FIXED by an equality `w == val` (in either orientation, modulo the same
    // invertible functions `invert_head_arg` already understands) with `val` over
    // target params only. This is an EXACT rewrite under an asserted equality (never a
    // weakening), so it preserves the image; the produced model is still re-validated
    // by the UNCHANGED kernel against the original transition, so an erroneous
    // elimination can only lose a proof, never forge one. Iterate to a fixpoint
    // (bounded by the atom count; each step strictly removes one leftover and
    // introduces none, since `val` is target-only).
    for _ in 0..=atoms.len().saturating_add(1) {
        let leftover_now: HashSet<ChcVar> = ChcExpr::and_all(atoms.clone())
            .vars()
            .into_iter()
            .filter(|v| !allowed.contains(v))
            .collect();
        if leftover_now.is_empty() {
            break;
        }
        let mut elim: Option<(ChcVar, ChcExpr)> = None;
        'find: for c in &atoms {
            let ChcExpr::Op(ChcOp::Eq, args) = c else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let sides = [
                (args[0].as_ref(), args[1].as_ref()),
                (args[1].as_ref(), args[0].as_ref()),
            ];
            for (lhs, rhs) in sides {
                let Some((w, val)) = invert_head_arg(lhs, rhs) else {
                    continue;
                };
                // `w` must be a leftover and `val` expressed purely over target
                // params (so the substitution cannot reintroduce a non-target var,
                // which also rules out a circular `w == f(w)`).
                if leftover_now.contains(&w) && val.vars().iter().all(|v| allowed.contains(v)) {
                    elim = Some((w, val));
                    break 'find;
                }
            }
        }
        let Some((w, val)) = elim else { break };
        let sub = [(w, val)];
        for c in &mut atoms {
            *c = c.substitute(&sub);
        }
    }

    let applied = ChcExpr::and_all(atoms);
    // All clause-local variables in the body relation must have been eliminated;
    // only target params may remain (a genuinely live non-invertible body var
    // cannot be eliminated and correctly rejects the lift).
    let leftover: Vec<ChcVar> = applied
        .vars()
        .into_iter()
        .filter(|v| !allowed.contains(v))
        .collect();
    if !leftover.is_empty() {
        if dbg {
            eprintln!(
                "IC3_EDGE: leftover non-target vars {:?} after substitution (headargs={:?}); these clause-local vars could not be eliminated -> None",
                leftover.iter().map(|v| v.name.clone()).collect::<Vec<_>>(),
                headargs
            );
        }
        return None;
    }
    if extras.is_empty() && link_eqs.is_empty() {
        Some(applied)
    } else {
        let mut all = Vec::with_capacity(1 + extras.len() + link_eqs.len());
        all.push(applied);
        all.extend(extras);
        all.extend(link_eqs);
        Some(ChcExpr::and_all(all))
    }
}

/// Collect the atomic conjuncts of `e` into `out`, descending recursively through
/// nested `And` nodes. A non-`And` expression contributes itself. Used by the
/// lift's equality-elimination so an equality nested inside a body predicate's
/// (conjunctive) interpretation is visible as a top-level atom.
fn flatten_conjuncts(e: &ChcExpr, out: &mut Vec<ChcExpr>) {
    match e {
        ChcExpr::Op(ChcOp::And, args) => {
            for a in args {
                flatten_conjuncts(a.as_ref(), out);
            }
        }
        other => out.push(other.clone()),
    }
}

/// Constant-fold a head-arg expression into the invertible shape
/// [`invert_head_arg`] understands, folding a CONSTANT-condition `Ite` and the
/// boolean not-equal forms:
///   `Ite(true, x, y) -> x`, `Ite(false, x, y) -> y`,
///   `Not(v == true) / v != true -> !v`, `Not(v == false) / v != false -> v`.
/// Recurses through the taken `Ite` branch so `Ite(true, Not(acc), acc) -> !acc`.
/// A pure syntactic simplification (semantics-preserving); returns the input
/// unchanged when no fold applies.
fn fold_invertible(harg: &ChcExpr) -> ChcExpr {
    match harg {
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => match as_bool_const(args[0].as_ref()) {
            Some(true) => fold_invertible(args[1].as_ref()),
            Some(false) => fold_invertible(args[2].as_ref()),
            None => harg.clone(),
        },
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            if let ChcExpr::Op(ChcOp::Eq, e) = args[0].as_ref() {
                if e.len() == 2 {
                    if let Some((v, c)) = var_and_boolconst(e[0].as_ref(), e[1].as_ref()) {
                        // Not(v == true) = !v ; Not(v == false) = v
                        return if c {
                            ChcExpr::not(ChcExpr::var(v))
                        } else {
                            ChcExpr::var(v)
                        };
                    }
                }
            }
            harg.clone()
        }
        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
            if let Some((v, c)) = var_and_boolconst(args[0].as_ref(), args[1].as_ref()) {
                // v != true = !v ; v != false = v
                return if c {
                    ChcExpr::not(ChcExpr::var(v))
                } else {
                    ChcExpr::var(v)
                };
            }
            harg.clone()
        }
        _ => harg.clone(),
    }
}

/// If exactly one of `a`/`c` is a `Var` and the other a Boolean constant (a
/// `Bool` literal or `Not(Bool)`), return `(var, const_value)`.
fn var_and_boolconst(a: &ChcExpr, c: &ChcExpr) -> Option<(ChcVar, bool)> {
    if let ChcExpr::Var(v) = a {
        if let Some(b) = as_bool_const(c) {
            return Some((v.clone(), b));
        }
    }
    if let ChcExpr::Var(v) = c {
        if let Some(b) = as_bool_const(a) {
            return Some((v.clone(), b));
        }
    }
    None
}

/// If `harg` is an invertible function of a single variable `x` (so that
/// `t = harg` can be rewritten as `x = f^{-1}(t)`), return `(x, f^{-1}(t))`.
/// Handles identity, boolean `not`, boolean `Ite` select, `+const`/`-const`
/// (Int and BitVec), `xor`-const, bitwise `~`, and unary `-`. Returns `None`
/// otherwise.
fn invert_head_arg(harg: &ChcExpr, t: &ChcExpr) -> Option<(ChcVar, ChcExpr)> {
    // Constant-fold the head arg into an invertible shape FIRST. The genuine
    // summarized bool `^` (e.g. `acc = xor_accumulate_parity(acc, true)`) lowers to
    // a CONSTANT-condition select `Ite(true, Not(acc), acc)` (`Select(b, !a, a)`
    // with `b = true`) and the ay-bindings builders never fold it, so it reaches
    // here un-simplified. `Ite(true, x, y) -> x`, `Ite(false, x, y) -> y`, and the
    // bool-not-eq forms `Not(v == c)` / `v != c` (`v != true -> !v`,
    // `v != false -> v`) collapse to the plain `Var`/`Not(Var)` shapes the arms
    // below already invert. Folding is an exact rewrite; it can only recover an
    // inversion, never forge one (the candidate is re-validated word-level).
    let folded = fold_invertible(harg);
    match &folded {
        ChcExpr::Var(v) => Some((v.clone(), t.clone())),
        ChcExpr::Op(op, args) => match (op, args.as_slice()) {
            (ChcOp::Not, [a]) => {
                let ChcExpr::Var(v) = a.as_ref() else {
                    return None;
                };
                Some((v.clone(), ChcExpr::not(t.clone())))
            }
            (ChcOp::BvNot, [a]) => {
                let ChcExpr::Var(v) = a.as_ref() else {
                    return None;
                };
                Some((
                    v.clone(),
                    ChcExpr::Op(ChcOp::BvNot, vec![Arc::new(t.clone())]),
                ))
            }
            (ChcOp::Neg, [a]) => {
                let ChcExpr::Var(v) = a.as_ref() else {
                    return None;
                };
                Some((
                    v.clone(),
                    ChcExpr::Op(ChcOp::Neg, vec![Arc::new(t.clone())]),
                ))
            }
            (ChcOp::BvNeg, [a]) => {
                let ChcExpr::Var(v) = a.as_ref() else {
                    return None;
                };
                Some((
                    v.clone(),
                    ChcExpr::Op(ChcOp::BvNeg, vec![Arc::new(t.clone())]),
                ))
            }
            // x XOR k => x = t XOR k (xor is its own inverse; k clause-var-free).
            (ChcOp::BvXor, [a, b]) => {
                if let ChcExpr::Var(v) = a.as_ref() {
                    if b.vars().is_empty() {
                        return Some((
                            v.clone(),
                            ChcExpr::Op(*op, vec![Arc::new(t.clone()), b.clone()]),
                        ));
                    }
                }
                if let ChcExpr::Var(v) = b.as_ref() {
                    if a.vars().is_empty() {
                        return Some((
                            v.clone(),
                            ChcExpr::Op(*op, vec![Arc::new(t.clone()), a.clone()]),
                        ));
                    }
                }
                None
            }
            // x + k  =>  x = t - k   (k a clause-var-free constant on either side)
            (ChcOp::Add | ChcOp::BvSub, [a, b]) | (ChcOp::BvAdd | ChcOp::Sub, [a, b]) => {
                let sub_op = match op {
                    ChcOp::Add => ChcOp::Sub,
                    ChcOp::BvAdd => ChcOp::BvSub,
                    ChcOp::Sub => ChcOp::Add,
                    ChcOp::BvSub => ChcOp::BvAdd,
                    _ => unreachable!(),
                };
                // var +/- const
                if let ChcExpr::Var(v) = a.as_ref() {
                    if b.vars().is_empty() {
                        return Some((
                            v.clone(),
                            ChcExpr::Op(sub_op, vec![Arc::new(t.clone()), b.clone()]),
                        ));
                    }
                }
                // const + var  (only for commutative add)
                if matches!(op, ChcOp::Add | ChcOp::BvAdd) {
                    if let ChcExpr::Var(v) = b.as_ref() {
                        if a.vars().is_empty() {
                            return Some((
                                v.clone(),
                                ChcExpr::Op(sub_op, vec![Arc::new(t.clone()), a.clone()]),
                            ));
                        }
                    }
                }
                None
            }
            // Ite(v, then_const, else_const) with `v` a Variable and both branches
            // Boolean constants is an invertible boolean select:
            //   Ite(v, true, false) == v   => v = t
            //   Ite(v, false, true) == !v  => v = !t
            // (MIR lowers `acc = acc ^ true` to `Ite(acc, false, true)`, where false
            // is `Not(Bool(true))`.) If both branches are equal it is a constant, not
            // a function of v, and is not invertible.
            (ChcOp::Ite, [cond, then_e, else_e]) => {
                let ChcExpr::Var(v) = cond.as_ref() else {
                    return None;
                };
                let then_b = as_bool_const(then_e.as_ref())?;
                let else_b = as_bool_const(else_e.as_ref())?;
                if then_b == else_b {
                    return None;
                }
                if then_b {
                    Some((v.clone(), t.clone()))
                } else {
                    Some((v.clone(), ChcExpr::not(t.clone())))
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// Interpret `e` as a Boolean constant if it is one syntactically: a `Bool`
/// literal, or `not` applied to one (the MIR `Not(Bool(true))` form for `false`).
fn as_bool_const(e: &ChcExpr) -> Option<bool> {
    match e {
        ChcExpr::Bool(b) => Some(*b),
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            as_bool_const(args[0].as_ref()).map(|b| !b)
        }
        _ => None,
    }
}

/// Eliminate clause-local temp variables from a query/guard constraint by
/// one-point substitution under their DEFINING equalities, leaving the constraint
/// expressed over the predicate's argument variables (`bound`) only.
///
/// A real loop-head assert loads the mutable cells into SSA temps and asserts over
/// them: `la == acc`, `lc == count`, then `Not(la == (lc & 1 == 1))`. Those temps
/// are NOT bound to the header args, so the bit-level encoder would otherwise mint
/// FRESH unconstrained SAT vars for them — disconnecting `bad`/`guard` from the
/// state latches (an empty / spuriously-wide cone-of-influence, and for the query
/// a spurious init `Unsafe`). Here we repeatedly find a conjunct `temp == expr`
/// (either orientation, modulo the invertible functions `invert_head_arg`
/// understands) whose `temp` is not a bound arg and whose `expr` is over bound args
/// only, DROP that conjunct, and substitute `temp := expr` into the rest — the
/// exact one-point rule (the same equality-elimination the lift's `edge_image`
/// already performs on body relations). Iterated to a fixpoint (each step removes
/// one temp and introduces none, since `expr` is bound-only).
///
/// Sound: substitution under an asserted equality preserves meaning, so this can
/// only sharpen `bad`/`guard` back onto the real state; the lane's candidate is
/// re-validated word-level regardless, so a mis-resolution can only miss a proof.
fn resolve_temps_to_args(constraint: &ChcExpr, bound: &HashSet<String>) -> ChcExpr {
    let mut atoms: Vec<ChcExpr> = Vec::new();
    flatten_conjuncts(constraint, &mut atoms);
    // Fixpoint bounded by the atom count (each iteration eliminates one temp).
    for _ in 0..=atoms.len() {
        let mut chosen: Option<(usize, ChcVar, ChcExpr)> = None;
        'scan: for (k, atom) in atoms.iter().enumerate() {
            let ChcExpr::Op(ChcOp::Eq, args) = atom else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            for (lhs, rhs) in [
                (args[0].as_ref(), args[1].as_ref()),
                (args[1].as_ref(), args[0].as_ref()),
            ] {
                if let Some((w, val)) = invert_head_arg(lhs, rhs) {
                    // `w` a clause-local temp; `val` over bound args only (so the
                    // substitution cannot reintroduce a temp — this also rules out a
                    // circular `w == f(w)`).
                    if !bound.contains(&w.name)
                        && val.vars().iter().all(|v| bound.contains(&v.name))
                    {
                        chosen = Some((k, w, val));
                        break 'scan;
                    }
                }
            }
        }
        let Some((k, w, val)) = chosen else { break };
        atoms.remove(k); // one-point: drop the consumed defining equality
        let sub = [(w, val)];
        for a in atoms.iter_mut() {
            *a = a.substitute(&sub);
        }
    }
    ChcExpr::and_all(atoms)
}

/// Variable names of the (simple-variable) predicate arguments `args` (non-`Var`
/// positions are skipped; `bind_in_args` has already required them all to be
/// simple vars before this is used).
fn arg_var_names(args: &[ChcExpr]) -> HashSet<String> {
    args.iter()
        .filter_map(|a| match a {
            ChcExpr::Var(v) => Some(v.name.clone()),
            _ => None,
        })
        .collect()
}

/// The lowered transition system plus the metadata needed to back-translate the
/// bit-level invariant into a word-level [`InvariantModel`].
pub(crate) struct Lowering {
    pub(crate) ts: BitLevelTransitionSystem,
    pred: PredicateId,
    /// Formal parameter variables for `P`, one per argument position. The
    /// reconstructed `PredicateInterpretation` is expressed over these
    /// (positional substitution at each use site).
    params: Vec<ChcVar>,
    /// Meaning of each state latch, indexed by latch index in `state_vars`.
    latches: Vec<LatchMeaning>,
    /// When the problem was a multi-block CFG that we collapsed by linearization,
    /// this is the ORIGINAL predicate id of the surviving loop header (the
    /// predicate whose word-level invariant the back-translated formula
    /// describes). `None` when the input was already single-predicate (then
    /// `pred` is already the original predicate id and the candidate validates
    /// directly). Used to LIFT the header invariant to a full multi-predicate
    /// model over the ORIGINAL predicates before the trusted re-validation.
    orig_header: Option<PredicateId>,
}

/// What a single bit-level latch stands for at the word level.
#[derive(Clone, Copy)]
struct LatchMeaning {
    /// Predicate argument position this latch belongs to.
    arg: usize,
    /// `None` => the whole `Bool` argument; `Some(i)` => bit `i` of an `Int` or
    /// `BitVec` argument (little-endian).
    bit: Option<usize>,
}

/// A bit-blasted value flowing through the encoder: either a single Boolean
/// literal or a little-endian vector of bit literals (an `Int` at [`INT_WIDTH`]
/// or a `BitVec(w)` at the width [`blast_width`] gives for `w`; the width is
/// the vector length).
enum Val {
    Bool(Literal),
    Int(Vec<Literal>),
}

/// Mutable CNF builder over a flat SAT variable space.
struct Builder {
    next: u32,
    init: Vec<Vec<Literal>>,
    trans: Vec<Vec<Literal>>,
    /// Directed combinational fan-in: `deps[out]` = the SAT variables that feed
    /// gate output `out`. Recorded as each Tseitin gate is built. Used to compute
    /// the cone-of-influence of the bad property over state latches (a *directed*
    /// output->inputs graph, NOT an undirected share-a-clause graph: the shared
    /// stutter `guard` literal fans OUT to every latch's ITE, so an undirected
    /// walk would leak the whole state through it).
    deps: HashMap<u32, Vec<u32>>,
    /// Known constant value of a SAT variable (set by [`mk_const`]). Drives the
    /// constant folding in the gate helpers: `count[i] & 0` folds to `0` with NO
    /// fan-in to `count[i]`, so the cone-of-influence does not mark dead masked
    /// bits live (e.g. `(bvand count 1)` keeps only bit 0). Folding is
    /// semantically exact and the lane's candidate is re-validated regardless.
    consts: HashMap<u32, bool>,
}

impl Builder {
    fn fresh(&mut self) -> Variable {
        let v = Variable::new(self.next);
        self.next += 1;
        v
    }

    /// Record that gate output `out` is combinationally driven by `inputs`.
    fn record(&mut self, out: Variable, inputs: &[Literal]) {
        self.deps.insert(
            out.index() as u32,
            inputs.iter().map(|l| l.variable().index() as u32).collect(),
        );
    }

    /// Constant value of `l` if its variable is a known constant (accounting for
    /// the literal's polarity), else `None`.
    fn cval(&self, l: Literal) -> Option<bool> {
        self.consts
            .get(&(l.variable().index() as u32))
            .map(|&v| if l.is_positive() { v } else { !v })
    }
}

/// Encoding target: which clause list new Tseitin defs are appended to.
#[derive(Clone, Copy)]
enum Target {
    Init,
    Trans,
    /// Append to BOTH init and trans (used for the bad/query definition, which
    /// must be visible to the init-state solver and the transition solver).
    Both,
}

/// Number of latches the given sort occupies.
fn sort_width(sort: &ChcSort) -> Option<usize> {
    match sort {
        ChcSort::Bool => Some(1),
        ChcSort::Int => Some(INT_WIDTH),
        ChcSort::BitVec(w) => Some(blast_width(*w)),
        _ => None,
    }
}

fn lower_loop(problem: &ChcProblem) -> Option<Lowering> {
    // (a) LINEARIZE: collapse a multi-block CFG to a single recursive predicate.
    // A single-predicate problem is already in the driven form.
    let dbg = std::env::var_os("TRUST_IC3_LANE_DEBUG").is_some();
    let linearized;
    let mut orig_header: Option<PredicateId> = None;
    let problem: &ChcProblem = if problem.predicates().len() > 1 {
        match linearize_to_single_loop(problem) {
            Some((l, header)) => {
                orig_header = Some(header);
                linearized = l;
                &linearized
            }
            None => {
                if dbg {
                    eprintln!(
                        "IC3_LANE: linearize FAILED (preds={})",
                        problem.predicates().len()
                    );
                }
                return None;
            }
        }
    } else {
        problem
    };

    // Exactly one predicate; every argument a blastable sort.
    let preds = problem.predicates();
    if preds.len() != 1 {
        if dbg {
            eprintln!("IC3_LANE: after-linearize preds={} != 1", preds.len());
        }
        return None;
    }
    let pred = &preds[0];
    let arity = pred.arg_sorts.len();
    if arity == 0 {
        return None;
    }
    let pid = pred.id;

    // Latch layout: contiguous per argument. `arg_offset[i]` is the first
    // current-state latch of argument `i`; `arg_width[i]` its latch count.
    let mut arg_offset = Vec::with_capacity(arity);
    let mut arg_width = Vec::with_capacity(arity);
    let mut latches: Vec<LatchMeaning> = Vec::new();
    for (i, sort) in pred.arg_sorts.iter().enumerate() {
        let w = match sort_width(sort) {
            Some(w) => w,
            None => {
                if dbg {
                    eprintln!("IC3_LANE: unblastable arg sort {sort:?}");
                }
                return None;
            }
        };
        arg_offset.push(latches.len());
        arg_width.push(w);
        if matches!(sort, ChcSort::Bool) {
            latches.push(LatchMeaning { arg: i, bit: None });
        } else {
            // Int / BitVec: one latch per (little-endian) bit.
            for bit in 0..w {
                latches.push(LatchMeaning {
                    arg: i,
                    bit: Some(bit),
                });
            }
        }
    }
    let total_latches = latches.len();

    // Partition clauses.
    let mut facts = Vec::new();
    let mut transitions = Vec::new();
    let mut queries = Vec::new();
    for clause in problem.clauses() {
        let body_preds = &clause.body.predicates;
        match &clause.head {
            ClauseHead::Predicate(h, args) if *h == pid => {
                if body_preds.is_empty() {
                    facts.push((args, clause.body.constraint.as_ref()));
                } else if body_preds.len() == 1 && body_preds[0].0 == pid {
                    transitions.push((&body_preds[0].1, args, clause.body.constraint.as_ref()));
                } else {
                    if dbg {
                        eprintln!(
                            "IC3_LANE: lower_loop None @gate915 (non-linear P-head: body_preds.len()={}, ids={:?})",
                            body_preds.len(),
                            body_preds.iter().map(|(p, _)| *p).collect::<Vec<_>>()
                        );
                    }
                    return None; // unexpected body shape
                }
            }
            ClauseHead::False => {
                if body_preds.is_empty() {
                    // A predicate-free `constraint -> false` clause. Linearizing
                    // a CFG resolves the entry directly into the error along the
                    // pre-loop path, producing such a global init-level
                    // assertion (typically infeasible). It does not constrain
                    // the loop predicate; skip it. This lane is candidate-only,
                    // so omitting an init assertion can at worst yield a
                    // candidate the trusted word-level validator rejects — never
                    // a false proof.
                } else if body_preds.len() == 1 && body_preds[0].0 == pid {
                    queries.push((&body_preds[0].1, clause.body.constraint.as_ref()));
                } else {
                    if dbg {
                        eprintln!(
                            "IC3_LANE: lower_loop None @gate928 (False-head non-single body: len={})",
                            body_preds.len()
                        );
                    }
                    return None;
                }
            }
            _ => {
                if dbg {
                    eprintln!("IC3_LANE: lower_loop None @gate932 (other head shape)");
                }
                return None;
            }
        }
    }

    if facts.is_empty() || transitions.is_empty() || queries.is_empty() {
        if dbg {
            eprintln!(
                "IC3_LANE: lower_loop None @gate938 (facts={} transitions={} queries={})",
                facts.len(),
                transitions.len(),
                queries.len()
            );
        }
        return None;
    }

    let state_vars: Vec<Variable> = (0..total_latches as u32).map(Variable::new).collect();
    let next_vars: Vec<Variable> = (total_latches as u32..2 * total_latches as u32)
        .map(Variable::new)
        .collect();
    let mut b = Builder {
        next: 2 * total_latches as u32,
        init: Vec::new(),
        trans: Vec::new(),
        deps: HashMap::new(),
        consts: HashMap::new(),
    };

    // --- Init = ⋁ facts: the union of every entry fact `P(args) <- constraint` ---
    //
    // Each fact `k` contributes one disjunct literal `f_k` that asserts "the state
    // latches equal this fact's encoded args AND (if present) the fact constraint
    // holds". `init` is then the single clause `⋁_k f_k`.
    //
    // REDUCTION EQUIVALENCE (facts.len() == 1): the clause is `[f_0]`, i.e. `f_0`
    // is forced true. Forcing `f_0` propagates (through the Tseitin definitions of
    // the equality gates) to pin every state latch to the fact's encoded bit and to
    // assert the constraint — logically identical to the prior hard `bind_latches`
    // (`latch <=> bit`) plus the constraint unit clause.
    //
    // OVER-APPROXIMATION (facts.len() > 1): `⋁_k f_k` is EXACTLY the union of the
    // per-fact singleton states — precisely the real initial set of a loop with
    // several entry facts. It never admits a state outside that union, and never
    // drops one, so a `Safe` on this init soundly implies the real loop is safe.
    {
        let mut fact_lits: Vec<Literal> = Vec::with_capacity(facts.len());
        for (args, constraint) in &facts {
            if args.len() != arity {
                return None;
            }
            let mut env: HashMap<String, Val> = HashMap::new();
            // f_k = /\_i (latch_i == arg_i) [/\ constraint]. Seed with `true`.
            let mut f_k = mk_const(&mut b, Target::Init, true);
            for (i, a) in args.iter().enumerate() {
                let v = encode(a, &mut env, &mut b, Target::Init)?;
                let eq = match &v {
                    Val::Bool(lit) => {
                        if arg_width[i] != 1 {
                            return None;
                        }
                        mk_xnor(
                            &mut b,
                            Target::Init,
                            Literal::positive(state_vars[arg_offset[i]]),
                            *lit,
                        )
                    }
                    Val::Int(bits) => {
                        let latch_bits: Vec<Literal> = (0..arg_width[i])
                            .map(|bit| Literal::positive(state_vars[arg_offset[i] + bit]))
                            .collect();
                        int_eq(&mut b, Target::Init, &latch_bits, bits)?
                    }
                };
                f_k = mk_and(&mut b, Target::Init, f_k, eq);
            }
            if let Some(c) = constraint {
                let lit = encode_bool(c, &mut env, &mut b, Target::Init)?;
                f_k = mk_and(&mut b, Target::Init, f_k, lit);
            }
            fact_lits.push(f_k);
        }
        // init requires the state to be one of the facts' states: ⋁_k f_k.
        b.init.push(fact_lits);
    }

    // --- Transition: T = ⋁_t T_t  (disjunctive, one T_t per body transition) ---
    //
    // A real branching loop body (a nondeterministic branch per iteration) lowers
    // to SEVERAL self-recursive transitions `P(in) /\ guard_t -> P(out_t)` over the
    // same predicate. We encode the transition relation as a NONDETERMINISTIC
    // CHOICE among the guard-enabled branches, or stutter:
    //
    //   next_i <=> ITE(sel_1, out_1_i, ITE(sel_2, out_2_i, ... , current_i))
    //
    // where `sel_t = s_t /\ guard_t`, `s_t` a FRESH unconstrained selector input
    // (the nondeterministic branch choice) and `guard_t` transition `t`'s residual
    // guard. The innermost else is the CURRENT-state bit — a stutter self-loop taken
    // when no branch is selected/enabled.
    //
    // Each residual `constraint` is a PURE GUARD over current-state variables
    // (data-flow lives in `out_args` as explicit expressions; see `resolve`), and we
    // do NOT assert any guard as a current-state unit clause. A hard current-state
    // assertion would make every state the transition solver sees satisfy the guard,
    // hiding guard-violating states from the frontier bad-state check. Stuttering
    // keeps guard-violating states reachable (a self-loop adds no new state) so
    // bad-state reachability is EXACT.
    //
    // OVER-APPROXIMATION / SOUNDNESS: free selectors make the choice among enabled
    // branches (and whether to stutter at all) nondeterministic, so the encoded T
    // ADMITS every real branch's successor plus the (state-preserving) stutter — it
    // never REMOVES a real transition. A `Safe` on this T therefore soundly implies
    // the real loop is safe. REDUCTION (transitions.len() == 1): the chain collapses
    // to `next_i <=> ITE(s_1 /\ guard_1, out_1_i, current_i)` — the prior stuttering
    // single-update, only with the guard weakened by the free `s_1`. Since a stutter
    // self-loop adds no reachable state, the reachable set (hence every Safe/Unsafe
    // outcome and every inductive invariant) is UNCHANGED from the prior shape.
    {
        // Per transition: FRESH env, bind in-args to current latches, resolve+encode
        // its guard, mint a free selector s_t, form sel_t = s_t /\ guard_t, and encode
        // every out arg to a per-latch `Val`.
        let mut per_trans: Vec<(Literal, Vec<Val>)> = Vec::with_capacity(transitions.len());
        for (in_args, out_args, constraint) in &transitions {
            if in_args.len() != arity || out_args.len() != arity {
                return None;
            }
            let mut env: HashMap<String, Val> = HashMap::new();
            bind_in_args(in_args, &state_vars, &arg_offset, &arg_width, &mut env)?;
            let guard = match constraint {
                // Resolve any loaded-cell temps back onto this transition's in-args so
                // the guard is over current-state latches, not freshly-minted free bits.
                Some(c) => {
                    let resolved = resolve_temps_to_args(c, &arg_var_names(in_args));
                    encode_bool(&resolved, &mut env, &mut b, Target::Trans)?
                }
                None => mk_const(&mut b, Target::Trans, true),
            };
            // Fresh unconstrained selector: the nondeterministic branch choice.
            let s_t = Literal::positive(b.fresh());
            let sel = mk_and(&mut b, Target::Trans, s_t, guard);
            let mut outs = Vec::with_capacity(arity);
            for a in out_args.iter() {
                outs.push(encode(a, &mut env, &mut b, Target::Trans)?);
            }
            per_trans.push((sel, outs));
        }
        // For each latch/arg position, build the priority-ITE chain across transitions
        // with the current state as the final (stutter) else.
        for i in 0..arity {
            let per: Vec<(Literal, &Val)> = per_trans
                .iter()
                .map(|(sel, outs)| (*sel, &outs[i]))
                .collect();
            gate_next_disjunctive(
                &mut b,
                &state_vars,
                &next_vars,
                arg_offset[i],
                arg_width[i],
                &per,
            )?;
        }
    }

    // --- Bad/query: OR of all query bodies (over current state) ---
    let mut disjunct_lits = Vec::new();
    for (args, constraint) in &queries {
        if args.len() != arity {
            return None;
        }
        let mut env: HashMap<String, Val> = HashMap::new();
        bind_in_args(args, &state_vars, &arg_offset, &arg_width, &mut env)?;
        let lit = match constraint {
            // Resolve the assert-condition temp chain (`la == acc`, `lc == count`,
            // `Not(la == (lc & 1 == 1))`) down onto the query's arg vars so `bad`
            // fans into the acc/count[0] latches instead of fresh free bits.
            Some(c) => {
                let resolved = resolve_temps_to_args(c, &arg_var_names(args));
                encode_bool(&resolved, &mut env, &mut b, Target::Both)?
            }
            None => {
                // unconditionally bad: a true literal in both targets.
                mk_const(&mut b, Target::Both, true)
            }
        };
        disjunct_lits.push(lit);
    }
    // bad <=> OR(disjunct_lits), defined in BOTH init and trans.
    let bad = b.fresh();
    let mut c1 = vec![Literal::negative(bad)];
    c1.extend(disjunct_lits.iter().copied());
    let mut def_clauses = vec![c1];
    for l in &disjunct_lits {
        def_clauses.push(vec![l.negated(), Literal::positive(bad)]);
    }
    for c in &def_clauses {
        b.init.push(c.clone());
        b.trans.push(c.clone());
    }
    b.record(bad, &disjunct_lits); // bad driven by the query disjuncts
    let bad_literals = vec![Literal::positive(bad)];

    let total_vars = b.next as usize;
    let params: Vec<ChcVar> = pred
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, s)| ChcVar::new(format!("__ic3_p{i}"), s.clone()))
        .collect();

    // --- CONE-OF-INFLUENCE SLICE of the state latches ---
    //
    // The linearized header carries EVERY block-live variable as a latch (a real
    // targo-lowered `u64` loop blasts each `BitVec(64)` arg to BV_BLAST_CAP
    // latches across several CFG blocks). IC3 generalises/propagates cubes over
    // the STATE-latch set, so an over-wide state space (e.g. count[1..7] plus dead
    // block state) prevents convergence even though the bad property `acc XOR
    // count[0]` only reads `{acc, count[0]}`. We restrict the IC3 state set to the
    // backward COI of `bad` through the transition's combinational fan-in.
    //
    // SOUND: dropping a latch from the state set only FREES it (the transition
    // clauses that referenced it remain, now over an unconstrained variable) — an
    // over-approximation of the reachable set. For a SAFETY property whose cone
    // excludes that latch this changes nothing; in general it can only ADD
    // behaviours, so a sliced `Safe` implies the unsliced system is safe too. And
    // the back-translated candidate is re-validated word-level downstream, so a
    // too-aggressive slice can at worst miss a proof, never forge one.
    let coi = coi_state_latches(&b.deps, &bad_literals, total_latches);
    let coi_idx: Vec<usize> = (0..total_latches).filter(|&i| coi[i]).collect();

    // SOUNDNESS/ROBUSTNESS GUARD: decline when `bad` can be satisfiable yet fans in
    // to NO state latch. That happens when the query constraint references temps
    // that could not be resolved onto the arg latches (so the encoder minted free
    // bits) or an unsupported-instruction `... -> false` edge left a constant-true
    // disjunct. With no state fan-in, `init /\ bad` is trivially satisfiable and the
    // solver returns a SPURIOUS init `Unsafe` — never a usable Safe/candidate.
    // Declining is strictly sound: the lane is candidate-only, so a decline can only
    // miss a proof, never forge one (and it replaces a misleading `solve_safe=false`
    // with a clean `None`). We do NOT decline when `bad` is identically false (all
    // disjuncts fold to `false`): that is a genuinely safe empty query IC3 discharges
    // trivially.
    let bad_maybe_sat = disjunct_lits.iter().any(|l| b.cval(*l) != Some(false));
    if total_latches > 0 && coi_idx.is_empty() && bad_maybe_sat {
        if dbg {
            eprintln!(
                "IC3_LANE: lower_loop None @coi-empty (bad has no state-latch fan-in; declining, candidate-only)"
            );
        }
        return None;
    }
    // `TRUST_IC3_LANE_NOSLICE` disables the slice (A/B measurement only; the slice
    // is always sound — see the contract above).
    let slice = std::env::var_os("TRUST_IC3_LANE_NOSLICE").is_none()
        && !coi_idx.is_empty()
        && coi_idx.len() < total_latches;
    if std::env::var_os("TRUST_IC3_LANE_DEBUG").is_some() {
        eprintln!(
            "IC3_LANE: coi_slice latches {}->{} (sliced={slice})",
            total_latches,
            coi_idx.len()
        );
    }
    let (num_state, sliced_state, sliced_next) = if slice {
        (
            coi_idx.len(),
            coi_idx.iter().map(|&i| state_vars[i]).collect(),
            coi_idx.iter().map(|&i| next_vars[i]).collect(),
        )
    } else {
        (total_latches, state_vars, next_vars)
    };

    let ts = BitLevelTransitionSystem::new(
        num_state,
        0,
        sliced_state,
        sliced_next,
        Vec::new(),
        b.init,
        b.trans,
        bad_literals,
        total_vars,
    );

    Some(Lowering {
        ts,
        pred: pid,
        params,
        latches,
        orig_header,
    })
}

// ---------------------------------------------------------------------------
// (a) CFG linearization: collapse a multi-block single-loop CHC to one
// recursive predicate by Gaussian/unfold elimination.
// ---------------------------------------------------------------------------

/// A mutable working clause during elimination.
#[derive(Clone)]
struct WClause {
    body: Vec<(PredicateId, Vec<ChcExpr>)>,
    constraint: Option<ChcExpr>,
    head: ClauseHead,
}

/// Linearize a multi-block (one-relation-per-basic-block) single-loop CHC into a
/// problem with exactly one self-recursive predicate, by resolving away every
/// predicate that is not directly self-recursive.
///
/// Returns `None` if the system is outside the supported fragment (more than one
/// residual recursive predicate — e.g. nested/parallel loops — or a clause that
/// uses the same predicate twice in its body).
///
/// Untrusted: the collapsed problem is only a candidate model; any invariant it
/// yields is re-validated against the ORIGINAL problem's word-level transition.
///
/// On success returns `(collapsed_problem, original_survivor_id)` where the
/// second element is the ORIGINAL predicate id of the surviving loop header (the
/// `r` below, before it is remapped to a fresh id in the collapsed problem). The
/// caller needs it to LIFT the header invariant back onto every original
/// predicate (see [`lift_header_to_full_model`]).
fn linearize_to_single_loop(problem: &ChcProblem) -> Option<(ChcProblem, PredicateId)> {
    let mut clauses: Vec<WClause> = problem
        .clauses()
        .iter()
        .map(|c| WClause {
            body: c.body.predicates.clone(),
            constraint: c.body.constraint.clone(),
            head: c.head.clone(),
        })
        .collect();

    // Protect the loop header(s) so the *header* survives each loop SCC (its
    // invariant is the one stated at the loop head, e.g. `acc <=> count[0]`). A
    // header is a recursive predicate with an in-edge from outside its SCC
    // (the entry edge); if an SCC has no such member, its lowest-id member is
    // protected. Computed once over the original call graph; ids are stable
    // until the final rebuild.
    let protected = protected_headers(&clauses);

    let mut suffix_ctr: usize = 0;
    loop {
        // Pick any still-referenced predicate that is not *directly* self-
        // recursive and not a protected header. Eliminating it preserves the
        // loop structure: when the penultimate SCC member is removed, the
        // resolvent makes the protected header self-recursive, so exactly one
        // recursive predicate per loop remains.
        let referenced = collect_referenced(&clauses);
        let candidate = referenced
            .iter()
            .copied()
            .find(|&q| !is_self_recursive(&clauses, q) && !protected.contains(&q));
        let Some(q) = candidate else { break };
        eliminate(&mut clauses, q, &mut suffix_ctr)?;
    }

    // All survivors must now be directly self-recursive; require exactly one.
    let referenced = collect_referenced(&clauses);
    if referenced.len() != 1 {
        return None;
    }
    let r = referenced[0];

    // Rebuild a single-predicate problem; remap the survivor to its fresh id.
    let r_pred = problem.get_predicate(r)?;
    let mut out = ChcProblem::new();
    let new_pid = out.declare_predicate(r_pred.name.clone(), r_pred.arg_sorts.clone());

    for wc in clauses {
        let mut body = Vec::with_capacity(wc.body.len());
        for (p, args) in wc.body {
            if p != r {
                return None; // a non-survivor predicate leaked: unsupported
            }
            body.push((new_pid, args));
        }
        let head = match wc.head {
            ClauseHead::Predicate(h, args) => {
                if h != r {
                    return None;
                }
                ClauseHead::Predicate(new_pid, args)
            }
            ClauseHead::False => ClauseHead::False,
        };
        out.add_clause(HornClause::new(ClauseBody::new(body, wc.constraint), head));
    }
    Some((out, r))
}

/// Predicates that appear in any clause head or body, first-seen order.
fn collect_referenced(clauses: &[WClause]) -> Vec<PredicateId> {
    let mut seen = Vec::new();
    let push = |p: PredicateId, seen: &mut Vec<PredicateId>| {
        if !seen.contains(&p) {
            seen.push(p);
        }
    };
    for c in clauses {
        for (p, _) in &c.body {
            push(*p, &mut seen);
        }
        if let ClauseHead::Predicate(h, _) = &c.head {
            push(*h, &mut seen);
        }
    }
    seen
}

/// Whether `q` appears in the body of one of its own defining clauses.
fn is_self_recursive(clauses: &[WClause], q: PredicateId) -> bool {
    clauses.iter().any(|c| {
        matches!(&c.head, ClauseHead::Predicate(h, _) if *h == q)
            && c.body.iter().any(|(p, _)| *p == q)
    })
}

/// Loop headers to protect from elimination: one representative per nontrivial
/// SCC of the predicate call graph (preferring a member with an external
/// predecessor — the natural loop head). Eliminating everything else collapses
/// each loop SCC onto its header, whose invariant is the loop-head invariant.
fn protected_headers(clauses: &[WClause]) -> HashSet<PredicateId> {
    // Call-graph adjacency: body predicate `q` -> head predicate `h`.
    let mut adj: HashMap<PredicateId, HashSet<PredicateId>> = HashMap::new();
    let mut nodes: HashSet<PredicateId> = HashSet::new();
    for c in clauses {
        for (q, _) in &c.body {
            nodes.insert(*q);
        }
        if let ClauseHead::Predicate(h, _) = &c.head {
            nodes.insert(*h);
            for (q, _) in &c.body {
                adj.entry(*q).or_default().insert(*h);
            }
        }
    }

    // Forward reachability per node (transitive closure via DFS).
    let reach_of: HashMap<PredicateId, HashSet<PredicateId>> = nodes
        .iter()
        .map(|&start| {
            let mut seen = HashSet::new();
            let mut stack = vec![start];
            while let Some(n) = stack.pop() {
                if let Some(succ) = adj.get(&n) {
                    for &m in succ {
                        if seen.insert(m) {
                            stack.push(m);
                        }
                    }
                }
            }
            (start, seen)
        })
        .collect();

    let recursive = |p: PredicateId| reach_of[&p].contains(&p);
    let same_scc =
        |p: PredicateId, q: PredicateId| reach_of[&p].contains(&q) && reach_of[&q].contains(&p);

    let mut protected: HashSet<PredicateId> = HashSet::new();
    // Headers: recursive predicate with a predecessor outside its SCC.
    for c in clauses {
        if let ClauseHead::Predicate(h, _) = &c.head {
            if recursive(*h) && c.body.iter().any(|(q, _)| !same_scc(*h, *q)) {
                protected.insert(*h);
            }
        }
    }
    // Ensure every nontrivial SCC has a protected member (fallback: lowest id).
    let recs: Vec<PredicateId> = nodes.iter().copied().filter(|&p| recursive(p)).collect();
    for &p in &recs {
        let scc: Vec<PredicateId> = recs.iter().copied().filter(|&q| same_scc(p, q)).collect();
        if !scc.iter().any(|m| protected.contains(m)) {
            if let Some(&m) = scc.iter().min_by_key(|m| m.index()) {
                protected.insert(m);
            }
        }
    }
    protected
}

/// Resolve away predicate `q`: replace every use of `q` in a body with each of
/// `q`'s definitions, then drop `q`'s defining clauses. `q` must not be directly
/// self-recursive (guaranteed by the caller).
fn eliminate(clauses: &mut Vec<WClause>, q: PredicateId, ctr: &mut usize) -> Option<()> {
    let defs: Vec<WClause> = clauses
        .iter()
        .filter(|c| matches!(&c.head, ClauseHead::Predicate(h, _) if *h == q))
        .cloned()
        .collect();

    let mut out = Vec::new();
    for c in std::mem::take(clauses) {
        if matches!(&c.head, ClauseHead::Predicate(h, _) if *h == q) {
            continue; // a definition of q: consumed by resolution
        }
        let occ: Vec<usize> = c
            .body
            .iter()
            .enumerate()
            .filter(|(_, (p, _))| *p == q)
            .map(|(i, _)| i)
            .collect();
        match occ.len() {
            0 => out.push(c),
            1 => {
                let j = occ[0];
                if defs.is_empty() {
                    // q is unconstrained (no definition): treat as `true` and
                    // drop the body occurrence (sound over-approximation; a
                    // missed candidate at worst).
                    let mut cc = c.clone();
                    cc.body.remove(j);
                    out.push(cc);
                } else {
                    for d in &defs {
                        *ctr += 1;
                        out.push(resolve(&c, j, d, q, *ctr)?);
                    }
                }
            }
            _ => return None, // same predicate twice in one body: unsupported
        }
    }
    *clauses = out;
    Some(())
}

/// Resolvent of use-clause `u` (body slot `j` is `q(s)`) against definition `d`
/// (head `q(t)`), by SUBSTITUTION (proper Gaussian/unfold elimination): the use
/// arguments `s` must be distinct simple variables, so unifying `q(s)` with the
/// definition's `q(t)` is the substitution `σ = {s_k ↦ t_k}`. `σ` is applied to
/// the rest of `u` (its other body predicates, constraint, and head); `d`'s body
/// and constraint (variables renamed fresh to avoid capture) are spliced in.
///
/// Substitution (rather than introducing equalities) keeps the data-flow
/// (e.g. `count + 1`) inside the resulting *head arguments* as explicit
/// expressions, leaving the residual constraint a PURE GUARD over current-state
/// variables. That separation lets the transition be lowered with a stuttering
/// guard (a total transition that never constrains the current state) instead of
/// a hard current-state assertion that would hide states from the model checker.
fn resolve(u: &WClause, j: usize, d: &WClause, q: PredicateId, ctr: usize) -> Option<WClause> {
    // Use arguments must be distinct simple variables for substitution.
    let s = &u.body[j].1;
    let mut names: Vec<String> = Vec::with_capacity(s.len());
    for a in s {
        match a {
            ChcExpr::Var(v) => {
                if names.contains(&v.name) {
                    return None; // repeated argument variable: unsupported
                }
                names.push(v.name.clone());
            }
            _ => return None, // non-variable argument: unsupported
        }
    }

    let suf = format!("$e{ctr}");
    let d_body: Vec<(PredicateId, Vec<ChcExpr>)> = d
        .body
        .iter()
        .map(|(p, args)| (*p, args.iter().map(|a| rename_expr(a, &suf)).collect()))
        .collect();
    let d_constraint = d.constraint.as_ref().map(|c| rename_expr(c, &suf));
    let t: Vec<ChcExpr> = match &d.head {
        ClauseHead::Predicate(h, args) if *h == q => {
            args.iter().map(|a| rename_expr(a, &suf)).collect()
        }
        _ => return None,
    };
    if t.len() != names.len() {
        return None;
    }
    let sigma: HashMap<String, ChcExpr> = names.into_iter().zip(t).collect();

    let mut body = Vec::with_capacity(u.body.len() - 1 + d_body.len());
    for (k, (p, args)) in u.body.iter().enumerate() {
        if k == j {
            continue;
        }
        body.push((*p, args.iter().map(|a| subst_expr(a, &sigma)).collect()));
    }
    body.extend(d_body);

    let mut conj = Vec::new();
    if let Some(c) = &u.constraint {
        conj.push(subst_expr(c, &sigma));
    }
    if let Some(c) = d_constraint {
        conj.push(c);
    }

    let head = match &u.head {
        ClauseHead::Predicate(h, args) => {
            ClauseHead::Predicate(*h, args.iter().map(|a| subst_expr(a, &sigma)).collect())
        }
        ClauseHead::False => ClauseHead::False,
    };

    Some(WClause {
        body,
        constraint: and_of(conj),
        head,
    })
}

/// Substitute variables by name with their mapped expressions.
fn subst_expr(e: &ChcExpr, sigma: &HashMap<String, ChcExpr>) -> ChcExpr {
    match e {
        ChcExpr::Var(v) => sigma.get(&v.name).cloned().unwrap_or_else(|| e.clone()),
        ChcExpr::Op(op, args) => ChcExpr::Op(
            *op,
            args.iter()
                .map(|a| Arc::new(subst_expr(a, sigma)))
                .collect(),
        ),
        other => other.clone(),
    }
}

/// Conjoin a list of constraints (`None` for the empty conjunction = `true`).
fn and_of(mut conj: Vec<ChcExpr>) -> Option<ChcExpr> {
    match conj.len() {
        0 => None,
        1 => Some(conj.pop().unwrap()),
        _ => Some(ChcExpr::Op(
            ChcOp::And,
            conj.into_iter().map(Arc::new).collect(),
        )),
    }
}

/// Rename every variable in `e` by appending `suf` (avoids capture when a
/// definition clause is spliced into a use clause). Only `Var`/`Op` carry
/// variables in linearized constraints; other leaves are cloned unchanged.
fn rename_expr(e: &ChcExpr, suf: &str) -> ChcExpr {
    match e {
        ChcExpr::Var(v) => ChcExpr::Var(ChcVar::new(format!("{}{}", v.name, suf), v.sort.clone())),
        ChcExpr::Op(op, args) => ChcExpr::Op(
            *op,
            args.iter().map(|a| Arc::new(rename_expr(a, suf))).collect(),
        ),
        other => other.clone(),
    }
}

/// Bind the recursive-call (`in`) argument variables to their current-state
/// latches in `env`. Each `in` argument must be a simple variable of the
/// matching sort/width.
fn bind_in_args(
    args: &[ChcExpr],
    state_vars: &[Variable],
    arg_offset: &[usize],
    arg_width: &[usize],
    env: &mut HashMap<String, Val>,
) -> Option<()> {
    for (i, a) in args.iter().enumerate() {
        match a {
            ChcExpr::Var(v) => {
                let w = sort_width(&v.sort)?;
                if w != arg_width[i] {
                    return None;
                }
                if matches!(v.sort, ChcSort::Bool) {
                    env.insert(
                        v.name.clone(),
                        Val::Bool(Literal::positive(state_vars[arg_offset[i]])),
                    );
                } else {
                    let bits: Vec<Literal> = (0..w)
                        .map(|bit| Literal::positive(state_vars[arg_offset[i] + bit]))
                        .collect();
                    env.insert(v.name.clone(), Val::Int(bits));
                }
            }
            _ => return None,
        }
    }
    Some(())
}

/// Constrain the next-state latch range `[offset, offset+width)` to a DISJUNCTIVE
/// guarded update across several candidate transitions:
///
///   next <=> ITE(sel_1, out_1, ITE(sel_2, out_2, ... ITE(sel_n, out_n, current)))
///
/// The first transition whose enabling literal `sel_k = s_k /\ guard_k` is true
/// drives the latch to that transition's output; if none is enabled the latch
/// STUTTERS (holds its current value — a self-loop that adds no reachable state).
/// Each `s_k` is a FREE selector input, so the choice among enabled branches (and
/// whether to stutter) is nondeterministic — an OVER-APPROXIMATION of the real
/// transition relation `T = ⋁_k T_k` (adds behaviours, never removes one). Encoded
/// on the transition target only.
///
/// With a single entry this is `next <=> ITE(sel_1, out_1, current)`, the prior
/// stuttering single-update (with the guard weakened by the free `s_1`, a strict
/// over-approximation).
///
/// `per_transition[k] = (sel_k, out_k)` is transition `k`'s enabling literal and
/// the `Val` it writes to THIS latch/arg position. `Val::Bool` requires `width == 1`
/// and `Val::Int` a `width`-bit vector.
fn gate_next_disjunctive(
    b: &mut Builder,
    state_vars: &[Variable],
    next_vars: &[Variable],
    offset: usize,
    width: usize,
    per_transition: &[(Literal, &Val)],
) -> Option<()> {
    for bit in 0..width {
        // Fold from the innermost stutter (current bit) outwards so transition 1 is
        // the outermost (highest-priority) ITE — iterate transitions in reverse.
        let mut chain = Literal::positive(state_vars[offset + bit]);
        for (sel, v) in per_transition.iter().rev() {
            let out_bit = match v {
                Val::Bool(lit) => {
                    if width != 1 {
                        return None;
                    }
                    *lit
                }
                Val::Int(bits) => {
                    if bits.len() != width {
                        return None;
                    }
                    bits[bit]
                }
            };
            chain = mk_ite(b, Target::Trans, *sel, out_bit, chain);
        }
        iff_clause(
            b,
            Target::Trans,
            Literal::positive(next_vars[offset + bit]),
            chain,
        );
        b.record(next_vars[offset + bit], &[chain]); // next latch driven by its update chain
    }
    Some(())
}

/// Append `o <=> l` clauses to the given target.
fn iff_clause(b: &mut Builder, target: Target, o: Literal, l: Literal) {
    push_target(b, target, vec![o.negated(), l]);
    push_target(b, target, vec![l.negated(), o]);
}

fn push_target(b: &mut Builder, target: Target, clause: Vec<Literal>) {
    match target {
        Target::Init => b.init.push(clause),
        Target::Trans => b.trans.push(clause),
        Target::Both => {
            b.init.push(clause.clone());
            b.trans.push(clause);
        }
    }
}

// ---------------------------------------------------------------------------
// Gate helpers (Tseitin). Each returns the literal naming the gate output.
// ---------------------------------------------------------------------------

/// A literal whose value is forced to `val` via a unit clause.
fn mk_const(b: &mut Builder, target: Target, val: bool) -> Literal {
    let f = b.fresh();
    let lit = Literal::positive(f);
    push_target(b, target, vec![if val { lit } else { lit.negated() }]);
    b.record(f, &[]); // constant: no state fan-in
    b.consts.insert(f.index() as u32, val);
    lit
}

/// `o <=> (a /\ c)`, constant-folded: `a & false = false`, `a & true = a`. When
/// a const operand collapses the gate there is NO fan-in to the other operand,
/// so the cone-of-influence does not mark dead masked bits live.
fn mk_and(b: &mut Builder, target: Target, a: Literal, c: Literal) -> Literal {
    match (b.cval(a), b.cval(c)) {
        (Some(false), _) | (_, Some(false)) => return mk_const(b, target, false),
        (Some(true), Some(true)) => return mk_const(b, target, true),
        (Some(true), _) => return c,
        (_, Some(true)) => return a,
        _ => {}
    }
    let o = b.fresh();
    let oo = Literal::positive(o);
    push_target(b, target, vec![oo.negated(), a]);
    push_target(b, target, vec![oo.negated(), c]);
    push_target(b, target, vec![oo, a.negated(), c.negated()]);
    b.record(o, &[a, c]);
    oo
}

/// `o <=> (a \/ c)`, constant-folded: `a | true = true`, `a | false = a`.
fn mk_or(b: &mut Builder, target: Target, a: Literal, c: Literal) -> Literal {
    match (b.cval(a), b.cval(c)) {
        (Some(true), _) | (_, Some(true)) => return mk_const(b, target, true),
        (Some(false), Some(false)) => return mk_const(b, target, false),
        (Some(false), _) => return c,
        (_, Some(false)) => return a,
        _ => {}
    }
    let o = b.fresh();
    let oo = Literal::positive(o);
    push_target(b, target, vec![oo, a.negated()]);
    push_target(b, target, vec![oo, c.negated()]);
    push_target(b, target, vec![oo.negated(), a, c]);
    b.record(o, &[a, c]);
    oo
}

/// `o <=> (a == c)` (XNOR), constant-folded: `true == c` is `c`, `false == c`
/// is `!c`.
fn mk_xnor(b: &mut Builder, target: Target, a: Literal, c: Literal) -> Literal {
    match (b.cval(a), b.cval(c)) {
        (Some(x), Some(y)) => return mk_const(b, target, x == y),
        (Some(true), _) => return c,
        (Some(false), _) => return c.negated(),
        (_, Some(true)) => return a,
        (_, Some(false)) => return a.negated(),
        _ => {}
    }
    let o = b.fresh();
    let oo = Literal::positive(o);
    push_target(b, target, vec![oo.negated(), a.negated(), c]);
    push_target(b, target, vec![oo.negated(), a, c.negated()]);
    push_target(b, target, vec![oo, a, c]);
    push_target(b, target, vec![oo, a.negated(), c.negated()]);
    b.record(o, &[a, c]);
    oo
}

/// `o <=> (a != c)` (XOR).
fn mk_xor(b: &mut Builder, target: Target, a: Literal, c: Literal) -> Literal {
    mk_xnor(b, target, a, c).negated()
}

/// `o <=> (s ? th : el)`, constant-folded on the selector and on equal branches.
fn mk_ite(b: &mut Builder, target: Target, s: Literal, th: Literal, el: Literal) -> Literal {
    match b.cval(s) {
        Some(true) => return th,
        Some(false) => return el,
        None => {}
    }
    if th == el {
        return th;
    }
    let o = b.fresh();
    let oo = Literal::positive(o);
    // s => (o <=> th)
    push_target(b, target, vec![s.negated(), oo.negated(), th]);
    push_target(b, target, vec![s.negated(), oo, th.negated()]);
    // !s => (o <=> el)
    push_target(b, target, vec![s, oo.negated(), el]);
    push_target(b, target, vec![s, oo, el.negated()]);
    b.record(o, &[s, th, el]);
    oo
}

/// Little-endian ripple-carry adder, wrapping at the operand width (carry-out
/// discarded). `a` and `c` must be the same length.
fn ripple_add(b: &mut Builder, target: Target, a: &[Literal], c: &[Literal]) -> Vec<Literal> {
    let mut carry = mk_const(b, target, false);
    let mut out = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        let axc = mk_xor(b, target, a[i], c[i]);
        let sum = mk_xor(b, target, axc, carry);
        let ac = mk_and(b, target, a[i], c[i]);
        let cc = mk_and(b, target, carry, axc);
        carry = mk_or(b, target, ac, cc);
        out.push(sum);
    }
    out
}

/// Bitwise NOT of `a`.
fn bit_not(a: &[Literal]) -> Vec<Literal> {
    a.iter().map(|l| l.negated()).collect()
}

/// Two's-complement subtraction `a - c`, wrapping at the operand width
/// (`a + ~c + 1`). `a` and `c` must be the same length.
fn ripple_sub(b: &mut Builder, target: Target, a: &[Literal], c: &[Literal]) -> Vec<Literal> {
    let nc = bit_not(c);
    let mut carry = mk_const(b, target, true);
    let mut out = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        let axc = mk_xor(b, target, a[i], nc[i]);
        let sum = mk_xor(b, target, axc, carry);
        let ac = mk_and(b, target, a[i], nc[i]);
        let cc = mk_and(b, target, carry, axc);
        carry = mk_or(b, target, ac, cc);
        out.push(sum);
    }
    out
}

/// Two's-complement negation `-a` (`~a + 1`).
fn ripple_neg(b: &mut Builder, target: Target, a: &[Literal]) -> Vec<Literal> {
    let zero: Vec<Literal> = (0..a.len()).map(|_| mk_const(b, target, false)).collect();
    ripple_sub(b, target, &zero, a)
}

/// Per-bit binary gate over equal-length operands.
fn bitwise<F>(
    b: &mut Builder,
    target: Target,
    a: &[Literal],
    c: &[Literal],
    f: F,
) -> Option<Vec<Literal>>
where
    F: Fn(&mut Builder, Target, Literal, Literal) -> Literal,
{
    if a.len() != c.len() {
        return None;
    }
    Some((0..a.len()).map(|i| f(b, target, a[i], c[i])).collect())
}

/// `o <=> (a == c)` over equal-length bit vectors (AND of per-bit XNOR).
fn int_eq(b: &mut Builder, target: Target, a: &[Literal], c: &[Literal]) -> Option<Literal> {
    if a.len() != c.len() {
        return None;
    }
    let mut acc = mk_const(b, target, true);
    for i in 0..a.len() {
        let e = mk_xnor(b, target, a[i], c[i]);
        acc = mk_and(b, target, acc, e);
    }
    Some(acc)
}

/// `o <=> (a < c)` unsigned, over equal-length bit vectors (LSB-first ripple).
fn unsigned_lt(b: &mut Builder, target: Target, a: &[Literal], c: &[Literal]) -> Option<Literal> {
    if a.len() != c.len() {
        return None;
    }
    let mut lt = mk_const(b, target, false);
    for i in 0..a.len() {
        let nac = mk_and(b, target, a[i].negated(), c[i]); // a_i < c_i
        let eq = mk_xnor(b, target, a[i], c[i]);
        let hi = mk_and(b, target, eq, lt);
        lt = mk_or(b, target, nac, hi);
    }
    Some(lt)
}

/// Little-endian bits of the integer constant `c` at `width` bits (low bits,
/// two's-complement for negatives).
fn int_const_bits(b: &mut Builder, target: Target, c: i128, width: usize) -> Vec<Literal> {
    // Bit-preserving reinterpretation (i128 -> u128, not a lossy narrowing);
    // the low-bit window is this untrusted lane's documented blast semantics
    // (candidates are re-validated word-level, see module docs).
    let u = c as u128;
    (0..width)
        .map(|i| mk_const(b, target, (u >> i) & 1 == 1))
        .collect()
}

/// Little-endian bits of the bit-vector constant `value` at `width` bits.
fn bv_const_bits(b: &mut Builder, target: Target, value: u128, width: usize) -> Vec<Literal> {
    (0..width)
        .map(|i| mk_const(b, target, (value >> i) & 1 == 1))
        .collect()
}

// ---------------------------------------------------------------------------
// Expression encoder.
// ---------------------------------------------------------------------------

fn encode(
    expr: &ChcExpr,
    env: &mut HashMap<String, Val>,
    b: &mut Builder,
    target: Target,
) -> Option<Val> {
    match expr {
        ChcExpr::Bool(v) => Some(Val::Bool(mk_const(b, target, *v))),
        ChcExpr::Int(c) => Some(Val::Int(int_const_bits(b, target, *c, INT_WIDTH))),
        ChcExpr::BitVec(value, width) => Some(Val::Int(bv_const_bits(
            b,
            target,
            *value,
            blast_width(*width),
        ))),
        ChcExpr::Var(var) => match &var.sort {
            ChcSort::Bool => Some(Val::Bool(lookup_or_fresh_bool(&var.name, env, b))),
            ChcSort::Int => Some(Val::Int(lookup_or_fresh_bits(&var.name, INT_WIDTH, env, b))),
            ChcSort::BitVec(w) => Some(Val::Int(lookup_or_fresh_bits(
                &var.name,
                blast_width(*w),
                env,
                b,
            ))),
            _ => None,
        },
        ChcExpr::Op(op, args) => encode_op(*op, args, env, b, target),
        _ => None,
    }
}

fn lookup_or_fresh_bool(name: &str, env: &mut HashMap<String, Val>, b: &mut Builder) -> Literal {
    if let Some(Val::Bool(l)) = env.get(name) {
        return *l;
    }
    let l = Literal::positive(b.fresh());
    env.insert(name.to_string(), Val::Bool(l));
    l
}

fn lookup_or_fresh_bits(
    name: &str,
    width: usize,
    env: &mut HashMap<String, Val>,
    b: &mut Builder,
) -> Vec<Literal> {
    if let Some(Val::Int(bits)) = env.get(name) {
        if bits.len() == width {
            return bits.clone();
        }
    }
    let bits: Vec<Literal> = (0..width).map(|_| Literal::positive(b.fresh())).collect();
    env.insert(name.to_string(), Val::Int(bits.clone()));
    bits
}

fn encode_bool(
    expr: &ChcExpr,
    env: &mut HashMap<String, Val>,
    b: &mut Builder,
    target: Target,
) -> Option<Literal> {
    match encode(expr, env, b, target)? {
        Val::Bool(l) => Some(l),
        Val::Int(_) => None,
    }
}

fn encode_int(
    expr: &ChcExpr,
    env: &mut HashMap<String, Val>,
    b: &mut Builder,
    target: Target,
) -> Option<Vec<Literal>> {
    match encode(expr, env, b, target)? {
        Val::Int(bits) => Some(bits),
        Val::Bool(_) => None,
    }
}

fn encode_op(
    op: ChcOp,
    args: &[Arc<ChcExpr>],
    env: &mut HashMap<String, Val>,
    b: &mut Builder,
    target: Target,
) -> Option<Val> {
    match op {
        ChcOp::Not => {
            if args.len() != 1 {
                return None;
            }
            Some(Val::Bool(encode_bool(&args[0], env, b, target)?.negated()))
        }
        ChcOp::And | ChcOp::Or => {
            let mut lits = Vec::with_capacity(args.len());
            for a in args {
                lits.push(encode_bool(a, env, b, target)?);
            }
            let mut acc = mk_const(b, target, matches!(op, ChcOp::And));
            for l in lits {
                acc = if matches!(op, ChcOp::And) {
                    mk_and(b, target, acc, l)
                } else {
                    mk_or(b, target, acc, l)
                };
            }
            Some(Val::Bool(acc))
        }
        ChcOp::Implies => {
            if args.len() != 2 {
                return None;
            }
            let a = encode_bool(&args[0], env, b, target)?;
            let c = encode_bool(&args[1], env, b, target)?;
            Some(Val::Bool(mk_or(b, target, a.negated(), c)))
        }
        ChcOp::Iff | ChcOp::Eq | ChcOp::Ne => {
            if args.len() != 2 {
                return None;
            }
            let a = encode(&args[0], env, b, target)?;
            let c = encode(&args[1], env, b, target)?;
            let eq = match (a, c) {
                (Val::Bool(la), Val::Bool(lc)) => mk_xnor(b, target, la, lc),
                (Val::Int(va), Val::Int(vc)) => int_eq(b, target, &va, &vc)?,
                _ => return None, // sort mismatch
            };
            Some(Val::Bool(if matches!(op, ChcOp::Ne) {
                eq.negated()
            } else {
                eq
            }))
        }
        ChcOp::Ite => {
            if args.len() != 3 {
                return None;
            }
            let s = encode_bool(&args[0], env, b, target)?;
            let th = encode(&args[1], env, b, target)?;
            let el = encode(&args[2], env, b, target)?;
            match (th, el) {
                (Val::Bool(t), Val::Bool(e)) => Some(Val::Bool(mk_ite(b, target, s, t, e))),
                (Val::Int(t), Val::Int(e)) => {
                    if t.len() != e.len() {
                        return None;
                    }
                    let bits = (0..t.len())
                        .map(|i| mk_ite(b, target, s, t[i], e[i]))
                        .collect();
                    Some(Val::Int(bits))
                }
                _ => None,
            }
        }
        // ---- Integer arithmetic (modelled at INT_WIDTH) --------------------
        ChcOp::Add | ChcOp::BvAdd => binary_int(args, env, b, target, |b, t, a, c| {
            if a.len() != c.len() {
                return None;
            }
            Some(ripple_add(b, t, a, c))
        }),
        ChcOp::Sub | ChcOp::BvSub => binary_int(args, env, b, target, |b, t, a, c| {
            if a.len() != c.len() {
                return None;
            }
            Some(ripple_sub(b, t, a, c))
        }),
        ChcOp::Neg | ChcOp::BvNeg => {
            if args.len() != 1 {
                return None;
            }
            let a = encode_int(&args[0], env, b, target)?;
            Some(Val::Int(ripple_neg(b, target, &a)))
        }
        ChcOp::Mod => {
            // Only `x mod 2^k`: the low `k` bits of `x`.
            if args.len() != 2 {
                return None;
            }
            let k = pow2_log(&args[1])?;
            let x = encode_int(&args[0], env, b, target)?;
            let zero = mk_const(b, target, false);
            let bits: Vec<Literal> = (0..x.len())
                .map(|i| if i < k { x[i] } else { zero })
                .collect();
            Some(Val::Int(bits))
        }
        ChcOp::Div => {
            // Only `x div 2^k`: `x` shifted right by `k`.
            if args.len() != 2 {
                return None;
            }
            let k = pow2_log(&args[1])?;
            let x = encode_int(&args[0], env, b, target)?;
            let zero = mk_const(b, target, false);
            let bits: Vec<Literal> = (0..x.len())
                .map(|i| if i + k < x.len() { x[i + k] } else { zero })
                .collect();
            Some(Val::Int(bits))
        }
        // ---- Bit-vector bitwise --------------------------------------------
        ChcOp::BvNot => {
            if args.len() != 1 {
                return None;
            }
            Some(Val::Int(bit_not(&encode_int(&args[0], env, b, target)?)))
        }
        ChcOp::BvAnd => binary_int(args, env, b, target, |b, t, a, c| {
            bitwise(b, t, a, c, mk_and)
        }),
        ChcOp::BvOr => binary_int(args, env, b, target, |b, t, a, c| {
            bitwise(b, t, a, c, mk_or)
        }),
        ChcOp::BvXor => binary_int(args, env, b, target, |b, t, a, c| {
            bitwise(b, t, a, c, mk_xor)
        }),
        ChcOp::BvXnor => binary_int(args, env, b, target, |b, t, a, c| {
            bitwise(b, t, a, c, mk_xnor)
        }),
        ChcOp::BvNand => binary_int(args, env, b, target, |b, t, a, c| {
            Some(bit_not(&bitwise(b, t, a, c, mk_and)?))
        }),
        ChcOp::BvNor => binary_int(args, env, b, target, |b, t, a, c| {
            Some(bit_not(&bitwise(b, t, a, c, mk_or)?))
        }),
        // ---- Bit-vector unsigned comparison --------------------------------
        ChcOp::BvULt => binary_cmp(args, env, b, target, |b, t, a, c| unsigned_lt(b, t, a, c)),
        ChcOp::BvUGt => binary_cmp(args, env, b, target, |b, t, a, c| unsigned_lt(b, t, c, a)),
        ChcOp::BvULe => binary_cmp(args, env, b, target, |b, t, a, c| {
            Some(unsigned_lt(b, t, c, a)?.negated())
        }),
        ChcOp::BvUGe => binary_cmp(args, env, b, target, |b, t, a, c| {
            Some(unsigned_lt(b, t, a, c)?.negated())
        }),
        ChcOp::BvComp => {
            // 1-bit result: 1 iff operands equal.
            if args.len() != 2 {
                return None;
            }
            let a = encode_int(&args[0], env, b, target)?;
            let c = encode_int(&args[1], env, b, target)?;
            Some(Val::Int(vec![int_eq(b, target, &a, &c)?]))
        }
        // ---- Bit-vector shift / slice by constant --------------------------
        ChcOp::BvShl => shift_by_const(args, env, b, target, true),
        ChcOp::BvLShr => shift_by_const(args, env, b, target, false),
        ChcOp::BvExtract(high, low) => {
            if args.len() != 1 || high < low {
                return None;
            }
            let x = encode_int(&args[0], env, b, target)?;
            let (h, l) = (high as usize, low as usize);
            if h >= x.len() {
                return None;
            }
            Some(Val::Int(x[l..=h].to_vec()))
        }
        _ => None,
    }
}

/// Encode a binary bit-vector operation returning a bit vector.
fn binary_int<F>(
    args: &[Arc<ChcExpr>],
    env: &mut HashMap<String, Val>,
    b: &mut Builder,
    target: Target,
    f: F,
) -> Option<Val>
where
    F: Fn(&mut Builder, Target, &[Literal], &[Literal]) -> Option<Vec<Literal>>,
{
    if args.len() != 2 {
        return None;
    }
    let a = encode_int(&args[0], env, b, target)?;
    let c = encode_int(&args[1], env, b, target)?;
    Some(Val::Int(f(b, target, &a, &c)?))
}

/// Encode a binary bit-vector comparison returning a Boolean.
fn binary_cmp<F>(
    args: &[Arc<ChcExpr>],
    env: &mut HashMap<String, Val>,
    b: &mut Builder,
    target: Target,
    f: F,
) -> Option<Val>
where
    F: Fn(&mut Builder, Target, &[Literal], &[Literal]) -> Option<Literal>,
{
    if args.len() != 2 {
        return None;
    }
    let a = encode_int(&args[0], env, b, target)?;
    let c = encode_int(&args[1], env, b, target)?;
    Some(Val::Bool(f(b, target, &a, &c)?))
}

/// Logical shift by a constant distance (`left` selects `<<` vs `>>`).
fn shift_by_const(
    args: &[Arc<ChcExpr>],
    env: &mut HashMap<String, Val>,
    b: &mut Builder,
    target: Target,
    left: bool,
) -> Option<Val> {
    if args.len() != 2 {
        return None;
    }
    let x = encode_int(&args[0], env, b, target)?;
    let k = const_shift_amount(&args[1])?;
    let zero = mk_const(b, target, false);
    let w = x.len();
    let bits: Vec<Literal> = (0..w)
        .map(|i| {
            if left {
                if i >= k {
                    x[i - k]
                } else {
                    zero
                }
            } else if i + k < w {
                x[i + k]
            } else {
                zero
            }
        })
        .collect();
    Some(Val::Int(bits))
}

/// Constant shift distance from an `Int` or `BitVec` literal.
fn const_shift_amount(expr: &ChcExpr) -> Option<usize> {
    match expr {
        ChcExpr::Int(c) if *c >= 0 => Some(*c as usize),
        ChcExpr::BitVec(v, _) => Some(*v as usize),
        _ => None,
    }
}

/// If `expr` is a positive power-of-two integer constant `2^k`, return `k`.
fn pow2_log(expr: &ChcExpr) -> Option<usize> {
    match expr {
        ChcExpr::Int(c) if *c > 0 && (*c as u64).is_power_of_two() => {
            Some((*c as u64).trailing_zeros() as usize)
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Cone-of-influence slice.
// ---------------------------------------------------------------------------

/// Backward cone-of-influence of the bad property over state latches.
///
/// `deps` is the directed combinational fan-in (`deps[out]` = the vars feeding
/// gate `out`); state latches are `0..total_latches` and their next-state copies
/// are `total_latches..2*total_latches`. Returns a `total_latches`-length bitmap:
/// `true` at `i` iff latch `i` can influence `bad` now or in any future step.
///
/// A latch enters the COI if (1) the property reads it, or (2) it feeds the
/// transition update of a latch already in the COI. We walk the gate graph
/// backward (output -> inputs); whenever the walk reaches a state latch `i` we
/// also seed the fan-in of its next-state gate `next_i = total_latches + i`, so
/// future iterations are covered. The *directed* walk is essential: the stutter
/// `guard` literal is an INPUT shared by every latch's ITE, so an undirected
/// (share-a-clause) walk would reach `guard` and from there every other latch's
/// update gate, collapsing the COI to the whole state.
fn coi_state_latches(
    deps: &HashMap<u32, Vec<u32>>,
    bad_literals: &[Literal],
    total_latches: usize,
) -> Vec<bool> {
    let mut in_coi = vec![false; total_latches];
    let mut visited: HashSet<u32> = HashSet::new();
    // Combinational worklist of gate-output vars to expand backward.
    let mut stack: Vec<u32> = bad_literals
        .iter()
        .map(|l| l.variable().index() as u32)
        .collect();
    while let Some(v) = stack.pop() {
        if (v as usize) < total_latches {
            // A state latch read by the cone: record it and seed its next-state
            // gate so its temporal update (and that gate's inputs) join the COI.
            let i = v as usize;
            if !in_coi[i] {
                in_coi[i] = true;
                stack.push((total_latches + i) as u32);
            }
            continue; // leaf: do not expand a state latch combinationally
        }
        if !visited.insert(v) {
            continue;
        }
        if let Some(inputs) = deps.get(&v) {
            for &inp in inputs {
                stack.push(inp);
            }
        }
    }
    in_coi
}

// ---------------------------------------------------------------------------
// Back-translation.
// ---------------------------------------------------------------------------

/// Translate the bit-level inductive invariant (CNF over current-state latches)
/// back into a word-level [`InvariantModel`] over `P`'s formal parameters.
///
/// Each blocked clause is a disjunction over latch literals; each latch maps to
/// a word-level Boolean atom (`Bool` argument -> the parameter; `Int` bit `i`
/// -> `(= (mod (div c 2^i) 2) 1)`; `BitVec` bit `i` -> `(= ((_ extract i i) c)
/// #b1)`). The model formula is the conjunction of the clauses. The result is a
/// CANDIDATE — the caller re-validates it.
fn back_translate(
    pred: PredicateId,
    params: &[ChcVar],
    latches: &[LatchMeaning],
    clauses: &[Vec<Literal>],
) -> Option<InvariantModel> {
    let mut conjuncts: Vec<ChcExpr> = Vec::new();
    for clause in clauses {
        let mut disjuncts: Vec<ChcExpr> = Vec::new();
        for lit in clause {
            let idx = lit.variable().index();
            let meaning = latches.get(idx)?; // invariant must be over state latches only
            let atom = latch_to_expr(meaning, params)?;
            if lit.is_positive() {
                disjuncts.push(atom);
            } else {
                disjuncts.push(ChcExpr::Op(ChcOp::Not, vec![Arc::new(atom)]));
            }
        }
        let clause_expr = match disjuncts.len() {
            0 => ChcExpr::Bool(false),
            1 => disjuncts.pop().unwrap(),
            _ => ChcExpr::Op(ChcOp::Or, disjuncts.into_iter().map(Arc::new).collect()),
        };
        conjuncts.push(clause_expr);
    }

    let formula = match conjuncts.len() {
        0 => ChcExpr::Bool(true),
        1 => conjuncts.pop().unwrap(),
        _ => ChcExpr::Op(ChcOp::And, conjuncts.into_iter().map(Arc::new).collect()),
    };

    let mut model = InvariantModel::new();
    model.set(pred, PredicateInterpretation::new(params.to_vec(), formula));
    Some(model)
}

/// Word-level Boolean atom for a single latch.
fn latch_to_expr(meaning: &LatchMeaning, params: &[ChcVar]) -> Option<ChcExpr> {
    let param = params.get(meaning.arg)?;
    match (meaning.bit, &param.sort) {
        (None, _) => Some(ChcExpr::Var(param.clone())),
        (Some(bit), ChcSort::BitVec(_)) => {
            // bit i of bv `c` is set iff ((_ extract i i) c) == #b1.
            let var = ChcExpr::Var(param.clone());
            let ext = ChcExpr::Op(
                ChcOp::BvExtract(bit as u32, bit as u32),
                vec![Arc::new(var)],
            );
            Some(ChcExpr::Op(
                ChcOp::Eq,
                vec![Arc::new(ext), Arc::new(ChcExpr::BitVec(1, 1))],
            ))
        }
        (Some(bit), _) => {
            // bit i of integer `c` is set iff (c div 2^i) mod 2 == 1.
            let var = ChcExpr::Var(param.clone());
            let shifted = if bit == 0 {
                var
            } else {
                let two_pow = 1i128 << bit;
                ChcExpr::Op(
                    ChcOp::Div,
                    vec![Arc::new(var), Arc::new(ChcExpr::Int(two_pow))],
                )
            };
            let modulo = ChcExpr::Op(
                ChcOp::Mod,
                vec![Arc::new(shifted), Arc::new(ChcExpr::Int(2))],
            );
            Some(ChcExpr::Op(
                ChcOp::Eq,
                vec![Arc::new(modulo), Arc::new(ChcExpr::Int(1))],
            ))
        }
    }
}

#[cfg(test)]
mod tests;
