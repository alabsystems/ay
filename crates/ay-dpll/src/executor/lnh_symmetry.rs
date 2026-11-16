// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sound symmetry breaking for TPTP-style finite-model QF_UF instances
//! (`NEQ*`/`PEQ*`/`QG-classification`: "find a model of size n" problems).
//!
//! These declare a domain of `n` constants `c_0..c_{n-1}` of an uninterpreted
//! sort (`declare-sort`; never a datatype or `RoundingMode`, see
//! [`is_genuinely_uninterpreted_sort`]) plus totality constraints forcing every
//! function result into that domain. When the domain constants are **fully
//! interchangeable** (`S_n` symmetry) — which we PROVE, not assume — proving
//! UNSAT explores `n!` equivalent assignments.
//!
//! # Soundness argument (the conditions, and where each is checked)
//!
//! Both schemes below ADD clauses `B` to the problem `F`, so they are sound
//! iff `F` satisfiable ⟹ `F ∧ B` satisfiable (a model of `F ∧ B` is a model
//! of `F`; an UNSAT of `F ∧ B` is published as an UNSAT of `F`). The argument
//! is a model-RENAMING one: for a permutation `σ` of the domain constants let
//! `M∘σ` be the interpretation that agrees with `M` everywhere except that each
//! `c` is interpreted as `M(σ(c))`. By the substitution lemma
//! `(M∘σ)(t) = M(σ(t))` for every term `t`, where `σ(t)` is the SYNTACTIC
//! substitution. Hence if `σ(F) ⊆ F` then `M |= F ⟹ M∘σ |= F`, and the
//! least-index / lex-leader arguments (at each scheme's function) pick, in
//! every orbit, a renamed model that also satisfies `B`. That needs:
//!
//! * **(C1) every domain element is a FREE CONSTANT SYMBOL.** `M∘σ` must be a
//!   legal interpretation of every theory in play, which holds exactly when
//!   `σ` only reassigns uninterpreted nullary symbols that nothing outside `F`
//!   constrains. Not admitted: datatype constructors and other interpreted
//!   constants (a tester `is-D` or the datatype axioms interpret `D`, so
//!   "swapping" `D` and `E` is no model symmetry), COMPOUND terms (`(hd l0)`,
//!   `(f a0)`: substituting the term `(f a0)` for `(f a1)` is not a renaming —
//!   the value of `(f a0)` is tied to `a0`, which `σ` leaves in place),
//!   defined / adopted-macro / let-bound symbols, and Skolem or solver-minted
//!   symbols (their meaning can live in side tables outside `F`). Checked by
//!   [`declared_free_constants`] (frontend authority: a live, direct, nullary,
//!   [`ay_frontend::DeclarationKind::Uninterpreted`] declaration whose bound
//!   term IS the element) and again structurally by [`is_free_domain_constant`]
//!   (`Var` shape, not a constructor, not a Skolem symbol, and its name bound
//!   by no quantifier or `let` of `F`, so substitution cannot capture).
//! * **(C2) `σ(F) ⊆ F` for a generating set of the permutations used**, where
//!   `F` is EVERYTHING the verdict is about: the assertions of the live scope
//!   stack, the solve-time definitions appended to them, and any assumptions
//!   carried beside them. Checked by [`domain_is_interchangeable`] over
//!   `assertions ∪ assumptions` for the transpositions `(c_0 c_i)`, which
//!   generate `S_n`; substitution rebuilds through the equivalence-preserving
//!   `mk_*` constructors, so a syntactic hit is a semantic one.
//! * **(C3) the schemes' own premises**: least-index uses only totality clauses
//!   that are top-level conjuncts of `F` ([`collect_totality_terms`]) and pins a
//!   subject only once every domain constant inside it is used (eligibility);
//!   the lex-leader computes each atom's image by the same substitution. The
//!   two schemes are never stacked ([`add_lnh_symmetry_breaking`]).
//! * **(C4) scope**: `B` is derived from, and valid only for, the `F` of THIS
//!   check. The domain and the atoms are read from the terms reachable from
//!   `F` ([`live_terms`]) — never from the term store, which still holds terms
//!   of popped scopes and earlier queries — and `B` is appended to the
//!   solve-time assertion vector that `check_sat` restores on every exit, so it
//!   is recomputed for each check. Restoring the vector is not enough on its
//!   own: a persistent incremental lane (the theory lane's DT/Seq/LIA/LRA
//!   persist-SAT pipelines, the BV lane, the FP lane) activates every
//!   non-root term it encodes at the current push depth and keeps that
//!   activation until the scope is popped — forever at depth 0 — so `B` would
//!   constrain every later check of the scope, including asymmetric ones the
//!   pass declines (wrong `unsat`, 2026-10-02 audit k00..k11). Hence: no
//!   check of an incremental session carries `B`
//!   ([`Executor::lnh_admissible_for_check`]); a check that does carry it
//!   runs on none of the session's lanes
//!   ([`Executor::set_aside_lanes_for_lnh`]), which are restored, never
//!   having seen `B`, when the check ends
//!   ([`Executor::with_lnh_lane_frame`]). So `B` never outlives its check.
//!   Only a WHOLE-PROBLEM ONE-SHOT check carries `B`
//!   ([`Executor::lnh_admissible_for_check`]): the outermost solve of the
//!   query that owns the thread — the check the caller asked for — in a
//!   non-incremental session. No executor that runs its query inside another
//!   one does (probes, sub-solves, replay probes on the caller's context),
//!   with one named exception: the deferred-trust certification re-solve of
//!   a refutation that used `B` (`unsat_cert.rs`, step (4)), which re-decides
//!   the same whole query on a private clone in a fresh executor dropped
//!   after its one check. Declining is the identity: a pass that adds
//!   nothing leaves the term store as it found it ([`domain_is_interchangeable`]).
//! * **(C5) no certificate is demanded.** `B` is satisfiability-preserving,
//!   not entailed: no proof rule derives it, so a refutation that uses it
//!   cannot be certified. Under `--self-check`, `--proof`, `--strict-proofs`,
//!   `:produce-proofs` or API proof checking the pass declines (z3 likewise
//!   never symmetry-reduces under proofs). The default posture admits such a
//!   refutation only through the deferred-trust discharge's fresh whole-query
//!   re-solve (`unsat_cert.rs`, step (4)), which re-applies the pass to the
//!   same query under C1..C4 — reproducibility evidence, not a checked
//!   derivation, exactly as that step documents for every refutation it
//!   admits.
//! * **(C6) the problem is ground.** A quantified problem is solved by
//!   instantiation rounds; a pinned model starves model-based instantiation
//!   (2026-10-09 audit lv7), and z3's `symmetry-reduce` targets ground goals.
//!   Like the array guard in [`domain_candidates`] this is a completeness and
//!   profitability gate: the renaming argument does not need it.
//!
//! # Why signature ordering (and NOT the naive LNH)
//!
//! A previous attempt fixed a function cell (`f(c_0,c_0) = c_0`). That is WLOG
//! only if the domain has an idempotent element (`x*x = x`); non-idempotent
//! quasigroups have models with `f(c_0,c_0) != c_0`, so it produced FALSE UNSAT
//! (caught by an oracle differential; reverted). The bug: a function cell's
//! value is NOT freely permutable because the cell's ARGUMENTS are domain
//! elements too.
//!
//! This pass instead canonicalizes by **unary-predicate signatures**, which ARE
//! permutation-covariant. Each domain element `c_i` gets a signature
//! `sig(c_i) = (p_1(c_i), .., p_m(c_i))` over the unary predicates `p_k: S->Bool`.
//! We require `sig(c_0) <=_lex sig(c_1) <=_lex .. <=_lex sig(c_{n-1})`.
//!
//! SOUNDNESS (satisfiability-preserving): take any model `M`. Its elements have
//! signatures; permute the domain to sort the elements by signature. Because the
//! formula is `S_n`-invariant (checked), the sorted model `M'` still satisfies
//! it, and `M'` satisfies the ordering constraint. So a solution survives in
//! every orbit. No idempotence / cell-value assumption is made — sorting by a
//! boolean signature is ALWAYS achievable by a permutation. Kill switch `--dpll-no-euf-lnh`.
//!
//! # Least-index orbit-prefix scheme (preferred when it applies)
//!
//! The lex-leader above is sound but propagates poorly (deep Tseitin chains).
//! [`add_least_index_symmetry_breaking`] instead emits the CADE'11
//! Déharbe/Fontaine/Merz/Paulus prefix clauses `t_k in {c_0..c_k}` over
//! totality-clause subjects — z3's `symmetry-reduce`, the mechanism that
//! collapses SEQ/PEQ/NEQ/QG pigeonhole cores to level-0 unit cascades
//! (SEQ009_size7: 3711 -> 1 conflicts). It differs from the SUNK cell-fixing
//! attempt above in two load-bearing ways: the first clause on a cell subject
//! keeps TWO candidates (`f(c_0,c_0) in {c_0, c_1}` — no idempotence
//! assumption), and a subject is only constrained once every domain constant
//! it contains is pinned (so the rescuing permutation never moves a
//! constrained subject's own arguments). The two schemes are mutually
//! exclusive per instance; both sit behind the same proven-`S_n` gate.

use std::cell::Cell;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};

use ay_core::kani_compat::DetHashSet;
use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::Sort;

use super::Executor;
use crate::incremental_state::{IncrementalBvState, IncrementalFpState, IncrementalTheoryState};

/// Enabled by default; `--dpll-no-euf-lnh` disables. Off on main from
/// faece014b1 (2026-10-02) to this repair: the pass had published WRONG
/// `unsat` in both postures, over domains that were not interchangeable
/// constants (C1) and through clauses that outlived their check on the
/// persistent lanes (C4). The module doc states the conditions and where each
/// is checked; the on/off agreement gate is `ay`'s
/// `group_soundness/lnh_on_off_agreement.rs` (CLI, both postures, every
/// fixture whose answer the pass ever got wrong). Only ever APPLIES when a
/// domain of declared free constants is proven `S_n`-interchangeable over the
/// whole problem and `n >= 5`, so it is a no-op on the vast majority of
/// instances.
pub(crate) fn lnh_enabled() -> bool {
    !ay_core::theory_disable_flags().no_euf_lnh // B28: CLI-owned; env retired.
}

/// The session's lanes, held aside while a check whose solve-time assertions
/// carry LNH clauses runs without them (C4).
pub(crate) struct LnhSetAsideLanes {
    theory: Option<IncrementalTheoryState>,
    bv: Option<Box<IncrementalBvState>>,
    fp: Option<Box<IncrementalFpState>>,
}

thread_local! {
    /// How many solve frames ([`Executor::with_lnh_lane_frame`]) are open on
    /// this thread, across every `Executor`. The executor that owns a check
    /// runs its solve in the OUTERMOST frame; a sub-solve of that solve (of
    /// the same executor over a window, or of an executor built inside it: a
    /// probe, an instantiation round's ground check) runs in a frame nested
    /// inside it (C4).
    static LNH_SOLVE_FRAME_DEPTH: Cell<u32> = const { Cell::new(0) };

    /// The address of the `Executor` whose query is the outermost one in
    /// progress on this thread (0: none) — the session executor whose check
    /// the caller asked for. Every executor a check builds, at any point of
    /// it (inside its solve, or at its publication boundary: certification
    /// probes, replay probes that borrow the caller's context), runs its own
    /// query inside the owner's, so it is never the owner (C4).
    static LNH_QUERY_OWNER: Cell<usize> = const { Cell::new(0) };
}

/// Query ownership claimed by [`Executor::lnh_claim_query_ownership`];
/// released on drop, a panic included.
pub(crate) struct LnhQueryOwnerGuard {
    claimed: bool,
}

impl Drop for LnhQueryOwnerGuard {
    fn drop(&mut self) {
        if self.claimed {
            LNH_QUERY_OWNER.with(|owner| owner.set(0));
        }
    }
}

fn executor_address(executor: &Executor) -> usize {
    std::ptr::from_ref(executor) as usize
}

/// Closes one solve frame on drop, so a panicking solve unwinds the count.
struct SolveFrameDepthGuard;

impl SolveFrameDepthGuard {
    fn enter() -> Self {
        LNH_SOLVE_FRAME_DEPTH.with(|depth| depth.set(depth.get().saturating_add(1)));
        Self
    }
}

impl Drop for SolveFrameDepthGuard {
    fn drop(&mut self) {
        LNH_SOLVE_FRAME_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
    }
}

/// Whether the solve running now is in the outermost solve frame on this
/// thread, i.e. no other executor's solve encloses it.
fn in_outermost_solve_frame() -> bool {
    LNH_SOLVE_FRAME_DEPTH.with(Cell::get) == 1
}

impl Executor {
    /// Whether this check may carry symmetry clauses at all.
    ///
    /// (C4) Only a WHOLE-PROBLEM ONE-SHOT check may: its problem is the whole
    /// query its verdict is published for, and nothing outlives it. That is
    /// the outermost solve (no other solve frame encloses it) of the query
    /// that owns the thread — the check the caller asked for — in a
    /// non-incremental session. Every other executor runs its query inside
    /// that one and never carries `B`: probes and sub-solves of part of the
    /// problem, an instantiation round's ground check, replay probes that
    /// borrow the caller's context (their terms would stay in the caller's
    /// store; 2026-10-09 verify lv4), whole-query re-solves of the incremental
    /// routes. One exception, by name: the deferred-trust certification
    /// re-solve (`unsat_cert.rs`, step (4)) of a refutation whose solve
    /// carried `B` — [`Self::lnh_reconfirms_carried_symmetry`]. It re-decides
    /// that same whole query on a private clone of the context in a fresh
    /// executor that is dropped after its one check, so it proves the
    /// symmetry of the query again itself and its clauses die with it.
    ///
    /// (C5) Never when the check's `unsat` must carry a checked certificate
    /// (`--self-check`/`--rigor certified`, `--proof`, `--strict-proofs`,
    /// `(set-option :produce-proofs true)`, API proof checking —
    /// [`Self::checked_certificate_demanded`]): `B` is
    /// satisfiability-preserving, not entailed, so no proof rule derives it
    /// and a refutation that uses it can never be certified. z3 likewise
    /// never symmetry-reduces under proofs. The default posture certifies a
    /// refutation that used `B` only through the deferred-trust discharge's
    /// fresh whole-query re-solve (`unsat_cert.rs`, step (4)), which proves
    /// the symmetry of that query again in its own one-shot check.
    ///
    /// And never in an incremental session (`push`, or a native-API assertion
    /// after a check):
    ///
    /// `B` preserves satisfiability for THIS check's problem only, but the
    /// persistent lanes of an incremental session (the theory lane on
    /// `incr_theory_state` — the DT, Seq, LIA/LRA persist-SAT pipelines —, the
    /// BV lane, the FP lane) activate every non-root term they encode at the
    /// current push depth and never retract it when the check ends: at depth
    /// 0 it is permanent. A later check whose problem is asymmetric (the pass
    /// correctly declines it) was then solved under the stale pin `x = c0` —
    /// wrong `unsat` in `--z3-mode`, `unknown` in the default posture
    /// (2026-10-02 audit k00..k11, M3*, M8b, L*; on main since the pass
    /// landed). Solving the check off the session's lanes instead does remove
    /// the leak, but it changes what every LATER check of the session starts
    /// from — a lane that never saw this check's roots — and the incremental
    /// datatype pipeline is measurably less complete from there: with the
    /// pass OFF, a first `(check-sat-assuming ())` (which also solves off the
    /// session's lanes) followed by a `(check-sat)` leaves the second check
    /// `unknown` where two plain checks decide it (k02 shape). Either
    /// isolation variant cost more verdicts than it bought on the audit's
    /// incremental corpus (measured in the commit message). z3 likewise
    /// applies `symmetry-reduce` only to one-shot goals. So an incremental
    /// session's checks are solved exactly as with the pass off.
    pub(in crate::executor) fn lnh_admissible_for_check(&self) -> bool {
        !self.incremental_mode
            && in_outermost_solve_frame()
            && (self.owns_outermost_query() || self.lnh_reconfirms_carried_symmetry)
            && !self.checked_certificate_demanded()
    }

    /// Whether this executor's query is the outermost one in progress on this
    /// thread (C4).
    fn owns_outermost_query(&self) -> bool {
        LNH_QUERY_OWNER.with(Cell::get) == executor_address(self)
    }

    /// Claim ownership of the thread's outermost query for this executor when
    /// no other executor holds it; hold the guard while the work runs. Taken
    /// at every boundary of the caller's work on this executor, so whatever
    /// it builds and runs inside never owns: the command boundary
    /// (`execute_stack_guarded`, which also covers a command's publication),
    /// the query boundary (`with_scope_root_depths`, for callers that solve
    /// without a command), and the UNSAT publication boundary
    /// (`certify_unsat_for_publication`, which the native API runs after the
    /// query returned).
    pub(in crate::executor) fn lnh_claim_query_ownership(&self) -> LnhQueryOwnerGuard {
        let address = executor_address(self);
        let claimed = LNH_QUERY_OWNER.with(|owner| {
            if owner.get() == 0 {
                owner.set(address);
                true
            } else {
                false
            }
        });
        LnhQueryOwnerGuard { claimed }
    }

    /// Run one solve entry and, if the LNH pass set the session's lanes aside
    /// inside it ([`Self::set_aside_lanes_for_lnh`]), put them back on every
    /// exit, a panic included; the lanes the solve built, which encoded the
    /// symmetry clauses, are dropped. Nested entries keep their own frame:
    /// the outer frame's set-aside lanes are restored by the outer frame.
    /// The frame is also what [`Self::lnh_admissible_for_check`] counts to
    /// tell the outermost solve from one nested inside it.
    pub(in crate::executor) fn with_lnh_lane_frame<T>(
        &mut self,
        solve: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let _frame = SolveFrameDepthGuard::enter();
        let outer = self.lnh_set_aside_lanes.take();
        let result = catch_unwind(AssertUnwindSafe(|| solve(self)));
        if let Some(saved) = self.lnh_set_aside_lanes.take() {
            self.incr_theory_state = saved.theory;
            self.incr_bv_state = saved.bv;
            self.incr_fp_state = saved.fp;
            // The terms this solve minted were seen only by the lanes just
            // dropped (`store_mirrors_session_lanes`).
            self.lnh_dropped_check_lanes = true;
        }
        self.lnh_set_aside_lanes = outer;
        result.unwrap_or_else(|payload| resume_unwind(payload))
    }

    /// Whether the term store of the current epoch (since the last
    /// `reset-assertions`, `assertion_epoch_terms_len`) still mirrors what the
    /// lanes the current solve runs on have seen: every term in it was minted
    /// by a check whose lanes the session kept. Not while this check runs
    /// with the session's lanes set aside for LNH clauses (it solves on fresh
    /// lanes), and never again once such a check dropped the lanes it built
    /// (the store then holds its scratch, which no lane of the session
    /// encoded). A whole-store scan that stands in for "what the lanes have
    /// seen" is only sound as a proxy while this holds.
    pub(in crate::executor) fn store_mirrors_session_lanes(&self) -> bool {
        !self.lnh_dropped_check_lanes && self.lnh_set_aside_lanes.is_none()
    }

    /// (C4) Outside incremental mode a session can still hold lanes — a
    /// `check-sat-assuming` window's lanes, or the session's own lanes after
    /// it left an incremental phase — and a later scoped window may continue
    /// or copy them (`lanes_for_scoped_window`). The symmetry clauses must
    /// reach none of them: the rest of this check runs on no lanes at all, as
    /// a non-incremental session starts, and the enclosing
    /// [`Self::with_lnh_lane_frame`] restores the session's lanes, which never
    /// saw `B`.
    pub(in crate::executor) fn set_aside_lanes_for_lnh(&mut self) {
        if self.lnh_set_aside_lanes.is_some() {
            return; // this frame already runs without the session's lanes
        }
        let theory = self.incr_theory_state.take();
        let bv = self.incr_bv_state.take();
        let fp = self.incr_fp_state.take();
        self.lnh_set_aside_lanes = Some(Box::new(LnhSetAsideLanes { theory, bv, fp }));
    }
}

fn is_builtin(sym: &Symbol) -> bool {
    matches!(
        sym.name(),
        "=" | "distinct" | "and" | "or" | "not" | "=>" | "ite" | "xor"
    )
}

const MAX_TERMS_FOR_CHECK: usize = 400_000;

/// The live problem (C4): every term reachable from the roots, in term-creation
/// order (the order the detection scans have always used), plus every name a
/// quantifier or `let` in it binds. `opaque` records a term kind this walk does
/// not know how to descend; the pass then declines (its scans could miss a
/// binder or an occurrence). `quantified` records a `forall`/`exists`; the
/// pass then declines too (C6).
pub(crate) struct LiveTerms {
    ids: Vec<TermId>,
    bound_names: DetHashSet<String>,
    opaque: bool,
    quantified: bool,
}

/// Collect the [`LiveTerms`] of `roots`.
fn live_terms(terms: &TermStore, roots: &[TermId]) -> LiveTerms {
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    let mut bound_names: DetHashSet<String> = DetHashSet::default();
    let mut opaque = false;
    let mut quantified = false;
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Const(_) | TermData::Var(..) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            TermData::Let(bindings, body) => {
                for (name, value) in bindings {
                    bound_names.insert(name.clone());
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                quantified = true;
                bound_names.extend(vars.iter().map(|(name, _)| name.clone()));
                stack.push(*body);
            }
            _ => opaque = true,
        }
    }
    let mut ids: Vec<TermId> = seen.into_iter().collect();
    ids.sort_unstable();
    LiveTerms {
        ids,
        bound_names,
        opaque,
        quantified,
    }
}

/// Whether `c` is a nullary datatype CONSTRUCTOR (an interpreted constant).
/// Defense in depth for (C1): the frontend authority already refuses these.
fn is_datatype_constructor(terms: &TermStore, c: TermId) -> bool {
    let name = match terms.get(c) {
        TermData::Var(name, _) => name.as_str(),
        TermData::App(sym, args) if args.is_empty() => sym.name(),
        _ => return false,
    };
    terms.constructor_field_names(name).is_some()
}

/// (C1), structural half: `c` is a bare constant symbol (`Var`), admitted by
/// the frontend authority (`free`), not a constructor or Skolem, and its name
/// is bound nowhere in the live problem (so substituting it cannot capture a
/// bound occurrence of the same spelling).
fn is_free_domain_constant(
    terms: &TermStore,
    live: &LiveTerms,
    free: &DetHashSet<TermId>,
    c: TermId,
) -> bool {
    let TermData::Var(name, _) = terms.get(c) else {
        return false;
    };
    free.contains(&c)
        && !is_datatype_constructor(terms, c)
        && !terms.is_skolem_symbol(name)
        && !live.bound_names.contains(name)
}

/// Whether `sort` is a GENUINELY uninterpreted sort: one `declare-sort` (or
/// the native API's equivalent) introduced, as opposed to an interpreted sort
/// the term store also spells `Sort::Uninterpreted` — a datatype
/// ([`Sort::as_term_sort`] lowers `Datatype(d)` to `Uninterpreted(d.name)`,
/// parametric instances included) or the floating-point `RoundingMode`.
///
/// Swapping free constants of an interpreted sort is still a model renaming,
/// so admitting them was never unsound (2026-10-09 verify: no wrong answer
/// in 500 datatype-domain files). It was a loss: the pinned model of a
/// datatype domain is the shape the datatype model gates fail closed on
/// (enum over-population, uncolourable dt-egraph classes), and most lost
/// verdicts of that verification were datatype domains (lv3: a single
/// `sat` check became `unknown` in both postures). The finite-model families
/// the pass exists for declare their domain with `declare-sort`. Model
/// completion's step 1b (`model/completion.rs`) gathers the solve's committed
/// equality atoms of these sorts only.
pub(in crate::executor) fn is_genuinely_uninterpreted_sort(
    ctx: &ay_frontend::Context,
    sort: &Sort,
) -> bool {
    let Sort::Uninterpreted(name) = sort else {
        return false;
    };
    name != "RoundingMode"
        && ctx.datatype_constructors(name).is_none()
        && !ctx.is_parametric_datatype_instance(name)
}

/// (C1), authority half: the subset of `candidates` that are LIVE, DIRECT,
/// nullary, uninterpreted declarations (`declare-const`/`declare-fun` or the
/// native API's equivalent) whose bound term is exactly the candidate, that
/// are not defined, adopted as a macro, solver-internal or constructors, and
/// whose sort is genuinely uninterpreted ([`is_genuinely_uninterpreted_sort`]).
pub(crate) fn declared_free_constants(
    ctx: &ay_frontend::Context,
    candidates: &[TermId],
) -> DetHashSet<TermId> {
    candidates
        .iter()
        .copied()
        .filter(|&c| {
            let TermData::Var(name, _) = ctx.terms.get(c) else {
                return false;
            };
            let Some(info) = ctx.symbol_info_by_identity(name) else {
                return false;
            };
            info.term == Some(c)
                && !info.sort.is_datatype()
                && is_genuinely_uninterpreted_sort(ctx, ctx.terms.sort(c))
                && info.arg_sorts.is_empty()
                && info.declaration_kind() == ay_frontend::DeclarationKind::Uninterpreted
                && info.is_completion_eligible_declaration()
                && ctx.adopted_macro_interp(name).is_none()
                && !ctx.is_defined_fun(name)
                && !ctx.is_internal_symbol(name)
                && ctx.is_constructor(name).is_none()
        })
        .collect()
}

/// Structurally possible domains of the live problem: each TOTALITY-shaped
/// or-node `(or (= t c_0) .. (= t c_{n-1}))` (`mk_distinct` expands
/// `(distinct ..)` into pairwise disequalities, so this is the robust signal)
/// whose elements are pairwise distinct bare `Var`s of one uninterpreted sort.
/// The or-node may sit anywhere in the live problem: it only nominates a
/// domain; (C1) and (C2) decide whether the domain is used.
pub(crate) struct DomainCandidates {
    /// The problem `F`: the assertions, then the carried assumptions.
    problem: Vec<TermId>,
    live: LiveTerms,
    domains: Vec<(Vec<TermId>, Sort)>,
}

impl DomainCandidates {
    /// Every element of every candidate domain, deduplicated, in first-seen
    /// order — what the caller hands to [`declared_free_constants`].
    pub(crate) fn constants(&self) -> Vec<TermId> {
        let mut seen: DetHashSet<TermId> = DetHashSet::default();
        self.domains
            .iter()
            .flat_map(|(domain, _)| domain.iter().copied())
            .filter(|c| seen.insert(*c))
            .collect()
    }
}

/// Collect the [`DomainCandidates`] of the live problem: the solve-time
/// `assertions` plus any `assumptions` carried beside them. Empty when no
/// totality-shaped or-node has bare constant elements.
pub(crate) fn domain_candidates(
    terms: &TermStore,
    assertions: &[TermId],
    assumptions: &[TermId],
) -> DomainCandidates {
    let mut problem = assertions.to_vec();
    problem.extend_from_slice(assumptions);
    // Cheap pre-filter (the store-wide scan this pass always paid): with no
    // totality-shaped or-node anywhere, there is nothing to nominate and the
    // reachability walk is skipped.
    if !terms
        .term_ids()
        .any(|id| totality_domain(terms, id).is_some())
    {
        return DomainCandidates {
            problem,
            live: LiveTerms {
                ids: Vec::new(),
                bound_names: DetHashSet::default(),
                opaque: false,
                quantified: false,
            },
            domains: Vec::new(),
        };
    }
    let live = live_terms(terms, &problem);
    let mut domains: Vec<(Vec<TermId>, Sort)> = Vec::new();
    // ARRAY SCOPE GUARD (#lnh-no-arrays): this pass targets finite-model QF_UF
    // (SEQ/QG/NEQ/PEQ). On array problems (QF_AX/QF_AUFLIA) the uninterpreted
    // Index/Element constants LOOK S_n-interchangeable to the prover, but the
    // array lemma machinery (witness-guided ROW, extensionality) already carries
    // the load and the extra least-index/lex clauses are pure overhead — measured
    // 2-70x wall regressions on the swap/cvc families (division bench
    // cert2->cert3: QF_AX same-file 0.69x, read5 195ms->14s). Equisatisfiability
    // is unaffected either way — this is a PROFITABILITY gate, mirroring the
    // domain-size gate. (B23: the experiment override is retired.)
    let has_arrays = live.ids.iter().any(
        |&id| matches!(terms.get(id), TermData::App(s, _) if matches!(s.name(), "select" | "store")),
    );
    // GROUND GUARD (C6): a quantified problem is solved by instantiation
    // rounds whose ground checks see only part of it, and a pinned model
    // starves model-based instantiation of the witnesses it needs
    // (2026-10-09 audit lv7: `--z3-mode` `unknown`, quantifier-unhandled,
    // where the pass fired; the problem is `sat`). z3's `symmetry-reduce`
    // likewise targets ground goals. Like the array guard, a profitability
    // and completeness gate: the renaming argument holds either way.
    if !has_arrays && !live.opaque && !live.quantified {
        for &id in &live.ids {
            if let Some(domain) = totality_domain(terms, id) {
                domains.push(domain);
            }
        }
    }
    DomainCandidates {
        problem,
        live,
        domains,
    }
}

/// The domain nominated by the or-node `id`, if it is totality-shaped.
fn totality_domain(terms: &TermStore, id: TermId) -> Option<(Vec<TermId>, Sort)> {
    let TermData::App(sym, ds) = terms.get(id) else {
        return None;
    };
    if sym.name() != "or" || ds.len() < 3 {
        return None;
    }
    let mut eqs: Vec<(TermId, TermId)> = Vec::with_capacity(ds.len());
    for &d in ds {
        match terms.get(d) {
            TermData::App(es, ea) if es.name() == "=" && ea.len() == 2 => {
                eqs.push((ea[0], ea[1]));
            }
            _ => return None,
        }
    }
    for &cand_t in &[eqs[0].0, eqs[0].1] {
        let mut domain = Vec::with_capacity(eqs.len());
        let mut good = true;
        for &(x, y) in &eqs {
            if x == cand_t {
                domain.push(y);
            } else if y == cand_t {
                domain.push(x);
            } else {
                good = false;
                break;
            }
        }
        if !good {
            continue;
        }
        let s0 = terms.sort(domain[0]).clone();
        if !matches!(s0, Sort::Uninterpreted(_))
            || !domain.iter().all(|&c| terms.sort(c) == &s0)
            || !domain
                .iter()
                .all(|&c| matches!(terms.get(c), TermData::Var(..)))
        {
            continue;
        }
        let mut sorted = domain.clone();
        sorted.sort();
        sorted.dedup();
        if sorted.len() != domain.len() {
            continue;
        }
        return Some((domain, s0));
    }
    None
}

/// The largest candidate domain all of whose elements are free constants
/// (C1); ties keep the first-seen. Returns (domain, uninterpreted sort).
fn find_domain(
    terms: &TermStore,
    candidates: &DomainCandidates,
    free: &DetHashSet<TermId>,
) -> Option<(Vec<TermId>, Sort)> {
    let mut best: Option<&(Vec<TermId>, Sort)> = None;
    for cand in &candidates.domains {
        if !cand
            .0
            .iter()
            .all(|&c| is_free_domain_constant(terms, &candidates.live, free, c))
        {
            continue;
        }
        if best.is_none_or(|(b, _)| cand.0.len() > b.len()) {
            best = Some(cand);
        }
    }
    best.cloned()
}

/// SOUND interchangeability proof (C2): every transposition `(c_0 c_i)` maps
/// the problem `F = assertions ∪ assumptions` into itself (transpositions
/// `(c_0 c_i)` generate `S_n`). Swaps are simultaneous and rebuilt through the
/// normalizing `mk_*` constructors, so a hit means genuine invariance. TRUE ⟹
/// real `S_n` symmetry of `F` (given C1). FALSE (incl. conservative misses) ⟹
/// skip (safe).
///
/// LEAVES NO TRACE in the store. The swapped images are interned to be
/// compared, and every image that is not already a term of `F` is a new term;
/// on a DECLINED pass they used to stay, so declining was not the identity:
/// it shifted the ids of every term the solve minted after it, and the
/// verdict of an asymmetric problem the pass never touched depended on
/// whether the pass was enabled (2026-10-09 audit lv5/lv6, verify lv5a/lv5b:
/// `unknown` with the pass on, `sat` with it off, in 0.04 s). The images are
/// discarded again ([`TermStore::rollback_to`]); nothing outside this
/// function sees an id they were given. The rollback cannot strand another
/// holder's checkpoint: the pass runs only at the top of the outermost solve
/// frame of a query (C4), before any speculative lane (the lazy datatype
/// lane, the quantifier lanes) opens its own rollback bracket on the store.
fn domain_is_interchangeable(terms: &mut TermStore, problem: &[TermId], domain: &[TermId]) -> bool {
    if terms.len() > MAX_TERMS_FOR_CHECK {
        return false;
    }
    let checkpoint = terms.rollback_checkpoint();
    let len_before = terms.len();
    let orig: DetHashSet<TermId> = problem.iter().copied().collect();
    let c0 = domain[0];
    let interchangeable = domain[1..].iter().all(|&ci| {
        let from = [c0, ci];
        let to = [ci, c0];
        problem
            .iter()
            .all(|&a| orig.contains(&terms.substitute(a, &from, &to)))
    });
    if terms.len() != len_before {
        terms.rollback_to(checkpoint);
    }
    interchangeable
}

/// Unary predicates `p: S -> Bool` applied to domain-sorted arguments in the
/// live problem, in a deterministic first-seen order. Signature components
/// must be permutation-covariant, so ONLY boolean-valued unary applications
/// qualify (a unary FUNCTION `S->S` yields a domain element, which is itself
/// permuted — not a stable comparison key).
fn find_unary_predicates(terms: &TermStore, live: &LiveTerms, dsort: &Sort) -> Vec<Symbol> {
    let mut seen: Vec<Symbol> = Vec::new();
    for &id in &live.ids {
        if let TermData::App(sym, args) = terms.get(id) {
            if args.len() == 1
                && !is_builtin(sym)
                && terms.sort(id) == &Sort::Bool
                && terms.sort(args[0]) == dsort
                && !seen.iter().any(|s| s.name() == sym.name())
            {
                seen.push(sym.clone());
            }
        }
    }
    seen
}

/// `sig(a) <=_lex sig(b)` over boolean predicate values (false < true), built
/// low-priority-last: `le_k = (¬a_k ∧ b_k) ∨ ((a_k = b_k) ∧ le_{k+1})`, base true.
fn lex_le(terms: &mut TermStore, a_sig: &[TermId], b_sig: &[TermId]) -> TermId {
    let mut le = terms.true_term();
    for k in (0..a_sig.len()).rev() {
        let a = a_sig[k];
        let b = b_sig[k];
        let na = terms.mk_not(a);
        let lt = terms.mk_and(vec![na, b]); // a < b : ¬a ∧ b
        let eq = terms.mk_eq(a, b); // a = b (iff on Bools)
        let eq_rest = terms.mk_and(vec![eq, le]);
        le = terms.mk_or(vec![lt, eq_rest]);
    }
    le
}

/// Uninterpreted binary functions `f: S x S -> S` used in the live problem
/// (distinct symbols, first-seen order). Their table equality atoms feed the
/// lex-leader.
fn find_binary_funcs(terms: &TermStore, live: &LiveTerms, dsort: &Sort) -> Vec<Symbol> {
    let mut seen: Vec<Symbol> = Vec::new();
    for &id in &live.ids {
        if let TermData::App(sym, args) = terms.get(id) {
            if args.len() == 2
                && !is_builtin(sym)
                && terms.sort(id) == dsort
                && terms.sort(args[0]) == dsort
                && terms.sort(args[1]) == dsort
                && !seen.iter().any(|s| s.name() == sym.name())
            {
                seen.push(sym.clone());
            }
        }
    }
    seen
}

/// Cap on the number of boolean atoms fed to each lex-leader chain (keeps the
/// per-transposition formula bounded; a subset lex-leader is still sound).
const MAX_LEX_ATOMS: usize = 600;

/// Least-index (orbit-prefix) symmetry breaking — the z3 `symmetry-reduce`
/// mechanism (Déharbe/Fontaine/Merz/Paulus, CADE'11) that collapses the
/// SEQ/QG finite-model family to level-0 unit-propagation cascades.
///
/// Enabled by default when the least-index scheme applies;
/// `--dpll-no-lnh-leastidx` falls back to the lex-leader for A/B.
fn least_index_enabled() -> bool {
    !ay_core::theory_disable_flags().no_lnh_leastidx // B28: CLI-owned; env retired.
}

/// Terms `t` with an asserted TOTALITY clause `(or (= t c_0) .. (= t c_{n-1}))`
/// covering the FULL domain, in deterministic first-seen assertion order.
///
/// Positivity is REQUIRED for soundness: the totality clause must be a
/// top-level conjunct (assertion root or nested under `and` only), so that
/// `F |= t in {c_0..c_{n-1}}` genuinely holds. (`find_domain` scans loose
/// or-nodes because it only needs a detection signal; here the clause is a
/// soundness premise of the added constraint.)
fn collect_totality_terms(
    terms: &TermStore,
    assertions: &[TermId],
    domain: &[TermId],
    dsort: &Sort,
) -> Vec<TermId> {
    use ay_core::kani_compat::DetHashSet;
    let domain_set: DetHashSet<TermId> = domain.iter().copied().collect();
    let mut out: Vec<TermId> = Vec::new();
    let mut seen_terms: DetHashSet<TermId> = DetHashSet::default();
    let mut seen_clauses: DetHashSet<TermId> = DetHashSet::default();
    // Walk conjuncts iteratively (assertion roots + nested `and`s).
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    let mut conjunct_or_clauses: Vec<TermId> = Vec::new();
    while let Some(a) = stack.pop() {
        match terms.get(a) {
            TermData::App(sym, args) if sym.name() == "and" => {
                for &c in args.iter().rev() {
                    stack.push(c);
                }
            }
            TermData::App(sym, _) if sym.name() == "or" => {
                if seen_clauses.insert(a) {
                    conjunct_or_clauses.push(a);
                }
            }
            _ => {}
        }
    }
    for clause in conjunct_or_clauses {
        let TermData::App(_, disjuncts) = terms.get(clause) else {
            continue;
        };
        if disjuncts.len() < domain.len() {
            continue;
        }
        let mut t: Option<TermId> = None;
        let mut covered: DetHashSet<TermId> = DetHashSet::default();
        let mut ok = true;
        for &d in disjuncts {
            let TermData::App(es, ea) = terms.get(d) else {
                ok = false;
                break;
            };
            if es.name() != "=" || ea.len() != 2 {
                ok = false;
                break;
            }
            // One side a domain constant, the other the common subject term.
            let (subj, cst) = if domain_set.contains(&ea[1]) && !domain_set.contains(&ea[0]) {
                (ea[0], ea[1])
            } else if domain_set.contains(&ea[0]) && !domain_set.contains(&ea[1]) {
                (ea[1], ea[0])
            } else {
                ok = false;
                break;
            };
            if *terms.sort(subj) != *dsort {
                ok = false;
                break;
            }
            match t {
                None => t = Some(subj),
                Some(prev) if prev == subj => {}
                Some(_) => {
                    ok = false;
                    break;
                }
            }
            covered.insert(cst);
        }
        if !ok || covered.len() != domain.len() {
            continue;
        }
        if let Some(t) = t {
            if seen_terms.insert(t) {
                out.push(t);
            }
        }
    }
    out
}

/// The set of domain constants occurring (as sub-terms) in `t`, under binders
/// included. (C3) depends on it being complete: a subject whose domain
/// constant hid under a `forall`/`exists`/`let` would count as constant-free
/// and be pinned first, `t_0 = c_0` with no fiat seeding of `c_0` — the
/// cell-pinning flaw. The walk descends every term kind [`live_terms`]
/// accepts (anything else made the pass decline already), and no binder of
/// the problem rebinds a domain constant's name (C1), so an occurrence under a
/// binder is the constant itself.
fn domain_consts_in(terms: &TermStore, t: TermId, domain: &[TermId]) -> Vec<TermId> {
    use ay_core::kani_compat::DetHashSet;
    let domain_set: DetHashSet<TermId> = domain.iter().copied().collect();
    let mut found: Vec<TermId> = Vec::new();
    let mut visited: DetHashSet<TermId> = DetHashSet::default();
    let mut stack = vec![t];
    while let Some(x) = stack.pop() {
        if !visited.insert(x) {
            continue;
        }
        if domain_set.contains(&x) {
            if !found.contains(&x) {
                found.push(x);
            }
            continue;
        }
        match terms.get(x) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            TermData::Const(_) | TermData::Var(..) => {}
            // Not reachable from a problem `live_terms` accepted; count every
            // domain constant so the subject is never eligible early.
            _ => {
                for &c in domain {
                    if !found.contains(&c) {
                        found.push(c);
                    }
                }
            }
        }
    }
    found
}

/// Append least-index symmetry-breaking clauses. Returns the number added.
///
/// For a PROVEN `S_n`-interchangeable domain `c_0..c_{n-1}` and totality
/// subjects `t` (terms asserted to take a value in the domain), process
/// subjects greedily: a subject is ELIGIBLE once every domain constant it
/// contains is already pinned ("used"). For the k-th processed subject add
///
///   `(or (= t u_1) .. (= t u_k) (= t c_next))`   (Used ∪ one fresh constant)
///
/// then mark `c_next` used.
///
/// SOUNDNESS (satisfiability-preserving; induction over emitted clauses):
/// given a model `M` of `F` (S_n-invariant over the domain) satisfying the
/// first k-1 clauses, subject `t_k`'s value equals some `M(c_j)` (totality).
/// If `c_j` is used or `c_j = c_next`, the k-th clause already holds.
/// Otherwise swap `c_j <-> c_next` — both UNUSED. The swap fixes `F`
/// (S_n-invariance), fixes the values of all used constants, and fixes the
/// values of every earlier subject `t_i` (eligibility: `t_i` contains only
/// used constants, and non-domain symbols are untouched), so earlier clauses
/// stay satisfied while the k-th becomes true. A model therefore survives in
/// every orbit. The subject ORDER (constants, then unary cells, then wider
/// terms) is a pure effectiveness heuristic — soundness only needs the
/// eligibility rule — chosen because pinning free constants and walking unary
/// orbits first turns injectivity/pigeonhole cores into unit cascades
/// (measured: SEQ009_size7 3711 -> 1 conflicts; the reverse order is inert).
///
/// The added clauses only STRENGTHEN the formula, so any model of the
/// augmented formula is a model of the original — the sat-side gates validate
/// against the untouched original assertions and need no reconstruction map.
fn add_least_index_symmetry_breaking(
    terms: &mut TermStore,
    assertions: &mut Vec<TermId>,
    domain: &[TermId],
    dsort: &Sort,
) -> usize {
    let subjects = collect_totality_terms(terms, assertions, domain, dsort);
    if subjects.is_empty() {
        return 0;
    }
    // (subject, domain constants it contains); order class = (#distinct domain
    // constants, arity bucket) — free constants first, then unary cells, then
    // binary and wider. Stable sort keeps first-seen order within a class.
    let mut ranked: Vec<(TermId, Vec<TermId>, usize)> = subjects
        .iter()
        .map(|&t| {
            let consts = domain_consts_in(terms, t, domain);
            let arity = match terms.get(t) {
                TermData::App(_, args) => args.len(),
                _ => 0,
            };
            let class = consts.len().max(arity);
            (t, consts, class)
        })
        .collect();
    ranked.sort_by_key(|(_, _, class)| *class);

    let mut used: Vec<TermId> = Vec::new();
    let mut unused: std::collections::VecDeque<TermId> = domain.iter().copied().collect();
    let mut processed = vec![false; ranked.len()];
    let mut added = 0usize;
    while !unused.is_empty() {
        // Prefer a subject whose domain constants are all pinned already.
        // Among eligible subjects order by CLASS (constants, then unary
        // orbits — the SEQ injectivity cascade — then wider cells), and
        // within a class by the STAIRCASE order (SEM/FALCON LNH): smallest
        // max pin-index of its constants first — cover the k-prefix subtable
        // before opening index k+1 — then first-seen. (Measured: staircase
        // fixed the qg iso_brn/iso_icl regressions that the plain first-seen
        // scan caused by walking whole rows.)
        let eligible = ranked
            .iter()
            .enumerate()
            .filter(|(i, (_, consts, _))| !processed[*i] && consts.iter().all(|c| used.contains(c)))
            .min_by_key(|(i, (_, consts, class))| {
                let max_pin = consts
                    .iter()
                    .map(|c| used.iter().position(|u| u == c).expect("eligible"))
                    .max()
                    .map_or(0, |p| p + 1);
                (*class, max_pin, *i)
            })
            .map(|(i, _)| i);
        let idx = match eligible {
            Some(i) => i,
            None => {
                // FIAT SEEDING: no eligible subject. Take the first unprocessed
                // subject and pin its not-yet-used constants by fiat (they join
                // Used with no constraint of their own). SOUND: the rescuing
                // permutation at this step is chosen to FIX every used constant
                // — including the fiat ones, which no earlier subject contains
                // (earlier subjects passed the eligibility rule against a
                // smaller Used) — and to swap only the two unused constants
                // `c_next <-> c_j`, exactly as in the eligible case. This seeds
                // families whose totality subjects are all function cells
                // (e.g. QG gensys: `f(c_0,c_0) in {c_0, c_1}` pins two).
                // Pick the unprocessed subject pinning the FEWEST new
                // constants (diagonal cells before off-diagonal); ties break
                // by ranked order.
                match (0..ranked.len())
                    .filter(|&i| !processed[i])
                    .min_by_key(|&i| ranked[i].1.iter().filter(|c| !used.contains(c)).count())
                {
                    Some(i) => {
                        let fiat: Vec<TermId> = ranked[i]
                            .1
                            .iter()
                            .filter(|c| !used.contains(c))
                            .copied()
                            .collect();
                        for c in fiat {
                            unused.retain(|&u| u != c);
                            used.push(c);
                        }
                        i
                    }
                    None => break,
                }
            }
        };
        processed[idx] = true;
        if used.len() >= domain.len() {
            break; // the clause would be the full-domain totality (tautology)
        }
        let t = ranked[idx].0;
        let Some(next) = unused.pop_front() else {
            break;
        };
        let mut lits: Vec<TermId> = Vec::with_capacity(used.len() + 1);
        for &u in &used {
            lits.push(terms.mk_eq(t, u));
        }
        lits.push(terms.mk_eq(t, next));
        let clause = terms.mk_or(lits);
        assertions.push(clause);
        used.push(next);
        added += 1;
    }
    added
}

/// Append SOUND symmetry-breaking assertions for the problem `candidates` was
/// computed over (`assertions` followed by the carried `assumptions`), using
/// only a domain of declared free constants (`free`, see
/// [`declared_free_constants`]). Returns the number of assertions appended.
///
/// Least-index prefix clauses are preferred; otherwise the lex-leader over the
/// adjacent transpositions `(c_i c_{i+1})` (which generate `S_n`): require the
/// model to be `<=_lex` its image under each swap, over a fixed sequence of
/// boolean atoms (function-table equalities `f(c_a,c_b)=c_c` and unary
/// predicates `p(c_a)`).
///
/// SOUND (lex-leader): for any generator `τ` that is a real symmetry (C1 + C2,
/// see the module doc), the orbit's lex-minimum model satisfies
/// `M <=_lex τ(M)` over ANY atom subset, so a solution survives. No cell value
/// is forced — the swap image `τ(atom)` is computed by simultaneous
/// `c_i<->c_{i+1}` substitution — so there is no idempotence assumption (the
/// bug that sank the cell-fixing version).
///
/// A pass that adds nothing leaves the term store exactly as it found it (see
/// [`domain_is_interchangeable`]): declining is the identity.
pub(crate) fn add_lnh_symmetry_breaking(
    terms: &mut TermStore,
    assertions: &mut Vec<TermId>,
    candidates: &DomainCandidates,
    free: &DetHashSet<TermId>,
) -> usize {
    // (C2)/(C4): the candidates must describe exactly this problem — the
    // invariance proof below runs over `candidates.problem`, so a vector that
    // moved since they were computed is refused rather than half-checked.
    if candidates.problem.get(..assertions.len()) != Some(assertions.as_slice()) {
        return 0;
    }
    let Some((domain, dsort)) = find_domain(terms, candidates, free) else {
        return 0;
    };
    let n = domain.len();
    // Domain-size gate: small finite-model instances (n < 6) already solve fast,
    // and the lex-leader constraint overhead would slow them (net-negative in an
    // efficacy sweep: all losses were n<=5, all gains n>=6). Only apply where the
    // S_n blowup actually causes timeouts. Overridable via AY_LNH_MIN_N.
    // B25: env override retired; the named constant is the value.
    let min_n: usize = 6;
    // The least-index scheme is a handful of short clauses (vs the lex-leader's
    // Tseitin chains), so it stays profitable one size below the lex gate
    // (measured: PEQ013_size5 3413 -> 15 conflicts). (B10: compiled constant;
    // the AY_LNH_LEASTIDX_MIN_N override nothing set is retired.)
    let li_min_n: usize = 5;
    let try_lex = n >= min_n.max(2);
    let try_li = least_index_enabled() && n >= li_min_n.max(2);
    if !try_lex && !try_li {
        return 0;
    }

    let funcs = find_binary_funcs(terms, &candidates.live, &dsort);
    let preds = find_unary_predicates(terms, &candidates.live, &dsort);
    if funcs.is_empty() && preds.is_empty() && !try_li {
        return 0; // no atoms to canonicalize over
    }

    // SOUNDNESS GATE: only apply if the domain is PROVABLY interchangeable.
    let interchangeable = domain_is_interchangeable(terms, &candidates.problem, &domain);
    if !interchangeable {
        return 0;
    }

    // From here on every term is built for the clauses; a scheme that ends up
    // adding none takes them back.
    let checkpoint = terms.rollback_checkpoint();
    let len_before = terms.len();
    let schemes = Schemes {
        try_li,
        try_lex,
        funcs,
        preds,
    };
    let added = add_symmetry_clauses(terms, assertions, &domain, &dsort, &schemes);
    if added == 0 && terms.len() != len_before {
        terms.rollback_to(checkpoint);
    }
    added
}

/// Which schemes [`add_symmetry_clauses`] may use, and the lex-leader's atom
/// sources.
struct Schemes {
    try_li: bool,
    try_lex: bool,
    funcs: Vec<Symbol>,
    preds: Vec<Symbol>,
}

/// The clause-building half of [`add_lnh_symmetry_breaking`], over a domain
/// already proven interchangeable.
fn add_symmetry_clauses(
    terms: &mut TermStore,
    assertions: &mut Vec<TermId>,
    domain: &[TermId],
    dsort: &Sort,
    schemes: &Schemes,
) -> usize {
    let Schemes {
        try_li,
        try_lex,
        funcs,
        preds,
    } = schemes;
    let n = domain.len();
    // Least-index orbit-prefix scheme (preferred: unit-propagation cascades).
    // MUTUALLY EXCLUSIVE with the lex-leader below — each scheme alone is
    // satisfiability-preserving, but their canonical-model choices differ, so
    // stacking both could exclude every model of a satisfiable orbit.
    if *try_li {
        let added = add_least_index_symmetry_breaking(terms, assertions, domain, dsort);
        if added > 0 {
            return added;
        }
    }
    if !*try_lex || (funcs.is_empty() && preds.is_empty()) {
        return 0; // lex-leader gated out, or no atoms for it
    }

    // Fixed atom sequence: function-table equalities, then unary predicates.
    let mut atoms: Vec<TermId> = Vec::new();
    'build: for f in funcs {
        for &a in domain {
            for &b in domain {
                let cell = terms.mk_app(f.clone(), [a, b], dsort.clone());
                for &c in domain {
                    atoms.push(terms.mk_eq(cell, c));
                    if atoms.len() >= MAX_LEX_ATOMS {
                        break 'build;
                    }
                }
            }
        }
    }
    if atoms.len() < MAX_LEX_ATOMS {
        'p: for p in preds {
            for &a in domain {
                atoms.push(terms.mk_app(p.clone(), [a], Sort::Bool));
                if atoms.len() >= MAX_LEX_ATOMS {
                    break 'p;
                }
            }
        }
    }
    if atoms.is_empty() {
        return 0;
    }

    // For each adjacent transposition, assert M <=_lex swap(M).
    let mut added = 0usize;
    for i in 0..n - 1 {
        let ci = domain[i];
        let ci1 = domain[i + 1];
        let from = [ci, ci1];
        let to = [ci1, ci];
        let swapped: Vec<TermId> = atoms
            .iter()
            .map(|&at| terms.substitute(at, &from, &to))
            .collect();
        let le = lex_le(terms, &atoms, &swapped);
        if le != terms.true_term() {
            assertions.push(le);
            added += 1;
        }
    }
    added
}

#[cfg(test)]
mod tests {
    use super::*;

    // 6 elements: the smallest domain that clears the default AY_LNH_MIN_N=6
    // gate, so the "fires" tests exercise the real shipped configuration
    // (a 3-element domain silently no-ops at the size gate).
    fn domain6(t: &mut TermStore) -> (Sort, Vec<TermId>) {
        let s = Sort::Uninterpreted("U".to_string());
        let c: Vec<TermId> = (0..6)
            .map(|i| t.mk_var(format!("c_{i}"), s.clone()))
            .collect();
        (s, c)
    }

    /// Run the pass the way `check_sat` does, with every candidate constant
    /// admitted as declared-free (these fixtures declare all of them).
    fn apply(t: &mut TermStore, assertions: &mut Vec<TermId>) -> usize {
        let candidates = domain_candidates(t, assertions, &[]);
        let free: DetHashSet<TermId> = candidates.constants().into_iter().collect();
        add_lnh_symmetry_breaking(t, assertions, &candidates, &free)
    }

    /// Symmetric formula with a unary predicate => interchangeable => LNH fires.
    #[test]
    fn test_sig_ordering_fires_when_symmetric() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = Vec::new();
        // totality clauses for cells f(c_i,c_j) (symmetric domain signal)
        for &a in &c {
            for &b in &c {
                let cell = t.mk_app(Symbol::named("f"), [a, b], s.clone());
                let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(cell, ci)).collect();
                assertions.push(t.mk_or(disj));
            }
        }
        // a unary predicate p over the domain, used symmetrically (totality of p
        // over all c_i is symmetric)
        for &ci in &c {
            let _ = t.mk_app(Symbol::named("p"), [ci], Sort::Bool);
        }
        // reference the predicate symmetrically so it appears; add p(c_i) OR ¬p(c_i)
        // (a tautology, symmetric) so the assertion set stays S_n-invariant.
        for &ci in &c {
            let p = t.mk_app(Symbol::named("p"), [ci], Sort::Bool);
            let np = t.mk_not(p);
            assertions.push(t.mk_or(vec![p, np]));
        }
        let added = apply(&mut t, &mut assertions);
        assert!(
            added > 0,
            "sig-ordering should fire on symmetric domain w/ predicate"
        );
    }

    /// Asymmetric unit singles out c_0 => not interchangeable => no LNH.
    #[test]
    fn test_sig_ordering_refuses_non_interchangeable() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = Vec::new();
        for &a in &c {
            for &b in &c {
                let cell = t.mk_app(Symbol::named("f"), [a, b], s.clone());
                let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(cell, ci)).collect();
                assertions.push(t.mk_or(disj));
            }
        }
        let p0 = t.mk_app(Symbol::named("p"), [c[0]], Sort::Bool);
        assertions.push(p0); // asserts p(c_0) only — breaks interchangeability
        let added = apply(&mut t, &mut assertions);
        assert_eq!(added, 0, "must refuse a non-interchangeable domain");
    }

    /// No binary function and no unary predicate: the lex-leader has no atoms,
    /// but the LEAST-INDEX scheme still pins the totality subject (`a = c_0`).
    /// (Before least-index landed this was a full no-op.)
    #[test]
    fn test_least_index_pins_where_lex_leader_had_no_atoms() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        // a domain-valued witness `a` with a totality clause (the domain signal),
        // but NO binary function and NO unary predicate.
        let a = t.mk_var("a", s.clone());
        let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(a, ci)).collect();
        let mut assertions = vec![t.mk_or(disj)];
        let added = apply(&mut t, &mut assertions);
        assert_eq!(added, 1, "least-index pins the lone totality subject");
        let pin = *assertions.last().expect("clause added");
        match t.get(pin) {
            TermData::App(sym, args) if sym.name() == "=" => {
                assert!(args.contains(&a) && args.contains(&c[0]));
            }
            other => panic!("expected unit pin (= a c_0), got {other:?}"),
        }
    }

    /// Least-index: free constants get prefix clauses `x_k in {c_0..c_k}` —
    /// the PHP(n+1,n) cascade shape. First clause must be the unit `x = c_0`.
    #[test]
    fn test_least_index_prefix_clauses_on_free_constants() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let xs: Vec<TermId> = (0..3)
            .map(|k| t.mk_var(format!("x_{k}"), s.clone()))
            .collect();
        let mut assertions = Vec::new();
        for &x in &xs {
            let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(x, ci)).collect();
            assertions.push(t.mk_or(disj));
        }
        let n_orig = assertions.len();
        let added = apply(&mut t, &mut assertions);
        assert_eq!(added, 3, "one prefix clause per free constant");
        // First added clause is the unit pin (= x c) for some x, c.
        let first = assertions[n_orig];
        match t.get(first) {
            TermData::App(sym, args) if sym.name() == "=" => {
                assert!(args.iter().any(|a| c.contains(a)));
            }
            other => panic!("expected unit equality pin, got {other:?}"),
        }
    }

    /// Least-index fiat seeding: all subjects are binary cells (no free
    /// constant), so the first clause pins the cell's own constants by fiat
    /// and still emits `f(c_0,c_0) in {c_0, c_1}`-shaped prefixes.
    #[test]
    fn test_least_index_fiat_seeds_cell_only_subjects() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = Vec::new();
        for &a in &c {
            for &b in &c {
                let cell = t.mk_app(Symbol::named("f"), [a, b], s.clone());
                let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(cell, ci)).collect();
                assertions.push(t.mk_or(disj));
            }
        }
        let added = apply(&mut t, &mut assertions);
        assert!(added > 0, "fiat seeding must fire on cell-only subjects");
    }

    /// A totality clause under NOT must not be used as a least-index subject
    /// (positivity is a soundness premise) — and with nothing else symmetric
    /// to work from, the pass adds nothing.
    #[test]
    fn test_least_index_ignores_negative_totality() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let x = t.mk_var("x", s.clone());
        let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(x, ci)).collect();
        let tot = t.mk_or(disj.clone());
        let neg = t.mk_not(tot);
        // Keep a POSITIVE totality clause on a different subject so
        // find_domain sees a domain, but x's clause is negative.
        let y = t.mk_var("y", s.clone());
        let disj_y: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(y, ci)).collect();
        let tot_y = t.mk_or(disj_y);
        let mut assertions = vec![neg, tot_y];
        let subjects = collect_totality_terms(&t, &assertions, &c, &s);
        assert_eq!(subjects, vec![y], "only the positive clause's subject");
        let _ = apply(&mut t, &mut assertions);
    }

    /// (kept) totality-only symmetric with a binary function => lex-leader fires.
    #[test]
    fn test_lex_leader_fires_with_function() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = Vec::new();
        for &a in &c {
            for &b in &c {
                let cell = t.mk_app(Symbol::named("f"), [a, b], s.clone());
                let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(cell, ci)).collect();
                assertions.push(t.mk_or(disj));
            }
        }
        let added = apply(&mut t, &mut assertions);
        assert!(
            added > 0,
            "lex-leader should fire on symmetric domain w/ function"
        );
    }

    /// Six free constants `x_k` each with a totality clause: the shape on
    /// which the pass fires (least-index pins the subjects).
    fn symmetric_totality(t: &mut TermStore, s: &Sort, c: &[TermId]) -> Vec<TermId> {
        (0..3)
            .map(|k| {
                let x = t.mk_var(format!("x_{k}"), s.clone());
                let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(x, ci)).collect();
                t.mk_or(disj)
            })
            .collect()
    }

    /// (C1) #lnh-compound-domain: a domain of COMPOUND terms `(f a_i)` passes
    /// the substitution check whenever nothing else mentions `(f a_i)`, but no
    /// model symmetry swaps their values (they are tied to the `a_i`). The
    /// least-index pin `e = (f a_0)` then made `l02_lnh_compound_domain_uf`
    /// (z3: sat) unsat. Refused: elements must be bare constant symbols.
    #[test]
    fn test_refuses_compound_term_domain() {
        let mut t = TermStore::new();
        let s = Sort::Uninterpreted("U".to_string());
        let e = t.mk_var("e", s.clone());
        let cells: Vec<TermId> = (0..6)
            .map(|i| {
                let a = t.mk_var(format!("a_{i}"), s.clone());
                t.mk_app(Symbol::named("f"), [a], s.clone())
            })
            .collect();
        let disj: Vec<TermId> = cells.iter().map(|&ci| t.mk_eq(e, ci)).collect();
        let mut assertions = vec![t.mk_or(disj)];
        let candidates = domain_candidates(&t, &assertions, &[]);
        assert!(
            candidates.constants().is_empty(),
            "compound elements nominate nothing"
        );
        assert_eq!(apply(&mut t, &mut assertions), 0);
    }

    /// (C1) the frontend authority decides: a structurally perfect domain whose
    /// elements are not all declared free constants is refused.
    #[test]
    fn test_refuses_domain_outside_declared_free_constants() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = symmetric_totality(&mut t, &s, &c);
        let candidates = domain_candidates(&t, &assertions, &[]);
        let free: DetHashSet<TermId> = c[..5].iter().copied().collect();
        assert_eq!(
            add_lnh_symmetry_breaking(&mut t, &mut assertions, &candidates, &free),
            0,
            "c_5 is not a declared free constant"
        );
        let free: DetHashSet<TermId> = c.iter().copied().collect();
        assert!(
            add_lnh_symmetry_breaking(&mut t, &mut assertions, &candidates, &free) > 0,
            "the same shape over declared constants fires"
        );
    }

    /// (C1) #dt-fd-lnh-ctor: nullary datatype CONSTRUCTORS are interpreted (a
    /// tester `is-C3` reads them), so they are never a domain even if a caller
    /// admitted them.
    #[test]
    fn test_refuses_datatype_constructor_domain() {
        let mut t = TermStore::new();
        let s = Sort::Uninterpreted("E".to_string());
        let c: Vec<TermId> = (0..6)
            .map(|i| {
                let name = format!("C{i}");
                t.register_constructor_fields(&name, Vec::new());
                t.mk_fresh_named_var(name, s.clone())
            })
            .collect();
        let e = t.mk_var("e", s.clone());
        let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(e, ci)).collect();
        let mut assertions = vec![t.mk_or(disj)];
        let tester = t.mk_app(Symbol::named("is-C3"), [e], Sort::Bool);
        assertions.push(tester);
        assert_eq!(
            apply(&mut t, &mut assertions),
            0,
            "constructors are interpreted"
        );
    }

    /// (C1) a domain constant whose spelling a quantifier binds could be
    /// captured by the substitution; such a domain is refused.
    #[test]
    fn test_refuses_domain_name_bound_in_problem() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = symmetric_totality(&mut t, &s, &c);
        let p3 = t.mk_app(Symbol::named("p"), [c[3]], Sort::Bool);
        assertions.push(t.mk_forall(vec![("c_3".to_string(), s.clone())], p3));
        let candidates = domain_candidates(&t, &assertions, &[]);
        let free: DetHashSet<TermId> = candidates.constants().into_iter().collect();
        assert!(find_domain(&t, &candidates, &free).is_none());
    }

    /// (C2) the invariance proof covers carried ASSUMPTIONS: `p(c_0)` assumed
    /// beside a symmetric assertion set breaks the symmetry.
    #[test]
    fn test_assumption_breaks_interchangeability() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = symmetric_totality(&mut t, &s, &c);
        let p0 = t.mk_app(Symbol::named("p"), [c[0]], Sort::Bool);
        let candidates = domain_candidates(&t, &assertions, &[p0]);
        let free: DetHashSet<TermId> = candidates.constants().into_iter().collect();
        assert_eq!(
            add_lnh_symmetry_breaking(&mut t, &mut assertions, &candidates, &free),
            0
        );
    }

    /// (C4) #lnh-stale-domain: a totality or-node that only a POPPED scope
    /// asserted is still in the term store; it must not nominate a domain for
    /// the live problem (the old store-wide scan let it drive a lex-leader over
    /// the live problem's predicates, `l05_lnh_stale_popped_domain`).
    #[test]
    fn test_stale_or_node_nominates_nothing() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let stale = symmetric_totality(&mut t, &s, &c);
        assert_ne!(stale, [] as [TermId; 0]);
        // A unary predicate over the domain exists in the store (lex-leader atoms).
        for &ci in &c {
            let _ = t.mk_app(Symbol::named("p"), [ci], Sort::Bool);
        }
        let mut assertions = vec![t.mk_distinct(c.clone())];
        let candidates = domain_candidates(&t, &assertions, &[]);
        assert!(
            candidates.constants().is_empty(),
            "only live or-nodes nominate"
        );
        assert_eq!(apply(&mut t, &mut assertions), 0);
    }

    /// The candidates must describe the vector they are applied to.
    #[test]
    fn test_refuses_candidates_of_another_problem() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = symmetric_totality(&mut t, &s, &c);
        let candidates = domain_candidates(&t, &assertions, &[]);
        let free: DetHashSet<TermId> = candidates.constants().into_iter().collect();
        let p0 = t.mk_app(Symbol::named("p"), [c[0]], Sort::Bool);
        assertions.insert(0, p0);
        assert_eq!(
            add_lnh_symmetry_breaking(&mut t, &mut assertions, &candidates, &free),
            0
        );
    }

    /// A DECLINED pass is the identity on the term store (2026-10-09 audit
    /// lv5/lv6): the swap check's images are taken back, so the ids every
    /// later term is minted with do not depend on whether the pass ran.
    #[test]
    fn test_declined_pass_leaves_store_untouched() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = symmetric_totality(&mut t, &s, &c);
        // `p(c_0)` singles out `c_0`: every transposition `(c_0 c_i)` maps it
        // to a new term `p(c_i)`, which the check must not leave behind.
        let p0 = t.mk_app(Symbol::named("p"), [c[0]], Sort::Bool);
        assertions.push(p0);
        let before = t.len();
        let snapshot = assertions.clone();
        assert_eq!(apply(&mut t, &mut assertions), 0, "asymmetric: declined");
        assert_eq!(t.len(), before, "a declined pass interned no term");
        assert_eq!(assertions, snapshot);
        let p1 = t.mk_app(Symbol::named("p"), [c[1]], Sort::Bool);
        assert_eq!(p1.index(), before, "the next term gets the next id");
    }

    /// The swap check of a pass that FIRES takes its images back too; only
    /// the clauses it adds are new terms.
    #[test]
    fn test_firing_pass_keeps_only_its_clauses() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = symmetric_totality(&mut t, &s, &c);
        let n_orig = assertions.len();
        let candidates = domain_candidates(&t, &assertions, &[]);
        let free: DetHashSet<TermId> = candidates.constants().into_iter().collect();
        let before = t.len();
        assert!(domain_is_interchangeable(&mut t, &candidates.problem, &c));
        assert_eq!(t.len(), before, "the proven swap check interned nothing");
        let added = add_lnh_symmetry_breaking(&mut t, &mut assertions, &candidates, &free);
        assert_eq!(added, 3);
        assert_eq!(assertions.len(), n_orig + added);
    }

    /// (C6) a quantified problem nominates no domain, however symmetric.
    #[test]
    fn test_quantified_problem_nominates_nothing() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = symmetric_totality(&mut t, &s, &c);
        let w = t.mk_var("w", s.clone());
        let pw = t.mk_app(Symbol::named("p"), [w], Sort::Bool);
        assertions.push(t.mk_forall(vec![("w".to_string(), s.clone())], pw));
        let candidates = domain_candidates(&t, &assertions, &[]);
        assert!(candidates.constants().is_empty(), "quantified: declined");
        assert_eq!(apply(&mut t, &mut assertions), 0);
    }

    /// (C3) #lnh-binder-eligibility (2026-10-02 audit, q5/q6): a subject's
    /// domain constants are found under `forall`/`exists`/`let` too. Missing
    /// them made `(h (ite (forall ((y U)) (r y c_3)) a b))` look constant-free,
    /// so least-index would pin it before `c_3` is used.
    #[test]
    fn test_domain_consts_in_descends_binders() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let a = t.mk_var("a", s.clone());
        let b = t.mk_var("b", s.clone());
        let y = t.mk_var("y", s.clone());
        let r = t.mk_app(Symbol::named("r"), [y, c[3]], Sort::Bool);
        let all = t.mk_forall(vec![("y".to_string(), s.clone())], r);
        let pick = t.mk_ite(all, a, b);
        let under_forall = t.mk_app(Symbol::named("h"), [pick], s.clone());
        assert_eq!(domain_consts_in(&t, under_forall, &c), vec![c[3]]);
        let some = t.mk_exists(vec![("y".to_string(), s.clone())], r);
        let pick = t.mk_ite(some, a, b);
        let under_exists = t.mk_app(Symbol::named("h"), [pick], s.clone());
        assert_eq!(domain_consts_in(&t, under_exists, &c), vec![c[3]]);
        let z = t.mk_var("z", s.clone());
        let body = t.mk_app(Symbol::named("h"), [z], s.clone());
        let bound = t.mk_let(vec![("z".to_string(), c[2])], body);
        assert_eq!(domain_consts_in(&t, bound, &c), vec![c[2]]);
    }
}
