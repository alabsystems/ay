//! THE COMMON CURRENCY — what a lane may claim, and how strong the evidence
//! behind it has to be before it is allowed to end the solve.
//!
//! # Why this module exists
//!
//! ay-milp is a PORTFOLIO of exact engines where the competition ships one.
//! That is its structural advantage, and it is only an advantage if adding an
//! engine cannot make the system worse. Before this module there was no unit in
//! which "worse" could even be stated: routing was greedy and irreversible, the
//! first recogniser that matched owned the whole solve, and the two things a
//! verdict is made of — WHAT was decided and WHAT BACKS IT — were compared
//! nowhere. Three measured failures followed directly, and all three are
//! consequences of the missing unit rather than of any one lane:
//!
//! * a lane that DECLINED could still delete a proof (see
//!   [`crate::bab::structural_prologue`] — `markshare_5_0`, 20 s timeout with a
//!   wrong incumbent against a 0.15 s proof);
//! * a REPLAY refutation could preempt a SUCCINCT tree certificate on the
//!   DEFAULT path (`W1_unsat_v9_c14_000008`, 758 unverifiable bytes against
//!   19,664 that `verify` accepts at exit 0);
//! * an admission scan with no bound of its own could spend 5.3x the caller's
//!   entire deadline and then decline (`control30-3-2-3`, 15.8 s against a 3 s
//!   limit, ZERO nodes searched).
//!
//! # The invariant
//!
//! > **THE PORTFOLIO MUST PROVABLY DOMINATE ITS OWN FALLBACK.** For every model,
//! > routing must yield a verdict at least as strong AND evidence at least as
//! > strong as `SolveOpts::with_structure_routing(false)` would have.
//!
//! [`may_close`] is that invariant, as one function, on the verdict-ending path
//! for replay and other floor-declared lanes. Their authors satisfy this
//! evidence contract without understanding the portfolio's certificate
//! formats. Typed-certified arms instead have to cross their independently
//! checked supplemental-proof boundary.
//!
//! # Two axes, and why evidence is per CLAIM
//!
//! Evidence is a property of a CLAIM, not of an `Outcome`. This is not a
//! refinement, it is forced by measurement. `sat_relu` on the ny W1 captures:
//!
//! ```text
//!   W1_sat_v16_c39_000000   routed OPTIMAL 0.039 s   anchor OPTIMAL 0.046 s   (tie, routed faster)
//!   W1_unsat_v9_c14_000008  routed REPLAY  exit 10   anchor SUCCINCT exit 0   (routed strictly worse)
//! ```
//!
//! The same lane TIES the anchor on `PointExists` and LOSES to it on
//! `Infeasible`. A per-`Outcome` floor would have to bar both scopes or admit
//! both: barring both throws away a class ay decides 46/46 where Gurobi 12.0.3
//! decides 34/46, and admitting both is the evidence downgrade above. Splitting
//! the floor by claim keeps the fast SAT path and demotes only the refutation.

//! # What this does NOT yet cover, stated plainly
//!
//! `DECLARED` is the authoritative registry of verdict-owning lanes that
//! pass through the evidence floor. It includes both route-specific policies
//! and conservative replay-reduction rows shared by families whose exhaustive
//! argument has no exported object. Typed-certified arms leave through their
//! independently checked supplemental-proof gate instead. Any route absent
//! from both mechanisms still publishes on its own authority, so the honest
//! reading remains: the invariant is ENFORCED at declared gates and ASSUMED
//! elsewhere.
//!
//! That is not a design position, it is a work boundary, and the two follow-ons
//! are concrete:
//!
//! * add a row here for each remaining lane — most carry typed certificates and
//!   will clear the floor trivially, which is exactly the cheap outcome a
//!   registry is for;
//! * close the SIDE CHANNEL. `cert_io::EmitCtx` still takes multiple typed
//!   optional artifact fields wired straight from `BabSession`, so the
//!   emitter can publish evidence the returned verdict never carried, and
//!   `Outcome::evidence_shape` — which intentionally sees only outcome-resident
//!   fields — reports a verdict backed by a verified single-row DP refutation as
//!   lacking a Farkas or tree artifact. Folding the side-channel artifacts into
//!   the verdict is what would make the floor unbypassable rather than merely
//!   observed. Until then this module is a checked convention, not a proof.

use crate::model::Model;
use crate::opts::SolveOpts;

/// How strongly ONE claim is backed. **Total order**, weakest first.
///
/// This is [`crate::cert_io::EvidenceKind`] refined by one rung. `Witness` sits
/// between `Replay` and `Succinct` because a returned point is not an exported
/// artifact but is not trust-only either: `finish`'s `validate_witnesses`
/// re-checks every original row and bound of the caller's model before the
/// verdict leaves, so a wrong point cannot be published. `verify` reports that
/// standing as PARTIAL (exit 11) — non-zero, but strictly above the exit 10 a
/// bare replay earns.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Ev {
    /// Trust only. Nothing was exported and nothing was re-checked.
    None = 0,
    /// No exported object: re-verification means re-running the solver.
    Replay = 1,
    /// A point, re-checked exactly against every original row and bound.
    Witness = 2,
    /// An exported artifact with a bounded exact re-check against the model.
    Succinct = 3,
}

impl Ev {
    /// The `.ayc` wire word, for the census line and for diagnostics.
    pub(crate) fn token(self) -> &'static str {
        match self {
            Self::None => "NONE",
            Self::Replay => "REPLAY",
            Self::Witness => "WITNESS",
            Self::Succinct => "SUCCINCT",
        }
    }
}

/// The four things a verdict can assert about a model.
///
/// Deliberately NOT `Optimal`. An optimum is `PointExists` AND `NoBetterThan`
/// at the same value, closed by the ordinary termination rule — so a lane
/// cannot assert one, it can only supply the two halves and let them meet. That
/// removes the single most dangerous power a lane holds, and it is why the
/// `markshare_5_0` shape cannot recur even if `structural_prologue` were
/// bypassed again: the lattice supplies bound 1 and a value-1 point, and
/// nothing "claims" the model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum ClaimKind {
    /// A feasible point of the caller's model exists (and here it is).
    PointExists = 0,
    /// No feasible point beats value `v` — the dual half of an optimum.
    NoBetterThan = 1,
    /// The feasible set is empty.
    Infeasible = 2,
    /// The objective is unbounded on a non-empty feasible set.
    Unbounded = 3,
}

impl ClaimKind {
    /// Every claim, for the conformance tests that sweep the floor table.
    /// Test-only by design: shipping code always knows WHICH claim it is
    /// asking about, and a loop over all four in the hot path would be a
    /// smell rather than a feature.
    #[cfg(test)]
    pub(crate) const ALL: [ClaimKind; 4] = [
        ClaimKind::PointExists,
        ClaimKind::NoBetterThan,
        ClaimKind::Infeasible,
        ClaimKind::Unbounded,
    ];

    pub(crate) fn token(self) -> &'static str {
        match self {
            Self::PointExists => "point-exists",
            Self::NoBetterThan => "no-better-than",
            Self::Infeasible => "infeasible",
            Self::Unbounded => "unbounded",
        }
    }
}

/// **THE ONE PLACE "how strong is the fallback" IS WRITTEN DOWN.**
///
/// Returns the best evidence the ANCHOR — `SolveOpts::with_structure_routing(false)`, the
/// native proof-producing tree — could still attach to `claim` on this model
/// under these options. Every entry is derived from what the anchor's own exit
/// path actually does, not from what it aspires to:
///
/// * **`PointExists`** — `Ev::Witness`, always. `finish` runs `validate_witnesses`
///   on every returned point, re-checking each original row and bound exactly.
///   It is never more: no MILP feasible point carries an exported artifact
///   beyond itself.
/// * **`NoBetterThan`** — splits on whether there is an OBJECTIVE at all, and
///   this cell took three tries to get right, so the wrong answers are recorded
///   with it.
///
///   A model carrying no objective makes no dual claim worth backing: every
///   feasible point is optimal and the anchor's own emitter says so — on
///   `W1_sat_v16_c39_000000` it writes `evidence dual NONE trivial-optcert`.
///   So `Ev::None`, and lanes that answer those models close immediately, which
///   is what keeps the ny ReLU class at its measured speed.
///
///   An objective-bearing model — including an explicitly supplied all-zero
///   objective — lets the anchor export a checkable `OptimalityCertificate`,
///   and it does: on the singleton-substitution model
///   `min x + z  s.t.  x + z = 1, z binary, x free`, the anchor writes
///   `evidence dual SUCCINCT optcert` while the routed default writes
///   `evidence dual REPLAY pb-portfolio-projection-optimal`. That downgrade is
///   present at HEAD, on the DEFAULT path, and it is a SECOND instance of the
///   `W1_unsat_v9_c14_000008` defect through a different lane. So `Ev::Succinct`.
///
///   Two rejected drafts, recorded because each looked right: keying the cap on
///   a public outcome's shape cannot express which certificate the anchor can
///   still produce, while a blanket replay assumption would defer all thirteen
///   fast OPTIMAL answers on the W1 corpus to buy evidence the anchor does not
///   have. `has_objective` is the line the measurements actually fall on.
/// * **`Infeasible`** — `Ev::Succinct`. A tree-certificate leaf budget can
///   provide the artifact (default 256), and independently the post-tree root
///   relaxation can attach an exact Farkas certificate even when that leaf
///   budget is zero. This table is an upper bound on what is reachable, not a
///   prediction for a particular model, so disabling one source cannot lower
///   the cell while the other remains available. The anchor emits 19,664
///   SUCCINCT bytes that `verify` accepts at exit 0 on
///   `W1_unsat_v9_c14_000008`; `Outcome::evidence_shape` marks that pairing
///   `FieldsPresent`, and `Outcome::check_against` performs the authoritative replay.
/// * **`Unbounded`** — `Ev::None`. The public outcome has no exported ray, so
///   there is nothing here for a lane to lose.
///
/// This is an UPPER bound on the anchor, so [`may_close`]'s `floor >= cap` test
/// is conservative in the sound direction: it can bar a lane that would in fact
/// have tied, costing speed, and it can never admit one that would have lost
/// evidence.
///
/// It is deliberately a table and not a prediction. It never asks whether the
/// tree WILL close — only what evidence is structurally on the table if it
/// does. A lane barred here is not discarded; it is DEFERRED behind the
/// anchor's bounded first refusal (see [`AnchorFirstRefusal`]), so the cost of
/// a conservative entry is bounded latency; the raw conclusion is retained
/// until caller-policy finalization.
pub(crate) fn anchor_cap(model: &Model, _opts: &SolveOpts, claim: ClaimKind) -> Ev {
    match claim {
        ClaimKind::PointExists => Ev::Witness,
        ClaimKind::NoBetterThan => {
            if model.has_objective() {
                Ev::Succinct
            } else {
                Ev::None
            }
        }
        ClaimKind::Infeasible => Ev::Succinct,
        ClaimKind::Unbounded => Ev::None,
    }
}

/// Every claim `outcome` asserts. A verdict may assert more than one — an
/// optimum is a POINT and a BOUND, and both halves must clear the floor before
/// the lane that produced it is allowed to end the solve.
///
/// This is why there is no `ClaimKind::Optimal`: an optimum is not a primitive
/// a lane can assert, it is two claims that happen to meet.
pub(crate) fn claims_of(outcome: &crate::outcome::Outcome) -> &'static [ClaimKind] {
    use crate::outcome::Outcome;
    match outcome {
        Outcome::Optimal { .. } => &[ClaimKind::PointExists, ClaimKind::NoBetterThan],
        Outcome::Feasible {
            dual_bound: Some(_),
            ..
        } => &[ClaimKind::PointExists, ClaimKind::NoBetterThan],
        Outcome::Feasible { .. } => &[ClaimKind::PointExists],
        Outcome::Infeasible { .. } => &[ClaimKind::Infeasible],
        Outcome::Unbounded => &[ClaimKind::Unbounded],
        // `Bound` asserts only the dual half; `Unknown` asserts nothing, and a
        // lane returning it never reaches the floor because it never closes.
        Outcome::Bound { .. } => &[ClaimKind::NoBetterThan],
        Outcome::Unknown { .. } => &[],
    }
}

/// **THE GATE, APPLIED TO A WHOLE VERDICT.** May this lane end the solve with
/// this outcome, or must every claim in it stand behind the anchor?
///
/// All-or-nothing on purpose: a verdict is published as one object, so a
/// verdict with one below-floor claim is deferred whole. Splitting it would
/// mean publishing half an optimum, which no consumer can use.
pub(crate) fn may_close_outcome(
    lane: &LaneFloor,
    outcome: &crate::outcome::Outcome,
    model: &Model,
    opts: &SolveOpts,
) -> bool {
    claims_of(outcome)
        .iter()
        .all(|&c| may_close(lane, c, model, opts))
}

#[cfg(test)]
fn model_has_integrality(model: &Model) -> bool {
    (0..model.num_cols()).any(|j| {
        !matches!(
            model.col_kind(crate::model::Col(u32::try_from(j).unwrap_or(u32::MAX))),
            crate::model::ColKind::Continuous
        )
    })
}

/// What a lane can produce, per claim. A FACT ABOUT THE LANE'S CODE, not about
/// the instance — which is why it is a `const` and can be reviewed once.
#[derive(Debug, Clone, Copy)]
pub(crate) struct LaneFloor {
    /// Stable identity. Appears in the trace and in test failures.
    pub(crate) lane: &'static str,
    /// Best evidence this lane attaches, indexed by [`ClaimKind`].
    pub(crate) floor: [Ev; 4],
}

impl LaneFloor {
    pub(crate) const fn get(&self, claim: ClaimKind) -> Ev {
        self.floor[claim as usize]
    }
}

/// **THE INVARIANT, AS ONE FUNCTION.**
///
/// May `lane` END the solve by asserting `claim`, or must it stand behind the
/// anchor? True exactly when the lane's evidence for that claim is at least as
/// strong as anything the anchor could still have attached to it.
///
/// The verdict axis needs no test here: a lane that returns a decided verdict
/// is by construction at least as strong as the anchor's `Unknown`, and a lane
/// whose verdict is WRONG is caught downstream by `validate_witnesses` and by
/// the typed certificate re-verification, neither of which this gate replaces.
/// What was missing was the EVIDENCE axis, and this is it.
pub(crate) fn may_close(
    lane: &LaneFloor,
    claim: ClaimKind,
    model: &Model,
    opts: &SolveOpts,
) -> bool {
    lane.get(claim) >= anchor_cap(model, opts, claim)
}

// ---------------------------------------------------------------------------
// The declared floors. ADDING A LANE MEANS ADDING A ROW HERE.
// ---------------------------------------------------------------------------

/// `sat_relu` — the bounded, proof-producing ny ReLU-verification route.
///
/// SAT side: the lifted point is a real point of the caller's model and the
/// checked-point finalizer preserves an explicit zero objective with an
/// independently checkable empty-multiplier optimality certificate.
///
/// UNSAT side: the single bounded ay-sat pass exports a model-bound
/// `sat-relu-rup` artifact only after independent RUP replay. The public
/// checker rebuilds the exact projection and replays that artifact again, so
/// infeasibility is `Succinct` rather than the old replay-only claim.
///
/// All asserted claims therefore tie or exceed the anchor's reachable evidence
/// and this route may close without paying anchor first refusal.
pub(crate) const SAT_RELU_PROOF: LaneFloor = LaneFloor {
    lane: "sat-relu-proof",
    floor: [Ev::Witness, Ev::Succinct, Ev::Succinct, Ev::None],
};

/// Legacy ordinary-CDCL fallback for an explicitly memory-unbounded caller.
///
/// A SAT point still receives exact source-model checking and, for an explicit
/// zero objective, a succinct empty-multiplier optimum certificate. An UNSAT
/// result has no retained RUP object, however, so it remains `Replay` and must
/// stand behind a reachable tree certificate. Keeping this as a separate row
/// prevents the bounded proof route's upgrade from laundering fallback UNSAT.
pub(crate) const SAT_RELU_FALLBACK: LaneFloor = LaneFloor {
    lane: "sat-relu-fallback",
    floor: [Ev::Witness, Ev::Succinct, Ev::Replay, Ev::None],
};

/// `block_angular` — exact Dantzig--Wolfe pricing for bounded integral
/// conservation chains.
///
/// The reconstructed source point is checked exactly against the caller's
/// model (`PointExists = Witness`). Its Lagrangian lower bound is exported as
/// a model-bound artifact whose verifier rebuilds every recognized block and
/// exhaustively re-prices it (`NoBetterThan = Succinct`). The route returns
/// only an optimum, so it makes no infeasibility or unboundedness claim.
pub(crate) const BLOCK_ANGULAR: LaneFloor = LaneFloor {
    lane: "block-angular",
    floor: [Ev::Witness, Ev::Succinct, Ev::None, Ev::None],
};

/// Exact GF(2) enumeration optimum without an exported dual artifact.
///
/// The point is rechecked against the source model. A nontrivial optimality
/// argument is retained as replay evidence and must stand behind an anchor
/// certificate. Typed parity refutations use their model-bound artifact and do
/// not pass through this row.
pub(crate) const PARITY_OPTIMUM_REPLAY: LaneFloor = LaneFloor {
    lane: "parity-optimum",
    floor: [Ev::Witness, Ev::Replay, Ev::None, Ev::None],
};

/// `direct_cnf` — the layout-independent Boolean-clause route. Same evidence
/// shape as [`SAT_RELU_FALLBACK`]: a lifted point is re-checked, while a
/// refutation is a replay claim.
pub(crate) const DIRECT_CNF: LaneFloor = LaneFloor {
    lane: "direct-cnf",
    floor: [Ev::Witness, Ev::None, Ev::Replay, Ev::None],
};

/// Exact specialized-PB reduction whose exhaustive argument is not exported.
///
/// These routes rebuild the source model in exact arithmetic and re-check any
/// lifted point, so existence is witnessed. Their infeasibility and dual-bound
/// arguments remain replay records, however: an internal exhaustive run is not
/// a model-bound proof object. The shared row is intentionally conservative
/// enough for every claim this lane can make; typed refutations bypass it only
/// through an independently verified supplemental-proof policy gate.
pub(crate) const SPECIALIZED_PB_REPLAY: LaneFloor = LaneFloor {
    lane: "specialized-pb",
    floor: [Ev::Witness, Ev::Replay, Ev::Replay, Ev::None],
};

/// Replay-only Hoffman-master decision after the model-bound network proof
/// route declined. The master proof is not a source-model artifact.
pub(crate) const NETWORK_DESIGN_REPLAY: LaneFloor = LaneFloor {
    lane: "network-design-replay",
    floor: SPECIALIZED_PB_REPLAY.floor,
};

/// Open-domain projection decision without a typed residual certificate.
pub(crate) const OPEN_DOMAIN_REPLAY: LaneFloor = LaneFloor {
    lane: "open-domain-replay",
    floor: SPECIALIZED_PB_REPLAY.floor,
};

/// Hybrid PB/LP optimum without an exported dual-optimality artifact.
pub(crate) const HYBRID_REPLAY: LaneFloor = LaneFloor {
    lane: "hybrid-pb-lp-replay",
    floor: SPECIALIZED_PB_REPLAY.floor,
};

/// `pb_route::try_solve_production_portfolio` — the bounded exact PB portfolio,
/// on its OPTIMISATION answers.
///
/// It projects the MILP onto a bounded pseudo-Boolean instance, proves it
/// exactly, and lifts the point back — so the point is real and
/// `validate_witnesses` re-checks it (`PointExists = Witness`). Its OPTIMALITY,
/// though, is an exhaustion argument over the projection: honest, and filed as
/// `pb-portfolio-projection-optimal`, but not an exported object anyone can
/// check (`NoBetterThan = Replay`).
///
/// Measured consequence of NOT declaring this, at HEAD, on the DEFAULT path:
/// `min x + z  s.t.  x + z = 1, z binary, x free` came back
/// `evidence dual REPLAY pb-portfolio-projection-optimal` where the anchor
/// produces `evidence dual SUCCINCT optcert` from the singleton postsolve lift.
/// A second copy of the flagship defect, found by the gate rather than by
/// reading code.
///
/// Typed single-row and multi-row refutations bypass this floor through their
/// supplemental-proof gate. A rare bare exhaustion result does use this row
/// and therefore remains replay evidence.
pub(crate) const PB_PORTFOLIO: LaneFloor = LaneFloor {
    lane: "pb-portfolio",
    floor: [Ev::Witness, Ev::Replay, Ev::Replay, Ev::None],
};

/// THE REGISTRY. Every lane that declares a floor appears here, and the
/// conformance test below sweeps it — so a new row is checked the moment it is
/// added, which is the whole point of having a registry rather than a
/// convention. Test-only because its only job is to be swept: shipping code
/// names the precise lane floor it is gating at the call site.
#[cfg(test)]
pub(crate) const DECLARED: &[LaneFloor] = &[
    SAT_RELU_PROOF,
    SAT_RELU_FALLBACK,
    BLOCK_ANGULAR,
    PARITY_OPTIMUM_REPLAY,
    DIRECT_CNF,
    SPECIALIZED_PB_REPLAY,
    NETWORK_DESIGN_REPLAY,
    OPEN_DOMAIN_REPLAY,
    HYBRID_REPLAY,
    PB_PORTFOLIO,
];

// ---------------------------------------------------------------------------
// The anchor's bounded first refusal
// ---------------------------------------------------------------------------

/// How long the anchor gets to try for stronger evidence before a DEFERRED raw
/// conclusion becomes the input to caller-policy finalization instead.
///
/// # Why a bound at all, and why this one
///
/// A deferred claim has already decided the model. The only question left is
/// whether the anchor can do better on the EVIDENCE axis, and the only honest
/// answer is to let it try for a while. Two properties make that safe:
///
/// * **The raw solver conclusion is retained.** Whether or not the anchor
///   finishes, an agreeing conclusion survives — the anchor's if it decides,
///   the deferred lane's if it does not. The caller's certificate policy is
///   applied after that selection, so strict posture may turn a replay-only
///   conclusion into `CertificateUnavailable`; timing may change exported
///   evidence or that policy outcome, but never silently substitute a
///   contradictory conclusion. This is pinned by the floor/posture tests.
/// * **The loss is bounded and charged to the right place.** It is capped here,
///   not drawn from whatever the caller happened to allow.
///
/// The bound is MODEL-DERIVED, not deadline-derived, and that is deliberate.
/// Deriving it from the caller's remaining time reproduces a measured
/// pathology: the old PB trial window was `min(remaining/10, 500 ms)`, so
/// `markshare_5_0`'s routed wall time SCALED with the caller's patience —
/// asking ay for more time made it slower to the same answer, and at
/// `--time-limit 20` it made the seeder succeed, which is what deleted the
/// lattice proof. Speculation must cost O(model), never O(deadline).
///
/// # Calibration — swept, not guessed
///
/// Chosen by sweeping the knob over the whole 46-model ny W1 capture corpus,
/// serially, at `--time-limit 20`, and reading the dominance gate's own verdict
/// (`tests/portfolio_dominance_corpus.sh`):
///
/// ```text
///   cap      decided   verify exit 0   regressions vs the anchor   total wall
///     0 ms     46/46         5                    7                  19.2 s
///  1000 ms     46/46        11                    1                  44.5 s
///  3000 ms     46/46        12                    0                  92.7 s
/// ```
///
/// `0` is greedy routing exactly, and it is the arm that loses seven proofs.
/// 3000 ms is the smallest swept value at which the invariant HOLDS on every
/// model — routed evidence matches the anchor's twelve verifying certificates
/// while still deciding all 46, which the anchor alone does not (it decides 27).
///
/// The cost is stated rather than buried: 4.8x total wall on this corpus,
/// bought entirely on models the anchor cannot decide at all, where it spends
/// the ceiling and the deferred refutation is then finalized under the caller's
/// certificate policy. The raw conclusion is never silently discarded; strict
/// posture may honestly return `CertificateUnavailable` instead of publishing
/// replay-only authority. A consumer who wants the fast path back can set
/// `--anchor-first-refusal-ms 0`, which disables deferral outright.
/// `--tree-cert-leaves 0` separately disables tree-certificate construction,
/// but deliberately does not lower [`anchor_cap`] for infeasibility: the root
/// LP may still supply a succinct Farkas certificate.
///
/// A 2000 ms cap was tried and REJECTED, for a reason worth recording: on
/// `W1_sat_v91_c217_000008` the anchor returns `INFEASIBLE` with a succinct
/// Farkas row in 0.42 s at `--time-limit 1`, 3, 4, 5, 8 and 20 — and `UNKNOWN`
/// at `--time-limit 2`. Its own internal budgets are cut as fractions of the
/// remaining deadline, so shortening the deadline does not shorten the search,
/// it selects a different one. That non-monotonicity is a pre-existing defect
/// of the anchor, not of this cap, but it means any slice can land in a hole,
/// and it is the strongest argument for eventually denominating first refusal
/// in NODES rather than milliseconds.
pub(crate) const ANCHOR_FIRST_REFUSAL_CAP: std::time::Duration = std::time::Duration::from_secs(3);

/// The cap, after `--anchor-first-refusal-ms`.
///
/// `0` disables deferral outright, and that degenerate point is the whole
/// reason the override exists: it turns "the portfolio dominates its fallback"
/// from a claim about two programs into a property of ONE program with a
/// parameter, which a differential test can assert per model. Read it under
/// the active attempt profile: this is a per-`SolveOpts` setting, never a
/// process-global first-use choice.
pub(crate) fn anchor_first_refusal_cap() -> std::time::Duration {
    crate::tune::count_opt(crate::tune::Knob::AnchorFirstRefusalMs)
        .map_or(ANCHOR_FIRST_REFUSAL_CAP, |ms| {
            std::time::Duration::from_millis(ms as u64)
        })
}

/// Nonzero-work floor: below this the anchor cannot even get a root LP away, so
/// granting it a slice is pure latency. Nothing in the corpus is this small and
/// also deferred, but a caller with a 50 ms limit should not pay 2 s.
pub(crate) const ANCHOR_FIRST_REFUSAL_MIN: std::time::Duration =
    std::time::Duration::from_millis(25);

/// A verdict a lane produced that is NOT allowed to end the solve yet, because
/// [`may_close`] said its evidence is below what the anchor could still reach.
///
/// This is the "Tier C" position, and it is dominance BY CONSTRUCTION rather
/// than by prediction:
///
/// * if the anchor decides inside its slice, its conclusion is selected with
///   its artifacts and the deferred claim rides along in the replay ledger;
///   the union is the evidence least upper bound before caller-policy output;
/// * if the anchor does not decide, the deferred raw conclusion is finalized
///   under caller certificate policy. Before that policy filter, the comparison
///   is `verdict` against `Unknown` and `Replay` against `None`, which is
///   dominance on both axes with nothing predicted.
///
/// There is no third case. In particular the deferred raw conclusion and its
/// claims are never silently discarded before policy finalization, which is
/// what the greedy router did in reverse.
pub(crate) struct Deferred {
    /// The lane that produced it, for the trace and for the disagreement trap.
    pub(crate) lane: &'static str,
    /// The raw conclusion to finalize if the anchor cannot decide.
    pub(crate) outcome: crate::outcome::Outcome,
    /// Replay claims filed by the lane, held here rather than left in the
    /// thread-local ledger so they cannot cross-attribute to the anchor's
    /// verdict if the anchor wins. See [`LaneFrame`].
    pub(crate) replay_claims: Vec<crate::cert_io::ReplayClaim>,
    /// The exact bounded anchor opportunity selected when this conclusion was
    /// admitted. Storing it prevents later route work from resetting the cap.
    pub(crate) first_refusal: AnchorFirstRefusal,
}

/// The anchor's slice for a deferred claim, and the reason it is a slice.
pub(crate) struct AnchorFirstRefusal {
    /// Absolute instant the anchor's attempt at stronger evidence ends. Always
    /// `<= ` the caller's own deadline: first refusal never extends a budget.
    pub(crate) until: std::time::Instant,
}

impl AnchorFirstRefusal {
    /// Compute the slice. `None` means "do not defer": there is no bounded time
    /// worth granting. In particular, an unrepresentable relative cap with no
    /// caller deadline cannot become an unlimited anchor attempt.
    pub(crate) fn plan(
        now: std::time::Instant,
        caller_deadline: Option<std::time::Instant>,
    ) -> Option<Self> {
        Self::plan_with_cap(now, caller_deadline, anchor_first_refusal_cap())
    }

    pub(crate) fn plan_with_cap(
        now: std::time::Instant,
        caller_deadline: Option<std::time::Instant>,
        cap_duration: std::time::Duration,
    ) -> Option<Self> {
        if cap_duration.is_zero() {
            return None;
        }
        let cap = now.checked_add(cap_duration);
        let until = match (caller_deadline, cap) {
            (Some(deadline), _) if deadline <= now => return None,
            (Some(deadline), Some(cap)) => deadline.min(cap),
            (Some(deadline), None) => deadline,
            (None, Some(cap)) => cap,
            (None, None) => return None,
        };
        if until.saturating_duration_since(now) < ANCHOR_FIRST_REFUSAL_MIN {
            return None;
        }
        Some(Self { until })
    }
}

// ---------------------------------------------------------------------------
// LaneFrame — the cross-attribution guard
// ---------------------------------------------------------------------------

/// RAII guard around one lane's execution.
///
/// `cert_io::ledger` is a THREAD-LOCAL. A lane that files evidence and then
/// declines leaves that evidence sitting where the NEXT lane's verdict will
/// pick it up. `lattice.rs` already hand-stashes and restores the ledger for
/// exactly this reason, which is direct evidence that the channel is live
/// rather than theoretical — and a portfolio that runs more lanes per solve
/// makes cross-attribution strictly more likely, not less.
///
/// Entering drains the ledger and holds it. [`Self::take_lane_claims`] restores
/// the caller's claims and returns only what THIS lane filed; dropping —
/// including on unwind — discards the lane's claims and restores the caller's.
/// A lane's evidence therefore cannot attach to a verdict the lane did not
/// produce.
pub(crate) struct LaneFrame {
    outer: Vec<crate::cert_io::ReplayClaim>,
}

impl LaneFrame {
    /// Begin a lane. Any claims already pending belong to the caller and are
    /// set aside.
    pub(crate) fn enter() -> Self {
        Self {
            outer: crate::cert_io::ledger::take(),
        }
    }

    /// End the lane, returning ONLY the claims it filed. The caller's own
    /// pending claims are restored to the ledger.
    pub(crate) fn take_lane_claims(self) -> Vec<crate::cert_io::ReplayClaim> {
        // `Drop` would restore-and-discard, which is right for a DECLINE and
        // wrong here, so the guard is defused before the caller's claims are put
        // back. `ManuallyDrop` rather than `mem::forget` + clone: the outer
        // claims are moved, not copied.
        let mut this = std::mem::ManuallyDrop::new(self);
        let mine = crate::cert_io::ledger::take();
        for claim in std::mem::take(&mut this.outer) {
            crate::cert_io::ledger::record(claim);
        }
        mine
    }
}

impl Drop for LaneFrame {
    fn drop(&mut self) {
        // Unwind or an early `?`: the lane's claims are DISCARDED (it did not
        // return a verdict, so nothing may carry them) and the caller's are
        // restored. Discarding here is the sound direction: a dropped replay
        // claim costs evidence, an attributed one is a lie.
        let _lane_claims = crate::cert_io::ledger::take();
        for claim in std::mem::take(&mut self.outer) {
            crate::cert_io::ledger::record(claim);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Col;

    fn integral_model() -> Model {
        let mut m = Model::new();
        let x = m.add_binary_col();
        let y = m.add_binary_col();
        m.add_row(0.0, 1.0, &[(x, 1.0), (y, 1.0)]);
        m
    }

    fn continuous_model() -> Model {
        let mut m = Model::new();
        let x = m.add_col(0.0, 1.0);
        m.add_row(0.0, 1.0, &[(x, 1.0)]);
        m
    }

    #[test]
    fn evidence_is_totally_ordered_weakest_first() {
        assert!(Ev::None < Ev::Replay);
        assert!(Ev::Replay < Ev::Witness);
        assert!(Ev::Witness < Ev::Succinct);
    }

    /// THE CELL THE `W1_unsat_v9_c14_000008` DEFECT LIVES IN.
    ///
    /// The legacy fallback CDCL refutation is REPLAY; the anchor can reach a
    /// SUCCINCT tree certificate whenever a leaf budget is armed. The bounded
    /// proof route, by contrast, now carries its own SUCCINCT RUP artifact.
    #[test]
    fn a_replay_refutation_may_not_preempt_a_reachable_tree_certificate() {
        let m = integral_model();
        let opts = SolveOpts::new();
        assert!(opts.tree_cert_leaves > 0, "default arms the leaf budget");
        assert_eq!(anchor_cap(&m, &opts, ClaimKind::Infeasible), Ev::Succinct);
        assert!(
            may_close(&SAT_RELU_PROOF, ClaimKind::Infeasible, &m, &opts),
            "the independently replayed model-bound RUP proof must tie the anchor"
        );
        assert!(
            !may_close(&SAT_RELU_FALLBACK, ClaimKind::Infeasible, &m, &opts),
            "a fallback REPLAY refutation must NOT end the solve while the \
             anchor can still reach a succinct tree certificate"
        );
        assert!(
            !may_close(&DIRECT_CNF, ClaimKind::Infeasible, &m, &opts),
            "direct-cnf's refutation is a replay claim too"
        );
    }

    /// THE OTHER HALF, AND WHY THE FLOOR MUST BE PER CLAIM.
    ///
    /// The SAME lane is admitted on the point side. If evidence were declared
    /// per `Outcome` this test and the one above could not both pass, and the
    /// 46/46 ReLU class would have to be sacrificed to fix the refutation.
    #[test]
    fn the_same_lane_is_admitted_on_the_claim_where_it_ties_the_anchor() {
        let m = integral_model();
        let opts = SolveOpts::new();
        assert_eq!(anchor_cap(&m, &opts, ClaimKind::PointExists), Ev::Witness);
        assert!(
            may_close(&SAT_RELU_PROOF, ClaimKind::PointExists, &m, &opts),
            "a lifted point is re-checked by validate_witnesses exactly as the \
             anchor's own point is; barring it would cost the ReLU class for nothing"
        );
    }

    /// Switching the leaf budget off does not remove the independent root
    /// Farkas enrichment path, so the conservative reach ceiling stays typed.
    #[test]
    fn disarming_the_leaf_budget_keeps_root_farkas_in_the_reach_ceiling() {
        let m = integral_model();
        let opts = SolveOpts::new().with_tree_cert_leaves(0);
        assert_eq!(anchor_cap(&m, &opts, ClaimKind::Infeasible), Ev::Succinct);
        assert!(
            !may_close(&SAT_RELU_FALLBACK, ClaimKind::Infeasible, &m, &opts),
            "a replay refutation must not preempt a reachable root Farkas artifact"
        );
    }

    /// The `NoBetterThan` cell follows objective presence: without an objective
    /// the claim is vacuous, while an objective-bearing integral model can
    /// export a non-crossing `OptimalityCertificate`. Pin both sides on the
    /// same integral shape.
    #[test]
    fn dual_cap_splits_on_objective_presence() {
        let opts = SolveOpts::new();
        // No objective: the dual claim is vacuous and the emitter writes
        // `evidence dual NONE`. Lanes close immediately — this is what keeps
        // the ny ReLU class fast.
        assert_eq!(
            anchor_cap(&integral_model(), &opts, ClaimKind::NoBetterThan),
            Ev::None,
        );
        // An objective: the anchor can export a checkable
        // `OptimalityCertificate`, so a lane whose optimality is an exhaustion
        // argument must stand behind it.
        let mut objective_bearing = integral_model();
        objective_bearing.set_objective(&[(Col(0), 1.0)], crate::model::Sense::Minimize);
        assert!(objective_bearing.has_objective());
        assert_eq!(
            anchor_cap(&objective_bearing, &opts, ClaimKind::NoBetterThan),
            Ev::Succinct,
        );
        let mut explicit_zero = integral_model();
        explicit_zero.set_objective(&[], crate::model::Sense::Minimize);
        assert!(explicit_zero.has_objective());
        assert_eq!(
            anchor_cap(&explicit_zero, &opts, ClaimKind::NoBetterThan),
            Ev::Succinct,
        );
        assert!(
            !may_close(
                &PB_PORTFOLIO,
                ClaimKind::NoBetterThan,
                &objective_bearing,
                &opts
            ),
            "the PB portfolio's exhaustion-based optimality must NOT preempt an \
             optimality certificate the anchor can lift"
        );
        assert!(
            may_close(
                &PB_PORTFOLIO,
                ClaimKind::NoBetterThan,
                &integral_model(),
                &opts
            ),
            "with no objective there is nothing to preempt"
        );
    }

    /// An optimum is TWO claims. A lane must clear the floor on both halves,
    /// and a `Feasible` that carries an interrupted dual bound asserts the dual
    /// half too.
    #[test]
    fn an_optimum_is_a_point_and_a_bound_and_both_are_gated() {
        use crate::outcome::Outcome;
        use num_traits::Zero as _;
        let optimal = Outcome::Optimal {
            value: num_rational::BigRational::zero(),
            model_values: Vec::new(),
            cert: None,
        };
        assert_eq!(
            claims_of(&optimal),
            &[ClaimKind::PointExists, ClaimKind::NoBetterThan]
        );
        let bare_point = Outcome::Feasible {
            model_values: Vec::new(),
            incumbent_only: false,
            dual_bound: None,
        };
        assert_eq!(claims_of(&bare_point), &[ClaimKind::PointExists]);
        let bounded_point = Outcome::Feasible {
            model_values: Vec::new(),
            incumbent_only: false,
            dual_bound: Some(num_rational::BigRational::zero()),
        };
        assert_eq!(
            claims_of(&bounded_point),
            &[ClaimKind::PointExists, ClaimKind::NoBetterThan]
        );
        assert!(claims_of(&Outcome::Unknown {
            reason: crate::outcome::UnknownReason::Timeout
        })
        .is_empty());

        // The whole-verdict gate agrees with the per-claim gate.
        let m = integral_model();
        let opts = SolveOpts::new();
        assert!(may_close_outcome(&SAT_RELU_PROOF, &optimal, &m, &opts));
        assert!(may_close_outcome(
            &SAT_RELU_PROOF,
            &Outcome::Infeasible {
                cert: None,
                tree_cert: None
            },
            &m,
            &opts
        ));
        assert!(!may_close_outcome(
            &SAT_RELU_FALLBACK,
            &Outcome::Infeasible {
                cert: None,
                tree_cert: None
            },
            &m,
            &opts
        ));
    }

    #[test]
    fn block_angular_optimum_meets_both_anchor_floors() {
        use crate::outcome::Outcome;
        use num_traits::Zero as _;

        let mut model = Model::new();
        let x = model.add_binary_col();
        model.add_row(0.0, 1.0, &[(x, 1.0)]);
        model.set_objective(&[(x, 1.0)], crate::Sense::Minimize);
        let outcome = Outcome::Optimal {
            value: num_rational::BigRational::zero(),
            model_values: vec![num_rational::BigRational::zero()],
            cert: None,
        };

        assert_eq!(
            anchor_cap(&model, &SolveOpts::new(), ClaimKind::PointExists),
            Ev::Witness
        );
        assert_eq!(
            anchor_cap(&model, &SolveOpts::new(), ClaimKind::NoBetterThan),
            Ev::Succinct
        );
        assert!(may_close_outcome(
            &BLOCK_ANGULAR,
            &outcome,
            &model,
            &SolveOpts::new()
        ));
    }

    /// Every declared lane must be honest about at least one claim, and no lane
    /// may declare a floor it cannot reach. A lane declaring `Succinct`
    /// everywhere would silently bypass every deferral, so the conformance test
    /// requires a lane to name the claims it does NOT back.
    #[test]
    fn every_declared_lane_names_a_claim_it_cannot_back() {
        for lane in DECLARED {
            assert!(
                ClaimKind::ALL.iter().any(|&c| lane.get(c) < Ev::Succinct),
                "lane `{}` declares SUCCINCT evidence for every claim; that is \
                 almost certainly a mis-declaration, and a mis-declaration here \
                 disables the dominance gate silently",
                lane.lane,
            );
        }
    }

    include!("claim/authority_tests.rs");

    /// `Col`/`ColKind` reachability check for `model_has_integrality`, which the
    /// dual cap depends on. Cheap, but the cap is load-bearing.
    #[test]
    fn integrality_detection_matches_column_kinds() {
        assert!(model_has_integrality(&integral_model()));
        assert!(!model_has_integrality(&continuous_model()));
        let mut mixed = continuous_model();
        mixed.add_int_col(0.0, 1.0);
        assert!(model_has_integrality(&mixed));
    }
}
