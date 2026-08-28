// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-tree MILP OPTIMALITY certificates — the dual half an `Optimal`
//! verdict never had.
//!
//! An `Outcome::Optimal` is TWO claims, and only one of them was ever
//! exportable. The primal half (`this point is feasible and attains z*`) has
//! shipped as a checkable witness since `.ayc` existed. The dual half
//! (`nothing feasible beats z*`) had no exported object at all on a branched
//! MILP: [`crate::cert::OptimalityCertificate`] is a ROOT bound and completes
//! optimality only when the root relaxation already meets the incumbent, so
//! every instance that needed a single branch shipped `evidence dual NONE` —
//! optimality on TRUST.
//!
//! [`MilpOptimalityCertificate`] is the missing object: the branch skeleton
//! plus, at every leaf, exact evidence that the leaf cannot contain anything
//! better than `value`. Two leaf kinds, and they are the two ways a
//! branch-and-bound node dies:
//!
//! - [`OptTreeNode::Empty`] — a [`FarkasCertificate`] priced at the leaf's
//!   effective bounds: no point at all satisfies the model under this branch.
//! - [`OptTreeNode::Dominated`] — positive multipliers whose oriented
//!   combination is exactly the model's own objective, priced at the leaf's
//!   effective bounds, establishing `objective >= value` over the whole leaf.
//!   Ties close: the claim is on the optimal VALUE, not on a unique optimiser,
//!   so a leaf whose bound is exactly `value` contains nothing BETTER and is
//!   finished.
//!
//! ## Why the two halves together are optimality
//!
//! Coverage is by construction, exactly as in
//! [`crate::tree_cert::MilpInfeasibilityCertificate`]: a split records only
//! `(col, cut)` with `col` integral in the model and `cut ∈ ℤ`, so every
//! model-feasible point has `x_col <= cut` or `x_col >= cut + 1` and the two
//! branches tile the parent with no reliance on any recorded box. Induction
//! from the leaves gives `objective >= value` over the model's ENTIRE feasible
//! set. The witness then exhibits a feasible point attaining `value`. Together:
//! `value` is the optimum.
//!
//! ## What the verifier refuses to be told
//!
//! The design review that preceded this
//! (the development design notes) found the same
//! failure mode five times over, and it is the only one that matters:
//!
//! > The certificate must DERIVE every fact from the model, never READ it from
//! > the emitter.
//!
//! So [`MilpOptimalityCertificate`] records **no box**, **no per-leaf bound**,
//! and **no objective**:
//!
//! - **The box is reconstructed**, never recorded. A recorded box is a
//!   confirmed-exploitable forgery — the review's counterexample (`x ∈ [0,10]`
//!   integer, `y` continuous, `y − x <= 0`, minimise `−y`) closes a single leaf
//!   at a recorded `x ∈ [0,0]` proving `obj >= 0` while the true optimum is
//!   `−10`. [`Self::verify`] walks from `model.col_bounds` and intersects the
//!   path's splits itself, so a leaf is always priced at the bounds its
//!   position in the tree actually implies. Pinned by
//!   `a_leaf_cannot_smuggle_in_a_tighter_box`.
//! - **The target is ONE field**, `value`, shared by the primal check and every
//!   leaf. There is no per-leaf bound to disagree with it, so the "small number
//!   in the block, large number on the verdict line" forgery has nowhere to
//!   live. `.ayc` carries the same discipline: `check_dual` prices the tree at
//!   the value the VERDICT line claims.
//! - **The objective comes from the model.** [`OptimalityCertificate::verify_bound_leaf`]
//!   builds its target from `model.cols`/`model.exact_obj`, never from the
//!   certificate, so a leaf claiming an empty objective cannot verify against a
//!   model that has one.
//!
//! ## Relation to VIPR
//!
//! This is the VIPR (Cheung–Gleixner–Steffy, *Verifying integer programming
//! results*) shape, specialised. VIPR's `sol`/`der`/`asm` sections encode the
//! same three obligations — an incumbent, a per-leaf derivation, and an
//! exhaustive assumption split — and its `rtp range` is exactly this `value`.
//! Three deliberate divergences, all narrowing:
//!
//! 1. **Splits only, no general assumptions.** VIPR's `asm` lets a derivation
//!    assume an arbitrary inequality, which puts the burden of proving the
//!    assumptions exhaustive on a separate `uns` accounting. Restricting to
//!    `x_col <= cut | x_col >= cut+1` on an integral column makes exhaustiveness
//!    a structural property the verifier cannot fail to check.
//! 2. **No derivation DAG / no cut lane.** VIPR derives each bound through a
//!    chain of previously-derived inequalities, which is what lets it certify
//!    cutting planes. A leaf here is one flat multiplier list over the MODEL's
//!    own rows and bounds. That is why this certificate can be produced without
//!    the search's cuts being derivable — and why it cannot inherit their
//!    strength (see [`derive_optimality_tree`]).
//! 3. **In-memory typed object first, text second.** The wire form is `.ayc`,
//!    not `.vipr`; a VIPR exporter would be a translation of this object, not a
//!    change to it.

use std::time::Instant;

use ay_lra::rational::Rational;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

use crate::cert::{
    BoundSide, CertificateError, FactRef, FarkasCertificate, Multiplier, OptimalityCertificate,
};
use crate::exact::{Budget, ExactLp, LpOptimum};
use crate::model::{exact, Col, ColKind, Model, Row, Sense};
use crate::outcome::UnknownReason;
use crate::simplex::{FloatLp, NbBound, SimplexStatus};
use crate::tree_cert::exact_farkas_from_float_ray_grid;

/// A rational as an EXACTLY-representable `f64`, within the range where
/// `f + 1.0` is also exact. `None` otherwise (fail closed). Mirrors
/// [`crate::tree_cert`]'s guard: a cut that does not round-trip would put the
/// deriver's working box and the verifier's reconstructed box in different
/// places.
const MAX_EXACT_INT: f64 = 4_503_599_627_370_496.0; // 2^52

/// One node of an optimality split tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptTreeNode {
    /// A case split on an integral column: `lo` covers `x_col <= cut`, `hi`
    /// covers `x_col >= cut + 1`. `cut` must be an integer — the two branches
    /// then cover the parent's integer domain by construction.
    Split {
        /// The integral column being split.
        col: Col,
        /// The integer split point.
        cut: BigRational,
        /// The `x_col <= cut` branch.
        lo: Box<OptTreeNode>,
        /// The `x_col >= cut + 1` branch.
        hi: Box<OptTreeNode>,
    },
    /// A leaf closed by EMPTINESS: the model under this branch's accumulated
    /// bound tightenings admits no point at all.
    Empty {
        /// The Farkas witness, priced at the leaf's effective column bounds.
        farkas: FarkasCertificate,
    },
    /// A leaf closed by DOMINATION: positive multipliers whose oriented
    /// combination is exactly the model's objective, establishing that the
    /// objective is at least (Minimize) / at most (Maximize) the certificate's
    /// `value` everywhere in this leaf.
    ///
    /// The bound itself is NOT recorded — it is recomputed from the
    /// multipliers and compared against the certificate's single `value`.
    Dominated {
        /// The positive multipliers, priced at the leaf's effective column
        /// bounds.
        multipliers: Vec<Multiplier>,
    },
}

/// An exact, independently checkable witness that `value` is the MODEL's
/// optimum: a primal point attaining it, plus a split tree proving nothing
/// feasible does better.
///
/// Verification consults only `model` and this value — the same "evidence is
/// data" contract as [`FarkasCertificate`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MilpOptimalityCertificate {
    /// The claimed optimum, in the model's frame INCLUDING the objective
    /// offset — the same frame as `Outcome::Optimal::value` and
    /// [`Model::objective_value_at`]. One field, shared by both halves.
    pub value: BigRational,
    /// A feasible point attaining `value`; one entry per model column.
    pub witness: Vec<BigRational>,
    /// The root of the split tree.
    pub root: OptTreeNode,
}

impl MilpOptimalityCertificate {
    /// Independently verify this certificate against `model` using exact
    /// arithmetic. No solver state is consulted.
    ///
    /// `Ok` means: `value` is the optimal objective value of `model`.
    pub fn verify(&self, model: &Model) -> Result<(), CertificateError> {
        self.verify_primal(model)?;
        self.verify_dual(model)
    }

    /// The primal half: the witness is a feasible point of `model` and attains
    /// `value`.
    ///
    /// Without this, the tree alone proves only `objective >= value`, i.e. that
    /// `value` is a valid BOUND — a claim any sufficiently small number
    /// satisfies. Attainment is what turns the bound into an optimum.
    fn verify_primal(&self, model: &Model) -> Result<(), CertificateError> {
        if self.witness.len() != model.num_cols() {
            return Err(CertificateError::WitnessRejected {
                msg: format!(
                    "witness has {} entries, the model has {} columns",
                    self.witness.len(),
                    model.num_cols()
                ),
            });
        }
        if let Err(violation) = model.check_point(&self.witness) {
            return Err(CertificateError::WitnessRejected {
                msg: format!("witness is not a feasible point of the model: {violation:?}"),
            });
        }
        let attained = model.objective_value_at(&self.witness);
        if attained != self.value {
            return Err(CertificateError::WitnessRejected {
                msg: format!(
                    "witness attains {attained}, the certificate claims {}",
                    self.value
                ),
            });
        }
        Ok(())
    }

    /// The dual half: every leaf of the split tree is empty or bounded by
    /// `value`, over a box the VERIFIER reconstructs.
    ///
    /// Structurally identical to
    /// [`crate::tree_cert::MilpInfeasibilityCertificate::verify`] — same
    /// explicit work stack (a certificate is input data; recursion depth must
    /// not be its caller's stack limit), same tighten/restore discipline, same
    /// integral-column/integer-cut coverage licence — with the one added leaf
    /// kind.
    fn verify_dual(&self, model: &Model) -> Result<(), CertificateError> {
        verify_optimality_tree_bound(model, &self.value, &self.root)
    }
}

/// Verify that `root` establishes `objective >= value` (Minimize) / `<= value`
/// (Maximize) over the WHOLE of `model`'s feasible set, in exact arithmetic.
///
/// # This is HALF of optimality, and the half that is easy to over-read
///
/// `Ok(())` means `value` is a valid BOUND — a claim that any sufficiently
/// pessimistic number satisfies. It becomes OPTIMALITY only when paired with a
/// feasible point ATTAINING `value`. [`MilpOptimalityCertificate::verify`] is
/// that pairing and is what callers should normally use; this is exposed
/// separately because `.ayc` splits an `Optimal` into two independently
/// reported claims (`primal` and `dual`) and the dual checker needs exactly
/// this half — priced at the value the VERDICT line claims, which is the same
/// value the primal checker pins the witness to.
pub fn verify_optimality_tree_bound(
    model: &Model,
    value: &BigRational,
    root: &OptTreeNode,
) -> Result<(), CertificateError> {
    let n = model.num_cols();
    // Effective column bounds, exact; `None` = that side is infinite.
    let mut lb: Vec<Option<BigRational>> = (0..n)
        .map(|j| exact(model.col_bounds(Col(j as u32)).0))
        .collect();
    let mut ub: Vec<Option<BigRational>> = (0..n)
        .map(|j| exact(model.col_bounds(Col(j as u32)).1))
        .collect();

    enum Step<'a> {
        Visit(&'a OptTreeNode),
        Tighten {
            col: usize,
            upper: bool,
            to: BigRational,
            child: &'a OptTreeNode,
        },
        Restore {
            col: usize,
            upper: bool,
            /// The bound to put back. Carried BY the frame rather than parked
            /// on a side stack, so restoring cannot depend on that stack being
            /// balanced -- a certificate is untrusted input and a verifier must
            /// not have a panic path at all, let alone one an unbalanced walk
            /// could reach.
            prev: Option<BigRational>,
        },
    }
    let mut stack: Vec<Step<'_>> = vec![Step::Visit(root)];
    let mut splits = 0usize;
    let mut leaves = 0usize;
    while let Some(step) = stack.pop() {
        match step {
            Step::Visit(OptTreeNode::Empty { farkas }) => {
                let index = leaves;
                leaves += 1;
                farkas
                    .verify_with_col_bounds(model, &lb, &ub)
                    .map_err(|error| CertificateError::LeafRejected {
                        index,
                        error: Box::new(error),
                    })?;
            }
            Step::Visit(OptTreeNode::Dominated { multipliers }) => {
                let index = leaves;
                leaves += 1;
                // THE TARGET IS THE CERTIFICATE'S SINGLE `value`, and the
                // OBJECTIVE comes from `model` inside `verify_bound_leaf`.
                // Nothing about this check is readable from the leaf.
                OptimalityCertificate::verify_bound_leaf(multipliers, model, &lb, &ub, value)
                    .map_err(|error| CertificateError::LeafRejected {
                        index,
                        error: Box::new(error),
                    })?;
            }
            Step::Visit(OptTreeNode::Split { col, cut, lo, hi }) => {
                let index = splits;
                splits += 1;
                let c = col.index();
                // Coverage licence: only an INTEGRAL column split at an
                // INTEGER leaves no point between the branches. A future
                // non-integral kind must not silently pass, so the kinds
                // are whitelisted, not blacklisted.
                let integral =
                    c < n && matches!(model.col_kind(*col), ColKind::Binary | ColKind::Integer);
                if !integral || !cut.is_integer() {
                    return Err(CertificateError::InvalidSplit { index, col: c });
                }
                // LIFO: the lo branch's frames go on top. Each `Tighten`
                // pushes its own `Restore` once it knows what it displaced.
                stack.push(Step::Tighten {
                    col: c,
                    upper: false,
                    to: cut.clone() + BigRational::one(),
                    child: hi,
                });
                stack.push(Step::Tighten {
                    col: c,
                    upper: true,
                    to: cut.clone(),
                    child: lo,
                });
            }
            Step::Tighten {
                col,
                upper,
                to,
                child,
            } => {
                let slot = if upper { &mut ub[col] } else { &mut lb[col] };
                let prev = slot.clone();
                // Branch bounds only ever TIGHTEN the effective box.
                *slot = Some(match slot.take() {
                    Some(prev) => {
                        if upper {
                            prev.min(to)
                        } else {
                            prev.max(to)
                        }
                    }
                    None => to,
                });
                // Restore first (LIFO: it runs LAST), carrying what it must
                // put back.
                stack.push(Step::Restore { col, upper, prev });
                stack.push(Step::Visit(child));
            }
            Step::Restore { col, upper, prev } => {
                if upper {
                    ub[col] = prev;
                } else {
                    lb[col] = prev;
                }
            }
        }
    }
    Ok(())
}

impl MilpOptimalityCertificate {
    /// The number of leaves in the tree (diagnostics; verification cost is
    /// linear in this).
    #[must_use]
    pub fn num_leaves(&self) -> usize {
        let mut stack = vec![&self.root];
        let mut leaves = 0usize;
        while let Some(node) = stack.pop() {
            match node {
                OptTreeNode::Empty { .. } | OptTreeNode::Dominated { .. } => leaves += 1,
                OptTreeNode::Split { lo, hi, .. } => {
                    stack.push(lo);
                    stack.push(hi);
                }
            }
        }
        leaves
    }

    /// How many leaves close by domination rather than emptiness
    /// (diagnostics).
    #[must_use]
    pub fn num_dominated_leaves(&self) -> usize {
        let mut stack = vec![&self.root];
        let mut n = 0usize;
        while let Some(node) = stack.pop() {
            match node {
                OptTreeNode::Dominated { .. } => n += 1,
                OptTreeNode::Empty { .. } => {}
                OptTreeNode::Split { lo, hi, .. } => {
                    stack.push(lo);
                    stack.push(hi);
                }
            }
        }
        n
    }
}

// ---------------------------------------------------------------------------
// Derivation: an INDEPENDENT certifying descent, not a capture of the search.
// ---------------------------------------------------------------------------

/// Resource bounds for [`derive_optimality_tree`]. Exceeding any of them yields
/// `None` — the verdict is never affected, only its evidence.
///
/// # The primary bound is WORK, not the clock
///
/// A budget denominated in seconds makes the emitted EVIDENCE a function of
/// machine load: same binary, same input, same verdict, different certificate.
/// Measured on `08af5e9a7` with the 5 s default, `f2gap40400` at load ~70 on a
/// 14-core box certified 509 leaves / 10,068,501 bytes / `verify` exit 0 on 4
/// of 4 interleaved reps, and with 14 extra spinners running declined on 4 of
/// 4 — at 350, 311, 304 and 320 leaves, a different partial tree every time.
/// For a proof-carrying solver that is the defect that matters most, and it is
/// what [`Self::work_cap`] exists to remove.
///
/// [`Self::deadline`] survives as a SAFETY NET only. It must be set wide enough
/// that it never binds in normal operation; when it does bind the descent says
/// so under its own name ([`OptTreeDecline::Deadline`], distinct from
/// [`OptTreeDecline::WorkCap`]), so the one remaining load-dependent path is
/// loud rather than silent.
#[derive(Debug, Clone)]
pub struct OptimalityTreeBudget {
    /// Maximum leaves in the produced tree.
    pub leaf_cap: usize,
    /// THE PRIMARY BOUND: maximum [`OptTreeReport::work`] the descent may
    /// spend. Deterministic — a function of the model and the target value
    /// alone — so the same binary on the same input emits the same certificate
    /// on an idle machine and on a saturated one.
    ///
    /// `u64::MAX` means unbounded, which is what [`Self::new`] leaves it at:
    /// an in-process caller that wants only a leaf bound keeps exactly the
    /// behaviour it had.
    pub work_cap: u64,
    /// Absolute wall-clock SAFETY NET for the whole derivation. Not the primary
    /// bound — see the type's own note.
    pub deadline: Option<Instant>,
    /// Which fractional column a node splits on. PURE ADVICE — every leaf is
    /// exact-verified against the caller's model whatever this picks, so the
    /// rule can only change how MANY leaves the descent needs, never whether
    /// one of them is valid.
    pub branch: OptTreeBranch,
    /// Snap every float dual — the bound leaves' row duals AND the empty
    /// leaves' phase-I rays — to a multiple of `2^-dual_grid_bits` BEFORE
    /// exactifying it. `None` keeps the lossless `f64 -> BigRational`
    /// conversion, which is what this feature shipped with.
    ///
    /// PURE ADVICE, exactly like [`Self::branch`]: weak duality holds for ANY
    /// dual vector, so a coarser `y` is still dual-feasible and still yields a
    /// VALID bound — merely a possibly weaker one — and every proposal is
    /// re-verified against the caller's model at the leaf's reconstructed box
    /// before it is adopted. A grid too coarse to close a leaf therefore costs
    /// LEAVES (the descent splits instead) or the certificate, never validity.
    ///
    /// What it buys is BYTES. A lossless `f64` dual is a dyadic rational with a
    /// denominator up to `2^1074`; the residual `d_j = c_j - sum_r y_r a_rj`
    /// inherits it, and a `boundleaf` writes one such rational per column with
    /// a nonzero residual. Snapping `y` to `p / 2^k` caps every denominator the
    /// leaf can print at `2^k` times the model's own coefficient denominators.
    /// This is the same device [`crate::bab`]'s `exact_bound` already uses at
    /// `GRID = 1 << 30`, for the same reason.
    pub dual_grid_bits: Option<u32>,
}

/// How a certifying descent picks its split column.
///
/// Nothing here is evidence. A split records `(col, cut)` with `col` integral
/// and `cut ∈ ℤ`, and the verifier re-derives coverage from that pair alone, so
/// a rule that chooses badly costs LEAVES and can never cost validity. That is
/// exactly why it is worth tuning: it is the one dial on this feature that
/// trades nothing away.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OptTreeBranch {
    /// The lowest-indexed fractional integral column. The historical rule.
    #[default]
    FirstFractional,
    /// The fractional integral column whose relaxation value sits nearest a
    /// half-integer — the classic most-infeasible rule.
    MostFractional,
}

impl OptimalityTreeBudget {
    /// A budget of `leaf_cap` leaves, unbounded work and no deadline.
    #[must_use]
    pub fn new(leaf_cap: usize) -> Self {
        Self {
            leaf_cap,
            work_cap: u64::MAX,
            deadline: None,
            branch: OptTreeBranch::default(),
            dual_grid_bits: DEFAULT_DUAL_GRID_BITS,
        }
    }

    /// This budget with a deterministic work cap — the bound a caller that
    /// cares about reproducible evidence should set.
    #[must_use]
    pub fn with_work(mut self, work_cap: u64) -> Self {
        self.work_cap = work_cap;
        self
    }

    /// This budget with an absolute wall-clock SAFETY NET. Never the primary
    /// bound; see [`OptimalityTreeBudget`].
    #[must_use]
    pub fn with_deadline(mut self, deadline: Option<Instant>) -> Self {
        self.deadline = deadline;
        self
    }

    /// This budget with an explicit split rule.
    #[must_use]
    pub fn with_branch(mut self, branch: OptTreeBranch) -> Self {
        self.branch = branch;
        self
    }

    /// This budget with an explicit dual grid. `None` restores the lossless
    /// `f64 -> BigRational` conversion. See [`Self::dual_grid_bits`].
    #[must_use]
    pub fn with_dual_grid_bits(mut self, bits: Option<u32>) -> Self {
        self.dual_grid_bits = bits;
        self
    }

    fn expired(&self) -> bool {
        self.deadline.is_some_and(|d| Instant::now() >= d)
    }
}

/// The DETERMINISTIC work currency the certifying descent is budgeted in.
///
/// One unit is one EXACT-ARITHMETIC PASS over the model — the thing the descent
/// actually spends. Four events cost one, and the weights are the ratio of
/// their costs, not fitted parameters:
///
/// * **A node.** Entering a node builds the exact effective box
///   ([`exact_box`], `2·cols` rationals) and runs
///   [`OptimalityCertificate::verify_bound_leaf`] over the model's nonzeros.
///   One pass; the unit is defined by it.
/// * **An exact-rim iteration.** A Bland pass over every column plus a
///   substitution over every row — the same order as a node's verification, and
///   measurably dearer per unit, so it is charged [`OPT_TREE_RIM_ITER_COST`].
/// * **An exact-rim construction.** [`ExactLp::new_within`] is a full
///   rational pass over the matrix with gcd reduction, dearer again:
///   [`OPT_TREE_RIM_BUILD_COST`].
/// * **Float simplex iterations.** `f64` work, orders of magnitude cheaper per
///   iteration, and charged as such — [`OPT_TREE_FLOAT_ITERS_PER_UNIT`] of them make one
///   unit. Not free, because a float lane that grinds must not be able to spend
///   an unbounded amount of a work budget denominated in anything else.
///
/// The total is a PURE FUNCTION of the four counters, all of which
/// [`OptTreeReport`] publishes, so any consumer can re-derive it and check the
/// arithmetic rather than trust it.
///
/// # Why not one of the simpler counters — MEASURED, not argued
///
/// Every candidate was priced the same way on the 30-instance
/// `~/ay-bench/milp-gate` corpus plus `f2gap40400` and `supportcase16`: set its
/// cap to the smallest value that preserves all eight certificates the old 5 s
/// budget produced, then ask what wall each of the 27 usable derivations pays.
///
/// ```text
///   currency                  median   worst
///   leaves                    58.7 s   950.7 s   the existing knob
///   this counter, unweighted  23.8 s  89,825 s
///   nodes x nnz               15.7 s   231.5 s
///   this counter x nnz        10.1 s   102.5 s   <- shipped
/// ```
///
/// * **Leaves alone cannot bound this**, and that is not a matter of
///   re-scaling. It is the WORST currency measured, and separately it is why the
///   shipped `--opt-tree-leaves 20000` was dead code: across 164 derivations
///   over 41 OPTIMAL instances at the 5 s default, 136 declined on the DEADLINE
///   and ZERO on the leaf cap. A descent can spend its whole budget inside one
///   subtree and commit no leaves at all while doing it — `air03` reaches 2
///   nodes and 0 leaves in 5 s, and `qnet1` 473 nodes and 0 leaves.
/// * **Nodes alone** ignores the exact rim, which is the expensive lane. On
///   `dcmulti` the descent runs 75,259 rim iterations against 1,038 nodes; a
///   node-only counter would price that descent at 1.4% of what it costs.
/// * **Simplex iterations alone** (either lane) miss the per-node exact
///   verification, which is what a float-first descent actually spends its time
///   on — every one of the two largest certificates in the corpus (`f2gap40400`
///   509 leaves, `p0033` 991) is derived with ZERO rim LPs.
///
/// # THE HONEST LIMIT: no counter this cheap tracks the exact rim's wall cost
///
/// One exact-rim iteration cost **132 ms on `air03`** (91,028 nnz) against
/// **0.066 ms on `dcmulti`** (1,315 nnz) — a factor of 2,000 that the 69x nnz
/// ratio does not explain, because the exact tableau's rational bit-width grows
/// with the solve. So no constant [`OPT_TREE_RIM_ITER_COST`] can make a work cap
/// correspond to a fixed wall time, and none is claimed to. That is precisely
/// why a wall SAFETY NET still exists — and why it is a net and not the budget.
#[must_use]
fn work_units(nodes: u64, float_iters: u64, rim_iters: u64, rim_builds: u64) -> u64 {
    nodes
        .saturating_add(rim_iters.saturating_mul(OPT_TREE_RIM_ITER_COST))
        .saturating_add(rim_builds.saturating_mul(OPT_TREE_RIM_BUILD_COST))
        .saturating_add(float_iters / OPT_TREE_FLOAT_ITERS_PER_UNIT)
}

/// Cost of one exact-rim simplex iteration, in [`OptTreeReport::work`] units.
///
/// PUBLIC because the total is only auditable if the weights are: a consumer
/// holding an [`OptTreeReport`] can recompute `work` from `nodes`,
/// `float_iters`, `rim_iters` and `rim_solves` and check the arithmetic rather
/// than trust it.
pub const OPT_TREE_RIM_ITER_COST: u64 = 2;
/// Cost of one exact-rim CONSTRUCTION, in [`OptTreeReport::work`] units.
pub const OPT_TREE_RIM_BUILD_COST: u64 = 4;
/// Float simplex iterations per [`OptTreeReport::work`] unit.
pub const OPT_TREE_FLOAT_ITERS_PER_UNIT: u64 = 256;

/// Iterations ONE float-lane solve inside the certifying descent may run.
///
/// This bounds a single node's overshoot of the work cap (at most
/// `OPT_TREE_FLOAT_ITERS_PER_SOLVE / OPT_TREE_FLOAT_ITERS_PER_UNIT` = 256 units)
/// without making the float lane's behaviour depend on how much budget is left
/// — see the call site for why that distinction is the difference between a
/// budget and a lottery. It sits well under the float simplex's own
/// `MAX_ITERS` of 200,000, and a per-node WARM re-solve differs from its
/// predecessor by a handful of branch bounds, so on everything measured it is
/// two orders of magnitude clear of what a node actually spends: measured over
/// 28 instances, the median node spends 31 float iterations and the worst
/// (`air03`) 366.
const OPT_TREE_FLOAT_ITERS_PER_SOLVE: u64 = 65_536;

/// WHY a derivation produced nothing.
///
/// `"declined (budget or model out of reach)"` was one message covering at
/// least three unrelated events, and the difference between them is the
/// difference between "spend more" and "never spend anything here again".
/// [`OptTreeReport`] separates them so the caller can tell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptTreeDecline {
    /// `work_cap` was exhausted mid-descent. BUDGET, and the DETERMINISTIC one:
    /// two runs of the same derivation stop at the same place, so a larger cap
    /// is the only thing that changes the answer.
    WorkCap,
    /// The wall-clock SAFETY NET ran out mid-descent. BUDGET, and the one
    /// load-dependent stop left: seeing this means the net BOUND, which is the
    /// condition it is sized never to reach. It keeps its own tag precisely so
    /// that event can be grepped for rather than inferred.
    Deadline,
    /// `leaf_cap` was exceeded. BUDGET: a larger one may succeed.
    LeafCap,
    /// [`MAX_DEPTH`] was exceeded. BUDGET-ish, but a descent this deep on a
    /// bounded model is already pathological.
    Depth,
    /// `leaf_cap == 0` — the feature was switched off by the caller.
    Disabled,
    /// The `(value, witness)` pair did not re-check against the model.
    /// STRUCTURAL, and it means the verdict itself is in question.
    WitnessRejected,
    /// A leaf's relaxation ran to −∞, or the exact rim could not decide it.
    /// STRUCTURAL: no multiplier set closes an unbounded leaf and splitting an
    /// integral column cannot fix a continuous ray.
    UnboundedLeaf,
    /// The rim found an INTEGRAL relaxation optimum strictly better than the
    /// value being certified. STRUCTURAL, and a red flag on the verdict.
    ValueRefuted,
    /// A split cut did not round-trip through `f64`, or the rim could not be
    /// constructed. STRUCTURAL for this box.
    InexactCut,
    /// The finished tree failed its own final re-verification. STRUCTURAL, and
    /// a bug if it ever fires.
    VerifyFailed,
}

impl OptTreeDecline {
    /// The short tag used in the CLI's `certificate:` note.
    #[must_use]
    pub fn tag(self) -> &'static str {
        match self {
            Self::WorkCap => "work-cap",
            Self::Deadline => "deadline",
            Self::LeafCap => "leaf-cap",
            Self::Depth => "depth-cap",
            Self::Disabled => "disabled",
            Self::WitnessRejected => "witness-rejected",
            Self::UnboundedLeaf => "unbounded-leaf",
            Self::ValueRefuted => "value-refuted",
            Self::InexactCut => "inexact-cut",
            Self::VerifyFailed => "verify-failed",
        }
    }

    /// `true` when a larger budget could plausibly change the answer. The
    /// STRUCTURAL reasons return `false`: spending more time on them is pure
    /// waste, which is the whole point of separating them.
    #[must_use]
    pub fn is_budget(self) -> bool {
        matches!(
            self,
            Self::WorkCap | Self::Deadline | Self::LeafCap | Self::Depth
        )
    }

    /// `true` when this stop is REPRODUCIBLE: the same binary on the same input
    /// reaches it at the same point whatever else the machine is doing.
    ///
    /// Every reason is deterministic except [`Self::Deadline`], which is the
    /// wall-clock safety net and the only remaining way a derivation's OUTPUT
    /// can depend on machine load. A harness that asserts on emitted evidence
    /// should assert this.
    #[must_use]
    pub fn is_deterministic(self) -> bool {
        !matches!(self, Self::Deadline)
    }
}

/// What a derivation attempt cost and, when it produced nothing, why.
///
/// Always populated, success or not — the counters are the only way to tell a
/// descent that closed 30 leaves in 2 ms from one that ground through 40 000
/// LP solves to close nothing.
#[derive(Debug, Clone, Default)]
pub struct OptTreeReport {
    /// The terminal decline reason: the LAST one raised, which is the one that
    /// actually ended the descent. `None` on success.
    pub decline: Option<OptTreeDecline>,
    /// Leaves committed to the tree when the descent ended.
    pub leaves: usize,
    /// Deepest split level reached.
    pub max_depth: usize,
    /// Float-lane LP solves attempted.
    pub float_solves: usize,
    /// Exact-rim LP solves attempted — the expensive lane.
    pub rim_solves: usize,
    /// Nodes entered, i.e. boxes the descent asked a question about. One node
    /// is one exact box build plus its bound-leaf verification attempts, which
    /// is the unit [`Self::work`] is denominated in.
    pub nodes: u64,
    /// Float simplex iterations spent inside this derivation.
    pub float_iters: u64,
    /// Exact-rim simplex iterations spent inside this derivation, over both
    /// phases.
    pub rim_iters: u64,
    /// THE DETERMINISTIC WORK CLOCK: what this derivation spent, in the
    /// currency `OptimalityTreeBudget::work_cap` bounds.
    ///
    /// A pure function of `nodes`, `float_iters`, `rim_iters` and `rim_solves`
    /// — all four published here — so a consumer can re-derive it. It is a
    /// function of the model and the target value alone: no clock, no thread,
    /// no allocator. Two runs of the same derivation report the same number.
    pub work: u64,
    /// The root relaxation's own dual bound in the MINIMISE frame, when the
    /// root was solved and not closed outright. This is the certifying
    /// descent's own root bound — no cuts, no presolve — and it is the honest
    /// predictor of how big the cut-free tree has to be.
    pub root_bound: Option<BigRational>,
    /// `(z − root_bound) / max(1, |z|)`, both sides in the MINIMISE frame so
    /// the offset and the sense cancel. The integrality gap the certifying
    /// descent — no cuts, no presolve — actually has to close by branching.
    pub root_gap_rel: Option<f64>,
    /// How many nodes were abandoned at [`MAX_DEPTH`].
    ///
    /// A SEPARATE COUNTER because `decline` cannot carry it. The terminal
    /// reason is the last one raised, and a descent that abandons a 512-deep
    /// subtree then keeps working until the clock runs out reports `Deadline` —
    /// truthfully, and while hiding the fact that part of its tree was
    /// structurally unreachable. Measured on 41 MIPLIB-class instances this is
    /// nonzero on 5 of them (`markshare2`, `markshare_4_0`, `markshare_5_0`,
    /// `neos-1425699`, `p0548`), every one of which reported only `deadline`.
    pub depth_capped: usize,
    /// How many times `leaf_cap` was hit.
    ///
    /// A SEPARATE COUNTER for the same reason as [`Self::depth_capped`], and it
    /// was found the same way. Under the old 5 s clock the leaf cap could not
    /// fire at all (136 of 164 derivations declined on the deadline, ZERO on the
    /// cap). Under a work budget it does — `lseu` commits 20,270 leaves against
    /// a cap of 20,000 — but the TERMINAL reason is the last one raised, and a
    /// descent that trips the leaf cap deep in a subtree, unwinds, and then
    /// spends the rest of its budget in the exact rim reports only `work-cap`.
    /// Measured: `lseu` and `markshare1` both exceed the leaf cap and both
    /// report `work-cap`, so without this counter the event stays invisible
    /// exactly as the depth cap did.
    pub leaf_capped: usize,

    /// Leaves — bound leaves and Farkas leaves alike — that the COARSE
    /// dual-grid rung could not close and a finer rung then did. See
    /// [`OptimalityTreeBudget::dual_grid_bits`].
    ///
    /// Its own counter, and load-invariant, because it is the ONLY direct read
    /// on whether a chosen grid is too coarse. `leaves` cannot show it: the
    /// ladder's last rung is the lossless conversion, so a grid that closes
    /// nothing produces exactly the leaf count the pre-grid code produced and
    /// looks, from the outside, like a grid that closes everything.
    pub grid_fallbacks: usize,
}

/// Mutable descent bookkeeping. Separate from [`OptimalityTreeBudget`] because
/// the budget is an input and this is an output.
#[derive(Default)]
struct Diag {
    decline: Option<OptTreeDecline>,
    max_depth: usize,
    float_solves: usize,
    rim_solves: usize,
    /// The four terms of [`work_units`]. Kept RAW rather than pre-summed so the
    /// report can publish them and the total stays re-derivable.
    nodes: u64,
    float_iters: u64,
    rim_iters: u64,
    root_bound: Option<BigRational>,
    depth_capped: usize,
    leaf_capped: usize,
}

impl Diag {
    /// This descent's deterministic work clock. See [`work_units`].
    fn work(&self) -> u64 {
        work_units(
            self.nodes,
            self.float_iters,
            self.rim_iters,
            self.rim_solves as u64,
        )
    }

    /// LAST WRITER WINS for the terminal reason. A `None` raised deep in a
    /// subtree may be recovered by the parent falling through to the exact rim,
    /// so an early reason is not necessarily the terminal one; the last reason
    /// raised before the derivation gave up is. The events that must not be
    /// lost to that rule get their own counters instead — see
    /// [`OptTreeReport::depth_capped`] and [`OptTreeReport::leaf_capped`].
    fn raise(&mut self, r: OptTreeDecline) {
        match r {
            OptTreeDecline::Depth => self.depth_capped += 1,
            OptTreeDecline::LeafCap => self.leaf_capped += 1,
            _ => {}
        }
        self.decline = Some(r);
    }
}

/// Split depth cap. Independent of `leaf_cap` because a pathological descent
/// can run deep without producing leaves (an integral column with a huge
/// range); this bounds the recursion regardless.
const MAX_DEPTH: usize = 512;

/// The dual grid every [`OptimalityTreeBudget`] starts on.
///
/// `2^-12` is an INTERIOR optimum, not a "coarser is better" limit, and that is
/// the whole shape of the trade. Coarser rationals are fewer bytes right up to
/// the point where the coarse rung stops closing leaves; past it the ladder
/// falls back to the lossless rung and re-emits exactly the enormous rationals
/// the grid existed to avoid, so the artifact grows again.
///
/// Measured on 5 MIPLIB instances, `--opt-tree-secs 120`, one binary with
/// `--opt-tree-grid` flipped between runs, arms interleaved, 2 reps agreeing to
/// the byte on all 70 runs, `ay-milp verify` exit 0 on all 70 (geomean of
/// bytes against the grid-off arm; `fb` is `OptTreeReport::grid_fallbacks`
/// summed over the same five):
///
/// ```text
///   grid   geomean   worst    fb
///   2^-32    0.619   0.808    55
///   2^-24    0.581   0.732    53
///   2^-16    0.542   0.661    62
///   2^-12    0.524   0.628    51   <- shipped
///   2^-8     0.545   0.635   426
///   2^-4     0.591   0.844  1066
/// ```
///
/// See the development design notes.
const DEFAULT_DUAL_GRID_BITS: Option<u32> = Some(12);

/// Snap `v` to the nearest multiple of `2^-bits`, exactly.
///
/// This is [`crate::bab`]'s `exact_bound` snapper, generalised over the grid
/// and reused for the same reason it exists there: a lossless `f64` dual is a
/// dyadic rational whose denominator can reach `2^1074`, and once those meet in
/// a sum every downstream numerator carries the union of their exponents.
/// Rounding first caps the denominator at `2^bits`.
///
/// `None` on a non-finite input, or on a value so large that the scaled
/// integer would not survive the round trip — the caller then drops the dual,
/// which only weakens the bound.
///
/// A dual that rounds to zero comes back as `Some(0)`, not `None`, and both
/// callers then DROP it. That is not a special case: round-to-nearest cannot
/// flip a sign, so the only thing rounding can do to a small dual is delete it,
/// and deleting a dual is the one edit weak duality most obviously permits —
/// the row simply names no fact.
///
/// The difference from `exact_bound` is scope, not arithmetic. `exact_bound`
/// also zeroes duals whose sign points at an INFINITE row bound; that decision
/// belongs to the caller here, because the two callers cite different facts
/// (a bound leaf's row side vs a Farkas ray's) and each already makes it.
pub(crate) fn snap_dyadic(v: f64, bits: u32) -> Option<BigRational> {
    if !v.is_finite() {
        return None;
    }
    // 2^bits as an f64 is exact for any bits <= 1023; the caller's grids are
    // single- and double-digit.
    let grid = 2f64.powi(i32::try_from(bits).ok()?);
    if !grid.is_finite() {
        return None;
    }
    let scaled = (v * grid).round();
    if !scaled.is_finite() || scaled.abs() > 9.0e18 {
        return None;
    }
    // `scaled` is an integer-valued f64 below 2^63, so the cast is exact.
    #[allow(clippy::cast_possible_truncation)]
    let numer = num_bigint::BigInt::from(scaled as i64);
    // `BigRational::new` reduces, which is what keeps a dual of, say, 1/2
    // printing as `1/2` and not `8388608/16777216`.
    Some(BigRational::new(
        numer,
        num_bigint::BigInt::from(1u32) << bits,
    ))
}

/// The rungs [`float_leaf`] tries, coarsest first, always ending at the
/// lossless conversion.
///
/// Ending at `None` is what makes the grid a pure size optimisation rather
/// than a trade: a leaf the coarse rung cannot close still gets the exact
/// float duals it would have had, so the ladder closes every leaf the
/// pre-grid code closed. What varies is only how many BYTES the closure
/// costs.
/// Allocation-free, and ONE rung when the grid is off so the pre-grid arm does
/// exactly the work it always did — a duplicated rung would re-price and
/// re-verify every leaf the lane declines, which would show up as derivation
/// cost in the very comparison the grid is being measured by.
fn grid_ladder(bits: Option<u32>) -> impl Iterator<Item = Option<u32>> {
    [bits, None]
        .into_iter()
        .take(if bits.is_some() { 2 } else { 1 })
}

/// Derive a whole-tree optimality certificate for `value` on `model`, or
/// `None`.
///
/// # This does not capture the search's tree — it runs its own
///
/// The obvious design is to record the branch-and-bound tree and export it.
/// That design is unsound here for a reason the preceding review named
/// precisely (the development design notes): the
/// existing infeasibility capture is safe only because *a bound-licensed box
/// exists only while an incumbent exists, and a search holding an incumbent can
/// never end `Infeasible`* — so `TreeCapture::finalize` never consumes a
/// closure licensed by anything but emptiness. An OPTIMALITY tree ALWAYS has an
/// incumbent. Capturing it would, for the first time, consume closures licensed
/// by reduced-cost fixing, cutoff-row propagation and LB no-goods, each of
/// which removes genuinely integer-feasible points, and the composition
/// argument for those routes back through the objective granularity — the very
/// lattice device the bound leaf exists to avoid needing.
///
/// So this derives from scratch, against the CALLER's model, with no cuts, no
/// presolve, no reduced-cost fixing and no propagation. Every fact in the
/// output is one this function proved itself on the exact rim. The search
/// contributes exactly two numbers — `value` and `witness` — and BOTH are
/// re-checked here before any work starts, and again by
/// [`MilpOptimalityCertificate::verify`] before the certificate is handed out.
///
/// # The cost of that independence, stated plainly
///
/// A certifying descent with no cuts and no presolve explores a tree that is
/// larger — often much larger — than the one the engine actually walked. That
/// is the price of an artifact that owes the engine nothing, and it is why this
/// fails closed on a leaf budget rather than promising coverage. See the
/// module-level measurements in `tests/opt_cert.rs`.
///
/// # Termination
///
/// Each split strictly shrinks an integral column's range, so a descent over a
/// box whose integral columns are all bounded terminates. Nothing here proves a
/// bound on the leaf COUNT, and an integral column with an infinite side can
/// descend forever — `leaf_cap` and `MAX_DEPTH` are caps, not a terminator, and
/// are the honest reason this returns `Option`.
#[must_use]
pub fn derive_optimality_tree(
    model: &Model,
    value: &BigRational,
    witness: &[BigRational],
    budget: &OptimalityTreeBudget,
) -> Option<MilpOptimalityCertificate> {
    derive_optimality_tree_reported(model, value, witness, budget).0
}

/// [`derive_optimality_tree`], plus the [`OptTreeReport`] saying what the
/// attempt cost and — when it produced nothing — WHICH of the several unrelated
/// events named by `OptTreeDecline` ended it.
///
/// Behaviourally identical to `derive_optimality_tree`; the report is pure
/// bookkeeping and touches neither the descent's decisions nor the artifact.
#[must_use]
pub fn derive_optimality_tree_reported(
    model: &Model,
    value: &BigRational,
    witness: &[BigRational],
    budget: &OptimalityTreeBudget,
) -> (Option<MilpOptimalityCertificate>, OptTreeReport) {
    let mut report = OptTreeReport::default();
    // THE PRIMAL HALF IS RE-CHECKED BEFORE ANY DUAL WORK. A tree proving
    // `objective >= value` is worthless — indeed misleading — if `value` is not
    // actually attained, so a witness that does not stand up ends the
    // derivation here rather than producing a bound dressed as an optimum.
    if witness.len() != model.num_cols() || model.check_point(witness).is_err() {
        report.decline = Some(OptTreeDecline::WitnessRejected);
        return (None, report);
    }
    if &model.objective_value_at(witness) != value {
        report.decline = Some(OptTreeDecline::WitnessRejected);
        return (None, report);
    }
    if budget.leaf_cap == 0 {
        report.decline = Some(OptTreeDecline::Disabled);
        return (None, report);
    }

    let mut work = model.clone();
    // ONE lowered float LP for the whole descent. `None` (a model the float
    // lane cannot lower) is not fatal: every leaf then falls through to the
    // exact rim, which is slower but is the authority in either case.
    let descent = Descent {
        model,
        obj: minimize_frame_objective(model),
        obj_min: minimize_frame_objective_dense(model),
        flp: FloatLp::from_model(model, &float_objective(model), Sense::Minimize).map(|lp| {
            FloatCtx {
                lp,
                warm: std::cell::RefCell::new(None),
                grid_fallbacks: std::cell::Cell::new(0),
            }
        }),
        z: value.clone(),
        budget,
        diag: std::cell::RefCell::new(Diag::default()),
    };
    let mut leaves = 0usize;
    let root = descent.node(&mut work, &mut leaves, 0);
    {
        let d = descent.diag.borrow();
        report.leaves = leaves;
        report.max_depth = d.max_depth;
        report.float_solves = d.float_solves;
        report.rim_solves = d.rim_solves;
        report.nodes = d.nodes;
        report.float_iters = d.float_iters;
        report.rim_iters = d.rim_iters;
        report.work = d.work();
        report.root_bound = d.root_bound.clone();
        report.decline = d.decline;
        report.depth_capped = d.depth_capped;
        report.leaf_capped = d.leaf_capped;
        report.grid_fallbacks = descent.flp.as_ref().map_or(0, |f| f.grid_fallbacks.get());
        // BOTH SIDES IN THE MINIMISE FRAME. `z_min` is the witness priced by the
        // very objective vector the root LP minimised, so the model's offset and
        // its sense cancel and the difference is the gap the descent has to
        // branch away.
        if let Some(rb) = &d.root_bound {
            let z_min: BigRational = descent
                .obj_min
                .iter()
                .zip(witness)
                .map(|(c, x)| c * x)
                .sum();
            let denom = z_min.to_f64().unwrap_or(0.0).abs().max(1.0);
            report.root_gap_rel = (&z_min - rb).to_f64().map(|g| g / denom);
        }
    }
    let Some(root) = root else {
        // A descent that ended without raising anything is a caps-free give-up
        // we have no name for. Attribute it to the bound that is actually gone,
        // preferring the DETERMINISTIC one: a run that stopped with its work
        // spent must not report the clock, or the diagnostic would claim a
        // load-dependence the run did not have.
        report.decline = report.decline.or(Some(if report.work >= budget.work_cap {
            OptTreeDecline::WorkCap
        } else {
            OptTreeDecline::Deadline
        }));
        return (None, report);
    };

    let cert = MilpOptimalityCertificate {
        value: value.clone(),
        witness: witness.to_vec(),
        root,
    };
    // FAIL CLOSED ON THE WHOLE ARTIFACT. Every leaf was already verified
    // against the box the deriver believed it was in; this re-verifies against
    // the box the CONSUMER will reconstruct, which is the only box that counts.
    if cert.verify(model).is_err() {
        report.decline = Some(OptTreeDecline::VerifyFailed);
        return (None, report);
    }
    (Some(cert), report)
}

/// The model's objective in the exact-rim's minimise frame: negated for a
/// Maximize model, exactly as `LpSession` does before calling
/// [`ExactLp::minimize`]. Coefficients come from the exact side-store, so a
/// column whose `f64` advice underflowed to zero still carries its true value.
fn minimize_frame_objective(model: &Model) -> Vec<(u32, Rational)> {
    let sense = model.sense();
    let mut out = Vec::new();
    for (j, spec) in model.cols.iter().enumerate() {
        if spec.obj != 0.0 || model.exact_obj.contains_key(&(j as u32)) {
            let a = model.obj_coeff_exact_at(j as u32, spec.obj);
            let a = match sense {
                Sense::Minimize => a,
                Sense::Maximize => -a,
            };
            if !a.is_zero() {
                out.push((j as u32, Rational::from(a)));
            }
        }
    }
    out
}

/// The same objective as [`minimize_frame_objective`], DENSE and exact: one
/// entry per column, which is the shape [`bound_multipliers_from_duals`] needs
/// to accumulate residuals into.
fn minimize_frame_objective_dense(model: &Model) -> Vec<BigRational> {
    let sense = model.sense();
    let mut out = vec![BigRational::zero(); model.num_cols()];
    for (j, spec) in model.cols.iter().enumerate() {
        if spec.obj != 0.0 || model.exact_obj.contains_key(&(j as u32)) {
            let a = model.obj_coeff_exact_at(j as u32, spec.obj);
            out[j] = match sense {
                Sense::Minimize => a,
                Sense::Maximize => -a,
            };
        }
    }
    out
}

/// The minimise-frame objective as `f64` ADVICE for the float lane. Rounding
/// here is harmless by construction: it can only make the float lane's duals a
/// worse guess, and every proposal built from them is re-verified against the
/// EXACT objective before it becomes evidence.
fn float_objective(model: &Model) -> Vec<(u32, f64)> {
    let sense = model.sense();
    let mut out = Vec::new();
    for (j, spec) in model.cols.iter().enumerate() {
        if spec.obj != 0.0 || model.exact_obj.contains_key(&(j as u32)) {
            let a = model
                .obj_coeff_exact_at(j as u32, spec.obj)
                .to_f64()
                .unwrap_or(spec.obj);
            let a = match sense {
                Sense::Minimize => a,
                Sense::Maximize => -a,
            };
            if a != 0.0 && a.is_finite() {
                out.push((j as u32, a));
            }
        }
    }
    out
}

/// The exact effective box of `work`'s current column bounds, in the shape
/// [`OptimalityCertificate::verify_bound_leaf`] and
/// [`FarkasCertificate::verify_with_col_bounds`] want.
fn exact_box(work: &Model) -> (Vec<Option<BigRational>>, Vec<Option<BigRational>>) {
    let n = work.num_cols();
    let lb = (0..n)
        .map(|j| exact(work.col_bounds(Col(j as u32)).0))
        .collect();
    let ub = (0..n)
        .map(|j| exact(work.col_bounds(Col(j as u32)).1))
        .collect();
    (lb, ub)
}

/// The shared caller-frame float lane: one lowered LP for the whole descent,
/// plus the previous leaf's basis as a warm hint -- DFS-adjacent leaves differ
/// by a handful of branch bounds, so each re-solve is a short dual repair
/// instead of a cold phase-I solve. Mirrors [`crate::tree_cert`]'s `FloatCtx`.
struct FloatCtx {
    lp: FloatLp,
    warm: std::cell::RefCell<Option<(Vec<usize>, Vec<NbBound>)>>,
    /// Leaves — of EITHER kind — the COARSE grid rung failed to close and a
    /// finer rung then did. A load-invariant read on how load-bearing the
    /// ladder's fallback is: at zero the coarse grid is closing everything by
    /// itself, and at `num_leaves` the grid is buying nothing but retries.
    grid_fallbacks: std::cell::Cell<usize>,
}

/// What the float lane made of the current box. Every variant is ADVICE: the
/// certificate-bearing ones have already been re-verified exactly against
/// `model` by the time they are returned, and `Decline` simply hands the leaf
/// to the exact rim.
enum FloatVerdict {
    /// An exact-verified Farkas witness for the leaf's box.
    Empty(FarkasCertificate),
    /// An exact-verified multiplier set dominating `z` over the leaf's box.
    Dominated(Vec<Multiplier>),
    /// Not closed, but the relaxation named a fractional integral column to
    /// split on: `(column, floor of its value)`.
    Branch(usize, f64),
    /// The float lane has nothing useful to say.
    Decline,
}

/// Solve the CURRENT box of `work` on the shared float LP and turn the result
/// into EXACT, ALREADY-VERIFIED evidence where it can.
///
/// # Why a float lane cannot weaken the certificate
///
/// The float solve contributes no arithmetic to the artifact. Its duals are
/// exactified into rational multipliers and the resulting combination is
/// re-verified against `model` at the leaf's reconstructed box before it is
/// returned -- so a float that lies produces `Decline` or a rejected proposal,
/// never a bad certificate, and the exact rim is still behind it.
/// [`derive_optimality_tree`] then verifies the whole tree a second time.
///
/// The dual SIGN CONVENTION is deliberately not relied upon: both orientations
/// are tried and only a verified one survives, exactly as
/// [`exact_farkas_from_float_ray_grid`] does for the phase-I ray.
///
/// `obj_out` is `Some` only at the ROOT, where it receives the relaxation's
/// f64 objective in the MINIMISE frame if the solve reached `Optimal`. It is
/// advice about the root's dual bound — never evidence — and exists so
/// [`OptTreeReport::root_gap_rel`] can be reported. `None` everywhere else
/// keeps the O(cols) walk off the per-node path.
fn float_leaf(
    model: &Model,
    work: &Model,
    flp: &FloatCtx,
    obj_min: &[BigRational],
    z: &BigRational,
    deadline: Option<Instant>,
    branch: OptTreeBranch,
    grid_bits: Option<u32>,
    obj_out: Option<&mut Option<f64>>,
) -> FloatVerdict {
    let n = work.num_cols();
    let m = work.num_rows();
    let mut lo = Vec::with_capacity(n + m);
    let mut up = Vec::with_capacity(n + m);
    for j in 0..n {
        let (l, u) = work.col_bounds(Col(j as u32));
        lo.push(l);
        up.push(u);
    }
    for r in 0..m {
        let (_, l, u) = work.row(Row(r as u32));
        lo.push(l);
        up.push(u);
    }
    let hint = flp.warm.borrow_mut().take();
    let cand = flp.lp.solve_bounded(
        &lo,
        &up,
        hint.as_ref().map(|(b, a)| (b.as_slice(), a.as_slice())),
        deadline,
    );
    // Whatever the verdict, the basis in hand seeds the NEXT leaf's repair.
    *flp.warm.borrow_mut() = Some((cand.basis.clone(), cand.at.clone()));

    let (lb, ub) = exact_box(work);
    match cand.status {
        SimplexStatus::PrimalInfeasible => {
            // THE SAME LADDER as the bound leaf's, for the same reason and with
            // the same last rung. An `Empty` leaf's multipliers are exactified
            // f64s too, and on a Farkas-dominated model they are where the
            // bytes are: `flugpl`'s tree at grid off is 871 empty leaves
            // (384,775 B) against 103 bound leaves (93,150 B).
            if cand.farkas.len() == m {
                for (rung, bits) in grid_ladder(grid_bits).into_iter().enumerate() {
                    if let Some(farkas) = exact_farkas_from_float_ray_grid(work, &cand.farkas, bits)
                    {
                        if farkas.verify_with_col_bounds(model, &lb, &ub).is_ok() {
                            if rung > 0 {
                                flp.grid_fallbacks.set(flp.grid_fallbacks.get() + 1);
                            }
                            return FloatVerdict::Empty(farkas);
                        }
                    }
                }
            }
            FloatVerdict::Decline
        }
        SimplexStatus::Optimal => {
            // ONLY WHEN ASKED, which is only at the root. This is an O(cols)
            // walk with a rational-to-float conversion per objective entry; run
            // at every node it would be a measurable tax on the very descent
            // the number exists to explain, and an instrument that changes what
            // it measures is worse than no instrument.
            if let Some(slot) = obj_out {
                if cand.values.len() >= n {
                    let mut acc = 0.0f64;
                    for (j, cj) in obj_min.iter().enumerate().take(n) {
                        if !cj.is_zero() {
                            acc += cj.to_f64().unwrap_or(0.0) * cand.values[j];
                        }
                    }
                    *slot = Some(acc);
                }
            }
            // THE GRID LADDER, coarsest rung first. A coarse grid is the cheap
            // artifact and closes most leaves outright; a leaf it cannot close
            // retries on the finer rungs BEFORE the descent pays for a split,
            // because a split costs a whole extra leaf and its subtree while a
            // finer rung costs one more exact re-verification of an LP that is
            // already solved and in hand. The ladder's last rung is always
            // `None` — the lossless conversion this feature shipped with — so
            // it closes every leaf the old code closed and no fewer.
            if cand.duals.len() == m {
                for (rung, bits) in grid_ladder(grid_bits).into_iter().enumerate() {
                    for sign in [1.0f64, -1.0] {
                        if let Some(mults) = bound_multipliers_from_duals(
                            work,
                            obj_min,
                            &cand.duals,
                            sign,
                            &lb,
                            &ub,
                            bits,
                        ) {
                            if OptimalityCertificate::verify_bound_leaf(&mults, model, &lb, &ub, z)
                                .is_ok()
                            {
                                if rung > 0 {
                                    flp.grid_fallbacks.set(flp.grid_fallbacks.get() + 1);
                                }
                                return FloatVerdict::Dominated(mults);
                            }
                        }
                    }
                }
            }
            // Not closed. The relaxation's own point picks the split column; it
            // is advice, and a wrong choice costs leaves, never soundness.
            if cand.values.len() >= n {
                let mut best: Option<(usize, f64, f64)> = None;
                for j in 0..n {
                    if matches!(
                        work.col_kind(Col(j as u32)),
                        ColKind::Binary | ColKind::Integer
                    ) {
                        let v = cand.values[j];
                        if v.is_finite() && (v - v.round()).abs() > 1e-6 {
                            if branch == OptTreeBranch::FirstFractional {
                                return FloatVerdict::Branch(j, v.floor());
                            }
                            // Most-infeasible: distance from the nearest
                            // integer, largest first.
                            let score = (v - v.round()).abs();
                            if best.is_none_or(|(_, _, s)| score > s) {
                                best = Some((j, v.floor(), score));
                            }
                        }
                    }
                }
                if let Some((j, floor, _)) = best {
                    return FloatVerdict::Branch(j, floor);
                }
            }
            FloatVerdict::Decline
        }
        _ => FloatVerdict::Decline,
    }
}

/// Turn an approximate row-dual vector into EXACT multipliers whose oriented
/// combination is exactly the minimise-frame objective.
///
/// This is the certificate-bearing analogue of [`crate::ns`]'s
/// Neumaier--Shcherbina bound. NS produces a rigorous NUMBER from any dual
/// vector, which is why the engine can prune safely -- but a number is not
/// evidence, which is exactly why `Outcome::Feasible`'s `dual_bound` has to
/// document itself as "not independently checkable". The same weak-duality
/// argument written as MULTIPLIERS instead of a scalar IS evidence:
///
/// * each row's dual becomes a positive multiplier on the bound side its sign
///   selects (`y_r > 0` -> the row's lower side, `y_r < 0` -> its upper side);
/// * a row whose selected side is INFINITE names no fact, so its dual is
///   dropped to zero -- legitimate, because weak duality holds for ANY `y` and
///   dropping only weakens the bound;
/// * the residual `d_j = c_j - sum_r y_r a_rj` is then priced at the column's
///   own bound, `d_j > 0` at the lower side and `d_j < 0` at the upper, which
///   makes the combination equal the objective EXACTLY rather than
///   approximately.
///
/// `None` when a residual's needed column-bound side is infinite: there is no
/// fact to cancel against, the identity cannot close, and fudging it is exactly
/// the hole the design review left open (its "dual analogue of
/// `eliminate_unbounded_residuals`"). Failing closed is the answer -- and the
/// exact rim behind this lane cannot reach the case at all, because an
/// unbounded direction makes its LP `Unbounded` rather than `Optimal`.
///
/// `grid_bits` ROUNDS each row dual to a multiple of `2^-grid_bits` first; the
/// residuals `d_j` are then computed EXACTLY from the rounded duals, so the
/// identity `sum multipliers == objective` still closes to the last bit and the
/// verifier's coefficient check is untouched. Only the CONSTANT moves, and only
/// downwards — which is the bound getting weaker, which is the trade. `None`
/// keeps the lossless conversion. See [`OptimalityTreeBudget::dual_grid_bits`].
///
/// Every other `f64` here converts to a rational LOSSLESSLY, so nothing else is
/// rounded; the floats' inaccuracy costs tightness (a leaf that fails to close
/// and is split instead) and never validity.
fn bound_multipliers_from_duals(
    work: &Model,
    obj_min: &[BigRational],
    duals: &[f64],
    sign: f64,
    lb: &[Option<BigRational>],
    ub: &[Option<BigRational>],
    grid_bits: Option<u32>,
) -> Option<Vec<Multiplier>> {
    let n = work.num_cols();
    let m = work.num_rows();
    let mut mults: Vec<Multiplier> = Vec::new();
    // `d` starts at the objective and has each row's contribution removed.
    let mut d: Vec<BigRational> = obj_min.to_vec();
    for r in 0..m {
        let raw = duals[r] * sign;
        if !raw.is_finite() || raw == 0.0 {
            continue;
        }
        // ROUND FIRST, then read the sign off the ROUNDED value. Round-to-
        // nearest cannot flip a sign -- it can only collapse a value to ZERO --
        // so this is not a different SIDE from the one `raw` would have chosen;
        // what it buys is that the zero case is handled before a bound side has
        // been committed to, because a dual that snaps to zero names no fact and
        // `combine_bounded` rejects a non-positive multiplier outright.
        let Some(y) = (match grid_bits {
            Some(bits) => snap_dyadic(raw, bits),
            None => exact(raw),
        }) else {
            continue;
        };
        if y.is_zero() {
            continue;
        }
        let (coeffs, row_lo, row_hi) = work.row(Row(r as u32));
        let positive = y > BigRational::zero();
        // A dual pointing at an infinite bound names no fact. Drop it.
        let bound = if positive { row_lo } else { row_hi };
        if !bound.is_finite() {
            continue;
        }
        for &(c, a) in coeffs {
            if c as usize >= n || !a.is_finite() {
                return None;
            }
            let a = work.row_coeff_exact_small(r, c, a);
            d[c as usize] -= &y * &a;
        }
        mults.push(Multiplier {
            fact: FactRef::RowBound {
                row: Row(r as u32),
                side: if positive {
                    BoundSide::Lower
                } else {
                    BoundSide::Upper
                },
            },
            coeff: if positive { y } else { -y },
        });
    }
    for (j, dj) in d.iter().enumerate() {
        if dj.is_zero() {
            continue;
        }
        let positive = *dj > BigRational::zero();
        // NO FACT, NO MULTIPLIER, NO CERTIFICATE.
        let slot = if positive { &lb[j] } else { &ub[j] };
        slot.as_ref()?;
        mults.push(Multiplier {
            fact: FactRef::ColBound {
                col: Col(j as u32),
                side: if positive {
                    BoundSide::Lower
                } else {
                    BoundSide::Upper
                },
            },
            coeff: if positive { dj.clone() } else { -dj.clone() },
        });
    }
    Some(mults)
}

/// Everything the descent holds FIXED: the caller's model, the objective in
/// both shapes the two lanes want, the shared float LP, the target value and
/// the budget. Only `work` (the current box), the leaf tally and the depth
/// vary from node to node, which is what keeps the recursive signatures small.
struct Descent<'a> {
    /// The CALLER's model. Every leaf is verified against this, never against
    /// the working copy the descent mutates.
    model: &'a Model,
    /// Sparse minimise-frame objective, for [`ExactLp::minimize`].
    obj: Vec<(u32, Rational)>,
    /// Dense minimise-frame objective, for the float lane's residuals.
    obj_min: Vec<BigRational>,
    /// The shared float LP, or `None` when the model could not be lowered.
    flp: Option<FloatCtx>,
    /// The value every leaf must dominate.
    z: BigRational,
    budget: &'a OptimalityTreeBudget,
    /// Descent bookkeeping. Written on every give-up so the caller can tell
    /// "ran out of time" from "cannot be done at any price".
    diag: std::cell::RefCell<Diag>,
}

impl Descent<'_> {
    fn raise(&self, r: OptTreeDecline) -> Option<OptTreeNode> {
        self.diag.borrow_mut().raise(r);
        None
    }

    /// Work still available, in [`work_units`]. Zero means the deterministic
    /// budget is gone.
    fn work_left(&self) -> u64 {
        self.budget
            .work_cap
            .saturating_sub(self.diag.borrow().work())
    }

    /// THE DETERMINISTIC STOP, and the one checked first everywhere.
    ///
    /// Checking work before the clock is what makes the wall a genuine safety
    /// net: [`OptTreeDecline::Deadline`] can then only be raised by a descent
    /// that still had work left, which is exactly the event "the net bound".
    fn out_of_work(&self) -> bool {
        self.work_left() == 0
    }

    /// Certify the CURRENT box of `work`, splitting when it neither is empty
    /// nor carries a dual bound reaching `z`.
    fn node(&self, work: &mut Model, leaves: &mut usize, depth: usize) -> Option<OptTreeNode> {
        let (model, obj, obj_min, z, budget) = (
            self.model,
            self.obj.as_slice(),
            self.obj_min.as_slice(),
            &self.z,
            self.budget,
        );
        let flp = self.flp.as_ref();
        {
            let mut d = self.diag.borrow_mut();
            d.max_depth = d.max_depth.max(depth);
            // CHARGED ON ENTRY, before any of this node's work is done, so the
            // clock cannot be dodged by a node that returns early.
            d.nodes += 1;
        }
        // WORK BEFORE CLOCK, here and at every other stop. See `out_of_work`.
        if self.out_of_work() {
            return self.raise(OptTreeDecline::WorkCap);
        }
        if budget.expired() {
            return self.raise(OptTreeDecline::Deadline);
        }
        if depth > MAX_DEPTH {
            return self.raise(OptTreeDecline::Depth);
        }
        // An empty box needs no LP at all.
        for j in 0..work.num_cols() {
            let (lo, hi) = work.col_bounds(Col(j as u32));
            if lo > hi {
                let out = trivial_empty_leaf(model, work, j, leaves, budget);
                if out.is_none() {
                    self.diag.borrow_mut().raise(if *leaves > budget.leaf_cap {
                        OptTreeDecline::LeafCap
                    } else {
                        OptTreeDecline::VerifyFailed
                    });
                }
                return out;
            }
        }

        // FLOAT FIRST: milliseconds of advice, then one exact verification of
        // authority. Every branch below has already been exact-verified against the
        // caller's model at this leaf's reconstructed box; a decline falls through
        // to the exact rim unchanged.
        if let Some(flp) = flp {
            self.diag.borrow_mut().float_solves += 1;
            let mut root_obj = None;
            let verdict = {
                // THE FLOAT LANE IS BOUNDED BY WORK, NOT BY THE CLOCK.
                // `IterCap` is the simplex's own work clock — the mechanism
                // `bab.rs` already uses to keep strong branching
                // load-independent — and a solve that runs out of it returns
                // `Stopped`, which this descent reads as
                // `FloatVerdict::Decline` exactly as it reads any other failure.
                //
                // A FIXED allowance, deliberately NOT the descent's remaining
                // budget. Deriving it from what is left would make the float
                // lane behave differently near exhaustion, which would make the
                // TREE SHAPE a function of the cap — so a larger budget could
                // produce a different (not merely longer) descent, and the
                // monotonicity a budget is supposed to have would be gone. The
                // iterations are still CHARGED, so a grinding float lane still
                // exhausts the budget; it just does so at node granularity.
                let _cap = crate::simplex::IterCap::set(OPT_TREE_FLOAT_ITERS_PER_SOLVE);
                let before = crate::simplex::stats::solve_work();
                let v = float_leaf(
                    model,
                    work,
                    flp,
                    obj_min,
                    z,
                    budget.deadline,
                    budget.branch,
                    budget.dual_grid_bits,
                    (depth == 0).then_some(&mut root_obj),
                );
                self.diag.borrow_mut().float_iters +=
                    crate::simplex::stats::solve_work().saturating_sub(before);
                v
            };
            if depth == 0 {
                if let Some(v) = root_obj.and_then(BigRational::from_float) {
                    let mut d = self.diag.borrow_mut();
                    if d.root_bound.is_none() {
                        d.root_bound = Some(v);
                    }
                }
            }
            match verdict {
                FloatVerdict::Empty(farkas) => {
                    *leaves += 1;
                    if *leaves > budget.leaf_cap {
                        return self.raise(OptTreeDecline::LeafCap);
                    }
                    return Some(OptTreeNode::Empty { farkas });
                }
                FloatVerdict::Dominated(multipliers) => {
                    *leaves += 1;
                    if *leaves > budget.leaf_cap {
                        return self.raise(OptTreeDecline::LeafCap);
                    }
                    return Some(OptTreeNode::Dominated { multipliers });
                }
                FloatVerdict::Branch(j, floor) => {
                    if let Some(node) = self.split_at(work, j, floor, leaves, depth) {
                        return Some(node);
                    }
                    // The split itself declined (an inexact cut, or a child the
                    // budget could not finish). Fall through: the exact rim may
                    // still close this leaf outright.
                    if self.out_of_work() {
                        return self.raise(OptTreeDecline::WorkCap);
                    }
                    if budget.expired() {
                        return self.raise(OptTreeDecline::Deadline);
                    }
                }
                FloatVerdict::Decline => {
                    if self.out_of_work() {
                        return self.raise(OptTreeDecline::WorkCap);
                    }
                    if budget.expired() {
                        return self.raise(OptTreeDecline::Deadline);
                    }
                }
            }
        }

        // THE RIM IS BOUNDED BY THE SAME WORK BUDGET. `max_iters` is capped at
        // what the descent can still afford as well as at the rim's own default,
        // so a single exact solve cannot overshoot the deterministic cap by more
        // than the rounding of one iteration — and the overshoot it can produce
        // is itself a function of the model, not of the machine.
        let rim_budget = Budget {
            deadline: budget.deadline,
            max_iters: Budget::default_iters(work.num_cols() + work.num_rows())
                .min((self.work_left() / OPT_TREE_RIM_ITER_COST).max(1)),
        };
        self.diag.borrow_mut().rim_solves += 1;
        let Some(mut rim) = ExactLp::new_within(work, budget.deadline) else {
            return self.raise(if self.out_of_work() {
                OptTreeDecline::WorkCap
            } else if budget.expired() {
                OptTreeDecline::Deadline
            } else {
                OptTreeDecline::InexactCut
            });
        };
        let verdict = rim.minimize(obj, &rim_budget);
        self.diag.borrow_mut().rim_iters += rim.iters_total();
        match verdict {
            LpOptimum::Infeasible(farkas) => {
                let (lb, ub) = exact_box(work);
                // The rim's own certificate, re-checked against the box it is about
                // to represent before it is adopted.
                if farkas.verify_with_col_bounds(model, &lb, &ub).is_err() {
                    return self.raise(OptTreeDecline::VerifyFailed);
                }
                *leaves += 1;
                if *leaves > budget.leaf_cap {
                    return self.raise(OptTreeDecline::LeafCap);
                }
                Some(OptTreeNode::Empty { farkas })
            }
            // A leaf whose relaxation runs to −∞ has no finite dual bound, so no
            // multiplier set can close it; splitting cannot fix an unbounded
            // continuous direction either. Fail closed — and note this arm can
            // never be a budget event: a clock and an iteration cap both produce
            // `Unknown`, never `Unbounded`.
            LpOptimum::Unbounded => self.raise(OptTreeDecline::UnboundedLeaf),
            // AN UNDECIDED RIM NAMES ITS OWN REASON. `max_iters` above is
            // clipped by the work still available, so an `IterationLimit` raised
            // by that clip is a BUDGET event and must not be filed as
            // `unbounded-leaf` — that tag tells a caller never to spend anything
            // here again, which would be exactly wrong. The rim's iterations are
            // charged before this match, so `out_of_work` is true in precisely
            // the clipped case.
            LpOptimum::Unknown(reason) => self.raise(match reason {
                UnknownReason::IterationLimit if self.out_of_work() => OptTreeDecline::WorkCap,
                UnknownReason::Timeout => OptTreeDecline::Deadline,
                _ => OptTreeDecline::UnboundedLeaf,
            }),
            LpOptimum::Optimal {
                value: rim_value,
                multipliers,
            } => {
                // THE ROOT'S OWN CUT-FREE DUAL BOUND, recorded once. This is the
                // number that says how big the certifying tree has to be, and it
                // is a by-product of an LP the descent was solving anyway.
                if depth == 0 {
                    self.diag.borrow_mut().root_bound = Some(rim_value.clone());
                }
                let (lb, ub) = exact_box(work);
                // CLOSE BY DOMINATION when the rim's own exact dual multipliers
                // already price this box at or beyond the incumbent. `>=` is
                // deliberate: a leaf bounded exactly AT `z` contains nothing
                // BETTER, which is the whole claim.
                if OptimalityCertificate::verify_bound_leaf(&multipliers, model, &lb, &ub, z)
                    .is_ok()
                {
                    *leaves += 1;
                    if *leaves > budget.leaf_cap {
                        return self.raise(OptTreeDecline::LeafCap);
                    }
                    return Some(OptTreeNode::Dominated { multipliers });
                }
                // Not dominated: split on a column whose relaxation value is
                // fractional.
                let vals = rim.structural_values();
                drop(rim);
                let integral = |j: usize| {
                    matches!(
                        work.col_kind(Col(j as u32)),
                        ColKind::Binary | ColKind::Integer
                    ) && !vals[j].is_integer()
                };
                let frac = match budget.branch {
                    OptTreeBranch::FirstFractional => (0..work.num_cols()).find(|&j| integral(j)),
                    // Most-infeasible on the EXACT values: the fractional part
                    // furthest from an integer. Advice, like every branching
                    // decision here.
                    OptTreeBranch::MostFractional => (0..work.num_cols())
                        .filter(|&j| integral(j))
                        .max_by(|&a, &b| {
                            frac_distance(&vals[a])
                                .partial_cmp(&frac_distance(&vals[b]))
                                .unwrap_or(std::cmp::Ordering::Equal)
                        }),
                };
                // An INTEGRAL relaxation optimum strictly better than `z` is a
                // feasible model point that beats the claimed optimum — the verdict
                // being certified is wrong. Emit nothing; never paper over it.
                let Some(j) = frac else {
                    return self.raise(OptTreeDecline::ValueRefuted);
                };
                let Some(floor) = exact_f64(&vals[j].floor()) else {
                    return self.raise(OptTreeDecline::InexactCut);
                };
                self.split_at(work, j, floor, leaves, depth)
            }
        }
    }

    /// Split column `c` at the integer `floor` and certify both children.
    ///
    /// The cut must round-trip through `f64` exactly: the deriver walks its working
    /// box in `f64` while the VERIFIER reconstructs it from the exact rational cut,
    /// and a cut that does not round-trip would put the two in different places.
    /// `exact_f64` is that guard, and failing it returns `None` rather than a tree
    /// whose leaves are priced somewhere the checker will not look.
    fn split_at(
        &self,
        work: &mut Model,
        c: usize,
        floor: f64,
        leaves: &mut usize,
        depth: usize,
    ) -> Option<OptTreeNode> {
        let Some(cut_r) = BigRational::from_float(floor) else {
            return self.raise(OptTreeDecline::InexactCut);
        };
        if !cut_r.is_integer() || exact_f64(&cut_r) != Some(floor) {
            return self.raise(OptTreeDecline::InexactCut);
        }
        let (lb0, ub0) = work.col_bounds(Col(c as u32));
        let lo = self.descend(work, c, lb0, ub0.min(floor), leaves, depth)?;
        let hi = self.descend(work, c, lb0.max(floor + 1.0), ub0, leaves, depth)?;
        Some(OptTreeNode::Split {
            col: Col(c as u32),
            cut: cut_r,
            lo: Box::new(lo),
            hi: Box::new(hi),
        })
    }

    /// One branch: apply the branch box `[lo, hi]` to column `c` of `work`,
    /// build the child, restore the box.
    fn descend(
        &self,
        work: &mut Model,
        c: usize,
        lo: f64,
        hi: f64,
        leaves: &mut usize,
        depth: usize,
    ) -> Option<OptTreeNode> {
        let (lb0, ub0) = work.col_bounds(Col(c as u32));
        work.set_col_bounds(Col(c as u32), lo, hi);
        let out = self.node(work, leaves, depth + 1);
        work.set_col_bounds(Col(c as u32), lb0, ub0);
        out
    }
}

/// The two-multiplier Farkas for an empty box on column `c`:
/// `1·(x_c − lb) + 1·(ub − x_c) = ub − lb < 0`.
///
/// Verified against `model` at the leaf's box before it is returned, exactly
/// like every other leaf: an empty box is only trivially contradictory when
/// BOTH sides are finite, and the shared verifier is what establishes that
/// rather than a comment.
fn trivial_empty_leaf(
    model: &Model,
    work: &Model,
    c: usize,
    leaves: &mut usize,
    budget: &OptimalityTreeBudget,
) -> Option<OptTreeNode> {
    let farkas = FarkasCertificate {
        multipliers: vec![
            Multiplier {
                fact: FactRef::ColBound {
                    col: Col(c as u32),
                    side: BoundSide::Lower,
                },
                coeff: BigRational::one(),
            },
            Multiplier {
                fact: FactRef::ColBound {
                    col: Col(c as u32),
                    side: BoundSide::Upper,
                },
                coeff: BigRational::one(),
            },
        ],
    };
    let (lb, ub) = exact_box(work);
    farkas.verify_with_col_bounds(model, &lb, &ub).ok()?;
    *leaves += 1;
    if *leaves > budget.leaf_cap {
        return None;
    }
    Some(OptTreeNode::Empty { farkas })
}

/// How far a rational sits from the nearest integer, as `f64` in `[0, 0.5]`.
/// Advice for the most-infeasible split rule; rounding it cannot cost validity
/// because the split it feeds records an exact integer cut either way.
fn frac_distance(v: &BigRational) -> f64 {
    let f = v.to_f64().unwrap_or(0.0);
    (f - f.round()).abs()
}

/// A rational as an EXACTLY-representable `f64`, within the range where
/// `f + 1.0` is also exact. `None` otherwise (fail closed).
fn exact_f64(r: &BigRational) -> Option<f64> {
    let f = r.to_f64()?;
    if !f.is_finite() || f.abs() > MAX_EXACT_INT {
        return None;
    }
    (&BigRational::from_float(f)? == r).then_some(f)
}
