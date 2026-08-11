// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-tree MILP infeasibility certificates (the P2
//! `MilpInfeasibilityCertificate` lane).
//!
//! A branch-and-bound proof of MILP infeasibility is a CASE SPLIT: the root
//! domain is recursively divided on integer columns, and every leaf's LP
//! relaxation (under that leaf's accumulated bound tightenings) is empty.
//! [`MilpInfeasibilityCertificate`] is that proof as data — a structural
//! split tree with one exact [`FarkasCertificate`] per leaf — checkable by
//! [`MilpInfeasibilityCertificate::verify`] against the model alone, in exact
//! rational arithmetic, with no solver state. This closes the gap named in
//! [`crate::Outcome::Infeasible`]: a case-split UNSAT used to rest on the
//! engine's own tree without exported evidence.
//!
//! ## Coverage is by construction
//!
//! A split records only `(col, cut)` with `cut ∈ ℤ` and `col` an integral
//! column: the lo branch asserts `x_col <= cut`, the hi branch asserts
//! `x_col >= cut + 1`. Every model-feasible point has `x_col ∈ ℤ`, and every
//! integer is `<= cut` or `>= cut + 1`, so the two branches cover the
//! parent's domain with NO reliance on any recorded box bounds — there is no
//! gap for `verify` to miss, only the two validations it performs (the column
//! is integral in the model; the cut is an integer). Induction from the
//! leaves then proves the root's domain — the model's own — empty:
//!
//! - **Leaf**: the Farkas combination over the model's rows and the leaf's
//!   effective column bounds (model bounds intersected with the branch
//!   tightenings, all exact) is `0·x >= positive` — no point satisfies the
//!   model plus this branch.
//! - **Split**: a model-feasible point under the accumulated tightenings
//!   would land in the lo or hi branch (coverage), both already empty.
//!
//! ## Frame convention: the CALLER's model
//!
//! Like the root-LP Farkas enrichment in [`crate::BabSession::check`], leaf
//! evidence is DERIVED against the caller's model (plus branch tightenings),
//! never against the engine's presolved/cut-strengthened internal model — so
//! the certificate verifies in the frame the consumer holds, exactly as
//! root certificates do today. The search's own fathoming may lean on
//! presolve-tightened bounds or root cuts that do not exist in the caller's
//! frame; a leaf whose caller-frame relaxation is NOT empty is finished by a
//! bounded exact sub-split (each side strictly smaller), and if the leaf
//! budget or deadline runs out the whole capture fails closed to `None` —
//! the verdict is never affected, only its evidence.

use std::time::{Duration, Instant};

use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::cert::{BoundSide, CertificateError, FactRef, FarkasCertificate, Multiplier};
use crate::exact::{Budget, ExactLp, LpFeasibility};
use crate::model::{exact, Col, ColKind, Model, Row, Sense};
use crate::simplex::{FloatLp, NbBound, SimplexStatus};

/// The shared caller-frame float lane for leaf derivation: one lowered LP for
/// the whole finalize walk, plus the previous leaf's basis as a warm hint —
/// DFS-adjacent leaves differ by a handful of branch bounds, so each re-solve
/// can be a short dual repair instead of a cold phase-I solve.
struct FloatCtx {
    lp: FloatLp,
    warm: std::cell::RefCell<Option<(Vec<usize>, Vec<NbBound>)>>,
}

/// Finalize diagnostics (trace-only; `AY_MILP_TRACE`). Which lane certified
/// each leaf, how the float lane declined when it did, and how the
/// size-preference lane (see [`compact_leaf`]) fared.
mod fstats {
    use std::sync::atomic::AtomicUsize;
    pub(super) static FLOAT_OK: AtomicUsize = AtomicUsize::new(0);
    pub(super) static FLOAT_STATUS: AtomicUsize = AtomicUsize::new(0);
    pub(super) static FLOAT_VERIFY: AtomicUsize = AtomicUsize::new(0);
    pub(super) static EXACT_OK: AtomicUsize = AtomicUsize::new(0);
    pub(super) static EXACT_FAIL: AtomicUsize = AtomicUsize::new(0);
    /// Leaves where the rim's second opinion was strictly smaller and won.
    pub(super) static COMPACT_OK: AtomicUsize = AtomicUsize::new(0);
    /// Leaves offered to the rim where the float proposal was kept anyway
    /// (the rim declined inside its slice, or did not come out smaller).
    pub(super) static COMPACT_MISS: AtomicUsize = AtomicUsize::new(0);
    /// Leaves whose float proposal was already compact enough to skip the offer.
    pub(super) static COMPACT_SKIP: AtomicUsize = AtomicUsize::new(0);
}

/// One node of the split tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TreeNode {
    /// A case split on an integral column: `lo` covers `x_col <= cut`, `hi`
    /// covers `x_col >= cut + 1`. `cut` must be an integer — the two branches
    /// then cover the parent's integer domain by construction.
    Split {
        /// The integral column being split.
        col: Col,
        /// The integer split point.
        cut: BigRational,
        /// The `x_col <= cut` branch.
        lo: Box<TreeNode>,
        /// The `x_col >= cut + 1` branch.
        hi: Box<TreeNode>,
    },
    /// A fathomed leaf: exact evidence that the model, under this branch's
    /// accumulated bound tightenings, admits no point at all.
    Leaf {
        /// The Farkas witness, priced at the leaf's effective column bounds.
        farkas: FarkasCertificate,
    },
}

/// An exact, independently checkable witness that a MILP is infeasible via
/// case split: the branch skeleton plus a Farkas certificate per leaf.
///
/// Verification consults only `model` and this value — the same "evidence is
/// data" contract as [`FarkasCertificate`]. A verified certificate proves the
/// MODEL infeasible (integrality included), not merely its LP relaxation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MilpInfeasibilityCertificate {
    /// The root of the split tree.
    pub root: TreeNode,
}

impl MilpInfeasibilityCertificate {
    /// Independently verify this certificate against `model` using exact
    /// arithmetic. No solver state is consulted.
    ///
    /// Walks the tree from the model's own domain, checking at each split
    /// that the column is integral in `model` and the cut is an integer
    /// (which makes the two branches cover the parent's integer domain by
    /// construction), and at each leaf that the Farkas certificate holds
    /// under that leaf's accumulated bound tightenings. ANY failure is an
    /// error; `Ok` means the model has no feasible point.
    pub fn verify(&self, model: &Model) -> Result<(), CertificateError> {
        let n = model.num_cols();
        // Effective column bounds, exact; `None` = that side is infinite.
        let mut lb: Vec<Option<BigRational>> = (0..n)
            .map(|j| exact(model.col_bounds(Col(j as u32)).0))
            .collect();
        let mut ub: Vec<Option<BigRational>> = (0..n)
            .map(|j| exact(model.col_bounds(Col(j as u32)).1))
            .collect();

        // Explicit work stack (a certificate is input data; recursion depth
        // must not be its caller's stack limit). `Tighten` snapshots the
        // touched bound onto `undo`; the matching `Restore` pops it.
        enum Step<'a> {
            Visit(&'a TreeNode),
            Tighten {
                col: usize,
                upper: bool,
                to: BigRational,
                child: &'a TreeNode,
            },
            Restore {
                col: usize,
                upper: bool,
            },
        }
        let mut undo: Vec<Option<BigRational>> = Vec::new();
        let mut stack: Vec<Step<'_>> = vec![Step::Visit(&self.root)];
        let mut splits = 0usize;
        let mut leaves = 0usize;
        while let Some(step) = stack.pop() {
            match step {
                Step::Visit(TreeNode::Leaf { farkas }) => {
                    let index = leaves;
                    leaves += 1;
                    farkas
                        .verify_with_col_bounds(model, &lb, &ub)
                        .map_err(|error| CertificateError::LeafRejected {
                            index,
                            error: Box::new(error),
                        })?;
                }
                Step::Visit(TreeNode::Split { col, cut, lo, hi }) => {
                    let index = splits;
                    splits += 1;
                    let c = col.index();
                    // Coverage license: only an INTEGRAL column split at an
                    // INTEGER leaves no point between the branches. A future
                    // non-integral kind must not silently pass, so the kinds
                    // are whitelisted, not blacklisted.
                    let integral =
                        c < n && matches!(model.col_kind(*col), ColKind::Binary | ColKind::Integer);
                    if !integral || !cut.is_integer() {
                        return Err(CertificateError::InvalidSplit { index, col: c });
                    }
                    // LIFO: the lo branch's frames go on top.
                    stack.push(Step::Restore {
                        col: c,
                        upper: false,
                    });
                    stack.push(Step::Tighten {
                        col: c,
                        upper: false,
                        to: cut.clone() + BigRational::one(),
                        child: hi,
                    });
                    stack.push(Step::Restore {
                        col: c,
                        upper: true,
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
                    undo.push(slot.clone());
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
                    stack.push(Step::Visit(child));
                }
                Step::Restore { col, upper } => {
                    let prev = undo.pop().expect("balanced undo stack");
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

    /// The number of leaves in the tree (diagnostics; verification cost is
    /// linear in this).
    #[must_use]
    pub fn num_leaves(&self) -> usize {
        let mut stack = vec![&self.root];
        let mut leaves = 0usize;
        while let Some(node) = stack.pop() {
            match node {
                TreeNode::Leaf { .. } => leaves += 1,
                TreeNode::Split { lo, hi, .. } => {
                    stack.push(lo);
                    stack.push(hi);
                }
            }
        }
        leaves
    }
}

// ---------------------------------------------------------------------------
// Capture: the emission side, driven by the branch-and-bound in `crate::bab`.
// ---------------------------------------------------------------------------

/// The sentinel for a search node the capture is not tracking.
pub(crate) const UNTRACKED: u32 = u32::MAX;

/// Cuts (and `cut + 1`) must convert exactly between `f64` and rationals.
/// Branch cuts are floors of in-box LP values, so this never binds in
/// practice; it is the guard that makes the conversions provably lossless.
const MAX_EXACT_INT: f64 = 4_503_599_627_370_496.0; // 2^52

#[derive(Clone)]
enum CapNode {
    /// Pushed but not yet resolved.
    Open,
    /// Branched: `lo` claims `x_col <= cut`, `hi` claims `x_col >= cut + 1`.
    Split {
        col: u32,
        cut: f64,
        lo: u32,
        hi: u32,
    },
    /// Fathomed empty (by any exact mechanism); caller-frame evidence is
    /// derived at [`TreeCapture::finalize`].
    Closed,
}

/// Records the branch skeleton of one `solve_milp_in` search so that an
/// `Infeasible` verdict can export a [`MilpInfeasibilityCertificate`].
///
/// FAIL-CLOSED THROUGHOUT: any bookkeeping hole, cap overrun, non-integer
/// cut, restart inconsistency, or underivable leaf poisons the capture —
/// `finalize` then returns `None` and the verdict is exactly what it was
/// before this lane existed. Recording is O(1) per branch/fathom; the only
/// real cost (one exact LP feasibility solve per leaf, in the caller's
/// frame) is paid inside `finalize`, i.e. only on an actual `Infeasible`
/// outcome, under the caller's own deadline.
#[derive(Clone)]
pub(crate) struct TreeCapture {
    active: bool,
    nodes: Vec<CapNode>,
    closed: usize,
    leaf_cap: usize,
}

impl TreeCapture {
    /// A capture with `leaf_cap` leaves of budget; `0` disables entirely.
    pub(crate) fn new(leaf_cap: usize) -> Self {
        let active = leaf_cap > 0;
        Self {
            active,
            nodes: if active {
                vec![CapNode::Open]
            } else {
                Vec::new()
            },
            closed: 0,
            leaf_cap,
        }
    }

    /// Whether capture is live (armed and not yet poisoned). Used by the
    /// search to decide whether to carve the #p2-finalize-reserve out of the
    /// caller deadline — a disabled/poisoned capture must not cost the search
    /// any budget.
    pub(crate) fn is_armed(&self) -> bool {
        self.active
    }

    /// The root's tracking id for the search's initial node.
    pub(crate) fn root(&self) -> u32 {
        if self.active {
            0
        } else {
            UNTRACKED
        }
    }

    /// Drop everything and stop tracking (the fail-closed exit).
    pub(crate) fn poison(&mut self) {
        self.active = false;
        self.nodes = Vec::new();
        self.closed = 0;
    }

    /// A primal restart re-roots the search and the new tree re-covers the
    /// whole domain, so the capture starts over with it.
    pub(crate) fn reset(&mut self) {
        if self.active {
            self.nodes = vec![CapNode::Open];
            self.closed = 0;
        }
    }

    /// Record a branch of tracked node `parent` on column `col` at integer
    /// `cut` (lo child: `x <= cut`; hi child: `x >= cut + 1`). Returns the
    /// children's tracking ids, or `(UNTRACKED, UNTRACKED)` once inactive.
    pub(crate) fn split(&mut self, parent: u32, col: usize, cut: f64) -> (u32, u32) {
        if !self.active {
            return (UNTRACKED, UNTRACKED);
        }
        // A completed tree with `<= leaf_cap` leaves has `<= 2·leaf_cap - 1`
        // nodes; growing past that can never finalize, so stop paying for it.
        let arena_cap = 2 * self.leaf_cap + 1;
        let ok = parent != UNTRACKED
            && (parent as usize) < self.nodes.len()
            && matches!(self.nodes[parent as usize], CapNode::Open)
            && cut.is_finite()
            && cut == cut.trunc()
            && cut.abs() <= MAX_EXACT_INT
            && self.nodes.len() + 2 <= arena_cap;
        if !ok {
            self.poison();
            return (UNTRACKED, UNTRACKED);
        }
        let lo = self.nodes.len() as u32;
        let hi = lo + 1;
        self.nodes.push(CapNode::Open);
        self.nodes.push(CapNode::Open);
        self.nodes[parent as usize] = CapNode::Split {
            col: col as u32,
            cut,
            lo,
            hi,
        };
        (lo, hi)
    }

    /// Record that tracked node `id` was fathomed as exactly empty.
    pub(crate) fn close(&mut self, id: u32) {
        if !self.active {
            return;
        }
        let ok = id != UNTRACKED
            && (id as usize) < self.nodes.len()
            && matches!(self.nodes[id as usize], CapNode::Open);
        if !ok {
            // A fathom the capture cannot place is a bookkeeping hole; the
            // tree would be missing a region. Fail closed.
            self.poison();
            return;
        }
        self.nodes[id as usize] = CapNode::Closed;
        self.closed += 1;
        if self.closed > self.leaf_cap {
            self.poison();
        }
    }

    /// Seal a quiescent interrupted tree and try to prove the ORIGINAL margin
    /// model infeasible over every region it still covers.
    ///
    /// The rigorous global bound is not evidence. Every `Open` leaf becomes a
    /// replay obligation, and [`Self::finalize`] independently derives exact
    /// caller-frame Farkas evidence. The only exported object is the ordinary
    /// replay-verified [`MilpInfeasibilityCertificate`].
    ///
    /// Quiescence is a caller invariant. Capture poisoning, too many terminal
    /// leaves, a replay deadline, a feasible leaf, or malformed coverage
    /// returns `None` and permanently disarms this capture.
    pub(crate) fn finalize_margin_cover(
        &mut self,
        model: &Model,
        deadline: Option<Instant>,
    ) -> Option<MilpInfeasibilityCertificate> {
        if !self.active || self.nodes.is_empty() {
            return None;
        }
        let terminal_leaves = self
            .nodes
            .iter()
            .filter(|node| matches!(node, CapNode::Open | CapNode::Closed))
            .count();
        if terminal_leaves == 0 || terminal_leaves > self.leaf_cap {
            self.poison();
            return None;
        }

        // Consume the one proof opportunity without moving the variable: an
        // interrupted caller still constructs its ordinary fail-closed
        // Bound/Feasible/Unknown fallback when replay declines.
        let nodes = std::mem::take(&mut self.nodes);
        self.active = false;
        self.closed = 0;
        let mut sealed = Self {
            active: true,
            nodes,
            closed: terminal_leaves,
            leaf_cap: self.leaf_cap,
        };
        for node in &mut sealed.nodes {
            if matches!(node, CapNode::Open) {
                *node = CapNode::Closed;
            }
        }
        // `None` rim slice: the marked-margin replay keeps its historical
        // whole-slice-per-leaf behaviour byte-identically. Its deadline is
        // already the proof slice it was explicitly granted, not a leftover.
        sealed.finalize(model, deadline, None)
    }

    /// Non-consuming marked-margin replay for a live search boundary.
    ///
    /// The clone owns the entire sealing/finalization attempt. Whether replay
    /// succeeds or fails, the real capture remains byte-for-byte available for
    /// continued refinement and a later terminal finalize. A returned
    /// certificate has passed the same original-model production verifier as
    /// [`Self::finalize_margin_cover`].
    pub(crate) fn preview_margin_cover(
        &self,
        model: &Model,
        deadline: Option<Instant>,
    ) -> Option<MilpInfeasibilityCertificate> {
        let mut preview = self.clone();
        preview.finalize_margin_cover(model, deadline)
    }

    /// Build the exportable certificate in the CALLER's frame, or `None`.
    ///
    /// Walks the recorded skeleton over a working copy of `model` (the
    /// caller's model, NOT the engine's presolved/cut model), deriving each
    /// leaf's Farkas evidence with the exact rim under that leaf's branch
    /// bounds. A leaf whose caller-frame relaxation is not empty (the search
    /// fathomed it with presolve-tightened bounds or root cuts the caller's
    /// frame lacks) is finished by a bounded exact sub-split. Every failure —
    /// deadline, leaf budget, an unresolved node, a rim decline — returns
    /// `None`. The final certificate is re-verified against `model` before it
    /// is handed out; an unverifiable certificate is never emitted.
    pub(crate) fn finalize(
        self,
        model: &Model,
        deadline: Option<Instant>,
        rim_slice: Option<Duration>,
    ) -> Option<MilpInfeasibilityCertificate> {
        if !self.active || self.nodes.is_empty() {
            return None;
        }
        let mut work = model.clone();
        let mut leaves_used = 0usize;
        // FLOAT-FIRST LEAF EVIDENCE: one caller-frame float LP, shared by every
        // leaf. Running a full exact-rational simplex from scratch per leaf can
        // make finalization dominate the search. The float lane proposes each
        // leaf solution, its
        // phase-I ray is exactified into a Farkas certificate, and the exact
        // verification of that certificate (O(nnz) rational work) is the ONLY
        // arithmetic the evidence rests on — the float is advice, the rim is
        // authority, exactly the crate's contract. Any decline (wrong status,
        // unverifiable ray, unrepresentable model) falls through to the exact
        // rim unchanged.
        let fctx = FloatLp::from_model(model, &[], Sense::Minimize).map(|lp| FloatCtx {
            lp,
            warm: std::cell::RefCell::new(None),
        });
        let t0 = Instant::now();
        let budget = FinalizeBudget {
            deadline,
            rim_slice,
            captured_leaves: self.closed,
            t0,
            baseline: std::cell::Cell::new(None),
            float_spent: std::cell::Cell::new(Duration::ZERO),
            compaction_spent: std::cell::Cell::new(Duration::ZERO),
            compaction_strikes: std::cell::Cell::new(0),
            compaction_off: std::cell::Cell::new(false),
        };
        let root = build_node(
            &self.nodes,
            0,
            &mut work,
            fctx.as_ref(),
            &mut leaves_used,
            self.leaf_cap,
            &budget,
        );
        if std::env::var_os("AY_MILP_TRACE").is_some() {
            use std::sync::atomic::Ordering::Relaxed;
            eprintln!(
                "AY_MILP_TRACE FINALIZE {} in {:.2}s: leaves={} float_ok={} float_status={} float_verify={} exact_ok={} exact_fail={}",
                if root.is_some() { "ok" } else { "FAILED" },
                t0.elapsed().as_secs_f64(),
                leaves_used,
                fstats::FLOAT_OK.load(Relaxed),
                fstats::FLOAT_STATUS.load(Relaxed),
                fstats::FLOAT_VERIFY.load(Relaxed),
                fstats::EXACT_OK.load(Relaxed),
                fstats::EXACT_FAIL.load(Relaxed),
            );
            eprintln!(
                "AY_MILP_TRACE COMPACT ok={} miss={} skip={} off={} float={:.2}s compaction={:.2}s",
                fstats::COMPACT_OK.load(Relaxed),
                fstats::COMPACT_MISS.load(Relaxed),
                fstats::COMPACT_SKIP.load(Relaxed),
                u8::from(budget.compaction_off.get()),
                budget.float_spent.get().as_secs_f64(),
                budget.compaction_spent.get().as_secs_f64(),
            );
        }
        let cert = MilpInfeasibilityCertificate { root: root? };
        // Emission is fail-closed: the certificate must convince the same
        // independent checker the consumer will run, or it does not ship.
        cert.verify(model).ok()?;
        Some(cert)
    }
}

/// Expired-deadline test (finalize runs strictly inside the solve's budget).
fn expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}

/// The wall policy the caller-frame leaf walk runs under.
///
/// # Why the cap moved INSIDE the walk
///
/// [`TreeCapture::finalize`] used to be handed a single pre-computed instant —
/// `min(caller deadline, now + finalize_reserve)`, and the reserve is clamped
/// to 5 s. That outer cap could only see the CLOCK. It could not see how many
/// leaves the capture holds, how fast they are coming, or whether the one leaf
/// currently in the exact rim is the hopeless one — so it answered every
/// question with the same 5 s, and got two different cases wrong in opposite
/// directions:
///
/// * **misc05inf** (the case the cap was written for): 7 nodes, one exact-rim
///   solve that was never going to close. Uncapped, finalize burned 29.72 s of
///   a 30 s budget and returned nothing.
/// * **the downstream optimization consumer's captured W1 corpus** (measured 2026-07-31, `--time-limit 120`,
///   `--tree-cert-leaves 65536`): `W1_unsat_v16_c39_000008` holds a 244-leaf
///   tree that finalizes SUCCESSFULLY in 41.3 s — 116 of its leaves need the
///   exact rim because the float ray does not exactify. The 5 s cap cut it off
///   at leaf 11 and the verdict shipped `evidence infeasible NONE`. The
///   certificate was affordable; the cap simply could not tell.
///
/// Two purpose-built predicates replace the one blunt number, and each targets
/// exactly one of those cases:
///
/// * `rim_slice` bounds ONE exact-rim leaf. A hopeless rim solve now costs at
///   most what the WHOLE finalize cost before, so misc05inf is unchanged.
/// * [`Self::hopeless`] abandons a walk whose observed leaf rate projects past
///   the caller's deadline. `W1_unsat_v16_c39_000000` (a ~7 900-leaf tree that
///   reached only 407 leaves in 115 s of uncapped finalize) is abandoned at its
///   FIRST judgement, 32 leaves in: measured 8.0 s against the old flat cap's
///   5.0 s. That 3 s is the whole price of the change on a hopeless tree, and
///   it buys the ability to keep going on one that is not.
///
/// The hard stop is the CALLER's own deadline and nothing shorter: once the
/// verdict is settled there is nothing else left to spend that budget on, and
/// the certificate is the deliverable.
///
/// FAIL-CLOSED IS UNTOUCHED. Every predicate here can only make the walk stop
/// EARLIER, and stopping early returns `None` — `tree_cert: None`, the verdict
/// exactly as it was. Neither predicate can admit a leaf, weaken a check, or
/// change what `finalize` re-verifies before it hands the certificate out.
struct FinalizeBudget {
    /// The hard stop: the caller's own deadline. `None` = unbounded, exactly
    /// as an unlimited solve has always been.
    deadline: Option<Instant>,
    /// The slice ONE exact-rim leaf solve may take. `None` = the whole
    /// remaining walk (the historical behaviour, kept for the margin lane).
    rim_slice: Option<Duration>,
    /// Terminal leaves the capture recorded — the walk's denominator. Leaf
    /// sub-splits can push the true count HIGHER, which only makes the
    /// projection more optimistic, i.e. less likely to abandon.
    captured_leaves: usize,
    /// When the walk started.
    t0: Instant,
    /// `(leaves, elapsed)` at the end of the warm-up, latched once by
    /// [`Self::hopeless`]. The projection is taken from the MARGINAL rate
    /// after this point, never from the average since `t0` — see the constant
    /// below for the measurement that forced the distinction.
    baseline: std::cell::Cell<Option<(usize, Duration)>>,
    /// Wall the FLOAT lane has spent so far. The compaction allowance is scaled
    /// off it (see [`Self::compaction_slice`]) so a long walk earns a
    /// proportionally longer one and a short walk cannot be dominated by it.
    float_spent: std::cell::Cell<Duration>,
    /// Wall the COMPACTION lane has spent so far.
    compaction_spent: std::cell::Cell<Duration>,
    /// CONSECUTIVE compaction offers that did not produce a smaller
    /// certificate. Reset by any adoption.
    compaction_strikes: std::cell::Cell<u32>,
    /// Latched: the compaction lane is closed for the rest of this walk.
    compaction_off: std::cell::Cell<bool>,
}

/// Leaves of WARM-UP, and then again of SAMPLE, before
/// [`FinalizeBudget::hopeless`] will act on its own rate estimate.
///
/// The average-since-start rate is badly biased early and the bias is not
/// small: on `W1_unsat_v16_c39_000008` the first 16 leaves cost 7.53 s
/// (0.47 s/leaf — the float LP's cold factorization, and the exact rim's first
/// cold solves) against 0.17 s/leaf over the full 244-leaf walk that finalizes
/// in 41.3 s. Projecting from the average abandoned a certificate that fits
/// the budget with room to spare. Projecting from the marginal rate measured
/// AFTER the warm-up does not.
const HOPELESS_MIN_SAMPLE: usize = 16;

/// How far past the remaining wall a projection must land before the walk is
/// abandoned.
///
/// Even the marginal rate is biased HIGH early, and for a structural reason:
/// the exact rim is the expensive lane and it is front-loaded — the float
/// warm-basis chain gets better as the DFS walk proceeds, so later leaves are
/// disproportionately float-derived. MEASURED on `W1_unsat_v16_c39_000008`:
/// 0.24 s/leaf marginal at leaf 41 (17 float / 24 rim) against 0.17 s/leaf
/// over the completed 244-leaf walk (128 float / 116 rim). Abandoning on a
/// bare `projected > remaining` therefore throws away certificates that fit.
///
/// A factor of 2 covers that bias and still catches the class this predicate
/// exists for by an order of magnitude: on `W1_unsat_v16_c39_000000` (a ~7 900-leaf
/// tree whose uncapped finalize reached 407 leaves in 115 s) the first judgement
/// lands at 32 leaves and projects ~2 000 s of leaf work against ~107 s of
/// remaining wall — abandoned by roughly 9x even after the margin.
const HOPELESS_MARGIN: u32 = 2;

/// The compaction lane's allowance BEFORE the float lane has spent anything —
/// the warm-up that lets a small tree be compacted at all.
///
/// The allowance is divided among the leaves still to come, so it is this
/// number, not any per-leaf constant, that decides whether a given tree gets
/// compacted. MEASURED slice against MEASURED rim cost, at 120 s:
///
/// | model                    | leaves | slice   | one rim | offer |
/// |--------------------------|--------|---------|---------|-------|
/// | `g503inf`                |      2 | 500 ms  | ~5 ms   | taken |
/// | `W1_sat_v16_c39_000008`  |      1 | 1000 ms | ~70 ms  | taken |
/// | `W1_unsat_v9_c14_000008` |      8 | 125 ms  | ~27 ms  | taken |
/// | `flugplinf`              |  2 542 | 0.39 ms | ~0.16 ms| taken |
/// | `W1_unsat_v30_c38_000008`|  1 928 | 0.52 ms | ~2.1 s  | struck|
/// | `W1_unsat_v25_c45_000008`| 25 398 | 0.04 ms | ~1.45 s | struck|
///
/// One second separates the two classes by three orders of magnitude in both
/// directions, which is why no tuning finer than "one second" is warranted.
const COMPACTION_WARMUP: Duration = Duration::from_secs(1);

/// On top of the warm-up, the compaction lane may spend this multiple of what
/// the FLOAT lane has already spent. A walk long enough to need more allowance
/// has, by construction, earned it — and the ratio bounds the whole lane at
/// "finalize costs at most twice what it costs without me".
const COMPACTION_FLOAT_SHARE: u32 = 1;

/// …and, when the caller set a deadline, never more than this fraction of the
/// wall that is left. Compaction buys SIZE, never coverage, so it must not be
/// able to talk the walk into missing the deadline it needs to finish at all.
const COMPACTION_WALL_DIVISOR: u32 = 4;

/// Consecutive offers that fail to produce a smaller certificate before the
/// lane latches off for the rest of the walk.
///
/// A certificate's size is the SUM over its leaves, so compacting a handful of
/// leaves out of thousands buys nothing measurable while costing real wall.
/// Three strikes is enough to tell "this model's rim is too slow / no smaller"
/// from one unlucky leaf, and caps the wasted wall at three slices.
const COMPACTION_STRIKES: u32 = 3;

/// Denominator width, in BITS, above which a leaf's float-lane proposal is
/// offered to the exact rim for a second opinion.
///
/// This is the measured signature of the exactified-float lane. A phase-I ray
/// is a rounded real vector, so exactifying it — and, since the free-column
/// elimination landed, pivoting on it — produces 53-bit dyadic multipliers:
/// `2514297896833393/70368744177664`. The rim's own pivot sequence produces
/// small rationals: `75733/1510`. MEASURED denominator bits per multiplier on
/// real leaves of the same models (median / p90):
///
/// | leaves                          | median | p90 |
/// |---------------------------------|--------|-----|
/// | `g503inf`, exact rim            |      7 |  11 |
/// | `W1_sat_v16_c39_000008`, rim    |      2 |  21 |
/// | `g503inf`, exactified float     |     54 |  60 |
/// | `stein15inf`, exactified float  |     53 | 102 |
///
/// 32 bits sits in the empty band between them, so the test costs one
/// `bits()` call per multiplier and never fires on a leaf the rim could not
/// improve on.
const COMPACT_DENOM_BITS: u64 = 32;

impl FinalizeBudget {
    fn expired(&self) -> bool {
        expired(self.deadline)
    }

    /// The deadline for ONE exact-rim leaf: the caller's deadline, further
    /// shortened by `rim_slice` when one is set.
    fn rim_deadline(&self) -> Option<Instant> {
        let slice = self.rim_slice.and_then(|s| Instant::now().checked_add(s));
        match (self.deadline, slice) {
            (Some(d), Some(s)) => Some(d.min(s)),
            (d, None) => d,
            (None, s) => s,
        }
    }

    /// Charge the float lane's wall. Its total is the scale the compaction
    /// allowance grows against.
    fn charge_float(&self, spent: Duration) {
        self.float_spent.set(self.float_spent.get() + spent);
    }

    /// Charge one compaction offer, and latch the lane off after
    /// [`COMPACTION_STRIKES`] consecutive offers that bought nothing.
    fn charge_compaction(&self, spent: Duration, adopted: bool) {
        self.compaction_spent
            .set(self.compaction_spent.get() + spent);
        if adopted {
            self.compaction_strikes.set(0);
            return;
        }
        let strikes = self.compaction_strikes.get() + 1;
        self.compaction_strikes.set(strikes);
        if strikes >= COMPACTION_STRIKES {
            self.compaction_off.set(true);
        }
    }

    /// The deadline for ONE compaction offer, or `None` to decline the offer.
    ///
    /// # Why the slice is a FAIR SHARE and not a constant
    ///
    /// The lane exists because the exact rim emits compact multipliers where
    /// the exactified float lane emits enormous ones — MEASURED on `g503inf`,
    /// 24 multipliers of median denominator 2^7 against 64 of median 2^54, a
    /// 5.2x difference in wire bytes (584 -> 2 972 per leaf). It is worth
    /// paying for only when it can be paid for on the WHOLE tree, so the
    /// allowance is divided by the leaves still to come. A rim that cannot
    /// close inside its own share of the allowance is, by that arithmetic,
    /// one the tree cannot afford — it runs out its slice, declines, and the
    /// already-verified float proposal stands.
    ///
    /// That single division replaces every per-model threshold: it is what
    /// separates `g503inf` (2 leaves, 500 ms each) from
    /// `W1_unsat_v25_c45_000008` (25 398 leaves, 40 us each) with no knowledge
    /// of either.
    fn compaction_slice(&self, leaves_done: usize) -> Option<Instant> {
        if self.compaction_off.get() {
            return None;
        }
        let mut allowance = COMPACTION_WARMUP + self.float_spent.get() * COMPACTION_FLOAT_SHARE;
        let now = Instant::now();
        if let Some(deadline) = self.deadline {
            allowance =
                allowance.min(deadline.saturating_duration_since(now) / COMPACTION_WALL_DIVISOR);
        }
        let Some(left) = allowance.checked_sub(self.compaction_spent.get()) else {
            self.compaction_off.set(true);
            return None;
        };
        // Leaves still to come, never zero: the LAST leaf is entitled to what
        // is left. Sub-splits can push the walk PAST `captured_leaves`, which
        // pins the divisor at 1 and hands those leaves the remaining
        // allowance — the total is still capped by `left`, so the worst case
        // is one generous offer, not an unbounded run of them.
        let ahead = u32::try_from(self.captured_leaves.saturating_sub(leaves_done).max(1))
            .unwrap_or(u32::MAX);
        let slice = left / ahead;
        if slice.is_zero() {
            return None;
        }
        // Never outlive the caller's deadline or the one-rim slice: an offer is
        // an ordinary exact-rim solve and answers to both.
        Some(match self.rim_deadline() {
            Some(rim) => rim.min(now.checked_add(slice)?),
            None => now.checked_add(slice)?,
        })
    }

    /// Is the rest of this walk unaffordable at the rate it is actually
    /// running? Conservative in the direction that matters: it declines to
    /// judge until it has a warm sample, it measures the MARGINAL rate rather
    /// than the warm-up-biased average, and a tree that fits under the old 5 s
    /// ceiling projects far inside a deadline that is now the caller's whole
    /// wall — so nothing that finalized before can be abandoned here.
    fn hopeless(&self, leaves_done: usize) -> bool {
        let Some(deadline) = self.deadline else {
            return false;
        };
        if leaves_done < HOPELESS_MIN_SAMPLE || self.captured_leaves <= leaves_done {
            return false;
        }
        let elapsed = self.t0.elapsed();
        let Some((base_leaves, base_elapsed)) = self.baseline.get() else {
            // End of warm-up: latch it and judge nothing yet.
            self.baseline.set(Some((leaves_done, elapsed)));
            return false;
        };
        let sample = leaves_done.saturating_sub(base_leaves);
        if sample < HOPELESS_MIN_SAMPLE {
            return false;
        }
        let remaining = u32::try_from(self.captured_leaves - leaves_done).unwrap_or(u32::MAX);
        let sampled = u32::try_from(sample).unwrap_or(u32::MAX);
        // A projection that overflows the clock is, by definition, hopeless.
        let Some(projected) = elapsed
            .saturating_sub(base_elapsed)
            .checked_div(sampled)
            .and_then(|per_leaf| per_leaf.checked_mul(remaining))
            .and_then(|cost| cost.checked_div(HOPELESS_MARGIN))
            .and_then(|p| Instant::now().checked_add(p))
        else {
            return true;
        };
        projected > deadline
    }
}

/// PROPOSE the caller-frame ROOT Farkas witness with the float LP, then prove
/// it exactly — the same float-first/rim-authority bargain every leaf inside
/// [`TreeCapture::finalize`] already strikes, applied to the root box.
///
/// # Why the root needed this too
///
/// [`crate::BabSession::check`]'s post-verdict enrichment reached for the
/// EXACT rim first (`ExactLp::make_feasible`) on a bare `Infeasible`, under a
/// bounded grace (`cert_budget_native`: `max(5 s, 15 % of the time limit)`).
/// A cold exact-rational phase A on a real model is not a 5-second operation,
/// so on anything past toy scale the grace expired and the verdict shipped
/// with `evidence infeasible NONE` even though a root Farkas witness EXISTED.
///
/// MEASURED on the downstream optimization consumer's real captured W1 workload (`ay-milp solve --emit-cert`
/// then `verify`, `--time-limit 60`), two models that PRESOLVE decides
/// infeasible with ZERO branch-and-bound nodes:
///
/// | model                    | rows x cols | exact-rim only        | float-first |
/// |--------------------------|-------------|-----------------------|-------------|
/// | `W1_sat_v83_c328_000008` | 1980 x 1567 | grace expired, NONE   | `SUCCINCT farkas`, 5.6 ms |
/// | `W1_sat_v91_c217_000008` | 1600 x 1290 | grace expired, NONE   | `SUCCINCT farkas`, 3.2 ms |
///
/// (Both DO have a root witness: with `AY_MILP_CERT_GRACE=0` the exact rim
/// finds one in 29.0 s and 16.4 s respectively. The evidence was never
/// missing — only unaffordable.)
///
/// # Why this cannot weaken the evidence
///
/// The float solve is ADVICE and contributes no arithmetic to the artifact.
/// Its phase-I ray is exactified into rational multipliers and the resulting
/// combination is re-verified against `model` by
/// [`exact_farkas_from_float_ray`] before it is returned — so a float that
/// lies produces `None`, never a bad certificate, and the caller's exact-rim
/// path is still there behind it. `BabSession::check`'s own `finish` gate then
/// verifies it a second time, independently.
pub(crate) fn root_float_farkas(
    model: &Model,
    deadline: Option<Instant>,
) -> Option<FarkasCertificate> {
    if expired(deadline) {
        return None;
    }
    let ctx = FloatCtx {
        lp: FloatLp::from_model(model, &[], Sense::Minimize)?,
        warm: std::cell::RefCell::new(None),
    };
    float_leaf_farkas(model, &ctx, deadline)
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

/// Rebuild the recorded arena node `id` as a certificate [`TreeNode`],
/// deriving leaf evidence against `work` (the caller's model with the branch
/// bounds applied; bounds are set on descent and restored on return).
fn build_node(
    arena: &[CapNode],
    id: u32,
    work: &mut Model,
    flp: Option<&FloatCtx>,
    leaves_used: &mut usize,
    leaf_cap: usize,
    budget: &FinalizeBudget,
) -> Option<TreeNode> {
    if budget.expired() {
        return None;
    }
    match arena.get(id as usize)? {
        // A node the search never resolved: the skeleton does not tile the
        // domain (this cannot happen on a genuine exhausted-tree Infeasible,
        // but the capture never assumes that).
        CapNode::Open => None,
        CapNode::Closed => derive_leaf(work, flp, leaves_used, leaf_cap, budget, 0),
        &CapNode::Split { col, cut, lo, hi } => {
            let c = col as usize;
            if c >= work.num_cols()
                || !matches!(work.col_kind(Col(col)), ColKind::Binary | ColKind::Integer)
            {
                return None;
            }
            let (lb0, ub0) = work.col_bounds(Col(col));
            // Both `cut` and `cut + 1.0` are exact (guarded at `split`).
            let lo_node = descend(
                arena,
                lo,
                work,
                flp,
                c,
                lb0,
                ub0.min(cut),
                leaves_used,
                leaf_cap,
                budget,
            )?;
            let hi_node = descend(
                arena,
                hi,
                work,
                flp,
                c,
                lb0.max(cut + 1.0),
                ub0,
                leaves_used,
                leaf_cap,
                budget,
            )?;
            Some(TreeNode::Split {
                col: Col(col),
                cut: BigRational::from_float(cut)?,
                lo: Box::new(lo_node),
                hi: Box::new(hi_node),
            })
        }
    }
}

/// One branch of [`build_node`]: apply the branch box `[lb, ub]` to column
/// `c` of `work`, build the child, restore the box. An empty branch box is a
/// trivially-empty leaf.
#[allow(clippy::too_many_arguments)]
fn descend(
    arena: &[CapNode],
    id: u32,
    work: &mut Model,
    flp: Option<&FloatCtx>,
    c: usize,
    lb: f64,
    ub: f64,
    leaves_used: &mut usize,
    leaf_cap: usize,
    budget: &FinalizeBudget,
) -> Option<TreeNode> {
    if lb > ub {
        // The branch box itself is empty: `x_c >= lb` and `x_c <= ub` with
        // `lb > ub` combine to the contradiction directly (both sides are
        // necessarily finite here). The recorded subtree below — if any — is
        // irrelevant; one leaf covers the branch.
        return trivial_empty_leaf(c, leaves_used, leaf_cap);
    }
    let (lb0, ub0) = work.col_bounds(Col(c as u32));
    work.set_col_bounds(Col(c as u32), lb, ub);
    let out = build_node(arena, id, work, flp, leaves_used, leaf_cap, budget);
    work.set_col_bounds(Col(c as u32), lb0, ub0);
    out
}

/// The two-multiplier Farkas for an empty box on column `c`:
/// `1·(x_c − lb) + 1·(ub − x_c) = ub − lb < 0`.
fn trivial_empty_leaf(c: usize, leaves_used: &mut usize, leaf_cap: usize) -> Option<TreeNode> {
    *leaves_used += 1;
    if *leaves_used > leaf_cap {
        return None;
    }
    Some(TreeNode::Leaf {
        farkas: FarkasCertificate {
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
        },
    })
}

/// Derive exact leaf evidence for the CURRENT box of `work`, extending with
/// further integer splits when the caller-frame relaxation is not yet empty
/// (the search's fathom may have leaned on presolve-tightened bounds or root
/// cuts that do not exist in this frame — each extension side is strictly
/// smaller, and the leaf budget/deadline bound the recursion).
fn derive_leaf(
    work: &mut Model,
    flp: Option<&FloatCtx>,
    leaves_used: &mut usize,
    leaf_cap: usize,
    budget: &FinalizeBudget,
    depth: usize,
) -> Option<TreeNode> {
    // AFFORDABILITY, checked before any work is done on this leaf: a walk whose
    // measured rate cannot reach the last captured leaf inside the caller's own
    // deadline is abandoned NOW rather than at the deadline. See
    // `FinalizeBudget::hopeless` for the two measured trees this separates.
    if budget.expired() || budget.hopeless(*leaves_used) || depth > leaf_cap {
        return None;
    }
    // An empty box needs no LP at all.
    for j in 0..work.num_cols() {
        let (lb, ub) = work.col_bounds(Col(j as u32));
        if lb > ub {
            return trivial_empty_leaf(j, leaves_used, leaf_cap);
        }
    }
    // Float-first: milliseconds of advice, one exact O(nnz) verification of
    // authority. Declines fall through to the exact rim below unchanged.
    if let Some(flp) = flp {
        let t = Instant::now();
        let attempt = float_leaf_farkas(work, flp, budget.deadline);
        budget.charge_float(t.elapsed());
        if let Some(farkas) = attempt {
            // SIZE-AWARE, not float-first-unconditionally: a bulky proposal is
            // offered to the rim, whose certificate ships if it is smaller.
            let farkas = compact_leaf(work, farkas, budget, *leaves_used);
            *leaves_used += 1;
            if *leaves_used > leaf_cap {
                return None;
            }
            return Some(TreeNode::Leaf { farkas });
        }
        if budget.expired() {
            return None;
        }
    }
    // ONE exact-rim leaf, on its OWN slice. The whole walk is bounded by the
    // caller's deadline; this additionally bounds the single solve that can
    // consume it — the misc05inf shape, where the rim was never going to close
    // and used to eat the entire finalize budget by itself.
    let rim_deadline = budget.rim_deadline();
    let rim_budget = Budget {
        deadline: rim_deadline,
        max_iters: Budget::default_iters(work.num_cols() + work.num_rows()),
    };
    let mut rim = ExactLp::new_within(work, rim_deadline)?;
    match rim.make_feasible(&rim_budget) {
        LpFeasibility::Infeasible(farkas) => {
            // The rim's own certificate, re-checked against the box it is
            // about to represent before it is adopted.
            farkas.verify(work).ok()?;
            *leaves_used += 1;
            if *leaves_used > leaf_cap {
                return None;
            }
            fstats::EXACT_OK.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Some(TreeNode::Leaf { farkas })
        }
        LpFeasibility::Unknown(_) => {
            fstats::EXACT_FAIL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            None
        }
        LpFeasibility::Feasible => {
            // Not LP-empty in the caller's frame: split further, exactly.
            let vals = rim.structural_values();
            drop(rim);
            let frac = (0..work.num_cols()).find(|&j| {
                matches!(
                    work.col_kind(Col(j as u32)),
                    ColKind::Binary | ColKind::Integer
                ) && !vals[j].is_integer()
            });
            // Integral relaxation point = a feasible MILP point: that would
            // contradict the verdict this capture is evidence FOR. Emit
            // nothing and leave the (uncertified) verdict to the engine's
            // own witness gates.
            let j = frac?;
            let cut_r = vals[j].floor();
            let cut = exact_f64(&cut_r)?;
            let (lb0, ub0) = work.col_bounds(Col(j as u32));
            let lo = descend_derived(
                work,
                flp,
                j,
                lb0,
                ub0.min(cut),
                leaves_used,
                leaf_cap,
                budget,
                depth,
            )?;
            let hi = descend_derived(
                work,
                flp,
                j,
                lb0.max(cut + 1.0),
                ub0,
                leaves_used,
                leaf_cap,
                budget,
                depth,
            )?;
            Some(TreeNode::Split {
                col: Col(j as u32),
                cut: cut_r,
                lo: Box::new(lo),
                hi: Box::new(hi),
            })
        }
    }
}

/// One branch of a `derive_leaf` extension split.
#[allow(clippy::too_many_arguments)]
fn descend_derived(
    work: &mut Model,
    flp: Option<&FloatCtx>,
    c: usize,
    lb: f64,
    ub: f64,
    leaves_used: &mut usize,
    leaf_cap: usize,
    budget: &FinalizeBudget,
    depth: usize,
) -> Option<TreeNode> {
    if lb > ub {
        return trivial_empty_leaf(c, leaves_used, leaf_cap);
    }
    let (lb0, ub0) = work.col_bounds(Col(c as u32));
    work.set_col_bounds(Col(c as u32), lb, ub);
    let out = derive_leaf(work, flp, leaves_used, leaf_cap, budget, depth + 1);
    work.set_col_bounds(Col(c as u32), lb0, ub0);
    out
}

/// PREFER THE SMALLER CERTIFICATE when both lanes are affordable.
///
/// # The regression this exists to remove
///
/// The float lane is tried first because it is milliseconds against an exact
/// rim's seconds. But the two lanes do not produce the same SIZE of evidence,
/// and once the free-column elimination let the float lane certify leaves that
/// used to fall through to the rim, those leaves' multipliers got much bulkier:
/// the rim emits `75733/1510`, the exactified float emits
/// `2514297896833393/70368744177664`. MEASURED on the four instances an
/// adversarial review found, at the `--emit-cert-max-bytes` values they were
/// filed under — every one had been exit 0 and became exit 10, the block
/// DROPPED and the claim downgraded:
///
/// | model                    | cap       | rim-derived | float-derived |
/// |--------------------------|-----------|-------------|---------------|
/// | `g503inf`                |     3 000 |       1 662 |         6 438 |
/// | `flugplinf`              | 1 000 000 |     917 884 |     1 214 577 |
/// | `W1_unsat_v9_c14_000008` |    25 000 |      18 584 |        33 608 |
/// | `W1_sat_v16_c39_000008`  |     1 500 |         917 |         2 731 |
///
/// On `g503inf` both leaves moved lane (`float_ok=0 exact_ok=2` before,
/// `float_ok=2 exact_ok=0` after) and the multiplier count went 47 -> 127.
///
/// # What this does about it
///
/// The float proposal is kept — it is already exact-verified, and it is the
/// only thing standing between these leaves and NO certificate at all — but
/// when it carries the dyadic signature of an exactified ray
/// ([`worth_compacting`]) the rim is asked for a second opinion inside a
/// measured fair-share slice ([`FinalizeBudget::compaction_slice`]). The rim's
/// answer ships only if it VERIFIES against the same box and is strictly
/// smaller in the bytes the cap counts.
///
/// # Why this cannot cost coverage or soundness
///
/// Every exit of this function returns a certificate that has already been
/// verified against `work`: the float proposal on entry, or a rim certificate
/// that passed its own `verify` in [`rim_leaf_farkas`]. There is no path on
/// which a failed, slow, or declining rim removes evidence — it can only fail
/// to replace it — so the coverage the float lane bought is untouchable here,
/// and `finalize` re-verifies the whole tree afterwards regardless.
///
/// (Rejected alternative, MEASURED: rescaling a leaf's multipliers to clear
/// their denominators is a real 2.1x win on the value bytes alone — 3 568 ->
/// 1 654 on `g503inf`'s two float leaves — but it cannot touch the multiplier
/// COUNT, and 64 multipliers per leaf against the rim's 24 still lands at
/// ~4 086 bytes against a 3 000 cap. The lane choice is the load-bearing part;
/// denominator clearing is at best an addition to it.)
fn compact_leaf(
    work: &Model,
    proposal: FarkasCertificate,
    budget: &FinalizeBudget,
    leaves_done: usize,
) -> FarkasCertificate {
    use std::sync::atomic::Ordering::Relaxed;
    if !worth_compacting(&proposal) {
        fstats::COMPACT_SKIP.fetch_add(1, Relaxed);
        return proposal;
    }
    let Some(slice) = budget.compaction_slice(leaves_done) else {
        return proposal;
    };
    let heavy = wire_weight(&proposal);
    let t = Instant::now();
    let rim = rim_leaf_farkas(work, Some(slice));
    let spent = t.elapsed();
    // STRICTLY smaller, in the bytes `--emit-cert-max-bytes` counts. A tie
    // keeps the float proposal: it is already in hand and cost nothing.
    let winner = rim.filter(|c| wire_weight(c) < heavy);
    budget.charge_compaction(spent, winner.is_some());
    match winner {
        Some(smaller) => {
            fstats::COMPACT_OK.fetch_add(1, Relaxed);
            smaller
        }
        None => {
            fstats::COMPACT_MISS.fetch_add(1, Relaxed);
            proposal
        }
    }
}

/// Does this proposal carry the exactified-float signature — a multiplier
/// whose denominator is wider than [`COMPACT_DENOM_BITS`] bits?
///
/// One `bits()` call per multiplier, so it runs on every float-derived leaf
/// (25 398 of them on `W1_unsat_v25_c45_000008`) without showing up.
fn worth_compacting(cert: &FarkasCertificate) -> bool {
    cert.multipliers
        .iter()
        .any(|m| m.coeff.denom().bits() > COMPACT_DENOM_BITS)
}

/// The wire cost of a leaf's multiplier block, in the bytes
/// `--emit-cert-max-bytes` counts.
///
/// Mirrors `cert_io::write_multipliers` exactly — one
/// `mult <row|col> <index> <lower|upper> <numer[/denom]>` line per multiplier
/// — because the flag this serves is denominated in bytes and the two lanes
/// are ranked against each other in the same units the consumer will pay.
/// `cert_io`'s own tests hold the two functions to the same number, so the
/// mirror cannot drift silently.
pub(crate) fn wire_weight(cert: &FarkasCertificate) -> usize {
    fn digits(v: &num_bigint::BigInt) -> usize {
        v.to_string().len()
    }
    cert.multipliers
        .iter()
        .map(|m| {
            let (index, side) = match m.fact {
                FactRef::RowBound { row, side } => (row.index(), side),
                FactRef::ColBound { col, side } => (col.index(), side),
                // `FactRef` is `#[non_exhaustive]`; an unknown variant is
                // written as the fixed `mult unsupported` and weighed as such.
                #[allow(unreachable_patterns)]
                _ => return "mult unsupported\n".len(),
            };
            let value = if m.coeff.denom().is_one() {
                digits(m.coeff.numer())
            } else {
                digits(m.coeff.numer()) + 1 + digits(m.coeff.denom())
            };
            // "mult " + "row " | "col " + index + " " + side + " " + value + "\n"
            5 + 4 + index.to_string().len() + 1 + side_wire_len(side) + 1 + value + 1
        })
        .sum()
}

/// `cert_io`'s token for a bound side is `lower` or `upper` — both 5 bytes.
fn side_wire_len(side: BoundSide) -> usize {
    match side {
        BoundSide::Lower | BoundSide::Upper => 5,
    }
}

/// ONE exact-rim leaf solve on the CURRENT box of `work`, yielding only a
/// Farkas certificate that has been re-verified against that same box.
///
/// `None` on anything else at all: an unrepresentable model, a budget the
/// solve could not close inside, a relaxation that is not empty in the
/// caller's frame, or a certificate that fails its own check. The caller
/// treats `None` as "no second opinion", never as evidence.
///
/// This is the compaction lane's view of the rim. `derive_leaf` keeps its own
/// inline rim because it must also act on `Feasible` — that is where a leaf
/// gets its bounded exact sub-split — which a size comparison has no use for.
fn rim_leaf_farkas(work: &Model, deadline: Option<Instant>) -> Option<FarkasCertificate> {
    let rim_budget = Budget {
        deadline,
        max_iters: Budget::default_iters(work.num_cols() + work.num_rows()),
    };
    let mut rim = ExactLp::new_within(work, deadline)?;
    match rim.make_feasible(&rim_budget) {
        LpFeasibility::Infeasible(farkas) => {
            farkas.verify(work).ok()?;
            Some(farkas)
        }
        LpFeasibility::Feasible | LpFeasibility::Unknown(_) => None,
    }
}

/// Solve the CURRENT box of `work` on the shared caller-frame float LP and, if
/// the float lane reports primal infeasibility with a phase-I ray, exactify
/// that ray into a [`FarkasCertificate`] and VERIFY it against `work` in exact
/// rationals. `None` on any decline — wrong status, no ray, an infinite bound
/// where the ray needs a finite one, or a combination that does not actually
/// contradict (the float lied). The certificate returned here has passed the
/// same independent exact check the consumer will run; no float enters the
/// evidence.
///
/// `flp` carries the caller model's MATRIX; the leaf's box is passed as
/// explicit bounds (structural columns from `work`'s current — branch-tightened
/// — bounds, logicals from the rows' own ranges), which is exactly the
/// `solve_bounded` node-re-solve convention.
fn float_leaf_farkas(
    work: &Model,
    flp: &FloatCtx,
    deadline: Option<Instant>,
) -> Option<FarkasCertificate> {
    let n = work.num_cols();
    let m = work.num_rows();
    let mut lo = Vec::with_capacity(n + m);
    let mut up = Vec::with_capacity(n + m);
    for j in 0..n {
        let (lb, ub) = work.col_bounds(Col(j as u32));
        lo.push(lb);
        up.push(ub);
    }
    for r in 0..m {
        let (_, lb, ub) = work.row(Row(r as u32));
        lo.push(lb);
        up.push(ub);
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
    if cand.status != SimplexStatus::PrimalInfeasible || cand.farkas.len() != m {
        fstats::FLOAT_STATUS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return None;
    }
    if let Some(cert) = exact_farkas_from_float_ray(work, &cand.farkas) {
        fstats::FLOAT_OK.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return Some(cert);
    }
    fstats::FLOAT_VERIFY.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    None
}

/// Exactify a phase-I row ray and verify the resulting contradiction against
/// `work`. The float solver's ray is advice only: both possible sign
/// conventions are tried, and only an independently exact-verified Farkas
/// certificate is returned.
pub(crate) fn exact_farkas_from_float_ray(work: &Model, ray: &[f64]) -> Option<FarkasCertificate> {
    if ray.len() != work.num_rows() {
        return None;
    }
    // The phase-I sign convention is not pinned down (see
    // `safe_farkas_proves_empty`); try the ray both ways.
    for sign in [1.0f64, -1.0] {
        if let Some(cert) = ray_to_farkas(work, ray, sign) {
            if cert.verify(work).is_ok() {
                return Some(cert);
            }
        }
    }
    None
}

/// Turn a float row ray into candidate Farkas multipliers over `work`'s facts,
/// EXACTLY: each `f64` converts losslessly to a rational, the column
/// cancellation coefficients are computed in exact arithmetic, and the bound
/// side each multiplier cites is chosen so the oriented combination is
/// `0·x >= −constant`. Soundness does not rest here — the caller re-verifies
/// the certificate — but everything is exact so an honest ray survives.
///
/// Rows whose needed side is infinite get their multiplier zeroed (any `y` is
/// a valid `y`). A COLUMN whose needed side is infinite has no bound fact to
/// cancel against, so its residual is driven to EXACTLY zero instead — see
/// [`eliminate_unbounded_residuals`].
fn ray_to_farkas(work: &Model, ray: &[f64], sign: f64) -> Option<FarkasCertificate> {
    let n = work.num_cols();
    let m = work.num_rows();
    // Exact row multipliers, indexed by row; zero = the row contributes
    // nothing. Held dense rather than emitted inline because the elimination
    // pass below adjusts individual entries after the fact.
    let mut w = vec![BigRational::zero(); m];
    // Column cancellation accumulator: d_j = Σ_r w_r · a_rj, exact.
    let mut d = vec![BigRational::zero(); n];
    let mut any_row = false;
    for (r, &y_r) in ray.iter().enumerate() {
        let v = sign * y_r;
        if v == 0.0 || !v.is_finite() {
            continue;
        }
        let (_, lb, ub) = work.row(Row(r as u32));
        // w_r > 0 cites the row's LOWER side (`a·x − lb >= 0`), w_r < 0 the
        // UPPER (`ub − a·x >= 0`); an infinite side zeroes the multiplier.
        let finite = if v > 0.0 {
            lb.is_finite()
        } else {
            ub.is_finite()
        };
        if !finite {
            continue;
        }
        let wr = exact(v)?;
        accumulate_row(work, r, &wr, &mut d)?;
        w[r] = wr;
        any_row = true;
    }
    if !any_row {
        return None;
    }
    eliminate_unbounded_residuals(work, &mut w, &mut d)?;

    // Emit the row facts from the FINAL multipliers: elimination can change a
    // multiplier's magnitude or its sign, and the sign picks the bound side.
    let mut multipliers = Vec::new();
    for (r, wr) in w.into_iter().enumerate() {
        if wr.is_zero() {
            continue;
        }
        let (_, lb, ub) = work.row(Row(r as u32));
        let side = if wr.is_positive() {
            BoundSide::Lower
        } else {
            BoundSide::Upper
        };
        // A multiplier that ended up citing an infinite side cannot simply be
        // dropped — its contribution is already in `d` — so decline. Only
        // two-sided rows are ever pivoted on, so this is unreachable today; it
        // is the guard that keeps it so.
        let finite = match side {
            BoundSide::Lower => lb.is_finite(),
            BoundSide::Upper => ub.is_finite(),
        };
        if !finite {
            return None;
        }
        multipliers.push(Multiplier {
            fact: FactRef::RowBound {
                row: Row(r as u32),
                side,
            },
            coeff: wr.abs(),
        });
    }
    if multipliers.is_empty() {
        return None;
    }
    for (j, dj) in d.into_iter().enumerate() {
        if dj.is_zero() {
            continue;
        }
        // `+d_j·x_j` cancels against the column bound: positive needs the
        // UPPER fact (`ub − x >= 0`), negative the LOWER (`x − lb >= 0`).
        let (lb, ub) = work.col_bounds(Col(j as u32));
        let side = if dj.is_positive() {
            if !ub.is_finite() {
                return None;
            }
            BoundSide::Upper
        } else {
            if !lb.is_finite() {
                return None;
            }
            BoundSide::Lower
        };
        multipliers.push(Multiplier {
            fact: FactRef::ColBound {
                col: Col(j as u32),
                side,
            },
            coeff: dj.abs(),
        });
    }
    Some(FarkasCertificate { multipliers })
}

/// `d += coeff · A_r`, exactly, over the TRUE matrix.
///
/// The coefficient comes from [`Model::row_coeff_exact`], not from `exact(a)`
/// on the stored `f64`: on a model carrying a rational side-store the stored
/// `f64` is only a rounded proxy, and [`crate::cert::FarkasCertificate::verify`]
/// prices the emitted certificate against the side-store. Accumulating against
/// anything else would mean cancelling a matrix nobody checks.
fn accumulate_row(
    work: &Model,
    r: usize,
    coeff: &BigRational,
    d: &mut [BigRational],
) -> Option<()> {
    let (coeffs, _, _) = work.row(Row(r as u32));
    for &(c, a) in coeffs {
        if !a.is_finite() || c as usize >= d.len() {
            return None;
        }
        d[c as usize] += coeff * work.row_coeff_exact(r, c, a);
    }
    Some(())
}

/// The TRUE rational entry `a_rj`, summing duplicate entries exactly as
/// `combine` accumulates them.
fn exact_col_entry(work: &Model, r: usize, j: usize) -> Option<BigRational> {
    let (coeffs, _, _) = work.row(Row(r as u32));
    let mut acc = BigRational::zero();
    for &(c, a) in coeffs {
        if c as usize != j {
            continue;
        }
        if !a.is_finite() {
            return None;
        }
        acc += work.row_coeff_exact(r, c, a);
    }
    Some(acc)
}

/// Whether residual `d_j` has a column-bound fact to cancel against: `+d_j·x_j`
/// needs the UPPER fact when positive, the LOWER when negative.
fn residual_has_bound(work: &Model, j: usize, dj: &BigRational) -> bool {
    let (lb, ub) = work.col_bounds(Col(j as u32));
    if dj.is_positive() {
        ub.is_finite()
    } else {
        lb.is_finite()
    }
}

/// How many elimination pivots one exactification may spend. Each step is one
/// row scan plus one sparse `axpy`, and the measured worst case over the ny W1
/// corpus is 14; the cap exists so a pathological free-column block degrades to
/// a decline instead of an open-ended exact elimination.
const ELIMINATION_STEP_CAP: usize = 64;

/// Drive every residual with no bound fact behind it to EXACTLY zero, by
/// moving the ray rather than by ignoring the residual.
///
/// # Why this is needed
///
/// A phase-I ray from the float lane is a rounded real vector. Where the true
/// ray cancels a column exactly — which it must, on every column with no finite
/// bound on the needed side — the float ray leaves `d_j` at roundoff scale
/// (measured: median 1.1e-16 against legitimate residuals of median 2.2). There
/// is no bound fact to absorb that dirt, so the old code declined the whole
/// leaf and the caller paid a cold exact rim solve instead. On the ny W1
/// Big-M models, whose NN pre-activations are 73 FREE columns of 231, that
/// dead-end fired on 47.5% of leaves and cost 99.5% of certificate finalize.
///
/// # What it does
///
/// For each such column `j`, pick a row `r` with `a_rj != 0` and set
/// `delta = −d_j / a_rj` exactly, then `w_r += delta` and `d += delta · A_r`.
/// This is one step of Gaussian elimination on the ray, in exact rationals:
/// the ray moves inside the affine set the true ray lives in, and column `j`
/// lands on a computed zero.
///
/// Pivot rows must have BOTH bounds finite, so however `w_r`'s sign ends up
/// the row still has a fact to cite. Each row is spent at most once, which
/// bounds the loop by the row count independently of the step cap.
///
/// # Why this cannot weaken the evidence
///
/// It changes only the PROPOSAL. The result is priced from scratch against the
/// model by `verify`, which requires every combined coefficient to be exactly
/// zero and the constant strictly negative — an overshooting or mis-pivoted
/// elimination produces a non-contradiction and is declined. Nothing here
/// introduces a tolerance, and no residual is ever assumed to be zero: `d_j`
/// is recomputed through the same accumulator as every other term.
fn eliminate_unbounded_residuals(
    work: &Model,
    w: &mut [BigRational],
    d: &mut [BigRational],
) -> Option<()> {
    let n = d.len();
    let m = w.len();
    let mut spent = vec![false; m];
    let mut steps = 0usize;
    loop {
        // Rescanned from scratch every step: a pivot can re-dirty a column an
        // earlier pivot cleared, and that column must be picked up again.
        let blocked = (0..n).find(|&j| !d[j].is_zero() && !residual_has_bound(work, j, &d[j]));
        let Some(j) = blocked else { return Some(()) };
        if steps >= ELIMINATION_STEP_CAP {
            return None;
        }
        // Largest available entry in column j, for bit-size: `delta` carries
        // `a_rj` in its denominator. The ranking is advice and runs in f64;
        // the pivot value itself is taken exactly below.
        let mut pivot: Option<(usize, f64)> = None;
        for r in 0..m {
            if spent[r] {
                continue;
            }
            let (coeffs, lb, ub) = work.row(Row(r as u32));
            if !lb.is_finite() || !ub.is_finite() {
                continue;
            }
            let mag = coeffs
                .iter()
                .filter(|&&(c, _)| c as usize == j)
                .map(|&(_, a)| a)
                .sum::<f64>()
                .abs();
            if mag > 0.0 && mag.is_finite() && pivot.is_none_or(|(_, best)| mag > best) {
                pivot = Some((r, mag));
            }
        }
        let (r, _) = pivot?;
        let a_rj = exact_col_entry(work, r, j)?;
        if a_rj.is_zero() {
            return None;
        }
        let delta = -(&d[j]) / &a_rj;
        accumulate_row(work, r, &delta, d)?;
        w[r] += delta;
        spent[r] = true;
        steps += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{Duration, Instant};

    fn contradictory_root() -> Model {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
        model
    }

    #[test]
    fn margin_cover_seals_an_open_root_and_replays_it() {
        let model = contradictory_root();
        let mut capture = TreeCapture::new(1);

        let cert = capture
            .finalize_margin_cover(&model, None)
            .expect("the original contradictory model has a one-leaf proof");
        assert_eq!(cert.num_leaves(), 1);
        cert.verify(&model)
            .expect("the emitted proof must verify in the original frame");
        assert!(
            !capture.is_armed(),
            "sealing consumes the proof opportunity"
        );
    }

    #[test]
    fn false_bound_trigger_cannot_prove_a_feasible_open_leaf() {
        let mut model = Model::new();
        model.add_binary_col();
        let mut capture = TreeCapture::new(1);

        assert!(
            capture.finalize_margin_cover(&model, None).is_none(),
            "the trigger is advice; a feasible original leaf must defeat replay"
        );
        assert!(
            !capture.is_armed(),
            "a failed replay cannot be retried as authority"
        );
    }

    #[test]
    fn sealing_rejects_more_terminal_regions_than_the_leaf_cap() {
        let model = contradictory_root();
        let mut capture = TreeCapture::new(1);
        let root = capture.root();
        let (_lo, _hi) = capture.split(root, 0, 0.0);

        assert!(
            capture.finalize_margin_cover(&model, None).is_none(),
            "two open regions do not fit a one-leaf certificate budget"
        );
        assert!(!capture.is_armed());
    }

    #[test]
    fn expired_margin_replay_deadline_fails_closed() {
        let model = contradictory_root();
        let mut capture = TreeCapture::new(1);
        let expired = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("monotonic clock supports a one-second lookback");

        assert!(capture
            .finalize_margin_cover(&model, Some(expired))
            .is_none());
        assert!(!capture.is_armed());
    }

    #[test]
    fn successful_margin_preview_preserves_the_real_capture() {
        let model = contradictory_root();
        let mut capture = TreeCapture::new(1);

        let cert = capture
            .preview_margin_cover(&model, None)
            .expect("the preview clone can replay the contradictory root");
        cert.verify(&model)
            .expect("preview authority is production-verified in the original frame");
        assert!(
            capture.is_armed(),
            "preview must not consume the real capture"
        );
        assert_eq!(capture.nodes.len(), 1);
        assert!(matches!(capture.nodes[0], CapNode::Open));
        assert_eq!(capture.closed, 0);

        let final_cert = capture
            .finalize_margin_cover(&model, None)
            .expect("the untouched real capture must remain finalizable");
        final_cert
            .verify(&model)
            .expect("the later real finalize still verifies");
        assert!(
            !capture.is_armed(),
            "only the real finalize consumes capture"
        );
    }

    #[test]
    fn expired_failed_margin_preview_preserves_capture_for_later_finalize() {
        let model = contradictory_root();
        let mut capture = TreeCapture::new(1);
        let expired = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("monotonic clock supports a one-second lookback");

        assert!(
            capture
                .preview_margin_cover(&model, Some(expired))
                .is_none(),
            "the clone must fail closed under an expired preview deadline"
        );
        assert!(
            capture.is_armed(),
            "a failed preview must leave the real capture armed"
        );
        assert_eq!(capture.nodes.len(), 1);
        assert!(matches!(capture.nodes[0], CapNode::Open));
        assert_eq!(capture.closed, 0);

        let cert = capture
            .finalize_margin_cover(&model, None)
            .expect("a later real finalize must still be able to succeed");
        cert.verify(&model)
            .expect("later authority verifies against the original model");
    }

    // -----------------------------------------------------------------------
    // The ROOT float-first Farkas proposer.
    // -----------------------------------------------------------------------

    /// The lane exists so that a root witness the exact rim cannot AFFORD is
    /// still exported. What it returns must be indistinguishable in authority
    /// from what the rim returns: an exact certificate that verifies against
    /// the caller's model.
    #[test]
    fn root_float_farkas_proposes_a_witness_that_verifies_exactly() {
        let model = contradictory_root();
        let cert = root_float_farkas(&model, None)
            .expect("a contradictory root relaxation has a Farkas witness");
        cert.verify(&model)
            .expect("the float lane may only ever return an exact-verified certificate");
    }

    /// AND IT MUST DECLINE. The float solve is advice; a model whose
    /// relaxation is satisfiable has no Farkas witness at all, and the lane
    /// must produce nothing rather than something unverifiable. (`x <= 1` over
    /// one binary column is trivially feasible.)
    #[test]
    fn root_float_farkas_declines_on_a_feasible_relaxation() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0)]);
        assert!(
            root_float_farkas(&model, None).is_none(),
            "a feasible relaxation has no root Farkas witness to export"
        );
    }

    // -----------------------------------------------------------------------
    // The finalize budget: the cap that moved inside the walk.
    // -----------------------------------------------------------------------

    fn budget(
        deadline: Option<Instant>,
        rim_slice: Option<Duration>,
        captured_leaves: usize,
        t0: Instant,
    ) -> FinalizeBudget {
        FinalizeBudget {
            deadline,
            rim_slice,
            captured_leaves,
            t0,
            baseline: std::cell::Cell::new(None),
            float_spent: std::cell::Cell::new(Duration::ZERO),
            compaction_spent: std::cell::Cell::new(Duration::ZERO),
            compaction_strikes: std::cell::Cell::new(0),
            compaction_off: std::cell::Cell::new(false),
        }
    }

    /// ONE exact-rim leaf may take the slice, and never more — this is the
    /// misc05inf bound, now applied where the runaway actually was (a single
    /// rim solve) instead of to the whole walk.
    #[test]
    fn the_rim_slice_bounds_one_leaf_and_never_outlives_the_caller() {
        let now = Instant::now();
        let far = now + Duration::from_secs(120);
        let slice = Duration::from_secs(5);

        let capped = budget(Some(far), Some(slice), 0, now)
            .rim_deadline()
            .expect("a caller deadline is present");
        assert!(
            capped <= now + slice + Duration::from_millis(500),
            "one rim leaf must not be handed the caller's whole wall"
        );

        // A caller deadline SHORTER than the slice still wins: the slice may
        // only shorten a leaf, never extend the run past the caller.
        let near = now + Duration::from_millis(50);
        assert_eq!(
            budget(Some(near), Some(slice), 0, now).rim_deadline(),
            Some(near)
        );

        // No slice, no deadline: unbounded, exactly as the margin lane and an
        // unlimited solve have always been.
        assert_eq!(budget(None, None, 0, now).rim_deadline(), None);
    }

    /// THE AFFORDABILITY PROJECTION, in both directions. A walk that cannot
    /// reach the last captured leaf inside the caller's deadline is abandoned;
    /// one that comfortably can is not — and neither judgement is made before
    /// the rate estimate has a warm sample to stand on.
    ///
    /// The baseline is INJECTED rather than slept for: `hopeless` measures the
    /// marginal rate between the warm-up latch and the current call, and a
    /// test that latched it for real would be measuring nothing but its own
    /// two adjacent calls. Injecting `(16 leaves, 0s)` against a `t0` ten
    /// seconds in the past states the rate exactly — 10 s over 16 leaves —
    /// so the arithmetic under test is the arithmetic that ships.
    #[test]
    fn hopeless_abandons_only_a_walk_that_cannot_finish() {
        let sample = 2 * HOPELESS_MIN_SAMPLE;
        let t0 = Instant::now()
            .checked_sub(Duration::from_secs(10))
            .expect("monotonic clock supports a ten-second lookback");
        let deadline = Instant::now() + Duration::from_secs(10);

        // Below the warm-up sample nothing is judged, however bad it looks —
        // and the baseline is not latched from a call that did not judge.
        let b = budget(Some(deadline), None, 1_000_000, t0);
        assert!(!b.hopeless(HOPELESS_MIN_SAMPLE - 1));
        assert!(b.baseline.get().is_none());
        // The first call AT the warm-up latches and still judges nothing:
        // there is no marginal rate yet.
        assert!(!b.hopeless(HOPELESS_MIN_SAMPLE));
        assert!(b.baseline.get().is_some());

        // ~0.6 s/leaf measured over the sample, against a million leaves left:
        // not reachable in ten seconds by three orders of magnitude.
        let runaway = budget(Some(deadline), None, 1_000_000, t0);
        runaway
            .baseline
            .set(Some((HOPELESS_MIN_SAMPLE, Duration::ZERO)));
        assert!(
            runaway.hopeless(sample),
            "a runaway tree must be abandoned as soon as its rate is known"
        );

        // The SAME rate against four remaining leaves fits with room to spare.
        let fits = budget(Some(deadline), None, sample + 4, t0);
        fits.baseline
            .set(Some((HOPELESS_MIN_SAMPLE, Duration::ZERO)));
        assert!(
            !fits.hopeless(sample),
            "a walk that fits the caller's wall must never be abandoned"
        );

        // An unbounded caller has no wall to project against.
        let unbounded = budget(None, None, 1_000_000, t0);
        unbounded
            .baseline
            .set(Some((HOPELESS_MIN_SAMPLE, Duration::ZERO)));
        assert!(!unbounded.hopeless(sample));
    }

    /// `x0` free, `x1 ∈ [0,1]`; `x0 + x1 = 0` and `x0 + 2·x1 >= 3`. Substituting
    /// the equality leaves `x1 >= 3` against `x1 <= 1`: infeasible, with an
    /// exact Farkas ray `(-1, +1)` on the two rows.
    fn free_column_infeasible(r1_lb: f64) -> Model {
        let mut model = Model::new();
        let x0 = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let x1 = model.add_col(0.0, 1.0);
        model.add_row(0.0, 0.0, &[(x0, 1.0), (x1, 1.0)]);
        model.add_row(r1_lb, f64::INFINITY, &[(x0, 1.0), (x1, 2.0)]);
        model
    }

    /// THE LEAF-EXACTIFICATION HOLE. A float ray carries roundoff, so where the
    /// TRUE ray cancels a free column exactly the float one leaves a residual
    /// of order 1e-16. A free column has no bound fact to absorb it, and the
    /// exactifier used to decline the whole leaf on that — forcing a cold exact
    /// rim solve that cost 99.5% of certificate finalize on the ny W1 models.
    ///
    /// The perturbed ray below is the smallest possible instance of that: one
    /// ULP on a single entry. The residual it leaves on the free column `x0` is
    /// `2^-52`, against a contradiction margin of 2.
    #[test]
    fn one_ulp_on_a_free_column_does_not_cost_the_certificate() {
        let model = free_column_infeasible(3.0);
        let ray = [-1.0, 1.0 + f64::EPSILON];

        let cert = exact_farkas_from_float_ray(&model, &ray)
            .expect("a ray that is right to one ULP still proves the leaf empty");
        cert.verify(&model)
            .expect("the emitted certificate must verify exactly against the model");

        // ELIMINATED, NOT ABSORBED. The free column must carry no column-bound
        // multiplier: it has no finite bound to cite, so a certificate that
        // cited one — or that quietly dropped the residual — would be pricing a
        // fact the model does not contain.
        assert!(
            !cert.multipliers.iter().any(|m| matches!(
                m.fact,
                FactRef::ColBound { col, .. } if col == Col(0)
            )),
            "the free column's residual must be driven to zero, never absorbed"
        );
    }

    /// FAIL-CLOSED. The same ray against a FEASIBLE model: `x0 + 2·x1 >= 0`
    /// admits `x0 = x1 = 0`. Elimination still clears the free column — it is
    /// pure linear algebra and knows nothing about feasibility — so the only
    /// thing standing between it and a false certificate is the independent
    /// exact re-check. That check must reject.
    #[test]
    fn elimination_cannot_manufacture_a_contradiction() {
        let model = free_column_infeasible(0.0);
        let ray = [-1.0, 1.0 + f64::EPSILON];
        assert!(
            exact_farkas_from_float_ray(&model, &ray).is_none(),
            "no ray can certify a feasible relaxation empty"
        );
    }

    /// FAIL-CLOSED, the other way. Elimination pivots only on rows with BOTH
    /// bounds finite, because such a row can cite a fact whichever way its
    /// multiplier's sign lands. With no such row touching the free column there
    /// is nothing to eliminate against, and the answer must be NO CERTIFICATE —
    /// never a combination carrying an uncancelled term on a column that ranges
    /// over all of R, which would read as a proof while proving nothing.
    #[test]
    fn a_free_column_with_no_two_sided_row_is_declined() {
        let mut model = Model::new();
        let x0 = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let x1 = model.add_col(0.0, 1.0);
        // Both rows one-sided, so neither is a legal pivot.
        model.add_row(0.0, f64::INFINITY, &[(x0, 1.0), (x1, 1.0)]);
        model.add_row(3.0, f64::INFINITY, &[(x0, 1.0), (x1, 2.0)]);

        for ray in [[-1.0, 1.0 + f64::EPSILON], [1.0, -1.0], [1.0, 1.0]] {
            assert!(
                exact_farkas_from_float_ray(&model, &ray).is_none(),
                "an uncancellable free column must decline, not ship"
            );
        }
    }

    /// THE EXACTIFIER MUST CANCEL THE MATRIX THE VERIFIER PRICES.
    ///
    /// When a coefficient's `f64` is only a rounded proxy the truth lives in
    /// the model's rational side-store, and `combine` prices the certificate
    /// against THAT. An exactifier that cancels against the stored `f64`
    /// instead is cancelling a matrix nobody checks: every combination it
    /// builds misses by the rounding error and `verify` rejects the lot with
    /// `CoefficientMismatch`. Safe, but it silently switches the whole float
    /// lane off for such models.
    ///
    /// Here `x0 + 7/3·x1 >= 3` has no `f64` for `7/3`. With the equality
    /// `x0 + x1 = 0` it forces `x1 >= 9/4`, against `x1 <= 1`.
    #[test]
    fn exactification_prices_the_side_store_not_the_rounded_proxy() {
        let mut model = Model::new();
        let x0 = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let x1 = model.add_col(0.0, 1.0);
        model.add_row(0.0, 0.0, &[(x0, 1.0), (x1, 1.0)]);
        let r1 = model.add_row(3.0, f64::INFINITY, &[(x0, 1.0), (x1, 7.0 / 3.0)]);
        let seven_thirds = BigRational::new(7.into(), 3.into());
        model.record_inexact_row_coeff(r1, 1, seven_thirds.clone());
        assert!(
            BigRational::from_float(7.0f64 / 3.0).unwrap() != seven_thirds,
            "the premise of this test is that 7/3 has no exact f64"
        );

        // One ULP of dirt on the free column as well, so this exercises the
        // elimination and the side-store accessor together.
        let cert = exact_farkas_from_float_ray(&model, &[-1.0, 1.0 + f64::EPSILON])
            .expect("a side-store model must still exactify");
        cert.verify(&model)
            .expect("and must verify against the TRUE rational matrix");
    }

    /// THE CATASTROPHIC PAIRING, pinned directly.
    ///
    /// Two changes are individually survivable and jointly fatal: dropping an
    /// uncancellable residual because it is "only 1e-16", and admitting a
    /// near-zero combined coefficient as zero. Either alone yields no
    /// certificate. TOGETHER they yield a certificate that verifies while
    /// establishing nothing — the leftover term sits on a column ranging over
    /// all of R, so the combination bounds nothing at all.
    ///
    /// The first half cannot be tested from outside `ray_to_farkas`, so this
    /// pins the second: the exact-zero test in `check_contradiction` is what
    /// makes the first half merely useless instead of unsound. It must never
    /// acquire a tolerance.
    #[test]
    fn a_hairs_breadth_of_uncancelled_coefficient_is_still_a_rejection() {
        let model = free_column_infeasible(3.0);
        // The honest certificate for this model, with one column-bound
        // multiplier perturbed by 2^-52 so the free column no longer cancels.
        let dirt = BigRational::new(1.into(), (1u64 << 52).into());
        let cert = FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(0),
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one() + &dirt,
                },
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(1),
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: Col(1),
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one(),
                },
            ],
        };
        match cert.verify(&model) {
            Err(CertificateError::CoefficientMismatch { .. }) => {}
            other => panic!(
                "a combination that does not cancel EXACTLY must be rejected as a \
                 coefficient mismatch, however small the leftover; got {other:?}"
            ),
        }
    }

    // -----------------------------------------------------------------------
    // The size-preference lane: keep the coverage, drop the weight.
    // -----------------------------------------------------------------------

    /// A VALID but deliberately bulky Farkas certificate for
    /// `free_column_infeasible(3.0)`: the honest one, scaled by
    /// `(2^40 + 1) / 2^40`.
    ///
    /// Scaling a Farkas combination by any positive rational leaves it a
    /// Farkas combination — `0·x >= c` with `c > 0` stays a contradiction — so
    /// this verifies exactly, which is the point: it is the shape the
    /// exactified float lane produces, evidence that is CORRECT and HEAVY.
    fn bulky_but_valid(model: &Model) -> FarkasCertificate {
        let fat = BigRational::new(((1i64 << 40) + 1).into(), (1i64 << 40).into());
        let cert = FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(0),
                        side: BoundSide::Upper,
                    },
                    coeff: fat.clone(),
                },
                Multiplier {
                    fact: FactRef::RowBound {
                        row: Row(1),
                        side: BoundSide::Lower,
                    },
                    coeff: fat.clone(),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: Col(1),
                        side: BoundSide::Upper,
                    },
                    coeff: fat,
                },
            ],
        };
        cert.verify(model)
            .expect("the premise of these tests is that the bulky proposal is VALID");
        cert
    }

    /// THE WEIGHT REGRESSION, pinned at the lane choice.
    ///
    /// A float proposal and a rim certificate can both be exact, verified and
    /// correct while differing 5x in wire bytes — MEASURED on `g503inf`, 584
    /// bytes per rim leaf against 2 972 per float leaf, which turned a 1 662
    /// byte certificate into a 6 438 byte one and pushed it through a
    /// documented `--emit-cert-max-bytes 3000`. Trying the float lane first is
    /// right; SHIPPING its answer when a cheaper rim would have produced a
    /// smaller one is what was wrong.
    #[test]
    fn a_bulky_proposal_loses_to_the_rim_when_the_rim_is_affordable() {
        let model = free_column_infeasible(3.0);
        let fat = bulky_but_valid(&model);
        let heavy = wire_weight(&fat);

        // One leaf, a whole minute of wall: the rim is affordable by any
        // measure, so the smaller certificate must be the one that ships.
        let b = budget(
            Some(Instant::now() + Duration::from_secs(60)),
            None,
            1,
            Instant::now(),
        );
        let shipped = compact_leaf(&model, fat, &b, 0);

        assert!(
            wire_weight(&shipped) < heavy,
            "an affordable rim's compact certificate must displace a bulky float \
             proposal: shipped {} bytes against the proposal's {heavy}",
            wire_weight(&shipped)
        );
        shipped
            .verify(&model)
            .expect("and whatever ships is exact-verified against the model");
    }

    /// COVERAGE IS NEVER THE PRICE OF WEIGHT.
    ///
    /// The compaction lane is an OFFER. When it cannot be afforded — here,
    /// because the governor has already latched off — the float proposal must
    /// come back untouched. The leaves this whole change exists for
    /// (`W1_unsat_v25_c45_000008` and friends, 25 398 leaves at ~1.45 s per rim
    /// solve) are exactly the ones that can never afford it, and they must
    /// still ship evidence rather than none.
    #[test]
    fn an_unaffordable_rim_leaves_the_float_proposal_exactly_as_it_was() {
        let model = free_column_infeasible(3.0);
        let fat = bulky_but_valid(&model);

        let b = budget(
            Some(Instant::now() + Duration::from_secs(60)),
            None,
            1,
            Instant::now(),
        );
        b.compaction_off.set(true);
        let shipped = compact_leaf(&model, fat.clone(), &b, 0);

        assert_eq!(
            shipped, fat,
            "a closed compaction lane must return the proposal untouched — \
             losing the leaf here is losing the certificate"
        );
    }

    /// The offer is only made to leaves that could benefit. A proposal whose
    /// multipliers are already small rationals is what the rim itself
    /// produces, so asking the rim costs a solve and buys nothing.
    ///
    /// MEASURED denominator bits: rim-derived leaves run 2-21 (`g503inf` median
    /// 7, `W1_sat_v16_c39_000008` median 2); exactified-float leaves run 53-61.
    #[test]
    fn only_the_dyadic_signature_of_an_exactified_ray_is_offered_to_the_rim() {
        let small = FarkasCertificate {
            multipliers: vec![Multiplier {
                fact: FactRef::RowBound {
                    row: Row(0),
                    side: BoundSide::Lower,
                },
                coeff: BigRational::new(75_733.into(), 1_510.into()),
            }],
        };
        assert!(
            !worth_compacting(&small),
            "a certificate the rim itself would have written is not a candidate"
        );

        let dyadic = FarkasCertificate {
            multipliers: vec![Multiplier {
                fact: FactRef::RowBound {
                    row: Row(0),
                    side: BoundSide::Lower,
                },
                coeff: BigRational::new(
                    2_514_297_896_833_393_i64.into(),
                    70_368_744_177_664_i64.into(),
                ),
            }],
        };
        assert!(
            worth_compacting(&dyadic),
            "a 2^46 denominator is the float lane's signature and must be offered"
        );
    }

    /// THE GOVERNOR IS A FAIR SHARE, and that one division is what separates
    /// the tree that can afford compaction from the tree that cannot.
    ///
    /// MEASURED at `--time-limit 120`: `g503inf` holds 2 leaves and one rim
    /// solve costs ~5 ms, so its share is ~500 ms and the offer is taken;
    /// `W1_unsat_v25_c45_000008` holds 25 398 leaves and one rim solve costs
    /// ~1.45 s, so its share is ~40 us and every offer is struck out.
    #[test]
    fn the_compaction_share_shrinks_with_the_leaves_still_ahead() {
        let t0 = Instant::now();
        let far = t0 + Duration::from_secs(120);

        let small = budget(Some(far), None, 2, t0);
        let big = budget(Some(far), None, 25_398, t0);
        let (s, b) = (
            small
                .compaction_slice(0)
                .expect("a 2-leaf tree gets a share"),
            big.compaction_slice(0).expect("so does a 25k-leaf tree"),
        );
        let (sd, bd) = (
            s.saturating_duration_since(Instant::now()),
            b.saturating_duration_since(Instant::now()),
        );
        assert!(
            sd > Duration::from_millis(100),
            "two leaves must each get a share a real rim solve can use, got {sd:?}"
        );
        assert!(
            bd < Duration::from_millis(1),
            "25 398 leaves must each get a share no rim solve can use, got {bd:?}"
        );

        // And the share never outlives the caller's own wall, however few
        // leaves are left to divide it among.
        let tight = budget(Some(t0 + Duration::from_millis(40)), None, 1, t0);
        let slice = tight
            .compaction_slice(0)
            .expect("a live deadline still yields a share");
        assert!(
            slice <= t0 + Duration::from_millis(40),
            "compaction buys SIZE and must never spend the wall the walk needs \
             to finish at all"
        );
    }

    /// The lane latches off after [`COMPACTION_STRIKES`] consecutive offers
    /// that bought nothing, so a model whose rim is too slow — or simply never
    /// smaller — pays three slices and not one per leaf. Any adoption resets
    /// the count: a lane that is working keeps working.
    #[test]
    fn three_fruitless_offers_close_the_lane_and_one_win_reopens_the_count() {
        let t0 = Instant::now();
        let b = budget(Some(t0 + Duration::from_secs(120)), None, 1_000, t0);

        for _ in 0..COMPACTION_STRIKES - 1 {
            b.charge_compaction(Duration::from_millis(1), false);
        }
        assert!(
            b.compaction_slice(0).is_some(),
            "one unlucky leaf must not close the lane"
        );

        b.charge_compaction(Duration::from_millis(1), true);
        for _ in 0..COMPACTION_STRIKES - 1 {
            b.charge_compaction(Duration::from_millis(1), false);
        }
        assert!(
            b.compaction_slice(0).is_some(),
            "an adoption must reset the strike count"
        );

        b.charge_compaction(Duration::from_millis(1), false);
        assert!(
            b.compaction_slice(0).is_none(),
            "three consecutive fruitless offers must close the lane for good"
        );
    }

    /// The whole lane is bounded by [`COMPACTION_WARMUP`] plus what the float
    /// lane has itself spent — so finalize can cost at most about twice what
    /// it costs with no compaction at all, whatever the model does.
    #[test]
    fn the_compaction_allowance_is_spent_once_and_then_the_lane_closes() {
        let t0 = Instant::now();
        let b = budget(Some(t0 + Duration::from_secs(3_600)), None, 4, t0);
        b.charge_compaction(COMPACTION_WARMUP + Duration::from_millis(1), true);
        assert!(
            b.compaction_slice(0).is_none(),
            "an exhausted allowance closes the lane even on a run of wins"
        );
    }
}
