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
/// each leaf, and how the float lane declined when it did.
mod fstats {
    use std::sync::atomic::AtomicUsize;
    pub(super) static FLOAT_OK: AtomicUsize = AtomicUsize::new(0);
    pub(super) static FLOAT_STATUS: AtomicUsize = AtomicUsize::new(0);
    pub(super) static FLOAT_VERIFY: AtomicUsize = AtomicUsize::new(0);
    pub(super) static EXACT_OK: AtomicUsize = AtomicUsize::new(0);
    pub(super) static EXACT_FAIL: AtomicUsize = AtomicUsize::new(0);
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
        deadline: Option<std::time::Instant>,
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
        let t0 = std::time::Instant::now();
        let root = build_node(
            &self.nodes,
            0,
            &mut work,
            fctx.as_ref(),
            &mut leaves_used,
            self.leaf_cap,
            deadline,
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
        }
        let cert = MilpInfeasibilityCertificate { root: root? };
        // Emission is fail-closed: the certificate must convince the same
        // independent checker the consumer will run, or it does not ship.
        cert.verify(model).ok()?;
        Some(cert)
    }
}

/// Expired-deadline test (finalize runs strictly inside the solve's budget).
fn expired(deadline: Option<std::time::Instant>) -> bool {
    deadline.is_some_and(|d| std::time::Instant::now() >= d)
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
    deadline: Option<std::time::Instant>,
) -> Option<TreeNode> {
    if expired(deadline) {
        return None;
    }
    match arena.get(id as usize)? {
        // A node the search never resolved: the skeleton does not tile the
        // domain (this cannot happen on a genuine exhausted-tree Infeasible,
        // but the capture never assumes that).
        CapNode::Open => None,
        CapNode::Closed => derive_leaf(work, flp, leaves_used, leaf_cap, deadline, 0),
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
                deadline,
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
                deadline,
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
    deadline: Option<std::time::Instant>,
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
    let out = build_node(arena, id, work, flp, leaves_used, leaf_cap, deadline);
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
    deadline: Option<std::time::Instant>,
    depth: usize,
) -> Option<TreeNode> {
    if expired(deadline) || depth > leaf_cap {
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
        if let Some(farkas) = float_leaf_farkas(work, flp, deadline) {
            *leaves_used += 1;
            if *leaves_used > leaf_cap {
                return None;
            }
            return Some(TreeNode::Leaf { farkas });
        }
        if expired(deadline) {
            return None;
        }
    }
    let budget = Budget {
        deadline,
        max_iters: Budget::default_iters(work.num_cols() + work.num_rows()),
    };
    let mut rim = ExactLp::new_within(work, deadline)?;
    match rim.make_feasible(&budget) {
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
                deadline,
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
                deadline,
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
    deadline: Option<std::time::Instant>,
    depth: usize,
) -> Option<TreeNode> {
    if lb > ub {
        return trivial_empty_leaf(c, leaves_used, leaf_cap);
    }
    let (lb0, ub0) = work.col_bounds(Col(c as u32));
    work.set_col_bounds(Col(c as u32), lb, ub);
    let out = derive_leaf(work, flp, leaves_used, leaf_cap, deadline, depth + 1);
    work.set_col_bounds(Col(c as u32), lb0, ub0);
    out
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
    deadline: Option<std::time::Instant>,
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
/// a valid `y`); a COLUMN whose needed side is infinite is a dead end (its
/// term cannot be canceled), declined.
fn ray_to_farkas(work: &Model, ray: &[f64], sign: f64) -> Option<FarkasCertificate> {
    let n = work.num_cols();
    let mut multipliers = Vec::new();
    // Column cancellation accumulator: d_j = Σ_r w_r · a_rj, exact.
    let mut d = vec![BigRational::zero(); n];
    for (r, &y_r) in ray.iter().enumerate() {
        let v = sign * y_r;
        if v == 0.0 || !v.is_finite() {
            continue;
        }
        let (coeffs, lb, ub) = work.row(Row(r as u32));
        // w_r > 0 cites the row's LOWER side (`a·x − lb >= 0`), w_r < 0 the
        // UPPER (`ub − a·x >= 0`); an infinite side zeroes the multiplier.
        let side = if v > 0.0 {
            BoundSide::Lower
        } else {
            BoundSide::Upper
        };
        let finite = match side {
            BoundSide::Lower => lb.is_finite(),
            BoundSide::Upper => ub.is_finite(),
        };
        if !finite {
            continue;
        }
        let w = exact(v)?;
        for &(c, a) in coeffs {
            d[c as usize] += &w * exact(a)?;
        }
        multipliers.push(Multiplier {
            fact: FactRef::RowBound {
                row: Row(r as u32),
                side,
            },
            coeff: w.abs(),
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
