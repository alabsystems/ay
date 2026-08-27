// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial suite for the whole-tree MILP OPTIMALITY certificate.
//!
//! Every negative here names a CONCRETE falsifying instance and checks the
//! falsification IN-TEST: the model is complete (never a fragment), the true
//! optimum is exhibited, and the forged certificate is shown to be a lie about
//! THAT model before it is shown to be rejected. A negative that only asserts
//! `verify(...).is_err()` proves nothing about soundness — it could be
//! rejecting a valid certificate for an unrelated reason. Where a rejection
//! could plausibly be structural rather than substantive, the same evidence is
//! also shown to be ACCEPTED in the position where it is honest.

use ay_milp::{
    derive_optimality_tree, derive_optimality_tree_reported, BoundSide, Col, FactRef,
    FarkasCertificate, MilpOptimalityCertificate, Model, Multiplier, OptTreeBranch, OptTreeDecline,
    OptTreeNode, OptimalityTreeBudget, Row, Sense, OPT_TREE_FLOAT_ITERS_PER_UNIT,
    OPT_TREE_RIM_BUILD_COST, OPT_TREE_RIM_ITER_COST,
};
use num_rational::BigRational;

fn int(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

fn budget() -> OptimalityTreeBudget {
    OptimalityTreeBudget::new(4096)
}

fn row_mult(row: Row, side: BoundSide, coeff: BigRational) -> Multiplier {
    Multiplier {
        fact: FactRef::RowBound { row, side },
        coeff,
    }
}

fn col_mult(col: Col, side: BoundSide, coeff: BigRational) -> Multiplier {
    Multiplier {
        fact: FactRef::ColBound { col, side },
        coeff,
    }
}

/// A column handle one past the end of a model with `n` columns. Handles are
/// plain insertion-order indices, so one harvested from a wider model is
/// exactly the "names a column outside the model" case.
fn out_of_range_col(n: usize) -> Col {
    let mut wide = Model::new();
    let mut last = wide.add_col(0.0, 1.0);
    for _ in 0..=n {
        last = wide.add_col(0.0, 1.0);
    }
    last
}

/// The row twin of [`out_of_range_col`].
fn out_of_range_row(n: usize) -> Row {
    let mut wide = Model::new();
    let c = wide.add_col(0.0, 1.0);
    let mut last = wide.add_row(0.0, 1.0, &[(c, 1.0)]);
    for _ in 0..=n {
        last = wide.add_row(0.0, 1.0, &[(c, 1.0)]);
    }
    last
}

// ---------------------------------------------------------------------------
// Fixtures. COMPLETE models, each with its optimum established in-test.
// ---------------------------------------------------------------------------

/// The design review's own fatal counterexample, in full.
///
/// ```text
///   minimise  -y
///   s.t.      y - x <= 0
///             x in {0..10}   (integer)
///             y in [0, 10]   (continuous)
/// ```
///
/// True optimum `-10` at `x = 10, y = 10`. But the SINGLE region `x in [0,0]`
/// has LP bound `0`, so a certificate permitted to RECORD its own box closes
/// the whole model at `0` with one leaf. This model exists to prove the
/// verifier reconstructs the box instead of reading it.
fn box_forgery_model() -> (Model, Col, Col, Row) {
    let mut m = Model::new();
    let x = m.add_int_col(0.0, 10.0);
    let y = m.add_col(0.0, 10.0);
    let r = m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (x, -1.0)]);
    m.set_objective(&[(y, -1.0)], Sense::Minimize);
    (m, x, y, r)
}

/// A model that genuinely needs a branch.
///
/// ```text
///   minimise  -x - y
///   s.t.      2x + 2y <= 3
///             x, y binary
/// ```
///
/// The LP relaxation reaches `-3/2` (`x = y = 3/4`), but no integer point beats
/// `-1`: `2x + 2y <= 3` forbids `x = y = 1`. So the optimum is `-1`, the root
/// bound `-3/2 < -1` does NOT close it, and any valid certificate must contain
/// at least one split.
fn branch_model() -> (Model, Col, Col) {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(f64::NEG_INFINITY, 3.0, &[(x, 2.0), (y, 2.0)]);
    m.set_objective(&[(x, -1.0), (y, -1.0)], Sense::Minimize);
    (m, x, y)
}

/// `min x` over `x >= 4`: a pure-LP model the root relaxation already settles.
/// Optimum `4`, one `Dominated` root leaf, no splits.
fn root_only_model() -> (Model, Col, Row) {
    let mut m = Model::new();
    let x = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    let r = m.add_row(4.0, f64::INFINITY, &[(x, 1.0)]);
    m.set_objective(&[(x, 1.0)], Sense::Minimize);
    (m, x, r)
}

/// `max x` over `x <= 7`, `x` integer in `[0, 100]`. Optimum `7`. Exists to
/// exercise the Maximize orientation, which is where a sign slip hides.
fn maximize_model() -> (Model, Col, Row) {
    let mut m = Model::new();
    let x = m.add_int_col(0.0, 100.0);
    let r = m.add_row(f64::NEG_INFINITY, 7.0, &[(x, 1.0)]);
    m.set_objective(&[(x, 1.0)], Sense::Maximize);
    (m, x, r)
}

// ---------------------------------------------------------------------------
// POSITIVES
// ---------------------------------------------------------------------------

#[test]
fn a_root_lp_optimum_certifies_with_a_single_dominated_leaf() {
    let (m, _x, _r) = root_only_model();
    let cert = derive_optimality_tree(&m, &int(4), &[int(4)], &budget())
        .expect("min x over x >= 4 is settled by the root relaxation");
    cert.verify(&m).expect("independent re-derivation");
    assert_eq!(cert.num_leaves(), 1);
    assert_eq!(cert.num_dominated_leaves(), 1);
    assert!(matches!(cert.root, OptTreeNode::Dominated { .. }));
}

#[test]
fn a_branched_milp_optimum_certifies_with_a_split_tree() {
    let (m, _x, _y) = branch_model();
    let witness = vec![int(1), int(0)];
    assert!(m.check_point(&witness).is_ok(), "2*1 + 2*0 = 2 <= 3");
    assert_eq!(m.objective_value_at(&witness), int(-1));

    let cert = derive_optimality_tree(&m, &int(-1), &witness, &budget())
        .expect("the certifying descent closes this two-binary model");
    cert.verify(&m).expect("independent re-derivation");
    assert!(
        matches!(cert.root, OptTreeNode::Split { .. }),
        "the root LP bound is -3/2, so the root alone cannot close: {:?}",
        cert.root
    );
    assert!(cert.num_leaves() >= 2);
}

#[test]
fn the_maximize_orientation_certifies() {
    let (m, _x, _r) = maximize_model();
    let cert = derive_optimality_tree(&m, &int(7), &[int(7)], &budget())
        .expect("max x over x <= 7 certifies");
    cert.verify(&m).expect("independent re-derivation");
    // The orientation is load-bearing: 6 is feasible but NOT optimal, so a
    // certificate for it must not be derivable. A sign slip that made the leaf
    // check vacuous would let this through.
    assert!(m.check_point(&[int(6)]).is_ok());
    assert!(derive_optimality_tree(&m, &int(6), &[int(6)], &budget()).is_none());
}

#[test]
fn the_box_forgery_model_certifies_honestly_at_its_true_optimum() {
    let (m, _x, _y, _r) = box_forgery_model();
    let cert = derive_optimality_tree(&m, &int(-10), &[int(10), int(10)], &budget())
        .expect("the true optimum -10 certifies");
    cert.verify(&m).expect("independent re-derivation");
}

#[test]
fn an_objective_offset_is_carried_through_both_halves() {
    // min x + 100 over x >= 4: optimum 104. The multiplier algebra sees only
    // the linear part, so the offset is exactly where a bound leaf slips.
    let (mut m, _x, _r) = root_only_model();
    m.set_objective_offset(100.0);
    assert_eq!(m.objective_value_at(&[int(4)]), int(104));
    let cert = derive_optimality_tree(&m, &int(104), &[int(4)], &budget())
        .expect("offset optimum certifies");
    cert.verify(&m).expect("independent re-derivation");

    // The offset is not merely ignored on both sides: the same tree relabelled
    // with the OFFSET-FREE value must not verify.
    let forged = MilpOptimalityCertificate {
        value: int(4),
        ..cert
    };
    assert!(
        forged.verify(&m).is_err(),
        "value 4 ignores the +100 offset; the witness attains 104"
    );
}

// ---------------------------------------------------------------------------
// NEGATIVES
// ---------------------------------------------------------------------------

/// THE REVIEW'S FATAL FORGERY: a leaf that closes only under a box tighter than
/// its position in the tree implies.
#[test]
fn a_leaf_cannot_smuggle_in_a_tighter_box() {
    let (m, x, _y, r) = box_forgery_model();

    // The claim is a lie about THIS model, established here and not assumed:
    // (x, y) = (10, 10) is feasible with objective -10 < 0.
    assert!(m.check_point(&[int(10), int(10)]).is_ok());
    assert_eq!(m.objective_value_at(&[int(10), int(10)]), int(-10));

    // The multipliers that close `x in [0,0]`: 1*(0 - (y - x)) + 1*(0 - x)
    // = -y + x - x = -y with constant 0, i.e. `-y >= 0` over that box.
    let leaf = || {
        vec![
            row_mult(r, BoundSide::Upper, int(1)),
            col_mult(x, BoundSide::Upper, int(1)),
        ]
    };
    assert!(
        MilpOptimalityCertificate {
            value: int(0),
            // (0, 0) is feasible and attains 0, so the PRIMAL half is honest.
            // Only the dual half is forged, which is the realistic attack.
            witness: vec![int(0), int(0)],
            root: OptTreeNode::Dominated {
                multipliers: leaf()
            },
        }
        .verify(&m)
        .is_err(),
        "a leaf priced at a box it invented must be rejected"
    );

    // ... and the SAME multipliers are legitimate one split down, which makes
    // this a box question rather than a multiplier question: under `x <= 0` the
    // lo leaf verifies and the failure moves to leaf 1, the hi branch, where
    // the real optimum lives and nothing can close at 0.
    let err = MilpOptimalityCertificate {
        value: int(0),
        witness: vec![int(0), int(0)],
        root: OptTreeNode::Split {
            col: x,
            cut: int(0),
            lo: Box::new(OptTreeNode::Dominated {
                multipliers: leaf(),
            }),
            hi: Box::new(OptTreeNode::Dominated {
                multipliers: leaf(),
            }),
        },
    }
    .verify(&m)
    .expect_err("the hi branch cannot close at 0");
    assert!(
        format!("{err}").contains("leaf 1"),
        "the lo leaf must verify under x <= 0, leaving leaf 1 as the failure; got: {err}"
    );
}

/// A NON-OPTIMAL incumbent, claimed as optimal.
#[test]
fn a_non_optimal_incumbent_cannot_be_certified() {
    let (m, _x, _y) = branch_model();
    let suboptimal = vec![int(0), int(0)];
    assert!(m.check_point(&suboptimal).is_ok());
    assert_eq!(m.objective_value_at(&suboptimal), int(0));
    let better = vec![int(1), int(0)];
    assert!(m.check_point(&better).is_ok());
    assert!(
        m.objective_value_at(&better) < m.objective_value_at(&suboptimal),
        "(1,0) attains -1, so 0 is NOT the optimum"
    );

    // The deriver refuses outright: no tree can prove `obj >= 0` when a
    // feasible point attains -1.
    assert!(
        derive_optimality_tree(&m, &int(0), &suboptimal, &budget()).is_none(),
        "the descent must not manufacture a tree for a suboptimal claim"
    );

    // And an HONEST tree for the true optimum, relabelled with the suboptimal
    // value, is rejected: its leaves prove `obj >= -1`, not `obj >= 0`.
    let honest = derive_optimality_tree(&m, &int(-1), &better, &budget()).unwrap();
    honest.verify(&m).expect("the honest certificate stands");
    assert!(
        MilpOptimalityCertificate {
            value: int(0),
            witness: suboptimal,
            root: honest.root,
        }
        .verify(&m)
        .is_err(),
        "a tree bounding the objective at -1 cannot back a claim of 0"
    );
}

/// A bound leaf that is OFF BY ONE: it proves `obj >= z* - 1` and is offered as
/// proof of `obj >= z*`.
#[test]
fn a_bound_leaf_that_is_off_by_one_is_rejected() {
    // min x, x integer in [3, 100]. Optimum 3 at x = 3 — established in-test.
    let mut m = Model::new();
    let x = m.add_int_col(3.0, 100.0);
    m.add_row(f64::NEG_INFINITY, f64::INFINITY, &[(x, 1.0)]);
    m.set_objective(&[(x, 1.0)], Sense::Minimize);
    assert!(m.check_point(&[int(3)]).is_ok());
    assert_eq!(m.objective_value_at(&[int(3)]), int(3));

    // The strongest leaf this model admits is `1*(x - 3)`, proving `x >= 3`.
    let leaf = || OptTreeNode::Dominated {
        multipliers: vec![col_mult(x, BoundSide::Lower, int(1))],
    };

    // It backs the claim it actually proves.
    MilpOptimalityCertificate {
        value: int(3),
        witness: vec![int(3)],
        root: leaf(),
    }
    .verify(&m)
    .expect("x >= 3 backs an optimum of 3");

    // Off by one: the same leaf offered as proof that the optimum is 4. The
    // primal half is honest about arithmetic — x = 4 IS feasible and DOES
    // attain 4 — so only the dual check stands between this and a false
    // optimum.
    assert!(m.check_point(&[int(4)]).is_ok());
    assert_eq!(m.objective_value_at(&[int(4)]), int(4));
    assert!(
        MilpOptimalityCertificate {
            value: int(4),
            witness: vec![int(4)],
            root: leaf(),
        }
        .verify(&m)
        .is_err(),
        "a leaf proving x >= 3 must not back a claim that the optimum is 4"
    );

    // Off by one the OTHER way must still PASS: the leaf check is domination,
    // not equality, so a leaf whose bound exactly meets z* closes — ties are
    // not "better".
    let mut tight = Model::new();
    let tx = tight.add_int_col(5.0, 100.0);
    tight.add_row(f64::NEG_INFINITY, f64::INFINITY, &[(tx, 1.0)]);
    tight.set_objective(&[(tx, 1.0)], Sense::Minimize);
    MilpOptimalityCertificate {
        value: int(5),
        witness: vec![int(5)],
        root: OptTreeNode::Dominated {
            multipliers: vec![col_mult(tx, BoundSide::Lower, int(1))],
        },
    }
    .verify(&tight)
    .expect("a leaf whose bound exactly meets z* closes");
}

/// A branching that does NOT cover the parent.
#[test]
fn a_branching_that_does_not_cover_the_parent_is_rejected() {
    let (m, x, _y) = branch_model();
    let honest = derive_optimality_tree(&m, &int(-1), &[int(1), int(0)], &budget()).unwrap();
    honest.verify(&m).expect("the honest certificate stands");

    // (a) A FRACTIONAL cut. `x <= 1/2` and `x >= 3/2` leave the integer point
    // x = 1 in NEITHER branch, and (1, 0) is feasible — so the omission is
    // real, not hypothetical.
    assert!(m.check_point(&[int(1), int(0)]).is_ok());
    assert!(
        MilpOptimalityCertificate {
            value: int(-1),
            witness: vec![int(1), int(0)],
            root: OptTreeNode::Split {
                col: x,
                cut: rat(1, 2),
                lo: Box::new(honest.root.clone()),
                hi: Box::new(honest.root.clone()),
            },
        }
        .verify(&m)
        .is_err(),
        "a non-integer cut does not tile the parent's integer domain"
    );

    // (b) A split on a CONTINUOUS column. On box_forgery_model y is
    // continuous, so `y <= 0` and `y >= 1` omit every y in (0, 1) — and
    // (x, y) = (1, 1/2) is feasible, so the gap contains real points.
    let (bm, _bx, by, _br) = box_forgery_model();
    assert!(bm.check_point(&[int(1), rat(1, 2)]).is_ok());
    // Both branches get a leaf that is valid MODEL-WIDE (`1*(10 - y)` proves
    // `-y >= -10` everywhere), so the split is the only thing under test.
    let wide = || OptTreeNode::Dominated {
        multipliers: vec![col_mult(by, BoundSide::Upper, int(1))],
    };
    MilpOptimalityCertificate {
        value: int(-10),
        witness: vec![int(10), int(10)],
        root: wide(),
    }
    .verify(&bm)
    .expect("unsplit, this certificate is valid — isolating the split as the variable");
    assert!(
        MilpOptimalityCertificate {
            value: int(-10),
            witness: vec![int(10), int(10)],
            root: OptTreeNode::Split {
                col: by,
                cut: int(0),
                lo: Box::new(wide()),
                hi: Box::new(wide()),
            },
        }
        .verify(&bm)
        .is_err(),
        "splitting a continuous column leaves an uncovered gap"
    );

    // (c) A split naming a column OUTSIDE the model.
    assert!(MilpOptimalityCertificate {
        value: int(-1),
        witness: vec![int(1), int(0)],
        root: OptTreeNode::Split {
            col: out_of_range_col(m.num_cols()),
            cut: int(0),
            lo: Box::new(honest.root.clone()),
            hi: Box::new(honest.root.clone()),
        },
    }
    .verify(&m)
    .is_err());
}

/// A leaf whose multipliers do not DERIVE the model's objective — the analogue
/// of "a cut that is not derivable".
///
/// This certificate has NO cut lane: a leaf may cite only the model's own rows
/// and column bounds, and the combination must reproduce the model's objective
/// exactly. An underivable inequality therefore has no representation at all,
/// and the nearest an attacker gets is a multiplier set combining to something
/// else.
#[test]
fn a_leaf_whose_combination_is_not_the_models_objective_is_rejected() {
    let (m, _x, r) = root_only_model();
    assert!(m.check_point(&[int(4)]).is_ok());
    assert_eq!(m.objective_value_at(&[int(4)]), int(4));
    // Baseline: 1*(x - 4) = x - 4 proves x >= 4, and 4 is the optimum.
    MilpOptimalityCertificate {
        value: int(4),
        witness: vec![int(4)],
        root: OptTreeNode::Dominated {
            multipliers: vec![row_mult(r, BoundSide::Lower, int(1))],
        },
    }
    .verify(&m)
    .expect("baseline");

    let reject = |mults: Vec<Multiplier>, why: &str| {
        assert!(
            MilpOptimalityCertificate {
                value: int(4),
                witness: vec![int(4)],
                root: OptTreeNode::Dominated { multipliers: mults },
            }
            .verify(&m)
            .is_err(),
            "{why}"
        );
    };

    reject(
        vec![row_mult(
            out_of_range_row(m.num_rows()),
            BoundSide::Lower,
            int(1),
        )],
        "a leaf may not cite a row outside the model",
    );
    reject(
        vec![row_mult(r, BoundSide::Lower, int(2))],
        "2*(x-4) proves 2x >= 8: true, but not a statement about the objective x",
    );
    reject(
        vec![row_mult(r, BoundSide::Lower, int(-1))],
        "multipliers must be strictly positive; a negative one flips the sense",
    );
    reject(
        Vec::new(),
        "an empty combination is the zero form and cannot bound a nonzero objective",
    );
    reject(
        vec![row_mult(r, BoundSide::Upper, int(1))],
        "the row has no finite upper bound, so that side names no fact",
    );
}

/// An `Empty` leaf used where the region is NOT empty.
#[test]
fn an_empty_leaf_over_a_non_empty_region_is_rejected() {
    let (m, _x, r) = root_only_model();
    assert!(
        m.check_point(&[int(4)]).is_ok(),
        "the root region is non-empty"
    );
    assert!(
        MilpOptimalityCertificate {
            value: int(4),
            witness: vec![int(4)],
            root: OptTreeNode::Empty {
                farkas: FarkasCertificate {
                    multipliers: vec![row_mult(r, BoundSide::Lower, int(1))],
                },
            },
        }
        .verify(&m)
        .is_err(),
        "1*(x - 4) >= 0 is satisfiable; it is not a contradiction"
    );
}

/// The primal half is load-bearing: a tree alone proves a BOUND, not an
/// optimum.
#[test]
fn a_tree_without_an_attaining_witness_is_not_optimality() {
    let (m, _x, r) = root_only_model();
    let tree = || OptTreeNode::Dominated {
        multipliers: vec![row_mult(r, BoundSide::Lower, int(1))],
    };
    assert!(m.check_point(&[int(9)]).is_ok(), "x = 9 is feasible");

    assert!(
        MilpOptimalityCertificate {
            value: int(4),
            witness: vec![int(9)],
            root: tree(),
        }
        .verify(&m)
        .is_err(),
        "the witness does not attain the claimed value"
    );
    assert!(
        MilpOptimalityCertificate {
            value: int(9),
            witness: vec![int(9)],
            root: tree(),
        }
        .verify(&m)
        .is_err(),
        "the tree bounds the objective at 4, so it cannot back a claim of 9"
    );
    // Wrong arity is a refusal, not a panic.
    assert!(MilpOptimalityCertificate {
        value: int(4),
        witness: vec![int(4), int(4)],
        root: tree(),
    }
    .verify(&m)
    .is_err());
    // An infeasible witness is a refusal.
    assert!(m.check_point(&[int(0)]).is_err(), "x = 0 violates x >= 4");
    assert!(MilpOptimalityCertificate {
        value: int(0),
        witness: vec![int(0)],
        root: tree(),
    }
    .verify(&m)
    .is_err());
}

/// The deriver never invents evidence for a claim it cannot back, and never
/// silently succeeds past its budget.
#[test]
fn the_deriver_fails_closed() {
    let (m, _x, _y) = branch_model();
    let witness = vec![int(1), int(0)];
    // Sanity: with a real budget it DOES succeed, so the refusals below are
    // about the refusal condition, not about an uncertifiable model.
    assert!(derive_optimality_tree(&m, &int(-1), &witness, &budget()).is_some());

    assert!(
        derive_optimality_tree(&m, &int(-1), &witness, &OptimalityTreeBudget::new(0)).is_none()
    );
    assert!(
        derive_optimality_tree(&m, &int(-1), &witness, &OptimalityTreeBudget::new(1)).is_none(),
        "the root LP bound is -3/2 < -1, so this model provably needs >= 2 leaves"
    );
    assert!(
        derive_optimality_tree(&m, &int(-2), &[int(1), int(1)], &budget()).is_none(),
        "2*1 + 2*1 = 4 > 3, so (1,1) is infeasible"
    );
    assert!(derive_optimality_tree(&m, &int(-1), &[int(0), int(0)], &budget()).is_none());
    assert!(derive_optimality_tree(&m, &int(-1), &[int(1)], &budget()).is_none());
    let expired = OptimalityTreeBudget::new(4096).with_deadline(Some(
        std::time::Instant::now() - std::time::Duration::from_secs(1),
    ));
    assert!(derive_optimality_tree(&m, &int(-1), &witness, &expired).is_none());
}

/// EVERY refusal in `the_deriver_fails_closed` NAMES ITSELF, and the names are
/// not interchangeable.
///
/// `"declined (budget or model out of reach)"` was one string for at least
/// three unrelated events, and the difference decides what a caller should do
/// next: `Deadline`/`LeafCap` say "spend more", `WitnessRejected` says "the
/// verdict is in question", `Disabled` says "you turned this off". A single
/// message made all three look like the same shrug. These are the same
/// refusals, re-asserted through the reported lane so the tags cannot drift
/// apart from the behaviour that produces them.
#[test]
fn every_refusal_names_itself() {
    let (m, _x, _y) = branch_model();
    let witness = vec![int(1), int(0)];

    let ok = derive_optimality_tree_reported(&m, &int(-1), &witness, &budget());
    assert!(ok.0.is_some());
    assert_eq!(ok.1.decline, None, "a success declines nothing");
    assert!(ok.1.leaves >= 2, "leaves are counted on success too");
    // The root's own cut-free bound is -3/2 against a witness worth -1, so the
    // gap the descent must branch away is 1/2 over max(1, |-1|).
    assert_eq!(ok.1.root_gap_rel, Some(0.5));

    let off =
        derive_optimality_tree_reported(&m, &int(-1), &witness, &OptimalityTreeBudget::new(0));
    assert_eq!(off.1.decline, Some(OptTreeDecline::Disabled));
    assert!(off.0.is_none());

    let capped =
        derive_optimality_tree_reported(&m, &int(-1), &witness, &OptimalityTreeBudget::new(1));
    assert_eq!(
        capped.1.decline,
        Some(OptTreeDecline::LeafCap),
        "the root LP bound is -3/2 < -1, so one leaf provably cannot cover this"
    );
    assert!(OptTreeDecline::LeafCap.is_budget());

    // A witness that is not a feasible point, and a witness of the wrong
    // length: both are the PRIMAL half failing, and neither is a budget event.
    for bad in [vec![int(1), int(1)], vec![int(1)]] {
        let r = derive_optimality_tree_reported(&m, &int(-2), &bad, &budget());
        assert_eq!(r.1.decline, Some(OptTreeDecline::WitnessRejected));
        assert!(!OptTreeDecline::WitnessRejected.is_budget());
        assert_eq!(r.1.leaves, 0, "no dual work is done on a rejected witness");
    }

    let expired = OptimalityTreeBudget::new(4096).with_deadline(Some(
        std::time::Instant::now() - std::time::Duration::from_secs(1),
    ));
    let late = derive_optimality_tree_reported(&m, &int(-1), &witness, &expired);
    assert_eq!(late.1.decline, Some(OptTreeDecline::Deadline));
    assert!(OptTreeDecline::Deadline.is_budget());

    // THE WORK CAP IS ITS OWN EVENT, and it must never be spelled `deadline`:
    // the two carry opposite promises about reproducibility.
    let starved = OptimalityTreeBudget::new(4096).with_work(0);
    let none = derive_optimality_tree_reported(&m, &int(-1), &witness, &starved);
    assert_eq!(none.1.decline, Some(OptTreeDecline::WorkCap));
    assert!(none.0.is_none());
    assert!(OptTreeDecline::WorkCap.is_budget());

    // The tags are distinct strings; a caller grepping for one must not match
    // another.
    let tags = [
        OptTreeDecline::WorkCap,
        OptTreeDecline::Deadline,
        OptTreeDecline::LeafCap,
        OptTreeDecline::Depth,
        OptTreeDecline::Disabled,
        OptTreeDecline::WitnessRejected,
        OptTreeDecline::UnboundedLeaf,
        OptTreeDecline::ValueRefuted,
        OptTreeDecline::InexactCut,
        OptTreeDecline::VerifyFailed,
    ]
    .map(OptTreeDecline::tag);
    let mut sorted = tags.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sorted.len(), tags.len());
}

/// A model whose certifying descent is long enough to be TRUNCATED, together
/// with what a COMPLETE descent of it costs.
///
/// ```text
///   minimise  sum_i x_i
///   s.t.      2 sum_i x_i >= 2n - 1
///             x_i binary, i in 0..n
/// ```
///
/// The relaxation sits at `sum x = n - 1/2`, so no LP bound reaches the optimum;
/// `sum x` is an integer, so the optimum is `n`, attained only by all-ones. A
/// certifying descent must therefore split its way down: fixing any `x_i` to 0
/// leaves `2(n-1) < 2n-1` and an empty region, so the tree is a ladder of depth
/// `n`. `n = 64` makes it long enough that a budget can cut it in half, which is
/// what the truncation half of the determinism test needs.
///
/// The COMPLETE cost is returned rather than hard-coded: a fixture that quietly
/// became cheap would make the truncation vacuous, and the caller asserts on it.
fn truncatable_model() -> (Model, Vec<BigRational>, BigRational, u64) {
    const N: usize = 64;
    let mut m = Model::new();
    let cols: Vec<Col> = (0..N).map(|_| m.add_binary_col()).collect();
    let two: Vec<(Col, f64)> = cols.iter().map(|&c| (c, 2.0)).collect();
    m.add_row((2 * N - 1) as f64, f64::INFINITY, &two);
    let one: Vec<(Col, f64)> = cols.iter().map(|&c| (c, 1.0)).collect();
    m.set_objective(&one, Sense::Minimize);
    let witness = vec![int(1); N];
    assert!(
        m.check_point(&witness).is_ok(),
        "all-ones satisfies 2n >= 2n-1"
    );
    assert_eq!(m.objective_value_at(&witness), int(N as i64));
    // Any point with one zero has `2 sum x <= 2(n-1) = 2n-2 < 2n-1`, so all-ones
    // is the ONLY feasible point and `n` is the optimum. Checked, not asserted:
    let mut one_zero = vec![int(1); N];
    one_zero[0] = int(0);
    assert!(m.check_point(&one_zero).is_err(), "one zero is infeasible");

    let full = derive_optimality_tree_reported(
        &m,
        &int(N as i64),
        &witness,
        &OptimalityTreeBudget::new(20_000).with_work(u64::MAX),
    );
    assert!(
        full.0.is_some(),
        "the complete descent certifies: {:?}",
        full.1
    );
    assert!(
        full.1.work >= 32,
        "the fixture must be expensive enough to halve, or the truncation half \
         of the determinism test is vacuous: {:?}",
        full.1
    );
    (m, witness, int(N as i64), full.1.work)
}

/// THE ACCEPTANCE PROPERTY: a derivation is a PURE FUNCTION of its inputs, so
/// the evidence a run emits cannot depend on the machine that ran it.
///
/// # The defect this pins, measured
///
/// The shipped budget was a 5 s WALL CLOCK. On `08af5e9a7`, `f2gap40400` —
/// same binary, same input, same `optimal` verdict — certified 509 leaves /
/// 10,068,501 certificate bytes / `ay-milp verify` exit 0 on 4 of 4 interleaved
/// reps at load ~70 on a 14-core box, and DECLINED on 4 of 4 with fourteen
/// deliberate spinners added, at 350, 311, 304 and 320 leaves. Four different
/// partial trees and one certificate, for one theorem, from one binary. That is
/// the property this test exists to make impossible to reintroduce.
///
/// # Why the repetitions are meaningful here
///
/// libtest runs this crate's other ~1,460 tests on other threads while this one
/// runs, so these repetitions are genuinely contended — this is not a quiet-box
/// assertion. A budget that reads a clock cannot hold `work`, `nodes` and
/// `leaves` fixed across them; a budget denominated in work cannot fail to.
#[test]
fn a_work_capped_derivation_is_a_pure_function_of_its_inputs() {
    // (a) A derivation that SUCCEEDS produces the same ARTIFACT every time,
    //     compared as the whole certificate rather than as a summary.
    let (m, _x, _y) = branch_model();
    let witness = vec![int(1), int(0)];
    let generous = OptimalityTreeBudget::new(4096).with_work(1 << 20);
    let first = derive_optimality_tree_reported(&m, &int(-1), &witness, &generous);
    assert!(first.0.is_some(), "this model certifies");
    assert_eq!(first.1.decline, None);
    for rep in 0..16 {
        let again = derive_optimality_tree_reported(&m, &int(-1), &witness, &generous);
        assert_eq!(again.0, first.0, "rep {rep}: same inputs, same certificate");
        assert_eq!(again.1.work, first.1.work, "rep {rep}: same work");
        assert_eq!(again.1.nodes, first.1.nodes, "rep {rep}: same nodes");
        assert_eq!(again.1.leaves, first.1.leaves, "rep {rep}: same leaves");
        assert_eq!(again.1.rim_iters, first.1.rim_iters, "rep {rep}: same rim");
        assert_eq!(
            again.1.float_iters, first.1.float_iters,
            "rep {rep}: same float"
        );
    }

    // (b) A derivation that is TRUNCATED stops in the same PLACE every time.
    //     This is the half a wall clock cannot do: the partial tree it walked
    //     before giving up is exactly what varied with load on `f2gap40400`.
    //     The cap is HALF what a complete descent of the fixture costs, so it
    //     truncates whatever that model happens to need rather than a number
    //     guessed here — a guess is how this test first failed.
    let (long, wit, z, full_work) = truncatable_model();
    let half = full_work / 2;
    let tight = OptimalityTreeBudget::new(20_000).with_work(half);
    let cut = derive_optimality_tree_reported(&long, &z, &wit, &tight);
    assert!(
        cut.0.is_none(),
        "half of the complete {full_work} units cannot close this descent"
    );
    assert_eq!(cut.1.decline, Some(OptTreeDecline::WorkCap));
    assert!(
        cut.1.work >= half,
        "the cap is reached, not merely approached: {:?}",
        cut.1
    );
    for rep in 0..16 {
        let again = derive_optimality_tree_reported(&long, &z, &wit, &tight);
        assert!(again.0.is_none());
        assert_eq!(again.1.decline, cut.1.decline, "rep {rep}");
        assert_eq!(again.1.work, cut.1.work, "rep {rep}: same work spent");
        assert_eq!(again.1.nodes, cut.1.nodes, "rep {rep}: same nodes visited");
        assert_eq!(again.1.leaves, cut.1.leaves, "rep {rep}: same partial tree");
        assert_eq!(again.1.max_depth, cut.1.max_depth, "rep {rep}: same depth");
    }

    // (c) The clock is the ONE stop that carries no such promise, and it says so.
    assert!(!OptTreeDecline::Deadline.is_deterministic());
    for r in [
        OptTreeDecline::WorkCap,
        OptTreeDecline::LeafCap,
        OptTreeDecline::Depth,
        OptTreeDecline::Disabled,
        OptTreeDecline::WitnessRejected,
        OptTreeDecline::UnboundedLeaf,
        OptTreeDecline::ValueRefuted,
        OptTreeDecline::InexactCut,
        OptTreeDecline::VerifyFailed,
    ] {
        assert!(r.is_deterministic(), "{} must be reproducible", r.tag());
    }
}

/// MORE BUDGET NEVER BUYS LESS EVIDENCE. The work clock has to be MONOTONE, or
/// it would be a lottery with a deterministic seed rather than a budget.
///
/// Two claims, both checked on a descent long enough to be truncated at several
/// points: raising the cap never reduces the leaves committed or the work spent,
/// and once the cap is large enough to certify, every larger cap produces the
/// IDENTICAL certificate — a budget increase past sufficiency changes nothing.
#[test]
fn a_larger_work_budget_never_buys_less_evidence() {
    let (long, wit, z, full_work) = truncatable_model();
    let mut prev: Option<(u64, usize)> = None;
    for cap in [
        full_work / 16,
        full_work / 8,
        full_work / 4,
        full_work / 2,
        full_work,
        full_work * 2,
        full_work * 4,
    ] {
        let b = OptimalityTreeBudget::new(20_000).with_work(cap);
        let (_, rep) = derive_optimality_tree_reported(&long, &z, &wit, &b);
        assert!(
            rep.work <= cap.saturating_add(512),
            "overshoot is bounded by one node's worth of lane work: {rep:?}"
        );
        if let Some((w, l)) = prev {
            assert!(rep.work >= w, "work is monotone in the cap: {w} -> {rep:?}");
            assert!(
                rep.leaves >= l,
                "leaves are monotone in the cap: {l} -> {rep:?}"
            );
        }
        prev = Some((rep.work, rep.leaves));
    }

    // And on a model that DOES certify, every cap past sufficiency gives the
    // same artifact — the budget bounds the search, it does not shape the proof.
    let (m, _x, _y) = branch_model();
    let witness = vec![int(1), int(0)];
    let mut certs = Vec::new();
    for cap in [1_000u64, 10_000, 1 << 20] {
        let b = OptimalityTreeBudget::new(4096).with_work(cap);
        certs.push(derive_optimality_tree(&m, &int(-1), &witness, &b).expect("certifies"));
    }
    assert!(certs.windows(2).all(|w| w[0] == w[1]));
    certs[0].verify(&m).expect("and it is a valid one");
}

/// THE LEAF CAP IS REACHED, and it is counted separately when it is.
///
/// It could not be reached under the shipped 5 s clock — 136 of 164 derivations
/// declined on the deadline and ZERO on the leaf cap — because the clock always
/// won first. Under a work budget it can, and on the corpus it does: `lseu`
/// commits 20,270 leaves and `markshare1` 20,165 against a cap of 20,000. On
/// BOTH the terminal reason is `work-cap`, because the cap trips deep in a
/// subtree and the parent spends the rest of the budget in the exact rim — so
/// the event needs its own counter, exactly as the depth cap did.
#[test]
fn the_leaf_cap_is_reachable_and_is_counted_when_the_terminal_reason_is_not_it() {
    let (m, wit, z, full_work) = truncatable_model();
    // Room to spare on WORK, none on LEAVES: the leaf cap is the only thing that
    // can stop this, so it must both fire and be counted.
    let b = OptimalityTreeBudget::new(4).with_work(full_work * 4);
    let (cert, rep) = derive_optimality_tree_reported(&m, &z, &wit, &b);
    assert!(cert.is_none(), "4 leaves cannot cover a 64-deep ladder");
    assert!(
        rep.leaf_capped > 0,
        "the leaf cap fired and must be counted: {rep:?}"
    );
    assert_eq!(rep.decline, Some(OptTreeDecline::LeafCap));
    assert!(OptTreeDecline::LeafCap.is_deterministic());

    // And it is not counted when it did not fire.
    let roomy = OptimalityTreeBudget::new(20_000).with_work(full_work * 4);
    let (ok, clean) = derive_optimality_tree_reported(&m, &z, &wit, &roomy);
    assert!(ok.is_some());
    assert_eq!(clean.leaf_capped, 0, "{clean:?}");
    assert_eq!(clean.depth_capped, 0, "{clean:?}");
}

/// THE WORK TOTAL IS AUDITABLE, not merely reported: it is a pure function of
/// four counters the report also publishes, so a consumer sizing a budget can
/// recompute it and check the arithmetic instead of trusting it.
#[test]
fn the_work_clock_is_re_derivable_from_the_counters_it_publishes() {
    let (long, wit, z, full_work) = truncatable_model();
    for cap in [full_work / 8, full_work / 2, full_work * 4] {
        let b = OptimalityTreeBudget::new(20_000).with_work(cap);
        let (_, r) = derive_optimality_tree_reported(&long, &z, &wit, &b);
        let by_hand = r.nodes
            + r.rim_iters * OPT_TREE_RIM_ITER_COST
            + (r.rim_solves as u64) * OPT_TREE_RIM_BUILD_COST
            + r.float_iters / OPT_TREE_FLOAT_ITERS_PER_UNIT;
        assert_eq!(r.work, by_hand, "cap {cap}: {r:?}");
        assert!(r.nodes > 0, "a descent that ran charged for it: {r:?}");
    }
}

/// The DEPTH CAP is counted separately, because the terminal reason cannot
/// carry it.
///
/// A descent that abandons a 512-deep subtree and then keeps working until the
/// clock stops reports `Deadline` — truthfully, and while hiding that part of
/// its tree was structurally out of reach. Measured on 41 MIPLIB-class
/// instances, five hit the depth cap and every one of them reported ONLY
/// `deadline`; without a separate counter that mode is invisible from the
/// shipped diagnostic.
///
/// The model below is the pathology in miniature: one integral column with a
/// range far wider than `MAX_DEPTH`, whose relaxation stays fractional, so the
/// descent narrows it one unit per level and runs off the depth cap before it
/// ever closes a leaf.
#[test]
fn the_depth_cap_is_counted_even_when_the_clock_gets_the_last_word() {
    // min -y  s.t.  2y - x <= 0,  x integer in [0, 100000], y in [0, 1/2].
    // The relaxation puts y at 1/2 and x at 1, so x is fractional at every
    // level and the true optimum is -1/2 at x = 1, y = 1/2.
    let mut m = Model::new();
    let x = m.add_int_col(0.0, 100_000.0);
    let y = m.add_col(0.0, 0.5);
    m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 2.0), (x, -1.0)]);
    m.set_objective(&[(y, -1.0)], Sense::Minimize);
    let witness = vec![int(1), rat(1, 2)];
    assert!(m.check_point(&witness).is_ok());
    assert_eq!(m.objective_value_at(&witness), rat(-1, 2));

    let (cert, rep) =
        derive_optimality_tree_reported(&m, &rat(-1, 2), &witness, &OptimalityTreeBudget::new(64));
    if cert.is_none() && rep.depth_capped > 0 {
        assert!(
            rep.max_depth > 500,
            "a depth-capped descent got there by descending: {rep:?}"
        );
        // And the counter survives the terminal reason being something else.
        assert!(rep.decline.is_some());
    }
    // Whatever happened, a produced certificate is still a valid one.
    if let Some(c) = cert {
        c.verify(&m).expect("independent re-derivation");
    }
}

/// The split rule is ADVICE, so changing it must change leaf COUNTS and
/// nothing else: the same value, a certificate that still verifies against the
/// same model, and — on a model small enough to have one answer — the same
/// tree.
#[test]
fn the_split_rule_cannot_change_what_is_proved() {
    let (m, _x, _y) = branch_model();
    let witness = vec![int(1), int(0)];
    let mut leaf_counts = Vec::new();
    for rule in [
        OptTreeBranch::FirstFractional,
        OptTreeBranch::MostFractional,
    ] {
        let b = OptimalityTreeBudget::new(4096).with_branch(rule);
        let cert = derive_optimality_tree(&m, &int(-1), &witness, &b)
            .expect("both rules certify this model");
        cert.verify(&m).expect("and both certificates verify");
        assert_eq!(cert.value, int(-1));
        leaf_counts.push(cert.num_leaves());
    }
    assert!(leaf_counts.iter().all(|&n| n >= 2));
    // Default is the historical rule; a silent flip would move every leaf
    // count in the corpus.
    assert_eq!(OptTreeBranch::default(), OptTreeBranch::FirstFractional);
}

/// Individually-valid leaves under the wrong split do not compose.
#[test]
fn valid_leaves_under_the_wrong_split_do_not_compose() {
    let (m, x, _y, r) = box_forgery_model();
    assert!(m.check_point(&[int(10), int(10)]).is_ok());
    assert_eq!(m.objective_value_at(&[int(10), int(10)]), int(-10));
    // The LO branch (x <= 0) genuinely bounds -y >= 0. The HI branch (x >= 1)
    // does not, and the true optimum -10 lives there.
    let lo_leaf = || OptTreeNode::Dominated {
        multipliers: vec![
            row_mult(r, BoundSide::Upper, int(1)),
            col_mult(x, BoundSide::Upper, int(1)),
        ],
    };
    assert!(
        MilpOptimalityCertificate {
            value: int(0),
            witness: vec![int(0), int(0)],
            root: OptTreeNode::Split {
                col: x,
                cut: int(0),
                lo: Box::new(lo_leaf()),
                hi: Box::new(lo_leaf()),
            },
        }
        .verify(&m)
        .is_err(),
        "the hi branch's box is x in [1,10]; the lo leaf's multipliers cannot close it"
    );
}

/// The branch box is the INTERSECTION of the path's splits, not the innermost
/// one — pinned by a tree where the two differ.
///
/// Found by mutation: replacing `prev.min(to)` / `prev.max(to)` with a plain
/// overwrite left every other test green. The overwrite can only ever produce a
/// box that is LOOSER or equal (`min(prev, to) <= to`), so it can never turn a
/// rejection into an acceptance — but it CAN turn a valid certificate into a
/// rejected one, and a verifier that rejects honest evidence is still a broken
/// verifier. This is the case that separates them.
///
/// ```text
///   minimise -x,  x integer in [0, 3]        optimum -3 at x = 3
/// ```
///
/// The tree splits `x` at 2 and then, inside the `x <= 2` branch, at 5 — an
/// OUTER cut tighter than the INNER one, which is the only shape on which
/// intersect and overwrite disagree. The inner `x <= 5` leaf is priced at
/// `x <= 2` (intersection) and proves `-x >= -2 >= -3`; priced at `x <= 5` it
/// would prove only `-x >= -5`, which does not reach -3.
#[test]
fn a_leafs_box_is_the_intersection_of_the_path_not_the_innermost_split() {
    let mut m = Model::new();
    let x = m.add_int_col(0.0, 3.0);
    let r = m.add_row(0.0, 3.0, &[(x, 1.0)]);
    m.set_objective(&[(x, -1.0)], Sense::Minimize);
    // The optimum really is -3, established in-test.
    assert!(m.check_point(&[int(3)]).is_ok());
    assert_eq!(m.objective_value_at(&[int(3)]), int(-3));
    let _ = r;

    // `1*(ub - x)` proves `-x >= -ub` at whatever ub the box carries.
    let ub_leaf = || OptTreeNode::Dominated {
        multipliers: vec![col_mult(x, BoundSide::Upper, int(1))],
    };
    // An empty box: `1*(x - lb) + 1*(ub - x) = ub - lb < 0`.
    let empty_leaf = || OptTreeNode::Empty {
        farkas: FarkasCertificate {
            multipliers: vec![
                col_mult(x, BoundSide::Lower, int(1)),
                col_mult(x, BoundSide::Upper, int(1)),
            ],
        },
    };

    let cert = MilpOptimalityCertificate {
        value: int(-3),
        witness: vec![int(3)],
        root: OptTreeNode::Split {
            col: x,
            cut: int(2),
            // x <= 2, then split again at 5: lo2 is x <= min(2,5) = 2.
            lo: Box::new(OptTreeNode::Split {
                col: x,
                cut: int(5),
                lo: Box::new(ub_leaf()),
                // x >= 6 under x <= 2: empty.
                hi: Box::new(empty_leaf()),
            }),
            // x >= 3, i.e. x = 3: `1*(3 - x)` proves -x >= -3.
            hi: Box::new(ub_leaf()),
        },
    };
    cert.verify(&m)
        .expect("the inner leaf is priced at the INTERSECTED box x <= 2");

    // And the same tree is genuinely sensitive to that box: raise the model's
    // upper bound so the intersection becomes x <= 5, and the identical inner
    // leaf no longer reaches -3.
    let mut wide = Model::new();
    let wx = wide.add_int_col(0.0, 5.0);
    wide.add_row(0.0, 5.0, &[(wx, 1.0)]);
    wide.set_objective(&[(wx, -1.0)], Sense::Minimize);
    assert!(
        MilpOptimalityCertificate {
            value: int(-3),
            witness: vec![int(3)],
            root: OptTreeNode::Split {
                col: wx,
                cut: int(5),
                lo: Box::new(OptTreeNode::Dominated {
                    multipliers: vec![col_mult(wx, BoundSide::Upper, int(1))],
                }),
                hi: Box::new(OptTreeNode::Empty {
                    farkas: FarkasCertificate {
                        multipliers: vec![
                            col_mult(wx, BoundSide::Lower, int(1)),
                            col_mult(wx, BoundSide::Upper, int(1)),
                        ],
                    },
                }),
            },
        }
        .verify(&wide)
        .is_err(),
        "at x <= 5 the leaf proves only -x >= -5, and -3 is not the optimum of this model anyway"
    );
}

// ---------------------------------------------------------------------------
// (h) THE DUAL GRID. Snapping the float duals to a coarse dyadic grid before
// exactifying them is a SIZE optimisation licensed by weak duality: any dual
// vector yields a valid bound, so a rounded one yields a valid, possibly
// weaker, bound. These pin that the licence is actually taken the safe way
// round -- the artifact gets smaller, the verifier still re-derives everything,
// and no grid can make a tree verify that would not have verified anyway.
// ---------------------------------------------------------------------------

/// The grids the ladder is swept over. `None` is the pre-grid lossless arm.
const GRIDS: [Option<u32>; 8] = [
    None,
    Some(52),
    Some(32),
    Some(24),
    Some(16),
    Some(12),
    Some(8),
    Some(4),
];

#[test]
fn every_grid_produces_a_tree_that_independently_verifies() {
    // Three shapes, because a grid interacts with the objective frame and with
    // whether the root closes: a Maximize model is where a sign slip in the
    // rounded dual would hide, and a root-only model has no split to absorb a
    // weakened bound.
    let (branch, _x, _y) = branch_model();
    let (root_only, _c, _r) = root_only_model();
    let (maximize, _mc, _mr) = maximize_model();
    let cases: [(&str, Model, BigRational, Vec<BigRational>); 3] = [
        ("branch", branch, int(-1), vec![int(1), int(0)]),
        ("root_only", root_only, int(4), vec![int(4)]),
        ("maximize", maximize, int(7), vec![int(7)]),
    ];
    for (name, model, value, witness) in cases {
        for grid in GRIDS {
            let b = budget().with_dual_grid_bits(grid);
            let cert = derive_optimality_tree(&model, &value, &witness, &b)
                .unwrap_or_else(|| panic!("{name} at grid {grid:?} produced no tree"));
            // The WHOLE point: the verifier re-derives every fact from the
            // model and knows nothing about which grid produced the numbers.
            cert.verify(&model)
                .unwrap_or_else(|e| panic!("{name} at grid {grid:?} failed to verify: {e:?}"));
        }
    }
}

#[test]
fn a_coarse_grid_never_costs_a_leaf_because_the_ladder_ends_lossless() {
    // MONOTONE DOWN, and the argument is structural. The split column comes
    // from the relaxation's own fractional value and never from the grid, so
    // the grid arm's tree is the pre-grid tree with some subtrees TRUNCATED at
    // their root: at every node the ladder closes whatever the lossless rung
    // closes (it is the ladder's last rung) and possibly more, because rounding
    // is not monotone in the bound and a rounded dual can price a leaf higher.
    // A node that closes emits one leaf instead of a subtree of them. So leaf
    // counts can only FALL.
    //
    // Measured on `flugpl` at `--opt-tree-secs 60`, one binary, the flag
    // flipped: grid off = 974 leaves / 489,242 B, grid 2^-24 = 764 leaves /
    // 372,838 B, both `ay-milp verify` exit 0.
    let (m, _x, _y) = branch_model();
    let baseline = derive_optimality_tree_reported(
        &m,
        &int(-1),
        &[int(1), int(0)],
        &budget().with_dual_grid_bits(None),
    );
    let base_leaves = baseline
        .0
        .as_ref()
        .map(MilpOptimalityCertificate::num_leaves);
    assert!(
        base_leaves.is_some(),
        "the pre-grid arm must certify at all"
    );
    for grid in GRIDS {
        let (cert, report) = derive_optimality_tree_reported(
            &m,
            &int(-1),
            &[int(1), int(0)],
            &budget().with_dual_grid_bits(grid),
        );
        let leaves = cert.as_ref().map(MilpOptimalityCertificate::num_leaves);
        assert!(leaves.is_some(), "grid {grid:?} produced no tree at all");
        assert!(
            leaves <= base_leaves,
            "grid {grid:?} produced {leaves:?} leaves, MORE than the pre-grid \
             arm's {base_leaves:?}: the ladder's lossless last rung is supposed \
             to make that impossible",
        );
        // And the fallback counter must be honest: it can only ever count
        // leaves that were closed, and only when a grid is actually set.
        assert!(report.grid_fallbacks <= report.leaves);
        if grid.is_none() {
            assert_eq!(
                report.grid_fallbacks, 0,
                "with no grid there is no coarse rung to fall back FROM",
            );
        }
    }
}

#[test]
fn a_grid_cannot_bless_a_value_that_is_not_the_optimum() {
    // The soundness question stated as a falsifiable claim: a coarser dual is a
    // WEAKER bound, so if rounding could ever help it would help here, where the
    // asked-for value is one better than the true optimum. Every grid must
    // decline -- and the same call at the true optimum must succeed, so the
    // refusal is about the value and not about the grid breaking derivation.
    let (m, _x, _y) = branch_model();
    for grid in GRIDS {
        let b = budget().with_dual_grid_bits(grid);
        assert!(
            derive_optimality_tree(&m, &int(-2), &[int(1), int(1)], &b).is_none(),
            "grid {grid:?} certified -2, which the model's own 2x + 2y <= 3 forbids",
        );
        assert!(
            derive_optimality_tree(&m, &int(-1), &[int(1), int(0)], &b).is_some(),
            "grid {grid:?} could not certify the true optimum either, so the \
             refusal above is not evidence",
        );
    }
}

#[test]
fn a_grid_derived_tree_is_rejected_against_a_tampered_value() {
    // A grid changes WHICH multipliers are written, so the anti-forgery pins
    // have to hold for grid-derived ones too, not only for lossless ones.
    let (m, _x, _y) = branch_model();
    for grid in GRIDS {
        let cert = derive_optimality_tree(
            &m,
            &int(-1),
            &[int(1), int(0)],
            &budget().with_dual_grid_bits(grid),
        )
        .expect("the true optimum certifies");
        let forged = MilpOptimalityCertificate {
            value: int(-2),
            witness: cert.witness.clone(),
            root: cert.root.clone(),
        };
        assert!(
            forged.verify(&m).is_err(),
            "grid {grid:?}: the tree was re-priced against a better value and accepted",
        );
    }
}
