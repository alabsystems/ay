// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The P2 `MilpInfeasibilityCertificate` lane, exercised over the public API
//! exactly as the downstream optimization consumer's admission seam consumes it: emission on a case-split-only
//! infeasibility, exact `verify(&Model)`, and — the soundness half — a
//! battery of tampered certificates that MUST all fail verification.

use ay_milp::{
    BabSession, BoundSide, CertificateError, FactRef, FarkasCertificate,
    MilpInfeasibilityCertificate, Model, Multiplier, Outcome, SolveOpts, TreeNode,
};
use num_rational::BigRational;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}

fn ratf(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

/// Binaries x, y, z with `x + y + z = 3/2`: the LP relaxation is satisfiable
/// (e.g. all 1/2), every 0/1 assignment sums to an integer != 3/2, and bound
/// propagation cannot tighten any box — infeasible ONLY via case split.
fn case_split_only_model() -> Model {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    let z = m.add_binary_col();
    m.add_row(1.5, 1.5, &[(x, 1.0), (y, 1.0), (z, 1.0)]);
    m
}

/// Solve `m` as a decision problem and return the outcome.
fn check(m: &Model, opts: &SolveOpts) -> Outcome {
    BabSession::new(m.clone(), opts).unwrap().check().unwrap()
}

/// Solve the case-split-only model and demand the whole-tree certificate.
fn emitted_cert() -> (Model, MilpInfeasibilityCertificate) {
    let m = case_split_only_model();
    match check(&m, &SolveOpts::new()) {
        Outcome::Infeasible { cert, tree_cert } => {
            assert!(
                cert.is_none(),
                "the relaxation is satisfiable; no root Farkas can exist"
            );
            let tree_cert = tree_cert.expect(
                "case-split infeasibility within the leaf budget must emit a tree certificate",
            );
            (m, tree_cert)
        }
        other => panic!("expected Infeasible, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// (a) Emission end-to-end.
// ---------------------------------------------------------------------------

#[test]
fn case_split_infeasibility_emits_verifying_tree_certificate() {
    let (m, cert) = emitted_cert();
    cert.verify(&m).unwrap();
    assert!(
        cert.num_leaves() >= 2,
        "a case split has at least two leaves"
    );
    assert!(
        cert.num_leaves() <= 256,
        "the default leaf budget bounds the tree"
    );
}

#[test]
fn live_binary_hint_breaks_the_root_score_tie_only() {
    let mut m = Model::new();
    let x0 = m.add_binary_col();
    let x1 = m.add_binary_col();
    let x2 = m.add_binary_col();
    let y0 = m.add_binary_col();
    let y1 = m.add_binary_col();
    let y2 = m.add_binary_col();
    let fixed = m.add_binary_col();
    let continuous = m.add_col(0.0, 0.0);
    let general_integer = m.add_int_col(0.0, 0.0);
    m.fix_col(fixed, 0.0);
    // Two independent three-binary half-integral equations leave two
    // fractional candidates in the root LP without triggering the simple
    // two-column parity presolve. Each equation is integer-infeasible, so the
    // whole model still closes only through case splits.
    m.add_row(1.5, 1.5, &[(x0, 1.0), (x1, 1.0), (x2, 1.0)]);
    m.add_row(1.5, 1.5, &[(y0, 1.0), (y1, 1.0), (y2, 1.0)]);
    let mut foreign = Model::new();
    let mut stale = foreign.add_binary_col();
    for _ in 0..m.num_cols() {
        stale = foreign.add_binary_col();
    }

    let mut session = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    // Every entry before `x1` is ineligible: stale, continuous, general
    // integer, or fixed. The two independent fractional candidates have equal
    // scores, so the first live preference among them must own the root split.
    session.hint_branch_order(&[
        stale,
        general_integer,
        continuous,
        fixed,
        x1,
        y1,
        y0,
        y2,
        x0,
        x2,
        x1,
    ]);
    match session.check().unwrap() {
        Outcome::Infeasible {
            tree_cert: Some(cert),
            ..
        } => {
            cert.verify(&m).unwrap();
            let TreeNode::Split { col, .. } = cert.root else {
                panic!("case-split-only model must have a split root");
            };
            assert_eq!(col, x1, "the first eligible equal-score hint must win");
        }
        other => panic!("expected certified Infeasible, got {other:?}"),
    }
}

/// The certificate is evidence about ONE model: against a feasible variant
/// (rhs 3/2 -> 1) it must refute. This is the live soundness probe — a tree
/// certificate that verified here would prove a feasible model infeasible.
#[test]
fn emitted_certificate_refutes_on_a_feasible_variant() {
    let (_, cert) = emitted_cert();
    let mut feasible = Model::new();
    let x = feasible.add_binary_col();
    let y = feasible.add_binary_col();
    let z = feasible.add_binary_col();
    feasible.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0), (z, 1.0)]);
    assert!(
        cert.verify(&feasible).is_err(),
        "a certificate for the 3/2 model must not verify against the feasible 1 model"
    );
}

// ---------------------------------------------------------------------------
// (b) Tamper battery, hand-built certificate: every failure mode lands on a
// DETERMINISTIC error variant.
//
// Model: binary x with rows `x >= 1/4` and `x <= 3/4` (LP point 1/2; no 0/1
// point). Tree: split x at 0 —
//   lo (x <= 0):  1·(x - 1/4 >= 0) + 1·(0 - x >= 0)  =  -1/4  (contradiction)
//   hi (x >= 1):  1·(3/4 - x >= 0) + 1·(x - 1 >= 0)  =  -1/4  (contradiction)
// ---------------------------------------------------------------------------

/// The model, its handles, and the hand-built certificate. `w` is an unused
/// CONTINUOUS column for the split-on-continuous tamper.
fn hand_built() -> (Model, MilpInfeasibilityCertificate) {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let _w = m.add_col(0.0, 1.0); // continuous; never split legitimately
    let r_lo = m.add_row(0.25, f64::INFINITY, &[(x, 1.0)]);
    let r_hi = m.add_row(f64::NEG_INFINITY, 0.75, &[(x, 1.0)]);
    let lo = TreeNode::Leaf {
        farkas: FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: r_lo,
                        side: BoundSide::Lower,
                    },
                    coeff: rat(1),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: x,
                        side: BoundSide::Upper,
                    },
                    coeff: rat(1),
                },
            ],
        },
    };
    let hi = TreeNode::Leaf {
        farkas: FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: r_hi,
                        side: BoundSide::Upper,
                    },
                    coeff: rat(1),
                },
                Multiplier {
                    fact: FactRef::ColBound {
                        col: x,
                        side: BoundSide::Lower,
                    },
                    coeff: rat(1),
                },
            ],
        },
    };
    let cert = MilpInfeasibilityCertificate {
        root: TreeNode::Split {
            col: x,
            cut: rat(0),
            lo: Box::new(lo),
            hi: Box::new(hi),
        },
    };
    (m, cert)
}

#[test]
fn hand_built_tree_certificate_verifies() {
    let (m, cert) = hand_built();
    cert.verify(&m).unwrap();
    assert_eq!(cert.num_leaves(), 2);
}

/// TAMPER 1 — non-integer cut. `lo: x <= 1/2` / `hi: x >= 3/2` would leave
/// the integer 1 covered by NEITHER branch: the narrowed-coverage attack.
#[test]
fn tamper_noninteger_cut_is_rejected() {
    let (m, mut cert) = hand_built();
    let TreeNode::Split { cut, .. } = &mut cert.root else {
        panic!("root is a split")
    };
    *cut = ratf(1, 2);
    assert!(matches!(
        cert.verify(&m),
        Err(CertificateError::InvalidSplit { index: 0, col: 0 })
    ));
}

/// TAMPER 2 — split on a CONTINUOUS column: `x <= cut ∪ x >= cut+1` does not
/// cover a continuous domain (the open interval between is lost).
#[test]
fn tamper_split_on_continuous_column_is_rejected() {
    let (m, mut cert) = hand_built();
    // Column 1 is the unused continuous `w`; steal its handle from a fresh
    // identical model (Col is opaque outside the crate).
    let mut twin = Model::new();
    let _x = twin.add_binary_col();
    let w = twin.add_col(0.0, 1.0);
    let TreeNode::Split { col, .. } = &mut cert.root else {
        panic!("root is a split")
    };
    *col = w;
    assert!(matches!(
        cert.verify(&m),
        Err(CertificateError::InvalidSplit { index: 0, col: 1 })
    ));
}

/// TAMPER 3 — scale one leaf multiplier: the combination's x-coefficient no
/// longer cancels to zero.
#[test]
fn tamper_scaled_leaf_multiplier_is_rejected() {
    let (m, mut cert) = hand_built();
    let TreeNode::Split { lo, .. } = &mut cert.root else {
        panic!("root is a split")
    };
    let TreeNode::Leaf { farkas } = lo.as_mut() else {
        panic!("lo is a leaf")
    };
    farkas.multipliers[0].coeff = rat(2);
    match cert.verify(&m) {
        Err(CertificateError::LeafRejected { index: 0, error }) => {
            assert!(matches!(
                *error,
                CertificateError::CoefficientMismatch { col: 0 }
            ));
        }
        other => panic!("expected LeafRejected(CoefficientMismatch), got {other:?}"),
    }
}

/// TAMPER 4 — non-positive multiplier: a Farkas combination may only scale
/// facts by strictly positive weights.
#[test]
fn tamper_nonpositive_multiplier_is_rejected() {
    let (m, mut cert) = hand_built();
    let TreeNode::Split { hi, .. } = &mut cert.root else {
        panic!("root is a split")
    };
    let TreeNode::Leaf { farkas } = hi.as_mut() else {
        panic!("hi is a leaf")
    };
    farkas.multipliers[1].coeff = rat(-1);
    match cert.verify(&m) {
        Err(CertificateError::LeafRejected { index: 1, error }) => {
            assert!(matches!(
                *error,
                CertificateError::NonpositiveMultiplier { index: 1 }
            ));
        }
        other => panic!("expected LeafRejected(NonpositiveMultiplier), got {other:?}"),
    }
}

/// TAMPER 5 — drop the split (replace the tree by one branch): the surviving
/// leaf is then priced at the MODEL's bounds, where its combination is
/// `x - 1/4 + 1 - x = 3/4 >= 0` — no contradiction.
#[test]
fn tamper_dropped_split_is_rejected() {
    let (m, mut cert) = hand_built();
    let TreeNode::Split { lo, .. } = &mut cert.root else {
        panic!("root is a split")
    };
    cert.root = (**lo).clone();
    match cert.verify(&m) {
        Err(CertificateError::LeafRejected { index: 0, error }) => {
            assert!(matches!(*error, CertificateError::NotContradictory));
        }
        other => panic!("expected LeafRejected(NotContradictory), got {other:?}"),
    }
}

/// TAMPER 6 — swap the branches: each leaf is checked under the OTHER side's
/// tightening, where its combination is positive.
#[test]
fn tamper_swapped_branches_are_rejected() {
    let (m, mut cert) = hand_built();
    let TreeNode::Split { lo, hi, .. } = &mut cert.root else {
        panic!("root is a split")
    };
    std::mem::swap(lo, hi);
    match cert.verify(&m) {
        Err(CertificateError::LeafRejected { index: 0, error }) => {
            assert!(matches!(*error, CertificateError::NotContradictory));
        }
        other => panic!("expected LeafRejected(NotContradictory), got {other:?}"),
    }
}

/// TAMPER 7 — empty leaf evidence: zero multipliers combine to `0 >= 0`,
/// which contradicts nothing.
#[test]
fn tamper_empty_leaf_is_rejected() {
    let (m, mut cert) = hand_built();
    let TreeNode::Split { lo, .. } = &mut cert.root else {
        panic!("root is a split")
    };
    **lo = TreeNode::Leaf {
        farkas: FarkasCertificate {
            multipliers: Vec::new(),
        },
    };
    match cert.verify(&m) {
        Err(CertificateError::LeafRejected { index: 0, error }) => {
            assert!(matches!(*error, CertificateError::NotContradictory));
        }
        other => panic!("expected LeafRejected(NotContradictory), got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// (b') Tamper battery on the EMITTED certificate — whatever tree shape the
// engine produced, mutations must fail verification.
// ---------------------------------------------------------------------------

/// The first leaf in walk order, mutable.
fn first_leaf_mut(node: &mut TreeNode) -> &mut FarkasCertificate {
    match node {
        TreeNode::Leaf { farkas } => farkas,
        TreeNode::Split { lo, .. } => first_leaf_mut(lo),
    }
}

#[test]
fn emitted_cert_tampers_all_fail() {
    let (m, original) = emitted_cert();

    // Mutate a leaf multiplier's coefficient.
    let mut t = original.clone();
    {
        let farkas = first_leaf_mut(&mut t.root);
        assert!(!farkas.multipliers.is_empty(), "a leaf carries multipliers");
        farkas.multipliers[0].coeff *= rat(2);
    }
    assert!(t.verify(&m).is_err(), "scaled multiplier must fail");

    // Drop a multiplier from a leaf.
    let mut t = original.clone();
    {
        let farkas = first_leaf_mut(&mut t.root);
        farkas.multipliers.pop();
    }
    assert!(t.verify(&m).is_err(), "dropped multiplier must fail");

    // Replace the whole tree by one of its leaves: a bare leaf at MODEL
    // bounds would be a root Farkas for an LP-feasible model — impossible.
    let mut t = original.clone();
    let leaf = first_leaf_mut(&mut t.root).clone();
    t.root = TreeNode::Leaf { farkas: leaf };
    assert!(t.verify(&m).is_err(), "leaf promoted to root must fail");

    // Shift the root split's cut by one: the branch that loses its
    // tightening now contains the relaxation's fractional points.
    if let TreeNode::Split { cut, .. } = &mut original.clone().root {
        let mut t = original.clone();
        let TreeNode::Split { cut: c, .. } = &mut t.root else {
            unreachable!()
        };
        *c = cut.clone() + rat(1);
        assert!(t.verify(&m).is_err(), "shifted cut must fail");
    }

    // De-integerize the root split's cut: coverage collapses structurally.
    let mut t = original.clone();
    if let TreeNode::Split { cut, .. } = &mut t.root {
        *cut += ratf(1, 2);
        assert!(
            matches!(t.verify(&m), Err(CertificateError::InvalidSplit { .. })),
            "non-integer cut must fail as InvalidSplit"
        );
    } else {
        panic!("emitted certificate for a case-split model must start with a split");
    }
}

// ---------------------------------------------------------------------------
// (c) Fail-closed: the leaf cap aborts capture, never the verdict.
// ---------------------------------------------------------------------------

#[test]
fn leaf_cap_fails_closed_and_verdict_is_unchanged() {
    let m = case_split_only_model();
    // A case split needs >= 2 leaves; a budget of 1 cannot hold it.
    match check(&m, &SolveOpts::new().with_tree_cert_leaves(1)) {
        Outcome::Infeasible { cert, tree_cert } => {
            assert!(cert.is_none());
            assert!(tree_cert.is_none(), "over-budget capture must fail closed");
        }
        other => panic!("expected Infeasible under cap 1, got {other:?}"),
    }
    // Budget 0 disables capture entirely.
    match check(&m, &SolveOpts::new().with_tree_cert_leaves(0)) {
        Outcome::Infeasible { cert, tree_cert } => {
            assert!(cert.is_none());
            assert!(tree_cert.is_none(), "capture disabled must yield None");
        }
        other => panic!("expected Infeasible with capture off, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// (d) Regressions: the classic root-LP Farkas lane and feasible solves.
// ---------------------------------------------------------------------------

#[test]
fn root_lp_infeasible_still_yields_classic_farkas() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    m.add_row(2.0, f64::INFINITY, &[(x, 1.0)]); // x >= 2 vs x <= 1
    match check(&m, &SolveOpts::new()) {
        Outcome::Infeasible { cert, .. } => {
            cert.expect("root-LP infeasibility is Farkas-certified")
                .verify(&m)
                .unwrap();
        }
        other => panic!("expected Infeasible, got {other:?}"),
    }
}

#[test]
fn feasible_decision_solve_is_unaffected() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
    match check(&m, &SolveOpts::new()) {
        Outcome::Feasible { model_values, .. } => {
            assert_eq!(model_values.len(), 2);
        }
        other => panic!("expected Feasible, got {other:?}"),
    }
}
