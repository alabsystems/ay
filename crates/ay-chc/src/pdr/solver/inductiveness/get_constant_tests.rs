// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::solver::PdrSolver;
use crate::ChcExpr;

#[test]
fn test_get_constant_bitvec_fits_i64() {
    let expr = ChcExpr::BitVec(42, 32);
    assert_eq!(PdrSolver::get_constant(&expr), Some(42));
}

#[test]
fn test_get_constant_wide_bitvec_rejected() {
    let expr = ChcExpr::BitVec(42, 64);
    assert_eq!(PdrSolver::get_constant(&expr), None);
}
