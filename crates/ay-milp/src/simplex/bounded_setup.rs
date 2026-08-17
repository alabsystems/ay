// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) struct ChainCensus {
    pub(super) equalities: usize,
    pub(super) peeled: usize,
    pub(super) candidate: bool,
    pub(super) is_chain: bool,
    pub(super) trace: bool,
}

/// Restore the identity operator only for a cold solve whose cached LU belongs
/// to another basis. Warm solves deliberately retain it for `warm_start`.
pub(super) fn reset_cached_lu_basis(lp: &FloatLp, sx: &mut Simplex, cold: bool) {
    let Some(cache) = sx.lu.as_mut() else {
        return;
    };
    if cold
        && cache
            .rep_basis
            .iter()
            .enumerate()
            .any(|(r, &j)| j != lp.n + r)
    {
        cache.eng.reset_to_identity();
        cache.rep_basis.clear();
        cache.rep_basis.extend(lp.n..lp.n + lp.m);
    }
    sx.sync_lu_counters();
}

/// Classify a cold eta-path LP once. State 3 arms the chain rescue; state 2
/// records a completed negative classification.
pub(super) fn classify_chain_shape(lp: &FloatLp, sx: &Simplex, cold: bool) -> Option<ChainCensus> {
    if !cold
        || sx.lu.is_some()
        || no_tri_crash()
        || lp.chain_shape.get() != 0
        || (lp.cols >= BIG_LP_COLS && lp.m >= BIG_LP_ROWS)
    {
        return None;
    }

    let candidate = chain_shape_enabled() && lp.m >= TALL_LU_ROWS && lp.n < DEVEX_WIDTH * lp.m;
    let emit_census = shape_census_enabled() && trace_enabled();
    let (equalities, peeled) = if candidate || emit_census {
        lp.chain_peel_census(&sx.lo, &sx.up)
    } else {
        (0, 0)
    };
    // Equality rows must carry real mass and peel near-completely. The bar is
    // deliberately high: this bundle targets near-triangular chains, not LPs
    // that merely contain some equalities.
    let is_chain = candidate && equalities * 4 >= lp.m && peeled * 16 >= equalities * 15;
    let trace = (candidate || emit_census) && trace_enabled();
    Some(ChainCensus {
        equalities,
        peeled,
        candidate,
        is_chain,
        trace,
    })
}
