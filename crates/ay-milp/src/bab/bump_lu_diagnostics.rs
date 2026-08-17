// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential diagnostics for the simplex factorization lanes.

use crate::model::{Col, Model};
use crate::simplex::{Candidate, FloatLp, NbBound, SimplexStatus};

/// Structured result of the basis-factorization DIFFERENTIAL harness — the
/// FTRAN/BTRAN image agreement between two requested factorization lanes
/// (0 = PFI slot-order, 1 = Markowitz bump-LU, 2 = block-triangular bump-LU)
/// that factor the SAME basis by independent algorithms. Public so
/// `tests/bump_lu_diff.rs` can assert on the raw numbers.
pub struct BumpLuDiff {
    /// Max abs elementwise difference between the lanes' FTRAN (`B⁻¹·M_j`) images.
    pub ftran_diff: f64,
    /// Max abs elementwise difference between the lanes' BTRAN (rows of `B⁻¹`) images.
    pub btran_diff: f64,
    /// Singular-repair kick count per lane: `[lane0, lane1]`. A differential
    /// invariant — both lanes factor the same basis, so the counts must match.
    pub kicked: [usize; 2],
    /// Exact original-basis columns kicked on each lane. Equality is
    /// load-bearing: equal counts alone can conceal different basis repairs.
    pub kicked_columns: [Vec<usize>; 2],
    /// Sorted final basis-column sets after singular repair. This includes the
    /// logical replacement columns, so equal kick identities cannot conceal
    /// different repaired operators.
    pub final_basis_columns: [Vec<usize>; 2],
    /// Actual factorization provenance. `false` means PFI; `true` means the
    /// requested bump segment (monolithic or BTF) really ran. Merely requesting
    /// a lane is insufficient because its peel/floor gate can decline.
    pub bump_lu_used: [bool; 2],
    /// Eta-file fill per lane: `[lane0, lane1]`.
    pub fill: [usize; 2],
    /// TRUE when the two lanes assigned basis columns to DIFFERENT row slots
    /// (their post-refactorize basis orders differ). This is the case the
    /// column-keyed comparison exists to handle: a `true` here with `agree()`
    /// also true is direct evidence the harness compares the operator, not the
    /// arbitrary internal permutation.
    pub perm_differs: bool,
    /// Probe wall time per lane in seconds: `[lane0, lane1]`.
    pub secs: [f64; 2],
    /// FTRAN columns and BTRAN rows sampled.
    pub n_ftran: usize,
    pub n_btran: usize,
    /// Magnitude of the largest lane-0 image entry — a natural scale for a
    /// relative tolerance (`diff <= rel_tol * scale.max(1.0)`).
    pub scale: f64,
    /// The two factorization lanes compared: `[a, b]`. `[0, 1]` = PFI vs
    /// monolithic bump-LU (the default gate); `[1, 2]` = bump-LU vs the
    /// block-triangular (BTF) lane. Every `[..; 2]` field above is indexed to
    /// match (slot 0 = lane `a`, slot 1 = lane `b`).
    pub lanes: [u8; 2],
}

impl BumpLuDiff {
    /// The two lanes agree to floating-point noise AND kick identically — the
    /// harness self-validation predicate.
    pub fn agree(&self, rel_tol: f64) -> bool {
        if !rel_tol.is_finite()
            || rel_tol < 0.0
            || !self.scale.is_finite()
            || self.scale <= 0.0
            || !self.ftran_diff.is_finite()
            || self.ftran_diff < 0.0
            || !self.btran_diff.is_finite()
            || self.btran_diff < 0.0
            || self.n_ftran == 0
            || self.n_btran == 0
            || self
                .secs
                .iter()
                .any(|secs| !secs.is_finite() || *secs < 0.0)
        {
            return false;
        }
        let lanes_valid =
            self.lanes[0] <= 2 && self.lanes[1] <= 2 && self.lanes[0] != self.lanes[1];
        let expected_bump_used = [self.lanes[0] != 0, self.lanes[1] != 0];
        let strictly_increasing =
            |columns: &[usize]| columns.windows(2).all(|pair| pair[0] < pair[1]);
        let t = rel_tol * self.scale.max(1.0);
        t.is_finite()
            && lanes_valid
            && self.bump_lu_used == expected_bump_used
            && self.ftran_diff <= t
            && self.btran_diff <= t
            && self.kicked[0] == self.kicked[1]
            && self.kicked[0] == self.kicked_columns[0].len()
            && self.kicked[1] == self.kicked_columns[1].len()
            && strictly_increasing(&self.kicked_columns[0])
            && strictly_increasing(&self.kicked_columns[1])
            && self.kicked_columns[0] == self.kicked_columns[1]
            && !self.final_basis_columns[0].is_empty()
            && strictly_increasing(&self.final_basis_columns[0])
            && strictly_increasing(&self.final_basis_columns[1])
            && self.final_basis_columns[0] == self.final_basis_columns[1]
    }
}

/// Sample ~`want` indices spread evenly and deterministically over `src`.
fn bumpdiff_sample(src: &[usize], want: usize) -> Vec<usize> {
    if src.is_empty() {
        return Vec::new();
    }
    let want = want.min(src.len());
    (0..want).map(|k| src[k * src.len() / want]).collect()
}

/// Core of the differential harness: sample a test batch (~64 nonbasic columns'
/// raw `M_j` for FTRAN, ~8 basis columns whose dual `B⁻¹` rows the BTRAN
/// extracts), factor `cand`'s basis on BOTH trusted lanes, and return the image
/// agreement. Both batches are keyed by COLUMN identity so the comparison is
/// invariant to the per-lane basis permutation (see `factor_probe`). `None` on a
/// probe decline.
fn bump_lu_diff_core(lp: &FloatLp, cand: &Candidate, lanes: [u8; 2]) -> Option<BumpLuDiff> {
    if lanes[0] > 2 || lanes[1] > 2 || lanes[0] == lanes[1] {
        return None;
    }
    let basic: std::collections::HashSet<usize> = cand.basis.iter().copied().collect();
    if basic.len() != cand.basis.len() {
        return None;
    }
    let nb: Vec<usize> = (0..lp.cols).filter(|j| !basic.contains(j)).collect();
    let ftran_cols = bumpdiff_sample(&nb, 64);
    // BTRAN probes basis COLUMNS (their dual rows of B⁻¹), not raw row slots —
    // the two lanes permute the basis differently across row slots.
    let btran_cols = bumpdiff_sample(&cand.basis, 8);

    let p0 = lp.factor_probe(cand, &ftran_cols, &btran_cols, lanes[0])?;
    let p1 = lp.factor_probe(cand, &ftran_cols, &btran_cols, lanes[1])?;
    if [p0.bump_lu_used, p1.bump_lu_used] != [lanes[0] != 0, lanes[1] != 0] {
        return None;
    }
    let mut basis0 = p0.basis_order.clone();
    let mut basis1 = p1.basis_order.clone();
    basis0.sort_unstable();
    basis1.sort_unstable();

    let max_diff = |a: &[Vec<f64>], b: &[Vec<f64>]| -> Option<f64> {
        if a.len() != b.len() {
            return None;
        }
        let mut m = 0.0f64;
        for (va, vb) in a.iter().zip(b) {
            if va.len() != vb.len() {
                return None;
            }
            for (x, y) in va.iter().zip(vb) {
                let diff = (x - y).abs();
                if !diff.is_finite() {
                    return None;
                }
                m = m.max(diff);
            }
        }
        Some(m)
    };
    let max_mag = |a: &[Vec<f64>]| -> Option<f64> {
        a.iter()
            .flat_map(|v| v.iter())
            .try_fold(0.0f64, |m, &x| x.is_finite().then(|| m.max(x.abs())))
    };
    let ftran_diff = max_diff(&p0.ftran, &p1.ftran)?;
    let btran_diff = max_diff(&p0.btran, &p1.btran)?;
    let scale = max_mag(&p0.ftran)?.max(max_mag(&p0.btran)?);
    Some(BumpLuDiff {
        ftran_diff,
        btran_diff,
        kicked: [p0.kicked, p1.kicked],
        kicked_columns: [p0.kicked_columns, p1.kicked_columns],
        final_basis_columns: [basis0, basis1],
        bump_lu_used: [p0.bump_lu_used, p1.bump_lu_used],
        fill: [p0.fill, p1.fill],
        perm_differs: p0.basis_order != p1.basis_order,
        secs: [p0.secs, p1.secs],
        n_ftran: ftran_cols.len(),
        n_btran: btran_cols.len(),
        scale,
        lanes,
    })
}

/// Human name of a factorization lane, for the diff report.
fn lane_name(lane: u8) -> &'static str {
    match lane {
        0 => "PFI",
        1 => "bump-LU",
        2 => "BTF",
        _ => "?",
    }
}

fn bumpdiff_report(d: &BumpLuDiff, m: usize, cols: usize) -> String {
    let agree = d.agree(1e-6);
    format!(
        "diag bumpdiff: {} FTRAN cols + {} BTRAN basis-cols over m={m} cols={cols} (scale={:.3e})\n\
         lane{} ({:>7}): used_bump={} fill={} kicked={} {:?} secs={:.3}\n\
         lane{} ({:>7}): used_bump={} fill={} kicked={} {:?} secs={:.3}\n\
         basis permutation differs between lanes: {}\n\
         max FTRAN diff = {:.3e}\n\
         max BTRAN diff = {:.3e}\n\
         VERDICT: lanes {} (harness {})",
        d.n_ftran,
        d.n_btran,
        d.scale,
        d.lanes[0],
        lane_name(d.lanes[0]),
        d.bump_lu_used[0],
        d.fill[0],
        d.kicked[0],
        d.kicked_columns[0],
        d.secs[0],
        d.lanes[1],
        lane_name(d.lanes[1]),
        d.bump_lu_used[1],
        d.fill[1],
        d.kicked[1],
        d.kicked_columns[1],
        d.secs[1],
        d.perm_differs,
        d.ftran_diff,
        d.btran_diff,
        if agree { "AGREE" } else { "DISAGREE" },
        if agree {
            "TRUSTWORTHY"
        } else {
            "BROKEN — do not trust; a lane or the harness is WRONG"
        },
    )
}

/// DIFFERENTIAL-CORRECTNESS HARNESS for the basis factorization. Reload a dumped
/// root basis, then factor it through `refactorize` on BOTH trusted lanes —
/// lane 0 = PFI slot-order, lane 1 = Markowitz bump-LU — and compare the FTRAN
/// (`B⁻¹·M_j` for ~64 sampled nonbasic columns) and BTRAN (rows of `B⁻¹` for ~8
/// sampled rows) images. The two lanes factor the SAME basis by two independent
/// algorithms, so their images MUST agree to floating-point noise (~1e-9..1e-6);
/// a large diff means a lane — or this harness — is wrong. This self-validation
/// is also the trust gate used below for the opt-in block-triangular (BTF) lane.
///
/// Set `the bump-lu-min knob` low (e.g. 1) so lane 1 genuinely takes the bump-LU
/// path on a modest bump; peel activation needs a BIG LP or `the tri-crash-all knob`.
pub fn diag_bump_lu_diff(model: &Model, basis_path: &str) -> String {
    let text = match std::fs::read_to_string(basis_path) {
        Ok(t) => t,
        Err(e) => return format!("diag bumpdiff: cannot read {basis_path}: {e}"),
    };
    let mut lines = text.lines();
    let cols: usize = match lines.next().and_then(|l| l.trim().parse().ok()) {
        Some(c) => c,
        None => return "diag bumpdiff: bad header".to_string(),
    };
    let basis: Vec<usize> = match lines
        .next()
        .unwrap_or_default()
        .split_whitespace()
        .map(str::parse)
        .collect()
    {
        Ok(basis) => basis,
        Err(_) => return "diag bumpdiff: malformed basis column".to_string(),
    };
    let at: Vec<NbBound> = match lines
        .next()
        .unwrap_or_default()
        .split_whitespace()
        .map(|token| match token {
            "0" => Ok(NbBound::Lower),
            "1" => Ok(NbBound::Upper),
            "2" => Ok(NbBound::Zero),
            _ => Err(()),
        })
        .collect()
    {
        Ok(at) => at,
        Err(()) => return "diag bumpdiff: malformed nonbasic-bound tag".to_string(),
    };
    let objective: Vec<(u32, f64)> = (0..model.num_cols())
        .map(|j| (j as u32, model.obj_coeff(Col(j as u32))))
        .filter(|&(_, a)| a != 0.0)
        .collect();
    let Some(lp) = FloatLp::from_model(model, &objective, model.sense()) else {
        return "diag: model cannot be lowered".to_string();
    };
    if cols != lp.cols || at.len() != lp.cols || basis.len() != lp.m {
        return format!(
            "diag bumpdiff: shape mismatch (file cols={cols} basis={} at={}; lp cols={} m={})",
            basis.len(),
            at.len(),
            lp.cols,
            lp.m
        );
    }

    let cand = Candidate {
        basis,
        at,
        values: Vec::new(),
        duals: Vec::new(),
        farkas: Vec::new(),
        farkas_verified: false,
        status: SimplexStatus::Optimal,
    };
    // Which two lanes to compare. Default `0,1` (PFI vs monolithic bump-LU),
    // the harness self-validation; set `--bumpdiff-lanes,2` to compare
    // the monolithic bump-LU against the block-triangular (BTF) lane.
    let lanes = bumpdiff_lanes_env();
    match bump_lu_diff_core(&lp, &cand, lanes) {
        Some(d) => bumpdiff_report(&d, lp.m, lp.cols),
        None => "diag bumpdiff: probe declined (bad sample index)".to_string(),
    }
}

/// The lane pair `--bumpdiff-lanes` selects for the `bumpdiff` diagnostic,
/// as `"a,b"` (default `"0,1"`). Any parse miss falls back to `[0, 1]`.
fn bumpdiff_lanes_env() -> [u8; 2] {
    // B40: encoded a*10+b on the caller layer (`--bumpdiff-lanes a,b`).
    crate::tune::count_opt(crate::tune::Knob::BumpdiffLanes)
        .and_then(|enc| {
            let (a, b) = ((enc / 10) as u8, (enc % 10) as u8);
            match (Some(a), Some(b), Option::<u8>::None) {
                (Some(a), Some(b), None) if a <= 2 && b <= 2 && a != b => Some([a, b]),
                _ => None,
            }
        })
        .unwrap_or([0, 1])
}

/// The differential harness driven from a MODEL directly (no basis-file round
/// trip): solve the root LP relaxation for a Candidate basis, then run the two
/// trusted factorization lanes and return the structured agreement. This is the
/// public entry point the CI unit test drives — it needs `the tri-crash-all knob`
/// (peel active on a small LP) and a low `the bump-lu-min knob` so lane 1 takes
/// the bump-LU path. `Err` if the root LP does not solve or the probe declines.
pub fn bump_lu_diff_on_model(model: &Model, secs: f64) -> Result<BumpLuDiff, String> {
    bump_lu_diff_on_model_lanes(model, secs, [0, 1])
}

/// As `bump_lu_diff_on_model`, but comparing an ARBITRARY pair of factorization
/// lanes (`0` = PFI, `1` = monolithic bump-LU, `2` = block-triangular BTF). The
/// BTF unit test drives this with `[1, 2]` to guard lane 2 against the trusted
/// lane 1 on a genuine multi-block bump.
pub fn bump_lu_diff_on_model_lanes(
    model: &Model,
    secs: f64,
    lanes: [u8; 2],
) -> Result<BumpLuDiff, String> {
    use std::time::{Duration, Instant};
    if lanes[0] > 2 || lanes[1] > 2 || lanes[0] == lanes[1] {
        return Err("factorization lanes must be distinct values in 0..=2".to_string());
    }
    if !secs.is_finite() || secs <= 0.0 || secs >= u64::MAX as f64 {
        return Err("time budget must be finite, positive, and representable".to_string());
    }
    let objective: Vec<(u32, f64)> = (0..model.num_cols())
        .map(|j| (j as u32, model.obj_coeff(Col(j as u32))))
        .filter(|&(_, a)| a != 0.0)
        .collect();
    let Some(lp) = FloatLp::from_model(model, &objective, model.sense()) else {
        return Err("model cannot be lowered".to_string());
    };
    let duration = Duration::from_secs_f64(secs);
    let deadline = Instant::now()
        .checked_add(duration)
        .ok_or_else(|| "time budget exceeds the platform Instant range".to_string())?;
    let cand = lp.solve_bounded(&lp.lower, &lp.upper, None, Some(deadline));
    if cand.status != SimplexStatus::Optimal {
        return Err(format!("root LP {:?} (not Optimal)", cand.status));
    }
    bump_lu_diff_core(&lp, &cand, lanes)
        .ok_or_else(|| "probe declined (bad sample index)".to_string())
}
