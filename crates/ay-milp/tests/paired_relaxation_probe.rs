// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Measurement probe (ignored by default): the paired-difference ReLU root
//! relaxation shape NY builds for relational ACAS Xu properties (NY
//! the development design notes: its 2,102 x 9,237 source row ran
//! 0 of 10 objectives in 89 s). Run:
//! `targo --unverified test --release -p ay-milp --test paired_relaxation_probe
//! -- --ignored --nocapture`. Two copies of
//! a 5-input, 6x50 ReLU network, triangle relaxations with interval boxes on
//! every variable, an input relation, and difference variables coupled by
//! equalities and difference rows. Ten objectives: min/max of each output
//! difference. Prints per-objective wall time for the float-dual and the
//! rigorous-bound queries.

use std::time::{Duration, Instant};

use ay_milp::{Col, LpSession, Model, Outcome, Sense, SolveOpts};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> f64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        ((x.wrapping_mul(0x2545_F491_4F6C_DD1D) >> 11) as f64) / (1u64 << 53) as f64
    }
    fn normal(&mut self) -> f64 {
        let u = self.next().max(1e-12);
        let v = self.next();
        (-2.0 * u.ln()).sqrt() * (std::f64::consts::TAU * v).cos()
    }
}

struct Layer {
    w: Vec<Vec<f64>>,
    b: Vec<f64>,
}

fn network(rng: &mut Rng, widths: &[usize]) -> Vec<Layer> {
    widths
        .windows(2)
        .map(|pair| {
            let (fan_in, fan_out) = (pair[0], pair[1]);
            let scale = 1.0 / (fan_in as f64).sqrt();
            Layer {
                w: (0..fan_out)
                    .map(|_| (0..fan_in).map(|_| rng.normal() * scale).collect())
                    .collect(),
                b: (0..fan_out).map(|_| rng.normal() * 0.05).collect(),
            }
        })
        .collect()
}

/// Interval bounds of one affine map over a box.
fn affine_box(layer: &Layer, lo: &[f64], hi: &[f64]) -> (Vec<f64>, Vec<f64>) {
    let mut out_lo = Vec::new();
    let mut out_hi = Vec::new();
    for (row, b) in layer.w.iter().zip(&layer.b) {
        let (mut l, mut u) = (*b, *b);
        for (w, (a, c)) in row.iter().zip(lo.iter().zip(hi)) {
            if *w >= 0.0 {
                l += w * a;
                u += w * c;
            } else {
                l += w * c;
                u += w * a;
            }
        }
        out_lo.push(l);
        out_hi.push(u);
    }
    (out_lo, out_hi)
}

/// Build the paired relaxation. Returns the model and the output-difference
/// columns.
fn paired_relaxation(seed: u64, eps: f64) -> (Model, Vec<Col>) {
    let mut rng = Rng(seed | 1);
    let widths = [5, 50, 50, 50, 50, 50, 50, 5];
    let net = network(&mut rng, &widths);
    let mut m = Model::new();
    // Copy A input box, copy B input = A + delta, delta in [-eps, eps].
    let in_lo = vec![-0.5; 5];
    let in_hi = vec![0.5; 5];
    let xa: Vec<Col> = (0..5).map(|i| m.add_col(in_lo[i], in_hi[i])).collect();
    let xb: Vec<Col> = (0..5)
        .map(|i| m.add_col(in_lo[i] - eps, in_hi[i] + eps))
        .collect();
    for i in 0..5 {
        let delta = m.add_col(-eps, eps);
        m.add_row(0.0, 0.0, &[(xb[i], 1.0), (xa[i], -1.0), (delta, -1.0)]);
    }
    let mut lo_a = in_lo.clone();
    let mut hi_a = in_hi.clone();
    let mut lo_b: Vec<f64> = in_lo.iter().map(|v| v - eps).collect();
    let mut hi_b: Vec<f64> = in_hi.iter().map(|v| v + eps).collect();
    let (mut prev_a, mut prev_b) = (xa, xb);
    // Difference of the previous layer's outputs, d = prev_a - prev_b.
    let mut prev_d: Vec<Col> = Vec::new();
    let mut d_lo = vec![-eps; 5];
    let mut d_hi = vec![eps; 5];
    for i in 0..5 {
        let d = m.add_col(-eps, eps);
        m.add_row(0.0, 0.0, &[(d, 1.0), (prev_a[i], -1.0), (prev_b[i], 1.0)]);
        prev_d.push(d);
    }
    let last = net.len() - 1;
    let mut outputs = Vec::new();
    for (k, layer) in net.iter().enumerate() {
        let (hla, hua) = affine_box(layer, &lo_a, &hi_a);
        let (hlb, hub) = affine_box(layer, &lo_b, &hi_b);
        // Difference pre-activation box: W applied to the difference box.
        let zero = Layer {
            w: layer.w.clone(),
            b: vec![0.0; layer.b.len()],
        };
        let (dhl, dhu) = affine_box(&zero, &d_lo, &d_hi);
        let mut next_a = Vec::new();
        let mut next_b = Vec::new();
        let mut next_d = Vec::new();
        let (mut nla, mut nua, mut nlb, mut nub, mut ndl, mut ndu) =
            (vec![], vec![], vec![], vec![], vec![], vec![]);
        for (j, (row, b)) in layer.w.iter().zip(&layer.b).enumerate() {
            let ha = m.add_col(hla[j], hua[j]);
            let hb = m.add_col(hlb[j], hub[j]);
            let dh = m.add_col(dhl[j], dhu[j]);
            // ha = W prev_a + b ; hb = W prev_b + b ; dh = W prev_d
            let mut ra: Vec<(Col, f64)> = prev_a.iter().zip(row).map(|(&c, &w)| (c, w)).collect();
            ra.push((ha, -1.0));
            m.add_row(-b, -b, &ra);
            let mut rb: Vec<(Col, f64)> = prev_b.iter().zip(row).map(|(&c, &w)| (c, w)).collect();
            rb.push((hb, -1.0));
            m.add_row(-b, -b, &rb);
            let mut rd: Vec<(Col, f64)> = prev_d.iter().zip(row).map(|(&c, &w)| (c, w)).collect();
            rd.push((dh, -1.0));
            m.add_row(0.0, 0.0, &rd);
            // dh = ha - hb (the authored consistency equality)
            m.add_row(0.0, 0.0, &[(dh, 1.0), (ha, -1.0), (hb, 1.0)]);
            if k == last {
                next_a.push(ha);
                next_b.push(hb);
                next_d.push(dh);
                outputs.push(dh);
                nla.push(hla[j]);
                nua.push(hua[j]);
                nlb.push(hlb[j]);
                nub.push(hub[j]);
                ndl.push(dhl[j]);
                ndu.push(dhu[j]);
                continue;
            }
            // Triangle relaxations of both copies.
            let relu = |m: &mut Model, h: Col, l: f64, u: f64| -> (Col, f64, f64) {
                if l >= 0.0 {
                    let y = m.add_col(l, u);
                    m.add_row(0.0, 0.0, &[(y, 1.0), (h, -1.0)]);
                    (y, l, u)
                } else if u <= 0.0 {
                    let y = m.add_col(0.0, 0.0);
                    (y, 0.0, 0.0)
                } else {
                    let y = m.add_col(0.0, u);
                    m.add_row(0.0, f64::INFINITY, &[(y, 1.0), (h, -1.0)]);
                    let s = u / (u - l);
                    m.add_row(f64::NEG_INFINITY, -s * l, &[(y, 1.0), (h, -s)]);
                    (y, 0.0, u)
                }
            };
            let (ya, yla, yua) = relu(&mut m, ha, hla[j], hua[j]);
            let (yb, ylb, yub) = relu(&mut m, hb, hlb[j], hub[j]);
            // Difference of post-activations, with the standard ReLU-difference
            // rows: dy between min(dh,0) and max(dh,0), and dy = ya - yb.
            let lo = (yla - yub).max(dhl[j].min(0.0));
            let hi = (yua - ylb).min(dhu[j].max(0.0));
            let dy = m.add_col(lo.min(hi), hi.max(lo));
            m.add_row(0.0, 0.0, &[(dy, 1.0), (ya, -1.0), (yb, 1.0)]);
            if dhl[j] < 0.0 && dhu[j] > 0.0 {
                // dy <= max(dh, 0) relaxed by its chord, dy >= min(dh, 0) likewise.
                let s = dhu[j] / (dhu[j] - dhl[j]);
                m.add_row(f64::NEG_INFINITY, -s * dhl[j], &[(dy, 1.0), (dh, -s)]);
                m.add_row(s * dhl[j], f64::INFINITY, &[(dy, 1.0), (dh, -(1.0 - s))]);
                m.add_row(f64::NEG_INFINITY, dhu[j].max(0.0), &[(dy, 1.0)]);
                m.add_row(dhl[j].min(0.0), f64::INFINITY, &[(dy, 1.0)]);
            } else if dhl[j] >= 0.0 {
                m.add_row(0.0, f64::INFINITY, &[(dy, 1.0)]);
                m.add_row(f64::NEG_INFINITY, 0.0, &[(dy, 1.0), (dh, -1.0)]);
            } else {
                m.add_row(f64::NEG_INFINITY, 0.0, &[(dy, 1.0)]);
                m.add_row(0.0, f64::INFINITY, &[(dy, 1.0), (dh, -1.0)]);
            }
            next_a.push(ya);
            next_b.push(yb);
            next_d.push(dy);
            nla.push(yla);
            nua.push(yua);
            nlb.push(ylb);
            nub.push(yub);
            ndl.push(lo.min(hi));
            ndu.push(hi.max(lo));
        }
        prev_a = next_a;
        prev_b = next_b;
        prev_d = next_d;
        (lo_a, hi_a, lo_b, hi_b, d_lo, d_hi) = (nla, nua, nlb, nub, ndl, ndu);
    }
    (m, outputs)
}

#[test]
#[ignore = "measurement probe; run with --ignored --nocapture in release"]
fn paired_relaxation_probe_times_ten_objectives() {
    for seed in [7u64, 11, 13] {
        let (model, outputs) = paired_relaxation(seed, 0.02);
        let nnz: usize = (0..model.num_rows())
            .map(|r| model.row(model.row_at(r).expect("row")).0.len())
            .sum();
        eprintln!(
            "PROBE seed {seed}: {} cols, {} rows, {} nnz",
            model.num_cols(),
            model.num_rows(),
            nnz
        );
        let opts = SolveOpts::new().with_time_limit(Duration::from_secs(60));
        let mut session = LpSession::new(&model, &opts).expect("continuous");
        for &out in &outputs {
            for sense in [Sense::Minimize, Sense::Maximize] {
                let start = Instant::now();
                let duals = session
                    .float_dual_for_expr(&[(out, 1.0)], sense)
                    .expect("valid form");
                let float_t = start.elapsed();
                let start = Instant::now();
                let bound = session
                    .rigorous_bound_expr(&[(out, 1.0)], sense)
                    .expect("valid");
                let bound_t = start.elapsed();
                let shown = match &bound {
                    Outcome::Bound { dual_bound, .. } => {
                        format!(
                            "{:.6}",
                            num_traits::ToPrimitive::to_f64(dual_bound).unwrap_or(f64::NAN)
                        )
                    }
                    other => format!("{other:?}").chars().take(60).collect(),
                };
                eprintln!(
                    "PROBE   out {:?} {sense:?}: float {float_t:?} (duals {}), rigorous {bound_t:?} -> {shown}",
                    out,
                    duals.is_some()
                );
            }
        }
    }
}

#[test]
#[ignore = "measurement probe; run with --ignored --nocapture in release"]
fn paired_relaxation_probe_cold_fresh_sessions() {
    ay_milp::enable_iter_ledger();
    let (model, outputs) = paired_relaxation(7, 0.02);
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs(60));
    for &out in outputs.iter().take(2) {
        for sense in [Sense::Minimize, Sense::Maximize] {
            let mut session = LpSession::new(&model, &opts).expect("continuous");
            let before = ay_milp::iter_ledger_line();
            let start = Instant::now();
            let duals = session
                .float_dual_for_expr(&[(out, 1.0)], sense)
                .expect("valid form");
            eprintln!(
                "COLD out {out:?} {sense:?}: fresh-session float {:?} (duals {})",
                start.elapsed(),
                duals.is_some()
            );
            eprintln!("COLD   ledger before: {before}");
            eprintln!("COLD   ledger after:  {}", ay_milp::iter_ledger_line());
        }
    }
}
