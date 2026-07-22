// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scratch: how good a primal solution is REACHABLE on the benchmark instance by local
//! search alone? The B&B's heuristics stall at 257 on 80x60 where HiGHS reports 267. Before
//! designing a fix, measure the ceiling: run an unapologetically thorough ruin-and-recreate
//! search in floats and see what it finds. If this can't reach 267 either, the gap is not in
//! the primal heuristic and I should stop looking there.
//!
//! ```text
//! cargo run --release -p ay-milp --example milp_ls -- 80 60
//! ```

use std::time::Instant;

use ay_milp::{Col, Model, Row, Sense};

struct Rng(u64);
impl Rng {
    fn next_u32(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (self.0 >> 33) as u32
    }
    fn coeff(&mut self) -> f64 {
        f64::from(self.next_u32() % 9) - 4.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next_u32() as usize) % n.max(1)
    }
    fn unit(&mut self) -> f64 {
        f64::from(self.next_u32() % 1_000_000) / 1_000_000.0
    }
}

fn build(n: usize, m: usize, seed: u64) -> (Model, Vec<Col>, Vec<Row>) {
    let mut rng = Rng(seed);
    let mut model = Model::new();
    let cols: Vec<_> = (0..n).map(|_| model.add_binary_col()).collect();
    let mut rows = Vec::new();
    for _ in 0..m {
        let terms: Vec<_> = cols
            .iter()
            .filter_map(|&c| {
                let a = rng.coeff();
                (a != 0.0).then_some((c, a))
            })
            .collect();
        if terms.is_empty() {
            continue;
        }
        let b = f64::from(rng.next_u32() % 12) + 3.0;
        rows.push(model.add_row(f64::NEG_INFINITY, b, &terms));
    }
    let obj: Vec<_> = cols
        .iter()
        .map(|&c| (c, f64::from(rng.next_u32() % 10) + 1.0))
        .collect();
    model.set_objective(&obj, Sense::Maximize);
    (model, cols, rows)
}

/// The instance in the shape a flip-based search wants: for each column, the rows it touches.
struct Inst {
    n: usize,
    m: usize,
    obj: Vec<f64>,
    /// per column: (row, coeff)
    col: Vec<Vec<(usize, f64)>>,
    ub: Vec<f64>,
}

impl Inst {
    fn new(model: &Model, cols: &[Col], rows: &[Row]) -> Self {
        let mut col = vec![Vec::new(); cols.len()];
        let mut ub = Vec::new();
        for (i, &r) in rows.iter().enumerate() {
            let (coeffs, _, u) = model.row(r);
            for &(c, a) in coeffs {
                col[c as usize].push((i, a));
            }
            ub.push(u);
        }
        Self {
            n: cols.len(),
            m: rows.len(),
            obj: cols.iter().map(|&c| model.obj_coeff(c)).collect(),
            col,
            ub,
        }
    }
}

/// A point plus the row activities it induces, so a flip costs only its own column.
struct Pt<'a> {
    inst: &'a Inst,
    x: Vec<bool>,
    act: Vec<f64>,
    val: f64,
}

impl<'a> Pt<'a> {
    fn empty(inst: &'a Inst) -> Self {
        Self {
            inst,
            x: vec![false; inst.n],
            act: vec![0.0; inst.m],
            val: 0.0,
        }
    }
    /// Can column `j` be turned on (or off) without breaking a row it touches?
    fn fits(&self, j: usize, on: bool) -> bool {
        if self.x[j] == on {
            return true;
        }
        let s = if on { 1.0 } else { -1.0 };
        self.inst.col[j]
            .iter()
            .all(|&(r, a)| self.act[r] + s * a <= self.inst.ub[r] + 1e-9)
    }
    fn set(&mut self, j: usize, on: bool) {
        if self.x[j] == on {
            return;
        }
        let s = if on { 1.0 } else { -1.0 };
        for &(r, a) in &self.inst.col[j] {
            self.act[r] += s * a;
        }
        self.val += s * self.inst.obj[j];
        self.x[j] = on;
    }
    fn feasible(&self) -> bool {
        (0..self.inst.m).all(|r| self.act[r] <= self.inst.ub[r] + 1e-9)
    }
}

/// Greedy fill in the given order: take every column that still fits.
fn fill(p: &mut Pt<'_>, order: &[usize]) {
    for &j in order {
        if !p.x[j] && p.inst.obj[j] > 0.0 && p.fits(j, true) {
            p.set(j, true);
        }
    }
}

/// Descend on 1-1 swaps and 1-flips until nothing improves. Unlike the shipped `swap_improve`
/// this does not stop after a fixed number of moves, and it takes the BEST swap, not the first.
fn descend(p: &mut Pt<'_>, order: &[usize]) {
    loop {
        fill(p, order);
        let on: Vec<usize> = (0..p.inst.n).filter(|&j| p.x[j]).collect();
        let off: Vec<usize> = (0..p.inst.n).filter(|&j| !p.x[j]).collect();
        let mut best: Option<(f64, usize, usize)> = None;
        for &out in &on {
            p.set(out, false);
            for &inn in &off {
                let gain = p.inst.obj[inn] - p.inst.obj[out];
                if gain <= 1e-9 || best.as_ref().is_some_and(|&(g, _, _)| gain <= g) {
                    continue;
                }
                if p.fits(inn, true) {
                    p.set(inn, true);
                    if p.feasible() {
                        best = Some((gain, out, inn));
                    }
                    p.set(inn, false);
                }
            }
            p.set(out, true);
        }
        match best {
            Some((_, out, inn)) => {
                p.set(out, false);
                p.set(inn, true);
            }
            None => return,
        }
    }
}

/// Tabu search over 1-flips. The hill-climb above cannot leave a local optimum: once the point
/// is filled, EVERY feasible move is a drop, and every drop loses objective. So allow the
/// worsening move -- take the best non-tabu flip whatever its sign, forbid re-flipping that
/// column for a while, and remember the best point ever seen.
fn tabu(inst: &Inst, start: &[bool], iters: u64, tenure: usize, rng: &mut Rng) -> (Vec<bool>, f64) {
    let mut p = Pt::empty(inst);
    for (j, &on) in start.iter().enumerate() {
        if on {
            p.set(j, true);
        }
    }
    let mut best = p.x.clone();
    let mut best_val = p.val;
    let mut until = vec![0u64; inst.n];
    for it in 1..=iters {
        let mut pick: Option<(f64, usize, bool)> = None;
        for j in 0..inst.n {
            let on = !p.x[j];
            if on && !p.fits(j, true) {
                continue; // adding it would break a row
            }
            let delta = if on { inst.obj[j] } else { -inst.obj[j] };
            // Aspiration: a move that beats the best point ever is taken even if tabu.
            let tabu = until[j] > it && p.val + delta <= best_val + 1e-9;
            if tabu {
                continue;
            }
            let score = delta + 1e-6 * rng.unit(); // break ties randomly
            if pick.as_ref().is_none_or(|&(s, _, _)| score > s) {
                pick = Some((score, j, on));
            }
        }
        let Some((_, j, on)) = pick else {
            // Every move is tabu. Forget the list rather than give up -- a stalled tabu search
            // that breaks here does ~40 flips and reports a hill-climb's answer.
            until.iter_mut().for_each(|u| *u = 0);
            continue;
        };
        p.set(j, on);
        until[j] = it + tenure as u64 + rng.below(tenure) as u64;
        if p.val > best_val + 1e-9 {
            best_val = p.val;
            best = p.x.clone();
        }
    }
    (best, best_val)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(80);
    let m: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(60);
    let secs: f64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(10.0);

    let (model, cols, rows) = build(n, m, 2_026);
    let inst = Inst::new(&model, &cols, &rows);
    let mut rng = Rng(12_345);

    // Baseline: exactly what the solver's heuristic does -- greedy by objective coefficient.
    let mut by_obj: Vec<usize> = (0..inst.n).collect();
    by_obj.sort_by(|&a, &b| inst.obj[b].partial_cmp(&inst.obj[a]).unwrap());
    let mut p = Pt::empty(&inst);
    fill(&mut p, &by_obj);
    println!("greedy by objective      : {}", p.val);
    descend(&mut p, &by_obj);
    println!("+ full 1-1 swap descent  : {}", p.val);

    // Ruin and recreate, keeping the best point ever seen.
    let mut best = p.x.clone();
    let mut best_val = p.val;
    let t0 = Instant::now();
    let mut iters = 0u64;
    while t0.elapsed().as_secs_f64() < secs {
        iters += 1;
        let mut q = Pt::empty(&inst);
        for j in 0..inst.n {
            if best[j] {
                q.set(j, true);
            }
        }
        // Ruin: drop a random handful of the columns that are on.
        let on: Vec<usize> = (0..inst.n).filter(|&j| q.x[j]).collect();
        let k = 1 + rng.below(on.len().max(1) / 2 + 2);
        for _ in 0..k {
            if on.is_empty() {
                break;
            }
            q.set(on[rng.below(on.len())], false);
        }
        // Recreate: greedy in a randomly perturbed value order, then descend.
        let mut order: Vec<usize> = (0..inst.n).collect();
        let noise: Vec<f64> = (0..inst.n).map(|_| rng.unit()).collect();
        order.sort_by(|&a, &b| {
            let ka = inst.obj[b] * (0.75 + 0.5 * noise[b]);
            let kb = inst.obj[a] * (0.75 + 0.5 * noise[a]);
            ka.partial_cmp(&kb).unwrap()
        });
        descend(&mut q, &order);
        if q.val > best_val + 1e-9 {
            best_val = q.val;
            best = q.x.clone();
            println!(
                "  {:6.2}s  iter {iters:6}  -> {best_val}",
                t0.elapsed().as_secs_f64()
            );
        }
    }
    println!("ruin-and-recreate ({iters} iters): {best_val}");

    // Tabu, restarted from the best point each time it stalls.
    let t1 = Instant::now();
    let mut rounds = 0u64;
    while t1.elapsed().as_secs_f64() < secs {
        rounds += 1;
        let tenure = 5 + rng.below(inst.n / 4);
        let (x, v) = tabu(&inst, &best, 20_000, tenure, &mut rng);
        if v > best_val + 1e-9 {
            best_val = v;
            best = x;
            println!(
                "  tabu {:6.2}s round {rounds:4} -> {best_val}",
                t1.elapsed().as_secs_f64()
            );
        }
    }
    println!("tabu ({rounds} rounds): {best_val}");
}
