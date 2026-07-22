// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SOUND clique-local-search witness finder for FRB / Model RB decision instances.
//!
//! Model RB / FRB instances (the `mgd` PB-COMP encoding) are *forced-satisfiable* but
//! provably defeat complete resolution-style search (2^Ω(n) refutation width). PB-COMP DEC
//! only needs a **witness**, and finding one is empirically cheap with stochastic local
//! search — the catch is the bloated dual one-hot+log encoding. This module:
//!
//! 1. Detects the mgd-FRB signature (one-hot blocks + binary nogoods + conjunction-aux
//!    `+a +b -2c >= 0` + support `sum c >= 1`), refusing everything else (so non-FRB
//!    instances pay nothing and cannot regress).
//! 2. Reduces the binary CSP to **max-clique** on the compatibility graph (vertices =
//!    one-hot (var,value) pairs; an edge connects different-block vertices iff their values
//!    are compatible — not a nogood, and on a support-edge an allowed tuple). A clique of
//!    size = #blocks selects one compatible value per CSP variable = a CSP solution.
//! 3. Runs many parallel clique local searches with configuration checking; the first to
//!    find a full clique extends it to a complete model (via the SAT encoding, which fixes
//!    the determined log/aux) and **verifies it against the original PB constraints**.
//!
//! Soundness is unconditional: a returned assignment is checked by
//! [`crate::verify_all_constraints`], so a wrong SAT is impossible — the search can only
//! fail to find a witness (returning `None`), never fabricate one.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;
use std::time::Instant;

use crate::encoding::CnfEncoder;
use crate::eval::verify_all_constraints;
use crate::types::{PbInstance, PbRel, PbTerm};

/// Xorshift64* RNG (deterministic per seed, no external dependency).
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed | 1)
    }
    #[inline]
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    #[inline]
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % (n as u64)) as usize
    }
}

#[inline]
fn unit_pos(t: &PbTerm) -> bool {
    t.lits.len() == 1 && !t.lits[0].negated
}

/// The extracted binary-CSP structure of an mgd-FRB instance.
struct FrbStructure {
    /// Original (1-based) var indices for the one-hot vertices, compactly numbered.
    /// (The vertex->block map is consumed during the adjacency build and not kept:
    /// the search walks `adj` only and `extend_and_verify` needs just `verts`.)
    verts: Vec<usize>,
    /// Number of CSP variables (exactly-one blocks) = target clique size.
    nblk: usize,
    /// Adjacency bitset (`nv * words`), row-major; bit w of row v set iff v—w compatible.
    adj: Vec<u64>,
    words: usize,
    nv: usize,
}

/// Cheap structural gate (O(constraints), NO graph build): does this instance carry the
/// mgd-FRB clique-arm fingerprint — ≥8 exactly-one blocks, ≥50 binary nogoods,
/// conjunction-aux (`+a +b -2c >= 0`), and a support constraint (`sum c >= 1`)? Lets the
/// caller decide whether to engage the arm (and run a probe-first guard) without paying the
/// graph build. Mirrors `detect_and_build`'s gate exactly.
pub fn clique_arm_matches(instance: &PbInstance) -> bool {
    let n = instance.num_vars as usize;
    let mut var_block = vec![usize::MAX; n];
    let mut nblk = 0usize;
    for c in &instance.constraints {
        if c.rel == PbRel::Eq
            && c.rhs == 1
            && c.terms.len() >= 2
            && c.terms.iter().all(|t| t.coeff == 1 && unit_pos(t))
        {
            for t in &c.terms {
                var_block[t.lits[0].var as usize - 1] = nblk;
            }
            nblk += 1;
        }
    }
    if nblk < 8 {
        return false;
    }
    let mut c_def: std::collections::HashSet<usize> = std::collections::HashSet::new();
    for c in &instance.constraints {
        if c.rel == PbRel::Ge && c.rhs == 0 && c.terms.len() == 3 {
            let pos = c
                .terms
                .iter()
                .filter(|t| t.coeff == 1 && unit_pos(t))
                .count();
            let neg: Vec<usize> = c
                .terms
                .iter()
                .filter(|t| t.coeff == -2 && unit_pos(t))
                .map(|t| t.lits[0].var as usize - 1)
                .collect();
            if pos == 2 && neg.len() == 1 {
                c_def.insert(neg[0]);
            }
        }
    }
    if c_def.is_empty() {
        return false;
    }
    let mut nogoods = 0usize;
    for c in &instance.constraints {
        if c.rel == PbRel::Ge
            && c.rhs == -1
            && c.terms.len() == 2
            && c.terms.iter().all(|t| t.coeff == -1 && unit_pos(t))
        {
            nogoods += 1;
        }
    }
    if nogoods < 50 {
        return false;
    }
    let has_support = instance.constraints.iter().any(|c| {
        c.rel == PbRel::Ge
            && c.rhs == 1
            && c.terms.len() >= 2
            && c.terms.iter().all(|t| t.coeff == 1 && unit_pos(t))
            && c.terms
                .iter()
                .all(|t| c_def.contains(&(t.lits[0].var as usize - 1)))
    });
    has_support
}

/// Detect the mgd-FRB signature and, if present, build the compatibility graph.
/// Returns `None` for any instance that is not an mgd-FRB binary CSP (so callers pay
/// only a cheap scan and never act on a non-matching instance).
fn detect_and_build(instance: &PbInstance) -> Option<FrbStructure> {
    let n = instance.num_vars as usize;
    let mut var_block = vec![usize::MAX; n];
    let mut var_value = vec![0usize; n];
    let mut blocks: Vec<Vec<usize>> = Vec::new();
    for c in &instance.constraints {
        if c.rel == PbRel::Eq
            && c.rhs == 1
            && c.terms.len() >= 2
            && c.terms.iter().all(|t| t.coeff == 1 && unit_pos(t))
        {
            let bi = blocks.len();
            let mut vs = Vec::with_capacity(c.terms.len());
            for (vi, t) in c.terms.iter().enumerate() {
                let v0 = t.lits[0].var as usize - 1;
                var_block[v0] = bi;
                var_value[v0] = vi;
                vs.push(v0);
            }
            blocks.push(vs);
        }
    }
    let nblk = blocks.len();
    // Cheap early-out: no one-hot CSP structure ⇒ not an mgd-FRB instance. Avoids the
    // conjunction-aux / nogood / support scans on the broad (non-FRB) corpus.
    if nblk < 8 {
        return None;
    }
    // conjunction-aux: +a +b -2c >= 0  (c -> a∧b)
    let mut c_def: std::collections::HashMap<usize, (usize, usize)> =
        std::collections::HashMap::new();
    for c in &instance.constraints {
        if c.rel == PbRel::Ge && c.rhs == 0 && c.terms.len() == 3 {
            let pos: Vec<usize> = c
                .terms
                .iter()
                .filter(|t| t.coeff == 1 && unit_pos(t))
                .map(|t| t.lits[0].var as usize - 1)
                .collect();
            let neg: Vec<usize> = c
                .terms
                .iter()
                .filter(|t| t.coeff == -2 && unit_pos(t))
                .map(|t| t.lits[0].var as usize - 1)
                .collect();
            if pos.len() == 2 && neg.len() == 1 {
                c_def.insert(neg[0], (pos[0], pos[1]));
            }
        }
    }
    // binary nogoods: -a -b >= -1
    let mut nogoods: Vec<(usize, usize)> = Vec::new();
    for c in &instance.constraints {
        if c.rel == PbRel::Ge
            && c.rhs == -1
            && c.terms.len() == 2
            && c.terms.iter().all(|t| t.coeff == -1 && unit_pos(t))
        {
            nogoods.push((
                c.terms[0].lits[0].var as usize - 1,
                c.terms[1].lits[0].var as usize - 1,
            ));
        }
    }
    // support edges: sum of conjunction-aux >= 1
    let mut supports: Vec<Vec<(usize, usize)>> = Vec::new();
    for c in &instance.constraints {
        if c.rel == PbRel::Ge
            && c.rhs == 1
            && c.terms.len() >= 2
            && c.terms.iter().all(|t| t.coeff == 1 && unit_pos(t))
        {
            let tuples: Vec<(usize, usize)> = c
                .terms
                .iter()
                .filter_map(|t| c_def.get(&(t.lits[0].var as usize - 1)).copied())
                .collect();
            if tuples.len() == c.terms.len() && !tuples.is_empty() {
                supports.push(tuples);
            }
        }
    }

    // The mgd-FRB fingerprint. Tight on purpose: requires the conjunction-aux + support
    // structure that is specific to the mgd support encoding, so non-FRB PB instances are
    // never matched.
    if nblk < 8 || nogoods.len() < 50 || c_def.is_empty() || supports.is_empty() {
        return None;
    }

    // Compact vertices = all one-hot vars.
    let verts: Vec<usize> = blocks.iter().flatten().copied().collect();
    let nv = verts.len();
    if nv == 0 {
        return None;
    }
    let mut vid = vec![usize::MAX; n];
    for (i, &ov) in verts.iter().enumerate() {
        vid[ov] = i;
    }
    let vblock: Vec<usize> = verts.iter().map(|&ov| var_block[ov]).collect();

    // support edges = block pairs that carry an explicit allowed-tuple list.
    let mut support_pairs: std::collections::HashSet<(usize, usize)> =
        std::collections::HashSet::new();
    let mut allowed: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();
    for ts in &supports {
        for &(a, b) in ts {
            let (ba, bb) = (var_block[a], var_block[b]);
            support_pairs.insert((ba.min(bb), ba.max(bb)));
            let (ua, ub) = (vid[a], vid[b]);
            allowed.insert((ua.min(ub), ua.max(ub)));
        }
    }
    let mut nogood_v: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();
    for &(a, b) in &nogoods {
        if vid[a] != usize::MAX && vid[b] != usize::MAX {
            let (ua, ub) = (vid[a], vid[b]);
            nogood_v.insert((ua.min(ub), ua.max(ub)));
        }
    }

    let words = nv.div_ceil(64);
    let mut adj = vec![0u64; nv * words];
    let set_adj = |adj: &mut [u64], u: usize, w: usize| {
        adj[u * words + (w >> 6)] |= 1u64 << (w & 63);
        adj[w * words + (u >> 6)] |= 1u64 << (u & 63);
    };
    // 1. different-block, non-support-edge pairs are compatible by default.
    for u in 0..nv {
        for w in (u + 1)..nv {
            let (bu, bw) = (vblock[u], vblock[w]);
            if bu == bw {
                continue;
            }
            let key = (bu.min(bw), bu.max(bw));
            if !support_pairs.contains(&key) {
                set_adj(&mut adj, u, w);
            }
        }
    }
    // 2. support edges: only allowed tuples are compatible.
    for &(u, w) in &allowed {
        set_adj(&mut adj, u, w);
    }
    // 3. remove all nogoods.
    for &(u, w) in &nogood_v {
        adj[u * words + (w >> 6)] &= !(1u64 << (w & 63));
        adj[w * words + (u >> 6)] &= !(1u64 << (u & 63));
    }

    Some(FrbStructure {
        verts,
        nblk,
        adj,
        words,
        nv,
    })
}

/// Recompute the candidate set = common neighbourhood of the current clique.
fn recompute_cand(cand: &mut [u64], k_list: &[usize], adj: &[u64], words: usize, k_bits: &[u64]) {
    if k_list.is_empty() {
        for c in cand.iter_mut() {
            *c = u64::MAX;
        }
    } else {
        let m0 = k_list[0];
        cand.copy_from_slice(&adj[m0 * words..m0 * words + words]);
        for &m in &k_list[1..] {
            let base = m * words;
            for i in 0..words {
                cand[i] &= adj[base + i];
            }
        }
    }
    for i in 0..words {
        cand[i] &= !k_bits[i];
    }
}

/// One worker's clique local search. Returns the vertex list of a full (size `nblk`)
/// clique, or `None` if it stops first (deadline / interrupt / another worker won).
/// Polls `stop` cheaply so a winning worker (or an external interrupt) ends the others.
#[allow(clippy::too_many_arguments)]
fn clique_search(
    s: &FrbStructure,
    base_seed: u64,
    deadline: Option<Instant>,
    stop: &AtomicBool,
    restart_thresh: u64,
) -> Option<Vec<usize>> {
    let FrbStructure {
        nblk,
        adj,
        words,
        nv,
        ..
    } = s;
    let (nblk, words, nv) = (*nblk, *words, *nv);
    let adj = adj.as_slice();

    let adjacent =
        |u: usize, w: usize| -> bool { (adj[u * words + (w >> 6)] >> (w & 63)) & 1 == 1 };
    let conflicts = |k_bits: &[u64], v: usize| -> u32 {
        let base = v * words;
        let mut c = 0u32;
        for i in 0..words {
            c += (k_bits[i] & !adj[base + i]).count_ones();
        }
        c
    };
    let set_conf_neighbors = |conf: &mut [bool], v: usize| {
        let base = v * words;
        for i in 0..words {
            let mut b = adj[base + i];
            while b != 0 {
                let t = b.trailing_zeros() as usize;
                conf[i * 64 + t] = true;
                b &= b - 1;
            }
        }
    };

    let mut rng = Rng::new(base_seed);
    let mut in_k = vec![false; nv];
    let mut k_list: Vec<usize> = Vec::new();
    let mut k_bits = vec![0u64; words];
    let mut cand = vec![0u64; words];
    let mut conf = vec![true; nv];
    let mut poll = 0u64;

    loop {
        if stop.load(Ordering::Relaxed) {
            return None;
        }
        if let Some(dl) = deadline {
            if Instant::now() >= dl {
                return None;
            }
        }
        // restart
        for x in in_k.iter_mut() {
            *x = false;
        }
        k_list.clear();
        for x in k_bits.iter_mut() {
            *x = 0;
        }
        for c in conf.iter_mut() {
            *c = true;
        }
        let seed_v = rng.below(nv);
        in_k[seed_v] = true;
        k_list.push(seed_v);
        k_bits[seed_v >> 6] |= 1u64 << (seed_v & 63);
        cand.copy_from_slice(&adj[seed_v * words..seed_v * words + words]);
        set_conf_neighbors(&mut conf, seed_v);

        let max_steps = 5_000_000u64;
        let mut steps = 0u64;
        let mut stagnant = 0u64;
        let mut best_in_run = 0usize;
        while steps < max_steps {
            if k_list.len() == nblk {
                return Some(k_list.clone());
            }
            // Restart when stuck relative to this run's best (frequent independent
            // restarts exploit the heavy-tailed fast-solve distribution).
            if k_list.len() > best_in_run {
                best_in_run = k_list.len();
                stagnant = 0;
            } else {
                stagnant += 1;
                if stagnant > restart_thresh {
                    break;
                }
            }
            poll += 1;
            if poll & 0x3FFF == 0 {
                if stop.load(Ordering::Relaxed) {
                    return None;
                }
                if let Some(dl) = deadline {
                    if Instant::now() >= dl {
                        return None;
                    }
                }
            }
            steps += 1;

            // 1. EXPAND: uniform-random addable vertex (in cand, conf set), no alloc.
            let mut chosen_v = usize::MAX;
            let mut seen = 0u64;
            for i in 0..words {
                let mut b = cand[i];
                while b != 0 {
                    let t = b.trailing_zeros() as usize;
                    let v = i * 64 + t;
                    b &= b - 1;
                    if v >= nv || !conf[v] {
                        continue;
                    }
                    seen += 1;
                    if rng.below(seen as usize) == 0 {
                        chosen_v = v;
                    }
                }
            }
            if chosen_v != usize::MAX {
                let v = chosen_v;
                in_k[v] = true;
                k_list.push(v);
                k_bits[v >> 6] |= 1u64 << (v & 63);
                let base = v * words;
                for i in 0..words {
                    cand[i] &= adj[base + i];
                }
                set_conf_neighbors(&mut conf, v);
                continue;
            }

            // 2. SWAP: a vertex v∉K with exactly one conflicting K-member (conf set).
            let mut sv = usize::MAX;
            let scan = nv.min(400);
            let s0 = rng.below(nv);
            for off in 0..scan {
                let v = (s0 + off) % nv;
                if !in_k[v] && conf[v] && conflicts(&k_bits, v) == 1 {
                    sv = v;
                    break;
                }
            }
            if sv != usize::MAX {
                let mut u = usize::MAX;
                for &m in &k_list {
                    if !adjacent(sv, m) {
                        u = m;
                        break;
                    }
                }
                if u != usize::MAX {
                    in_k[u] = false;
                    if let Some(p) = k_list.iter().position(|&x| x == u) {
                        k_list.swap_remove(p);
                    }
                    k_bits[u >> 6] &= !(1u64 << (u & 63));
                    conf[u] = false;
                    set_conf_neighbors(&mut conf, u);
                    in_k[sv] = true;
                    k_list.push(sv);
                    k_bits[sv >> 6] |= 1u64 << (sv & 63);
                    set_conf_neighbors(&mut conf, sv);
                    recompute_cand(&mut cand, &k_list, adj, words, &k_bits);
                    continue;
                }
            }

            // 3. STUCK: drop a random K-member; full restart handled at loop top.
            if k_list.is_empty() {
                break;
            }
            let victim = k_list[rng.below(k_list.len())];
            in_k[victim] = false;
            if let Some(p) = k_list.iter().position(|&x| x == victim) {
                k_list.swap_remove(p);
            }
            k_bits[victim >> 6] &= !(1u64 << (victim & 63));
            conf[victim] = false;
            set_conf_neighbors(&mut conf, victim);
            recompute_cand(&mut cand, &k_list, adj, words, &k_bits);
        }
    }
}

/// Extend a clique (one value per block) to a full model and verify it against the
/// original PB constraints. The one-hot vars are fixed as units; CDCL propagates the
/// determined log/aux. Returns the verified assignment, or `None` if (somehow) the
/// extension or verification fails — guaranteeing soundness.
fn extend_and_verify(
    instance: &PbInstance,
    s: &FrbStructure,
    clique: &[usize],
) -> Option<Vec<bool>> {
    let n = instance.num_vars as usize;
    // one-hot vars set true by the clique; everything else (in a block) false.
    let mut onehot_true = vec![false; n];
    for &v in clique {
        onehot_true[s.verts[v]] = true;
    }
    // set of all one-hot vars (to fix as units, false unless selected).
    let mut is_onehot = vec![false; n];
    for &ov in &s.verts {
        is_onehot[ov] = true;
    }

    let cnf = CnfEncoder::encode_instance(instance);
    let mut solver = cnf.to_sat_solver();
    for (v, &oh) in is_onehot.iter().enumerate() {
        if oh {
            let d = (v as i32) + 1;
            let lit = if onehot_true[v] { d } else { -d };
            solver.add_clause(vec![ay_sat::Literal::from_dimacs(lit)]);
        }
    }
    match solver.solve().into_inner() {
        ay_sat::SatResult::Sat(model) => {
            let assign: Vec<bool> = (0..n)
                .map(|i| model.get(i).copied().unwrap_or(false))
                .collect();
            if verify_all_constraints(&instance.constraints, &assign) {
                Some(assign)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Worker count for the parallel search: `NBCORE` (competition convention), else the
/// machine parallelism, clamped to a sane range.
fn worker_count() -> usize {
    let n = std::env::var("NBCORE")
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|n| *n >= 1)
        .or_else(|| std::thread::available_parallelism().ok().map(|p| p.get()))
        .unwrap_or(4);
    n.clamp(1, 64)
}

/// Try to find a SOUND, verified SAT witness for an mgd-FRB decision instance via parallel
/// clique local search. Returns `Some(assignment)` (already verified against the original
/// PB constraints) or `None` (not FRB-shaped, or no witness found before the deadline /
/// interrupt). Never returns an unverified or unsound model.
pub fn try_clique_witness(
    instance: &PbInstance,
    deadline: Option<Instant>,
    term_flag: &AtomicBool,
    base_seed: u64,
) -> Option<Vec<bool>> {
    let s = detect_and_build(instance)?;

    let threads = worker_count();
    let stop = AtomicBool::new(false);
    let winner: Mutex<Option<Vec<usize>>> = Mutex::new(None);

    std::thread::scope(|scope| {
        for t in 0..threads {
            let s_ref = &s;
            let stop_ref = &stop;
            let winner_ref = &winner;
            let seed = base_seed
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add((t as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9) + 1);
            // Diversify the restart cadence across workers: frequent-restart workers catch
            // the heavy-tailed early solve; deeper-restart workers explore each plateau
            // longer. A portfolio is more robust than one fixed threshold.
            let restart_thresh = [8_000u64, 20_000, 40_000, 80_000][t % 4];
            scope.spawn(move || {
                // Mix in the shared interrupt: stop if a worker won OR the caller asked.
                if let Some(clique) = clique_search(s_ref, seed, deadline, stop_ref, restart_thresh)
                {
                    let mut w = winner_ref.lock().unwrap();
                    if w.is_none() {
                        *w = Some(clique);
                    }
                    stop_ref.store(true, Ordering::Relaxed);
                }
            });
        }
        // A lightweight watcher that propagates the external interrupt into `stop`.
        let stop_ref = &stop;
        scope.spawn(move || loop {
            if stop_ref.load(Ordering::Relaxed) {
                return;
            }
            if term_flag.load(Ordering::SeqCst) {
                stop_ref.store(true, Ordering::Relaxed);
                return;
            }
            if let Some(dl) = deadline {
                if Instant::now() >= dl {
                    stop_ref.store(true, Ordering::Relaxed);
                    return;
                }
            }
            std::thread::sleep(std::time::Duration::from_millis(20));
        });
    });

    let clique = winner.into_inner().unwrap()?;
    // Extend + verify on the main thread (fast). Soundness gate.
    extend_and_verify(instance, &s, &clique)
}
