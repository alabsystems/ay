// FRB SLS witness probe (research experiment, Track B-1).
//
// Hypothesis (FRB research program): Model RB / FRB instances are *satisfiable*
// and stochastic local search (WalkSAT/SKC, ULSA-style) finds a witness in
// seconds, even though *complete* (CDCL / tree-like resolution) search is
// provably exponential. PB-COMP DEC only needs a witness, and a witness is
// self-verifying against the original PB constraints (zero UNSAT-soundness risk).
//
// Two modes:
//   full  -> encode the whole OPB to CNF via AY's CnfEncoder, SLS that.
//   core  -> strip to the one-hot CSP core (exactly-one blocks + binary nogoods),
//            SLS only the one-hot vars. The redundant 5-bit log encoding +
//            channeling that bloats the "mgd" encoding is dropped, which is what
//            kills SLS on the full form.
//
// Usage: cargo run --release --example frb_sls_probe -- <file.opb> [secs] [seed] [noise] [mode]

use std::time::Instant;

use ay_pb::CnfEncoder;
use ay_pb::{parse_opb, verify_all_constraints, PbInstance, PbRel};
use ay_sat::{Literal, SatResult};

// Local xorshift64* RNG (no external dep; deterministic per seed).
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
    #[inline]
    fn frac(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }
}

/// Build the one-hot CSP core: exactly-one blocks (coeff +1, rhs 1, Eq) become
/// at-least-one + pairwise at-most-one clauses; binary nogoods (2-term Ge with
/// coeff -1, rhs -1) become binary clauses. All over the original var numbering.
/// Returns (clauses as Vec<(var0,sign)>, set of vars that are one-hot).
fn build_core(instance: &PbInstance) -> (Vec<Vec<(usize, bool)>>, Vec<bool>) {
    let n = instance.num_vars as usize;
    let mut is_onehot = vec![false; n];
    let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();
    for c in &instance.constraints {
        // exactly-one block?
        let all_unit_pos = c
            .terms
            .iter()
            .all(|t| t.coeff == 1 && t.lits.len() == 1 && !t.lits[0].negated);
        if c.rel == PbRel::Eq && c.rhs == 1 && all_unit_pos && c.terms.len() >= 2 {
            let vars: Vec<usize> = c.terms.iter().map(|t| t.lits[0].var as usize - 1).collect();
            for &v in &vars {
                is_onehot[v] = true;
            }
            // at-least-one
            clauses.push(vars.iter().map(|&v| (v, true)).collect());
            // pairwise at-most-one
            for i in 0..vars.len() {
                for j in (i + 1)..vars.len() {
                    clauses.push(vec![(vars[i], false), (vars[j], false)]);
                }
            }
        }
    }
    // nogoods: 2-term Ge, coeff -1 each, rhs -1  ->  (not a) or (not b)
    for c in &instance.constraints {
        if c.rel == PbRel::Ge
            && c.rhs == -1
            && c.terms.len() == 2
            && c.terms
                .iter()
                .all(|t| t.coeff == -1 && t.lits.len() == 1 && !t.lits[0].negated)
        {
            let a = c.terms[0].lits[0].var as usize - 1;
            let b = c.terms[1].lits[0].var as usize - 1;
            if is_onehot[a] && is_onehot[b] {
                clauses.push(vec![(a, false), (b, false)]);
            }
        }
    }
    (clauses, is_onehot)
}

/// Build the full non-log clausal core. Drops the redundant log/channeling block
/// (any constraint touching a var <= `log_max`, 1-based) and expresses every
/// remaining constraint as clauses with NO auxiliary variables:
///   exactly-one (=1, all +1)        -> at-least-one + pairwise at-most-one
///   binary nogood (-a -b >= -1)     -> (¬a ∨ ¬b)
///   conj-def (+a +b -2c >= 0)       -> (¬c ∨ a) ∧ (¬c ∨ b)
///   support (sum +1 >= 1)           -> (a ∨ b ∨ …)
/// Returns (clauses, set of original vars that appear in the core).
fn build_nolog_core(instance: &PbInstance, log_max: u32) -> (Vec<Vec<(usize, bool)>>, Vec<bool>) {
    let n = instance.num_vars as usize;
    let mut in_core = vec![false; n];
    let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();
    let mark = |v: u32, in_core: &mut Vec<bool>| {
        in_core[v as usize - 1] = true;
    };
    for c in &instance.constraints {
        let touches_log = c
            .terms
            .iter()
            .flat_map(|t| t.lits.iter())
            .any(|l| l.var <= log_max);
        if touches_log {
            continue;
        }
        // All terms here are single-literal (the mgd core has no products).
        let unit_pos = |t: &ay_pb::PbTerm| t.lits.len() == 1 && !t.lits[0].negated;
        if c.rel == PbRel::Eq && c.rhs == 1 && c.terms.iter().all(|t| t.coeff == 1 && unit_pos(t)) {
            let vars: Vec<usize> = c
                .terms
                .iter()
                .map(|t| {
                    mark(t.lits[0].var, &mut in_core);
                    t.lits[0].var as usize - 1
                })
                .collect();
            clauses.push(vars.iter().map(|&v| (v, true)).collect());
            for i in 0..vars.len() {
                for j in (i + 1)..vars.len() {
                    clauses.push(vec![(vars[i], false), (vars[j], false)]);
                }
            }
        } else if c.rel == PbRel::Ge
            && c.rhs == -1
            && c.terms.len() == 2
            && c.terms.iter().all(|t| t.coeff == -1 && unit_pos(t))
        {
            let a = c.terms[0].lits[0].var;
            let b = c.terms[1].lits[0].var;
            mark(a, &mut in_core);
            mark(b, &mut in_core);
            clauses.push(vec![(a as usize - 1, false), (b as usize - 1, false)]);
        } else if c.rel == PbRel::Ge && c.rhs == 0 && c.terms.len() == 3 {
            // +1 a +1 b -2 c >= 0  -> (¬c ∨ a) ∧ (¬c ∨ b)
            let pos: Vec<u32> = c
                .terms
                .iter()
                .filter(|t| t.coeff == 1 && unit_pos(t))
                .map(|t| t.lits[0].var)
                .collect();
            let neg: Vec<u32> = c
                .terms
                .iter()
                .filter(|t| t.coeff == -2 && unit_pos(t))
                .map(|t| t.lits[0].var)
                .collect();
            if pos.len() == 2 && neg.len() == 1 {
                let cc = neg[0];
                for &p in &pos {
                    mark(p, &mut in_core);
                    mark(cc, &mut in_core);
                    clauses.push(vec![(cc as usize - 1, false), (p as usize - 1, true)]);
                }
            } else {
                eprintln!("c WARN: unhandled 3-term GE shape, falling back may be unsound-core");
            }
        } else if c.rel == PbRel::Ge
            && c.rhs == 1
            && c.terms.iter().all(|t| t.coeff == 1 && unit_pos(t))
        {
            // sum +1 vars >= 1  -> big clause
            clauses.push(
                c.terms
                    .iter()
                    .map(|t| {
                        mark(t.lits[0].var, &mut in_core);
                        (t.lits[0].var as usize - 1, true)
                    })
                    .collect(),
            );
        } else {
            eprintln!(
                "c WARN: unhandled non-log constraint (rel={:?} rhs={} terms={})",
                c.rel,
                c.rhs,
                c.terms.len()
            );
        }
    }
    (clauses, in_core)
}

/// Block-structured CSP min-conflicts for the mgd FRB encoding. Searches only the
/// Recompute the candidate set = common neighbourhood of the current clique
/// (vertices adjacent to every member), excluding members themselves. Empty clique
/// ⇒ all vertices are candidates.
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
    // never re-offer current members
    for i in 0..words {
        cand[i] &= !k_bits[i];
    }
}

/// Max-clique local search with **configuration checking** (the NuMVC/ULSA
/// anti-cycling mechanism) for the FRB CSP. Reduces the mgd binary CSP to a clique:
/// vertices = the 945 one-hot (var,value) pairs; an edge connects two vertices in
/// DIFFERENT blocks iff their values are *compatible* (not a nogood; and for the 16
/// support-edges, an allowed tuple). A clique of size = #blocks (45) picks exactly
/// one compatible value per variable = a CSP solution. Returns a full PB-var
/// assignment with only the one-hot vars set, or None.
fn solve_clique(
    instance: &PbInstance,
    budget_secs: f64,
    base_seed: u64,
    start: Instant,
) -> Option<Vec<bool>> {
    let n = instance.num_vars as usize;
    let unit_pos = |t: &ay_pb::PbTerm| t.lits.len() == 1 && !t.lits[0].negated;
    // Blocks (exactly-one) -> per-vertex block/value, and the compact vertex list.
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
    // Also detect ALO blocks: `+x1 .. +xk >= 1` (all +1). With same-block vertices
    // non-adjacent in the clique graph (≤1 per block) and a *full* clique required,
    // at-most-one and at-least-one are both enforced — so the at-most-one nogoods need
    // not be `= 1`. Used for the 3-coloring (FromCNF) family.
    for c in &instance.constraints {
        if c.rel == PbRel::Ge
            && c.rhs == 1
            && c.terms.len() >= 2
            && c.terms.iter().all(|t| t.coeff == 1 && unit_pos(t))
            && c.terms
                .iter()
                .all(|t| var_block[t.lits[0].var as usize - 1] == usize::MAX)
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
    if nblk == 0 {
        return None;
    }
    // Compact vertices = all one-hot original vars.
    let verts: Vec<usize> = blocks.iter().flatten().copied().collect();
    let nv = verts.len();
    let mut vid = vec![usize::MAX; n];
    for (i, &ov) in verts.iter().enumerate() {
        vid[ov] = i;
    }
    let vblock: Vec<usize> = verts.iter().map(|&ov| var_block[ov]).collect();
    // c-defs and supports (as in solve_csp).
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
    // Support edges: normalized block pair -> set of allowed (vertex,vertex).
    let mut support_pairs: std::collections::HashSet<(usize, usize)> =
        std::collections::HashSet::new();
    let mut allowed: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();
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
            if tuples.len() != c.terms.len() || tuples.is_empty() {
                continue;
            }
            for &(a, b) in &tuples {
                let (ba, bb) = (var_block[a], var_block[b]);
                support_pairs.insert((ba.min(bb), ba.max(bb)));
                let (ua, ub) = (vid[a], vid[b]);
                allowed.insert((ua.min(ub), ua.max(ub)));
            }
        }
    }
    // Nogoods (vertex pairs).
    let mut nogood: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();
    for c in &instance.constraints {
        if c.rel == PbRel::Ge
            && c.rhs == -1
            && c.terms.len() == 2
            && c.terms.iter().all(|t| t.coeff == -1 && unit_pos(t))
        {
            let a = c.terms[0].lits[0].var as usize - 1;
            let b = c.terms[1].lits[0].var as usize - 1;
            if vid[a] != usize::MAX && vid[b] != usize::MAX {
                let (ua, ub) = (vid[a], vid[b]);
                nogood.insert((ua.min(ub), ua.max(ub)));
            }
        }
    }

    // Build adjacency bitsets.
    let words = (nv + 63) / 64;
    let mut adj = vec![0u64; nv * words];
    let set_adj = |adj: &mut [u64], u: usize, w: usize| {
        adj[u * words + (w >> 6)] |= 1u64 << (w & 63);
        adj[w * words + (u >> 6)] |= 1u64 << (u & 63);
    };
    let clr_adj = |adj: &mut [u64], u: usize, w: usize| {
        adj[u * words + (w >> 6)] &= !(1u64 << (w & 63));
        adj[w * words + (u >> 6)] &= !(1u64 << (u & 63));
    };
    // 1. all different-block, non-support-edge pairs compatible by default.
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
    for &(u, w) in &nogood {
        clr_adj(&mut adj, u, w);
    }
    let adjacent = |adj: &[u64], u: usize, w: usize| -> bool {
        (adj[u * words + (w >> 6)] >> (w & 63)) & 1 == 1
    };

    eprintln!(
        "clique: {} vertices, {} blocks, {} support-edges, target clique = {}",
        nv,
        nblk,
        support_pairs.len(),
        nblk
    );

    let mut rng = Rng::new(base_seed);
    let mut in_k = vec![false; nv];
    let mut k_list: Vec<usize> = Vec::new();
    let mut k_bits = vec![0u64; words];
    // cand = common neighbourhood of K = the addable vertices (O(words) to update on add).
    let mut cand = vec![0u64; words];
    let mut conf = vec![true; nv]; // configuration-checking flags
                                   // DLS-MC-style vertex penalties (persist across restarts): bumped on stuck so the
                                   // search diversifies away from over-used vertices; periodically decayed.
    let mut vweight = vec![0u32; nv];
    let mut since_decay = 0u64;
    // Full-restart threshold (steps stuck at the plateau). Lower = more frequent
    // restarts = more independent "lottery tickets" for the heavy-tailed fast solve.
    let restart_thresh: u64 = std::env::var("AY_CLIQUE_RESTART")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(30_000);
    let mut best = 0usize;
    let mut best_assign = vec![false; n];

    // popcount of (k_bits & ~adj_row(v)) — number of K-members NOT adjacent to v.
    let conflicts = |k_bits: &[u64], adj: &[u64], v: usize| -> u32 {
        let base = v * words;
        let mut c = 0u32;
        for i in 0..words {
            c += (k_bits[i] & !adj[base + i]).count_ones();
        }
        c
    };
    let set_conf_neighbors = |conf: &mut [bool], adj: &[u64], v: usize| {
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

    loop {
        if start.elapsed().as_secs_f64() > budget_secs {
            break;
        }
        // restart from a random seed vertex.
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
        set_conf_neighbors(&mut conf, &adj, seed_v);

        let max_steps = 5_000_000u64;
        let mut steps = 0u64;
        let mut stagnant = 0u64;
        while steps < max_steps {
            if k_list.len() == nblk {
                break;
            }
            if steps & 0x3FFF == 0 && start.elapsed().as_secs_f64() > budget_secs {
                break;
            }
            steps += 1;
            if k_list.len() > best {
                best = k_list.len();
                for x in best_assign.iter_mut() {
                    *x = false;
                }
                for &v in &k_list {
                    best_assign[verts[v]] = true;
                }
                stagnant = 0;
            } else {
                stagnant += 1;
            }

            // 1. EXPAND: uniform-random addable vertex (in cand, conf set), no alloc
            //    (reservoir sampling over the candidate bitset). Uniform randomness
            //    avoids the deterministic trapping a min-penalty bias caused.
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
                set_conf_neighbors(&mut conf, &adj, v);
                continue;
            }

            // 2. SWAP: a vertex v∉K with exactly one conflicting K-member (conf set).
            //    BMS: sample a window of vertices rather than scanning all.
            let mut sv = usize::MAX;
            let scan = nv.min(400);
            let s0 = rng.below(nv);
            for off in 0..scan {
                let v = (s0 + off) % nv;
                if !in_k[v] && conf[v] && conflicts(&k_bits, &adj, v) == 1 {
                    sv = v;
                    break;
                }
            }
            if sv != usize::MAX {
                let mut u = usize::MAX;
                for &m in &k_list {
                    if !adjacent(&adj, sv, m) {
                        u = m;
                        break;
                    }
                }
                if u != usize::MAX {
                    // remove u
                    in_k[u] = false;
                    if let Some(p) = k_list.iter().position(|&x| x == u) {
                        k_list.swap_remove(p);
                    }
                    k_bits[u >> 6] &= !(1u64 << (u & 63));
                    conf[u] = false;
                    set_conf_neighbors(&mut conf, &adj, u);
                    // add sv
                    in_k[sv] = true;
                    k_list.push(sv);
                    k_bits[sv >> 6] |= 1u64 << (sv & 63);
                    set_conf_neighbors(&mut conf, &adj, sv);
                    // recompute cand = AND of adj over K, minus K members
                    recompute_cand(&mut cand, &k_list, &adj, words, &k_bits);
                    continue;
                }
            }

            // 3. STUCK: penalise the current clique, then drop its most-penalised
            //    member (DLS-MC diversification); full restart only on long stagnation.
            if stagnant > restart_thresh || k_list.is_empty() {
                break;
            }
            let _ = (&mut vweight, &mut since_decay); // penalties unused in the random variant
            let victim = k_list[rng.below(k_list.len())];
            in_k[victim] = false;
            if let Some(p) = k_list.iter().position(|&x| x == victim) {
                k_list.swap_remove(p);
            }
            k_bits[victim >> 6] &= !(1u64 << (victim & 63));
            conf[victim] = false;
            set_conf_neighbors(&mut conf, &adj, victim);
            recompute_cand(&mut cand, &k_list, &adj, words, &k_bits);
        }
        if k_list.len() == nblk {
            for x in best_assign.iter_mut() {
                *x = false;
            }
            for &v in &k_list {
                best_assign[verts[v]] = true;
            }
            eprintln!(
                "c CLIQUE solved: size={} time={:.3}s",
                nblk,
                start.elapsed().as_secs_f64()
            );
            return Some(best_assign);
        }
    }
    eprintln!(
        "c CLIQUE no full clique: best={}/{} time={:.3}s",
        best,
        nblk,
        start.elapsed().as_secs_f64()
    );
    if best == nblk {
        Some(best_assign)
    } else {
        None
    }
}

/// CSP variables (the exactly-one blocks), one value each, so exactly-one is
/// maintained for free and the conjunction-aux `c` are *eliminated* (a support
/// `sum c >= 1` becomes "some allowed tuple (a,b) is selected", via `c→(a∧b)`).
/// Returns a full PB-var assignment with only the one-hot vars set, or None.
fn solve_csp(
    instance: &PbInstance,
    budget_secs: f64,
    base_seed: u64,
    noise: f64,
    start: Instant,
) -> Option<Vec<bool>> {
    let n = instance.num_vars as usize;
    let mut var_block = vec![usize::MAX; n];
    let mut var_value = vec![0usize; n];
    let mut blocks: Vec<Vec<usize>> = Vec::new();
    let unit_pos = |t: &ay_pb::PbTerm| t.lits.len() == 1 && !t.lits[0].negated;
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
    let nb = blocks.len();
    // c-aux definition: c -> (a,b) from +1 a +1 b -2 c >= 0.
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
    // nogoods (binary) incident lists, and supports (lists of allowed tuples).
    let mut nogood_nbr: Vec<Vec<usize>> = vec![Vec::new(); n];
    for c in &instance.constraints {
        if c.rel == PbRel::Ge
            && c.rhs == -1
            && c.terms.len() == 2
            && c.terms.iter().all(|t| t.coeff == -1 && unit_pos(t))
        {
            let a = c.terms[0].lits[0].var as usize - 1;
            let b = c.terms[1].lits[0].var as usize - 1;
            nogood_nbr[a].push(b);
            nogood_nbr[b].push(a);
        }
    }
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
    let mut support_by_block: Vec<Vec<usize>> = vec![Vec::new(); nb];
    for (si, ts) in supports.iter().enumerate() {
        let mut seen = std::collections::HashSet::new();
        for &(a, b) in ts {
            for blk in [var_block[a], var_block[b]] {
                if blk != usize::MAX && seen.insert(blk) {
                    support_by_block[blk].push(si);
                }
            }
        }
    }
    eprintln!(
        "csp: {} blocks, {} c-defs, {} supports",
        nb,
        c_def.len(),
        supports.len()
    );
    if nb == 0 {
        return None;
    }

    let coord_repair = std::env::var("AY_CSP_NOCOORD").is_err();
    let mut rng = Rng::new(base_seed);
    let mut cur = vec![0usize; nb];
    let selected = |cur: &[usize], v0: usize| -> bool {
        var_block[v0] != usize::MAX && cur[var_block[v0]] == var_value[v0]
    };
    let support_sat = |cur: &[usize], si: usize, supports: &[Vec<(usize, usize)>]| -> bool {
        supports[si]
            .iter()
            .any(|&(a, b)| selected(cur, a) && selected(cur, b))
    };
    // total violations under cur
    let count_viol = |cur: &[usize], supports: &[Vec<(usize, usize)>]| -> usize {
        let mut v = 0;
        for bb in 0..nb {
            let var = blocks[bb][cur[bb]];
            for &nb_ in &nogood_nbr[var] {
                if selected(cur, nb_) {
                    v += 1;
                }
            }
        }
        v /= 2; // each violated nogood counted twice
        for si in 0..supports.len() {
            if !support_sat(cur, si, supports) {
                v += 1;
            }
        }
        v
    };

    let mut tries = 0u64;
    let mut global_best = usize::MAX;
    let mut best_assign = vec![false; n];
    // PAWS-style support weights (persist across restarts): bumped when a support
    // stays violated, which biases move SELECTION toward satisfying the hard
    // support-edges. Weights affect only which move is chosen, never the violation
    // count, so solution detection (viol_total==0) stays exact.
    let mut support_w = vec![1u32; supports.len()];
    loop {
        if start.elapsed().as_secs_f64() > budget_secs {
            break;
        }
        tries += 1;
        for b in 0..nb {
            cur[b] = rng.below(blocks[b].len());
        }
        let mut viol_total = count_viol(&cur, &supports);
        // local cost of block bb at value v = (violated nogoods incident to var(bb,v))
        // + (supports touching bb that are unsat with bb=v). Only these change when
        // bb is re-valued, so viol_total += cost(new) - cost(old).
        // Returns (weighted_cost, unweighted_violations) of block bb at value v.
        // weighted is used to *choose* moves; unweighted updates viol_total.
        let cost_at = |cur: &mut Vec<usize>,
                       bb: usize,
                       v: usize,
                       supports: &[Vec<(usize, usize)>],
                       support_w: &[u32]|
         -> (usize, usize) {
            let var = blocks[bb][v];
            let mut w = 0usize;
            let mut u = 0usize;
            for &x in &nogood_nbr[var] {
                if selected(cur, x) {
                    w += 1;
                    u += 1;
                }
            }
            let saved = cur[bb];
            cur[bb] = v;
            for &si in &support_by_block[bb] {
                if !support_sat(cur, si, supports) {
                    w += support_w[si] as usize;
                    u += 1;
                }
            }
            cur[bb] = saved;
            (w, u)
        };

        let max_moves: u64 = std::env::var("AY_CSP_MAXMOVES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(200_000);
        // Iterated local search: when stuck for `stag` moves, perturb `kick`
        // random blocks (keeps the descent's progress, escapes local minima).
        let stag: u64 = std::env::var("AY_CSP_STAG")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(800);
        let kick: usize = std::env::var("AY_CSP_KICK")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(3);
        let mut best_this_try = usize::MAX;
        let mut since_improve = 0u64;
        let mut moves = 0u64;
        while moves < max_moves {
            // Resync against drift in the incremental counter.
            if moves & 0xFFFF == 0 {
                viol_total = count_viol(&cur, &supports);
            }
            if viol_total < best_this_try {
                best_this_try = viol_total;
                since_improve = 0;
            } else {
                since_improve += 1;
                if since_improve > stag {
                    // PAWS escape: make every currently-violated support heavier so
                    // future moves prioritise satisfying it; then a small kick.
                    for si in 0..supports.len() {
                        if !support_sat(&cur, si, &supports) {
                            support_w[si] = (support_w[si] + 1).min(100_000);
                        }
                    }
                    for _ in 0..kick {
                        let bb = rng.below(nb);
                        let old = cur[bb];
                        let nv = rng.below(blocks[bb].len());
                        if nv != old {
                            let c_old = cost_at(&mut cur, bb, old, &supports, &support_w).1;
                            let c_new = cost_at(&mut cur, bb, nv, &supports, &support_w).1;
                            cur[bb] = nv;
                            viol_total = viol_total + c_new - c_old;
                        }
                    }
                    since_improve = 0;
                    best_this_try = viol_total;
                }
            }
            if viol_total < global_best {
                global_best = viol_total;
                for v in best_assign.iter_mut() {
                    *v = false;
                }
                for bb in 0..nb {
                    best_assign[blocks[bb][cur[bb]]] = true;
                }
            }
            if viol_total == 0 {
                let mut out = vec![false; n];
                for bb in 0..nb {
                    out[blocks[bb][cur[bb]]] = true;
                }
                eprintln!(
                    "c CSP solved: try={} moves={} time={:.3}s",
                    tries,
                    moves,
                    start.elapsed().as_secs_f64()
                );
                return Some(out);
            }
            if moves & 0xFFF == 0 && start.elapsed().as_secs_f64() > budget_secs {
                break;
            }
            moves += 1;

            // Coordinated support repair: with prob (1-noise), if some support is
            // unsatisfied, place BOTH endpoints of a random allowed tuple so the
            // support lands on an allowed tuple in one atomic move (single-block
            // greedy can never do this — it needs two blocks to move together).
            if coord_repair && !supports.is_empty() && rng.frac() >= noise {
                let si0 = rng.below(supports.len());
                let mut repaired = false;
                for off in 0..supports.len() {
                    let si = (si0 + off) % supports.len();
                    if !support_sat(&cur, si, &supports) {
                        // Each support is a binary edge (2 blocks). Among its allowed
                        // tuples pick the one whose placement adds the fewest nogood
                        // violations (selected nogood-neighbours of each endpoint).
                        let nogood_cost = |cur: &Vec<usize>, x: usize, other: usize| -> usize {
                            nogood_nbr[x]
                                .iter()
                                .filter(|&&y| y != other && selected(cur, y))
                                .count()
                        };
                        let mut best_t = supports[si][0];
                        let mut best_c = usize::MAX;
                        for &(a, b) in &supports[si] {
                            let c = nogood_cost(&cur, a, b) + nogood_cost(&cur, b, a);
                            if c < best_c {
                                best_c = c;
                                best_t = (a, b);
                            }
                        }
                        let (a, b) = best_t;
                        for &endp in &[a, b] {
                            let blk = var_block[endp];
                            let val = var_value[endp];
                            let old_v = cur[blk];
                            if blk != usize::MAX && old_v != val {
                                let c_old = cost_at(&mut cur, blk, old_v, &supports, &support_w).1;
                                let c_new = cost_at(&mut cur, blk, val, &supports, &support_w).1;
                                cur[blk] = val;
                                viol_total = viol_total + c_new - c_old;
                            }
                        }
                        repaired = true;
                        break;
                    }
                }
                if repaired {
                    continue;
                }
            }

            // Pick a violated constraint and a block to re-value.
            let mut bb = usize::MAX;
            if !supports.is_empty() && rng.frac() < 0.5 {
                let si0 = rng.below(supports.len());
                for off in 0..supports.len() {
                    let si = (si0 + off) % supports.len();
                    if !support_sat(&cur, si, &supports) {
                        let (a, b) = supports[si][rng.below(supports[si].len())];
                        bb = if rng.frac() < 0.5 {
                            var_block[a]
                        } else {
                            var_block[b]
                        };
                        break;
                    }
                }
            }
            if bb == usize::MAX {
                let b0 = rng.below(nb);
                for off in 0..nb {
                    let cand = (b0 + off) % nb;
                    let var = blocks[cand][cur[cand]];
                    if nogood_nbr[var].iter().any(|&x| selected(&cur, x)) {
                        bb = cand;
                        break;
                    }
                }
                if bb == usize::MAX {
                    // only supports violated; pick a random unsat support's block
                    let si0 = rng.below(supports.len().max(1));
                    for off in 0..supports.len() {
                        let si = (si0 + off) % supports.len();
                        if !support_sat(&cur, si, &supports) {
                            let (a, _b) = supports[si][rng.below(supports[si].len())];
                            bb = var_block[a];
                            break;
                        }
                    }
                    if bb == usize::MAX {
                        bb = rng.below(nb);
                    }
                }
            }

            let old = cur[bb];
            let bsz = blocks[bb].len();
            let cost_old = cost_at(&mut cur, bb, old, &supports, &support_w).1;
            let chosen = if rng.frac() < noise {
                rng.below(bsz)
            } else {
                let mut best_val = old;
                let mut best_cost = usize::MAX;
                let v0_start = rng.below(bsz);
                for off in 0..bsz {
                    let v = (v0_start + off) % bsz;
                    let c = cost_at(&mut cur, bb, v, &supports, &support_w).0; // weighted
                    if c < best_cost {
                        best_cost = c;
                        best_val = v;
                    }
                }
                best_val
            };
            let cost_new = cost_at(&mut cur, bb, chosen, &supports, &support_w).1;
            cur[bb] = chosen;
            viol_total = viol_total + cost_new - cost_old;
        }
    }
    // Final independent verification of the best assignment (guards against any
    // incremental-counter drift hiding a real solution).
    let mut bcur = vec![0usize; nb];
    for bb in 0..nb {
        for (vi, &v0) in blocks[bb].iter().enumerate() {
            if best_assign[v0] {
                bcur[bb] = vi;
            }
        }
    }
    let true_best = count_viol(&bcur, &supports);
    eprintln!(
        "c CSP no model: tries={} best_viol={} (verified={}) time={:.3}s",
        tries,
        global_best,
        true_best,
        start.elapsed().as_secs_f64()
    );
    Some(best_assign)
}

/// WalkSAT/SKC over `n` vars and the given clauses. Returns a full satisfying
/// assignment if found within the budget, else None (reporting best unsat).
fn walksat(
    n: usize,
    clauses: &[Vec<(usize, bool)>],
    budget_secs: f64,
    base_seed: u64,
    noise: f64,
    start: Instant,
) -> Option<Vec<bool>> {
    let m = clauses.len();
    // probSAT break-exponent: enabled when AY_PROBSAT_CB > 0 (e.g. 2.5).
    let probsat_cb: f64 = std::env::var("AY_PROBSAT_CB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0.0);
    let mut occ: Vec<Vec<(usize, bool)>> = vec![Vec::new(); n];
    for (ci, cl) in clauses.iter().enumerate() {
        for &(v, s) in cl {
            occ[v].push((ci, s));
        }
    }
    let mut rng = Rng::new(base_seed);
    let mut assign = vec![false; n];
    let mut num_true = vec![0u32; m];
    let mut unsat: Vec<usize> = Vec::new();
    let mut unsat_pos: Vec<i64> = vec![-1; m];
    let mut tries = 0u64;
    let mut total_flips: u64 = 0;
    let mut global_best = usize::MAX;

    loop {
        if start.elapsed().as_secs_f64() > budget_secs {
            break;
        }
        tries += 1;
        for a in assign.iter_mut() {
            *a = rng.next_u64() & 1 == 1;
        }
        for c in num_true.iter_mut() {
            *c = 0;
        }
        unsat.clear();
        for p in unsat_pos.iter_mut() {
            *p = -1;
        }
        for (ci, cl) in clauses.iter().enumerate() {
            let mut t = 0u32;
            for &(v, s) in cl {
                if assign[v] == s {
                    t += 1;
                }
            }
            num_true[ci] = t;
            if t == 0 {
                unsat_pos[ci] = unsat.len() as i64;
                unsat.push(ci);
            }
        }

        // Adaptive noise (Hoos): when `noise < 0`, p rises on stagnation and
        // falls on improvement, which escapes the small conjunction-aux plateaus.
        let adaptive = noise < 0.0;
        let phi = 0.2f64;
        let theta = ((m as f64) / 100.0).max(50.0);
        let mut p = if adaptive { 0.0 } else { noise };
        let mut best_this_try = usize::MAX;
        let mut since_improve = 0u64;

        let mult: u64 = std::env::var("AY_MAXFLIPS_PER_N")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(2000);
        let max_flips: u64 = (n as u64).saturating_mul(mult).max(2_000_000);
        let mut flips = 0u64;
        while flips < max_flips {
            if unsat.is_empty() {
                break;
            }
            if unsat.len() < global_best {
                global_best = unsat.len();
            }
            if adaptive {
                if unsat.len() < best_this_try {
                    best_this_try = unsat.len();
                    since_improve = 0;
                    p -= p * phi / 2.0;
                } else {
                    since_improve += 1;
                    if (since_improve as f64) > theta {
                        p += (1.0 - p) * phi;
                        since_improve = 0;
                    }
                }
            }
            if flips & 0x3FFF == 0 && start.elapsed().as_secs_f64() > budget_secs {
                break;
            }
            flips += 1;
            total_flips += 1;

            let c = unsat[rng.below(unsat.len())];
            let cl = &clauses[c];
            let flip_var = if probsat_cb > 0.0 {
                // probSAT (poly): pick var in clause with prob ∝ (eps + break)^(-cb).
                let mut weights: [f64; 64] = [0.0; 64];
                let mut total = 0.0f64;
                let k = cl.len().min(64);
                for (idx, &(v, _s)) in cl.iter().take(k).enumerate() {
                    let mut b = 0u32;
                    for &(ci, s) in &occ[v] {
                        if assign[v] == s && num_true[ci] == 1 {
                            b += 1;
                        }
                    }
                    let w = (0.9f64 + b as f64).powf(-probsat_cb);
                    weights[idx] = w;
                    total += w;
                }
                let mut pick = rng.frac() * total;
                let mut chosen = cl[0].0;
                for (idx, &(v, _s)) in cl.iter().take(k).enumerate() {
                    pick -= weights[idx];
                    if pick <= 0.0 {
                        chosen = v;
                        break;
                    }
                }
                chosen
            } else {
                let mut best_var = cl[0].0;
                let mut best_break = u32::MAX;
                let mut zero_break = false;
                for &(v, _s) in cl {
                    let mut b = 0u32;
                    for &(ci, s) in &occ[v] {
                        if assign[v] == s && num_true[ci] == 1 {
                            b += 1;
                            if b >= best_break {
                                break;
                            }
                        }
                    }
                    if b == 0 {
                        best_var = v;
                        zero_break = true;
                        break;
                    }
                    if b < best_break {
                        best_break = b;
                        best_var = v;
                    }
                }
                if zero_break {
                    best_var
                } else if rng.frac() < p {
                    cl[rng.below(cl.len())].0
                } else {
                    best_var
                }
            };

            let old = assign[flip_var];
            let new = !old;
            assign[flip_var] = new;
            for &(ci, s) in &occ[flip_var] {
                let before = old == s;
                let after = new == s;
                if before == after {
                    continue;
                }
                if after {
                    let was = num_true[ci];
                    num_true[ci] = was + 1;
                    if was == 0 {
                        let p = unsat_pos[ci];
                        if p >= 0 {
                            let p = p as usize;
                            let last = unsat.pop().unwrap();
                            if last != ci {
                                unsat[p] = last;
                                unsat_pos[last] = p as i64;
                            }
                            unsat_pos[ci] = -1;
                        }
                    }
                } else {
                    num_true[ci] -= 1;
                    if num_true[ci] == 0 {
                        unsat_pos[ci] = unsat.len() as i64;
                        unsat.push(ci);
                    }
                }
            }
        }
        if unsat.is_empty() {
            eprintln!(
                "c found model: try={} total_flips={} time={:.3}s",
                tries,
                total_flips,
                start.elapsed().as_secs_f64()
            );
            return Some(assign);
        }
    }
    eprintln!(
        "c no model: tries={} total_flips={} best_unsat={} time={:.3}s",
        tries,
        total_flips,
        global_best,
        start.elapsed().as_secs_f64()
    );
    None
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: frb_sls_probe <file.opb> [secs] [seed] [noise] [mode=full|core]");
        std::process::exit(2);
    }
    let path = &args[1];
    let budget_secs: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(60.0);
    let base_seed: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(0xC0FFEE);
    let noise: f64 = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(0.5);
    let mode = args.get(5).map(|s| s.as_str()).unwrap_or("full");

    let text = std::fs::read_to_string(path).expect("read opb");
    let instance = parse_opb(&text).expect("parse opb");
    let pb_nvars = instance.num_vars as usize;
    eprintln!(
        "parsed: {} PB vars, {} constraints | mode={}",
        pb_nvars,
        instance.constraints.len(),
        mode
    );

    let start = Instant::now();

    if mode == "clique" {
        match solve_clique(&instance, budget_secs, base_seed, start) {
            Some(out) => {
                // out has exactly one one-hot var true per block. Fix all one-hot
                // vars as units and let CDCL recover the determined log/aux, verify.
                let mut is_onehot = vec![false; pb_nvars];
                for c in &instance.constraints {
                    if c.rel == PbRel::Eq
                        && c.rhs == 1
                        && c.terms.len() >= 2
                        && c.terms
                            .iter()
                            .all(|t| t.coeff == 1 && t.lits.len() == 1 && !t.lits[0].negated)
                    {
                        for t in &c.terms {
                            is_onehot[t.lits[0].var as usize - 1] = true;
                        }
                    }
                }
                let t_ext = Instant::now();
                let cnf = CnfEncoder::encode_instance(&instance);
                let mut solver = cnf.to_sat_solver();
                for (v, &oh) in is_onehot.iter().enumerate() {
                    if oh {
                        let d = (v as i32) + 1;
                        solver.add_clause(vec![Literal::from_dimacs(if out[v] { d } else { -d })]);
                    }
                }
                match solver.solve().into_inner() {
                    SatResult::Sat(model) => {
                        let pb_assign: Vec<bool> = (0..pb_nvars).map(|i| model[i]).collect();
                        let ok = verify_all_constraints(&instance.constraints, &pb_assign);
                        println!("s SATISFIABLE");
                        println!(
                            "c FULL witness: verify_original_PB={} extend={:.3}s total={:.3}s",
                            ok,
                            t_ext.elapsed().as_secs_f64(),
                            start.elapsed().as_secs_f64()
                        );
                        if !ok {
                            eprintln!("WARNING: model failed original PB!");
                            std::process::exit(3);
                        }
                    }
                    other => {
                        println!("s UNKNOWN");
                        eprintln!("c extension not SAT: {:?}", other);
                    }
                }
            }
            None => println!("s UNKNOWN"),
        }
        return;
    }

    if mode == "csp" {
        match solve_csp(&instance, budget_secs, base_seed, noise, start) {
            Some(out) => {
                // Fix every one-hot var to the CSP solution, extend via CDCL.
                let mut is_onehot = vec![false; pb_nvars];
                for c in &instance.constraints {
                    if c.rel == PbRel::Eq
                        && c.rhs == 1
                        && c.terms.len() >= 2
                        && c.terms
                            .iter()
                            .all(|t| t.coeff == 1 && t.lits.len() == 1 && !t.lits[0].negated)
                    {
                        for t in &c.terms {
                            is_onehot[t.lits[0].var as usize - 1] = true;
                        }
                    }
                }
                let t_ext = Instant::now();
                // Hybrid finish: phase-seed CDCL on the CLEAN nolog core (no log
                // bloat) from the SLS near-solution. Starting ~1 conflict from a
                // model, the residual CDCL search is tiny — this finishes what the
                // SLS got close to. Phases are hints; CDCL still enforces all core
                // constraints. The resulting core model is then fixed as units on
                // the full instance to recover the log bits, and verified.
                let mut min_onehot = u32::MAX;
                for c in &instance.constraints {
                    if c.rel == PbRel::Eq
                        && c.rhs == 1
                        && c.terms.len() >= 2
                        && c.terms
                            .iter()
                            .all(|t| t.coeff == 1 && t.lits.len() == 1 && !t.lits[0].negated)
                    {
                        for t in &c.terms {
                            min_onehot = min_onehot.min(t.lits[0].var);
                        }
                    }
                }
                let log_max = min_onehot.saturating_sub(1);
                let (core_clauses, in_core) = build_nolog_core(&instance, log_max);
                let mut core_solver = ay_sat::Solver::new(pb_nvars);
                for cl in &core_clauses {
                    let lits: Vec<Literal> = cl
                        .iter()
                        .map(|&(v, s)| {
                            let d = (v as i32) + 1;
                            Literal::from_dimacs(if s { d } else { -d })
                        })
                        .collect();
                    core_solver.add_clause(lits);
                }
                let mut seeded = 0usize;
                for (v, &oh) in is_onehot.iter().enumerate() {
                    if oh {
                        core_solver.set_phase(ay_sat::Variable::new(v as u32), out[v]);
                        seeded += 1;
                    }
                }
                eprintln!(
                    "c phase-seeded {} one-hot vars on clean core; finishing with CDCL ...",
                    seeded
                );
                match core_solver.solve().into_inner() {
                    SatResult::Sat(core_model) => {
                        // Fix all core vars from the core model, recover log on full.
                        let cnf = CnfEncoder::encode_instance(&instance);
                        let mut solver = cnf.to_sat_solver();
                        for (v, &inc) in in_core.iter().enumerate() {
                            if inc {
                                let d = (v as i32) + 1;
                                solver.add_clause(vec![Literal::from_dimacs(if core_model[v] {
                                    d
                                } else {
                                    -d
                                })]);
                            }
                        }
                        match solver.solve().into_inner() {
                            SatResult::Sat(model) => {
                                let pb_assign: Vec<bool> =
                                    (0..pb_nvars).map(|i| model[i]).collect();
                                let ok = verify_all_constraints(&instance.constraints, &pb_assign);
                                println!("s SATISFIABLE");
                                println!(
                                    "c FULL witness: verify_original_PB={} finish={:.3}s total={:.3}s",
                                    ok, t_ext.elapsed().as_secs_f64(), start.elapsed().as_secs_f64()
                                );
                                if !ok {
                                    eprintln!("WARNING: model failed original PB!");
                                    std::process::exit(3);
                                }
                            }
                            other => {
                                println!("s UNKNOWN");
                                eprintln!("c log recovery not SAT: {:?}", other);
                            }
                        }
                    }
                    other => {
                        println!("s UNKNOWN");
                        eprintln!("c phase-seeded core CDCL did not finish: {:?}", other);
                    }
                }
            }
            None => println!("s UNKNOWN"),
        }
        return;
    }

    if mode == "nolog" {
        // log block = vars below the smallest one-hot var (mgd puts the 5-bit log
        // + channeling there). Detect it from the exactly-one blocks.
        let mut min_onehot = u32::MAX;
        for c in &instance.constraints {
            if c.rel == PbRel::Eq
                && c.rhs == 1
                && c.terms.len() >= 2
                && c.terms
                    .iter()
                    .all(|t| t.coeff == 1 && t.lits.len() == 1 && !t.lits[0].negated)
            {
                for t in &c.terms {
                    min_onehot = min_onehot.min(t.lits[0].var);
                }
            }
        }
        let log_max = min_onehot.saturating_sub(1);
        let (clauses, in_core) = build_nolog_core(&instance, log_max);
        let n_core_vars = in_core.iter().filter(|&&b| b).count();
        eprintln!(
            "nolog core: log_max={} core_vars={} clauses={}",
            log_max,
            n_core_vars,
            clauses.len()
        );

        // Optional: solve the cleaned core with AY's real CDCL instead of SLS.
        if std::env::var("AY_CORE_CDCL").is_ok() {
            let mut solver = ay_sat::Solver::new(pb_nvars);
            for cl in &clauses {
                let lits: Vec<Literal> = cl
                    .iter()
                    .map(|&(v, s)| {
                        let d = (v as i32) + 1;
                        Literal::from_dimacs(if s { d } else { -d })
                    })
                    .collect();
                solver.add_clause(lits);
            }
            eprintln!("c solving nolog core with ay-sat CDCL ...");
            match solver.solve().into_inner() {
                SatResult::Sat(model) => {
                    // verify core + extend to full instance
                    let core_assign: Vec<bool> = (0..pb_nvars).map(|i| model[i]).collect();
                    let cnf = CnfEncoder::encode_instance(&instance);
                    let mut full = cnf.to_sat_solver();
                    for (v, &inc) in in_core.iter().enumerate() {
                        if inc {
                            let d = (v as i32) + 1;
                            full.add_clause(vec![Literal::from_dimacs(if core_assign[v] {
                                d
                            } else {
                                -d
                            })]);
                        }
                    }
                    match full.solve().into_inner() {
                        SatResult::Sat(fm) => {
                            let pa: Vec<bool> = (0..pb_nvars).map(|i| fm[i]).collect();
                            let ok = verify_all_constraints(&instance.constraints, &pa);
                            println!("s SATISFIABLE");
                            println!(
                                "c CDCL-core FULL witness: verify_original_PB={} total={:.3}s",
                                ok,
                                start.elapsed().as_secs_f64()
                            );
                        }
                        other => {
                            println!("s UNKNOWN");
                            eprintln!("c extend not SAT: {:?}", other);
                        }
                    }
                }
                other => {
                    println!("s UNKNOWN");
                    eprintln!("c nolog core CDCL: {:?}", other);
                }
            }
            return;
        }
        match walksat(pb_nvars, &clauses, budget_secs, base_seed, noise, start) {
            Some(assign) => {
                let core_ok = clauses
                    .iter()
                    .all(|cl| cl.iter().any(|&(v, s)| assign[v] == s));
                eprintln!(
                    "c nolog CORE solved: time={:.3}s core_clauses_ok={}",
                    start.elapsed().as_secs_f64(),
                    core_ok
                );
                let t_ext = Instant::now();
                let cnf = CnfEncoder::encode_instance(&instance);
                let mut solver = cnf.to_sat_solver();
                for (v, &inc) in in_core.iter().enumerate() {
                    if inc {
                        let d = (v as i32) + 1;
                        let lit = if assign[v] { d } else { -d };
                        solver.add_clause(vec![Literal::from_dimacs(lit)]);
                    }
                }
                match solver.solve().into_inner() {
                    SatResult::Sat(model) => {
                        let pb_assign: Vec<bool> = (0..pb_nvars).map(|i| model[i]).collect();
                        let ok = verify_all_constraints(&instance.constraints, &pb_assign);
                        println!("s SATISFIABLE");
                        println!(
                            "c FULL witness: verify_original_PB={} extend={:.3}s total={:.3}s",
                            ok,
                            t_ext.elapsed().as_secs_f64(),
                            start.elapsed().as_secs_f64()
                        );
                        if !ok {
                            eprintln!("WARNING: extended model failed original PB!");
                            std::process::exit(3);
                        }
                    }
                    other => {
                        println!("s UNKNOWN");
                        eprintln!("c extension did not return SAT: {:?}", other);
                    }
                }
            }
            None => println!("s UNKNOWN"),
        }
        return;
    }

    if mode == "core" {
        let (clauses, is_onehot) = build_core(&instance);
        let n_oh = is_onehot.iter().filter(|&&b| b).count();
        eprintln!(
            "core: {} one-hot vars, {} clauses (ALO+AMO+nogoods)",
            n_oh,
            clauses.len()
        );
        match walksat(pb_nvars, &clauses, budget_secs, base_seed, noise, start) {
            Some(assign) => {
                // Verify the core: each one-hot block has exactly one true, no nogood violated.
                let core_ok = clauses
                    .iter()
                    .all(|cl| cl.iter().any(|&(v, s)| assign[v] == s));
                eprintln!(
                    "c CORE solved: time={:.3}s core_clauses_ok={}",
                    start.elapsed().as_secs_f64(),
                    core_ok
                );

                // Extend to a full mgd witness: fix the one-hot vars as units and
                // let CDCL propagate the functionally-determined aux (log bits +
                // channeling). Then verify the full model against ALL original
                // mgd constraints. A verified witness is unconditionally sound.
                let t_ext = Instant::now();
                let cnf = CnfEncoder::encode_instance(&instance);
                let mut solver = cnf.to_sat_solver();
                for (v, &oh) in is_onehot.iter().enumerate() {
                    if oh {
                        let d = (v as i32) + 1;
                        let lit = if assign[v] { d } else { -d };
                        solver.add_clause(vec![Literal::from_dimacs(lit)]);
                    }
                }
                match solver.solve().into_inner() {
                    SatResult::Sat(model) => {
                        let pb_assign: Vec<bool> = (0..pb_nvars).map(|i| model[i]).collect();
                        let ok = verify_all_constraints(&instance.constraints, &pb_assign);
                        println!("s SATISFIABLE");
                        println!(
                            "c FULL witness: verify_original_PB={} extend_time={:.3}s total={:.3}s",
                            ok,
                            t_ext.elapsed().as_secs_f64(),
                            start.elapsed().as_secs_f64()
                        );
                        if !ok {
                            eprintln!("WARNING: extended model failed original PB!");
                            std::process::exit(3);
                        }
                    }
                    other => {
                        println!("s UNKNOWN");
                        eprintln!("c extension did not return SAT: {:?}", other);
                    }
                }
            }
            None => println!("s UNKNOWN"),
        }
        return;
    }

    // full mode
    let cnf = CnfEncoder::encode_instance(&instance);
    let n = cnf.num_vars as usize;
    eprintln!("encoded CNF: {} vars, {} clauses", n, cnf.clauses.len());
    let mut clauses: Vec<Vec<(usize, bool)>> = Vec::with_capacity(cnf.clauses.len());
    for cl in &cnf.clauses {
        clauses.push(
            cl.iter()
                .map(|&lit| ((lit.unsigned_abs() as usize) - 1, lit > 0))
                .collect(),
        );
    }
    match walksat(n, &clauses, budget_secs, base_seed, noise, start) {
        Some(assign) => {
            let pb_assign: Vec<bool> = assign[..pb_nvars].to_vec();
            let ok = verify_all_constraints(&instance.constraints, &pb_assign);
            println!("s SATISFIABLE");
            println!(
                "c witness found: time={:.3}s verify_original_PB={}",
                start.elapsed().as_secs_f64(),
                ok
            );
            if !ok {
                eprintln!("WARNING: CNF model did NOT satisfy original PB!");
                std::process::exit(3);
            }
        }
        None => println!("s UNKNOWN"),
    }
}
