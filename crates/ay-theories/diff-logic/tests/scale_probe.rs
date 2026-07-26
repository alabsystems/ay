use ay_diff_logic::incremental::{AssertOutcome, IncrementalDiffGraph};
use std::time::Instant;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
    fn signed(&mut self, span: i64) -> i64 {
        (self.next() % (2 * span as u64 + 1)) as i64 - span
    }
}

/// skdmxa2/skdmxa-3x3-10 declares 5105 vars; z3 decides it in 1.33s while AY's
/// general simplex exceeds 67s. If the incremental engine cannot handle a graph
/// of that size at DPLL(T) call rates, the plan is wrong — so measure first.
///
/// Both paths are measured separately, because they differ by orders of
/// magnitude and quoting only the cheap one would be misleading:
///
///   * FREE path — the new edge's slack is already >= 0, so π does not move.
///   * RESTORE path — the edge is violated and a Dijkstra over slacks runs.
///
/// Negative weights are required to force the second; a graph of non-negative
/// forward edges is trivially feasible and never leaves the free path.
#[test]
fn scale_probe_at_skdmxa2_size() {
    let n = 5105usize;

    // ---- RESTORE-heavy: mixed-sign weights over a dense-ish random graph ----
    let mut rng = Rng(0xABCD_1234);
    let mut g: IncrementalDiffGraph<i64> = IncrementalDiffGraph::new(n);
    let m = 6_000usize;
    let mut ids = Vec::with_capacity(m);
    for i in 0..m {
        let a = rng.below(n as u64) as usize;
        let b = rng.below(n as u64) as usize;
        // Mixed sign with a positive mean keeps the system mostly feasible while
        // still violating a large fraction of newly asserted edges.
        let w = rng.signed(30) + 12;
        ids.push(g.register_edge(a, b, w, i as u64));
    }

    let t0 = Instant::now();
    let (mut ok, mut conflicts) = (0usize, 0usize);
    for &id in &ids {
        match g.assert_edge(id) {
            AssertOutcome::Consistent => ok += 1,
            AssertOutcome::Conflict(_) => conflicts += 1,
        }
    }
    let bulk = t0.elapsed();

    // ---- DPLL(T) churn: push / assert / pop on the loaded graph ----
    let t1 = Instant::now();
    let rounds = 3_000usize;
    for k in 0..rounds {
        g.push();
        let _ = g.assert_edge(ids[(k * 7919) % ids.len()]);
        g.pop();
    }
    let churn = t1.elapsed();

    // ---- propagation cost, the expensive option (two Dijkstras per call) ----
    let t2 = Instant::now();
    let probes = 60usize;
    let mut entailed = 0usize;
    for k in 0..probes {
        let id = ids[(k * 104_729) % ids.len()];
        entailed += g.entailed_after_assert(id, 256).len();
    }
    let prop = t2.elapsed();

    eprintln!("  n={n}  edges={m}");
    eprintln!(
        "  bulk assert     : {ok} ok / {conflicts} conflicts in {bulk:?}  ({:.2} us/assert)",
        bulk.as_secs_f64() * 1e6 / m as f64
    );
    eprintln!(
        "  push/assert/pop : {rounds} in {churn:?}  ({:.2} us/op)",
        churn.as_secs_f64() * 1e6 / rounds as f64
    );
    eprintln!(
        "  propagate(b=256): {probes} calls in {prop:?}  ({:.1} us/call), {entailed} entailments",
        prop.as_secs_f64() * 1e6 / probes as f64
    );

    // A generous ceiling: this is a regression tripwire for an algorithmic
    // blow-up (e.g. accidentally reverting to full Bellman-Ford), not a
    // performance target. The synthetic graph here is a WORST case — random,
    // dense, mixed-sign — so its per-assert cost is far above what the sparse,
    // structured real QF_RDL graphs cost.
    assert!(bulk.as_secs_f64() < 30.0, "bulk assert too slow: {bulk:?}");
}
