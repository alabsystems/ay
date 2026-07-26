// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! STAGE-0 COLD-CLONE PARALLEL-READINESS PROOF-OF-CONCEPT.
//!
//! The parallel branch-and-bound plan
//! (the development design notes) rests on ONE
//! prerequisite (worklist #1): an owned per-worker `FloatLp::clone()` can move into
//! a thread and solve an independent COLD node relaxation concurrently, producing
//! the same exact per-node bound as a fresh serial clone.
//!
//! This test validates that limited property empirically without touching the serial
//! hot path. It does not exercise production warm bases, dynamic cut slots, or tree
//! scheduling, so passing it is a feasibility signal rather than a proof that a
//! future parallel B&B implementation is sound.
//!
//! The four claims (mirroring the task's a–d):
//!   (a) `FloatLp::clone()` compiles, is `Send`, and cross-thread solves run without
//!       panic or data race;
//!   (b) a cloned engine's per-node bound EQUALS the serial engine's, exactly, for
//!       both stateless (fresh clone per node) and persistent (one clone per worker,
//!       many nodes) usage;
//!   (c) N-thread concurrent node-solve throughput vs serial (raw LP throughput);
//!   (d) the per-clone memory cost for air05's ~7195-col matrix.
//!
//! The always-on guard includes an in-repository MPS fixture. Larger models are
//! located via `AY_MILP_CORPUS` (a dir of `*.mps`) or known developer corpus dirs;
//! absent optional models skip with a diagnostic.

use std::path::PathBuf;
use std::time::{Duration, Instant};

use ay_milp::{read_mps, ColKind, Model, NodeBound, NodeLpProbe};
use num_rational::BigRational;

const SMOKE_MPS: &str = "\
NAME          parallel-smoke
ROWS
 N  obj
 G  cover
 L  cap
COLUMNS
    MARK0     'MARKER'                 'INTORG'
    x         obj                 1   cover               1
    x         cap                 2
    y         obj                 2   cover               1
    y         cap                 1
    z         obj                 3   cover               1
    z         cap                 1
    MARK1     'MARKER'                 'INTEND'
RHS
    RHS       cover               1   cap                 2
BOUNDS
 BV BND       x
 BV BND       y
 BV BND       z
ENDATA
";

// --- (a) COMPILE-TIME PROOF that the per-worker engine is `Send` (movable into a
// --- thread) — the mechanical half of worklist #1. If `FloatLp` were not `Send`
// --- (e.g. an `Rc` slipped into a cache) this would fail to compile.
fn assert_send<T: Send>() {}
const _: fn() = || {
    assert_send::<NodeLpProbe>();
    assert_send::<NodeBound>();
};

/// The comparable fingerprint of a node bound: the safe f64 by its exact BITS, the
/// exact rational, and the two LP-status flags. Byte-equality of this tuple is the
/// "cloning did not perturb the exact result" assertion.
type BoundKey = (Option<u64>, Option<BigRational>, bool, bool);

fn key(b: &NodeBound) -> BoundKey {
    (
        b.safe.map(f64::to_bits),
        b.exact.clone(),
        b.optimal,
        b.infeasible,
    )
}

/// Locate `<name>.mps` across the corpus dirs; `None` (skip) if nowhere found.
fn find_model(name: &str) -> Option<Model> {
    if name == "parallel-smoke" {
        return Some(
            read_mps(SMOKE_MPS)
                .expect("the in-repository parallel smoke model must parse")
                .model,
        );
    }
    let mut dirs: Vec<PathBuf> = Vec::new();
    if let Ok(d) = std::env::var("AY_MILP_CORPUS") {
        dirs.push(PathBuf::from(d));
    }
    dirs.push(PathBuf::from("/private/tmp"));
    for d in dirs {
        let p = d.join(format!("{name}.mps"));
        if let Ok(text) = std::fs::read_to_string(&p) {
            match read_mps(&text) {
                Ok(prob) => {
                    eprintln!("[corpus] loaded {name} from {}", p.display());
                    return Some(prob.model);
                }
                Err(e) => eprintln!("[corpus] {} parse error: {e}", p.display()),
            }
        }
    }
    eprintln!("[corpus] SKIP: {name}.mps not found (set AY_MILP_CORPUS to a dir of .mps)");
    None
}

/// Integer/binary structural columns of `model`.
fn integer_cols(model: &Model) -> Vec<usize> {
    (0..model.num_cols())
        .filter(|&j| {
            model
                .col_at(j)
                .is_some_and(|c| !matches!(model.col_kind(c), ColKind::Continuous))
        })
        .collect()
}

/// A deterministic batch of `count` single-column node subproblems:
/// for integer column `j` alternately pin it to its lower bound (a "down" child)
/// and one unit above (an "up" child), clamped into the box. Each is a genuine,
/// distinct B&B node whose relaxation bound is a pure function of the box.
fn gen_subs(model: &Model, probe: &NodeLpProbe, count: usize) -> Vec<Vec<(usize, f64, f64)>> {
    let ints = integer_cols(model);
    if ints.is_empty() {
        return Vec::new();
    }
    let (lo, up) = probe.root_box();
    let mut subs = Vec::with_capacity(count);
    let mut k = 0usize;
    while subs.len() < count {
        let j = ints[k % ints.len()];
        let base = lo[j];
        let side = (k / ints.len()) % 2;
        let val = if side == 0 {
            base
        } else {
            let v = base + 1.0;
            if up[j].is_finite() && v > up[j] {
                base
            } else {
                v
            }
        };
        subs.push(vec![(j, val, val)]);
        k += 1;
        if k > count.saturating_mul(4) + 8 {
            break; // pathological guard (e.g. a single int column)
        }
    }
    subs.truncate(count);
    subs
}

/// Contiguous work slices: `nthreads` near-equal index ranges over `0..n`.
fn slices(n: usize, nthreads: usize) -> Vec<std::ops::Range<usize>> {
    if n == 0 {
        return Vec::new();
    }
    let nt = nthreads.max(1).min(n);
    let chunk = n.div_ceil(nt);
    (0..nt)
        .map(|w| (w * chunk).min(n)..((w + 1) * chunk).min(n))
        .filter(|r| r.start < r.end)
        .collect()
}

/// SERIAL reference: `nthreads` fresh clones, each solving its contiguous slice in
/// order (persistent per-slice engine — the realistic worker model, run one at a
/// time). Engines are pre-cloned so the returned wall time is pure LP-solve.
fn serial_replay(
    root: &NodeLpProbe,
    subs: &[Vec<(usize, f64, f64)>],
    nthreads: usize,
) -> (Vec<NodeBound>, Duration) {
    let ranges = slices(subs.len(), nthreads);
    let mut engines: Vec<NodeLpProbe> = ranges.iter().map(|_| root.clone()).collect();
    let mut out: Vec<Option<NodeBound>> = (0..subs.len()).map(|_| None).collect();
    let t0 = Instant::now();
    for (engine, range) in engines.iter_mut().zip(&ranges) {
        for i in range.clone() {
            out[i] = Some(engine.solve_node_bound(&subs[i], None));
        }
    }
    let wall = t0.elapsed();
    (out.into_iter().map(Option::unwrap).collect(), wall)
}

/// PARALLEL: the same partition, each slice on its OWN pre-cloned engine, run
/// CONCURRENTLY in scoped threads. Returns the results (reassembled in index order)
/// and the wall time of the concurrent solve region (clone cost excluded).
fn parallel_replay(
    root: &NodeLpProbe,
    subs: &[Vec<(usize, f64, f64)>],
    nthreads: usize,
) -> (Vec<NodeBound>, Duration) {
    let ranges = slices(subs.len(), nthreads);
    // Pre-clone every worker engine OUTSIDE the timed region (worklist #1's
    // one-clone-per-worker); the timing then reflects only concurrent LP solves.
    let engines: Vec<NodeLpProbe> = ranges.iter().map(|_| root.clone()).collect();
    let t0 = Instant::now();
    let collected: Vec<Vec<(usize, NodeBound)>> = std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for (mut engine, range) in engines.into_iter().zip(ranges.iter().cloned()) {
            // `subs` is borrowed read-only by every thread (a `&Model`-style share);
            // `engine` is MOVED in — the exact `Send`-clone-per-worker pattern.
            let subs_ref = subs;
            handles.push(scope.spawn(move || {
                let mut local = Vec::with_capacity(range.len());
                for i in range {
                    local.push((i, engine.solve_node_bound(&subs_ref[i], None)));
                }
                local
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().expect("worker panicked"))
            .collect()
    });
    let wall = t0.elapsed();
    let mut out: Vec<Option<NodeBound>> = (0..subs.len()).map(|_| None).collect();
    for chunk in collected {
        for (i, b) in chunk {
            out[i] = Some(b);
        }
    }
    (out.into_iter().map(Option::unwrap).collect(), wall)
}

/// Best-effort resident-set size (KiB) of THIS process via `ps`; `None` if unusable.
fn rss_kib() -> Option<u64> {
    let out = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output()
        .ok()?;
    String::from_utf8_lossy(&out.stdout)
        .trim()
        .parse::<u64>()
        .ok()
}

// ===========================================================================
// (a)+(b) CORRECTNESS — small model: cloning does not perturb the exact result,
//          across threads, both stateless and persistent.
// ===========================================================================
#[test]
fn clone_cross_thread_bounds_match_serial() {
    for name in ["parallel-smoke", "flugpl", "gt2"] {
        let model = match find_model(name) {
            Some(model) => model,
            None if name == "parallel-smoke" => {
                panic!("the in-repository smoke model must parse")
            }
            None => continue,
        };
        let root = match NodeLpProbe::from_model(&model) {
            Some(root) => root,
            None if name == "parallel-smoke" => {
                panic!("the in-repository smoke model must lower")
            }
            None => {
                eprintln!("[{name}] cannot be lowered — skipping");
                continue;
            }
        };
        let n = root.num_cols();
        eprintln!(
            "[{name}] n={n} cols, per-clone ~{} KiB, {} integer cols",
            root.approx_bytes() / 1024,
            integer_cols(&model).len()
        );

        let subs = gen_subs(&model, &root, 40);
        assert!(!subs.is_empty(), "[{name}] produced no subproblems");

        // --- STATELESS pure-function claim: the canonical bound of each node,
        // --- computed on a FRESH clone (empty caches, cold solve). This is the
        // --- cleanest statement of "clone(root).solve(node) is a pure function".
        let canon: Vec<BoundKey> = subs
            .iter()
            .map(|s| key(&root.clone().solve_node_bound(s, None)))
            .collect();
        let finite = canon
            .iter()
            .filter(|k| k.0.is_some_and(|bits| f64::from_bits(bits).is_finite()))
            .count();
        eprintln!(
            "[{name}] {} subproblems, {finite} with a finite safe bound",
            subs.len()
        );
        assert!(
            finite > 0,
            "[{name}] no subproblem produced a finite bound — test is vacuous"
        );

        // Each of N threads INDEPENDENTLY recomputes the whole batch on its own
        // fresh-per-node clones and must reproduce `canon` byte-for-byte.
        for &nt in &[4usize, 8] {
            let threads: Vec<Vec<BoundKey>> = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..nt)
                    .map(|_| {
                        // Each worker gets its OWN owned engine MOVED in (a `&root`
                        // capture will NOT compile: `FloatLp` is `!Sync`, so a shared
                        // `&NodeLpProbe` is not `Send` — worklist #1's exact reason
                        // per-worker clones are mandatory). The worker then makes a
                        // fresh clone per node for a pristine cold solve.
                        let root_owned = root.clone();
                        let subs_ref = &subs;
                        scope.spawn(move || {
                            subs_ref
                                .iter()
                                .map(|s| key(&root_owned.clone().solve_node_bound(s, None)))
                                .collect::<Vec<_>>()
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|h| h.join().expect("worker panicked"))
                    .collect()
            });
            for (t, got) in threads.iter().enumerate() {
                assert_eq!(
                    got, &canon,
                    "[{name}] stateless clone on thread {t}/{nt} disagreed with serial canonical bound"
                );
            }
            eprintln!(
                "[{name}] STATELESS: {nt} threads all reproduced the canonical bounds exactly"
            );

            // --- PERSISTENT claim (the realistic worker): one clone per worker,
            // --- each solving a contiguous slice of many nodes in sequence. The
            // --- concurrent run must equal the sequential run node-for-node.
            let (ser, _) = serial_replay(&root, &subs, nt);
            let (par, _) = parallel_replay(&root, &subs, nt);
            let ser_keys: Vec<_> = ser.iter().map(key).collect();
            let par_keys: Vec<_> = par.iter().map(key).collect();
            assert_eq!(
                ser_keys, canon,
                "[{name}] PERSISTENT: {nt}-slice serial replay disagreed with fresh canonical bounds"
            );
            assert_eq!(
                par_keys, canon,
                "[{name}] PERSISTENT: {nt}-thread replay disagreed with fresh canonical bounds"
            );
            eprintln!("[{name}] PERSISTENT: {nt}-thread replay matched fresh canonical bounds");
        }
    }
}

// ===========================================================================
// (a)+(b)+(c)+(d) BOUNDED CHARACTERIZATION — always exercises the in-repository
//   model. An explicit AY_MILP_PARALLEL_STRESS setting additionally includes
//   air05 (wide, ~7195 cols) and mas74 from AY_MILP_CORPUS.
// ===========================================================================
#[test]
fn bounded_parallel_throughput_and_memory_characterization() {
    let mut workloads = vec![("parallel-smoke", 12usize)];
    if std::env::var_os("AY_MILP_PARALLEL_STRESS").is_some() {
        workloads.extend([("air05", 48usize), ("mas74", 96usize)]);
    }

    let mut ran_any = false;
    for (name, batch) in workloads {
        let Some(model) = find_model(name) else {
            continue;
        };
        let Some(root) = NodeLpProbe::from_model(&model) else {
            eprintln!("[{name}] cannot be lowered — skipping");
            continue;
        };
        let n = root.num_cols();

        // --- (d) PER-CLONE MEMORY. Deterministic structural estimate + an
        // --- empirical RSS delta from holding 8 live clones.
        let per_clone = root.approx_bytes();
        let n_hold = if name == "parallel-smoke" {
            4usize
        } else {
            8usize
        };
        let rss_before = rss_kib();
        let held: Vec<NodeLpProbe> = (0..n_hold).map(|_| root.clone()).collect();
        let rss_after = rss_kib();
        let clone_t0 = Instant::now();
        let _timed: Vec<NodeLpProbe> = (0..n_hold).map(|_| root.clone()).collect();
        let per_clone_wall = clone_t0.elapsed() / n_hold as u32;
        eprintln!(
            "[{name}] n={n} cols | per-clone ~{} KiB (structural), clone time ~{:?}",
            per_clone / 1024,
            per_clone_wall
        );
        if let (Some(a), Some(b)) = (rss_before, rss_after) {
            eprintln!(
                "[{name}] RSS delta holding {n_hold} clones: {} KiB (~{} KiB/clone empirical)",
                b.saturating_sub(a),
                b.saturating_sub(a) / n_hold as u64
            );
        }
        eprintln!(
            "[{name}] projected resident matrix at 16 workers: ~{} MiB",
            per_clone * 16 / (1024 * 1024)
        );
        drop(held);

        let subs = gen_subs(&model, &root, batch);
        if subs.is_empty() {
            assert_ne!(
                name, "parallel-smoke",
                "the in-repository smoke model must produce integer subproblems"
            );
            eprintln!("[{name}] no integer columns — skipping optional solve stress");
            continue;
        }

        // Baseline: total solves across the batch, single thread (1 engine per
        // slice, but nthreads=1 => one engine over the whole batch).
        let (base, base_wall) = serial_replay(&root, &subs, 1);
        let base_keys: Vec<_> = base.iter().map(key).collect();
        let canonical_keys: Vec<_> = subs
            .iter()
            .map(|s| key(&root.clone().solve_node_bound(s, None)))
            .collect();
        assert_eq!(
            base_keys, canonical_keys,
            "[{name}] persistent serial baseline disagreed with fresh canonical bounds"
        );
        let solves = subs.len();
        eprintln!(
            "[{name}] serial baseline: {solves} node-LP solves in {:.3}s = {:.0} solves/s",
            base_wall.as_secs_f64(),
            solves as f64 / base_wall.as_secs_f64().max(1e-9)
        );

        // --- (c) THROUGHPUT at 4T and 8T, across a few workload permutations
        // --- ("seeds": rotations of the batch, so different nodes land on
        // --- different workers). Every run re-asserts concurrent == serial.
        let worker_counts: &[usize] = if name == "parallel-smoke" {
            &[2, 4]
        } else {
            &[4, 8]
        };
        let rotations: &[usize] = if name == "parallel-smoke" {
            &[0, 1]
        } else {
            &[0, 11]
        };
        for &nt in worker_counts {
            let mut best_ratio = 0.0f64;
            let mut par_solves_per_s = 0.0f64;
            for &rot in rotations {
                let mut rotated = subs.clone();
                let len = rotated.len().max(1);
                rotated.rotate_left(rot % len);
                let mut rotated_canonical = canonical_keys.clone();
                rotated_canonical.rotate_left(rot % len);

                let (ser, ser_wall) = serial_replay(&root, &rotated, nt);
                let (par, par_wall) = parallel_replay(&root, &rotated, nt);

                // SOUNDNESS UNDER CONCURRENCY: identical partition, identical order,
                // only the concurrency differs — so the bounds MUST be identical.
                let ser_keys: Vec<_> = ser.iter().map(key).collect();
                let par_keys: Vec<_> = par.iter().map(key).collect();
                assert_eq!(
                    ser_keys, rotated_canonical,
                    "[{name}] {nt}T rot={rot}: serial persistent replay disagreed with fresh canonical bounds"
                );
                assert_eq!(
                    par_keys, rotated_canonical,
                    "[{name}] {nt}T rot={rot}: concurrent replay disagreed with fresh canonical bounds"
                );

                let ratio = ser_wall.as_secs_f64() / par_wall.as_secs_f64().max(1e-9);
                best_ratio = best_ratio.max(ratio);
                par_solves_per_s =
                    par_solves_per_s.max(rotated.len() as f64 / par_wall.as_secs_f64().max(1e-9));
            }
            eprintln!(
                "[{name}] {nt}T: best speedup {best_ratio:.2}x (serial/parallel LP-solve wall), \
                 up to {par_solves_per_s:.0} solves/s [LOAD-CAVEATED: shared box]"
            );
        }

        // Also confirm the batch's serial result is stable across a re-run (a
        // determinism sanity check the concurrency assertions lean on).
        let (base2, _) = serial_replay(&root, &subs, 1);
        let base2_keys: Vec<_> = base2.iter().map(key).collect();
        assert_eq!(
            base2_keys, base_keys,
            "[{name}] serial baseline is non-deterministic"
        );
        ran_any = true;
    }
    assert!(
        ran_any,
        "the in-repository parallel smoke workload must always run"
    );
}
