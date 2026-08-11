// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve a model from an MPS file, so `ay-milp` can be pointed at MIPLIB and compared with
//! every other solver on the same bytes.
//!
//! ```text
//! cargo run --release -p ay-milp --example mps_solve -- flugpl.mps 60
//! ```
//!
//! Prints one machine-readable line: `status value time nodes`, plus the model's shape.

use std::time::{Duration, Instant};

use ay_milp::{BabSession, ColKind, Outcome, SolveOpts};

/// COUNTING GLOBAL ALLOCATOR — load-invariant evidence for a change that claims to remove work.
///
/// Wall clock on a loaded box is noise; allocation count is not. This wraps the system allocator
/// with two relaxed counters and is reported under `AY_MILP_ALLOCSTAT`. The counters are bumped
/// unconditionally (a branch on an env flag inside `alloc` would cost more than the `fetch_add`),
/// and every measurement in the campaign report is taken with this same binary, so the overhead
/// is common-mode between baseline and candidate.
struct Counting;

static ALLOC_N: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static ALLOC_B: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

unsafe impl std::alloc::GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: std::alloc::Layout) -> *mut u8 {
        ALLOC_N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        ALLOC_B.fetch_add(l.size() as u64, std::sync::atomic::Ordering::Relaxed);
        unsafe { std::alloc::System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: std::alloc::Layout) {
        unsafe { std::alloc::System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: std::alloc::Layout, n: usize) -> *mut u8 {
        ALLOC_N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        ALLOC_B.fetch_add(n as u64, std::sync::atomic::Ordering::Relaxed);
        unsafe { std::alloc::System.realloc(p, l, n) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

fn main() {
    // Dump on EVERY exit path, including the diagnostic early returns (`AY_ROOT_CLOSURE` is the
    // deterministic, load-invariant way to measure the root cut loop, and it returns before the
    // bottom of `main`).
    struct Dump;
    impl Drop for Dump {
        fn drop(&mut self) {
            ay_milp::sepstat::dump();
            if std::env::var_os("AY_MILP_ALLOCSTAT").is_some() {
                eprintln!(
                    "AY_ALLOCSTAT allocs={} bytes={}",
                    ALLOC_N.load(std::sync::atomic::Ordering::Relaxed),
                    ALLOC_B.load(std::sync::atomic::Ordering::Relaxed),
                );
            }
        }
    }
    let _dump = Dump;
    let mut args = std::env::args().skip(1);
    let Some(path) = args.next() else {
        eprintln!("usage: mps_solve <file.mps> [seconds]");
        std::process::exit(2);
    };
    let secs: f64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(60.0);

    let text = read_maybe_gz(&path).unwrap_or_else(|e| {
        eprintln!("cannot read {path}: {e}");
        std::process::exit(2);
    });
    let p = ay_milp::read_mps(&text).unwrap_or_else(|e| {
        eprintln!("PARSE_ERROR {e}");
        std::process::exit(3);
    });

    // `AY_MILP_DUAL_CUTOFF` IS READ IN THE MODEL'S OBJECTIVE FRAME, AND THIS FILE IS NOT IN IT.
    //
    // The reader multiplies the objective by `obj_scale` (an integralising LCM times a power-of-two
    // normaliser) so its coefficients are exactly representable; every value the solver holds is in
    // those units, and this example already divides by `obj_scale` on the way OUT. An external dual
    // bound arrives in the FILE's units — a Gurobi `ObjBound`, a published optimum — so it needs the
    // same map in the other direction, and getting it wrong is not a cosmetic error: the cutoff
    // PRUNES, so a bound landed in the wrong frame silently deletes the optimum. It did, at first:
    // gt2 (`obj_scale` = 1/8) took the injected 21166 as a bound eight times too strong and returned
    // "OPTIMAL 126223" at node 0 against a true optimum of 21166. The exact rational round-trip is
    // the whole point of holding `obj_scale` as a `BigRational`.
    //
    // SAFETY: single-threaded — this runs before `BabSession` exists, so before any solver thread
    // can read the environment, and nothing else in this process writes it.
    if let Ok(v) = std::env::var("AY_MILP_DUAL_CUTOFF") {
        match v.parse::<f64>().and_then(|f| {
            num_rational::BigRational::from_float(f).ok_or_else(|| "".parse::<f64>().unwrap_err())
        }) {
            Ok(file_frame) => {
                let model_frame = &file_frame * &p.obj_scale;
                let mut scaled = num_traits::ToPrimitive::to_f64(&model_frame).unwrap_or(f64::NAN);
                // `to_f64` rounds to NEAREST, which can land the bound a hair on the STRONG
                // side — and on the strong side this thing deletes optima. Step back outward
                // by a relative 2^-52 whenever the rational is not an f64; a dual bound is
                // still a dual bound after being weakened, and the tree only loses the last
                // ulp of the prune.
                if num_rational::BigRational::from_float(scaled).as_ref() != Some(&model_frame) {
                    let out = scaled.abs() * f64::EPSILON;
                    scaled = match p.model.sense() {
                        ay_milp::Sense::Minimize => scaled - out,
                        ay_milp::Sense::Maximize => scaled + out,
                    };
                }
                eprintln!(
                    "AY_MILP_DUAL_CUTOFF: {v} (file frame) -> {scaled} (model frame, obj_scale {})",
                    p.obj_scale
                );
                unsafe { std::env::set_var("AY_MILP_DUAL_CUTOFF", format!("{scaled:?}")) };
            }
            Err(_) => {
                eprintln!("AY_MILP_DUAL_CUTOFF: `{v}` is not a finite number, ignoring");
                unsafe { std::env::remove_var("AY_MILP_DUAL_CUTOFF") };
            }
        }
    }

    let (mut bin, mut int, mut con) = (0, 0, 0);
    for j in 0..p.model.num_cols() {
        let c = p.model.col_at(j).expect("in range");
        match p.model.col_kind(c) {
            ColKind::Binary => bin += 1,
            ColKind::Integer => int += 1,
            _ => con += 1,
        }
    }
    eprintln!(
        "{}: {} rows, {} cols ({bin} bin, {int} int, {con} cont), sense {:?}",
        p.name,
        p.model.num_rows(),
        p.model.num_cols(),
        p.model.sense()
    );

    // W0 MEASUREMENT: root dual bound before and after the cut loop, no branching.
    // The one signal that attributes a change to the CUTS rather than to the tree.
    // Reported on stdout in the file's own objective frame (un-scaled, re-sensed), so
    // it is directly comparable with a published optimum and with another solver's
    // root bound.
    if std::env::var_os("AY_ROOT_CLOSURE").is_some() {
        use num_traits::ToPrimitive as _;
        let line = ay_milp::diag_root_closure(&p.model, secs);
        // The diagnostic already reports in the model's own sense/offset frame; what it
        // cannot undo is the reader's integralising objective scale, which lives here.
        let scale = p.obj_scale.to_f64().unwrap_or(1.0);
        let rescaled = line
            .split_whitespace()
            .map(|tok| match tok.split_once('=') {
                Some((k @ ("bound_lp" | "bound_cut" | "gain"), v)) => {
                    let x: f64 = v.parse().unwrap_or(f64::NAN);
                    format!("{k}={}", x / scale)
                }
                _ => tok.to_string(),
            })
            .collect::<Vec<_>>()
            .join(" ");
        println!("{rescaled}");
        // INSTRUMENTATION GAP, closed. This early return preceded the ITERLEDGER
        // dump at the bottom of the file, so `AY_MILP_ITER_LEDGER=1` was silently
        // a no-op in root-closure mode — the ONE mode whose whole subject is
        // where the root LP's iterations go. Same emission as the `AY_LP_ONLY`
        // arm just below, which already did this correctly.
        if std::env::var_os("AY_MILP_ITER_LEDGER").is_some() {
            let ledger = ay_milp::iter_ledger_line();
            if !ledger.is_empty() {
                eprintln!("{ledger}");
            }
        }
        return;
    }

    // Diagnostic: solve just the float-lane LP relaxation (cold) and report
    // iteration economics; AY_MILP_LP_STATS=1 adds per-phase LPSTAT lines.
    if std::env::var_os("AY_LP_ONLY").is_some() {
        eprintln!("{}", ay_milp::diag_float_lp(&p.model, secs));
        if std::env::var_os("AY_MILP_ITER_PROFILE").is_some() {
            let line = ay_milp::rt_profile_line();
            if !line.is_empty() {
                eprintln!("{line}");
            }
            let uline = ay_milp::upd_profile_line();
            if !uline.is_empty() {
                eprintln!("{uline}");
            }
            let pxline = ay_milp::px_profile_line();
            if !pxline.is_empty() {
                eprintln!("{pxline}");
            }
        }
        if std::env::var_os("AY_MILP_ITER_LEDGER").is_some() {
            let ledger = ay_milp::iter_ledger_line();
            if !ledger.is_empty() {
                eprintln!("{ledger}");
            }
        }
        return;
    }

    // MARGIN REFRAME DEMO. `AY_MILP_MARGIN_ROW=last` (or a 0-based row index)
    // names a band-violation row in this objective-≡0 feasibility model and
    // reports the reframed dual bound — the number that "comes alive" (nonzero,
    // informative) versus the trivial 0 of the zero objective. This exercises
    // the same `mark_margin_row` + reframe path `BabSession::check` takes.
    if let Ok(spec) = std::env::var("AY_MILP_MARGIN_ROW") {
        let nrows = p.model.num_rows();
        let row_idx = if spec.eq_ignore_ascii_case("last") {
            nrows.checked_sub(1)
        } else {
            spec.parse::<usize>().ok()
        };
        let Some(row_idx) = row_idx.filter(|&i| i < nrows) else {
            eprintln!("AY_MILP_MARGIN_ROW: bad row `{spec}` ({nrows} rows)");
            std::process::exit(2);
        };
        let mut m = p.model.clone();
        let row = m.row_at(row_idx).expect("in range");
        if let Err(e) = m.mark_margin_row(row) {
            eprintln!("mark_margin_row({row_idx}): {e}");
            std::process::exit(2);
        }
        eprintln!("{}", ay_milp::diag_margin_reframe(&m, secs));
        return;
    }

    // Cross-check: take another solver's optimum, PIN this model's integer columns to its
    // integer values, and solve the rest exactly. If the model in the file has that solution,
    // this must come back OPTIMAL at the published value -- and if it does, any verdict of
    // INFEASIBLE from the search is the search's fault, not the reader's.
    //
    // Only the integer columns are pinned. The continuous ones are re-derived here, because a
    // rival's float output ("600.0000000000003") is not a rational that satisfies an equality
    // row, and feeding it in as one would manufacture a violation that is not in the model.
    if let Ok(sol) = std::env::var("AY_CHECK_SOL") {
        let text = std::fs::read_to_string(&sol).expect("read solution");
        let index: std::collections::HashMap<&str, usize> = p
            .col_names
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), i))
            .collect();
        let mut m = p.model.clone();
        let mut pinned = 0;
        for line in text.lines() {
            let f: Vec<&str> = line.split_whitespace().collect();
            let [nm, v] = f[..] else { continue };
            let (Some(&j), Ok(x)) = (index.get(nm), v.parse::<f64>()) else {
                continue;
            };
            let c = m.col_at(j).expect("in range");
            if m.col_kind(c).is_integral() {
                m.fix_col(c, x.round());
                pinned += 1;
            }
        }
        eprintln!("cross-check: pinned {pinned} integer columns to the reference solution");
        let opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
        // Lever A: hand the pinned model to the session (moved, not cloned); `m`
        // is not read again on this cross-check branch.
        let mut s = BabSession::new(m, &opts).expect("model");
        match s.check() {
            Ok(Outcome::Optimal { value, .. }) => {
                eprintln!(
                    "cross-check: OPTIMAL at {} -- the model HAS this solution",
                    ratio_str(&p.unscale(&value))
                );
            }
            Ok(o) => eprintln!("cross-check: {o:?}"),
            Err(e) => eprintln!("cross-check: ERROR {e:?}"),
        }
        return;
    }

    let mut opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
    // Measurement lever: `AY_MILP_TREE_CERT_LEAVES=N` sets the tree-certificate
    // leaf budget (default 256). Set it to 0 to opt into the certificate-free
    // fast path, which enables duplicate-column merging and makes the separately
    // gated `AY_MILP_SINGLETON_SUB=1` substitution eligible to run.
    if let Ok(v) = std::env::var("AY_MILP_TREE_CERT_LEAVES") {
        if let Ok(n) = v.parse::<usize>() {
            opts = opts.with_tree_cert_leaves(n);
        }
    }
    // Typed parallelism, for measurement runs: `AY_MILP_THREADS=N` (N > 1)
    // requests N worker threads through the SolveOpts contract and opts out of
    // the determinism default (deterministic solves always take the serial
    // paths). `AY_MILP_LATTICE_THREADS`/`NBCORE` remain ceilings only.
    if let Ok(v) = std::env::var("AY_MILP_THREADS") {
        if let Ok(n) = v.parse::<u32>() {
            if n > 1 {
                opts = opts.with_threads(n).with_determinism(false);
            }
        }
    }
    // Lever A: MOVE the parsed model into the session so only ONE f64 matrix is
    // resident during the solve (was: `&p.model`, which kept the parser's copy
    // alive alongside the session's clone). The model is read back below via
    // `s.model()`; the remaining `p` fields (`obj_scale`, `col_names`) are small
    // and stay accessible after this partial move. Byte-identical output.
    let mut s = match BabSession::new(p.model, &opts) {
        Ok(s) => s,
        Err(e) => {
            println!("SETUP_ERROR {e:?} - -");
            return;
        }
    };
    // Measurement harness: seed the search with a reference incumbent (name value per line,
    // e.g. a HiGHS --solution_file). Advice only — `seed_incumbent` candidates are exactly
    // re-checked before belief, so a wrong file cannot corrupt a verdict. This isolates
    // "the primal is the blocker" from "the enumeration is the blocker" on an instance.
    if let Ok(seedf) = std::env::var("AY_MILP_SEED_SOL") {
        let text = std::fs::read_to_string(&seedf).expect("read seed solution");
        let index: std::collections::HashMap<&str, usize> = p
            .col_names
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), i))
            .collect();
        let mut vals = vec![0.0f64; s.model().num_cols()];
        let mut hits = 0usize;
        for line in text.lines() {
            let f: Vec<&str> = line.split_whitespace().collect();
            let [nm, v] = f[..] else { continue };
            if let (Some(&j), Ok(x)) = (index.get(nm), v.parse::<f64>()) {
                vals[j] = x;
                hits += 1;
            }
        }
        eprintln!("seed: loaded {hits} column values from {seedf}");
        if hits > 0 {
            s.seed_incumbent(&vals);
        }
    }
    let t0 = Instant::now();
    let out = s.check();
    let dt = t0.elapsed().as_secs_f64();

    // NODES-TO-PROOF, appended as the line's fourth field — the shape this example's own
    // doc comment has always advertised (`status value time nodes`). Wall clock moves with
    // machine load; the node count does not, so it is the signal that says whether two
    // builds ran the SAME search rather than merely reached the same answer. Appending
    // leaves every existing parser (which reads fields 0 and 1) working unchanged.
    let nodes = ay_milp::nodes_explored();

    // The reader multiplied the objective through to make its coefficients exactly
    // representable. That scaling never moved the argmin, but it did rename the value, so undo
    // it -- exactly, with rationals -- before reporting a number anyone will compare.
    // DEPRECATED SHIM. This example is kept, byte-identical on stdout, because
    // every measurement campaign in the journal invokes it by this name and a
    // paper trail that stops reproducing is a real loss. New work should use the
    // `ay-milp` binary, which has real flags, certificate emission, and a
    // checker: `ay-milp solve <file> --time-limit <secs>`.
    match out {
        Ok(Outcome::Optimal {
            ref value,
            ref model_values,
            ..
        }) => {
            // THE HOLE THIS FIXES. `AY_DUMP_SOL` used to live only on the
            // `Feasible` arm, so `AY_DUMP_SOL=/tmp/x mps_solve markshare1.mps 30`
            // printed `OPTIMAL 1` and created NO FILE — the witness of a PROVEN
            // optimum was the one thing you could not get out. Same file format,
            // now on both arms. stdout is untouched.
            dump_sol(&p.col_names, model_values);
            println!(
                "OPTIMAL {} {dt:.3} {nodes}",
                ratio_str(&(value / &p.obj_scale))
            );
        }
        Ok(Outcome::Feasible {
            model_values,
            dual_bound,
            ..
        }) => {
            // Diagnostic: dump the incumbent point (name value per line) so it can be
            // compared against a reference solver's optimum.
            dump_sol(&p.col_names, &model_values);
            let v = s.model().objective_value_at(&model_values);
            // The rigorous dual bound, on stderr so the machine-readable stdout line keeps
            // its shape. Unscaled like the value: it is compared against published optima.
            if let Some(db) = &dual_bound {
                eprintln!(
                    "dual bound (rigorous) = {}",
                    ratio_str(&(db / &p.obj_scale))
                );
            }
            println!(
                "FEASIBLE {} {dt:.3} {nodes}",
                ratio_str(&(&v / &p.obj_scale))
            );
        }
        // NO PRIMAL POINT, BUT A RIGOROUS DUAL BOUND. An interrupted tree that
        // never found an incumbent used to print `UNKNOWN Timeout` even when it
        // held a valid bound on the optimum; it now reports the bound. The value
        // column carries the bound (unscaled like every other value here, so it
        // is directly comparable against `ref_obj`), keeping the
        // "STATUS value time nodes" shape every harness in the journal parses.
        Ok(Outcome::Bound {
            ref dual_bound,
            rigorous,
        }) => println!(
            "BOUND{} {} {dt:.3} {nodes}",
            if rigorous { "" } else { "-HEURISTIC" },
            ratio_str(&(dual_bound / &p.obj_scale))
        ),
        Ok(Outcome::Infeasible { .. }) => println!("INFEASIBLE - {dt:.3} {nodes}"),
        Ok(Outcome::Unbounded) => println!("UNBOUNDED - {dt:.3} {nodes}"),
        Ok(Outcome::Unknown { reason }) => println!("UNKNOWN {reason:?} {dt:.3} {nodes}"),
        Err(e) => println!("ERROR {e:?} {dt:.3} {nodes}"),
        Ok(other) => println!("OTHER {other:?} {dt:.3} {nodes}"),
    }
    // Fused ratio-test profiler (AY_MILP_ITER_PROFILE): us/pivot split of the dual
    // ratio test's build vs select phases. Empty line when unsampled.
    if std::env::var_os("AY_MILP_ITER_PROFILE").is_some() {
        let line = ay_milp::rt_profile_line();
        if !line.is_empty() {
            eprintln!("{line}");
        }
        let uline = ay_milp::upd_profile_line();
        if !uline.is_empty() {
            eprintln!("{uline}");
        }
        let pxline = ay_milp::px_profile_line();
        if !pxline.is_empty() {
            eprintln!("{pxline}");
        }
        let sbline = ay_milp::sb_profile_line();
        if !sbline.is_empty() {
            eprintln!("{sbline}");
        }
    }
    // ITERATION LEDGER (AY_MILP_ITER_LEDGER): one parseable ITERLEDGER line
    // attributing every simplex iteration to the solve phase that ran it, with
    // the solve count per phase so iterations-per-solve is readable. Counts
    // only, never time: the line is identical on an idle and a contended box.
    if std::env::var_os("AY_MILP_ITER_LEDGER").is_some() {
        let ledger = ay_milp::iter_ledger_line();
        if !ledger.is_empty() {
            eprintln!("{ledger}");
        }
    }
    if std::env::var_os("AY_MILP_ALLOCSTAT").is_some() {
        eprintln!("AY_ALLOCSTAT nodes={nodes}");
    }
}

/// MIPLIB ships `.mps.gz` and the corpus is kept that way (320 MB gzipped, several
/// gigabytes not). Decompressing through the system `gzip` keeps the engine crate free of
/// a compression dependency for the sake of a measurement example.
fn read_maybe_gz(path: &str) -> std::io::Result<String> {
    if !path
        .get(path.len().saturating_sub(3)..)
        .is_some_and(|extension| extension.eq_ignore_ascii_case(".gz"))
    {
        return std::fs::read_to_string(path);
    }
    let out = std::process::Command::new("gzip")
        .args(["-dc", path])
        .output()?;
    if !out.status.success() {
        return Err(std::io::Error::other(format!(
            "gzip -dc {path}: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        )));
    }
    String::from_utf8(out.stdout).map_err(std::io::Error::other)
}

/// Write the point as `name value` per line, the historical `AY_DUMP_SOL`
/// format, when that variable is set.
///
/// The deprecation note goes to stderr and only on runs that set the variable,
/// so no existing parser sees a byte it did not see before.
fn dump_sol(col_names: &[String], model_values: &[num_rational::BigRational]) {
    let Ok(dump) = std::env::var("AY_DUMP_SOL") else {
        return;
    };
    eprintln!(
        "note: AY_DUMP_SOL is deprecated, use `ay-milp solve --emit-witness {dump}` \
         (the env name still works)"
    );
    use std::io::Write as _;
    if let Ok(mut f) = std::fs::File::create(&dump) {
        for (j, v) in model_values.iter().enumerate() {
            let _ = writeln!(f, "{} {}", col_names[j], ratio_str(v));
        }
    }
}

/// A rational objective as a decimal, which is what every other solver prints.
fn ratio_str(v: &num_rational::BigRational) -> String {
    use num_traits::ToPrimitive;
    v.to_f64().map_or_else(|| v.to_string(), |f| format!("{f}"))
}
