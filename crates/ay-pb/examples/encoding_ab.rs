// CNF-encoding A/B measurement harness (PB26 encoding-layer work).
//
// Two modes, both single-threaded and deterministic so wall-clock A/B
// comparisons attribute time to the encoding + SAT search alone:
//
//   profile <file.opb>
//     Parse + encode the instance with `CnfEncoder::encode_instance_with_profile`
//     and print encode size (vars/clauses/aux) plus the Auto strategy mix and
//     objective shape. Machine-readable single line.
//
//   solve <file.opb> <auto|linear|binary|oll> [timeout_ms]
//     Replicates the portfolio's SAT-encoded optimization arm
//     (`solve_optimization_sat_with_strategy`): encode -> import into ay-sat ->
//     `OptimizationEngine` with the forced strategy -> solve under a wall-clock
//     deadline (with the production-style inprocessing interrupt watchdog).
//     Prints verdict, objective, and phase timings.
//
// Usage: cargo run --release -p ay-pb --example encoding_ab -- <mode> <file> ...

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use ay_pb::{parse_opb, CnfEncoder, OptResult, OptStrategy, OptimizationEngine};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mode = args.first().map(String::as_str).unwrap_or("");
    match mode {
        "profile" => profile(&args[1..]),
        "rows" => rows(&args[1..]),
        "solve" => solve(&args[1..]),
        _ => {
            eprintln!("usage: encoding_ab profile <file.opb>");
            eprintln!("       encoding_ab rows <file.opb>");
            eprintln!("       encoding_ab solve <file.opb> <auto|linear|binary|oll> [timeout_ms]");
            std::process::exit(2);
        }
    }
}

// ---------------------------------------------------------------------------
// rows mode: normalized-row shape analysis for encoder-routing measurement.
//
// Re-implements (for MEASUREMENT ONLY — never used to answer instances) the
// encoder's normalization of each linear constraint into >=-rows with positive
// coefficients (including saturation at rhs and gcd division), classifies each
// row with the current `auto_select` + clamp routing, and for "gap" rows
// (max_coeff <= 10_000 < rhs, currently routed to the adder) computes:
//   * a generalized-totalizer dry-run estimate (aux outputs, clause upper
//     bound, pair-merge work), and
//   * a BDD dry-run estimate (memo node count; clauses <= 2*nodes + 1),
// so encoder budgets can be sized from real corpus data.
// ---------------------------------------------------------------------------

fn rows(args: &[String]) {
    let path = args.first().expect("rows: missing <file.opb>");
    let text = std::fs::read_to_string(path).expect("failed to read instance");
    let instance = match parse_opb(&text) {
        Ok(instance) => instance,
        Err(err) => {
            println!("ROWS file={path} error=parse:{err:?}");
            return;
        }
    };

    let mut normalized: Vec<(Vec<i128>, i128)> = Vec::new();
    let mut nonlinear = 0usize;
    for c in &instance.constraints {
        let mut terms: Vec<i128> = Vec::new();
        let mut linear = true;
        for t in &c.terms {
            if t.lits.len() != 1 {
                linear = false;
                break;
            }
            terms.push(t.coeff);
        }
        if !linear {
            nonlinear += 1;
            continue;
        }
        normalized.push(normalize_row(&terms, c.rhs));
        if c.rel == ay_pb::PbRel::Eq {
            let neg: Vec<i128> = terms.iter().map(|&c| -c).collect();
            normalized.push(normalize_row(&neg, -c.rhs));
        }
    }

    // Simulated upper-bound row for the objective (binary-search probe shape):
    // obj <= mid, i.e. sum(-w_i x_i) >= -mid, at the midpoint of [0, total].
    if let Some(obj) = &instance.objective {
        let all_single = obj.terms.iter().all(|t| t.lits.len() == 1);
        if all_single && !obj.terms.is_empty() {
            let coeffs: Vec<i128> = obj.terms.iter().map(|t| -t.coeff).collect();
            let total: i128 = obj.terms.iter().map(|t| t.coeff.max(0)).sum();
            let mid = total / 2;
            let (c, r) = normalize_row(&coeffs, -mid);
            println!("OBJROW file={path} {}", describe_row(&c, r));
        }
    }

    let mut counts = [0usize; 6]; // trivial, unit, seq, bdd, tot, adder
    let mut gap_rows = 0usize;
    for (coeffs, rhs) in &normalized {
        let class = route_row(coeffs, *rhs);
        counts[class as usize] += 1;
        if class == RowClass::Adder {
            let max_c = coeffs.iter().copied().max().unwrap_or(0);
            if max_c <= 10_000 && *rhs > 10_000 {
                gap_rows += 1;
                if gap_rows <= 8 {
                    println!("GAPROW file={path} {}", describe_row(coeffs, *rhs));
                }
            }
        }
    }
    println!(
        "ROWS file={path} rows={} nonlinear_cons={nonlinear} trivial={} unit={} seq={} bdd={} tot={} adder={} gap={}",
        normalized.len(),
        counts[0], counts[1], counts[2], counts[3], counts[4], counts[5],
        gap_rows,
    );
}

fn describe_row(coeffs: &[i128], rhs: i128) -> String {
    let n = coeffs.len();
    let max_c = coeffs.iter().copied().max().unwrap_or(0);
    let mut distinct = coeffs.to_vec();
    distinct.sort_unstable();
    distinct.dedup();
    let (gte_aux, gte_clause_ub, gte_work, gte_fit) =
        gte_estimate(coeffs, rhs, 50_000_000, 4_000_000);
    let (bdd_nodes, bdd_fit) = bdd_estimate(coeffs, rhs, 8_000_000);
    format!(
        "n={n} rhs={rhs} max_c={max_c} distinct_c={} gte_aux={gte_aux} gte_clause_ub={gte_clause_ub} \
         gte_work={gte_work} gte_fit={gte_fit} bdd_nodes={bdd_nodes} bdd_fit={bdd_fit}",
        distinct.len()
    )
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum RowClass {
    Trivial = 0,
    Unit = 1,
    Seq = 2,
    Bdd = 3,
    Tot = 4,
    Adder = 5,
}

/// Mirror of `auto_select` + `clamp_unary_strategy` (measurement copy).
fn route_row(coeffs: &[i128], rhs: i128) -> RowClass {
    let n = coeffs.len();
    if rhs <= 0 || coeffs.iter().sum::<i128>() < rhs {
        return RowClass::Trivial;
    }
    if n == 1 {
        return RowClass::Unit;
    }
    let max_coeff = coeffs.iter().copied().max().unwrap_or(0);
    let all_unit = coeffs.iter().all(|&c| c == 1);
    let clamp = |s: RowClass| -> RowClass {
        match s {
            RowClass::Seq | RowClass::Tot
                if (n as u128).saturating_mul(rhs as u128) > 2_000_000 =>
            {
                RowClass::Adder
            }
            other => other,
        }
    };
    if all_unit {
        if rhs <= (n as i128) / 2 && rhs <= 64 {
            return clamp(RowClass::Seq);
        }
        return RowClass::Bdd;
    }
    if max_coeff > 10_000 || rhs > 10_000 {
        return RowClass::Adder;
    }
    if n < 30 && max_coeff < 1000 {
        return RowClass::Bdd;
    }
    if n >= 30 {
        return clamp(RowClass::Tot);
    }
    RowClass::Bdd
}

/// Normalize a >=-row: positive coefficients (negate lits), saturate at rhs,
/// divide by gcd. Mirrors `normalize_ge_direction` + `simplify_normalized_ge`.
fn normalize_row(coeffs: &[i128], rhs: i128) -> (Vec<i128>, i128) {
    let mut out = Vec::with_capacity(coeffs.len());
    let mut adjusted = rhs;
    for &c in coeffs {
        if c == 0 {
            continue;
        }
        if c > 0 {
            out.push(c);
        } else {
            out.push(-c);
            adjusted -= c;
        }
    }
    if adjusted > 0 && !out.is_empty() {
        for c in out.iter_mut() {
            if *c > adjusted {
                *c = adjusted;
            }
        }
        let mut g: u128 = 0;
        for &c in &out {
            g = gcd_u128(g, c.unsigned_abs());
        }
        if g > 1 {
            let g = g as i128;
            for c in out.iter_mut() {
                *c /= g;
            }
            adjusted = if adjusted >= 0 {
                (adjusted + g - 1) / g
            } else {
                adjusted / g
            };
        }
    }
    (out, adjusted)
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// GTE dry run: simulate the adjacent-pair merge tree of `encode_totalizer`
/// (weight sets capped at rhs, saturating insert of rhs) and report
/// (total aux outputs, clause upper bound, pair work, fit-within-budgets).
fn gte_estimate(coeffs: &[i128], rhs: i128, max_work: u64, max_aux: u64) -> (u64, u64, u64, bool) {
    use std::collections::BTreeSet;
    let mut nodes: Vec<BTreeSet<i128>> = coeffs
        .iter()
        .map(|&c| {
            let mut s = BTreeSet::new();
            s.insert(c.min(rhs));
            s
        })
        .collect();
    let mut aux: u64 = 0;
    let mut clause_ub: u64 = 0;
    let mut work: u64 = 0;
    while nodes.len() > 1 {
        let mut next = Vec::with_capacity(nodes.len().div_ceil(2));
        let mut i = 0;
        while i < nodes.len() {
            if i + 1 < nodes.len() {
                let (l, r) = (&nodes[i], &nodes[i + 1]);
                let mut merged = BTreeSet::new();
                for &wl in l {
                    if wl <= rhs {
                        merged.insert(wl);
                    }
                }
                for &wr in r {
                    if wr <= rhs {
                        merged.insert(wr);
                    }
                }
                for &wl in l {
                    for &wr in r {
                        work += 1;
                        let sum = wl.saturating_add(wr);
                        merged.insert(if sum <= rhs { sum } else { rhs });
                    }
                }
                let (wl, wr, ww) = (l.len() as u64, r.len() as u64, merged.len() as u64);
                aux += ww;
                // Clause upper bound per merge (see totalizer merge structure):
                // monotonicity (|W|-1) + per-weight forward (2 + |L|) +
                // backward boundaries (|L|+1 + |R|+1).
                clause_ub += ww.saturating_mul(2 * wl + wr + 4) + ww;
                if work > max_work || aux > max_aux {
                    return (aux, clause_ub, work, false);
                }
                next.push(merged);
                i += 2;
            } else {
                next.push(std::mem::take(&mut nodes[i]));
                i += 1;
            }
        }
        nodes = next;
    }
    (aux, clause_ub, work, true)
}

/// BDD dry run: count reachable memoized `(i, slack)` states of `encode_bdd`
/// (coefficient-descending order, suffix-sum pruning). Clauses <= 2*nodes + 1.
fn bdd_estimate(coeffs: &[i128], rhs: i128, max_nodes: u64) -> (u64, bool) {
    use std::collections::BTreeSet;
    let mut sorted: Vec<i128> = coeffs.to_vec();
    sorted.sort_unstable_by(|a, b| b.cmp(a));
    let n = sorted.len();
    let mut suffix = vec![0i128; n + 1];
    for i in (0..n).rev() {
        suffix[i] = suffix[i + 1].saturating_add(sorted[i]);
    }
    // Level-by-level reachable slack values (deduped), pruned like build_bdd:
    // terminal when s <= 0 (true) or suffix[i] < s (false).
    let mut level: BTreeSet<i128> = BTreeSet::new();
    if rhs > 0 && suffix[0] >= rhs {
        level.insert(rhs);
    }
    let mut nodes: u64 = 0;
    for i in 0..n {
        if level.is_empty() {
            break;
        }
        nodes += level.len() as u64;
        if nodes > max_nodes {
            return (nodes, false);
        }
        let mut next: BTreeSet<i128> = BTreeSet::new();
        for &s in &level {
            for s2 in [s - sorted[i], s] {
                if s2 > 0 && i + 1 < n && suffix[i + 1] >= s2 {
                    next.insert(s2);
                }
            }
        }
        level = next;
    }
    (nodes, true)
}

fn profile(args: &[String]) {
    let path = args.first().expect("profile: missing <file.opb>");
    let text = std::fs::read_to_string(path).expect("failed to read instance");
    let parse_start = Instant::now();
    let instance = match parse_opb(&text) {
        Ok(instance) => instance,
        Err(err) => {
            println!("PROFILE file={path} error=parse:{err:?}");
            return;
        }
    };
    let parse_ms = parse_start.elapsed().as_millis();

    // Objective shape (routing of upper-bound rows depends on it).
    let (obj_terms, obj_max_w, obj_total_w) = instance
        .objective
        .as_ref()
        .map(|obj| {
            let max_w = obj.terms.iter().map(|t| t.coeff.abs()).max().unwrap_or(0);
            let total_w: i128 = obj.terms.iter().map(|t| t.coeff.abs()).sum();
            (obj.terms.len(), max_w, total_w)
        })
        .unwrap_or((0, 0, 0));

    // Constraint coefficient shape.
    let mut max_coeff: i128 = 0;
    let mut max_rhs: i128 = 0;
    for c in &instance.constraints {
        for t in &c.terms {
            max_coeff = max_coeff.max(t.coeff.abs());
        }
        max_rhs = max_rhs.max(c.rhs.abs());
    }

    let enc_start = Instant::now();
    let (encoded, profile) = CnfEncoder::encode_instance_with_profile(&instance);
    let enc_ms = enc_start.elapsed().as_millis();

    println!(
        "PROFILE file={path} vars={} cons={} enc_vars={} enc_aux={} enc_clauses={} \
         seq={} bdd={} tot={} adder={} trivial_sat={} trivial_unsat={} unit={} \
         obj_terms={obj_terms} obj_max_w={obj_max_w} obj_total_w={obj_total_w} \
         max_coeff={max_coeff} max_rhs={max_rhs} parse_ms={parse_ms} enc_ms={enc_ms}",
        instance.num_vars,
        instance.constraints.len(),
        encoded.num_vars,
        profile.aux_vars,
        profile.clauses,
        profile.strategies.sequential_counter,
        profile.strategies.bdd,
        profile.strategies.totalizer,
        profile.strategies.adder,
        profile.trivial_satisfied,
        profile.trivial_unsatisfied,
        profile.unit_forced,
    );
}

fn solve(args: &[String]) {
    let path = args.first().expect("solve: missing <file.opb>");
    let strategy = args.get(1).map(String::as_str).unwrap_or("auto");
    let timeout_ms: u64 = args
        .get(2)
        .map(|s| s.parse().expect("timeout_ms must be an integer"))
        .unwrap_or(60_000);

    let text = std::fs::read_to_string(path).expect("failed to read instance");
    let instance = parse_opb(&text).expect("failed to parse OPB");
    let objective = instance
        .objective
        .clone()
        .expect("solve mode requires an objective (OPT instance)");

    let start = Instant::now();
    let deadline = start + Duration::from_millis(timeout_ms);

    // Encode (interruptible, like the portfolio arm).
    let enc_start = Instant::now();
    let mut encoding_should_stop = || Instant::now() >= deadline;
    let Some(encoded) =
        CnfEncoder::encode_instance_interruptible(&instance, &mut encoding_should_stop)
    else {
        println!(
            "SOLVE file={path} strat={strategy} verdict=ENCODE_TIMEOUT wall_s={:.3}",
            start.elapsed().as_secs_f64()
        );
        return;
    };
    let enc_s = enc_start.elapsed().as_secs_f64();

    if !encoded.fits_sat_arena() {
        println!(
            "SOLVE file={path} strat={strategy} verdict=ARENA_DECLINE wall_s={:.3}",
            start.elapsed().as_secs_f64()
        );
        return;
    }

    // Import into ay-sat.
    let import_start = Instant::now();
    let mut import_should_stop = || Instant::now() >= deadline;
    let Some(mut base_solver) = encoded.to_sat_solver_interruptible(4096, &mut import_should_stop)
    else {
        println!(
            "SOLVE file={path} strat={strategy} verdict=IMPORT_TIMEOUT wall_s={:.3}",
            start.elapsed().as_secs_f64()
        );
        return;
    };
    let import_s = import_start.elapsed().as_secs_f64();

    // Inprocessing interrupt watchdog (mirrors the production arm).
    let interrupt = Arc::new(AtomicBool::new(false));
    base_solver.set_interrupt(Arc::clone(&interrupt));

    let num_pb_vars = instance.num_vars;
    let enc_vars = encoded.num_vars;
    let enc_clauses = encoded.clauses.len();
    let should_stop = move || Instant::now() >= deadline;

    let mut engine =
        OptimizationEngine::new(base_solver, objective, encoded, num_pb_vars, should_stop);
    engine.set_original_constraints(instance.constraints.clone());
    match strategy {
        "auto" => {}
        "linear" => engine.set_forced_strategy(OptStrategy::Linear),
        "binary" => engine.set_forced_strategy(OptStrategy::BinarySearch),
        "oll" => engine.set_forced_strategy(OptStrategy::CoreGuided),
        other => panic!("unknown strategy {other}"),
    }

    let solve_start = Instant::now();
    let watchdog_done = Arc::new(AtomicBool::new(false));
    let result = std::thread::scope(|scope| {
        let wd_done = Arc::clone(&watchdog_done);
        let wd_interrupt = Arc::clone(&interrupt);
        let watchdog = scope.spawn(move || {
            while !wd_done.load(Ordering::Relaxed) {
                if Instant::now() >= deadline {
                    wd_interrupt.store(true, Ordering::Relaxed);
                    break;
                }
                std::thread::sleep(Duration::from_millis(25));
            }
        });
        let result = engine.solve();
        watchdog_done.store(true, Ordering::Relaxed);
        let _ = watchdog.join();
        result
    });
    let solve_s = solve_start.elapsed().as_secs_f64();

    let (verdict, obj) = match &result {
        OptResult::Optimal(_, value) => ("OPTIMUM", Some(*value)),
        OptResult::Satisfiable(_, value) => ("SATISFIABLE", Some(*value)),
        OptResult::Infeasible => ("UNSATISFIABLE", None),
        OptResult::Unknown => ("UNKNOWN", None),
    };
    println!(
        "SOLVE file={path} strat={strategy} verdict={verdict} obj={} enc_vars={enc_vars} \
         enc_clauses={enc_clauses} enc_s={enc_s:.3} import_s={import_s:.3} solve_s={solve_s:.3} \
         wall_s={:.3}",
        obj.map_or_else(|| "-".to_string(), |v| v.to_string()),
        start.elapsed().as_secs_f64(),
    );
}
