// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the binary root; command ordering remains source-stable.

/// Dump both sides' view of one polynomial, given its coefficients low-to-high.
/// Used to triage a divergence down to the primitive that produced it.
fn cmd_dbg(z3_path: &Path, spec: &str) -> i32 {
    let mut z = open_z3(z3_path);
    let mut coeffs = Vec::new();
    for token in spec.split(',') {
        let Some(value) = z3::parse_rational(token.trim()) else {
            emit_stderr(format_args!(
                "error: invalid rational coefficient {token:?}"
            ));
            return 64;
        };
        coeffs.push(value);
    }
    emit_stdout(format_args!("p = {}", polygen::render(&coeffs)));
    let p = ay_nra::oracle_api::OPoly::from_coeffs(coeffs.clone());
    emit_stdout(format_args!("AY degree: {:?}", p.degree()));
    match p.square_free_part() {
        None => emit_stdout(format_args!("AY square_free_part: declined")),
        Some(sf) => emit_stdout(format_args!(
            "AY square_free_part: {}",
            polygen::render(&sf.coeffs())
        )),
    }
    match p.square_free_part().and_then(|sf| sf.isolate_roots()) {
        None => emit_stdout(format_args!("AY isolate_roots: declined")),
        Some(ms) => {
            emit_stdout(format_args!("AY markers ({}):", ms.len()));
            for (i, m) in ms.iter().enumerate() {
                emit_stdout(format_args!("  #{i}: {m:?}"));
            }
        }
    }
    let show = |label: &str, cs: &[num_rational::BigRational]| match z.roots(cs) {
        None => emit_stdout(format_args!("z3 roots of {label}: declined")),
        Some(rs) => {
            emit_stdout(format_args!(
                "z3 roots of {label} ({}), in returned order:",
                rs.len()
            ));
            for (i, r) in rs.iter().enumerate() {
                let b = z.bracket(*r, 40).map_or_else(
                    || "?".to_string(),
                    |(lo, hi)| format!("{:.9} .. {:.9}", ratio_f64(&lo), ratio_f64(&hi)),
                );
                emit_stdout(format_args!("  #{i}: {b}"));
            }
            emit_stdout(format_args!("  pairwise lt matrix:"));
            for a in &rs {
                let row: Vec<&str> = rs
                    .iter()
                    .map(|b| {
                        if z.lt(*a, *b) == Some(true) {
                            "<"
                        } else if z.lt(*b, *a) == Some(true) {
                            ">"
                        } else if z.eq(*a, *b) == Some(true) {
                            "="
                        } else {
                            "?"
                        }
                    })
                    .collect();
                emit_stdout(format_args!("    {}", row.join(" ")));
            }
        }
    };
    show("p", &coeffs);
    if let Some(sf) = p.square_free_part() {
        show("sf", &sf.coeffs());
        // Now the interleaved order the checks actually use: fetch BOTH root
        // lists first, then compare. If this disagrees with the sequential
        // dump above, the fault is in the harness's lifetime handling, not in
        // either implementation.
        emit_stdout(format_args!(
            "interleaved (both lists fetched before any comparison):"
        ));
        if let (Some(rp), Some(rs)) = (z.roots(&coeffs), z.roots(&sf.coeffs())) {
            for (i, (a, b)) in rp.iter().zip(rs.iter()).enumerate() {
                let ba = z.bracket(*a, 40).map_or(f64::NAN, |(lo, _)| ratio_f64(&lo));
                let bb = z.bracket(*b, 40).map_or(f64::NAN, |(lo, _)| ratio_f64(&lo));
                emit_stdout(format_args!(
                    "  #{i}: p {ba:.9}   sf {bb:.9}   eq={:?}",
                    z.eq(*a, *b)
                ));
            }
        }
    }
    reference_status(&mut z, 0)
}

/// Decimal rendering for the debug dump only.
fn ratio_f64(r: &num_rational::BigRational) -> f64 {
    let n = r.numer().to_string().parse::<f64>().unwrap_or(f64::NAN);
    let d = r.denom().to_string().parse::<f64>().unwrap_or(f64::NAN);
    n / d
}

fn cmd_golden(z3_path: Option<&Path>, heavy: bool) -> i32 {
    let mut z = z3_path.map(open_z3);
    let results = golden::run_all(z.as_ref(), heavy);
    let mut failed = 0;
    for r in &results {
        if r.passed {
            if r.detail.is_empty() {
                emit_stdout(format_args!("  ok   {}", r.name));
            } else {
                emit_stdout(format_args!("  ok   {}   [{}]", r.name, r.detail));
            }
        } else {
            failed += 1;
            emit_stdout(format_args!("  FAIL {}   {}", r.name, r.detail));
        }
    }
    emit_stdout(format_args!(
        "\ngolden fixtures: {} run, {} passed, {failed} failed",
        results.len(),
        results.len() - failed
    ));
    let status = i32::from(failed > 0);
    z.as_mut().map_or(status, |z| reference_status(z, status))
}

fn cmd_fuzz(
    z3_path: &Path,
    seed: u64,
    cases: u64,
    start: u64,
    dump_dir: Option<PathBuf>,
    progress_every: u64,
    max_cost: usize,
) -> i32 {
    let mut z = open_z3(z3_path);
    // The check-set size is part of a case's identity, not decoration: the
    // driver picks with `ALL_CHECKS[i % len]`, so the SAME (seed, case) names a
    // DIFFERENT check under a different `len`. Five lanes believed appending
    // preserved case numbering; it never did. See `ALL_CHECKS`.
    emit_stdout(format_args!(
        "seed {seed}, cases {cases} (starting at index {start}), work budget {max_cost}, \
         checks {}",
        ALL_CHECKS.len()
    ));
    let mut report = Report::new();
    let begin = Instant::now();
    let mut last_progress = Instant::now();

    for i in start..start + cases {
        if (i - start) % RECYCLE_EVERY == RECYCLE_EVERY - 1 {
            if let Err(e) = z.recycle() {
                emit_stderr(format_args!(
                    "FATAL: could not recycle the reference libz3 context: {e}"
                ));
                return 2;
            }
        }
        let check = ALL_CHECKS[usize::try_from(i % (ALL_CHECKS.len() as u64)).unwrap_or(0)];
        let mut rng = Rng::new(case_seed(seed, i));
        let t0 = Instant::now();
        let result = checks::run_case(&z, check, &mut rng, max_cost, checks::Sabotage::Off);
        let ms = t0.elapsed().as_millis();
        if ms > report.slowest_ms {
            report.slowest_ms = ms;
            report.slowest_case = i;
        }
        report.record(check, &result.outcome, &result.shapes);
        if let Outcome::Diverged(d) = &result.outcome {
            dump_divergence(z3_path, seed, i, check, d, dump_dir.as_deref());
        }
        if progress_every > 0
            && (i - start + 1).is_multiple_of(progress_every)
            && last_progress.elapsed().as_secs_f64() > 0.0
        {
            let done = i - start + 1;
            let el = begin.elapsed().as_secs_f64();
            emit_stderr(format_args!(
                "  [{done}/{cases}] {:.0} cases/s, {} asserts, {} divergences, {:.0}s elapsed",
                done as f64 / el.max(1e-9),
                report.total.comparisons,
                report.total.diverged,
                el
            ));
            last_progress = Instant::now();
        }
    }

    let reference_failures = finalize_reference(&mut z);
    report.print(seed, begin.elapsed().as_secs_f64(), reference_failures);
    if reference_failures > 0 {
        emit_stderr(format_args!(
            "FATAL: reference libz3 failed; this run is not clean evidence"
        ));
        return 2;
    }
    if report.reference_comparisons == 0 {
        emit_stderr(format_args!("FATAL: no reference comparison completed"));
        return 2;
    }
    i32::from(report.total.diverged > 0)
}
/// The catch rate below which a check is reported DEGRADED and `selftest`
/// fails, even though the check still catches something.
///
/// The old gate was `hits > 0`. A verifier proved what that permits: hardwiring
/// `Zp::is_irreducible` to `Some(true)` dropped `up-zp-factor` from 39 of 39
/// caught to 17 of 39, and `selftest` still printed "detects sabotage" and
/// exited 0. Detection can collapse by more than half and the gate stays green,
/// which makes a clean selftest much weaker evidence than it reads as.
///
/// 0.80 is chosen against the MEASURED floor of the honest checks, not picked
/// for roundness: at `--cases 1100` the lowest legitimate rates are `gcd`
/// 28/29 = 96.6%, `pm-representation` 48/50 = 96.0% and `square-free`
/// 34/35 = 97.1%. Those misses are real — a saboteur can multiply by a factor
/// that happens to preserve the property under test — so 100% is not
/// achievable. 0.80 leaves each of them ~16 points of sampling headroom while
/// still failing the 43.6% collapse above decisively.
const MIN_CATCH_RATE: f64 = 0.80;

/// Prove the oracle can fail.
///
/// A clean run only means something if a dirty one would have been caught, so
/// this replays ordinary cases with [`checks::Sabotage::On`] — AY's answer is
/// minimally corrupted right at the comparison — and requires EVERY check to
/// report divergences. A check that stays silent under sabotage is not
/// checking anything, and the command exits non-zero.
fn cmd_selftest(z3_path: &Path, seed: u64, cases: u64, max_cost: usize) -> i32 {
    let mut z = open_z3(z3_path);
    emit_stdout(format_args!(
        "selftest: {cases} sabotaged cases at seed {seed}\n"
    ));
    let mut caught: BTreeMap<&'static str, (u64, u64)> = BTreeMap::new();
    for i in 0..cases {
        if i % RECYCLE_EVERY == RECYCLE_EVERY - 1 {
            if let Err(e) = z.recycle() {
                emit_stderr(format_args!(
                    "FATAL: could not recycle the reference libz3 context: {e}"
                ));
                return 2;
            }
        }
        let check = ALL_CHECKS[usize::try_from(i % (ALL_CHECKS.len() as u64)).unwrap_or(0)];
        let mut rng = Rng::new(case_seed(seed, i));
        let result = checks::run_case(&z, check, &mut rng, max_cost, checks::Sabotage::On);
        let e = caught.entry(check.name()).or_insert((0, 0));
        match result.outcome {
            Outcome::Diverged(_) => {
                e.0 += 1;
                e.1 += 1;
            }
            Outcome::Match(_) => e.1 += 1,
            // Declined / inapplicable cases never reached a comparison, so they
            // are not evidence either way.
            Outcome::Declined(_) | Outcome::Skipped(_) => {}
        }
    }
    emit_stdout(format_args!(
        "{:<22} {:>10} {:>10} {:>7}  {}",
        "check", "compared", "caught", "rate", "verdict"
    ));
    let mut blind = 0;
    let mut degraded = 0;
    for (name, (hits, compared)) in &caught {
        #[allow(clippy::cast_precision_loss)]
        let rate = if *compared == 0 {
            0.0
        } else {
            *hits as f64 / *compared as f64
        };
        let verdict = if *hits == 0 {
            blind += 1;
            "BLIND"
        } else if rate < MIN_CATCH_RATE {
            degraded += 1;
            "DEGRADED"
        } else {
            "detects sabotage"
        };
        emit_stdout(format_args!(
            "{name:<22} {compared:>10} {hits:>10} {:>6.1}%  {verdict}",
            rate * 100.0
        ));
    }
    for c in ALL_CHECKS {
        if !caught.contains_key(c.name()) {
            blind += 1;
            emit_stdout(format_args!(
                "{:<22} {:>10} {:>10} {:>7}  NEVER RAN",
                c.name(),
                0,
                0,
                "-"
            ));
        }
    }
    let status = if blind == 0 && degraded == 0 {
        emit_stdout(format_args!(
            "\nselftest: every check detects a corrupted AY answer."
        ));
        0
    } else {
        if blind > 0 {
            emit_stdout(format_args!(
                "\nselftest: {blind} check(s) cannot fail — a clean run proves nothing for them."
            ));
        }
        if degraded > 0 {
            emit_stdout(format_args!(
                "selftest: {degraded} check(s) caught sabotage at under {:.0}% — detection has \
                 COLLAPSED even though they still catch something.",
                MIN_CATCH_RATE * 100.0
            ));
        }
        1
    };
    reference_status(&mut z, status)
}

fn cmd_repro(z3_path: &Path, seed: u64, index: u64, max_cost: usize) -> i32 {
    let mut z = open_z3(z3_path);
    let check = ALL_CHECKS[usize::try_from(index % (ALL_CHECKS.len() as u64)).unwrap_or(0)];
    let mut rng = Rng::new(case_seed(seed, index));
    // `checks N` is required to replay this: `index % N` is what selected the
    // check, so a case number without it is ambiguous across commits.
    emit_stdout(format_args!(
        "case #{index} of seed {seed} (checks {}): check `{}`",
        ALL_CHECKS.len(),
        check.name()
    ));
    let result = checks::run_case(&z, check, &mut rng, max_cost, checks::Sabotage::Off);
    emit_stdout(format_args!("shapes: {}", result.shapes.join(", ")));
    let status = match &result.outcome {
        Outcome::Match(n) => {
            emit_stdout(format_args!("MATCH ({n} assertions held)"));
            0
        }
        Outcome::Declined(r) => {
            emit_stdout(format_args!(
                "AY DECLINED at `{r}` (fail-closed; not a divergence)"
            ));
            0
        }
        Outcome::Skipped(r) => {
            emit_stdout(format_args!("inapplicable: {r}"));
            0
        }
        Outcome::Diverged(d) => {
            dump_divergence(z3_path, seed, index, check, d, None);
            1
        }
    };
    reference_status(&mut z, status)
}
