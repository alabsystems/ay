// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the binary root; command ordering remains source-stable.

fn dump_divergence(
    z3_path: &Path,
    seed: u64,
    index: u64,
    check: Check,
    d: &checks::Divergence,
    out_dir: Option<&Path>,
) {
    let inputs: serde_json::Map<String, serde_json::Value> = d
        .inputs
        .iter()
        .map(|(k, v)| (k.clone(), serde_json::Value::String(v.clone())))
        .collect();
    let blob = serde_json::json!({
        "seed": seed,
        "case": index,
        "check": check.name(),
        "reference": d.reference,
        "detail": d.detail,
        "inputs": inputs,
        // The check-set size is part of the reproducer. `index % checks` is
        // what selects the check, so this command replays THIS case only
        // against a binary with the same number of checks.
        "reproduce": format!(
            "ay-nra-oracle repro --z3 {:?} --seed {seed} --case {index}   # checks={}",
            z3_path.display().to_string(),
            ALL_CHECKS.len()
        ),
    });
    let text =
        serde_json::to_string_pretty(&blob).unwrap_or_else(|e| format!("{{\"error\":\"{e}\"}}"));
    emit_stderr(format_args!(
        "\n!!! DIVERGENCE ({} vs {}) !!!\n{text}",
        d.check, d.reference
    ));
    if let Some(dir) = out_dir {
        let _ = std::fs::create_dir_all(dir);
        let path = dir.join(format!("divergence-{seed}-{index}.json"));
        if let Err(e) = std::fs::write(&path, &text) {
            emit_stderr(format_args!(
                "(could not write reproducer to {}: {e})",
                path.display()
            ));
        } else {
            emit_stderr(format_args!("(reproducer written to {})", path.display()));
        }
    }
}

#[expect(
    unsafe_code,
    reason = "an operator-selected native reference requires an explicit trusted-ABI assertion"
)]
fn open_z3(path: &Path) -> Z3 {
    // SAFETY: this developer oracle deliberately executes the operator-selected
    // reference library as trusted native code. Its CLI contract requires
    // `path` to name a genuine, ABI-compatible libz3 for this target.
    match unsafe { Z3::open_trusted_reference(path) } {
        Ok(z) => {
            emit_stdout(format_args!(
                "reference libz3: {} ({})",
                path.display(),
                z.version
            ));
            z
        }
        Err(e) => {
            emit_stderr(format_args!(
                "FATAL: could not load the reference libz3: {e}"
            ));
            emit_stderr(format_args!(
                "The oracle refuses to report a clean run without a reference."
            ));
            std::process::exit(2);
        }
    }
}

fn finalize_reference(z: &mut Z3) -> u64 {
    let before = z.reference_failure_count();
    let finalize_failed = match z.recycle() {
        Ok(()) => false,
        Err(e) => {
            emit_stderr(format_args!(
                "FATAL: could not finalize the reference libz3 context: {e}"
            ));
            true
        }
    };
    let failures = z.reference_failure_count();
    failures.saturating_add(u64::from(finalize_failed && failures == before))
}

fn reference_status(z: &mut Z3, status: i32) -> i32 {
    let failures = finalize_reference(z);
    if failures == 0 {
        status
    } else {
        emit_stderr(format_args!(
            "FATAL: reference libz3 failed {failures} time(s); result is not clean evidence"
        ));
        2
    }
}

/// Sanity-check the z3 binding itself before trusting any verdict it produces.
/// If this fails, every "0 divergences" result downstream is worthless.
fn probe_algebraic_api(z: &Z3) -> u32 {
    let mut failures = 0;
    let roots = match z.roots(&checks::ipoly(&[-2, 0, 1])) {
        Some(roots) if roots.len() == 2 => roots,
        other => {
            emit_stdout(format_args!(
                "probe roots(x^2-2): FAILED ({:?} roots)",
                other.map(|roots| roots.len())
            ));
            return 1;
        }
    };
    let alpha = roots[1];
    match z.bracket(alpha, 40) {
        Some((lo, hi)) => {
            emit_stdout(format_args!(
                "probe roots(x^2-2): 2 roots, upper root in ({lo}, {hi})"
            ));
            let want_lo = checks::rat(1_414_213, 1_000_000);
            let want_hi = checks::rat(1_414_214, 1_000_000);
            if lo < want_lo || hi > want_hi {
                emit_stdout(format_args!(
                    "probe bracket(x^2-2): FAILED to certify the 1e-6 enclosure"
                ));
                failures += 1;
            }
        }
        None => {
            emit_stdout(format_args!("probe bracket(x^2-2): FAILED"));
            failures += 1;
        }
    }

    let s0 = z.eval_sign(&checks::ipoly(&[-2, 0, 1]), alpha);
    let s1 = z.eval_sign(&checks::ipoly(&[-3, 0, 1]), alpha);
    let s2 = z.eval_sign(&checks::ipoly(&[-1, 1]), alpha);
    emit_stdout(format_args!(
        "probe eval_sign at sqrt(2): x^2-2 -> {s0:?}, x^2-3 -> {s1:?}, x-1 -> {s2:?}"
    ));
    if s0 != Some(0) || s1 != Some(-1) || s2 != Some(1) {
        failures += 1;
    }

    match z.rational(&checks::rat(2, 1)) {
        Some(two) => {
            let ok = z
                .mul(alpha, alpha)
                .is_some_and(|sq| z.eq(sq, two) == Some(true));
            emit_stdout(format_args!("probe sqrt(2)*sqrt(2) == 2: {ok}"));
            failures += u32::from(!ok);
            let rational_index_ok = z.root_index(two).is_none() && !z.errored();
            emit_stdout(format_args!(
                "probe rational root index rejected: {rational_index_ok}"
            ));
            failures += u32::from(!rational_index_ok);
        }
        None => {
            emit_stdout(format_args!("probe rational(2): FAILED"));
            failures += 2;
        }
    }

    let defining = z
        .defining_poly(alpha)
        .map(|poly| poly.iter().map(ToString::to_string).collect::<Vec<_>>());
    let root_index = z.root_index(alpha);
    emit_stdout(format_args!(
        "probe defining poly of sqrt(2): {defining:?}, root index {root_index:?}"
    ));
    failures += u32::from(defining.is_none());
    failures += u32::from(root_index.is_none());
    failures
}

fn probe_handle_guards(z3_path: &Path, z: &mut Z3) -> (u32, u64) {
    let baseline = z.reference_failure_count();
    let Some(value) = z.rational(&checks::rat(2, 1)) else {
        emit_stdout(format_args!(
            "probe typed handles: FAILED to build source value"
        ));
        return (1, 0);
    };
    let Some(poly) = z.poly_bound(&checks::ipoly(&[1, 1])) else {
        emit_stdout(format_args!(
            "probe typed handles: FAILED to build wrong-kind operand"
        ));
        return (1, 0);
    };
    let wrong_kind_rejected = z.eq(value, poly).is_none();

    let other = open_z3(z3_path);
    let other_baseline = other.reference_failure_count();
    let Some(other_value) = other.rational(&checks::rat(2, 1)) else {
        emit_stdout(format_args!(
            "probe typed handles: FAILED to build foreign-context control"
        ));
        return (
            1,
            other
                .reference_failure_count()
                .saturating_sub(other_baseline),
        );
    };
    let foreign_rejected = other.eq(value, other_value).is_none();
    let foreign_clean = other.reference_failure_count() == other_baseline;

    if let Err(e) = z.recycle() {
        emit_stdout(format_args!(
            "probe typed handles: FAILED to recycle context: {e}"
        ));
        return (1, 0);
    }
    let Some(current_value) = z.rational(&checks::rat(2, 1)) else {
        emit_stdout(format_args!(
            "probe typed handles: FAILED to build post-recycle control"
        ));
        return (1, 0);
    };
    let stale_rejected = z.eq(value, current_value).is_none();
    let local_clean = z.reference_failure_count() == baseline;
    let ok =
        wrong_kind_rejected && foreign_rejected && stale_rejected && foreign_clean && local_clean;
    emit_stdout(format_args!(
        "probe typed handles: wrong-kind={wrong_kind_rejected}, foreign={foreign_rejected}, \
         stale={stale_rejected}, expected guards clean={}",
        foreign_clean && local_clean
    ));
    (
        u32::from(!ok),
        other
            .reference_failure_count()
            .saturating_sub(other_baseline),
    )
}

fn subresultant_probe_cases() -> Vec<(
    &'static str,
    Vec<num_rational::BigRational>,
    Vec<num_rational::BigRational>,
)> {
    // The subresultant mapping: p = x+1, q = x+2 must give a single psc
    // (z3's own `src/test/api_polynomial.cpp` asserts exactly this).
    vec![
        ("x+1 vs x+2", checks::ipoly(&[1, 1]), checks::ipoly(&[2, 1])),
        (
            "x^2-2 vs x^2-3",
            checks::ipoly(&[-2, 0, 1]),
            checks::ipoly(&[-3, 0, 1]),
        ),
        (
            "x^2-2 vs x^2-11",
            checks::ipoly(&[-2, 0, 1]),
            checks::ipoly(&[-11, 0, 1]),
        ),
        (
            "x^2-1 vs x-1",
            checks::ipoly(&[-1, 0, 1]),
            checks::ipoly(&[-1, 1]),
        ),
        (
            "x^2+3x+2 vs 2x+3",
            checks::ipoly(&[2, 3, 1]),
            checks::ipoly(&[3, 2]),
        ),
        (
            "x^3-2 vs x^2-2",
            checks::ipoly(&[-2, 0, 0, 1]),
            checks::ipoly(&[-2, 0, 1]),
        ),
        (
            "x^3-2 vs 3x^2",
            checks::ipoly(&[-2, 0, 0, 1]),
            checks::ipoly(&[0, 0, 3]),
        ),
        // Reversed argument order: z3 sorts by degree internally, so this
        // pins whether the sign convention survives the swap.
        (
            "x^2-2 vs x^3-2 (swapped)",
            checks::ipoly(&[-2, 0, 1]),
            checks::ipoly(&[-2, 0, 0, 1]),
        ),
        (
            "x-1 vs x^3-2 (swapped)",
            checks::ipoly(&[-1, 1]),
            checks::ipoly(&[-2, 0, 0, 1]),
        ),
        (
            "x^3-2 vs x-1",
            checks::ipoly(&[-2, 0, 0, 1]),
            checks::ipoly(&[-1, 1]),
        ),
        // Non-unit content: does z3's polynomial manager rescale?
        (
            "2x^2-4 vs x-1",
            checks::ipoly(&[-4, 0, 2]),
            checks::ipoly(&[-1, 1]),
        ),
        (
            "6x^2-12 vs 3x-3",
            checks::ipoly(&[-12, 0, 6]),
            checks::ipoly(&[-3, 3]),
        ),
        // Shared factor of degree 1: psc_0 = 0 and z3 skips it.
        (
            "(x-1)(x-2)(x-3) vs (x-1)(x-5)",
            checks::ipoly(&[-6, 11, -6, 1]),
            checks::ipoly(&[5, -6, 1]),
        ),
        // Shared factor of degree 2.
        (
            "(x-1)^2(x-3) vs (x-1)^2(x-5)",
            checks::ipoly(&[-3, 7, -5, 1]),
            checks::ipoly(&[-5, 11, -7, 1]),
        ),
    ]
}

fn probe_subresultants(z: &Z3) -> u32 {
    let mut failures = 0;
    for (name, p, q) in subresultant_probe_cases() {
        let ay = ay_nra::oracle_api::resultant(
            &ay_nra::oracle_api::OPoly::from_coeffs(p.clone()),
            &ay_nra::oracle_api::OPoly::from_coeffs(q.clone()),
        );
        match z.subresultants(&p, &q) {
            None => {
                emit_stdout(format_args!("probe psc {name}: z3 declined"));
                failures += 1;
            }
            Some(chain) => {
                let rendered: Vec<String> = chain
                    .iter()
                    .map(|a| {
                        z.numeral_value(*a).map_or_else(
                            || {
                                z.ast_string(*a)
                                    .unwrap_or_else(|| "<invalid-z3-ast>".into())
                            },
                            |v| v.to_string(),
                        )
                    })
                    .collect();
                emit_stdout(format_args!(
                    "probe psc {name}: z3 = [{}]   AY resultant = {}",
                    rendered.join(", "),
                    ay.map_or_else(|| "None".to_string(), |v| v.to_string())
                ));
            }
        }
    }
    failures
}

fn cmd_probe(z3_path: &Path) -> i32 {
    let mut z = open_z3(z3_path);
    let mut failures = probe_algebraic_api(&z);
    let (guard_failures, foreign_reference_failures) = probe_handle_guards(z3_path, &mut z);
    failures += guard_failures;
    failures += probe_subresultants(&z);
    let reference_failures = z
        .reference_failure_count()
        .saturating_add(foreign_reference_failures);
    let status = if reference_failures > 0 {
        emit_stdout(format_args!(
            "probe reference API failures recorded: {reference_failures}"
        ));
        2
    } else if failures == 0 {
        emit_stdout(format_args!("\nprobe: z3 binding behaves as documented."));
        0
    } else {
        emit_stdout(format_args!(
            "\nprobe: {failures} FAILURES — do not trust downstream results."
        ));
        1
    };
    reference_status(&mut z, status)
}
