// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ===========================================================================
// A/B BEHAVIOURAL EQUIVALENCE DUMP + ladder-exercise proof
// ===========================================================================

#[cfg(test)]
struct Rng(u64);
#[cfg(test)]
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
}

/// Every case this run touches, as `tag | verdict | sep_bits | bound | steps`.
/// Verdict/sep_bits/bound must be IDENTICAL between the two builds; `steps` is
/// the quantity the change is allowed to move.
#[cfg(test)]
fn emit_dump_comparison(out: &mut String, tag: String, a: &Num, b: &Num) -> (bool, u64) {
    use std::fmt::Write as _;

    let (Some(aa), Some(bb)) = (a.to_ay(), b.to_ay()) else {
        let _ = writeln!(out, "{tag} | NOCELL");
        return (false, 0);
    };
    match aa.cmp_anum_traced(&bb) {
        None => {
            let _ = writeln!(out, "{tag} | DECLINED");
            (false, 0)
        }
        Some((ordering, trace)) => {
            let _ = writeln!(
                out,
                "{tag} | {ordering:?} | sep={:?} | bound={} | cert={} | steps={}/{}",
                trace.sep_bits,
                trace.bound,
                trace.equal_by_certificate,
                trace.steps_a,
                trace.steps_b
            );
            (
                trace.steps_a > 0 || trace.steps_b > 0,
                u64::from(trace.steps_a) + u64::from(trace.steps_b),
            )
        }
    }
}

#[cfg(test)]
#[derive(Default)]
struct DumpStats {
    cases: usize,
    with_bisection: usize,
    total_steps: u64,
    wrong: Vec<String>,
}

#[cfg(test)]
fn collect_dump_numbers(rng: &mut Rng) -> Vec<(String, Num)> {
    let mut built = Vec::new();
    let mut tries = 0;
    while built.len() < 90 && tries < 4000 {
        tries += 1;
        let degree = 1 + usize::try_from(rng.below(4)).unwrap();
        let mut coefficients: Vec<BigInt> = (0..=degree)
            .map(|_| BigInt::from(rng.range(-12, 12)))
            .collect();
        if coefficients[degree].is_zero() {
            coefficients[degree] = BigInt::one();
        }
        if coefficients.iter().all(Zero::is_zero) {
            continue;
        }
        let polynomial = QP::from_ints(&coefficients);
        if polynomial.deg().is_none_or(|value| value < 1) {
            continue;
        }
        let Ok(intervals) = std::panic::catch_unwind(|| isolate(&polynomial)) else {
            continue;
        };
        for (index, (lo, hi, exponent)) in intervals.iter().enumerate() {
            let number = Num {
                p: coefficients.clone(),
                lo: (lo.clone(), *exponent),
                hi: (hi.clone(), *exponent),
            };
            if number.to_ay().is_some() {
                built.push((
                    format!("rand{}[{index}]{coefficients:?}", built.len()),
                    number,
                ));
            }
        }
    }
    built
}

#[cfg(test)]
fn record_random_dump(out: &mut String, built: &[(String, Num)], stats: &mut DumpStats) {
    for (tag_a, a) in built {
        for (tag_b, b) in built {
            stats.cases += 1;
            let (bisected, steps) =
                emit_dump_comparison(out, format!("R {tag_a} vs {tag_b}"), a, b);
            if bisected {
                stats.with_bisection += 1;
            }
            stats.total_steps += steps;
            if let (Some(aa), Some(bb)) = (a.to_ay(), b.to_ay()) {
                if let Some(ordering) = aa.cmp_anum(&bb) {
                    let model = model_cmp(a, b);
                    if ordering != model {
                        stats.wrong.push(format!(
                            "{tag_a} vs {tag_b}: AY {ordering:?} vs MODEL {model:?}"
                        ));
                    }
                }
            }
        }
    }
}

#[cfg(test)]
fn record_close_dump(out: &mut String, stats: &mut DumpStats) {
    for bits in 0..=60u32 {
        for sign in [1i64, -1] {
            let (Some(a), Some(b)) = (num_of(p_sqrt2(), 1), num_of(p_sqrt2_eps(bits, sign), 1))
            else {
                continue;
            };
            stats.cases += 1;
            let (bisected, steps) = emit_dump_comparison(
                out,
                format!("C sqrt2 vs eps(2^-{},{sign})", 2 * bits),
                &a,
                &b,
            );
            if bisected {
                stats.with_bisection += 1;
            }
            stats.total_steps += steps;
            if let (Some(aa), Some(bb)) = (a.to_ay(), b.to_ay()) {
                if let Some(ordering) = aa.cmp_anum(&bb) {
                    let model = model_cmp(&a, &b);
                    if ordering != model {
                        stats.wrong.push(format!(
                            "close nb={bits} s={sign}: AY {ordering:?} vs MODEL {model:?}"
                        ));
                    }
                }
            }
        }
    }
}

#[cfg(test)]
fn record_sign_dump(out: &mut String, stats: &mut DumpStats) {
    use std::fmt::Write as _;

    let sample = num_of(p_sqrt2(), 1).unwrap();
    let sample = sample.to_ay().unwrap();
    for bits in 0..=60u32 {
        for sign in [1i64, -1, 7] {
            let polynomial = p_sqrt2_eps(bits, sign);
            stats.cases += 1;
            match sample.sign_of_poly_traced(&polynomial) {
                None => {
                    let _ = writeln!(out, "S nb={bits} s={sign} | DECLINED");
                }
                Some((value, trace)) => {
                    let _ = writeln!(
                        out,
                        "S nb={bits} s={sign} | {value} | sep={:?} | bound={} | steps={}",
                        trace.sep_bits, trace.bound, trace.steps_a
                    );
                    if trace.steps_a > 0 {
                        stats.with_bisection += 1;
                    }
                    stats.total_steps += u64::from(trace.steps_a);
                    let model = if sign > 0 { -1 } else { 1 };
                    if value != model {
                        stats.wrong.push(format!(
                            "sign nb={bits} s={sign}: AY {value} vs MODEL {model}"
                        ));
                    }
                }
            }
        }
    }
}

#[test]
fn av_dump_verdicts() {
    let mut output = String::new();
    let mut stats = DumpStats::default();
    let mut rng = Rng(0x5eed_1234_abcd_0001);
    let built = collect_dump_numbers(&mut rng);
    record_random_dump(&mut output, &built, &mut stats);
    record_close_dump(&mut output, &mut stats);
    record_sign_dump(&mut output, &mut stats);

    let path = std::env::var("AV_DUMP").unwrap_or_else(|_| "/tmp/av_dump.txt".to_string());
    std::fs::write(&path, &output).expect("write dump");
    println!(
        "[dump] cases={} lines={} with_bisection={} total_steps={} wrong={} -> {path}",
        stats.cases,
        output.lines().count(),
        stats.with_bisection,
        stats.total_steps,
        stats.wrong.len()
    );
    for wrong in stats.wrong.iter().take(40) {
        println!("  WRONG: {wrong}");
    }
    assert!(
        stats.cases >= 3000,
        "anti-vacuity: only {} cases",
        stats.cases
    );
    assert!(
        stats.with_bisection >= 100,
        "LADDER NOT EXERCISED: only {} cases performed any bisection",
        stats.with_bisection
    );
    assert!(stats.wrong.is_empty());
}
