// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the binary root; command ordering remains source-stable.

#[derive(Default)]
struct DeclineCensus {
    by_reason: BTreeMap<&'static str, u64>,
    by_shape: BTreeMap<&'static str, (u64, u64)>,
    by_shape_reason: BTreeMap<(&'static str, &'static str), u64>,
    totals: [u64; 14],
    points_over_bound: BTreeMap<i64, u64>,
    cases: u64,
    declined: u64,
}

impl DeclineCensus {
    fn record(&mut self, row: pmgr::DeclineRow) {
        self.cases += 1;
        let shape = self.by_shape.entry(row.label).or_default();
        shape.0 += 1;
        if row.certified {
            return;
        }
        self.declined += 1;
        shape.1 += 1;
        *self.by_reason.entry(row.reason).or_default() += 1;
        *self
            .by_shape_reason
            .entry((row.label, row.reason))
            .or_default() += 1;
        let events = [
            row.prime_bad_coeff,
            row.prime_bad_lcg,
            row.prime_rec_declined,
            row.lc_gate_rejected,
            row.cert_reject_u,
            row.cert_reject_v,
            row.rec_inner_declined,
            row.rec_budget_exhausted,
            row.rec_lch_mismatch,
            row.rec_trialdiv_reject,
            row.rec_unlucky_degree,
            row.rec_base_failed + row.rec_content_failed,
            row.rec_reset_smaller,
            row.rec_points_tried,
        ];
        for (total, event) in self.totals.iter_mut().zip(events) {
            *total += u64::from(event);
        }
        let over = i64::from(row.rec_max_points_at_level) - (i64::from(row.rec_max_deg_bound) + 1);
        *self.points_over_bound.entry(over.clamp(-4, 8)).or_default() += 1;
    }

    #[allow(clippy::cast_precision_loss)]
    fn percent(&self, count: u64) -> f64 {
        100.0 * count as f64 / self.cases.max(1) as f64
    }
}

fn collect_declines(seed: u64, cases: u64) -> DeclineCensus {
    let mut rng = Rng::new(case_seed(seed, 0));
    let mut census = DeclineCensus::default();
    for _ in 0..cases {
        if let Some(row) = pmgr::diagnose_random(&mut rng) {
            census.record(row);
        }
    }
    census
}

fn print_decline_rates(census: &DeclineCensus) {
    println!("cases   {}", census.cases);
    println!(
        "declines {}  ({:.2}%)",
        census.declined,
        census.percent(census.declined)
    );
    println!(
        "\n{:<52} {:>8} {:>8}",
        "primary cause of decline", "count", "% of all"
    );
    let mut reasons: Vec<_> = census.by_reason.iter().collect();
    reasons.sort_by_key(|(_, count)| std::cmp::Reverse(**count));
    for (reason, count) in reasons {
        println!("{reason:<52} {count:>8} {:>7.2}%", census.percent(*count));
    }
    println!(
        "\n{:<16} {:>8} {:>10} {:>8}",
        "generated shape", "cases", "declines", "rate"
    );
    for (shape, (cases, declines)) in &census.by_shape {
        #[allow(clippy::cast_precision_loss)]
        let rate = 100.0 * *declines as f64 / (*cases).max(1) as f64;
        println!("{shape:<16} {cases:>8} {declines:>10} {rate:>7.2}%");
    }
    println!("\n-- shape x cause --");
    for ((shape, reason), count) in &census.by_shape_reason {
        println!("{shape:<16} {count:>6}  {reason}");
    }
}

fn print_decline_events(census: &DeclineCensus) {
    println!("\n-- raw event totals over declining cases (a case can log several) --");
    let labels = [
        "prime rejected: coefficient vanished",
        "prime rejected: lc_g vanished",
        "prime rejected: recursion declined",
        "lc gate rejected the CRA candidate",
        "EXACT certificate rejected on u",
        "EXACT certificate rejected on v",
        "recursion: inner call at a point declined",
        "recursion: budget exhausted",
        "recursion: lc_H != lc_g (needs more points)",
        "recursion: trial division rejected",
        "recursion: unlucky point (degree too high)",
        "recursion: base/content refused",
        "recursion: Newton form reset (smaller image deg)",
        "recursion: evaluation points consumed",
    ];
    for (label, count) in labels.into_iter().zip(census.totals) {
        println!("{label:<48} {count:>10}");
    }
    println!(
        "\n-- how far the interpolation ran past `deg_bound + 1` before giving up --\n\
         (a value > 0 means MORE points than the degree bound can require were supplied \
         and the trial division STILL rejected: more budget is not the fix)"
    );
    for (over, count) in &census.points_over_bound {
        println!("{over:>+4} points   {count:>8}");
    }
}

/// Report why the modular GCD fail-closed path declined, by fixture and sample.
fn cmd_declines(seed: u64, cases: u64) -> i32 {
    println!("mod_gcd DECLINE CENSUS");
    println!("a decline is a fail-closed `None`; `PolyManager::gcd` falls back to the PRS\n");
    print_decline_shapes();
    println!("\n-- {cases} random cases, seed {seed} (the `pm-mod-gcd` generator) --");
    let census = collect_declines(seed, cases);
    print_decline_rates(&census);
    print_decline_events(&census);
    0
}
