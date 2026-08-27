// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the binary root; the harness remains a single private namespace.

struct Options {
    seed: u64,
    cases: usize,
    output: String,
}

fn parse_options() -> Options {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args
        .iter()
        .position(|a| a == "--seed")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);
    let cases = args
        .iter()
        .position(|a| a == "--cases")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(200);
    let output = args
        .iter()
        .position(|a| a == "--out")
        .and_then(|i| args.get(i + 1))
        .cloned()
        .unwrap_or_else(|| "/tmp/vexplain".to_string());
    Options {
        seed,
        cases,
        output,
    }
}

fn build_lits(case: &Case) -> Option<Vec<OExplainLit>> {
    let mut lits = Vec::with_capacity(case.polys.len());
    for (i, (poly, condition)) in case.polys.iter().zip(&case.conds).enumerate() {
        if poly.iter().rposition(|x| !x.is_zero()).unwrap_or(0) < 1 {
            return None;
        }
        let isolated = isolate(poly)?;
        let roots = isolated
            .iter()
            .map(|root| to_anum(poly, root))
            .collect::<Option<Vec<_>>>()?;
        lits.push(OExplainLit {
            lit: i32::try_from(i + 1).ok()?,
            p: poly.clone(),
            cond: *condition,
            roots,
        });
    }
    (lits.len() == case.polys.len()).then_some(lits)
}

struct RunSummary<'a> {
    seed: u64,
    cases: usize,
    isolate_declined: usize,
    produced: usize,
    skipped: usize,
    ay_valid_true: usize,
    ay_valid_false: usize,
    ay_valid_none: usize,
    countermodels: usize,
    falsified_fail: usize,
    shapes: &'a std::collections::BTreeMap<&'a str, usize>,
}

fn persist(output: &str, smt: &str, manifest: &[String]) {
    std::fs::write(format!("{output}.smt2"), smt).unwrap();
    std::fs::write(format!("{output}.manifest"), manifest.join("\n")).unwrap();
}

fn print_summary(summary: &RunSummary<'_>) {
    let mut err = std::io::stderr();
    let usable = summary.cases - summary.isolate_declined;
    writeln!(
        err,
        "seed={} cases={} usable={usable} produced={} noclause={} isolate_declined={}",
        summary.seed, summary.cases, summary.produced, summary.skipped, summary.isolate_declined
    )
    .unwrap();
    writeln!(
        err,
        "clause_is_valid: true={} false={} DECLINE={}  countermodels={}  falsified_fail={}",
        summary.ay_valid_true,
        summary.ay_valid_false,
        summary.ay_valid_none,
        summary.countermodels,
        summary.falsified_fail
    )
    .unwrap();
    writeln!(err, "shapes: {:?}", summary.shapes).unwrap();
}

fn append_full_query(
    smt: &mut String,
    manifest: &mut Vec<String>,
    case_id: usize,
    case: &Case,
    lits: &[OExplainLit],
    produced: bool,
) {
    let full = case
        .polys
        .iter()
        .zip(&case.conds)
        .map(|(poly, condition)| smt_atom(poly, *condition));
    smt.push_str("(push 1)\n");
    for atom in full {
        smt.push_str(&format!("(assert {atom})\n"));
    }
    smt.push_str("(check-sat)\n(pop 1)\n");
    let verdict = match oexplain_clause_is_valid(lits) {
        Some(true) => "valid",
        Some(false) => "invalid",
        None => "decline",
    };
    manifest.push(format!(
        "{case_id}\tFULL\t{}\t{produced}\t{verdict}",
        case.shape
    ));
}

fn main() {
    // #govern: see crates/ay-sys/src/govern.rs.
    ay_sys::govern::arm();
    let Options {
        seed,
        cases: n,
        output: out,
    } = parse_options();

    let mut rng = Rng(seed.wrapping_mul(6364136223846793005).wrapping_add(1) | 1);
    let mut smt = String::from("(set-logic QF_NRA)\n(declare-fun x () Real)\n");
    let mut manifest: Vec<String> = Vec::new();
    let mut produced = 0usize;
    let mut declined_isolate = 0usize;
    let mut skipped = 0usize;
    let mut ay_valid_true = 0usize;
    let mut ay_valid_false = 0usize;
    let mut ay_valid_none = 0usize;
    let mut cm_present = 0usize;
    let mut falsified_fail = 0usize;
    let mut shapes: std::collections::BTreeMap<&str, usize> = Default::default();

    for case_id in 0..n {
        let c = gencase(&mut rng);
        // build AY lits with MY roots
        let Some(lits) = build_lits(&c) else {
            declined_isolate += 1;
            continue;
        };
        *shapes.entry(c.shape).or_default() += 1;

        // Drive the module.
        let validity = oexplain_clause_is_valid(&lits);
        match validity {
            Some(true) => ay_valid_true += 1,
            Some(false) => ay_valid_false += 1,
            None => ay_valid_none += 1,
        }
        let cm = oexplain_countermodel(&lits);
        if matches!(cm, Some(Some(_))) {
            cm_present += 1;
        }
        // relevant_pairs, driven directly
        let _ = oexplain_relevant_pairs(&lits);

        let expl = oexplain_univariate(&lits);

        // FULL conjunction query
        append_full_query(&mut smt, &mut manifest, case_id, &c, &lits, expl.is_some());

        if let Some(e) = &expl {
            produced += 1;
            // property (a): false under the trail
            let trail: Vec<i32> = lits.iter().map(|l| l.lit).collect();
            if !oexplain_clause_is_falsified(&e.lits, &trail) {
                falsified_fail += 1;
            }
            // CITED conjunction query — MUST be unsat
            smt.push_str("(push 1)\n");
            for cl in &e.cited {
                let l = lits.iter().find(|l| l.lit == *cl).unwrap();
                smt.push_str(&format!("(assert {})\n", smt_atom(&l.p, l.cond)));
            }
            smt.push_str("(check-sat)\n(pop 1)\n");
            manifest.push(format!(
                "{case_id}\tCITED\t{}\t{:?}\t{:?}",
                c.shape, e.lits, e.cited
            ));
        } else {
            skipped += 1;
        }
    }

    persist(&out, &smt, &manifest);
    print_summary(&RunSummary {
        seed,
        cases: n,
        isolate_declined: declined_isolate,
        produced,
        skipped,
        ay_valid_true,
        ay_valid_false,
        ay_valid_none,
        countermodels: cm_present,
        falsified_fail,
        shapes: &shapes,
    });
}
