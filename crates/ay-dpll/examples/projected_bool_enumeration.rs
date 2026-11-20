//! Native TY indicator-family enumeration with checked source completeness.
//!
//! Usage: projected_bool_enumeration [n=10] [k=4] [cap=1024] [query-dump-dir]
//! The optional directory captures the actual terminal original-source query;
//! existing strict-check diagnostic flags report any refusing envelope charge.

use ay_dpll::api::{BoolEnumerationOutcome, Logic, Solver, Sort};
use std::time::{Duration, Instant};

fn main() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let n = args
        .next()
        .map(|value| value.parse::<usize>())
        .transpose()
        .map_err(|error| error.to_string())?
        .unwrap_or(10);
    let k = args
        .next()
        .map(|value| value.parse::<i64>())
        .transpose()
        .map_err(|error| error.to_string())?
        .unwrap_or(4);
    let cap = args
        .next()
        .map(|value| value.parse::<usize>())
        .transpose()
        .map_err(|error| error.to_string())?
        .unwrap_or(1024);
    if let Some(directory) = args.next() {
        if !ay_core::set_global_misc_cli_flags_with(|flags| {
            flags.dump_query_dir = Some(directory);
            flags.probe_strict_check = true;
        }) {
            return Err("process diagnostic configuration was already captured".into());
        }
    }
    let mut solver = Solver::try_new(Logic::QfLia).map_err(|error| error.to_string())?;
    solver.set_timeout(Some(Duration::from_secs(60)));
    let mut leaves = Vec::new();
    for id in 0..n {
        leaves.push(
            solver
                .try_declare_const(&format!("edge{id}"), Sort::Bool)
                .map_err(|error| error.to_string())?,
        );
    }
    let one = solver.int_const(1);
    let zero = solver.int_const(0);
    let mut indicators = Vec::new();
    for &leaf in &leaves {
        indicators.push(
            solver
                .try_ite(leaf, one, zero)
                .map_err(|error| error.to_string())?,
        );
    }
    let sum = solver
        .try_add_many(&indicators)
        .map_err(|error| error.to_string())?;
    let threshold = solver.int_const(k);
    let root = solver
        .try_ge(sum, threshold)
        .map_err(|error| error.to_string())?;
    solver
        .try_assert_term(root)
        .map_err(|error| error.to_string())?;
    let started = Instant::now();
    let report = solver
        .try_enumerate_bool(&leaves, cap)
        .map_err(|error| error.to_string())?;
    for end in [50, 800] {
        if report.rows().len() < end {
            continue;
        }
        let rows = &report.rows()[end - 50..end];
        let conflicts: u64 = rows.iter().map(|row| row.search_work().conflicts).sum();
        let decisions: u64 = rows.iter().map(|row| row.search_work().decisions).sum();
        let propagations: u64 = rows.iter().map(|row| row.search_work().propagations).sum();
        let materialization: u64 = rows
            .iter()
            .map(|row| row.candidate_materialization_work())
            .sum();
        let validation: u64 = rows.iter().map(|row| row.original_validation_work()).sum();
        println!("models{}..{}: conflicts={conflicts}, decisions={decisions}, propagations={propagations}, materialization={materialization}, original_validation={validation}", end - 49, end);
    }
    println!(
        "outcome={:?}, rows={}, elapsed={:?}",
        report.outcome(),
        report.rows().len(),
        started.elapsed()
    );
    println!("statistics={:?}", report.statistics());
    println!("diagnostic={:?}", report.diagnostic());
    match report.outcome() {
        BoolEnumerationOutcome::Exhaustive => {
            println!(
                "completeness=native-strict-source-proof; external_surface={:?}",
                report
                    .completeness_proof()
                    .map(|proof| &proof.carcara_surface)
            );
            Ok(())
        }
        other => Err(format!(
            "enumeration did not establish completeness: {other:?}"
        )),
    }
}
