// Copyright 2026 Andrew Yates
// Temporary profiling runner: per-check-sat wall time + phase breakdown + reason.
use std::time::Instant;

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: smt_profile <file.smt2>");
    let input = std::fs::read_to_string(&path).expect("read");
    let commands = ay_frontend::parse(&input).expect("parse");
    let mut exec = ay_dpll::Executor::new();
    let mut idx = 0usize;
    for cmd in &commands {
        let is_check = matches!(
            cmd,
            ay_frontend::Command::CheckSat | ay_frontend::Command::CheckSatAssuming(_)
        );
        let t0 = Instant::now();
        let out = exec.execute(cmd).expect("execute");
        let dt = t0.elapsed().as_secs_f64();
        if is_check {
            idx += 1;
            let res = out.unwrap_or_default();
            let reason = exec.get_reason_unknown();
            let s = exec.statistics();
            let sat_solve = s.get_float("time.dpll.sat_solve").unwrap_or(0.0);
            let theory_check = s.get_float("time.dpll.theory_check").unwrap_or(0.0);
            let theory_sync = s.get_float("time.dpll.theory_sync").unwrap_or(0.0);
            let preprocess = s.get_float("time.construct.preprocess").unwrap_or(0.0);
            eprintln!(
                "CHK#{idx:<3} {res:<8} dt={dt:7.3}s sat={sat_solve:6.3} thy_chk={theory_check:6.3} thy_sync={theory_sync:6.3} prep={preprocess:6.3} confl={confl} dec={dec} restarts={rst} refine={rf} reason={reason:?}",
                confl = s.conflicts,
                dec = s.decisions,
                rst = s.restarts,
                rf = s.refinement_count,
            );
        }
    }
}
