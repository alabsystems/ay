// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Diagnostic + soundness regression harness for the INTERNAL `check_sat`
//! theory loop on QF_LIA disequality / mod-div fragments.
//!
//! Background: CEGAR feasibility checks call the internal `check_sat` path
//! (`check_sat_internal`), which is fast but theory-incomplete on some
//! disequality-heavy / mod-div QF_LIA queries — it returns `Unknown` and the
//! caller falls back to the complete-but-slow executor (which matches z3). This
//! harness:
//!   (a) SOUNDNESS GUARD (permanent): the internal loop must NEVER return a
//!       definitive answer opposite to the known verdict (no Sat-for-unsat /
//!       Unsat-for-sat). A regression here is a wrong-answer bug.
//!   (b) CHARACTERIZATION: logs which constructed queries the internal loop
//!       punts on (`Unknown`) — the actionable completeness-gap list that a
//!       future internal-completeness fix should target.

use super::*;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use std::sync::Arc;

fn ivar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn imod(a: ChcExpr, m: i64) -> ChcExpr {
    ChcExpr::Op(ChcOp::Mod, vec![Arc::new(a), Arc::new(ChcExpr::int(m))])
}

/// (label, formula, expect_sat). `expect_sat == false` means UNSAT.
fn corpus() -> Vec<(String, ChcExpr, bool)> {
    let mut out = Vec::new();

    // Pigeonhole: N vars each in [0, N-2], all pairwise distinct -> UNSAT.
    for n in 3..=7i64 {
        let mut cs = Vec::new();
        let vars: Vec<ChcExpr> = (0..n).map(|i| ivar(&format!("p{n}_{i}"))).collect();
        for v in &vars {
            cs.push(ChcExpr::ge(v.clone(), ChcExpr::int(0)));
            cs.push(ChcExpr::le(v.clone(), ChcExpr::int(n - 2)));
        }
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                cs.push(ChcExpr::ne(vars[i].clone(), vars[j].clone()));
            }
        }
        out.push((format!("pigeonhole_{n}"), ChcExpr::and_all(cs), false));
    }

    // Distinct strictly-increasing chain in [0, N] -> SAT.
    for n in 3..=6i64 {
        let mut cs = Vec::new();
        let vars: Vec<ChcExpr> = (0..n).map(|i| ivar(&format!("c{n}_{i}"))).collect();
        for v in &vars {
            cs.push(ChcExpr::ge(v.clone(), ChcExpr::int(0)));
            cs.push(ChcExpr::le(v.clone(), ChcExpr::int(n)));
        }
        for i in 0..(vars.len() - 1) {
            cs.push(ChcExpr::lt(vars[i].clone(), vars[i + 1].clone()));
        }
        out.push((format!("distinct_chain_{n}"), ChcExpr::and_all(cs), true));
    }

    // CRT: x in [0,30], x%3==1 && x%5==2 -> SAT (x = 7, 22).
    {
        let x = ivar("crt");
        out.push((
            "crt_mod_sat".into(),
            ChcExpr::and_all(vec![
                ChcExpr::ge(x.clone(), ChcExpr::int(0)),
                ChcExpr::le(x.clone(), ChcExpr::int(30)),
                ChcExpr::eq(imod(x.clone(), 3), ChcExpr::int(1)),
                ChcExpr::eq(imod(x, 5), ChcExpr::int(2)),
            ]),
            true,
        ));
    }

    // Mod contradiction: x%2==0 && x%2==1 -> UNSAT.
    {
        let x = ivar("mc");
        out.push((
            "mod_contradiction".into(),
            ChcExpr::and_all(vec![
                ChcExpr::eq(imod(x.clone(), 2), ChcExpr::int(0)),
                ChcExpr::eq(imod(x, 2), ChcExpr::int(1)),
            ]),
            false,
        ));
    }

    // Mixed disequality + mod: x,y in [0,4], x!=y, x%2==0, y%2==0 -> SAT (0,2).
    {
        let x = ivar("mx");
        let y = ivar("my");
        out.push((
            "diseq_mod_mixed_sat".into(),
            ChcExpr::and_all(vec![
                ChcExpr::ge(x.clone(), ChcExpr::int(0)),
                ChcExpr::le(x.clone(), ChcExpr::int(4)),
                ChcExpr::ge(y.clone(), ChcExpr::int(0)),
                ChcExpr::le(y.clone(), ChcExpr::int(4)),
                ChcExpr::ne(x.clone(), y.clone()),
                ChcExpr::eq(imod(x, 2), ChcExpr::int(0)),
                ChcExpr::eq(imod(y, 2), ChcExpr::int(0)),
            ]),
            true,
        ));
    }

    out
}

#[test]
fn diagnose_internal_check_sat_completeness_qf_lia() {
    let mut unknowns: Vec<(String, bool)> = Vec::new();
    let cases = corpus();
    let total = cases.len();

    for (label, formula, expect_sat) in cases {
        let mut ctx = SmtContext::new();
        // 5s per-query cap so a hard case can't hang the test. With no genuine
        // timeout pressure on these tiny formulas, an `Unknown` reflects the
        // internal loop's structural incompleteness, not budget exhaustion.
        ctx.check_timeout
            .set(Some(std::time::Duration::from_secs(5)));
        let r = ctx.check_sat_internal(&formula);

        if r.is_sat() {
            assert!(
                expect_sat,
                "SOUNDNESS VIOLATION: internal check_sat returned SAT for UNSAT `{label}`"
            );
        } else if r.is_unsat() {
            assert!(
                !expect_sat,
                "SOUNDNESS VIOLATION: internal check_sat returned UNSAT for SAT `{label}`"
            );
        } else {
            unknowns.push((label, expect_sat));
        }
    }

    eprintln!(
        "INTERNAL check_sat QF_LIA completeness: {}/{} decided, {} punted to executor fallback:",
        total - unknowns.len(),
        total,
        unknowns.len()
    );
    for (label, exp) in &unknowns {
        eprintln!(
            "  PUNT {label} (truth={})",
            if *exp { "sat" } else { "unsat" }
        );
    }
}
