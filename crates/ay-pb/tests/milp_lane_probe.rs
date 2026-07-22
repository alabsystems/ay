//! Feasibility probe for a native MILP lane: translate an OPT-LIN PB instance
//! into an `ay-milp` 0/1 MILP and solve it, to measure whether the MILP engine
//! cracks instances the CDCL portfolio does not (hard-feasibility + prove-optimum
//! classes). This is a *probe*, not the production lane: it prints outcomes and
//! (crucially) re-verifies any returned point against the ORIGINAL integer
//! constraints, so a lossy f64 translation can never masquerade as a real solve.
//!
//! ## Re-measured (2026-07-14, post +40-commit ay-milp / HiGHS-beating): STILL not a lane
//!
//! Even the vastly-improved ay-milp (now above HiGHS on its dense 80x60
//! neural-net-verification benchmark) times out (Unknown, no incumbent, no
//! bound) on fx30 (774v) and domset (473v) at 60s via `check()`. Reason:
//! `check()`'s Native B&B has "no cuts, no presolve" and hands unsettled nodes to
//! an enumerating SMT lane; the VNS-ladder wins are on a structurally different
//! (dense) problem class than sparse combinatorial PB. Verdict unchanged: not a
//! drop-in PB lane until ay-milp's optimize path is effective on sparse
//! set-cover/covering structure. Original verdict retained below.
//!
//! ## Measured verdict (2026-07-14): NOT YET a lane
//!
//! Translation is validated (tiny/triangle -> OPTIMAL value=2, feasible-recheck
//! true). But on the medium-hard PB25 OPT-LIN instances the CDCL portfolio can't
//! close, `ay-milp` (current) **times out with no verdict**:
//!   - `fx30` (774 vars): Unknown/Timeout @ 45s
//!   - `domset` (473 vars): Unknown/Timeout @ 45s
//! AY's CDCL actually BEATS ay-milp on domset (CDCL streams incumbents 220->181;
//! ay-milp finds none), so the gap is NOT primal — it is the DUAL BOUND needed to
//! *prove* those incumbents optimal. A naive "replace CDCL with MILP" lane is a
//! no-go until ay-milp is competition-grade (its own design docs call the current
//! simplex a "toy" dense-tableau engine). The viable lane is narrower: extract a
//! strong root LP+cuts *lower bound* for the prove-optimum class. Re-run this
//! probe as ay-milp matures:
//!   PROBE_FILES=a.opb,b.opb PROBE_SECS=45 \
//!     cargo test -p ay-pb --release --test milp_lane_probe -- --ignored --nocapture

use ay_milp::{BabSession, Col, Model, Outcome, Sense, SolveOpts};
use ay_pb::{parse_opb, PbConstraint, PbInstance, PbRel, PbTerm};
use std::collections::HashMap;
use std::time::Duration;

/// Linear-term view: `(var0, coeff_on_x, constant_offset)`. A negated literal
/// `~x` contributes `c*(1-x) = c - c*x`, i.e. `-c` on x and `+c` to the LHS
/// constant. Returns `None` on a non-linear (product) term.
fn lin(term: &PbTerm) -> Option<(usize, i128, i128)> {
    let [lit] = term.lits.as_slice() else {
        return None;
    };
    let v = (lit.var as usize).checked_sub(1)?;
    if lit.negated {
        Some((v, -term.coeff, term.coeff))
    } else {
        Some((v, term.coeff, 0))
    }
}

/// Aggregate a term list into `(var0 -> coeff)` on x plus the total LHS constant
/// offset from negations. `None` on any non-linear term (OPT-LIN only).
fn linear_row(terms: &[PbTerm]) -> Option<(HashMap<usize, i128>, i128)> {
    let mut coeffs: HashMap<usize, i128> = HashMap::new();
    let mut offset = 0i128;
    for t in terms {
        let (v, cx, k) = lin(t)?;
        *coeffs.entry(v).or_insert(0) += cx;
        offset += k;
    }
    Some((coeffs, offset))
}

fn pb_to_milp(inst: &PbInstance) -> Option<(Model, Vec<Col>)> {
    let mut model = Model::new();
    let cols: Vec<Col> = (0..inst.num_vars).map(|_| model.add_binary_col()).collect();

    for c in &inst.constraints {
        let (coeffs, offset) = linear_row(&c.terms)?;
        let row: Vec<(Col, f64)> = coeffs.iter().map(|(&v, &a)| (cols[v], a as f64)).collect();
        // LHS = sum(a*x) + offset  REL  rhs   ->   sum(a*x)  REL  rhs-offset
        let rhs = (c.rhs - offset) as f64;
        match c.rel {
            PbRel::Ge => model.add_row(rhs, f64::INFINITY, &row),
            PbRel::Eq => model.add_row(rhs, rhs, &row),
            _ => return None,
        };
    }

    if let Some(obj) = &inst.objective {
        let (coeffs, offset) = linear_row(&obj.terms)?;
        let row: Vec<(Col, f64)> = coeffs.iter().map(|(&v, &a)| (cols[v], a as f64)).collect();
        model.set_objective(&row, Sense::Minimize);
        model.set_objective_offset(offset as f64);
    }
    Some((model, cols))
}

/// Re-verify a 0/1 point against the ORIGINAL integer constraints (exact i128).
fn point_is_feasible(inst: &PbInstance, point: &[bool]) -> bool {
    let eval = |c: &PbConstraint| -> Option<bool> {
        let mut lhs = 0i128;
        for t in &c.terms {
            let (v, cx, k) = lin(t)?;
            lhs += k + if point.get(v).copied().unwrap_or(false) {
                cx
            } else {
                0
            };
        }
        match c.rel {
            PbRel::Ge => Some(lhs >= c.rhs),
            PbRel::Eq => Some(lhs == c.rhs),
            _ => None,
        }
    };
    inst.constraints.iter().all(|c| eval(c) == Some(true))
}

fn probe(path: &str, budget_secs: u64) {
    let raw = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(_) => {
            eprintln!("SKIP {path}: not found");
            return;
        }
    };
    let inst = parse_opb(&raw).expect("parse opb");
    let Some((model, _cols)) = pb_to_milp(&inst) else {
        println!("{path}: DECLINE (non-linear)");
        return;
    };
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs(budget_secs));
    let mut session = BabSession::new(model.clone(), &opts).expect("bab session");
    let t0 = std::time::Instant::now();
    let outcome = session.check().expect("check");
    let dt = t0.elapsed().as_secs_f64();

    let name = path.rsplit('/').next().unwrap_or(path);
    let extract = |vals: &[num_rational::BigRational]| -> Vec<bool> {
        use num_traits::ToPrimitive;
        (0..inst.num_vars as usize)
            .map(|i| vals.get(i).and_then(|r| r.to_f64()).unwrap_or(0.0) > 0.5)
            .collect()
    };
    match &outcome {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            let pt = extract(model_values);
            let feas = point_is_feasible(&inst, &pt);
            use num_traits::ToPrimitive;
            println!(
                "{name}: OPTIMAL value={:.0} feasible-recheck={feas} time={dt:.1}s",
                value.to_f64().unwrap_or(f64::NAN)
            );
        }
        Outcome::Feasible {
            model_values,
            incumbent_only,
            dual_bound,
        } => {
            use num_traits::ToPrimitive;
            let pt = extract(model_values);
            let feas = point_is_feasible(&inst, &pt);
            let db = dual_bound.as_ref().and_then(|d| d.to_f64());
            println!("{name}: FEASIBLE (incumbent_only={incumbent_only}) feasible-recheck={feas} dual_bound={db:?} time={dt:.1}s");
        }
        Outcome::Infeasible { .. } => println!("{name}: INFEASIBLE time={dt:.1}s"),
        Outcome::Bound {
            dual_bound,
            rigorous,
        } => {
            use num_traits::ToPrimitive;
            println!(
                "{name}: BOUND dual={:.1} rigorous={rigorous} time={dt:.1}s",
                dual_bound.to_f64().unwrap_or(f64::NAN)
            );
        }
        Outcome::Unbounded => println!("{name}: UNBOUNDED time={dt:.1}s"),
        Outcome::Unknown { reason } => println!("{name}: UNKNOWN ({reason:?}) time={dt:.1}s"),
        _ => println!("{name}: OTHER {outcome:?} time={dt:.1}s"),
    }
}

#[test]
#[ignore = "manual MILP-lane feasibility probe; run with --ignored --nocapture"]
fn milp_lane_probe_hard_instances() {
    let budget: u64 = std::env::var("PROBE_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(60);
    for p in std::env::var("PROBE_FILES").unwrap_or_default().split(',') {
        if !p.is_empty() {
            probe(p, budget);
        }
    }
}
