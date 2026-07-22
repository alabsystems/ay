//! Root-LP bound probe: translate an OPT-LIN PB into a CONTINUOUS [0,1] model and
//! solve the pure LP relaxation with ay-milp's exact LpSession. Prints the exact
//! root LP optimum so we can compare it to a known integer incumbent and decide
//! whether the integrality gap (LP*..IntOpt) is the bottleneck.
//!
//!   PROBE_FILES=a.opb,b.opb PROBE_SECS=60 \
//!     cargo test -p ay-pb --release --test lp_root_probe -- --ignored --nocapture

use ay_milp::{Col, LpSession, Model, Outcome, Sense, SolveOpts};
use ay_pb::{parse_opb, PbInstance, PbRel, PbTerm};
use std::collections::HashMap;
use std::time::Duration;

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

/// Build a CONTINUOUS relaxation: every var is a [0,1] real column.
fn pb_to_lp(inst: &PbInstance) -> Option<Model> {
    let mut model = Model::new();
    let cols: Vec<Col> = (0..inst.num_vars)
        .map(|_| model.add_col(0.0, 1.0))
        .collect();
    for c in &inst.constraints {
        let (coeffs, offset) = linear_row(&c.terms)?;
        let row: Vec<(Col, f64)> = coeffs.iter().map(|(&v, &a)| (cols[v], a as f64)).collect();
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
    Some(model)
}

fn probe(path: &str, budget_secs: u64) {
    let Ok(raw) = std::fs::read_to_string(path) else {
        eprintln!("SKIP {path}: not found");
        return;
    };
    let inst = parse_opb(&raw).expect("parse opb");
    let name = path.rsplit('/').next().unwrap_or(path);
    let Some(model) = pb_to_lp(&inst) else {
        println!("{name}: DECLINE (non-linear)");
        return;
    };
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs(budget_secs));
    let mut lp = LpSession::new(&model, &opts).expect("lp session");
    let t0 = std::time::Instant::now();
    let outcome = lp.optimize_model_objective().expect("optimize");
    let dt = t0.elapsed().as_secs_f64();
    use num_traits::ToPrimitive;
    match &outcome {
        Outcome::Optimal { value, .. } => println!(
            "{name}: nvars={} ncons={} ROOT-LP* = {:.4} time={dt:.2}s",
            inst.num_vars,
            inst.constraints.len(),
            value.to_f64().unwrap_or(f64::NAN)
        ),
        Outcome::Infeasible { .. } => println!("{name}: LP INFEASIBLE time={dt:.2}s"),
        Outcome::Unbounded => println!("{name}: LP UNBOUNDED time={dt:.2}s"),
        Outcome::Unknown { reason } => println!("{name}: LP UNKNOWN ({reason:?}) time={dt:.2}s"),
        other => println!("{name}: LP OTHER {other:?} time={dt:.2}s"),
    }
}

#[test]
#[ignore = "manual root-LP probe; run with --ignored --nocapture"]
fn lp_root_probe_instances() {
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
