//! Root-LP translation regression: translate an OPT-LIN PB into a continuous
//! `[0,1]` model and require ay-milp's exact `LpSession` to return the known
//! fractional optimum.

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

#[test]
fn root_lp_returns_exact_fractional_cover_bound() {
    // min x1+x2 subject to 2*x1+2*x2 >= 3 has LP optimum 3/2 but
    // integer optimum 2.  This pins both translation and the root relaxation,
    // including the integrality gap that the former manual probe investigated.
    let inst = parse_opb(
        "* #variable= 2 #constraint= 1\n\
         min: +1 x1 +1 x2 ;\n\
         +2 x1 +2 x2 >= 3 ;\n",
    )
    .expect("parse fixture");
    let model = pb_to_lp(&inst).expect("linear fixture");
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs(2));
    let mut lp = LpSession::new(&model, &opts).expect("lp session");
    let outcome = lp.optimize_model_objective().expect("optimize");
    match outcome {
        Outcome::Optimal { value, .. } => {
            assert_eq!(
                value,
                num_rational::BigRational::new(3.into(), 2.into()),
                "the continuous relaxation must preserve its fractional optimum"
            );
        }
        other => panic!("expected a proved LP optimum, got {other:?}"),
    }
}
