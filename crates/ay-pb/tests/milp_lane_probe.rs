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
//! strong root LP+cuts *lower bound* for the prove-optimum class. The bounded
//! regression below keeps exact translation, optimum, and original-PB witness
//! checks continuously exercised.

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

#[test]
fn milp_lane_finds_and_rechecks_cover_optimum() {
    // The old opt-in corpus probe only printed timing data.  Keep its essential
    // contract as a bounded fixture: translate a genuine PB covering model,
    // prove its optimum in the MILP lane, then re-check the returned point using
    // the original integer PB semantics.
    let inst = parse_opb(
        "* #variable= 3 #constraint= 1\n\
         min: +1 x1 +1 x2 +1 x3 ;\n\
         +1 x1 +1 x2 +1 x3 >= 2 ;\n",
    )
    .expect("parse fixture");
    let (model, _cols) = pb_to_milp(&inst).expect("linear fixture");
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs(2));
    let mut session = BabSession::new(model.clone(), &opts).expect("bab session");
    let outcome = session.check().expect("check");

    let extract = |vals: &[num_rational::BigRational]| -> Vec<bool> {
        use num_traits::ToPrimitive;
        (0..inst.num_vars as usize)
            .map(|i| vals.get(i).and_then(|r| r.to_f64()).unwrap_or(0.0) > 0.5)
            .collect()
    };
    match outcome {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            let point = extract(&model_values);
            assert_eq!(value, num_rational::BigRational::from_integer(2.into()));
            assert!(point_is_feasible(&inst, &point));
            assert_eq!(point.iter().filter(|&&selected| selected).count(), 2);
        }
        other => panic!("expected a proved optimum, got {other:?}"),
    }
}
