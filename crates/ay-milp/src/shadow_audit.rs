// INDEPENDENT ADVERSARIAL AUDIT of the perturbation-matched cut control (arm C,
// `the cut-shadow knob`). Written by the verifier, and deliberately sharing nothing with
// `shadow_control_model`: its own f64 -> rational conversion (IEEE-754 bit
// decomposition, NOT `crate::model::exact`), its own box-activity interval, and cuts
// produced by the shipped root loop rather than a hand-built cut fixture.
//
// The claim under test is the strong one: the shadow rows remove NO POINT of the LP
// relaxation. Adding a row can only ever remove points, so "implied by the column box"
// is necessary and sufficient, and it subsumes both "no integer point is excluded" and
// "the root LP bound is unchanged" -- LP(model) is literally the same SET.

use super::*;
use num_bigint::BigInt;

/// f64 -> exact rational by IEEE-754 bit decomposition. Independent of
/// `crate::model::exact` on purpose: if the construction and its check shared a
/// conversion, a bug in that conversion would be invisible to the check.
fn rat(f: f64) -> Option<BigRational> {
    if !f.is_finite() {
        return None;
    }
    let bits = f.to_bits();
    let neg = bits >> 63 == 1;
    let exp_field = ((bits >> 52) & 0x7ff) as i64;
    let frac = bits & ((1u64 << 52) - 1);
    let (mant, exp) = if exp_field == 0 {
        (frac, -1074i64)
    } else {
        (frac | (1u64 << 52), exp_field - 1075)
    };
    let mut num = BigInt::from(mant);
    if neg {
        num = -num;
    }
    let two = BigInt::from(2u32);
    Some(if exp >= 0 {
        BigRational::new(num * two.pow(exp as u32), BigInt::from(1u32))
    } else {
        BigRational::new(num, two.pow((-exp) as u32))
    })
}

struct Audit {
    rows: usize,
    implied: usize,
    unbounded: usize,
    nnz: usize,
}

/// Exact interval of each added row's activity over the model's column box, and the
/// implication test `lb <= min && max <= ub`.
fn audit_added_rows(base: &Model, aug: &Model) -> Audit {
    let n0 = base.num_rows();
    let mut a = Audit {
        rows: 0,
        implied: 0,
        unbounded: 0,
        nnz: 0,
    };
    for r in n0..aug.num_rows() {
        let (coeffs, lb, ub) = aug.row(Row(r as u32));
        a.rows += 1;
        a.nnz += coeffs.len();
        let mut lo = BigRational::zero();
        let mut hi = BigRational::zero();
        let mut lo_finite = true;
        let mut hi_finite = true;
        for &(c, coef) in coeffs {
            let Some(g) = rat(coef) else {
                lo_finite = false;
                hi_finite = false;
                break;
            };
            let (cl, cu) = base.col_bounds(Col(c));
            // The bound that MINIMISES this term, and the one that maximises it.
            let (blo, bhi) = if coef >= 0.0 { (cl, cu) } else { (cu, cl) };
            match rat(blo) {
                Some(b) => lo += &g * &b,
                None => lo_finite = false,
            }
            match rat(bhi) {
                Some(b) => hi += &g * &b,
                None => hi_finite = false,
            }
        }
        // A row whose box activity is UNBOUNDED in the direction its own bound
        // constrains is not proven implied; count it as a failure, never as a pass.
        let ok_lo = if lb.is_finite() {
            lo_finite && rat(lb).expect("finite") <= lo
        } else {
            true
        };
        let ok_hi = if ub.is_finite() {
            hi_finite && hi <= rat(ub).expect("finite")
        } else {
            true
        };
        if (lb.is_finite() && !lo_finite) || (ub.is_finite() && !hi_finite) {
            a.unbounded += 1;
        }
        if ok_lo && ok_hi {
            a.implied += 1;
        }
    }
    a
}

fn audit_model() -> Model {
    // A checked-in, deterministic liveness case: the root relaxation of this
    // binary knapsack is fractional and its cover cuts are not box-implied.
    // This keeps the audit non-vacuous on a fresh checkout with no local corpus.
    let mut smoke = Model::new();
    let cols: Vec<Col> = (0..4).map(|_| smoke.add_binary_col()).collect();
    smoke.add_row(
        f64::NEG_INFINITY,
        10.0,
        &[
            (cols[0], 6.0),
            (cols[1], 5.0),
            (cols[2], 4.0),
            (cols[3], 3.0),
        ],
    );
    smoke.set_objective(
        &cols
            .iter()
            .copied()
            .map(|col| (col, -1.0))
            .collect::<Vec<_>>(),
        Sense::Minimize,
    );

    smoke
}

/// THE MAIN AUDIT. Run the shipped cut loop (arm B) and the control (arm C) on the SAME
/// model, and prove in exact arithmetic that every row arm C installs is implied by the
/// model's own column bounds -- while checking that arm B's rows are NOT (otherwise the
/// control would be trivially matched and the whole comparison vacuous).
#[test]
fn shadow_rows_are_implied_by_the_box_on_a_fractional_knapsack() {
    let _lock = ay_test_support::env::lock_env();
    let opts = SolveOpts::new();
    let model = audit_model();
    let armb = add_root_cuts(model.clone(), &opts);
    let armc = {
        let _g = crate::tune::activate_caller(
            crate::tune::Profile::EMPTY
                .with(crate::tune::Knob::CutShadow, crate::tune::Setting::Count(1)),
        );
        add_root_cuts(model.clone(), &opts)
    };
    let b = audit_added_rows(&model, &armb);
    let c = audit_added_rows(&model, &armc);
    eprintln!(
        "AUDIT fractional-knapsack: armB rows={} nnz={} box_implied={} | armC rows={} nnz={} \
         box_implied={} unbounded={}",
        b.rows, b.nnz, b.implied, c.rows, c.nnz, c.implied, c.unbounded
    );
    assert_eq!(
        c.rows, b.rows,
        "the control must install the same NUMBER of rows as the real pool"
    );
    assert_eq!(
        c.implied, c.rows,
        "a control row is NOT implied by the column box -- it removes a point \
         of the LP relaxation and the arm is invalid"
    );
    eprintln!(
        "AUDIT TOTAL: armC {}/{} rows implied by the box; armB {}/{} implied (arm B \
         SHOULD be far below 100% -- a real cut cuts something)",
        c.implied, c.rows, b.implied, b.rows
    );
    assert_eq!(c.implied, c.rows);
    assert!(
        b.implied < b.rows,
        "if the REAL pool were also box-implied there would be nothing to measure"
    );
}

/// THE OTHER HALF OF THE SPEC: the control must be BINDING at the root vertex, or it
/// perturbs nothing. The exact activity of each control row at the cut-free root LP
/// vertex is checked against its own right-hand side.
///
/// Also re-derives the cut-free root vertex INDEPENDENTLY (a fresh cold LP solve of the
/// bare model), rather than trusting the vertex the cut loop captured.
#[test]
fn shadow_rows_are_tight_at_an_independently_recomputed_root_vertex() {
    let _lock = ay_test_support::env::lock_env();
    let opts = SolveOpts::new();
    let model = audit_model();
    let armc = {
        let _g = crate::tune::activate_caller(
            crate::tune::Profile::EMPTY
                .with(crate::tune::Knob::CutShadow, crate::tune::Setting::Count(1)),
        );
        add_root_cuts(model.clone(), &opts)
    };
    // Independent cut-free root vertex: the bare model's LP optimum, solved here.
    let objective: Vec<(u32, f64)> = (0..model.num_cols())
        .map(|j| (j as u32, model.obj_coeff(Col(j as u32))))
        .filter(|&(_, a)| a != 0.0)
        .collect();
    let mut lp = FloatLp::from_model(&model, &objective, model.sense()).expect("lp");
    lp.plain_cold = !lp.wide_tall();
    let cand = lp.solve_bounded(&lp.lower.clone(), &lp.upper.clone(), None, None);
    let x0 = &cand.values[..model.num_cols()];
    let n0 = model.num_rows();
    let (mut tight, mut rows, mut worst) = (0usize, 0usize, 0.0f64);
    for r in n0..armc.num_rows() {
        let (coeffs, lb, ub) = armc.row(Row(r as u32));
        rows += 1;
        let act: f64 = coeffs
            .iter()
            .map(|&(c, a)| a * x0.get(c as usize).copied().unwrap_or(0.0))
            .sum();
        let rhs = if lb.is_finite() { lb } else { ub };
        let d = (act - rhs).abs();
        worst = worst.max(d);
        if d <= 1e-7 * (1.0 + rhs.abs()) {
            tight += 1;
        }
    }
    eprintln!(
        "TIGHT fractional-knapsack: {tight}/{rows} rows tight at an independent root vertex, \
         worst |act-rhs| = {worst:.3e}"
    );
    assert!(
        rows > 0 && tight * 4 >= rows * 3,
        "a control that binds nowhere perturbs nothing ({tight}/{rows})"
    );
}
