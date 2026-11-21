// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The route of `ay lp solve` for MPS and CPLEX LP input (and of the
//! z3-compatible `-lp` mode): AY's MILP engine (`ay-milp`) on the one exact
//! reading of the file, run in rounds so that each improving
//! point is written as soon as a round ends.
//!
//! `ay-milp` reports its point only when `BabSession::check` returns, and it
//! has no interrupt. The route therefore runs the engine with a round time
//! limit that doubles from [`FIRST_ROUND`], seeds each round with the best
//! point so far, and writes a point when it improves. A run stopped by a
//! signal keeps the block written at the end of the last finished round.
//!
//! # One model
//!
//! The file is read once, exactly, by [`ay_lp::parse_mps_exact`] or
//! [`ay_lp::parse_lp_exact`]. The
//! engine's model is built from those rationals ([`engine_model`],
//! [`ay_milp::model_from_exact`]), column for column; nothing passes through
//! `f64` on the way in. The engine's verdicts, the printed objective and the
//! point checks are all about that reading. (The route once handed the file
//! to the engine's own MPS reader, which reads some files differently, and
//! later passed the engine numbers rounded to `f64`; both printed verdicts
//! about another model, AY-N6 review, AY-N11.)
//!
//! The engine's model drops a side of `1e20` or more in its open direction
//! (an upper bound `>= 1e20`, a lower bound `<= -1e20`), as solvers read
//! such values: a relaxation, so an infeasibility of the engine's model is
//! one of the file's, and an optimum of the engine's model at a point of the
//! file's model is the file's optimum.
//!
//! # What is printed, and what confirms it
//!
//! - A point (`o`/`v` block): the engine's exact point passes
//!   [`ExactProblem::check_point`] at tolerance 0 (every bound, row and
//!   integrality exactly), and its written texts, read back, pass
//!   [`ExactProblem::check_written`]: the MIPLIB checker's own test at
//!   `1e-9`, a thousandth of the competition's tolerance.
//! - `s OPTIMAL`: additionally, the engine's outcome replays exactly against
//!   its model (`Outcome::check_against`, which accepts optimality only when
//!   a verified certificate's bound meets the point's value), and the last
//!   written point has that value. Otherwise the run ends `s FEASIBLE` with a
//!   `c optimality not confirmed:` line.
//! - `s INFEASIBLE`: an empty column domain or an empty constraint row seen
//!   exactly ([`ExactProblem::empty_domain`]), or the engine's infeasibility
//!   certificate (root Farkas or case-split tree) replayed exactly against its
//!   model. Otherwise `s UNKNOWN` with a `c infeasibility not confirmed:`
//!   line.
//! - `s UNBOUNDED` is never printed: the engine exports no ray to check.
//!
//! The dense simplex of `ay-lp` answers for no input: it works on a rounded
//! copy and has no exact certificate, so none of its verdicts could be
//! confirmed (AY-N11, AY-N12).

use std::io::Write;
use std::time::{Duration, Instant};

use anyhow::Result;
use ay_lp::exact::decimal::write_value;
use ay_lp::{ExactProblem, Sense};
use ay_milp::{BabSession, MpsProblem, Outcome, RationalColumn, RationalRow, SolveOpts};
use num_rational::BigRational;
use num_traits::ToPrimitive;

use super::write_block;

/// Time limit of the first round; each later round doubles it.
const FIRST_ROUND: Duration = Duration::from_secs(20);

/// How a sparse solve ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SparseEnd {
    /// The last written point is optimal, confirmed exactly.
    Optimal,
    /// The model has no point, confirmed exactly.
    Infeasible,
    /// The time limit ran out, or no verdict could be confirmed.
    Stopped,
}

/// `side` unless it is `1e20` or more in its open direction (module docs).
fn engine_side(side: Option<&BigRational>, upper: bool) -> Option<BigRational> {
    let side = side?;
    let open = ay_lp::exact::referee_infinity();
    let dropped = if upper { *side >= open } else { *side <= -open };
    (!dropped).then(|| side.clone())
}

/// The engine's model of `exact`: column `j` is `exact.columns[j]`, one row
/// per constraint row, the same objective and constant, every number the
/// rational the file wrote.
fn engine_model(exact: &ExactProblem) -> Result<MpsProblem, String> {
    let columns: Vec<RationalColumn> = exact
        .columns
        .iter()
        .map(|c| RationalColumn {
            name: c.name.clone(),
            lower: engine_side(c.lower.as_ref(), false),
            upper: engine_side(c.upper.as_ref(), true),
            integral: c.is_integral(),
            objective: c.objective.clone(),
        })
        .collect();
    let rows: Vec<RationalRow> = exact
        .rows
        .iter()
        .map(|r| RationalRow {
            name: r.name.clone(),
            coeffs: r.coeffs.clone(),
            lower: engine_side(r.lower.as_ref(), false),
            upper: engine_side(r.upper.as_ref(), true),
        })
        .collect();
    let sense = match exact.sense {
        Sense::Min => ay_milp::Sense::Minimize,
        Sense::Max => ay_milp::Sense::Maximize,
    };
    let milp = ay_milp::model_from_exact(&exact.name, sense, &columns, &rows, &exact.offset)
        .map_err(|e| format!("building the engine's model: {e}"))?;
    if milp.col_names.len() != exact.columns.len() {
        return Err(format!(
            "the engine's model has {} columns for {} columns read",
            milp.col_names.len(),
            exact.columns.len()
        ));
    }
    Ok(milp)
}

fn improves(sense: Sense, best: Option<&BigRational>, candidate: &BigRational) -> bool {
    match (best, sense) {
        (None, _) => true,
        (Some(b), Sense::Min) => candidate < b,
        (Some(b), Sense::Max) => candidate > b,
    }
}

/// The `o`/`v` block of `values` (one per column) whose exact objective is
/// `objective`, after both checks of the module docs; a message when either
/// fails or a value has no text the checker reads.
pub(super) fn checked_block(
    exact: &ExactProblem,
    values: &[BigRational],
) -> Result<(BigRational, String), String> {
    use std::fmt::Write as _;
    let objective = exact.check_point(values, &BigRational::default())?;
    let objective_text =
        write_value(&objective).ok_or_else(|| format!("objective {objective} has no text"))?;
    let mut texts = Vec::with_capacity(values.len());
    for (column, value) in exact.columns.iter().zip(values) {
        texts.push(
            write_value(value)
                .ok_or_else(|| format!("value {value} of '{}' has no text", column.name))?,
        );
    }
    exact.check_written(&objective_text, &texts)?;
    let mut block = String::new();
    let _ = writeln!(block, "o {objective_text}");
    for (column, text) in exact.columns.iter().zip(&texts) {
        let _ = writeln!(block, "v {} = {text}", column.name);
    }
    block.push_str(&super::block_end(texts.len()));
    Ok((objective, block))
}

/// Solves `exact` with `ay-milp`, writing each improving checked point to
/// `out`. `time_limit` bounds the whole solve; without it rounds continue
/// until a verdict or a signal. Returns how the solve ended and the number
/// of points written.
pub(super) fn solve_sparse(
    exact: &ExactProblem,
    time_limit: Option<Duration>,
    out: &mut dyn Write,
) -> Result<(SparseEnd, usize)> {
    let started = Instant::now();
    if let Some(reason) = exact.empty_domain() {
        write_block(out, &format!("c infeasible: {reason}\n"))?;
        return Ok((SparseEnd::Infeasible, 0));
    }
    let milp = match engine_model(exact) {
        Ok(milp) => milp,
        Err(e) => {
            write_block(out, &format!("c stopped: {e}\n"))?;
            return Ok((SparseEnd::Stopped, 0));
        }
    };
    let mut best: Option<BigRational> = None;
    let mut seed: Option<Vec<f64>> = None;
    let mut written = 0usize;
    let mut round = FIRST_ROUND;
    loop {
        let limit = match time_limit {
            Some(total) => {
                let left = total.saturating_sub(started.elapsed());
                if left.is_zero() {
                    return Ok((SparseEnd::Stopped, written));
                }
                round.min(left)
            }
            None => round,
        };
        // The search rounds buy no tree certificate: an infeasibility is
        // certified by its own retry and an optimum by its own tree
        // (`confirm_infeasible`, `confirm_optimum`).
        let opts = SolveOpts::new()
            .with_time_limit(limit)
            .with_tree_cert_leaves(0);
        let mut session = match BabSession::new(milp.model.clone(), &opts) {
            Ok(session) => session,
            Err(e) => {
                write_block(out, &format!("c stopped: sparse engine setup: {e:?}\n"))?;
                return Ok((SparseEnd::Stopped, written));
            }
        };
        if let Some(seed) = &seed {
            session.seed_incumbent(seed);
        }
        let round_started = Instant::now();
        let outcome = match session.check() {
            Ok(outcome) => outcome,
            Err(e) => {
                write_block(out, &format!("c stopped: sparse engine: {e:?}\n"))?;
                return Ok((SparseEnd::Stopped, written));
            }
        };
        let point = match &outcome {
            Outcome::Optimal { model_values, .. } | Outcome::Feasible { model_values, .. } => {
                Some(model_values)
            }
            Outcome::Infeasible { .. } => {
                let note = if written > 0 {
                    "c stopped: the sparse engine contradicted a checked point\n".to_string()
                } else {
                    match confirm_infeasible(
                        &milp.model,
                        &outcome,
                        proof_deadline(started, time_limit),
                    ) {
                        Ok(how) => {
                            write_block(out, &format!("c infeasible: {how}\n"))?;
                            return Ok((SparseEnd::Infeasible, 0));
                        }
                        Err(why) => format!("c infeasibility not confirmed: {why}\n"),
                    }
                };
                write_block(out, &note)?;
                return Ok((SparseEnd::Stopped, written));
            }
            Outcome::Unbounded => {
                write_block(
                    out,
                    "c unboundedness not confirmed: the engine exports no ray to check\n",
                )?;
                return Ok((SparseEnd::Stopped, written));
            }
            _ => None,
        };
        if let Some(model_values) = point {
            match checked_block(exact, model_values) {
                Ok((objective, block)) => {
                    if improves(exact.sense, best.as_ref(), &objective) {
                        write_block(out, &block)?;
                        written += 1;
                        best = Some(objective.clone());
                        seed = Some(
                            model_values
                                .iter()
                                .map(|v| v.to_f64().unwrap_or(0.0))
                                .collect(),
                        );
                    }
                    // The engine claims an optimum, or gave up on a point
                    // (a longer round would repeat that): try to prove it.
                    let gave_up = round_started.elapsed() < limit / 2;
                    let claim = match &outcome {
                        Outcome::Optimal { value, .. } => Some((Some(&outcome), value.clone())),
                        _ if gave_up => Some((None, milp.model.objective_value_at(model_values))),
                        _ => None,
                    };
                    if let Some((sealed, value)) = claim {
                        let note = if best.as_ref() != Some(&objective) {
                            "c optimality not confirmed: a written point is better than the \
                             engine's\n"
                                .to_string()
                        } else {
                            match confirm_optimum(
                                &milp.model,
                                sealed,
                                &value,
                                model_values,
                                proof_deadline(started, time_limit),
                            ) {
                                Ok(how) => {
                                    write_block(out, &format!("c optimal: {how}\n"))?;
                                    return Ok((SparseEnd::Optimal, written));
                                }
                                Err(why) => {
                                    let claim = if sealed.is_some() {
                                        "the engine's optimum"
                                    } else {
                                        "the point the engine stopped at"
                                    };
                                    format!("c optimality not confirmed for {claim}: {why}\n")
                                }
                            }
                        };
                        write_block(out, &note)?;
                        if sealed.is_some() {
                            return Ok((SparseEnd::Stopped, written));
                        }
                    }
                }
                Err(e) => {
                    write_block(out, &format!("c sparse engine point rejected: {e}\n"))?;
                    if matches!(outcome, Outcome::Optimal { .. }) {
                        return Ok((SparseEnd::Stopped, written));
                    }
                }
            }
        }
        // A round that ends well inside its limit without a verdict gave up
        // for its own reasons; a longer round would repeat it.
        if round_started.elapsed() < limit / 2 {
            write_block(
                out,
                &format!("c stopped: sparse engine: {}\n", outcome_word(&outcome)),
            )?;
            return Ok((SparseEnd::Stopped, written));
        }
        round = round.saturating_mul(2);
    }
}

/// Most leaves an optimality tree may have.
const OPT_TREE_LEAVES: usize = 20_000;
/// The tree's deterministic work budget, in passes over the model times its
/// nonzeros (the budget `ay-milp solve` uses).
const OPT_TREE_WORK_NNZ: u64 = 24_000_000;
/// Wall-clock safety net of one proof attempt.
const OPT_TREE_SECS: Duration = Duration::from_secs(60);
/// Leaf budget of the case-split tree of an infeasibility proof.
const INFEASIBILITY_TREE_LEAVES: usize = 4096;

/// When a proof attempt must end: the run's time limit, and at most
/// [`OPT_TREE_SECS`] from now.
fn proof_deadline(started: Instant, time_limit: Option<Duration>) -> Instant {
    let cap = Instant::now() + OPT_TREE_SECS;
    time_limit.map_or(cap, |total| (started + total).min(cap))
}

/// Confirms that `model_values`, which attain `value` (the engine model's
/// frame), are optimal, in exact arithmetic: the certificate the engine
/// attached to `outcome`, replayed by `Outcome::check_against`; or else an
/// optimality tree derived after the fact (`ay_milp::derive_optimality_tree`:
/// every leaf an exact dual bound or an exact infeasibility proof of its box)
/// whose pairing with the point `MilpOptimalityCertificate::verify` accepts.
fn confirm_optimum(
    model: &ay_milp::Model,
    outcome: Option<&Outcome>,
    value: &BigRational,
    model_values: &[BigRational],
    deadline: Instant,
) -> Result<String, String> {
    let sealed = match outcome.map(|o| o.check_against(model)) {
        Some(Ok(checked)) if checked.is_rim_closed() => {
            return Ok("the engine's certificate replayed exactly".to_string());
        }
        Some(Ok(_)) => "the engine's outcome does not close; ".to_string(),
        Some(Err(e)) => format!("{e}; "),
        None => String::new(),
    };
    let nnz: u64 = (0..model.num_rows())
        .filter_map(|r| model.row_at(r))
        .map(|r| u64::try_from(model.row(r).0.len()).unwrap_or(u64::MAX))
        .sum();
    let budget = ay_milp::OptimalityTreeBudget::new(OPT_TREE_LEAVES)
        .with_work((OPT_TREE_WORK_NNZ / nnz.max(1)).max(1))
        .with_deadline(Some(deadline));
    let (tree, report) =
        ay_milp::derive_optimality_tree_reported(model, value, model_values, &budget);
    match tree {
        Some(cert) => match cert.verify(model) {
            Ok(()) => Ok(format!(
                "an optimality tree of {} leaves replayed exactly",
                cert.num_leaves()
            )),
            Err(e) => Err(format!(
                "{sealed}the optimality tree does not verify: {e:?}"
            )),
        },
        None => Err(format!("{sealed}no optimality tree ({:?})", report.decline)),
    }
}

/// Confirms an infeasibility verdict in exact arithmetic: the certificate the
/// engine attached to `outcome`, replayed by `Outcome::check_against`; or else
/// one more solve on the engine's native branch-and-bound, the lane that
/// exports a root Farkas or a whole case-split tree, whose certificate is
/// replayed the same way.
fn confirm_infeasible(
    model: &ay_milp::Model,
    outcome: &Outcome,
    deadline: Instant,
) -> Result<String, String> {
    let first = match outcome.check_against(model) {
        Ok(checked) if checked.is_rim_closed() => {
            return Ok("the engine's certificate replayed exactly".to_string());
        }
        Ok(_) => "the engine's outcome does not close".to_string(),
        Err(e) => e.to_string(),
    };
    let left = deadline.saturating_duration_since(Instant::now());
    if left.is_zero() {
        return Err(first);
    }
    let engine = ay_milp::EngineEconomics::new()
        .with_cuts(false)
        .with_presolve_share(0.0)
        .map_err(|e| format!("{first}; {e:?}"))?;
    let opts = SolveOpts::new()
        .with_time_limit(left)
        .with_structure_routing(false)
        .with_tree_cert_leaves(INFEASIBILITY_TREE_LEAVES)
        .with_engine(engine);
    let mut session =
        BabSession::new(model.clone(), &opts).map_err(|e| format!("{first}; {e:?}"))?;
    let again = session.check().map_err(|e| format!("{first}; {e:?}"))?;
    if !again.is_infeasible() {
        return Err(format!(
            "{first}; the native search ended {}",
            outcome_word(&again)
        ));
    }
    match again.check_against(model) {
        Ok(checked) if checked.is_rim_closed() => {
            Ok("the native search's certificate replayed exactly".to_string())
        }
        Ok(_) => Err(format!(
            "{first}; the native search's outcome does not close"
        )),
        Err(e) => Err(format!("{first}; native search: {e}")),
    }
}

fn outcome_word(outcome: &Outcome) -> String {
    match outcome {
        Outcome::Feasible { .. } => "feasible point without a proof".to_string(),
        Outcome::Bound { .. } => "bound without a point".to_string(),
        Outcome::Unknown { reason } => format!("unknown ({reason:?})"),
        other => format!("{other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(text: &str, limit: u64) -> (SparseEnd, usize, String) {
        let exact = ay_lp::parse_mps_exact(text).expect("parse");
        let mut out: Vec<u8> = Vec::new();
        let (end, written) =
            solve_sparse(&exact, Some(Duration::from_secs(limit)), &mut out).expect("solve");
        (end, written, String::from_utf8(out).expect("utf8"))
    }

    const KNAPSACK: &str = "NAME KNAP
OBJSENSE
    MAX
ROWS
 N OBJ
 L CAP
COLUMNS
    MARKER 'MARKER' 'INTORG'
    X OBJ 3 CAP 2
    Y OBJ 4 CAP 3
    MARKER 'MARKER' 'INTEND'
RHS
    RHS CAP 6
BOUNDS
 UP BND X 2
 UP BND Y 2
ENDATA
";

    /// The sparse route proves the knapsack optimum (8 at x=0, y=2, by
    /// enumeration) and writes it as the last block.
    #[test]
    fn test_sparse_route_solves_small_mip() {
        let (end, written, text) = run(KNAPSACK, 60);
        assert_eq!(end, SparseEnd::Optimal, "{text}");
        assert!(written >= 1);
        assert!(
            text.contains("o 8\nv X = 0\nv Y = 2\nc solution end 2\nc optimal: "),
            "{text}"
        );
    }

    /// AY-N6: a sparse model far above the dense tableau cap (150000 binary
    /// columns, so 150001 x 300001 dense) is solved by the sparse route; the
    /// dense route refuses it with `ResourceLimit`.
    #[test]
    fn test_sparse_route_solves_model_too_large_for_dense_tableau() {
        let n = 150_000;
        let mut mps =
            String::from("NAME BIG\nROWS\n N OBJ\n G COVER\nCOLUMNS\n    M 'MARKER' 'INTORG'\n");
        for i in 0..n {
            mps.push_str(&format!("    X{i} OBJ 1 COVER 1\n"));
        }
        mps.push_str("    M 'MARKER' 'INTEND'\nRHS\n    RHS COVER 1\nBOUNDS\n");
        for i in 0..n {
            mps.push_str(&format!(" UP BND X{i} 1\n"));
        }
        mps.push_str("ENDATA\n");
        let problem = ay_lp::parse_mps(&mps).expect("parse");
        assert!(matches!(
            ay_lp::solve(&problem),
            Err(ay_lp::LpError::ResourceLimit(_))
        ));
        let (end, written, text) = run(&mps, 100);
        assert_eq!(
            end,
            SparseEnd::Optimal,
            "{}",
            &text[text.len().saturating_sub(300)..]
        );
        assert!(written >= 1);
        let last_o = text.rfind("o ").expect("o line");
        assert!(text[last_o..].starts_with("o 1\n"));
    }

    #[test]
    fn test_sparse_route_reports_infeasible() {
        let mps = "NAME INF
ROWS
 N OBJ
 G LO
 L HI
COLUMNS
    M 'MARKER' 'INTORG'
    X OBJ 1 LO 2
    X HI 2
    M 'MARKER' 'INTEND'
RHS
    RHS LO 1 HI 1.5
BOUNDS
 UP BND X 10
ENDATA
";
        let (end, written, text) = run(mps, 30);
        assert_eq!(end, SparseEnd::Infeasible, "{text}");
        assert_eq!(written, 0);
    }

    /// Review finding (200554215): the engine read the file with its own MPS
    /// reader, which gives an integer column with no BOUNDS entry [0, +inf)
    /// where `ay-lp` (and the MIPLIB checker) give [0, 1]. The route now
    /// solves `ay-lp`'s model: the optimum is 1, not 5.
    #[test]
    fn test_sparse_route_solves_the_model_ay_lp_read() {
        let mps = "NAME DEFAULTBIN
OBJSENSE
    MAX
ROWS
 N OBJ
 L C1
COLUMNS
    M 'MARKER' 'INTORG'
    X OBJ 1 C1 1
    M 'MARKER' 'INTEND'
RHS
    RHS C1 5
ENDATA
";
        let exact = ay_lp::parse_mps_exact(mps).expect("parse");
        let milp = engine_model(&exact).expect("model");
        assert_eq!(milp.col_names, vec!["X".to_string()]);
        let (end, _, text) = run(mps, 30);
        assert_eq!(end, SparseEnd::Optimal, "{text}");
        assert!(
            text.contains("o 1\nv X = 1\nc solution end 1\nc optimal: "),
            "{text}"
        );
    }

    /// RANGES, an objective constant and an extra `N` row: the route's
    /// optimum is the one of `ay-lp`'s reading, which the dense route also
    /// finds. min x + 2y + 3 (RHS -3 on the objective row), x, y integer in
    /// [0, 10], 4 <= x + y <= 6 (G row with range 2), x <= 3: optimum
    /// x = 3, y = 1, 3 + 2 + 3 = 8.
    #[test]
    fn test_sparse_route_reads_ranges_offset_and_free_rows_as_ay_lp() {
        let mps = "NAME RNG
ROWS
 N OBJ
 N FREE
 G SUM
 L CAP
COLUMNS
    M 'MARKER' 'INTORG'
    X OBJ 1 SUM 1
    X CAP 1 FREE 7
    Y OBJ 2 SUM 1
    M 'MARKER' 'INTEND'
RHS
    RHS OBJ -3 SUM 4
    RHS CAP 3
RANGES
    RNG SUM 2
BOUNDS
 UP BND X 10
 UP BND Y 10
ENDATA
";
        let problem = ay_lp::parse_mps(mps).expect("parse");
        let dense = ay_lp::solve(&problem).expect("dense optimum");
        assert!((dense.objective - 8.0).abs() < 1e-9);
        let (end, _, text) = run(mps, 30);
        assert_eq!(end, SparseEnd::Optimal, "{text}");
        assert!(
            text.contains("o 8\nv X = 3\nv Y = 1\nc solution end 2\nc optimal: "),
            "{text}"
        );
    }

    #[test]
    fn test_improves_follows_sense() {
        let n = |v: i64| BigRational::from_integer(v.into());
        assert!(improves(Sense::Min, None, &n(5)));
        assert!(improves(Sense::Min, Some(&n(6)), &n(5)));
        assert!(!improves(Sense::Min, Some(&n(5)), &n(5)));
        assert!(improves(Sense::Max, Some(&n(5)), &n(6)));
        assert!(!improves(Sense::Max, Some(&n(6)), &n(5)));
    }
}
