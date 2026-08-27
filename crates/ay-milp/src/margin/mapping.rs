// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `margin` to preserve mapping helper paths.

fn reframe_info(status: &'static str, bound: Option<BigRational>, decided: bool) -> ReframeInfo {
    ReframeInfo {
        reframed_status: status,
        reframed_bound: bound,
        decided,
    }
}

fn map_optimal(
    orig: &Model,
    row: Row,
    sense: Sense,
    threshold: &BigRational,
    value: BigRational,
    model_values: Vec<BigRational>,
    cert: Option<OptimalityCertificate>,
) -> Reframed {
    // `value` is the reframed optimum in the model frame (min c·x for a
    // `<=` row, max c·x for a `>=` row); the reframed offset is 0.
    let reaches = match sense {
        Sense::Minimize => value <= *threshold,
        Sense::Maximize => value >= *threshold,
    };
    if reaches {
        Reframed {
            verdict: Outcome::Feasible {
                model_values,
                incumbent_only: false,
                dual_bound: None,
            },
            info: reframe_info("OPTIMAL", Some(value), true),
        }
    } else {
        // Compose the reframed dual proof with the band bound into a Farkas for
        // the original model; verification remains at the shared finish gate.
        let farkas = cert
            .as_ref()
            .and_then(|certificate| margin_farkas(orig, row, sense, certificate));
        Reframed {
            verdict: Outcome::Infeasible {
                cert: farkas,
                tree_cert: None,
            },
            info: reframe_info("OPTIMAL", Some(value), true),
        }
    }
}

/// Map the reframed solve's outcome to the ORIGINAL feasibility verdict.
fn map_reframed(
    orig: &Model,
    row: Row,
    sense: Sense,
    threshold: &BigRational,
    reframed: Outcome,
) -> Reframed {
    match reframed {
        Outcome::Optimal {
            value,
            model_values,
            cert,
        } => map_optimal(orig, row, sense, threshold, value, model_values, cert),
        Outcome::Infeasible { cert, tree_cert } => {
            // Ordinarily this means `R` alone is infeasible, so the original
            // (a subset) is too and its witnesses transfer verbatim. The
            // explicit interrupted-margin path may instead have returned a
            // tree already derived against the original row. In either case,
            // keep only artifacts that independently re-verify in that
            // original frame.
            let cert = cert.filter(|c| c.verify(orig).is_ok());
            let tree_cert = tree_cert.filter(|c| c.verify(orig).is_ok());
            Reframed {
                verdict: Outcome::Infeasible { cert, tree_cert },
                info: reframe_info("INFEASIBLE", None, true),
            }
        }
        Outcome::Feasible {
            model_values,
            dual_bound,
            ..
        } => {
            // A timeout with an incumbent of `R`. If the incumbent also lands in
            // the band it settles the original FEASIBLE; otherwise we cannot
            // decide from an incumbent alone (the un-exported tree dual bound is
            // not independently checkable), so return the honest `Unknown` and
            // surface the reframed bound for the demo.
            if orig.check_point(&model_values).is_ok() {
                Reframed {
                    verdict: Outcome::Feasible {
                        model_values,
                        incumbent_only: false,
                        dual_bound: None,
                    },
                    info: reframe_info("FEASIBLE_INCUMBENT", dual_bound, true),
                }
            } else {
                Reframed {
                    verdict: Outcome::Unknown {
                        reason: UnknownReason::Timeout,
                    },
                    info: reframe_info("FEASIBLE_UNDECIDED", dual_bound, false),
                }
            }
        }
        Outcome::Unknown { reason } => Reframed {
            verdict: Outcome::Unknown { reason },
            info: reframe_info("UNKNOWN", None, false),
        },
        // `min c·x = -inf` (resp. `max = +inf`) means the band IS reachable, so
        // the original is FEASIBLE — but the reframed `Unbounded` carries no
        // witness ray to exhibit one. Decline; the caller's plain feasibility
        // solve produces a witnessed verdict.
        Outcome::Unbounded => Reframed {
            verdict: Outcome::Unknown {
                reason: UnknownReason::SolverIncomplete {
                    detail: "margin reframe unbounded; deferring to plain feasibility".to_owned(),
                },
            },
            info: reframe_info("UNBOUNDED", None, false),
        },
        // An interrupted tree's rigorous dual bound is not verdict authority
        // (it maps to `Unknown`, exactly as before), but it IS the number this
        // module exists to produce, and dropping it here was the reason a
        // consumer could not tell a reframe that ran out of wall one ulp from
        // the band from one that never left the root. Diagnostics only:
        // `ReframeInfo` reaches no verdict, no certificate, and no caller.
        Outcome::Bound { dual_bound, .. } => Reframed {
            verdict: Outcome::Unknown {
                reason: UnknownReason::Timeout,
            },
            info: reframe_info("BOUND", Some(dual_bound), false),
        },
    }
}
