// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native tree dispatch and post-verdict evidence enrichment.

use super::super::*;

pub(super) struct Request<'prefix, 'target, 'margin_ref, 'proof_model> {
    pub(super) shared_binary_prefix: &'prefix [Col],
    pub(super) proof_first_workers: Option<NonZeroUsize>,
    pub(super) target_fsb_prefix: Option<crate::bab::TargetFsbPrefixRequest<'target>>,
    pub(super) margin_proof_target:
        Option<&'margin_ref crate::margin::MarginProofTarget<'proof_model>>,
}

#[derive(Clone, Copy)]
enum AuthorityWindow {
    Caller,
    FirstRefusal,
}

struct AnchorPlan {
    opts: SolveOpts,
    window: AuthorityWindow,
}

impl AnchorPlan {
    fn certificate_budget(&self, model: &Model) -> Budget {
        let mut budget = cert_budget_native(model, &self.opts);
        if matches!(self.window, AuthorityWindow::FirstRefusal) {
            budget.deadline = match (budget.deadline, self.opts.deadline) {
                (Some(enrichment), Some(refusal)) => Some(enrichment.min(refusal)),
                (None, refusal) => refusal,
                (enrichment, None) => enrichment,
            };
        }
        budget
    }
}

pub(super) fn solve(
    session: &mut BabSession,
    state: &CheckState,
    request: Request<'_, '_, '_, '_>,
) -> Result<Outcome, MilpError> {
    let plan = anchor_plan(session);
    let mut raw = run_tree(session, &request, &plan.opts)?;
    session.capture_affine_certificate(&raw);
    capture_parity_certificate(session, &raw);
    #[cfg(feature = "smt")]
    maybe_run_smt_fallback(
        session,
        state,
        request.shared_binary_prefix,
        &plan.opts,
        &mut raw,
    )?;
    let raw = normalize_feasibility_answer(raw, state);
    Ok(enrich_bare_infeasibility(session, &plan, raw))
}

fn anchor_plan(session: &BabSession) -> AnchorPlan {
    let Some(deferred) = &session.deferred_claim else {
        return AnchorPlan {
            opts: session.opts.clone(),
            window: AuthorityWindow::Caller,
        };
    };
    let mut tightened = session.opts.clone();
    tightened.deadline = Some(deferred.first_refusal.until);
    AnchorPlan {
        opts: tightened,
        window: AuthorityWindow::FirstRefusal,
    }
}

fn run_tree(
    session: &BabSession,
    request: &Request<'_, '_, '_, '_>,
    opts: &SolveOpts,
) -> Result<Outcome, MilpError> {
    if let Some(seed) = session.incumbent_seed.as_deref() {
        return Ok(crate::bab::solve_milp_seeded(
            &session.model,
            opts,
            seed,
            &session.branch_hints,
            &session.root_strong_branch_shortlist,
        ));
    }
    if !request.shared_binary_prefix.is_empty() || request.margin_proof_target.is_some() {
        return run_partitioned_tree(session, request, opts);
    }
    if session.branch_hints.is_empty() && session.root_strong_branch_shortlist.is_empty() {
        Ok(crate::bab::solve_milp(&session.model, opts))
    } else {
        Ok(crate::bab::solve_milp_advised(
            &session.model,
            opts,
            &session.branch_hints,
            &session.root_strong_branch_shortlist,
        ))
    }
}

fn run_partitioned_tree(
    session: &BabSession,
    request: &Request<'_, '_, '_, '_>,
    opts: &SolveOpts,
) -> Result<Outcome, MilpError> {
    match (request.proof_first_workers, request.margin_proof_target) {
        (Some(workers), None) => Ok(crate::bab::solve_milp_shared_binary_prefix_proof_first(
            &session.model,
            opts,
            request.shared_binary_prefix,
            workers,
            &session.branch_hints,
            &session.root_strong_branch_shortlist,
        )),
        (None, Some(target)) => Ok(crate::bab::solve_milp_margin_proof(
            &session.model,
            opts,
            request.shared_binary_prefix,
            target,
            &session.branch_hints,
            &session.root_strong_branch_shortlist,
            request.target_fsb_prefix,
        )),
        (None, None) => Ok(crate::bab::solve_milp_shared_binary_prefix(
            &session.model,
            opts,
            request.shared_binary_prefix,
            &session.branch_hints,
            &session.root_strong_branch_shortlist,
        )),
        (Some(_), Some(_)) => Err(MilpError::Session {
            message: "marked-margin proof target does not compose with proof-first prefix workers"
                .to_owned(),
        }),
    }
}

fn capture_parity_certificate(session: &mut BabSession, raw: &Outcome) {
    let Some(certificate) = crate::parity::take_pending_infeasibility_certificate() else {
        return;
    };
    if raw.is_infeasible()
        && crate::verify_parity_infeasibility_certificate(&session.model, &certificate).is_ok()
    {
        session.parity_infeasibility_certificate = Some(certificate);
    }
}

#[cfg(feature = "smt")]
fn maybe_run_smt_fallback(
    session: &BabSession,
    state: &CheckState,
    shared_binary_prefix: &[Col],
    opts: &SolveOpts,
    raw: &mut Outcome,
) -> Result<(), MilpError> {
    if !shared_binary_prefix.is_empty()
        || !(raw.is_unknown() || matches!(raw, Outcome::Bound { .. }))
        || deadline_expired(opts)
        || !session.smt_fallback_within_reach_for(opts)
    {
        return Ok(());
    }
    let held_bound = match raw {
        Outcome::Bound {
            dual_bound,
            rigorous,
        } => Some((dual_bound.clone(), *rigorous)),
        _ => None,
    };
    let mut smt = crate::smt::SmtMilp::new(&session.model, opts)?;
    *raw = if state.has_objective {
        smt.optimize(
            &session.model,
            opts,
            &state.objective,
            session.model.sense(),
        )?
    } else {
        smt.check_feasible(opts)?
    };
    if let (true, Some((dual_bound, rigorous))) = (raw.is_unknown(), held_bound) {
        *raw = Outcome::Bound {
            dual_bound,
            rigorous,
        };
    }
    Ok(())
}

fn normalize_feasibility_answer(raw: Outcome, state: &CheckState) -> Outcome {
    if state.has_objective {
        return raw;
    }
    match raw {
        Outcome::Optimal { model_values, .. } => Outcome::Feasible {
            model_values,
            incumbent_only: false,
            dual_bound: None,
        },
        other => other,
    }
}

fn enrich_bare_infeasibility(session: &BabSession, plan: &AnchorPlan, raw: Outcome) -> Outcome {
    match raw {
        Outcome::Infeasible {
            cert: None,
            tree_cert: None,
        } if session.parity_infeasibility_certificate.is_none()
            && !session.affine_infeasibility_verified() =>
        {
            derive_root_farkas(session, plan).map_or(
                Outcome::Infeasible {
                    cert: None,
                    tree_cert: None,
                },
                |cert| Outcome::Infeasible {
                    cert: Some(cert),
                    tree_cert: None,
                },
            )
        }
        other => other,
    }
}

fn derive_root_farkas(session: &BabSession, plan: &AnchorPlan) -> Option<FarkasCertificate> {
    let budget = plan.certificate_budget(&session.model);
    if let Some(cert) = crate::tree_cert::root_float_farkas(&session.model, budget.deadline) {
        return Some(cert);
    }
    let mut lp = ExactLp::new(&session.model);
    match lp.make_feasible(&budget) {
        LpFeasibility::Infeasible(cert) => Some(cert),
        _ => None,
    }
}

#[cfg(feature = "smt")]
pub(super) fn solve_smt(
    session: &mut BabSession,
    state: &CheckState,
) -> Result<Outcome, MilpError> {
    let MilpLane::Smt(smt) = &mut session.lane else {
        unreachable!("lane kind changed during one check")
    };
    let raw = if state.has_objective {
        let raw = smt.optimize(
            &session.model,
            &session.opts,
            &state.objective,
            session.model.sense(),
        )?;
        add_objective_offset(&session.model, raw)
    } else {
        smt.check_feasible(&session.opts)?
    };
    Ok(enrich_smt_infeasibility(&session.model, &session.opts, raw))
}

#[cfg(feature = "smt")]
fn add_objective_offset(model: &Model, raw: Outcome) -> Outcome {
    match raw {
        Outcome::Optimal {
            value,
            model_values,
            cert,
        } => Outcome::Optimal {
            value: value + model.obj_offset_exact(),
            model_values,
            cert,
        },
        other => other,
    }
}

#[cfg(feature = "smt")]
fn enrich_smt_infeasibility(model: &Model, opts: &SolveOpts, raw: Outcome) -> Outcome {
    let Outcome::Infeasible {
        cert: None,
        tree_cert: None,
    } = raw
    else {
        return raw;
    };
    let budget = cert_budget_for(model, opts);
    let cert = crate::tree_cert::root_float_farkas(model, budget.deadline).or_else(|| {
        let mut lp = ExactLp::new(model);
        match lp.make_feasible(&budget) {
            LpFeasibility::Infeasible(cert) => {
                debug_assert!(cert.verify(model).is_ok());
                Some(cert)
            }
            _ => None,
        }
    });
    cert.map_or(
        Outcome::Infeasible {
            cert: None,
            tree_cert: None,
        },
        |cert| Outcome::Infeasible {
            cert: Some(cert),
            tree_cert: None,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_refusal_caps_post_tree_certificate_enrichment() {
        let mut model = Model::new();
        model.add_binary_col();
        let refusal = Instant::now() + Duration::from_millis(50);
        let mut opts = SolveOpts::new();
        opts.deadline = Some(refusal);
        opts.time_limit = None;
        let plan = AnchorPlan {
            opts,
            window: AuthorityWindow::FirstRefusal,
        };

        let budget = plan.certificate_budget(&model);
        assert!(budget.deadline.is_some_and(|deadline| deadline <= refusal));
    }
}
