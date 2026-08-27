// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to preserve private CLI item and test DefPaths.

/// Try the specialized MILP route before constructing the SMT executor.
///
/// A QF_LRA script that is exactly a big-M MILP feasibility problem —
/// conjunctive linear rows plus 0/1 disjunctions, the shape the downstream optimization consumer's mip-diff pipes
/// in — is decided by ay-milp's branch-and-cut instead of the generic DPLL(T)
/// case-split, which produces no verdict on real NN windows the MILP lane
/// settles in minutes. Fail-closed: anything outside the recognised fragment
/// falls through to the standard lane untouched.
///
/// The route is skipped when the caller asked for stats, visualization, an
/// EXPLICIT `--proof`, or a mandatory result gate — the fast path cannot
/// produce Alethe or route its verdict through those gates. Solver-synthesized
/// DEFAULT certificate configs do not block it: a fast-path `sat` needs no
/// certificate, and a fast-path `unsat` trades the best-effort default
/// certificate for a verdict the generic lane cannot reach at all on this
/// shape. The default-on DRAT/LRAT auto-check likewise does not disable this
/// SMT-only lane; an EXPLICIT `--verify-proof` is rejected by the caller because
/// AY has no Alethe post-checker.
fn try_smt_milp_fastpath(
    content: &str,
    stats_cfg: &stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    visualization: &Option<VisualizationFormat>,
) -> bool {
    let explicit_proof = proof_config.is_some_and(|p| !p.synthesized_default && !p.is_temp);
    !explicit_proof
        // These modes promise to inspect the executor's SAT/UNSAT result before
        // it reaches stdout. The standalone MILP lane prints its own verdict
        // and cannot provide those checks/certificates, so it must not bypass
        // the common result-gate path.
        && may_use_ungated_solver_route(ResultGateRequests::current())
        // Decision traces are produced by the SAT-backed executor. The MILP
        // fast path prints directly and cannot finalize the reserved trace.
        && ay_core::trace_config().decision_trace_path.is_none()
        && visualization.is_none()
        && !stats_cfg.human
        && !stats_cfg.json
        && crate::milp_fastpath::try_milp_fastpath(content)
}
