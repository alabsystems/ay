// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `margin` to preserve public diagnostic paths.

/// Diagnostic: build the margin reframe for `model` and report the reframed
/// dual bound next to the trivial-0 zero-objective bound, plus the mapped
/// verdict. Mirrors [`crate::diag_float_lp`]; used by the `mps_solve` example
/// under the margin-row demo flag.
///
/// Runs under the DEFAULT engine profile. Every caller that has parsed engine
/// flags wants [`diag_margin_reframe_with`] instead — see its note.
#[must_use]
pub fn diag_margin_reframe(model: &Model, secs: f64) -> String {
    diag_margin_reframe_with(model, secs, &SolveOpts::new())
}

/// [`diag_margin_reframe`] under a caller's own [`SolveOpts`] — the variant a
/// flagged harness or CLI lane calls.
///
/// WHY IT EXISTS (the same dead-flag family as [`crate::diag_float_lp_with`]).
/// Three separate reads on this path resolve through `tune`'s CALLER layer and
/// none of them could see a flag before this variant existed:
///
/// * `reframe_disabled` (`--no-margin-reframe`), the module's whole kill
///   switch, read by `prepare`/`prepare_auto` BEFORE any session exists;
/// * `auto_margin_row`'s arming knob (`--auto-margin`);
/// * every pricing knob the root LP walk reads, since the "before" number came
///   from the zero-opts [`crate::diag_float_lp`].
///
/// The old body did build a `SolveOpts` for the nested `reframe` — but a
/// THROWAWAY `SolveOpts::new()` with only a time limit, so the caller's flags
/// were shadowed one line before the only place they could have mattered. That
/// is the same one-line shadow `diag cross-check` and `diag profile` carried.
///
/// MEASURED, release binary + `target-cpu=native`,
/// `ay-milp diag margin-row benchmarks/milp-ny/safenlp/safenlp_ruarobot_1181_feas.mps 30 --row last`:
///
/// | flag | tail of the line |
/// |---|---|
/// | `--no-margin-reframe` | `reframed_solve=DECLINED reframed_bound=- decided=false => original=plain-feasibility`, 3/3 repeats |
/// | (none) | `reframed_solve=FEASIBLE_UNDECIDED … => original=UNKNOWN`, 5/5 repeats |
///
/// Two independent controls on two different reads. `--no-margin-reframe` is the
/// module kill switch, read BEFORE any session exists, so it proves the
/// `activate_caller` frame; it flips a CATEGORICAL field and is exactly
/// reproducible.
///
/// `--devex` is the second, and it needs a caveat that is the whole reason it is
/// written down: **`reframed_bound` is an ANYTIME number on this model** — the
/// reframed search does not terminate inside the budget (`FEASIBLE_UNDECIDED`),
/// so the digits move run to run and a single before/after pair would be
/// meaningless. Five repeats of each arm, release binary, 30 s budget:
///
/// ```text
/// (none)    -0.016926  -0.022446  -0.024704  -0.027859  -0.110415
/// --devex   +0.146599  +0.146471  +0.146367  +0.145837  +0.149808
/// ```
///
/// The two ranges do not overlap and do not even share a sign, so the flag
/// reaches the nested `BabSession` — but quote the RANGES, never one pair.
///
/// `--row last` on the `_margin` sibling model is a bad control bed — its last
/// row is two-sided, so `mark_margin_row` refuses before the diagnostic is ever
/// reached.
#[must_use]
pub fn diag_margin_reframe_with(model: &Model, secs: f64, opts: &SolveOpts) -> String {
    let _tuned = crate::tune::activate_caller(opts.engine().profile());
    use num_traits::ToPrimitive;
    let Some(row) = model.margin_row() else {
        return "diag_margin_reframe: no margin row marked (call mark_margin_row)".to_owned();
    };
    // Root LP bound of the zero objective (the "before"): always the trivial 0.
    // Root LP bound of the reframe (the "after"): the meaningful margin bound.
    let ridx = row.index();
    let (_c, lb, ub) = model.row(row);
    let sense = match (lb.is_finite(), ub.is_finite()) {
        (false, true) => Sense::Minimize,
        (true, false) => Sense::Maximize,
        _ => return "diag_margin_reframe: margin row is not one-sided".to_owned(),
    };
    let threshold = match sense {
        Sense::Minimize => model.row_ub_exact(ridx, ub),
        Sense::Maximize => model.row_lb_exact(ridx, lb),
    };
    let reframed_model = build_reframed(model, row, sense);

    // The reframed root LP relaxation optimum (float lane, min-form): the
    // rigorous dual bound the search's own pruning reads. This is the "dual
    // bound comes alive" number — nonzero and informative where the zero
    // objective's is the trivial 0. Extracted from the shared `diag_float_lp`
    // so it measures exactly the engine's root LP.
    //
    // THE STATUS TRAVELS WITH THE NUMBER. This field used to take
    // `obj(min-form)` and drop `status` on the floor, so a walk that hit the
    // budget printed wherever the clock fell under the name "root LP bound" —
    // the scaffold's signature failure mode, inherited here because this
    // function CONSUMES its line. A truncated walk's objective is not a bound
    // in either direction, so the reader needs the status in the same breath.
    let lp_budget = secs.min(15.0);
    let root_lp_line = crate::diag_float_lp_with(&reframed_model, lp_budget, opts);
    let field = |line: &str, key: &str| -> String {
        line.split(key)
            .nth(1)
            .and_then(|s| s.split_whitespace().next())
            .unwrap_or("?")
            .to_owned()
    };
    let root_lp_status = field(&root_lp_line, "status=");
    let root_lp = field(&root_lp_line, "obj(min-form)=");
    // Only a walk that TERMINATED reports a number here.
    let root_lp = if root_lp_status == "Optimal" {
        root_lp
    } else {
        format!("NOT-A-BOUND(walk {root_lp_status})")
    };

    // The full reframe + verdict map (what the session would return). The
    // caller's own opts, re-budgeted — NOT a fresh `SolveOpts::new()`, which is
    // the one-line shadow this `_with` variant exists to remove.
    let sub = opts
        .clone()
        .with_time_limit(std::time::Duration::from_secs_f64(secs.min(30.0)));
    let mapped = reframe(model, &sub);
    let (status, bound, decided, verdict) = match mapped {
        Some(r) => {
            let b = r.info.reframed_bound.as_ref().map_or_else(
                || "-".to_owned(),
                |v| {
                    v.to_f64()
                        .map_or_else(|| v.to_string(), |f| format!("{f:.6}"))
                },
            );
            (
                r.info.reframed_status,
                b,
                r.info.decided,
                verdict_tag(&r.verdict),
            )
        }
        None => ("DECLINED", "-".to_owned(), false, "plain-feasibility"),
    };
    let t = threshold.as_ref().map_or_else(
        || "?".to_owned(),
        |v| v.to_f64().map_or_else(|| v.to_string(), |f| format!("{f}")),
    );
    format!(
        "diag_margin_reframe: row={ridx} sense={sense:?} threshold={t} \
         zero_obj_root_bound=0 reframed_root_LP_bound={root_lp} \
         reframed_root_LP_walk={root_lp_status} \
         reframed_solve={status} reframed_bound={bound} decided={decided} => original={verdict}"
    )
}

/// A one-word tag for an outcome (diagnostics).
fn verdict_tag(o: &Outcome) -> &'static str {
    match o {
        Outcome::Optimal { .. } => "OPTIMAL",
        Outcome::Feasible { .. } => "FEASIBLE",
        Outcome::Infeasible { .. } => "INFEASIBLE",
        Outcome::Unbounded => "UNBOUNDED",
        Outcome::Bound { .. } => "BOUND",
        Outcome::Unknown { .. } => "UNKNOWN",
    }
}
