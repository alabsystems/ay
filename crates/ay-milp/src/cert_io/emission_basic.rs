// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Build a dual claim from the replay ledger, or `NONE`.
pub(super) fn dual_claim_from_replay(ctx: &EmitCtx<'_>, wanted: &[&str]) -> EmittedClaim {
    if let Some(rc) = ctx
        .replay_claims
        .iter()
        .find(|r| wanted.contains(&r.claim.as_str()))
    {
        EmittedClaim {
            name: "dual",
            kind: EvidenceKind::Replay,
            source: Some(rc.claim.clone()),
        }
    } else {
        EmittedClaim {
            name: "dual",
            kind: EvidenceKind::None,
            source: None,
        }
    }
}

pub(super) fn infeasible_claim_from_replay(ctx: &EmitCtx<'_>) -> EmittedClaim {
    if let Some(rc) = ctx.replay_claims.iter().find(|r| {
        r.claim == "feasibility-face-empty"
            || r.claim == "coset-inconsistent"
            || r.claim == "sat-relu-cnf-unsat"
            || r.claim == "direct-cnf-unsat"
            || r.claim == "pb-projection-infeasible"
            || r.claim == "pb-portfolio-projection-infeasible"
            || r.claim == "network-design-projection-infeasible"
            || r.claim == "open-domain-projection-infeasible"
            || r.claim == "hybrid-pb-lp-infeasible"
    }) {
        EmittedClaim {
            name: "infeasible",
            kind: EvidenceKind::Replay,
            source: Some(rc.claim.clone()),
        }
    } else {
        EmittedClaim {
            name: "infeasible",
            kind: EvidenceKind::None,
            source: None,
        }
    }
}

/// Whether an optimality certificate is the exact empty-multiplier bound for
/// an identically-zero variable objective. The marker is diagnostic only: with
/// a separately verified feasible point, this bound proves the optimum.
pub(super) fn is_trivial_optcert(oc: &OptimalityCertificate) -> bool {
    oc.bound.is_zero() && oc.objective.iter().all(|(_, a)| a.is_zero())
}

pub(super) fn unknown_reason_line(r: &UnknownReason) -> String {
    match r {
        UnknownReason::Timeout => "timeout".into(),
        UnknownReason::Interrupted => "interrupted".into(),
        UnknownReason::IterationLimit => "iteration-limit".into(),
        UnknownReason::MemoryLimit => "memory-limit".into(),
        UnknownReason::CertificateUnavailable => "certificate-unavailable".into(),
        UnknownReason::SolverIncomplete { detail } => {
            format!("solver-incomplete detail={}", sanitize(detail))
        }
        // The one reason that means the SOLVER IS WRONG. Never swallowed.
        UnknownReason::WitnessRejected { detail } => {
            format!("witness-rejected detail={}", sanitize(detail))
        }
    }
}

/// Collapse anything that could forge a record boundary.
pub(super) fn sanitize(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_control() { ' ' } else { c })
        .collect::<String>()
        .trim()
        .to_string()
}

pub(super) fn witness_block(ctx: &EmitCtx<'_>, values: &[BigRational]) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "witness cols={}", values.len());
    for (j, v) in values.iter().enumerate() {
        let name = ctx.col_names.get(j).map_or("-", String::as_str);
        let _ = writeln!(s, "x {j} {name} {}", fmt_rat(v));
    }
    let _ = writeln!(s, "end");
    s
}

pub(super) fn write_multipliers(s: &mut String, mults: &[Multiplier]) {
    for m in mults {
        match m.fact {
            FactRef::RowBound { row, side } => {
                let _ = writeln!(
                    s,
                    "mult row {} {} {}",
                    row.index(),
                    side_token(side),
                    fmt_rat(&m.coeff)
                );
            }
            FactRef::ColBound { col, side } => {
                let _ = writeln!(
                    s,
                    "mult col {} {} {}",
                    col.index(),
                    side_token(side),
                    fmt_rat(&m.coeff)
                );
            }
        }
    }
}

pub(super) fn farkas_block(fc: &FarkasCertificate) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "farkas mults={}", fc.multipliers.len());
    write_multipliers(&mut s, &fc.multipliers);
    let _ = writeln!(s, "end");
    s
}

pub(super) fn optcert_block(oc: &OptimalityCertificate, trivial: bool) -> String {
    let mut s = String::new();
    let _ = writeln!(
        s,
        "optcert sense={} bound={} frame=model trivial={}",
        sense_token(oc.sense),
        fmt_rat(&oc.bound),
        u8::from(trivial)
    );
    // The certificate names its OWN objective: `tighten_col_bounds` produces
    // certificates over per-column objectives, and a checker that assumed the
    // model's objective would bless a bound on a different function.
    for (c, a) in &oc.objective {
        let _ = writeln!(s, "obj {c} {}", fmt_rat(a));
    }
    write_multipliers(&mut s, &oc.multipliers);
    let _ = writeln!(s, "end");
    s
}

/// The `rootdual` block: a bound on the model's optimum that is NOT a proof of
/// it, written so that the part it leaves unproved is a field of the record.
///
/// Same shape as [`optcert_block`] — a bound, the objective it bounds, and the
/// multipliers — plus one field `optcert` does not have and must not have:
/// `gap`, the residual between this bound and the value the verdict line
/// claims. `optcert` under the `dual` claim asserts that its bound IS the
/// optimum, so a residual there would be a contradiction; a `rootdual` asserts
/// only that the optimum is no better than `bound`, so the distance still to be
/// closed is the single most important thing a reader needs and it is written
/// down rather than left to be inferred.
///
/// `gap` is REDUNDANT BY CONSTRUCTION — it is a function of `bound`, the
/// model's offset and the verdict line — and that is exactly why it is safe to
/// write: the checker RE-DERIVES it and refuses the block if the two disagree,
/// so an emitter cannot understate its own residual. Everything load-bearing
/// still has exactly one source.
pub(super) fn root_dual_block(oc: &OptimalityCertificate, gap: &BigRational) -> String {
    let mut s = String::new();
    let _ = writeln!(
        s,
        "rootdual sense={} bound={} gap={} frame=model",
        sense_token(oc.sense),
        fmt_rat(&oc.bound),
        fmt_rat(gap)
    );
    for (c, a) in &oc.objective {
        let _ = writeln!(s, "obj {c} {}", fmt_rat(a));
    }
    write_multipliers(&mut s, &oc.multipliers);
    let _ = writeln!(s, "end");
    s
}

/// The `opttree` block: a whole-tree OPTIMALITY certificate's DUAL half.
///
/// The witness rides in the certificate's own `witness` block (the `primal`
/// claim), and the target value rides on the `verdict` line — so this block
/// carries the split skeleton and the leaf multipliers and NOTHING ELSE. In
/// particular a `boundleaf` writes no bound: recording one would create a
/// second number that could disagree with the verdict, which is precisely the
/// forgery the design review named.
pub(super) fn opt_tree_block(root: &OptTreeNode) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "opttree");
    // Explicit pre-order, iterative: a certificate is input data and its depth
    // must not be the writer's stack limit.
    let mut stack: Vec<&OptTreeNode> = vec![root];
    while let Some(node) = stack.pop() {
        match node {
            OptTreeNode::Split { col, cut, lo, hi } => {
                let _ = writeln!(s, "split {} {}", col.index(), fmt_rat(cut));
                stack.push(hi);
                stack.push(lo);
            }
            OptTreeNode::Empty { farkas } => {
                let _ = writeln!(s, "leaf");
                write_multipliers(&mut s, &farkas.multipliers);
                let _ = writeln!(s, "endleaf");
            }
            OptTreeNode::Dominated { multipliers } => {
                let _ = writeln!(s, "boundleaf");
                write_multipliers(&mut s, multipliers);
                let _ = writeln!(s, "endleaf");
            }
        }
    }
    let _ = writeln!(s, "end");
    s
}

pub(super) fn tree_block(tc: &MilpInfeasibilityCertificate) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "tree");
    write_tree_body(&mut s, tc, "end");
    s
}

pub(super) fn write_tree_body(s: &mut String, tc: &MilpInfeasibilityCertificate, terminator: &str) {
    // Explicit pre-order. `split` consumes exactly two following nodes (lo then
    // hi); `leaf` runs to its `endleaf`. Written iteratively — a certificate is
    // input data and its depth must not be the writer's stack limit.
    let mut stack: Vec<&TreeNode> = vec![&tc.root];
    while let Some(node) = stack.pop() {
        match node {
            TreeNode::Split { col, cut, lo, hi } => {
                let _ = writeln!(s, "split {} {}", col.index(), fmt_rat(cut));
                stack.push(hi);
                stack.push(lo);
            }
            TreeNode::Leaf { farkas } => {
                let _ = writeln!(s, "leaf");
                write_multipliers(s, &farkas.multipliers);
                let _ = writeln!(s, "endleaf");
            }
        }
    }
    let _ = writeln!(s, "{terminator}");
}
