// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordered lowering from solve-command flags to [`SolveOpts`].

use std::time::Duration;

use ay_milp::SolveOpts;

use super::{engine_flags, flag_or_env, Flags, Require};

/// Apply the solve command's evidence, resource, and determinism policy.
///
/// The order is observable when more than one value is malformed, and when
/// `--threads` disables determinism before an explicit determinism flag restores
/// or disables it. Keep that order aligned with the CLI contract.
pub(super) fn from_flags(
    flags: &Flags,
    require: Require,
    seconds: f64,
) -> Result<SolveOpts, String> {
    let mut opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(seconds));
    if require == Require::Full {
        opts = opts.with_require_certificates(true);
    }
    opts = engine_flags::apply(flags, opts)?;

    let tree_cert_leaves = flags.get("tree-cert-leaves").cloned();
    if let Some(value) = &tree_cert_leaves {
        opts = opts.with_tree_cert_leaves(
            value
                .parse::<usize>()
                .map_err(|_| "--tree-cert-leaves needs an integer".to_owned())?,
        );
    }

    // A tree certificate with no consumer is not bought. The artifact costs a
    // whole re-solve; `--no-emit-cert` used to pay that cost and discard it.
    // Measured across eight infeasible instances this saved 12.7% overall and
    // 2.93x on neos859080. Full-evidence posture and an explicit leaf budget
    // still buy the proof because those callers requested checkable evidence.
    if flags.has("no-emit-cert") && require != Require::Full && tree_cert_leaves.is_none() {
        opts = opts.with_tree_cert_leaves(0);
    }
    if let Some(value) = flag_or_env(flags, "threads", "AY_MILP_THREADS") {
        match value.parse::<u32>() {
            Ok(threads) if threads > 1 => {
                opts = opts.with_threads(threads).with_determinism(false);
            }
            Ok(_) => {}
            Err(_) => return Err("--threads needs an integer".to_owned()),
        }
    }
    if let Some(value) = flags.get("seed") {
        opts = opts.with_seed(
            value
                .parse::<u64>()
                .map_err(|_| "--seed needs an integer".to_owned())?,
        );
    }
    if flags.has("deterministic") {
        opts = opts.with_determinism(true);
    }
    if flags.has("no-deterministic") {
        opts = opts.with_determinism(false);
    }

    // The retired AY_MILP_OPEN_BYTES alias is deliberately not consulted.
    if let Some(value) = flags.get("memory-budget") {
        opts = opts.with_memory_budget(Some(
            value
                .parse::<usize>()
                .map_err(|_| "--memory-budget needs an integer".to_owned())?,
        ));
    }
    Ok(opts)
}
