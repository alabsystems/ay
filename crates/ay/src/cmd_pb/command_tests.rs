// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use clap::Parser;

#[derive(Parser)]
struct TestCli {
    #[command(subcommand)]
    command: PbCommand,
}

#[test]
fn hidden_disable_flags_parse_and_invert_once() {
    let parsed = TestCli::try_parse_from([
        "test",
        "solve",
        "input.opb",
        "--proof-tap-legacy",
        "--no-pb-clique-coloring",
        "--no-pb-injcomp",
        "--no-pb-compact-cert",
        "--no-pb-restart-floor",
        "--no-pb-counting",
        "--no-pb-bnn-feas",
        "--no-pb-bnn-sched",
        "--no-pb-sls-nlc",
        "--no-pb-wbo-sls",
        "--no-pb-lns2",
        "--no-pb-symmetry-arm",
    ])
    .expect("hidden B14/B31 flags should parse");
    assert!(match &parsed.command {
        PbCommand::Solve { ab_switches, .. } => ab_switches.proof_tap_legacy(),
    });
    let requested = parsed.command.requested_ab_switches();
    assert_eq!(
        requested,
        PbAbSwitches {
            clique_coloring: false,
            injcomp: false,
            compact_cert: false,
            restart_floor: false,
            counting: false,
            bnn_feas: false,
            bnn_sched: false,
            sls_nlc: false,
            wbo_sls: false,
            lns2: false,
            symmetry_arm: false,
            wcsp_edac: false,
            parallel_workers: None,
            two_club_max_nodes: None,
            two_club_branch: None,
            two_club_trace: false,
            two_club_dump_frontier: false,
        }
    );
}

#[test]
fn default_installation_is_idempotent() {
    let parsed = TestCli::try_parse_from(["test", "solve", "input.opb"])
        .expect("default PB command should parse");
    parsed
        .command
        .install_ab_switches()
        .expect("first default installation should succeed");
    parsed
        .command
        .install_ab_switches()
        .expect("identical re-entry should succeed");
}

#[test]
fn reinstall_must_be_identical() {
    let shipped = PbAbSwitches::default();
    assert!(validate_reinstall(shipped, shipped).is_ok());

    let changed = PbAbSwitches {
        counting: false,
        ..shipped
    };
    assert!(validate_reinstall(changed, shipped).is_err());
}
