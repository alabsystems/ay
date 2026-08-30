// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed command-line surface for the PB frontend.

use std::path::PathBuf;

use anyhow::{bail, Result};
use ay_pb::ab_switches::{self, PbAbSwitches};
use clap::{Args, Subcommand};

/// Hidden process-constant controls for the PB engine.
#[derive(Args, Default)]
pub(crate) struct PbAbSwitchesCli {
    /// Select the legacy synchronous proof path (the dense async tap is
    /// the default). B31: replaces `AY_PB_PROOF_TAP=legacy`.
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    proof_tap_legacy: bool,
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    no_pb_clique_coloring: bool,
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    no_pb_injcomp: bool,
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    no_pb_compact_cert: bool,
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    no_pb_restart_floor: bool,
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    no_pb_counting: bool,
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    no_pb_bnn_feas: bool,
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    no_pb_bnn_sched: bool,
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    no_pb_sls_nlc: bool,
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    no_pb_wbo_sls: bool,
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    no_pb_lns2: bool,
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    no_pb_symmetry_arm: bool,
    /// Opt in to the root EDAC/VAC-lite WCSP probe (B56).
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    pb_wcsp_edac: bool,
    /// Parallel-portfolio worker policy: 0 = sequential, N = N workers;
    /// omit for the auto default (B57).
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    pb_parallel: Option<u16>,
    /// Two-club node cap override (B74).
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    pb_two_club_max_nodes: Option<u64>,
    /// Two-club branch-rule selector (B74).
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    pb_two_club_branch: Option<String>,
    /// Two-club search tracing (B74).
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    pb_two_club_trace: bool,
    /// Two-club frontier dump (B74).
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    pb_two_club_dump_frontier: bool,
    /// PB certificate diagnostics: which OPT-LIN rung ran, what slice of the
    /// certification budget it was given, and how long it took.
    ///
    /// THE CARRIER GAP THIS CLOSES. `MiscCliFlags::cert_debug` has existed for
    /// a while and `crates/ay/src/cmd_pb.rs` and
    /// `crates/ay-pb-core/src/proof/cert.rs` are full of `if
    /// misc_cli_flags().cert_debug` diagnostics — but the flag was only ever
    /// parsed by `ay solve`, never by `ay pb solve`. So on the PB path every
    /// one of those sites was dead code and the certificate chain's own
    /// scheduling could not be observed from the shipped binary at all. That is
    /// exactly the observation this track needed: the per-route budget defect
    /// is invisible to code review and only a measured slice settles it.
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    cert_debug: bool,
}

impl PbAbSwitchesCli {
    pub(super) fn proof_tap_legacy(&self) -> bool {
        self.proof_tap_legacy
    }

    fn cert_debug(&self) -> bool {
        self.cert_debug
    }

    fn requested(&self) -> PbAbSwitches {
        PbAbSwitches {
            clique_coloring: !self.no_pb_clique_coloring,
            injcomp: !self.no_pb_injcomp,
            compact_cert: !self.no_pb_compact_cert,
            restart_floor: !self.no_pb_restart_floor,
            counting: !self.no_pb_counting,
            bnn_feas: !self.no_pb_bnn_feas,
            bnn_sched: !self.no_pb_bnn_sched,
            sls_nlc: !self.no_pb_sls_nlc,
            wbo_sls: !self.no_pb_wbo_sls,
            lns2: !self.no_pb_lns2,
            symmetry_arm: !self.no_pb_symmetry_arm,
            wcsp_edac: self.pb_wcsp_edac,
            parallel_workers: self.pb_parallel,
            two_club_max_nodes: self.pb_two_club_max_nodes,
            two_club_branch: self
                .pb_two_club_branch
                .clone()
                .map(|s| &*Box::leak(s.into_boxed_str())),
            two_club_trace: self.pb_two_club_trace,
            two_club_dump_frontier: self.pb_two_club_dump_frontier,
        }
    }
}

/// PB solver subcommands.
#[derive(Subcommand)]
pub(crate) enum PbCommand {
    /// Solve an OPB or WBO pseudo-Boolean instance.
    Solve {
        /// Input file in OPB or WBO format.
        file: PathBuf,

        /// Timeout in milliseconds.
        #[arg(short = 't', long, value_name = "MS")]
        timeout: Option<u64>,

        /// Write VeriPB proof to file.
        #[arg(long, value_name = "FILE")]
        proof: Option<PathBuf>,

        /// Print PB-specific comments before the result.
        #[arg(long)]
        stats: bool,

        /// Print shared stats envelope as JSON to stderr.
        #[arg(long)]
        stats_json: bool,

        /// INTERNAL benchmarking override: force the native PB CDCL engine and
        /// bypass automatic engine selection. Not a normal solving option — the
        /// solver already picks the best engine per instance automatically
        /// (`portfolio::select_strategy`). Kept hidden for A/B measurement
        /// (development sweep tooling) and tests only.
        #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
        native: bool,

        /// A/B measurement switches (hidden; every default is the shipped
        /// engine — see `ay_pb::ab_switches`). B14/B31: these replace the
        /// retired `AY_PB_*` env vars.
        #[command(flatten)]
        ab_switches: PbAbSwitchesCli,
    },
}

impl PbCommand {
    fn requested_ab_switches(&self) -> PbAbSwitches {
        match self {
            Self::Solve { ab_switches, .. } => ab_switches.requested(),
        }
    }

    fn cert_debug(&self) -> bool {
        match self {
            Self::Solve { ab_switches, .. } => ab_switches.cert_debug(),
        }
    }

    /// Install this command's process-constant A/B switches before solving.
    pub(super) fn install_ab_switches(&self) -> Result<()> {
        // Diagnostics carrier, not an engine switch. INSTALL WITHOUT READING
        // FIRST: `misc_cli_flags()` initialises the set-once global as a side
        // effect of reading it, so an `if !misc_cli_flags().cert_debug` guard
        // burns the cell with the default and makes the install that follows a
        // silent no-op. (Measured: the first cut of this flag parsed fine and
        // printed nothing.) A failed set — another command already installed
        // flags in-process — is not an error here; the flag only decides
        // whether comments are printed.
        if self.cert_debug() {
            let _ = ay_core::set_global_misc_cli_flags_with(|flags| {
                flags.cert_debug = true;
            });
        }
        // A thread-scoped test override IS the resolution: reads route
        // through it, and the set-once global must not be burned (or
        // compared) on a per-test request.
        if ab_switches::consumer_test_override::active() {
            return Ok(());
        }
        let requested = self.requested_ab_switches();

        if ab_switches::set(requested).is_ok() {
            return Ok(());
        }
        validate_reinstall(requested, ab_switches::get())
    }
}

#[cfg(test)]
mod tests {
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
}

fn validate_reinstall(requested: PbAbSwitches, installed: PbAbSwitches) -> Result<()> {
    if installed == requested {
        return Ok(());
    }
    bail!(
        "PB A/B switches already installed as {installed:?}; \
             refusing different request {requested:?}"
    )
}
