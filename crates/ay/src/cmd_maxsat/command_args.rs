// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Hidden engine switches shared by direct MaxSAT solves and benchmark
/// children. Keeping one carrier prevents the two MaxSAT command surfaces from
/// silently drifting apart.
#[derive(clap::Args, Debug, Default)]
struct MaxSatEngineFlags {
    /// Drop MaxSAT totalizer output equalities (B17).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_tot_eqs: bool,
    /// Keep the preprocessed engine after a mostly-risky BCE reduction (B17).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_bce_revert: bool,
    /// Restore the shared-only AM1 cover (B32).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_am1_maxcover: bool,
    /// Arm the opt-in one-shot BCE preprocessing lane (B32).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_bce: bool,
    /// Disable BMO stratified descent (B32).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_bmo: bool,
    /// Disable the cold-descent gate (B32).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_cold_descent: bool,
    /// Disable residual-descent reuse (B32).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_descent_residual: bool,
    /// Never select the DPW encoding (B32).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_dpw: bool,
    /// Disable the early stratified-descent slice (B32).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_early_descent: bool,
    /// Disable one-shot MaxSAT preprocessing (B32).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_preproc: bool,
    /// Disable the correct-by-default MILP race lane (B32).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_milp_race: bool,
}

impl MaxSatEngineFlags {
    /// Build the process-global carrier without mutating its singleton.
    fn misc_cli_flags(&self) -> ay_core::MiscCliFlags {
        ay_core::MiscCliFlags {
            maxsat_no_tot_eqs: self.maxsat_no_tot_eqs,
            maxsat_no_bce_revert: self.maxsat_no_bce_revert,
            maxsat_no_am1_maxcover: self.maxsat_no_am1_maxcover,
            maxsat_bce: self.maxsat_bce,
            maxsat_no_bmo: self.maxsat_no_bmo,
            maxsat_no_cold_descent: self.maxsat_no_cold_descent,
            maxsat_no_descent_residual: self.maxsat_no_descent_residual,
            maxsat_no_dpw: self.maxsat_no_dpw,
            maxsat_no_early_descent: self.maxsat_no_early_descent,
            maxsat_no_preproc: self.maxsat_no_preproc,
            maxsat_no_milp_race: self.maxsat_no_milp_race,
            ..ay_core::MiscCliFlags::default()
        }
    }

    /// Install direct-solve settings before constructing the MaxSAT engine.
    fn install_misc_cli_flags(&self) -> Result<()> {
        ay_core::set_global_misc_cli_flags(self.misc_cli_flags()).map_err(|_| {
            anyhow::anyhow!("MaxSAT engine switches were initialized before command dispatch")
        })
    }

    /// Spell active switches for an internal `ay maxsat solve` child.
    ///
    /// Parallel bench plans opt out of the solver's second MILP thread; a
    /// single-child plan retains the solver's correct-by-default race lane.
    fn solver_cli_args(&self, parallel_bench: bool) -> Vec<&'static str> {
        let mut args = Vec::new();
        let switches = [
            (self.maxsat_no_tot_eqs, "--maxsat-no-tot-eqs"),
            (self.maxsat_no_bce_revert, "--maxsat-no-bce-revert"),
            (self.maxsat_no_am1_maxcover, "--maxsat-no-am1-maxcover"),
            (self.maxsat_bce, "--maxsat-bce"),
            (self.maxsat_no_bmo, "--maxsat-no-bmo"),
            (self.maxsat_no_cold_descent, "--maxsat-no-cold-descent"),
            (
                self.maxsat_no_descent_residual,
                "--maxsat-no-descent-residual",
            ),
            (self.maxsat_no_dpw, "--maxsat-no-dpw"),
            (self.maxsat_no_early_descent, "--maxsat-no-early-descent"),
            (self.maxsat_no_preproc, "--maxsat-no-preproc"),
            (self.maxsat_no_milp_race, "--maxsat-no-milp-race"),
        ];
        args.extend(
            switches
                .into_iter()
                .filter_map(|(enabled, flag)| enabled.then_some(flag)),
        );
        if parallel_bench && !self.maxsat_no_milp_race {
            args.push("--maxsat-no-milp-race");
        }
        args
    }
}

/// Arguments for `ay maxsat solve`.
#[derive(clap::Args)]
pub(crate) struct MaxSatSolveArgs {
    /// WCNF/MaxSAT input file.
    pub file: PathBuf,
    /// Wall-clock timeout in seconds (0 = none). On timeout, prints the best
    /// bound found and `s UNKNOWN`.
    #[arg(long, default_value_t = 0.0)]
    pub timeout: f64,
    /// EXPERIMENTAL: solve via the native ay-milp 0/1-ILP encoding instead of
    /// the OLL core-guided engine. Validation lane for LP-structured weighted
    /// families (facility-location / MPE / auctions) where OLL stalls.
    #[arg(long)]
    pub milp: bool,
    /// Write a VeriPB certificate of the reported answer to `<STEM>.opb` and
    /// `<STEM>.opb.pbp`. Emission is write-only: it can refuse to certify (which
    /// raises an alarm) but never changes the answer AY reports.
    #[arg(long, value_name = "STEM")]
    pub proof: Option<PathBuf>,
    #[command(flatten)]
    engine_flags: MaxSatEngineFlags,
}

/// Arguments for `ay maxsat bench`.
#[derive(clap::Args)]
pub(crate) struct MaxSatBenchArgs {
    /// Directory containing .wcnf instances (searched recursively).
    pub dir: PathBuf,
    /// Per-instance wall-clock timeout in seconds.
    #[arg(long, default_value_t = 60.0)]
    pub timeout: f64,
    /// Reference field CSV (columns: instance, o_value, then one column of
    /// per-instance runtimes per competing solver). Enables optimum
    /// verification and a retroactive leaderboard at the same timeout.
    #[arg(long)]
    pub field: Option<PathBuf>,
    /// Number of instances to run in parallel.
    #[arg(long)]
    pub jobs: Option<usize>,
    /// Run only the first N instances (sorted by name).
    #[arg(long)]
    pub limit: Option<usize>,
    /// Deterministically subsample: keep every Nth instance.
    #[arg(long)]
    pub stride: Option<usize>,
    /// Write detailed per-instance results to a JSON file.
    #[arg(long)]
    pub out: Option<PathBuf>,
    /// Skip re-verifying reported models against the instance.
    #[arg(long)]
    pub no_verify: bool,
    /// Certify every reported optimum: ask the solver child for a VeriPB
    /// certificate and check it with the pinned checker before the row is
    /// scored. OFF by default. A certified sweep writes a multi-MB `.opb` per
    /// instance (36MB for a 1,035,351-constraint one) and pays for that
    /// emission inside the measured `seconds`, so its PAR2 and solved count are
    /// DELIBERATELY pessimistic — campaign numbers come from the uncertified
    /// lane. Certification can only downgrade a row or annotate it; it can
    /// never turn a non-optimum into an optimum.
    #[arg(long)]
    pub proof_check: bool,
    /// Directory for certificate artifacts. Default: a per-run scratch
    /// directory under the system temp dir, removed when the sweep ends.
    /// Point this at a large volume when certifying the full corpus.
    #[arg(long, value_name = "DIR", requires = "proof_check")]
    pub proof_dir: Option<PathBuf>,
    /// Skip certification for instances above this size (MiB; 0 = no cap).
    /// The artifacts are BIGGER than the `.wcnf`, not "roughly its size":
    /// measured, a 43,020,161-byte `.wcnf` produced a 71,989,226-byte `.opb`
    /// plus a 7,059,974-byte `.pbp` — 1.84x the input, on disk, for every armed
    /// row. The default is therefore 40MiB of `.wcnf`, which is ~74MiB of
    /// artifacts: just under `GIANT_INSTANCE_BYTES` (80MiB), the size at which
    /// the OOM guard already special-cases an instance. The checker's RSS is
    /// also not in the resource plan (`MaxSatResources::plan`) — it borrows the
    /// solver's slot after the solver exits. Skips are annotated per row and
    /// counted in the summary; they are never silently recorded as verified.
    #[arg(
        long,
        value_name = "MIB",
        default_value_t = PROOF_MAX_INSTANCE_MIB_DEFAULT,
        requires = "proof_check"
    )]
    pub proof_max_instance_mib: u64,
    /// Benchmark an external solver instead of AY: "NAME=CMD" where CMD is
    /// a program plus arguments; "{file}" in CMD is replaced by the
    /// instance path (appended if absent). The same wall-clock timeout,
    /// kill policy, and model/optimum verification apply.
    #[arg(long)]
    pub solver: Option<String>,
    #[command(flatten)]
    engine_flags: MaxSatEngineFlags,
}

impl MaxSatBenchArgs {
    /// Reject AY-only engine switches before an external child can be spawned.
    fn validate_engine_flags(&self) -> Result<()> {
        if self.solver.is_some() && !self.engine_flags.solver_cli_args(false).is_empty() {
            anyhow::bail!("MaxSAT engine switches apply only to internal AY benchmark children");
        }
        Ok(())
    }

    /// Exact engine switches applied to every internal solver child.
    fn effective_internal_solver_cli_args(&self, jobs: usize) -> Option<Vec<&'static str>> {
        self.solver
            .is_none()
            .then(|| self.engine_flags.solver_cli_args(jobs > 1))
    }
}

#[cfg(test)]
mod maxsat_cli_flag_tests {
    use super::*;
    use clap::Parser as _;

    const ALL_ENGINE_ARGS: [&str; 11] = [
        "--maxsat-no-tot-eqs",
        "--maxsat-no-bce-revert",
        "--maxsat-no-am1-maxcover",
        "--maxsat-bce",
        "--maxsat-no-bmo",
        "--maxsat-no-cold-descent",
        "--maxsat-no-descent-residual",
        "--maxsat-no-dpw",
        "--maxsat-no-early-descent",
        "--maxsat-no-preproc",
        "--maxsat-no-milp-race",
    ];

    fn solve_args(argv: &[&str]) -> MaxSatSolveArgs {
        let cli = crate::Cli::try_parse_from(argv).expect("MaxSAT CLI parses");
        match cli.command {
            Some(crate::Command::Maxsat(MaxSatCommand::Solve(args))) => args,
            _ => panic!("expected `ay maxsat solve`"),
        }
    }

    #[test]
    fn actual_maxsat_solve_accepts_and_maps_every_engine_switch() {
        let mut argv = vec!["ay", "maxsat", "solve", "input.wcnf"];
        argv.extend(ALL_ENGINE_ARGS);
        let args = solve_args(&argv);
        let flags = args.engine_flags.misc_cli_flags();
        assert_eq!(args.file, PathBuf::from("input.wcnf"));
        assert!(flags.maxsat_no_tot_eqs);
        assert!(flags.maxsat_no_bce_revert);
        assert!(flags.maxsat_no_am1_maxcover);
        assert!(flags.maxsat_bce);
        assert!(flags.maxsat_no_bmo);
        assert!(flags.maxsat_no_cold_descent);
        assert!(flags.maxsat_no_descent_residual);
        assert!(flags.maxsat_no_dpw);
        assert!(flags.maxsat_no_early_descent);
        assert!(flags.maxsat_no_preproc);
        assert!(flags.maxsat_no_milp_race);
        assert_eq!(args.engine_flags.solver_cli_args(false), ALL_ENGINE_ARGS);
    }

    #[test]
    fn actual_maxsat_solve_preserves_engine_default_polarities() {
        let args = solve_args(&["ay", "maxsat", "solve", "input.wcnf"]);
        let flags = args.engine_flags.misc_cli_flags();
        assert!(!flags.maxsat_bce, "BCE remains opt-in");
        assert!(!flags.maxsat_no_milp_race, "MILP race remains default-on");
        assert!(args.engine_flags.solver_cli_args(false).is_empty());
    }

    #[test]
    fn bench_forwards_switches_and_opts_out_of_parallel_race() {
        let cli = crate::Cli::try_parse_from([
            "ay",
            "maxsat",
            "bench",
            "corpus",
            "--maxsat-bce",
            "--maxsat-no-dpw",
        ])
        .expect("MaxSAT bench CLI parses");
        let args = match cli.command {
            Some(crate::Command::Maxsat(MaxSatCommand::Bench(args))) => args,
            _ => panic!("expected `ay maxsat bench`"),
        };
        assert_eq!(
            args.engine_flags.solver_cli_args(false),
            ["--maxsat-bce", "--maxsat-no-dpw"]
        );
        assert_eq!(
            args.engine_flags.solver_cli_args(true),
            ["--maxsat-bce", "--maxsat-no-dpw", "--maxsat-no-milp-race"]
        );
        assert_eq!(
            args.effective_internal_solver_cli_args(3),
            Some(vec![
                "--maxsat-bce",
                "--maxsat-no-dpw",
                "--maxsat-no-milp-race"
            ])
        );
    }

    #[test]
    fn bench_rejects_ay_engine_switches_for_external_solvers() {
        let cli = crate::Cli::try_parse_from([
            "ay",
            "maxsat",
            "bench",
            "corpus",
            "--solver",
            "other=solver",
            "--maxsat-bce",
        ])
        .expect("syntactically valid MaxSAT bench CLI");
        let args = match cli.command {
            Some(crate::Command::Maxsat(MaxSatCommand::Bench(args))) => args,
            _ => panic!("expected `ay maxsat bench`"),
        };
        assert!(args.validate_engine_flags().is_err());
        assert_eq!(args.effective_internal_solver_cli_args(3), None);
    }
}
