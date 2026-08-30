// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by the standalone PB binary to preserve private item DefPaths.

#[derive(Debug)]
struct SolveArgs {
    file: PathBuf,
    timeout: Option<u64>,
    proof: Option<PathBuf>,
    stats: bool,
    stats_json: bool,
    native: bool,
}

fn parse_solve_args(args: Vec<String>) -> Result<SolveArgs, String> {
    let mut file = None;
    let mut timeout = None;
    let mut proof = None;
    let mut stats = false;
    let mut stats_json = false;
    let mut native = false;
    let mut proof_tap_legacy = false;
    let mut switches = ay_pb::ab_switches::PbAbSwitches::default();
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            // B31 A/B opt-outs (hidden; replace the retired AY_PB_* env vars
            // the official wrapper used to export).
            "--no-pb-clique-coloring" => switches.clique_coloring = false,
            "--no-pb-injcomp" => switches.injcomp = false,
            "--no-pb-compact-cert" => switches.compact_cert = false,
            "--no-pb-restart-floor" => switches.restart_floor = false,
            "--no-pb-counting" => switches.counting = false,
            "--no-pb-bnn-feas" => switches.bnn_feas = false,
            "--no-pb-bnn-sched" => switches.bnn_sched = false,
            "--no-pb-sls-nlc" => switches.sls_nlc = false,
            "--no-pb-wbo-sls" => switches.wbo_sls = false,
            "--no-pb-lns2" => switches.lns2 = false,
            "--no-pb-symmetry-arm" => switches.symmetry_arm = false,
            // The legacy synchronous proof path (escape hatch; the dense
            // async tap is the default — was AY_PB_PROOF_TAP=legacy).
            "--proof-tap-legacy" => proof_tap_legacy = true,
            // B56: opt in to the root EDAC/VAC-lite WCSP probe.
            "--pb-wcsp-edac" => switches.wcsp_edac = true,
            "--pb-two-club-trace" => switches.two_club_trace = true,
            "--pb-two-club-dump-frontier" => switches.two_club_dump_frontier = true,
            "--pb-two-club-max-nodes" => {
                i += 1;
                let value = args
                    .get(i)
                    .ok_or_else(|| "--pb-two-club-max-nodes requires a count".to_string())?;
                let nodes = value
                    .parse::<u64>()
                    .map_err(|_| format!("invalid --pb-two-club-max-nodes value: {value}"))?;
                switches.two_club_max_nodes = Some(nodes);
            }
            "--pb-two-club-branch" => {
                i += 1;
                let value = args
                    .get(i)
                    .ok_or_else(|| "--pb-two-club-branch requires a selector".to_string())?;
                switches.two_club_branch = Some(&*Box::leak(value.clone().into_boxed_str()));
            }
            // B57: parallel worker policy (0 = sequential, N = N workers).
            "--pb-parallel" => {
                i += 1;
                let value = args
                    .get(i)
                    .ok_or_else(|| "--pb-parallel requires a worker count".to_string())?;
                let workers = value
                    .parse::<u16>()
                    .map_err(|_| format!("invalid --pb-parallel value: {value}"))?;
                switches.parallel_workers = Some(workers);
            }
            // B55: certified-optimization portfolio kill + sidecar opt-in.
            "--no-opt-cert-portfolio" => {
                let _ = OPT_CERT_PORTFOLIO_OFF.set(true);
            }
            "--clique-row-map-sidecar" => {
                let _ = CLIQUE_ROW_MAP_SIDECAR.set(true);
            }
            // B47: pin the certified-optimization native slice, milliseconds.
            "--cert-native-cap-ms" => {
                i += 1;
                let value = args
                    .get(i)
                    .ok_or_else(|| "--cert-native-cap-ms requires a value (ms)".to_string())?;
                let ms = value
                    .parse::<u64>()
                    .map_err(|_| format!("invalid --cert-native-cap-ms value: {value}"))?;
                let _ = CERT_NATIVE_CAP_MS.set(ms);
            }
            "--timeout" | "-t" => {
                i += 1;
                let value = args
                    .get(i)
                    .ok_or_else(|| "--timeout requires a millisecond value".to_string())?;
                timeout = Some(
                    value
                        .parse::<u64>()
                        .map_err(|_| format!("invalid timeout value: {value}"))?,
                );
            }
            "--proof" => {
                i += 1;
                proof = Some(PathBuf::from(
                    args.get(i)
                        .ok_or_else(|| "--proof requires a path".to_string())?,
                ));
            }
            "--stats" => stats = true,
            "--stats-json" => stats_json = true,
            "--native" => native = true,
            // PB certificate diagnostics: which OPT-LIN rung ran, the slice of
            // the certification budget it was given, and how long it took.
            // `MiscCliFlags::cert_debug` gates diagnostics all through
            // `ay-pb-core`'s certificate module, but nothing on the PB command
            // line ever set it, so those sites were dead here. Set-once; a
            // second install (tests) is not an error, the flag only decides
            // whether comments print.
            // INSTALL WITHOUT READING FIRST: `misc_cli_flags()` initialises
            // the set-once global as a side effect of reading it, so guarding
            // this on its current value makes the install a no-op.
            "--cert-debug" => {
                let _ = ay_core::set_global_misc_cli_flags_with(|flags| {
                    flags.cert_debug = true;
                });
            }
            "--help" | "-h" => return Err(usage()),
            arg if arg.starts_with('-') => return Err(format!("unknown argument: {arg}")),
            path => {
                if file.is_some() {
                    return Err(format!("unexpected extra input path: {path}"));
                }
                file = Some(PathBuf::from(path));
            }
        }
        i += 1;
    }

    if ay_pb::ab_switches::set(switches).is_err() && ay_pb::ab_switches::get() != switches {
        return Err("PB A/B switches already installed with a different value".to_string());
    }
    if proof_tap_legacy {
        PROOF_TAP_LEGACY.store(true, Ordering::Relaxed);
    }
    Ok(SolveArgs {
        file: file.ok_or_else(usage)?,
        timeout,
        proof,
        stats,
        stats_json,
        native,
    })
}
