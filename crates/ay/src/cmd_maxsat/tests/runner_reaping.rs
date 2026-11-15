// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The external-solver runner's watchdog arming, per platform.

use super::*;

/// Runs `run_one` against a fake external MaxSAT solver that forks a 60 s
/// descendant, records that descendant's pid and the `NBCORE` it was handed,
/// and answers `s UNKNOWN`. Returns the result, the scratch directory and the
/// two record files.
#[cfg(unix)]
fn run_descendant_forking_solver() -> (RunResult, PathBuf, PathBuf, PathBuf) {
    use std::os::unix::fs::PermissionsExt as _;

    let dir = std::env::temp_dir().join(format!(
        "ay-maxsat-runner-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&dir).expect("mkdir");
    let solver = dir.join("solver.sh");
    let pid_file = dir.join("descendant.pid");
    let env_file = dir.join("nbcore.txt");
    fs::write(
        &solver,
        format!(
            "#!/bin/sh\nsleep 60 &\necho $! > '{}'\necho \"${{NBCORE:-}}\" > '{}'\nprintf 's UNKNOWN\\n'\n",
            pid_file.display(),
            env_file.display()
        ),
    )
    .expect("write solver");
    let mut permissions = fs::metadata(&solver).unwrap().permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&solver, permissions).expect("chmod");
    let input = dir.join("case.wcnf");
    fs::write(&input, "h 1 0\n").expect("write input");
    let lease_command = OomGuardSource::Embedded.command();
    let lease_lock_path = dir.join("host-lease.lock");
    let campaign_lease = MaxSatCampaignLease::acquire_command(
        lease_command,
        "MaxSAT runner test",
        Stdio::null(),
        Some(&lease_lock_path),
    )
    .expect("campaign lease");
    let resources = MaxSatResources {
        plan: MaxSatResourcePlan {
            schema: MAXSAT_RESOURCE_ENVELOPE_SCHEMA_V2,
            requested_jobs: 1,
            jobs: 1,
            memlimit_mb_per_child: 10_000,
            nbcore_per_child: 3,
            headroom_mb: 16_000,
            planner: "test".to_string(),
            planner_protocol: MAXSAT_RESOURCE_PLANNER_PROTOCOL_V1,
            enforcement: MAXSAT_CHILD_ENFORCEMENT_V1,
            solver_environment: MAXSAT_SOLVER_ENVIRONMENT_V1,
            aggregate_enforcement: MAXSAT_AGGREGATE_ENFORCEMENT_V1,
            lease_protocol: MAXSAT_LEASE_PROTOCOL_V1,
            lease_readiness: MAXSAT_LEASE_READINESS_V1,
            lease_location: MAXSAT_LEASE_LOCATION_V1,
        },
        guard: OomGuardSource::Checkout(locate_oom_guard().expect("oom guard")),
        campaign_lease: Arc::new(campaign_lease),
        watchdog_server: MaxSatWatchdogServer::new(OomGuardSource::Checkout(
            locate_oom_guard().expect("oom guard"),
        )),
    };
    let external = ("fake".to_string(), vec![solver.display().to_string()]);
    let result = run_one(
        Path::new("unused-ay"),
        Some(&external),
        &input,
        5.0,
        false,
        None,
        &resources,
        None,
        &MaxSatEngineFlags::default(),
    );
    (result, dir, pid_file, env_file)
}

/// Where the runner can observe an unreaped child it arms the RSS watchdog,
/// runs the solver under the core envelope and reaps its whole process group.
/// The platform list is the one `observe_maxsat_child_unreaped` and
/// `wait_for_maxsat_guard_stop` are implemented for; this test was `unix`-wide
/// and failed on macOS, which that code refuses by design (and whose missing
/// `/proc` would have made the reaping check below vacuous there anyway).
#[cfg(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
))]
#[test]
fn maxsat_runner_reaps_descendants_and_applies_core_envelope() {
    let (result, dir, pid_file, env_file) = run_descendant_forking_solver();
    assert_eq!(result.status, RunStatus::Timeout, "{}", result.detail);
    assert_eq!(fs::read_to_string(env_file).unwrap().trim(), "3");
    let descendant = fs::read_to_string(pid_file).unwrap();
    let proc_stat = PathBuf::from(format!("/proc/{}/stat", descendant.trim()));
    for _ in 0..100 {
        let dead_or_zombie = fs::read_to_string(&proc_stat)
            .map(|stat| {
                stat.rsplit(')')
                    .nth(1)
                    .is_some_and(|rest| rest.trim().starts_with('Z'))
            })
            .unwrap_or(true);
        if dead_or_zombie {
            fs::remove_dir_all(&dir).ok();
            return;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    panic!(
        "descendant {} survived process-group cleanup",
        descendant.trim()
    );
}

/// Darwin's observation path must provide the same cleanup and core contract.
/// Use its real process inventory, rather than treating absent /proc as death.
#[cfg(target_os = "macos")]
#[test]
fn maxsat_darwin_runner_reaps_descendants_and_applies_core_envelope() {
    let (result, dir, pid_file, env_file) = run_descendant_forking_solver();
    assert_eq!(result.status, RunStatus::Timeout, "{}", result.detail);
    assert_eq!(
        fs::read_to_string(env_file).expect("core envelope").trim(),
        "3"
    );
    let descendant = fs::read_to_string(pid_file).expect("descendant pid");
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        let status = Command::new("/bin/ps")
            .args(["-o", "stat=", "-p", descendant.trim()])
            .output()
            .expect("native Darwin process inventory");
        let text = String::from_utf8(status.stdout).expect("process state UTF-8");
        if (status.status.code() == Some(1) && text.trim().is_empty())
            || (status.status.success() && text.trim().starts_with('Z'))
        {
            fs::remove_dir_all(&dir).ok();
            return;
        }
        assert!(
            status.status.success(),
            "could not observe descendant state"
        );
        assert!(
            Instant::now() < deadline,
            "descendant survived cleanup: {text}"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
}

/// Everywhere else the runner cannot observe an unreaped child, so it must not
/// run an unwatched solver: the guard, held stopped before it execs the solver,
/// is killed with its process group, and the run is an error naming the
/// platform. The solver never ran, so it wrote neither record file.
#[cfg(all(
    unix,
    not(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc")),
    ))
))]
#[test]
fn maxsat_runner_refuses_an_unwatchable_solver_on_this_platform() {
    let (result, dir, pid_file, env_file) = run_descendant_forking_solver();
    assert_eq!(result.status, RunStatus::Error, "{}", result.detail);
    assert!(
        result.detail.contains("unavailable on this platform"),
        "{}",
        result.detail
    );
    assert!(
        !pid_file.exists() && !env_file.exists(),
        "an unwatched MaxSAT solver ran"
    );
    fs::remove_dir_all(&dir).ok();
}
