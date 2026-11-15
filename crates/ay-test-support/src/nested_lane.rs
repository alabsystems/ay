// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The lane a nested Cargo build names for itself, and the two halves that
//! carry it.
//!
//! Split out of `lib.rs` so the argument half (naming `--unverified`) and the
//! environment half (giving the child its own empty rustflags list) sit beside
//! each other and beside the tests that pin them.

use super::{run_with_environment, NestedCargoScheduling, WorkspaceBinarySpec};
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::Path;

/// Cargo's encoded-rustflags channel. Set EMPTY for every nested build.
pub(crate) const NESTED_RUSTFLAGS_ENV: &str = "CARGO_ENCODED_RUSTFLAGS";

/// Give the nested oracle build an empty rustflags list of its own.
///
/// WHY. These builds run with `current_dir` inside the frozen source snapshot,
/// so Cargo auto-loads the workspace's `.cargo/config.toml` — the file that
/// carries this repository's REQUIRED build posture for the code under test:
/// full static discharge on every unit, and an explicit frontend-lowering
/// value. That posture is right for the workspace and wrong for a test oracle
/// compiled out of third-party crates. Naming the lane is only half of it:
/// `--unverified` switches verification off (targo reports `compiled WITHOUT
/// Trust verification — 0 obligations checked`) but does NOT neutralise an
/// EXPLICIT frontend-lowering value, so the nested build still died inside
/// `memchr`. Measured 2026-09-23 from the worktree root with the workspace
/// config loaded, `targo --unverified build --locked --offline -p
/// ay-lrat-check --bin ay-lrat-check`: 349 `error` lines, `could not compile
/// memchr (lib) due to 112 previous errors`, and the same run with this
/// variable set to the empty string finished in 11.03 s with 0 errors.
///
/// WHY THIS CHANNEL, and not an override of one config table. Cargo consults
/// the encoded-rustflags environment BEFORE any config table, so one empty
/// value answers target units and host units together. A `--config` override
/// of `target."cfg(all())".rustflags` merges into that one array only and
/// leaves the `[host]` table alive, which is exactly how the `libc`,
/// `proc-macro2`, `quote` and `serde_core` build scripts stayed strict under
/// the nested build's own sanitized environment. The candidate run above
/// compiled all of those, plus `autocfg`, `unicode-ident` and `cc`, from one
/// setting. Empty is also the only value this needs: the child must inherit
/// NOTHING, not a different posture, so no compiler flag is named here — which
/// is also what keeps this file shippable, since the public export's
/// fail-closed residue guard refuses the private verifier flag text in
/// exported source and `publish/transforms.sh` reserves its prose transforms
/// for comments, executable occurrences being required to fail.
///
/// NO ORACLE IS WEAKENED. Verification is already off on this lane by
/// `--unverified`, which claims no proof; what remains in that config array is
/// strict frontend lowering, which "rejects unsupported bodies and
/// disagreements in the already-running source/MIR comparison, without
/// changing codegen" (`.cargo/config.toml`), plus target-CPU tuning. So this
/// removes a compiler-side refusal and a tuning flag, not a check on the
/// oracle's own behaviour. The oracle itself is unchanged: the separately
/// built, exact-source, provenance-checked checker binary, which now actually
/// gets built and therefore actually checks the proof.
///
/// An ambient value never reaches here: `BUILD_ENV_PASSTHROUGH` is an
/// allowlist and does not carry any rustflags variable, so the caller's
/// environment is already gone by the time this writes. The nested build's
/// whole environment is hashed into its build identity, so this setting is an
/// input to the artifact, not just to how it was produced.
pub(crate) fn clear_inherited_rustflags(environment: &mut BTreeMap<OsString, OsString>) {
    environment.insert(OsString::from(NESTED_RUSTFLAGS_ENV), OsString::new());
}

/// Which Cargo front end drives the nested build, and therefore whether it has
/// to be told a lane.
///
/// A Trust sysroot ships `cargo` as a compat entry of `targo`, and targo brands
/// itself from `argv[0]`: invoked as `cargo` it is ordinary Cargo and can
/// neither take nor propagate a Trust lane. The nested build then compiles
/// under the workspace's required posture and dies in third-party crates the
/// same way the bare `targo build` this repo refuses would. targo's
/// nested-unverified handoff, which would let a `$CARGO` child inherit the
/// outer lane, exists only on Linux, so on every other host the child has to
/// name its own lane — targo says so in its own warning. The oracle binaries
/// built here are test tooling, not the code under test, and `--unverified` is
/// the lane that claims exactly that: no proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CargoDriver {
    /// Stock Cargo: no lane vocabulary, plain `cargo build`.
    Cargo,
    /// Trust's targo, invoked through its own `targo` entry so the brand is
    /// targo and `--unverified` is accepted.
    Targo,
}

/// Does the executable at `targo` take a Trust lane?
///
/// This is the discriminator, not a comparison with the sysroot's `cargo`.
/// Both spellings can be one program and still answer differently, because
/// targo brands itself from `argv[0]`: in the stage2 sysroot `cargo` and
/// `targo` are literally the same inode and `cargo --unverified --version`
/// still fails. And the converse is what broke the three LRAT oracle tests:
/// in the sealed atpkg store the two entries are the same program but NOT
/// byte-identical — they differ at one offset, because each authenticates at
/// its own real path — so a byte-equality test reads targo as stock Cargo,
/// drops the lane, and the nested build compiles under the workspace's full
/// required posture and dies in third-party code.
///
/// `--unverified` is the one discriminator that has held under every
/// measurement here: the real targo accepts it (exit 0, prints its version),
/// while the compat `cargo` entry answers
/// `error: unexpected argument '--unverified' found`. Measured 2026-09-23 on
/// targo 321aaeda7 (atpkg store 9192) and targo ba1f66612 (stage2), both
/// spellings each.
pub(crate) fn targo_takes_a_trust_lane(
    targo: &Path,
    workspace: &Path,
    environment: &BTreeMap<OsString, OsString>,
) -> bool {
    if !targo.is_file() {
        return false;
    }
    run_with_environment(
        targo,
        &["--unverified", "--version"],
        workspace,
        environment,
    )
    .status
    .success()
}

pub(crate) fn nested_cargo_build_arguments(
    spec: WorkspaceBinarySpec<'_>,
    target_dir: &Path,
    cargo_scheduling: NestedCargoScheduling,
    driver: CargoDriver,
) -> Vec<OsString> {
    let mut arguments = Vec::new();
    if driver == CargoDriver::Targo {
        // The lane precedes the subcommand; see `CargoDriver`. The other half
        // of the lane is `clear_inherited_rustflags`, which is driver-
        // independent: stock Cargo cannot read this repository's posture flags
        // either, so it must not inherit them.
        arguments.push(OsString::from("--unverified"));
    }
    arguments.push(OsString::from("build"));
    if let Some(jobs) = cargo_scheduling.jobs() {
        arguments.push("--jobs".into());
        arguments.push(jobs.to_string().into());
    }
    arguments.extend(
        [
            "--locked",
            "--offline",
            "-p",
            spec.package,
            "--bin",
            spec.binary,
            "--target-dir",
        ]
        .into_iter()
        .map(OsString::from),
    );
    arguments.push(target_dir.as_os_str().to_owned());
    if !spec.features.is_empty() {
        arguments.push("--features".into());
        arguments.push(spec.features.join(",").into());
    }
    arguments
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SourceBinding;
    use std::ffi::OsStr;

    #[test]
    fn nested_cargo_command_explicitly_applies_validated_job_cap() {
        let spec = WorkspaceBinarySpec {
            workspace: Path::new("."),
            target_name: "exact",
            package: "example-package",
            binary: "example-binary",
            features: &["one", "two"],
            source_binding: SourceBinding::IdentityTarget,
        };
        let capped = nested_cargo_build_arguments(
            spec,
            Path::new("exact-target"),
            NestedCargoScheduling::ParentEnvelopeSerialized { jobs: 3 },
            CargoDriver::Cargo,
        );
        assert_eq!(
            capped,
            [
                "build",
                "--jobs",
                "3",
                "--locked",
                "--offline",
                "-p",
                "example-package",
                "--bin",
                "example-binary",
                "--target-dir",
                "exact-target",
                "--features",
                "one,two",
            ]
            .into_iter()
            .map(OsString::from)
            .collect::<Vec<_>>()
        );

        let uncapped = nested_cargo_build_arguments(
            spec,
            Path::new("exact-target"),
            NestedCargoScheduling::CargoDefault,
            CargoDriver::Cargo,
        );
        assert!(
            !uncapped
                .iter()
                .any(|argument| argument == OsStr::new("--jobs")),
            "ordinary tests without a configured cap retain Cargo's default"
        );

        let through_targo = nested_cargo_build_arguments(
            spec,
            Path::new("exact-target"),
            NestedCargoScheduling::CargoDefault,
            CargoDriver::Targo,
        );
        assert_eq!(
            &through_targo[..2],
            [OsString::from("--unverified"), OsString::from("build")],
            "a targo-driven nested build names its lane before the subcommand"
        );
        assert_eq!(&through_targo[2..], &uncapped[1..]);
    }

    #[test]
    fn the_nested_lane_gives_every_child_an_empty_rustflags_list() {
        let mut environment = BTreeMap::new();
        environment.insert(
            OsString::from(NESTED_RUSTFLAGS_ENV),
            OsString::from("--cfg=inherited"),
        );
        clear_inherited_rustflags(&mut environment);
        assert_eq!(
            environment.get(OsStr::new(NESTED_RUSTFLAGS_ENV)),
            Some(&OsString::new()),
            "the nested build must carry an EMPTY rustflags list, which is what \
             stops it inheriting the workspace's required build posture; an \
             absent key would let that posture through"
        );
    }

    #[test]
    fn a_missing_or_refusing_executable_takes_no_trust_lane() {
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR"));
        let environment = BTreeMap::new();
        let absent = workspace.join("this-executable-does-not-exist");
        assert!(
            !targo_takes_a_trust_lane(&absent, workspace, &environment),
            "a missing entry takes no lane"
        );
        #[cfg(unix)]
        assert!(
            !targo_takes_a_trust_lane(Path::new("/usr/bin/false"), workspace, &environment),
            "an executable that refuses the lane takes no lane"
        );
    }
}
