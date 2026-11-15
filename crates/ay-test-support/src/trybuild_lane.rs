// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `$CARGO` a trybuild run is given: a funnel-owned, lane-aware shim.
//!
//! trybuild compiles its UI cases by spawning `$CARGO` itself, so it never
//! passes through the exact-source funnel in `lib.rs`. Measured with a probe
//! wrapper (the development design notes §5.8), that
//! left every trybuild test red for four reasons, and this module answers each:
//!
//! 1. **The lane, per subcommand.** Under Trust `$CARGO` is targo, which
//!    refuses a plain `build` or `check` and refuses `--unverified` on
//!    `metadata`, `clean` and `generate-lockfile` (`--unverified is valid only
//!    for a Targo compilation command`); trybuild runs all of them. The shim
//!    names `--unverified` on exactly [`COMPILING_SUBCOMMANDS`], and only when
//!    the funnel's own probe (`targo --unverified --version`) says the driver
//!    takes a lane at all.
//!    `--unverified` claims no proof, which is what a type-level compile-fail
//!    lock needs: it asks whether the compiler accepts a program, not whether
//!    anything was proved.
//! 2. **The working directory.** trybuild puts its project under the Cargo
//!    target directory, which sits inside the workspace, and Cargo discovers
//!    configuration from the WORKING DIRECTORY upward, so every trybuild child
//!    loaded this repository's required posture for the code under test and
//!    died in third-party build scripts. The shim runs Cargo from a directory
//!    chosen here (`chosen_working_directory`), which is checked to discover
//!    no semantic Cargo configuration, and names the manifest the caller meant
//!    with `--manifest-path` (found exactly as Cargo finds it: the nearest
//!    `Cargo.toml` at or above the caller's directory). A relative
//!    `CARGO_TARGET_DIR` is resolved against the caller's directory first, as
//!    Cargo would have. The manifest keeps deciding WHAT is built and where it
//!    lands; only configuration discovery moves.
//! 3. **Host units.** trybuild always passes `--target`, and with an explicit
//!    target Cargo gives build scripts and proc-macros only the `[host]`
//!    table's rustflags. So the funnel's own answer, an empty encoded-rustflags
//!    list, reaches target units only; and it would be wrong here anyway,
//!    because it outranks the rustflags trybuild itself passes through
//!    `--config` (`--cfg trybuild` and the diagnostic width its `.stderr`
//!    expectations are rendered at). This module's answer is item 2: from the
//!    chosen directory no `[host]` table is discovered, so host units compile
//!    with no configured flags, under the lane named in item 1, and target
//!    units see exactly the flags trybuild passes. No compiler flag is named
//!    anywhere here, which keeps this file exportable: `publish/transforms.sh`
//!    ends with a fail-closed guard against the private verifier flag text in
//!    every exported file, and `crates/` is exported.
//! 4. **The compiler.** The shim pins `RUSTC` to the sysroot compiler paired
//!    with the driver, as the funnel does for its own nested builds, so moving
//!    the working directory cannot move the compiler (a rustup proxy chooses
//!    its toolchain from the working directory).
//!
//! NO ORACLE IS WEAKENED. trybuild's expectations are untouched: a `pass` case
//! must still compile and run, and a `compile_fail` case must still fail with
//! the recorded diagnostics. What the child no longer loads is a compiler-side
//! refusal plus target-CPU tuning, the same scope the funnel's nested builds
//! already drop (`nested_lane::clear_inherited_rustflags`).
//!
//! The shim is a POSIX `sh` script. Off Unix there is no shim, and
//! [`with_trybuild_cargo`] fails closed rather than let trybuild run a `$CARGO`
//! that cannot name a lane.

#[cfg(unix)]
use super::cargo_config::{cargo_config_paths, semantic_cargo_config_key};
#[cfg(unix)]
use super::nested_lane::CargoDriver;
#[cfg(unix)]
use super::{
    cargo_home, finish_build_identity, hash_component, prepare_cargo_target_root,
    resolve_paired_toolchain, UNIQUE_PATH_SEQUENCE,
};
#[cfg(unix)]
use sha2::{Digest as _, Sha256};
#[cfg(unix)]
use std::fs as filesystem;
use std::path::{Path, PathBuf};
#[cfg(unix)]
use std::sync::atomic::Ordering;

/// The subcommands trybuild runs that compile, and therefore take the lane.
pub const COMPILING_SUBCOMMANDS: &[&str] = &["build", "check", "run"];

/// The subcommands trybuild runs that compile nothing. targo refuses a lane on
/// these, so the shim passes them through without one.
pub const NON_COMPILING_SUBCOMMANDS: &[&str] = &["metadata", "clean", "generate-lockfile"];

#[cfg(unix)]
const WORKING_DIRECTORY_NAME: &str = "ay-test-support-cargo-cwd-v1";
#[cfg(unix)]
const SHIM_NAMESPACE: &str = "ay-trybuild-cargo-v1";
#[cfg(unix)]
const SHIM_FILE_NAME: &str = "cargo";

/// Run `run` (which must create AND drop its `trybuild::TestCases`, since
/// trybuild compiles on drop) with `CARGO` pointing at the lane-aware shim.
///
/// The process-wide environment lock ([`crate::env::lock_env`]) is held for the
/// whole run and the previous `CARGO` is restored afterwards, also on panic.
/// Do not call this while already holding that lock, and keep everything else
/// that reads `CARGO` out of `run`: for its duration `CARGO` names the shim,
/// not the cargo that built the test (this crate's own nested builds seed
/// their toolchain from it).
pub fn with_trybuild_cargo<T>(workspace: &Path, run: impl FnOnce() -> T) -> T {
    let _environment = crate::env::lock_env();
    let shim = install_trybuild_cargo(workspace);
    let _cargo = crate::env::ScopedEnvVar::set("CARGO", &shim);
    run()
}

#[cfg(not(unix))]
fn install_trybuild_cargo(workspace: &Path) -> PathBuf {
    panic!(
        "the trybuild cargo shim is a POSIX sh script and this host is not Unix; \
         refusing to let trybuild run an unshimmed $CARGO for {}",
        workspace.display()
    );
}

#[cfg(unix)]
fn install_trybuild_cargo(workspace: &Path) -> PathBuf {
    let workspace = workspace.canonicalize().unwrap_or_else(|error| {
        panic!(
            "failed to resolve trybuild workspace {}: {error}",
            workspace.display()
        )
    });
    // Resolved while `CARGO` still names the cargo that built this test: the
    // funnel seeds its toolchain from it.
    let toolchain = resolve_paired_toolchain(&workspace);
    let working_directory =
        chosen_working_directory(&std::env::temp_dir(), &cargo_home(&workspace));
    let script = shim_script(
        &toolchain.cargo,
        toolchain.driver,
        &toolchain.rustc,
        &working_directory,
    );
    publish_shim(&prepare_cargo_target_root(&workspace), &script)
}

/// Create (once) and return the directory the trybuild child runs Cargo from.
///
/// It must discover no Cargo configuration that can change what is compiled:
/// that is the whole point of moving there. So every file Cargo would discover
/// from it, including `$CARGO_HOME`'s, is classified by the same rule the
/// funnel applies to configuration outside a nested build's source identity,
/// and a semantic key fails closed, naming the file and key. A temporary
/// directory that sits inside a checkout is exactly the case this refuses.
#[cfg(unix)]
pub(crate) fn chosen_working_directory(base: &Path, cargo_home: &Path) -> PathBuf {
    let directory = base.join(WORKING_DIRECTORY_NAME);
    filesystem::create_dir_all(&directory).unwrap_or_else(|error| {
        panic!(
            "failed to create trybuild working directory {}: {error}",
            directory.display()
        )
    });
    let metadata = filesystem::symlink_metadata(&directory).unwrap_or_else(|error| {
        panic!(
            "failed to inspect trybuild working directory {}: {error}",
            directory.display()
        )
    });
    assert!(
        metadata.is_dir() && !metadata.file_type().is_symlink(),
        "trybuild working directory is not a real directory: {}",
        directory.display()
    );
    let directory = directory.canonicalize().unwrap_or_else(|error| {
        panic!(
            "failed to resolve trybuild working directory {}: {error}",
            directory.display()
        )
    });
    for config in cargo_config_paths(&directory, cargo_home) {
        let contents = filesystem::read_to_string(&config).unwrap_or_else(|error| {
            panic!("failed to read Cargo config {}: {error}", config.display())
        });
        let parsed = contents.parse::<toml::Value>().unwrap_or_else(|error| {
            panic!("failed to parse Cargo config {}: {error}", config.display())
        });
        let key = semantic_cargo_config_key(&config, &parsed);
        assert!(
            key.is_none(),
            "trybuild working directory {} discovers Cargo config {} which sets semantic key \
             {:?}; the trybuild child must load no build posture, so run with a temporary \
             directory outside any checkout or remove the override",
            directory.display(),
            config.display(),
            key.unwrap_or_default()
        );
    }
    directory
}

/// Quote `path` as one POSIX `sh` word.
#[cfg(unix)]
fn sh_word(path: &Path) -> String {
    let text = path
        .to_str()
        .unwrap_or_else(|| panic!("trybuild cargo shim path is not UTF-8: {}", path.display()));
    format!("'{}'", text.replace('\'', r"'\''"))
}

/// The shim's text. Everything it depends on is written into it, so the file
/// is content-addressed by what it does. The first half, written here, binds
/// the tools and finds the subcommand; `SHIM_TAIL` is the rest.
#[cfg(unix)]
pub(crate) fn shim_script(
    cargo: &Path,
    driver: CargoDriver,
    rustc: &Path,
    working_directory: &Path,
) -> String {
    let lane = match driver {
        CargoDriver::Targo => "--unverified",
        CargoDriver::Cargo => "",
    };
    let cargo = sh_word(cargo);
    let rustc = sh_word(rustc);
    let working_directory = sh_word(working_directory);
    let compiling = COMPILING_SUBCOMMANDS.join("|");
    let non_compiling = NON_COMPILING_SUBCOMMANDS.join("|");
    format!(
        r#"#!/bin/sh
# trybuild's $CARGO, written by ay-test-support (src/trybuild_lane.rs).
# Generated and content-addressed: do not edit.
set -eu
cargo={cargo}
lane='{lane}'
rustc={rustc}
working_directory={working_directory}
caller_directory=$(pwd -P)

# The subcommand is the first operand that is neither a global option nor the
# value of one.
subcommand=
manifest_named=
option_value=
for argument do
  if [ -n "$subcommand" ]; then
    case $argument in --manifest-path|--manifest-path=*) manifest_named=1 ;; esac
  elif [ -n "$option_value" ]; then
    option_value=
  else
    case $argument in
      --config|--color|-Z|-C) option_value=1 ;;
      -*) ;;
      *) subcommand=$argument ;;
    esac
  fi
done

case $subcommand in
  {compiling}) ;;
  {non_compiling}) lane= ;;
  *)
    printf '%s\n' "ay-test-support trybuild cargo: refusing subcommand '$subcommand'; this shim knows the lane only for {compiling}|{non_compiling}" >&2
    exit 2
    ;;
esac

"#
    ) + SHIM_TAIL
}

/// The half of the shim that depends on nothing it is written with: name the
/// manifest, keep a relative target directory meaning the caller's, move, pin
/// the compiler, run.
#[cfg(unix)]
const SHIM_TAIL: &str = r#"# Cargo runs from the chosen working directory below, so name the manifest the
# caller meant, found as Cargo finds it, directly after the subcommand.
if [ -z "$manifest_named" ]; then
  manifest_directory=$caller_directory
  while [ ! -f "$manifest_directory/Cargo.toml" ]; do
    if [ "$manifest_directory" = / ]; then
      printf '%s\n' "ay-test-support trybuild cargo: no Cargo.toml at or above $caller_directory" >&2
      exit 2
    fi
    manifest_directory=$(dirname "$manifest_directory")
  done
  placed=
  option_value=
  for argument do
    shift
    set -- "$@" "$argument"
    if [ -n "$placed" ]; then
      continue
    elif [ -n "$option_value" ]; then
      option_value=
    else
      case $argument in
        --config|--color|-Z|-C) option_value=1 ;;
        -*) ;;
        *)
          placed=1
          set -- "$@" --manifest-path "$manifest_directory/Cargo.toml"
          ;;
      esac
    fi
  done
fi

# Cargo reads a relative target directory against its working directory, so
# resolve one against the caller's before moving.
case ${CARGO_TARGET_DIR-} in
  ''|/*) ;;
  *) CARGO_TARGET_DIR=$caller_directory/$CARGO_TARGET_DIR; export CARGO_TARGET_DIR ;;
esac
cd "$working_directory"
RUSTC=$rustc
export RUSTC
if [ -n "$lane" ]; then
  exec "$cargo" "$lane" "$@"
fi
exec "$cargo" "$@"
"#;

/// Write `script` to a content-addressed path below the funnel's target root
/// and return it. Concurrent test processes writing the same script race only
/// on an atomic rename of identical bytes.
#[cfg(unix)]
fn publish_shim(target_root: &Path, script: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt as _;

    let mut hasher = Sha256::new();
    hash_component(&mut hasher, b"schema", SHIM_NAMESPACE.as_bytes());
    hash_component(&mut hasher, b"script", script.as_bytes());
    let directory = target_root
        .join(SHIM_NAMESPACE)
        .join(finish_build_identity(hasher));
    filesystem::create_dir_all(&directory).unwrap_or_else(|error| {
        panic!(
            "failed to create trybuild cargo shim directory {}: {error}",
            directory.display()
        )
    });
    let shim = directory.join(SHIM_FILE_NAME);
    let current = filesystem::read(&shim).is_ok_and(|bytes| bytes == script.as_bytes())
        && filesystem::metadata(&shim)
            .is_ok_and(|metadata| metadata.permissions().mode() & 0o777 == 0o755);
    if current {
        return shim;
    }
    let sequence = UNIQUE_PATH_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let staging = directory.join(format!(
        ".{SHIM_FILE_NAME}.{}.{sequence}",
        std::process::id()
    ));
    filesystem::write(&staging, script).unwrap_or_else(|error| {
        panic!(
            "failed to write trybuild cargo shim {}: {error}",
            staging.display()
        )
    });
    filesystem::set_permissions(&staging, filesystem::Permissions::from_mode(0o755))
        .unwrap_or_else(|error| {
            panic!(
                "failed to mark trybuild cargo shim executable {}: {error}",
                staging.display()
            )
        });
    filesystem::rename(&staging, &shim).unwrap_or_else(|error| {
        panic!(
            "failed to publish trybuild cargo shim {}: {error}",
            shim.display()
        )
    });
    shim
}

#[cfg(all(test, unix))]
#[path = "trybuild_lane_tests.rs"]
mod tests;
