// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The resolver against toolchain files and fake elans in a temporary
//! directory: never the real elan, never the ambient `PATH`, `HOME` or
//! `ELAN_HOME`.

use super::*;

const PIN: &str = "leanprover/lean4:v4.30.0-rc2";
const PINNED_BANNER: &str =
    "Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2, Release)";

struct Tree {
    root: tempfile::TempDir,
}

impl Tree {
    fn new() -> Self {
        Self {
            root: tempfile::tempdir().expect("temporary directory"),
        }
    }

    fn dir(&self, name: &str) -> PathBuf {
        let dir = self.root.path().join(name);
        std::fs::create_dir_all(&dir).expect("create directory");
        dir
    }

    fn pin(&self, dir: &str, contents: &str) -> PathBuf {
        let file = self.dir(dir).join(TOOLCHAIN_FILE);
        std::fs::write(&file, contents).expect("write lean-toolchain");
        file
    }

    /// An executable `elan` in `dir` that runs `script` (a POSIX sh body).
    fn elan(&self, dir: &str, script: &str) -> PathBuf {
        let path = self.dir(dir).join(ELAN);
        std::fs::write(&path, format!("#!/bin/sh\n{script}")).expect("write fake elan");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
                .expect("make fake elan executable");
        }
        path
    }

    /// A fake elan that knows only `toolchain` and answers
    /// `run <toolchain> lean --version` with `banner`.
    fn elan_serving(&self, dir: &str, toolchain: &str, banner: &str) -> PathBuf {
        self.elan(
            dir,
            &format!(
                "[ \"$1\" = run ] || exit 64\n\
                 [ \"$2\" = '{toolchain}' ] || {{ echo \"error: toolchain '$2' is not installed\" >&2; exit 1; }}\n\
                 [ \"$3\" = lean ] && [ \"$4\" = --version ] || exit 65\n\
                 echo '{banner}'\n"
            ),
        )
    }

    fn sentinel(&self) -> PathBuf {
        self.root.path().join("stub-was-executed")
    }

    fn path(&self, dirs: &[&str]) -> OsString {
        std::env::join_paths(dirs.iter().map(|dir| self.root.path().join(dir)))
            .expect("join fake PATH")
    }

    fn search(&self, elan_home: Option<&str>, home: Option<&str>, path: &[&str]) -> ElanSearch {
        ElanSearch {
            elan_home: elan_home.map(|dir| self.root.path().join(dir).into_os_string()),
            home: home.map(|dir| self.root.path().join(dir).into_os_string()),
            path: Some(self.path(path)),
        }
    }
}

#[test]
fn the_nearest_lean_toolchain_at_or_above_the_start_is_the_pin() {
    let tree = Tree::new();
    let repository_pin = tree.pin("repo", &format!("{PIN}\n"));
    let start = tree.dir("repo/crates/ay-sat");

    assert_eq!(find_toolchain_file(&start), Some(repository_pin.clone()));
    assert_eq!(read_toolchain(&repository_pin), Ok(PIN.to_string()));

    let crate_pin = tree.pin("repo/crates", "leanprover/lean4:v4.31.0");
    assert_eq!(find_toolchain_file(&start), Some(crate_pin.clone()));
    assert_eq!(
        read_toolchain(&crate_pin),
        Ok("leanprover/lean4:v4.31.0".to_string())
    );
}

#[test]
fn a_toolchain_file_names_exactly_one_toolchain() {
    let tree = Tree::new();
    let padded = tree.pin("padded", &format!("\n  {PIN}  \n\n"));
    assert_eq!(read_toolchain(&padded), Ok(PIN.to_string()));
    for (dir, contents) in [("empty", ""), ("blank", " \n\n"), ("two", "a\nb\n")] {
        let file = tree.pin(dir, contents);
        assert!(
            matches!(
                read_toolchain(&file),
                Err(LeanUnavailable::BadToolchainFile { file: ref bad, .. }) if *bad == file
            ),
            "{contents:?} must not read as a pin"
        );
    }
    let missing = tree.root.path().join("absent").join(TOOLCHAIN_FILE);
    assert!(matches!(
        read_toolchain(&missing),
        Err(LeanUnavailable::BadToolchainFile { .. })
    ));
}

#[test]
fn this_repository_pins_a_release_the_version_check_can_name() {
    let file = find_toolchain_file(Path::new(env!("CARGO_MANIFEST_DIR")))
        .expect("the AY repository has a lean-toolchain");
    let toolchain = read_toolchain(&file).expect("the AY lean-toolchain reads as a pin");
    assert!(
        expected_banner_prefix(&toolchain).ends_with(','),
        "{toolchain} is not a release pin, so `lean --version` could not be checked against it"
    );
}

#[test]
fn the_banner_prefix_names_a_release_and_only_a_release() {
    assert_eq!(
        expected_banner_prefix(PIN),
        "Lean (version 4.30.0-rc2,".to_string()
    );
    assert_eq!(
        expected_banner_prefix("v4.8.0"),
        "Lean (version 4.8.0,".to_string()
    );
    for channel in [
        "stable",
        "leanprover/lean4:nightly-2026-01-01",
        "leanprover/lean4:vX",
    ] {
        assert_eq!(
            expected_banner_prefix(channel),
            "Lean (version ".to_string()
        );
    }
    assert!(PINNED_BANNER.starts_with(&expected_banner_prefix(PIN)));
    assert!(!"Lean (version 4.30.0, x)".starts_with(&expected_banner_prefix(PIN)));
}

#[test]
fn the_command_is_elan_run_of_the_named_toolchain_never_a_bare_lean() {
    let tree = Tree::new();
    tree.pin("repo", PIN);
    let elan = tree.elan("elan-home/bin", "exit 0\n");

    let lean = resolve_pinned_lean(
        &tree.dir("repo/crates/ay-sat"),
        &tree.search(Some("elan-home"), None, &[]),
    )
    .expect("resolve the pinned Lean");
    assert_eq!(lean.toolchain(), PIN);
    assert_eq!(lean.elan(), elan);

    let mut command = lean.lean();
    command.arg("proof.lean");
    assert_eq!(command.get_program(), elan.as_os_str());
    let args: Vec<_> = command.get_args().collect();
    assert_eq!(args, ["run", PIN, "lean", "proof.lean"]);

    let lake = lean.command("lake");
    let args: Vec<_> = lake.get_args().collect();
    assert_eq!(args, ["run", PIN, "lake"]);

    let identity = lean.identity();
    assert!(identity.starts_with(PIN), "{identity}");
    assert!(identity.contains(&elan.display().to_string()), "{identity}");
}

#[test]
fn elan_is_found_in_elan_home_then_the_home_default_then_path() {
    let tree = Tree::new();
    let configured = tree.elan("configured/bin", "exit 0\n");
    let default = tree.elan("home/.elan/bin", "exit 0\n");
    let on_path = tree.elan("bin", "exit 0\n");

    let all = tree.search(Some("configured"), Some("home"), &["bin"]);
    assert_eq!(locate_elan(&all), Ok(configured.clone()));

    // A set ELAN_HOME without an elan in it (Homebrew's elan-init keeps the
    // binary elsewhere) falls through rather than failing.
    let unset_home = tree.search(Some("no-such-elan-home"), Some("home"), &["bin"]);
    assert_eq!(locate_elan(&unset_home), Ok(default.clone()));

    let path_only = tree.search(None, Some("empty-home"), &["bin"]);
    assert_eq!(locate_elan(&path_only), Ok(on_path));

    let relative = ElanSearch {
        elan_home: Some(OsString::from("configured")),
        home: None,
        path: Some(OsString::from("bin")),
    };
    assert!(
        locate_elan(&relative).is_err(),
        "relative locations never count"
    );
}

#[test]
fn the_path_walk_passes_over_reroute_directories_and_stub_files_without_running_them() {
    let tree = Tree::new();
    let signature = ay_sys::z3_oracle::REROUTE_STUB_SIGNATURE;
    let touch = format!("touch '{}'\nexit 0\n", tree.sentinel().display());
    let rerouted = tree.elan("reroute", &touch);
    std::fs::write(tree.dir("reroute").join(REROUTE_DIR_MARKER), "aterm\n")
        .expect("mark the reroute directory");
    let stub = tree.elan("unmarked", &format!("{signature}\n{touch}"));
    let real = tree.elan("real", "exit 0\n");

    let search = tree.search(None, None, &["reroute", "unmarked", "real"]);
    assert_eq!(locate_elan(&search), Ok(real));

    let without_real = tree.search(None, None, &["reroute", "unmarked"]);
    assert_eq!(locate_elan(&without_real), Err(vec![rerouted, stub]));
    assert!(
        !tree.sentinel().exists(),
        "locating elan executed a reroute stub"
    );
}

#[test]
fn without_elan_the_failure_names_the_toolchain_and_how_to_install_it() {
    let tree = Tree::new();
    tree.pin("repo", PIN);
    let search = tree.search(Some("elan-home"), Some("home"), &["bin"]);

    let failure = resolve_pinned_lean(&tree.dir("repo"), &search)
        .expect_err("no elan anywhere must not resolve");
    let LeanUnavailable::NoElan {
        toolchain,
        looked_at,
    } = &failure
    else {
        panic!("expected NoElan, got {failure:?}");
    };
    assert_eq!(toolchain, PIN);
    assert_eq!(
        looked_at,
        &[
            tree.root.path().join("elan-home/bin").join(ELAN),
            tree.root.path().join("home/.elan/bin").join(ELAN),
        ]
    );
    let message = failure.to_string();
    assert!(
        message.contains(&format!("pinned Lean toolchain {PIN}")),
        "{message}"
    );
    assert!(
        message.contains(&format!("`elan toolchain install {PIN}`")),
        "{message}"
    );
}

#[test]
fn a_missing_pin_is_reported_as_unpinned() {
    let message = LeanUnavailable::NoToolchainFile {
        start: PathBuf::from("/somewhere"),
    }
    .to_string();
    assert!(message.contains(TOOLCHAIN_FILE), "{message}");
    assert!(message.contains("/somewhere"), "{message}");
}

#[cfg(unix)]
#[test]
fn verify_accepts_the_pinned_release_and_nothing_else() {
    let tree = Tree::new();
    tree.pin("repo", PIN);
    let resolve = |elan_home: &str| {
        resolve_pinned_lean(&tree.dir("repo"), &tree.search(Some(elan_home), None, &[]))
            .expect("resolve against the fake elan")
    };

    tree.elan_serving("pinned/bin", PIN, PINNED_BANNER);
    assert_eq!(resolve("pinned").verify(), Ok(PINNED_BANNER.to_string()));

    tree.elan_serving("other/bin", PIN, "Lean (version 4.31.0, arm64, Release)");
    let wrong = resolve("other")
        .verify()
        .expect_err("another release is not the pin");
    assert!(
        matches!(wrong, LeanUnavailable::NotThePin { .. }),
        "{wrong:?}"
    );
    let message = wrong.to_string();
    assert!(message.contains("4.31.0"), "{message}");
    assert!(
        message.contains(&format!("elan toolchain install {PIN}")),
        "{message}"
    );

    tree.elan_serving("missing/bin", "leanprover/lean4:v4.8.0", PINNED_BANNER);
    let absent = resolve("missing")
        .verify()
        .expect_err("an uninstalled pin cannot run");
    let message = absent.to_string();
    assert!(message.contains("is not installed"), "{message}");
    assert!(
        message.contains(&format!("elan toolchain install {PIN}")),
        "{message}"
    );
}
