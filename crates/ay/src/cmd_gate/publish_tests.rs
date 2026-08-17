// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::fs;

use tempfile::TempDir;

use super::*;

fn write_policy_fixture(config: &str, shim: &str) -> TempDir {
    let repo = TempDir::new().expect("temporary repository");
    let publish = repo.path().join("publish");
    fs::create_dir(&publish).expect("create publication policy directory");
    fs::write(publish.join("config.sh"), config).expect("write publication config");
    fs::write(publish.join("publish.sh"), shim).expect("write publication shim");
    repo
}

fn canonical_shim() -> &'static str {
    "#!/usr/bin/env bash\ncd \"$HERE\" && exec \"$ENGINE/bin/pub\" \"$@\"\n"
}

#[test]
fn policy_wiring_accepts_pinned_config_and_central_driver_shim() {
    let repo = write_policy_fixture(
        concat!(
            "CHECK_CMD_DEFAULT=\"",
            "cargo check --locked --workspace --all-targets --all-features",
            " && cargo test --locked -p ay-proof-common --lib\"\n",
        ),
        canonical_shim(),
    );

    assert!(
        !repo.path().join(".github").exists(),
        "local publication wiring must not require hosted CI"
    );
    check_policy_wiring(repo.path())
        .expect("flat pinned config and central-driver shim should be accepted");
}

#[test]
fn policy_wiring_rejects_non_flat_or_duplicate_check_commands() {
    for (case, config) in [
        (
            "shell default expression",
            format!(": \"${{CHECK_CMD_DEFAULT:={REQUIRED_CHECK}}}\"\n"),
        ),
        (
            "leading whitespace",
            format!(" CHECK_CMD_DEFAULT=\"{REQUIRED_CHECK}\"\n"),
        ),
        (
            "commented assignment",
            format!("# CHECK_CMD_DEFAULT=\"{REQUIRED_CHECK}\"\n"),
        ),
        (
            "duplicate assignment",
            format!(
                "CHECK_CMD_DEFAULT=\"{REQUIRED_CHECK}\"\nCHECK_CMD_DEFAULT=\"{REQUIRED_CHECK}\"\n"
            ),
        ),
    ] {
        let repo = write_policy_fixture(&config, canonical_shim());
        let error = check_policy_wiring(repo.path())
            .expect_err("non-flat or duplicate publication config must fail closed");
        assert!(
            format!("{error:#}").contains("exactly one flat CHECK_CMD_DEFAULT"),
            "unexpected wiring error for {case}: {error:#}"
        );
    }
}

#[test]
fn policy_wiring_rejects_empty_or_incomplete_check_commands() {
    for (case, config, expected) in [
        (
            "empty command",
            "CHECK_CMD_DEFAULT=\"\"\n".to_string(),
            "must not be empty",
        ),
        (
            "partial workspace command",
            "CHECK_CMD_DEFAULT=\"cargo check --locked --workspace\"\n".to_string(),
            "all targets, and all features",
        ),
    ] {
        let repo = write_policy_fixture(&config, canonical_shim());
        let error = check_policy_wiring(repo.path())
            .expect_err("empty or incomplete publication check must fail closed");
        assert!(
            format!("{error:#}").contains(expected),
            "unexpected wiring error for {case}: {error:#}"
        );
    }
}

#[test]
fn policy_wiring_rejects_noncanonical_driver_delegation() {
    let config = format!("CHECK_CMD_DEFAULT=\"{REQUIRED_CHECK}\"\n");
    for (case, shim) in [
        (
            "commented delegation",
            "# cd \"$HERE\" && exec \"$ENGINE/bin/pub\" \"$@\"\n",
        ),
        (
            "engine script bypass",
            "exec \"$ENGINE/engine/publish.sh\" \"$@\"\n",
        ),
        (
            "argument suffix",
            "cd \"$HERE\" && exec \"$ENGINE/bin/pub\" \"$@\" --check\n",
        ),
    ] {
        let repo = write_policy_fixture(&config, shim);
        let error = check_policy_wiring(repo.path())
            .expect_err("noncanonical publication shim must fail closed");
        assert!(
            format!("{error:#}").contains("$ENGINE/bin/pub"),
            "unexpected wiring error for {case}: {error:#}"
        );
    }
}

#[test]
fn gate_uses_direct_quality_checks_and_full_publication_check() {
    let steps = external_steps("HEAD~1..HEAD");
    for expected in ["code_quality", "rustfmt", "clippy", "python_zero_skip"] {
        assert!(
            steps.iter().any(|step| step.name == expected),
            "publish gate is missing {expected}"
        );
    }
    let doctests = steps
        .iter()
        .find(|step| step.name == "doctests")
        .expect("publish gate must run doctests");
    assert_eq!(doctests.program, "cargo");
    assert_eq!(doctests.args, ["test", "--locked", "--workspace", "--doc"]);

    let publication = steps
        .last()
        .expect("publish gate must run the canonical publication check last");
    assert_eq!(publication.name, "publication_check");
    assert_eq!(publication.program, SHIM_PATH);
    assert_eq!(publication.args, ["check", "ay", "--check"]);
}

#[test]
fn required_assets_use_local_policy_and_pinned_toolchain() {
    for required in [
        CONFIG_PATH,
        SHIM_PATH,
        "publish/manifest.txt",
        "publish/transforms.sh",
        "rust-toolchain.toml",
    ] {
        assert!(
            REQUIRED_ASSETS.contains(&required),
            "release assets must include {required}"
        );
    }
    assert!(
        REQUIRED_ASSETS.iter().all(|path| {
            !path.starts_with(".github/workflows/") && *path != "scripts/check_api_docs.sh"
        }),
        "release assets must not depend on hosted CI or a missing wrapper"
    );
}
