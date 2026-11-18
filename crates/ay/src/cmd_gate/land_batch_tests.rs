// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::path::Path;
use std::process::Command;

const PACKAGE: &str = "ay-native-batch-probe";
const SOURCE: &str = r#"
use std::io::Write;
fn record(case: &str) {
    let path = std::env::var_os("AY_GATE_BATCH_MARKERS").unwrap();
    let mut file = std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap();
    let feature = if cfg!(feature = "probe") { "probe" } else { "plain" };
    writeln!(file, "{NAME}:{case}:{feature}").unwrap();
}
#[test]
fn selected() {
    record("selected");
    assert_ne!(NAME, "failure", "deliberate runtime failure");
}
#[test]
fn alternate() { record("alternate"); }
#[test]
fn trap() { panic!("a harness filter was lost"); }
"#;

struct Workspace(tempfile::TempDir);

impl Workspace {
    fn new() -> Self {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        std::fs::create_dir_all(root.join("probe/src")).unwrap();
        std::fs::create_dir(root.join("probe/tests")).unwrap();
        std::fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers=['probe']\nresolver='2'\n",
        )
        .unwrap();
        std::fs::write(
            root.join("Cargo.lock"),
            format!("version = 4\n[[package]]\nname = {PACKAGE:?}\nversion = '0.1.0'\n"),
        )
        .unwrap();
        std::fs::write(root.join("probe/src/lib.rs"), "pub const VALUE: u8 = 1;\n").unwrap();
        let mut manifest = format!("[package]\nname={PACKAGE:?}\nversion='0.1.0'\nedition='2021'\nautotests=false\n[features]\nprobe=[]\n");
        for target in ["alpha", "beta", "failure", "zz_after"] {
            manifest.push_str(&format!(
                "[[test]]\nname={target:?}\npath='tests/{target}.rs'\n"
            ));
            std::fs::write(
                root.join(format!("probe/tests/{target}.rs")),
                format!("const NAME: &str = {target:?};\n{SOURCE}"),
            )
            .unwrap();
        }
        std::fs::write(root.join("probe/Cargo.toml"), manifest).unwrap();
        Self(directory)
    }

    fn root(&self) -> &Path {
        self.0.path()
    }

    fn run(&self, steps: Vec<Step>) -> (bool, usize, Vec<String>) {
        let markers = self.root().join("markers");
        if markers.exists() {
            std::fs::remove_file(&markers).unwrap();
        }
        let mut success = true;
        let mut invocations = 0;
        for step in compatible(steps) {
            // The containing native gate test already retains machine
            // admission. Execute the actual produced Targo payload within
            // that same owned budget, without a nested build-slot request.
            let output = Command::new(&step.args[1])
                .args(&step.args[2..])
                .current_dir(self.root())
                .env("AY_GATE_BATCH_MARKERS", &markers)
                .output()
                .expect("run actual Trust/Targo multi-target fixture");
            invocations += 1;
            if !output.status.success() {
                success = false;
                assert!(
                    String::from_utf8_lossy(&output.stdout).contains("deliberate runtime failure"),
                    "unexpected infrastructure failure: {}\n{}",
                    String::from_utf8_lossy(&output.stderr),
                    String::from_utf8_lossy(&output.stdout)
                );
                break;
            }
        }
        let mut rows = std::fs::read_to_string(markers)
            .unwrap()
            .lines()
            .map(str::to_owned)
            .collect::<Vec<_>>();
        rows.sort();
        (success, invocations, rows)
    }
}

fn selection(target: &str, feature: Option<&str>, filter: &str, no_fail_fast: bool) -> Step {
    let mut args = vec![
        "test".into(),
        "--locked".into(),
        "-p".into(),
        PACKAGE.into(),
        "--test".into(),
        target.into(),
    ];
    if let Some(feature) = feature {
        args.extend(["--features".into(), feature.into()]);
    }
    if no_fail_fast {
        args.push("--no-fail-fast".into());
    }
    args.extend(["--".into(), filter.into()]);
    Step::compiler(args)
}

#[test]
fn quiet_test_build_compiles_without_running_the_selected_failure() {
    let workspace = Workspace::new();
    let markers = workspace.root().join("markers");
    let mut runtime = selection("failure", Some("probe"), "selected", false);
    runtime.args.insert(0, "--exclusive".into());
    let build = runtime.quiet_test_compilation().unwrap();
    // A compiler build for this fixture can use the containing test's admission.
    let output = Command::new(&build.args[1])
        .args(&build.args[2..])
        .current_dir(workspace.root())
        .env("AY_GATE_BATCH_MARKERS", &markers)
        .output()
        .expect("compile the selected Trust/Targo test fixture");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!markers.exists());

    // The fixture has no benchmark planner. Its selected body must fail even
    // after a successful compilation while still honoring the feature/filter.
    runtime.args.remove(0);
    assert_eq!(
        workspace.run(vec![runtime]),
        (false, 1, vec!["failure:selected:probe".into()])
    );
}

#[test]
fn actual_multi_target_workspace_preserves_coverage_features_filters_and_failure() {
    let workspace = Workspace::new();
    let run = |steps| workspace.run(steps);
    assert_eq!(
        run(vec![
            selection("alpha", None, "selected", false),
            selection("beta", None, "selected", false)
        ]),
        (
            true,
            1,
            vec!["alpha:selected:plain".into(), "beta:selected:plain".into()]
        )
    );
    assert_eq!(
        run(vec![
            selection("alpha", None, "selected", false),
            selection("beta", Some("probe"), "selected", false)
        ]),
        (
            true,
            2,
            vec!["alpha:selected:plain".into(), "beta:selected:probe".into()]
        )
    );
    assert_eq!(
        run(vec![
            selection("alpha", None, "selected", false),
            selection("beta", None, "alternate", false)
        ]),
        (
            true,
            2,
            vec!["alpha:selected:plain".into(), "beta:alternate:plain".into()]
        )
    );
    assert_eq!(
        run(vec![
            selection("alpha", None, "selected", false),
            selection("beta", None, "selected", false),
            selection("alpha", None, "selected", false)
        ]),
        (
            true,
            2,
            vec![
                "alpha:selected:plain".into(),
                "alpha:selected:plain".into(),
                "beta:selected:plain".into()
            ]
        )
    );
    assert_eq!(
        run(vec![
            selection("alpha", None, "selected", false),
            selection("failure", None, "selected", false),
            selection("zz_after", None, "selected", false)
        ]),
        (
            false,
            1,
            vec![
                "alpha:selected:plain".into(),
                "failure:selected:plain".into()
            ]
        )
    );
    assert_eq!(
        run(vec![
            selection("failure", None, "selected", true),
            selection("zz_after", None, "selected", true)
        ]),
        (false, 1, vec!["failure:selected:plain".into()])
    );
}
