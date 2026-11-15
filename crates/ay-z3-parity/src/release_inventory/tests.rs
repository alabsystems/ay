// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
use super::*;

#[test]
fn multiline_catalog_escapes_and_refusals() {
    let source = r#"const TEST: &[(&str,&str)] = &[
        ("one", "first"),
        // generated description
        (
          "two", "escaped \"quote\" and \\ slash",
        ),
    ];"#;
    let parsed = catalog(source, "TEST", CatalogKind::Pairs).unwrap();
    assert_eq!(parsed["two"], "escaped \"quote\" and \\ slash");
    for bad in [
        "const TEST: &[(&str,&str)] = &[ ];",
        "const TEST: &[(&str,&str)] = &[(\"a\",\"b\"),(\"a\",\"c\")];",
        "const TEST: &[(&str,&str)] = &[(\"a\",)];",
        "const TEST: &[(&str,&str)] = &[(\"a\",\"b\")",
    ] {
        assert!(catalog(bad, "TEST", CatalogKind::Pairs).is_err(), "{bad}");
    }
    assert!(catalog(
        "const OTHER: &[&str] = &[\"a\"];",
        "TEST",
        CatalogKind::Names
    )
    .is_err());
}

#[test]
fn module_parameter_defaults_and_globals() {
    let parsed = module_parameters("Global parameters\n    timeout (unsigned int) (default: 1)\n[module] smt, description: solver\n    timeout (unsigned int) (default: 2)\n    logic (symbol)\n[module] ff\n    enabled (bool) (default: true)\n    max_prime (unsigned int)\n").unwrap();
    assert_eq!(parsed.len(), 4);
    assert!(parsed.contains_key("smt.timeout"));
    assert!(parsed.contains_key("ff.enabled"));
    assert!(parsed.contains_key("smt.logic"));
    assert!(parsed.contains_key("ff.max_prime"));
    for bad in [
        "",
        "[module] \n",
        "[module] smt\n    bad (bool",
        "[module] smt\n    bad (bool) trailing garbage",
        "[module] smt\n    bad (bool) (default: true",
        "[module] smt\n    a (bool) (default: true)\n    a (bool) (default: false)",
    ] {
        assert!(module_parameters(bad).is_err(), "{bad}");
    }
}

#[cfg(unix)]
#[test]
fn actual_clang_include_graph_enums_and_signature_changes() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(
        dir.path().join("z3.h"),
        "#include \"included.h\"\nint Z3_f(int x);\n",
    )
    .unwrap();
    fs::write(dir.path().join("included.h"), "typedef enum {Z3_FIRST=10, Z3_SECOND, OTHER=50, Z3_AFTER_OTHER, Z3_NEG=-3, Z3_AFTER_NEG} kind;\n#define Z3_TYPED ((kind)(Z3_SECOND + 7))\n#define Z3_TYPED_NEG ( kind ) -7\n#define Z3_NOT_ENUM ((unsigned)99)\n#define Z3_FUNCTION(x) ((kind)(x))\n").unwrap();
    let (before_functions, before_enums) = clang_inventory(dir.path()).unwrap();
    assert_eq!(before_enums["Z3_SECOND"], 11);
    assert_eq!(before_enums["Z3_AFTER_OTHER"], 51);
    assert_eq!(before_enums["Z3_AFTER_NEG"], -2);
    assert_eq!(before_enums["Z3_TYPED"], 18);
    assert_eq!(before_enums["Z3_TYPED_NEG"], -7);
    assert!(!before_enums.contains_key("Z3_NOT_ENUM"));
    assert!(!before_enums.contains_key("Z3_FUNCTION"));
    fs::write(dir.path().join("z3.h"), "typedef enum {Z3_FIRST=10, Z3_NEW, Z3_SECOND} kind;\nlong Z3_f(int x); int Z3_new(void);\n").unwrap();
    let (after_functions, after_enums) = clang_inventory(dir.path()).unwrap();
    let enums = delta(&before_enums, &after_enums);
    assert_eq!(
        enums["changed"]["Z3_SECOND"],
        json!({"ay":11,"upstream":12})
    );
    assert_eq!(enums["missing"]["Z3_NEW"], 11);
    let functions = delta(&before_functions, &after_functions);
    assert_eq!(
        functions["changed"]["Z3_f"],
        json!({"ay":"int (int)","upstream":"long (int)"})
    );
    assert_eq!(functions["missing"]["Z3_new"], "int (void)");
    fs::write(dir.path().join("z3.h"), "#include \"included.h\"\nint Z3_f(int x);\n#undef Z3_TYPED\n#define Z3_TYPED ((kind)unknown_identifier)\n").unwrap();
    assert!(clang_inventory(dir.path()).is_err());
    fs::write(dir.path().join("z3.h"), "this is not C;\n").unwrap();
    assert!(clang_inventory(dir.path()).is_err());
}

#[test]
fn malformed_ast_never_guesses_values_or_signatures() {
    let valid = json!({"kind":"TranslationUnitDecl","inner":[
        {"kind":"FunctionDecl","name":"Z3_f","type":{"qualType":"int (void)"}},
        {"kind":"EnumDecl","inner":[{"kind":"EnumConstantDecl","name":"Z3_ZERO"}]}
    ]});
    assert_eq!(ast_inventory(&valid).unwrap().1["Z3_ZERO"], 0);
    let mut broken = valid.clone();
    broken["inner"][0]["type"] = json!({});
    assert!(ast_inventory(&broken).is_err());
    let mut broken = valid.clone();
    broken["inner"][1]["inner"][0]["inner"] = json!([{"kind":"IntegerLiteral","value":"42"}]);
    assert!(ast_inventory(&broken).is_err());
    let mut broken = valid.clone();
    broken["inner"][1]["inner"][0]["inner"] = json!([{"kind":"ConstantExpr","value":"unknown"}]);
    assert!(ast_inventory(&broken).is_err());
    let mut broken = valid.clone();
    broken["inner"][1]["inner"] = json!([
        {"kind":"EnumConstantDecl","name":"Z3_MAX","inner":[{"kind":"ConstantExpr","value":i64::MAX.to_string()}]},
        {"kind":"EnumConstantDecl","name":"Z3_OVERFLOW"}
    ]);
    assert!(ast_inventory(&broken).is_err());
    assert!(ast_inventory(&json!({"kind":"TranslationUnitDecl","inner":[]})).is_err());
}

#[cfg(unix)]
#[test]
fn bounded_execution_refuses_diagnostics_nonzero_timeout_and_overflow() {
    // Native existing system programs, no generated shell scripts or harnesses.
    let bad = query(
        Path::new("clang"),
        &["-not-a-clang-option".into()],
        b"",
        Duration::from_secs(10),
        1024,
    );
    assert!(bad.is_err());
    let timeout = query(
        Path::new("/bin/sleep"),
        &["10".into()],
        b"",
        Duration::from_millis(25),
        1024,
    );
    assert!(timeout.unwrap_err().contains("deadline"));
    let overflow = query(
        Path::new("/usr/bin/yes"),
        &[],
        b"",
        Duration::from_secs(2),
        1024,
    );
    assert!(overflow.unwrap_err().contains("bound"));
    assert!(observed_catalog("not a catalog").is_err());
    assert!(observed_catalog("- same desc\n- same duplicate\n").is_err());
}

#[test]
fn hashes_cover_compat_wrapper_and_nested_headers() {
    let dir = tempfile::tempdir().unwrap();
    fs::create_dir(dir.path().join("nested")).unwrap();
    fs::write(dir.path().join("z3.h"), "#include \"ay_z3_compat.h\"\n").unwrap();
    fs::write(dir.path().join("ay_z3_compat.h"), "/* original */\n").unwrap();
    fs::write(dir.path().join("nested/other.h"), "/* nested */\n").unwrap();
    let before = headers(dir.path()).unwrap();
    assert_eq!(before.len(), 3);
    assert!(before.contains_key("nested/other.h"));
    fs::write(dir.path().join("ay_z3_compat.h"), "/* changed */\n").unwrap();
    assert_ne!(
        before["ay_z3_compat.h"],
        headers(dir.path()).unwrap()["ay_z3_compat.h"]
    );
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn exited_leader_stays_waitable_until_group_cleanup_and_reap() {
    let child = Command::new("/usr/bin/true")
        .process_group(0)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let mut process = Process { child: Some(child) };
    let started = Instant::now();
    while !process.exited_unreaped().unwrap() {
        assert!(started.elapsed() < Duration::from_secs(5));
        std::thread::sleep(Duration::from_millis(5));
    }
    // A second WNOWAIT observation must still find the same exited leader;
    // consuming observation would instead make waitid fail with ECHILD.
    assert!(process.exited_unreaped().unwrap());
    assert!(process.terminate_and_reap().unwrap().success());
    assert!(process.child.is_none());
    // Cleanup has consumed the authority; neither this call nor Drop can
    // signal the old PGID after the leader's wait status has been consumed.
    assert!(process.terminate_and_reap().is_err());
    assert!(process.exited_unreaped().is_err());
}

// Re-enter the native test binary to create an actual fast-exiting group
// leader with a residual process. No generated helper program or shell script.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn residual_group_fixture() {
    if std::env::var_os("AY_RELEASE_INVENTORY_RESIDUAL_FIXTURE").is_none() {
        return;
    }
    let _descendant = Command::new("/bin/sleep")
        .arg("20")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::inherit())
        .spawn()
        .unwrap();
    // Leave the descendant alive in this process group, holding stderr open.
    std::process::exit(0);
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn exited_leader_cleanup_terminates_residual_group_child() {
    use std::os::fd::OwnedFd;
    use std::os::unix::net::UnixStream;
    let (mut reader, writer) = UnixStream::pair().unwrap();
    reader.set_nonblocking(true).unwrap();
    let child = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "release_inventory::tests::residual_group_fixture",
            "--nocapture",
        ])
        .env("AY_RELEASE_INVENTORY_RESIDUAL_FIXTURE", "1")
        .process_group(0)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::from(OwnedFd::from(writer)))
        .spawn()
        .unwrap();
    let mut process = Process { child: Some(child) };
    let started = Instant::now();
    while !process.exited_unreaped().unwrap() {
        assert!(started.elapsed() < Duration::from_secs(5));
        std::thread::sleep(Duration::from_millis(5));
    }
    let mut byte = [0];
    assert_eq!(
        reader.read(&mut byte).unwrap_err().kind(),
        std::io::ErrorKind::WouldBlock,
        "residual descendant must still hold the stream after leader exit"
    );
    assert!(process.terminate_and_reap().unwrap().success());
    let started = Instant::now();
    loop {
        match reader.read(&mut byte) {
            Ok(0) => break,
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                assert!(
                    started.elapsed() < Duration::from_secs(2),
                    "residual child survived cleanup"
                );
                std::thread::sleep(Duration::from_millis(5));
            }
            result => panic!("unexpected residual stream result: {result:?}"),
        }
    }
    assert!(process.child.is_none());
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn quiescence_requires_two_dead_identity_samples() {
    use ay_sys::supervisor::process_group::{ProcessGroupSample, ProcessIdentity};
    let leader = ProcessIdentity {
        pid: 101,
        parent: 100,
        group: 101,
        birth: 123,
    };
    let child = ProcessIdentity {
        pid: 102,
        parent: 101,
        group: 101,
        birth: 124,
    };
    let sample =
        |members: Vec<ProcessIdentity>, live_members: Vec<ProcessIdentity>| ProcessGroupSample {
            resident_bytes: 0,
            members,
            live_members,
        };
    let first = sample(vec![leader, child], vec![]);
    assert!(samples_prove_quiescence(
        &first,
        &sample(vec![leader, child], vec![])
    ));
    // A known zombie may disappear between complete samples.
    assert!(samples_prove_quiescence(
        &first,
        &sample(vec![leader], vec![])
    ));
    assert!(samples_prove_quiescence(
        &sample(vec![], vec![]),
        &sample(vec![], vec![])
    ));
    assert!(!samples_prove_quiescence(
        &sample(vec![leader, child], vec![child]),
        &sample(vec![leader], vec![])
    ));
    assert!(!samples_prove_quiescence(
        &first,
        &sample(vec![leader, child], vec![child])
    ));
    // Even an already-dead newcomer could have forked after the first walk.
    assert!(!samples_prove_quiescence(
        &sample(vec![leader], vec![]),
        &sample(vec![leader, child], vec![])
    ));
    let changed_birth = ProcessIdentity {
        birth: 125,
        ..child
    };
    assert!(!samples_prove_quiescence(
        &first,
        &sample(vec![leader, changed_birth], vec![])
    ));
    let changed_parent = ProcessIdentity {
        parent: 99,
        ..child
    };
    assert!(!samples_prove_quiescence(
        &first,
        &sample(vec![leader, changed_parent], vec![])
    ));
}
