// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The resolver against fakes written to a temporary directory: never the real
//! z3, never the ambient `PATH` or `Z3_PATH`.

use super::*;

#[test]
fn a_real_banner_identifies_and_nothing_else_does() {
    assert_eq!(
        z3_version_banner(true, "Z3 version 4.16.0 - 64 bit\n"),
        Some("Z3 version 4.16.0 - 64 bit")
    );
    assert_eq!(
        z3_version_banner(true, "\nZ3 version 4.8.12 - 64 bit\n"),
        Some("Z3 version 4.8.12 - 64 bit")
    );
    // The aterm refusal shape, a failing real banner, a successful impostor,
    // usage text, and a banner that is not the first line.
    assert_eq!(z3_version_banner(false, ""), None);
    assert_eq!(
        z3_version_banner(false, "Z3 version 4.16.0 - 64 bit\n"),
        None
    );
    assert_eq!(z3_version_banner(true, ""), None);
    assert_eq!(z3_version_banner(true, "cvc5 version 1.0.8\n"), None);
    assert_eq!(z3_version_banner(true, "usage: z3 [options]\n"), None);
    assert_eq!(
        z3_version_banner(true, "warning\nZ3 version 4.16.0 - 64 bit\n"),
        None
    );
}

#[test]
fn banner_versions_parse() {
    assert_eq!(
        parse_banner_version("Z3 version 4.8.12 - 64 bit"),
        Some((4, 8, 12))
    );
    assert_eq!(
        parse_banner_version("Z3 version 4.15 - 64 bit"),
        Some((4, 15, 0))
    );
    assert_eq!(parse_banner_version("not z3"), None);
}

#[test]
fn a_bare_name_is_not_a_path() {
    assert!(!names_a_path(Path::new("z3")));
    assert!(names_a_path(Path::new("./z3")));
    assert!(names_a_path(Path::new("bin/z3")));
    assert!(names_a_path(Path::new("/opt/homebrew/bin/z3")));
}

#[cfg(unix)]
mod fakes {
    use super::*;
    use std::os::unix::fs::PermissionsExt as _;

    /// What a fake `z3` does.
    enum Fake {
        /// Real z3's shape: the banner, and an error for `--z3-mode`.
        Z3(&'static str),
        /// aterm's refusal: exit 2, empty stdout, the reason on stderr.
        Refusing,
        /// Exits 0 without a banner.
        Silent,
        /// AY under the name z3: a banner for `--version` AND for
        /// `--z3-mode --version`.
        Impostor,
        /// A banner for `--z3-mode --version` too, but a failing exit there:
        /// the control must refuse on the banner, not on the exit code.
        ImpostorFailingControl,
        /// An aterm reroute stub file (its second line is the signature) that
        /// leaves `sentinel` behind if it is ever executed.
        Stub,
    }

    struct Scratch {
        root: tempfile::TempDir,
    }

    impl Scratch {
        fn new() -> Self {
            Self {
                root: tempfile::tempdir().expect("temporary directory"),
            }
        }

        fn dir(&self, name: &str) -> PathBuf {
            let dir = self.root.path().join(name);
            std::fs::create_dir_all(&dir).expect("create fake PATH directory");
            dir
        }

        fn sentinel(&self) -> PathBuf {
            self.root.path().join("stub-was-executed")
        }

        fn install(&self, dir: &str, fake: Fake) -> PathBuf {
            let script = match fake {
                Fake::Z3(banner) => format!(
                    "#!/bin/sh\ncase \"$1\" in\n  --version) echo '{banner}'; exit 0;;\n  \
                     --z3-mode) echo 'Error: invalid command line option: --z3-mode'; exit 109;;\n\
                     esac\necho sat\n"
                ),
                Fake::Refusing => {
                    "#!/bin/sh\necho \"'z3' is refused by name\" >&2\nexit 2\n".to_string()
                }
                Fake::Silent => "#!/bin/sh\nexit 0\n".to_string(),
                Fake::Impostor => {
                    "#!/bin/sh\necho 'Z3 version 5.1.0 - 64 bit'\nexit 0\n".to_string()
                }
                Fake::ImpostorFailingControl => "#!/bin/sh\necho 'Z3 version 5.1.0 - 64 bit'\n\
                     [ \"$1\" = --z3-mode ] && exit 3\nexit 0\n"
                    .to_string(),
                Fake::Stub => format!(
                    "#!/bin/sh\n{REROUTE_STUB_SIGNATURE}\ntouch '{}'\n\
                     echo 'Z3 version 5.1.0 - 64 bit'\nexit 0\n",
                    self.sentinel().display()
                ),
            };
            let path = self.dir(dir).join("z3");
            std::fs::write(&path, script).expect("write fake z3");
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
                .expect("make fake z3 executable");
            path
        }

        fn mark_reroute_dir(&self, dir: &str) {
            std::fs::write(self.dir(dir).join(REROUTE_DIR_MARKER), "aterm\n")
                .expect("write reroute marker");
        }

        fn path(&self, dirs: &[&str]) -> OsString {
            std::env::join_paths(dirs.iter().map(|dir| self.root.path().join(dir)))
                .expect("join fake PATH")
        }
    }

    fn resolve(z3_path: Option<&Path>, path: &OsString) -> Result<Z3Oracle, Z3Unavailable> {
        resolve_z3(z3_path.map(Path::as_os_str), Some(path.as_os_str()))
    }

    #[test]
    fn a_refusing_stub_directory_ahead_of_a_real_z3_resolves_to_the_z3_by_path() {
        let scratch = Scratch::new();
        let stub = scratch.install("reroute", Fake::Refusing);
        scratch.mark_reroute_dir("reroute");
        let real = scratch.install("real", Fake::Z3("Z3 version 4.16.0 - 64 bit"));

        let oracle = resolve(None, &scratch.path(&["reroute", "real"])).expect("resolve fake z3");

        assert_eq!(oracle.path(), real);
        assert!(oracle.path().is_absolute());
        assert_eq!(oracle.banner(), "Z3 version 4.16.0 - 64 bit");
        assert_eq!(oracle.version(), Some((4, 16, 0)));
        assert_eq!(oracle.source(), Z3Source::PathSearch);
        assert_eq!(oracle.passed_over().len(), 1);
        assert_eq!(oracle.passed_over()[0].path, stub);
        let identity = oracle.identity();
        assert!(
            identity.starts_with("Z3 version 4.16.0 - 64 bit ("),
            "{identity}"
        );
        assert!(identity.contains(&real.display().to_string()), "{identity}");
        assert!(identity.contains("via PATH"), "{identity}");
        assert!(identity.contains(REROUTE_DIR_MARKER), "{identity}");

        let output = oracle.command().output().expect("run the resolved fake");
        assert_eq!(String::from_utf8_lossy(&output.stdout), "sat\n");
    }

    #[test]
    fn a_stub_file_without_the_marker_is_skipped_by_its_signature_and_never_run() {
        let scratch = Scratch::new();
        let stub = scratch.install("unmarked", Fake::Stub);
        let real = scratch.install("real", Fake::Z3("Z3 version 4.16.0 - 64 bit"));

        let oracle = resolve(None, &scratch.path(&["unmarked", "real"])).expect("resolve fake z3");

        assert_eq!(oracle.path(), real);
        assert_eq!(
            oracle.passed_over(),
            [PassedOver {
                path: stub,
                reason: "aterm reroute stub".to_string()
            }]
        );
        assert!(
            !scratch.sentinel().exists(),
            "the resolver executed a reroute stub"
        );
    }

    #[test]
    fn a_refusing_program_without_the_stub_markers_is_probed_rejected_and_passed_over() {
        let scratch = Scratch::new();
        let refusing = scratch.install("refusing", Fake::Refusing);
        let real = scratch.install("real", Fake::Z3("Z3 version 4.8.12 - 64 bit"));

        let oracle = resolve(None, &scratch.path(&["refusing", "real"])).expect("resolve fake z3");

        assert_eq!(oracle.path(), real);
        assert_eq!(oracle.passed_over().len(), 1);
        assert_eq!(oracle.passed_over()[0].path, refusing);
        assert!(oracle.passed_over()[0]
            .reason
            .contains("did not print a Z3 banner"));
    }

    #[test]
    fn a_program_that_exits_zero_without_the_banner_is_not_z3() {
        let scratch = Scratch::new();
        let silent = scratch.install("silent", Fake::Silent);

        let error =
            resolve(None, &scratch.path(&["silent"])).expect_err("a silent program is not z3");

        let Z3Unavailable::NotFound { passed_over } = &error else {
            panic!("expected NotFound, got {error:?}");
        };
        assert_eq!(passed_over.len(), 1);
        assert_eq!(passed_over[0].path, silent);
        assert!(error.to_string().contains("identifies as z3"), "{error}");
    }

    #[test]
    fn an_ay_drop_in_answering_the_negative_control_with_a_banner_is_refused() {
        let scratch = Scratch::new();
        scratch.install("impostor", Fake::Impostor);

        let error = resolve(None, &scratch.path(&["impostor"])).expect_err("an impostor is not z3");

        let Z3Unavailable::NotFound { passed_over } = error else {
            panic!("expected NotFound");
        };
        assert!(
            passed_over[0].reason.contains("AY drop-in"),
            "{passed_over:?}"
        );
    }

    #[test]
    fn a_banner_in_a_failing_negative_control_is_still_refused() {
        let scratch = Scratch::new();
        scratch.install("impostor", Fake::ImpostorFailingControl);

        let error = resolve(None, &scratch.path(&["impostor"]))
            .expect_err("a banner under --z3-mode is not z3, whatever the exit code");

        let Z3Unavailable::NotFound { passed_over } = error else {
            panic!("expected NotFound");
        };
        assert!(
            passed_over[0].reason.contains("AY drop-in"),
            "{passed_over:?}"
        );
    }

    #[test]
    fn z3_path_wins_over_path() {
        let scratch = Scratch::new();
        scratch.install("on-path", Fake::Z3("Z3 version 4.16.0 - 64 bit"));
        let configured = scratch.install("configured", Fake::Z3("Z3 version 4.8.12 - 64 bit"));

        let oracle =
            resolve(Some(&configured), &scratch.path(&["on-path"])).expect("resolve Z3_PATH");

        assert_eq!(oracle.path(), configured);
        assert_eq!(oracle.banner(), "Z3 version 4.8.12 - 64 bit");
        assert_eq!(oracle.source(), Z3Source::Z3PathEnv);
        assert!(oracle.identity().contains("via Z3_PATH"));
        // An empty Z3_PATH is unset.
        let unset = resolve_z3(
            Some(OsStr::new("")),
            Some(scratch.path(&["on-path"]).as_os_str()),
        )
        .expect("empty Z3_PATH falls through to PATH");
        assert_eq!(unset.source(), Z3Source::PathSearch);
    }

    #[test]
    fn a_wrong_z3_path_is_misconfigured_and_never_falls_back_to_path() {
        let scratch = Scratch::new();
        scratch.install("on-path", Fake::Z3("Z3 version 4.16.0 - 64 bit"));
        let fallback = scratch.path(&["on-path"]);
        let impostor = scratch.install("impostor", Fake::Impostor);
        let stub = scratch.install("stub", Fake::Stub);

        for value in [
            OsString::from("z3"),
            impostor.into_os_string(),
            stub.into_os_string(),
            scratch.root.path().join("missing/z3").into_os_string(),
        ] {
            let error = resolve_z3(Some(&value), Some(&fallback))
                .expect_err("a wrong Z3_PATH must not resolve");
            assert!(error.is_misconfigured(), "{value:?}: {error:?}");
        }
        assert!(
            !scratch.sentinel().exists(),
            "Z3_PATH executed a reroute stub"
        );
    }

    #[test]
    fn empty_relative_and_non_executable_entries_are_skipped() {
        let scratch = Scratch::new();
        let relative_dir = scratch.dir("relative");
        let relative_z3 = scratch.install("relative", Fake::Z3("Z3 version 4.16.0 - 64 bit"));
        let not_executable = scratch.dir("plain").join("z3");
        std::fs::write(
            &not_executable,
            "#!/bin/sh\necho 'Z3 version 4.16.0 - 64 bit'\n",
        )
        .expect("write non-executable z3");
        std::fs::set_permissions(&not_executable, std::fs::Permissions::from_mode(0o644))
            .expect("drop the execute bits");
        let real = scratch.install("real", Fake::Z3("Z3 version 4.16.0 - 64 bit"));

        // The same directory spelled relative to the working directory: the
        // stub's passthrough skips relative entries, and so must the resolver.
        let cwd = std::env::current_dir().expect("current directory");
        let relative = PathBuf::from("../".repeat(cwd.components().count())).join(
            relative_dir
                .strip_prefix("/")
                .expect("absolute temporary directory"),
        );
        assert!(
            relative.join("z3").is_file(),
            "relative spelling must reach the fake"
        );
        assert!(relative_z3.is_file());
        let path = std::env::join_paths([
            PathBuf::new(),
            relative,
            scratch.dir("plain"),
            scratch.dir("real"),
        ])
        .expect("join fake PATH");

        let oracle = resolve(None, &path).expect("resolve past the skipped entries");
        assert_eq!(oracle.path(), real);
        assert!(
            oracle.passed_over().is_empty(),
            "{:?}",
            oracle.passed_over()
        );
    }

    #[test]
    fn nothing_on_path_is_not_found() {
        let scratch = Scratch::new();
        scratch.dir("empty");
        let error = resolve(None, &scratch.path(&["empty"])).expect_err("nothing to find");
        assert_eq!(
            error,
            Z3Unavailable::NotFound {
                passed_over: Vec::new()
            }
        );
        assert!(!error.is_misconfigured());
        assert_eq!(
            resolve_z3(None, None),
            Err(Z3Unavailable::NotFound {
                passed_over: Vec::new()
            })
        );
    }

    #[test]
    fn an_explicit_program_is_a_path_or_a_stub_skipping_lookup() {
        let scratch = Scratch::new();
        scratch.install("reroute", Fake::Refusing);
        scratch.mark_reroute_dir("reroute");
        let real = scratch.install("real", Fake::Z3("Z3 version 4.16.0 - 64 bit"));
        let path = scratch.path(&["reroute", "real"]);

        let by_name = resolve_z3_program(OsStr::new("z3"), Some(&path)).expect("bare name");
        assert_eq!(by_name.path(), real);
        let by_path = resolve_z3_program(real.as_os_str(), None).expect("explicit path");
        assert_eq!(by_path.source(), Z3Source::Explicit);
        assert!(resolve_z3_program(OsStr::new("z3"), None).is_err());
    }
}
