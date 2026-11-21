// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ay's runners leave nothing beside a corpus (DC-77).
//!
//! On 18 November 2026, 49.8 GiB of default proofs sat beside benchmark inputs:
//! every UNSAT a sweep solved wrote `<input>.drat` or `<input>.alethe` next to
//! it, and a run killed mid-write left its transaction files there too.
//! `--proof-store DIR` sends the default proof, and every file its transaction
//! makes, to `DIR/<input sha256>-<ay build>/`; every proof ay writes carries a
//! label naming the input's sha256 and ay's build. The sibling default stays
//! for people.

#[cfg(unix)]
mod unix_tests {
    use ay::proof_store::{
        build_identity, read_label_at, sha256_file, ProofLabel, CACHEDIR_TAG_SIGNATURE, COMPANIONS,
        SIDECAR_PAIRS, STORE_TAG_NAME, TRANSACTION_LEFTOVERS,
    };
    use ntest::timeout;
    use std::collections::BTreeMap;
    use std::fs;
    use std::io::{BufWriter, Write as _};
    use std::os::unix::process::CommandExt as _;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Output, Stdio};
    use std::time::{Duration, Instant};
    use wait_timeout::ChildExt as _;

    /// Pigeonhole: `holes + 1` pigeons in `holes` holes, UNSAT.
    fn write_pigeonhole(path: &Path, holes: usize) {
        let pigeons = holes + 1;
        let var = |pigeon: usize, hole: usize| pigeon * holes + hole + 1;
        let mut clauses = Vec::new();
        for pigeon in 0..pigeons {
            clauses.push(
                (0..holes)
                    .map(|hole| var(pigeon, hole).to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
            );
        }
        for hole in 0..holes {
            for a in 0..pigeons {
                for b in a + 1..pigeons {
                    clauses.push(format!("-{} -{}", var(a, hole), var(b, hole)));
                }
            }
        }
        let mut text = format!("p cnf {} {}\n", pigeons * holes, clauses.len());
        for clause in clauses {
            text.push_str(&clause);
            text.push_str(" 0\n");
        }
        fs::write(path, text).expect("write pigeonhole CNF");
    }

    /// Random 3-SAT at the phase transition, large enough that a solve runs
    /// for minutes: the run the sweep is killed in.
    fn write_hard_random_3sat(path: &Path) {
        const VARIABLES: u64 = 600;
        const CLAUSES: u64 = 2_556; // 600 * 4.26
        let mut out = BufWriter::new(fs::File::create(path).expect("create CNF"));
        writeln!(out, "p cnf {VARIABLES} {CLAUSES}").expect("header");
        let mut state: u64 = 0x2026_1118;
        let mut next = || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            state >> 33
        };
        for _ in 0..CLAUSES {
            let mut picked = Vec::with_capacity(3);
            while picked.len() < 3 {
                let variable = next() % VARIABLES + 1;
                if !picked.contains(&variable) {
                    picked.push(variable);
                }
            }
            for variable in picked {
                let literal = if next() & 1 == 0 {
                    variable as i64
                } else {
                    -(variable as i64)
                };
                write!(out, "{literal} ").expect("literal");
            }
            writeln!(out, "0").expect("clause end");
        }
        out.flush().expect("flush CNF");
    }

    const CONTRADICTION_SMT2: &str = "(set-logic QF_UF)\n\
        (declare-const p Bool)\n\
        (assert p)\n\
        (assert (not p))\n\
        (check-sat)\n";

    const SAFE_HORN_SMT2: &str = "(set-logic HORN)\n\
        (declare-fun inv (Int) Bool)\n\
        (assert (forall ((x Int)) (=> (= x 0) (inv x))))\n\
        (assert (forall ((x Int)) (=> (and (inv x) (< x 10)) (inv (+ x 1)))))\n\
        (assert (forall ((x Int)) (=> (and (inv x) (> x 10)) false)))\n\
        (check-sat)\n";

    /// Every name in `dir` with its bytes.
    fn snapshot(dir: &Path) -> BTreeMap<String, Vec<u8>> {
        fs::read_dir(dir)
            .expect("list corpus")
            .map(|entry| {
                let entry = entry.expect("corpus entry");
                let name = entry.file_name().to_string_lossy().into_owned();
                let bytes = fs::read(entry.path()).unwrap_or_else(|error| {
                    panic!("{name} beside the corpus is not a plain file: {error}")
                });
                (name, bytes)
            })
            .collect()
    }

    /// Every name in `dir`.
    fn names(dir: &Path) -> Vec<String> {
        let mut names: Vec<String> = fs::read_dir(dir)
            .expect("list")
            .flatten()
            .map(|entry| entry.file_name().to_string_lossy().into_owned())
            .collect();
        names.sort();
        names
    }

    fn ay() -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
        command.stdin(Stdio::null());
        command
    }

    fn solve(store: &Path, input: &Path) -> Output {
        let output = ay()
            .arg("--proof-store")
            .arg(store)
            .args(["--timeout", "60000"])
            .arg(input)
            .output()
            .expect("run ay");
        assert!(
            output.status.code().is_some(),
            "ay on {} died: {:?}\n{}",
            input.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        output
    }

    fn stdout(output: &Output) -> String {
        String::from_utf8_lossy(&output.stdout).into_owned()
    }

    fn stderr(output: &Output) -> String {
        String::from_utf8_lossy(&output.stderr).into_owned()
    }

    /// Whether `name` is one of the companion or transaction names ay
    /// declares for some proof in `proof_names`.
    fn is_declared_leftover(name: &str, proof_names: &[String]) -> bool {
        COMPANIONS
            .iter()
            .chain(TRANSACTION_LEFTOVERS)
            .any(|leftover| {
                let candidates: Vec<String> = if leftover.pattern.contains("{P}") {
                    proof_names
                        .iter()
                        .map(|proof| leftover.pattern.replace("{P}", proof))
                        .collect()
                } else {
                    vec![leftover.pattern.to_string()]
                };
                candidates
                    .iter()
                    .any(|pattern| matches_numbered(pattern, name))
            })
    }

    /// `pattern` with `{pid}` and `{n}` standing for runs of digits.
    fn matches_numbered(pattern: &str, name: &str) -> bool {
        let mut rest = name;
        let mut parts = pattern.split('{').peekable();
        let first = parts.next().unwrap_or("");
        let Some(after) = rest.strip_prefix(first) else {
            return false;
        };
        rest = after;
        for part in parts {
            let (placeholder, literal) = part.split_once('}').unwrap_or((part, ""));
            assert!(matches!(placeholder, "pid" | "n"), "{pattern}");
            let digits = rest.chars().take_while(char::is_ascii_digit).count();
            if digits == 0 {
                return false;
            }
            let Some(after) = rest[digits..].strip_prefix(literal) else {
                return false;
            };
            rest = after;
        }
        rest.is_empty()
    }

    fn proof_names(inputs: &[String]) -> Vec<String> {
        inputs
            .iter()
            .flat_map(|input| {
                SIDECAR_PAIRS
                    .iter()
                    .map(move |pair| format!("{input}.{}", pair.proof_extension))
            })
            .collect()
    }

    /// Kill `child`'s whole process group, as a sweep runner's hard stop does.
    fn kill_group(child: &mut std::process::Child) {
        let status = Command::new("kill")
            .args(["-s", "KILL", "--", &format!("-{}", child.id())])
            .status()
            .expect("signal the run's process group");
        assert!(status.success(), "kill -KILL reached the group");
        child
            .wait_timeout(Duration::from_secs(30))
            .expect("reap the killed run")
            .expect("a SIGKILLed run exits");
    }

    /// The DC-77 exit test.
    #[test]
    #[timeout(600_000)]
    fn a_killed_proof_store_sweep_leaves_the_corpus_unchanged_and_every_proof_labelled() {
        let dir = tempfile::tempdir().expect("tempdir");
        let corpus = dir.path().join("corpus");
        let store = dir.path().join("proof-store");
        fs::create_dir(&corpus).expect("corpus");
        write_pigeonhole(&corpus.join("php5.cnf"), 5);
        write_pigeonhole(&corpus.join("php4.dimacs"), 4);
        fs::write(corpus.join("contradiction.smt2"), CONTRADICTION_SMT2).expect("smt2");
        fs::write(corpus.join("safe.smt2"), SAFE_HORN_SMT2).expect("horn");
        write_hard_random_3sat(&corpus.join("hard.cnf"));
        let before = snapshot(&corpus);

        // The sweep: each input in turn, the last one killed mid-run.
        for name in ["php5.cnf", "php4.dimacs", "contradiction.smt2", "safe.smt2"] {
            let output = solve(&store, &corpus.join(name));
            if name != "safe.smt2" {
                assert_eq!(
                    stdout(&output).lines().find(|line| !line.starts_with('c')),
                    Some(if name.ends_with("smt2") {
                        "unsat"
                    } else {
                        "s UNSATISFIABLE"
                    }),
                    "{name}: {}",
                    stderr(&output)
                );
            }
        }
        let hard = corpus.join("hard.cnf");
        let hard_slot = store.join(format!(
            "{}-{}",
            sha256_file(&hard).expect("hash hard.cnf"),
            build_identity()
        ));
        let mut child = ay()
            .arg("--proof-store")
            .arg(&store)
            .args(["--timeout", "600000"])
            .arg(&hard)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .process_group(0)
            .spawn()
            .expect("spawn the run the sweep is killed in");
        let deadline = Instant::now() + Duration::from_secs(60);
        let mut staged = false;
        while Instant::now() < deadline && !staged {
            staged = fs::read_dir(&hard_slot).is_ok_and(|entries| {
                entries.flatten().any(|entry| {
                    let name = entry.file_name().to_string_lossy().into_owned();
                    // Linux stages on an anonymous inode, which has no name
                    // here; the status marker's lock is the run's first name.
                    name.starts_with(".ay-dimacs-proof-") || name.ends_with(".ay-status.lock")
                })
            });
            std::thread::sleep(Duration::from_millis(20));
        }
        assert!(
            staged,
            "the killed run started its proof transaction in its slot"
        );
        std::thread::sleep(Duration::from_millis(500));
        assert!(
            child.try_wait().expect("poll the run").is_none(),
            "the run is still solving when the sweep is killed"
        );
        kill_group(&mut child);

        // The corpus is byte-identical: no proof, no transaction file beside it.
        assert_eq!(snapshot(&corpus), before, "the corpus changed");

        // The store is tagged, and holds only slots named by input and build.
        let tag = fs::read_to_string(store.join(STORE_TAG_NAME)).expect("CACHEDIR.TAG");
        assert!(tag.starts_with(CACHEDIR_TAG_SIGNATURE), "{tag}");
        let inputs: Vec<String> = before.keys().cloned().collect();
        let proofs = proof_names(&inputs);
        let mut labelled = Vec::new();
        for slot in fs::read_dir(&store).expect("list store").flatten() {
            let slot_name = slot.file_name().to_string_lossy().into_owned();
            if slot_name == STORE_TAG_NAME {
                continue;
            }
            let (sha256, build) = slot_name
                .split_once('-')
                .unwrap_or_else(|| panic!("{slot_name} is not <sha256>-<build>"));
            assert_eq!(build, build_identity(), "{slot_name}");
            let input = inputs
                .iter()
                .find(|input| sha256_file(&corpus.join(input)).expect("hash") == sha256)
                .unwrap_or_else(|| panic!("slot {slot_name} names no corpus input"));
            for entry in fs::read_dir(slot.path()).expect("list slot").flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                let path = entry.path();
                if proofs.contains(&name) {
                    // A published proof: labelled, the label written on this
                    // very file, naming its input and build and its own bytes.
                    let label: ProofLabel = read_label_at(&path)
                        .expect("read label")
                        .unwrap_or_else(|| panic!("{} carries no label", path.display()));
                    assert_eq!(label.maker, "ay");
                    assert_eq!(label.class, "cache");
                    assert_eq!(&label.input, input, "{name}");
                    assert!(name.starts_with(&format!("{input}.")), "{name}");
                    assert_eq!(label.input_sha256, sha256, "{name}");
                    assert_eq!(label.build, build_identity(), "{name}");
                    assert!(
                        label
                            .sits_on(&fs::File::open(&path).expect("open"))
                            .expect("stat"),
                        "{name}'s label was written on it"
                    );
                    assert_eq!(
                        label.proof_sha256.as_deref(),
                        Some(sha256_file(&path).expect("hash proof").as_str()),
                        "{name}'s label records its bytes"
                    );
                    labelled.push(name);
                } else {
                    assert!(
                        is_declared_leftover(&name, &proofs),
                        "{} is not a name `ay proof sidecars` declares",
                        path.display()
                    );
                    if name.starts_with(".ay-dimacs-proof-") && entry.path().is_file() {
                        // The killed run's unpublished proof says what it is.
                        let label = read_label_at(&path)
                            .expect("read label")
                            .unwrap_or_else(|| panic!("{} carries no label", path.display()));
                        assert_eq!(label.input_sha256, sha256);
                        assert_eq!(label.proof_sha256, None, "never published");
                    }
                }
            }
        }
        for proof in [
            "php5.cnf.drat",
            "php4.dimacs.drat",
            "contradiction.smt2.alethe",
        ] {
            assert!(
                labelled.iter().any(|name| name == proof),
                "{proof} is in the store: {labelled:?}"
            );
        }
    }

    #[test]
    #[timeout(120_000)]
    fn the_sibling_default_stays_for_people_and_is_labelled() {
        let dir = tempfile::tempdir().expect("tempdir");
        let input = dir.path().join("php4.cnf");
        write_pigeonhole(&input, 4);
        let output = ay().arg(&input).output().expect("run ay");
        assert!(
            stdout(&output).contains("s UNSATISFIABLE"),
            "{}",
            stderr(&output)
        );
        let proof = dir.path().join("php4.cnf.drat");
        let label = read_label_at(&proof)
            .expect("read label")
            .expect("the sibling proof is labelled");
        assert_eq!(label.input, "php4.cnf");
        assert_eq!(label.input_sha256, sha256_file(&input).expect("hash"));
        assert_eq!(
            label.proof_sha256,
            Some(sha256_file(&proof).expect("hash proof"))
        );
        assert!(label.command.contains("php4.cnf"), "{}", label.command);
        assert_eq!(label.class, "cache");
        // The status marker stays beside its proof, and says what it is too.
        let marker = read_label_at(&dir.path().join("php4.cnf.drat.ay-status"))
            .expect("read label")
            .expect("the status marker is labelled");
        assert_eq!(marker.input_sha256, label.input_sha256);
    }

    #[test]
    #[timeout(120_000)]
    fn an_explicit_proof_wins_over_the_store_and_no_proof_conflicts_with_it() {
        let dir = tempfile::tempdir().expect("tempdir");
        let input = dir.path().join("php4.cnf");
        write_pigeonhole(&input, 4);
        let store = dir.path().join("store");
        let explicit = dir.path().join("named.drat");
        let output = ay()
            .arg("--proof-store")
            .arg(&store)
            .arg("--proof")
            .arg(&explicit)
            .arg(&input)
            .output()
            .expect("run ay");
        assert!(
            stdout(&output).contains("s UNSATISFIABLE"),
            "{}",
            stderr(&output)
        );
        let label = read_label_at(&explicit)
            .expect("read label")
            .expect("a proof a person named is labelled too");
        assert_eq!(label.input_sha256, sha256_file(&input).expect("hash"));
        assert_eq!(label.class, "personal", "the person's file, not cache");
        assert!(!store.exists(), "the explicit proof needs no store");

        let refused = ay()
            .arg("--proof-store")
            .arg(&store)
            .arg("--no-proof")
            .arg(&input)
            .output()
            .expect("run ay");
        assert_eq!(refused.status.code(), Some(2), "{}", stderr(&refused));
    }

    #[test]
    #[timeout(240_000)]
    fn a_stored_proof_is_reused_only_after_it_is_checked_again() {
        let dir = tempfile::tempdir().expect("tempdir");
        let corpus = dir.path().join("corpus");
        fs::create_dir(&corpus).expect("corpus");
        let input = corpus.join("php5.cnf");
        write_pigeonhole(&input, 5);
        let store = dir.path().join("store");

        let first = solve(&store, &input);
        let slot = store.join(format!(
            "{}-{}",
            sha256_file(&input).expect("hash"),
            build_identity()
        ));
        let proof = slot.join("php5.cnf.drat");
        let stored = fs::read(&proof).unwrap_or_else(|error| {
            panic!("first run stored its proof: {error}\n{}", stderr(&first))
        });

        let names_before = names(&slot);
        let second = solve(&store, &input);
        let second_err = stderr(&second);
        assert_eq!(
            stdout(&second).lines().find(|line| !line.starts_with('c')),
            Some("s UNSATISFIABLE"),
            "{second_err}"
        );
        assert!(
            // The store's folder is named canonically (`/private/var/...` for
            // `/var/...` on macOS), so only the slot's own names are compared.
            second_err.lines().any(|line| {
                line.starts_with("c proof store: ")
                    && line.contains(&format!(
                        "/{}/php5.cnf.drat is this input's proof from this build",
                        slot.file_name().expect("slot name").to_string_lossy()
                    ))
                    && line.ends_with("this run writes no second copy")
            }),
            "the stored proof is checked again and counts:\n{second_err}"
        );
        // It counts: the run writes no second copy, so nothing fails to
        // publish, and the slot is as it was.
        for failure in [
            "stale-not-current",
            "was not published",
            "refusing to overwrite",
            "ay.proof.decline",
            "artifact-refused",
            "could not publish",
        ] {
            assert!(
                !second_err.contains(failure),
                "a reused proof is not a failed one ({failure}):\n{second_err}"
            );
        }
        assert_eq!(fs::read(&proof).expect("still stored"), stored);
        assert_eq!(names(&slot), names_before, "no second copy, no leftover");

        // A stored proof whose bytes changed does not count: it is set aside
        // in its slot, never removed, and the run writes a fresh proof.
        fs::OpenOptions::new()
            .append(true)
            .open(&proof)
            .expect("open stored proof")
            .write_all(b"1 0\n")
            .expect("tamper");
        let third = solve(&store, &input);
        assert!(
            stderr(&third).contains("does not count"),
            "{}",
            stderr(&third)
        );
        let fresh = read_label_at(&proof)
            .expect("read label")
            .expect("a fresh, labelled proof");
        assert_eq!(
            fresh.proof_sha256,
            Some(sha256_file(&proof).expect("hash proof"))
        );
        let set_aside: Vec<PathBuf> = fs::read_dir(&slot)
            .expect("list slot")
            .flatten()
            .map(|entry| entry.path())
            .filter(|path| {
                path.file_name().is_some_and(|name| {
                    let name = name.to_string_lossy();
                    name.starts_with(".php5.cnf.drat.rejected-") && !name.ends_with(".ay-status")
                })
            })
            .collect();
        assert_eq!(set_aside.len(), 1, "{set_aside:?}");
        let mut tampered = stored.clone();
        tampered.extend_from_slice(b"1 0\n");
        assert_eq!(fs::read(&set_aside[0]).expect("kept"), tampered);
        assert_eq!(
            snapshot(&corpus).len(),
            1,
            "nothing beside the input after three runs"
        );
    }

    /// The slot `store` gives `input` under this build.
    fn slot_of(store: &Path, input: &Path) -> PathBuf {
        store.join(format!(
            "{}-{}",
            sha256_file(input).expect("hash input"),
            build_identity()
        ))
    }

    /// A run SIGKILLed mid-solve leaves its status transaction lock in its
    /// slot, and a run that times out leaves a `stale-not-current` marker
    /// with no proof. The DRAT writer never replaces either, so before a check
    /// again set them aside, every later run of that input in that store
    /// published no proof: the sweep killed, or timed out, then resumed.
    #[test]
    #[timeout(600_000)]
    fn a_killed_or_timed_out_run_does_not_stop_the_next_from_publishing() {
        let dir = tempfile::tempdir().expect("tempdir");
        let corpus = dir.path().join("corpus");
        let store = dir.path().join("store");
        fs::create_dir(&corpus).expect("corpus");
        let hard = corpus.join("hard.cnf");
        write_hard_random_3sat(&hard);
        let hard_slot = slot_of(&store, &hard);
        let hard_lock = hard_slot.join("hard.cnf.drat.ay-status.lock");
        let hard_marker = hard_slot.join("hard.cnf.drat.ay-status");

        // Killed mid-run: its lock stays behind, with nobody holding it.
        let mut child = ay()
            .arg("--proof-store")
            .arg(&store)
            .args(["--timeout", "600000"])
            .arg(&hard)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .process_group(0)
            .spawn()
            .expect("spawn the run that is killed");
        let deadline = Instant::now() + Duration::from_secs(60);
        while Instant::now() < deadline && !hard_lock.exists() {
            std::thread::sleep(Duration::from_millis(20));
        }
        assert!(hard_lock.exists(), "the run took its status transaction");
        std::thread::sleep(Duration::from_millis(300));
        kill_group(&mut child);
        assert!(hard_lock.is_file(), "the killed run left its lock");

        // The next run sets the dead run's lock aside and takes the name; it
        // times out, and leaves a stale marker with no proof.
        let timed_out = ay()
            .arg("--proof-store")
            .arg(&store)
            .args(["--timeout", "300"])
            .arg(&hard)
            .output()
            .expect("run ay");
        let timed_out_err = stderr(&timed_out);
        assert!(
            timed_out_err.lines().any(|line| {
                line.starts_with("c proof store: ")
                    && line.contains("/hard.cnf.drat.ay-status.lock does not count")
                    && line.contains("set aside as")
            }),
            "{timed_out_err}"
        );
        assert!(!hard_lock.exists(), "{timed_out_err}");
        let marker = fs::read_to_string(&hard_marker)
            .unwrap_or_else(|error| panic!("a timed-out run's marker: {error}\n{timed_out_err}"));
        assert!(marker.contains("status=stale-not-current"), "{marker}");
        assert!(!hard_slot.join("hard.cnf.drat").exists());

        // That marker, alone in the slot of an input that is quick to refute,
        // is what a resumed sweep meets: the run sets it aside and publishes.
        let quick = corpus.join("php5.cnf");
        write_pigeonhole(&quick, 5);
        let quick_slot = slot_of(&store, &quick);
        fs::create_dir(&quick_slot).expect("slot");
        let planted = quick_slot.join("php5.cnf.drat.ay-status");
        fs::rename(&hard_marker, &planted).expect("move the dead run's marker");
        let output = solve(&store, &quick);
        let err = stderr(&output);
        assert_eq!(
            stdout(&output).lines().find(|line| !line.starts_with('c')),
            Some("s UNSATISFIABLE"),
            "{err}"
        );
        assert!(
            err.lines().any(|line| line.starts_with("c proof store: ")
                && line.contains("/php5.cnf.drat.ay-status does not count")),
            "{err}"
        );
        for failure in ["refusing to overwrite", "was not published"] {
            assert!(!err.contains(failure), "{failure}:\n{err}");
        }
        let proof = quick_slot.join("php5.cnf.drat");
        let label = read_label_at(&proof)
            .expect("read label")
            .unwrap_or_else(|| panic!("a labelled proof is published:\n{err}"));
        assert_eq!(
            label.proof_sha256,
            Some(sha256_file(&proof).expect("hash proof"))
        );
        let marker = fs::read_to_string(&planted).expect("the fresh proof's marker");
        assert!(marker.contains("status=current-same-run"), "{marker}");
        assert!(
            read_label_at(&planted).expect("read label").is_some(),
            "the marker is labelled as its proof is"
        );
        let set_aside = names(&quick_slot)
            .into_iter()
            .filter(|name| name.starts_with(".php5.cnf.drat.ay-status.rejected-"))
            .count();
        assert_eq!(set_aside, 1, "set aside, never removed");
    }
}
