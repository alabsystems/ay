// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
use super::*;

fn commit(runner: &mut Runner, name: &str) -> String {
    runner
        .git(&[
            "-c",
            "core.hooksPath=/dev/null",
            "commit",
            "--allow-empty",
            "-m",
            name,
        ])
        .unwrap();
    runner.head().unwrap()
}
fn fixture() -> (tempfile::TempDir, Runner, String, String, String) {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().join("work");
    fs::create_dir(&root).unwrap();
    let mut runner = Runner::new(root);
    runner.git(&["init", "--initial-branch=topic"]).unwrap();
    runner
        .git(&["config", "user.name", "Transport fixture"])
        .unwrap();
    runner
        .git(&["config", "user.email", "transport@example.invalid"])
        .unwrap();
    runner.git(&["config", "commit.gpgsign", "false"]).unwrap();
    runner
        .git(&[
            "remote",
            "add",
            "origin",
            "https://github.com/alabsystems/ay.git",
        ])
        .unwrap();
    let base = commit(&mut runner, "base");
    let head = commit(&mut runner, "validated");
    let later = commit(&mut runner, "concurrent main");
    runner.git(&["reset", "--hard", &head]).unwrap();
    runner.git(&["update-ref", TRACKING, &base]).unwrap();
    (temp, runner, base, head, later)
}

#[derive(Clone, Copy)]
enum Outcome {
    Ack,
    LostAck,
    ReadFailure,
    ReadBehind,
    Descendant,
    DryRunConflict,
    DryRunUnchanged,
    DryRunPermission,
}
struct Peer {
    fetched: String,
    desired: String,
    later: String,
    race: Option<String>,
    outcome: Outcome,
    writes: usize,
    dry_runs: usize,
    fetches: usize,
    receipts: Vec<PathBuf>,
}
impl Peer {
    fn new(base: &str, head: &str, later: &str, outcome: Outcome) -> Self {
        Self {
            fetched: base.into(),
            desired: head.into(),
            later: later.into(),
            race: None,
            outcome,
            writes: 0,
            dry_runs: 0,
            fetches: 0,
            receipts: vec![],
        }
    }
}
impl Drop for Peer {
    fn drop(&mut self) {
        for path in &self.receipts {
            let _ = fs::remove_dir_all(path);
        }
    }
}
impl Agh for Peer {
    fn fetch(&mut self, runner: &mut Runner) -> Result<()> {
        self.fetches += 1;
        if self.writes > 0 && matches!(self.outcome, Outcome::ReadFailure) {
            bail!("readback unavailable");
        }
        runner.git(&["update-ref", FETCHED, &self.fetched])?;
        if let Some(race) = self.race.take() {
            runner.git(&["update-ref", TRACKING, &race])?;
        }
        Ok(())
    }
    fn push(&mut self, _runner: &mut Runner, receipts: &Path, dry_run: bool) -> Result<()> {
        let intent: serde_json::Value =
            serde_json::from_slice(&fs::read(receipts.join("intent.json"))?)?;
        assert_eq!(
            intent,
            serde_json::json!([{"ref":"refs/heads/main", "before":self.fetched,"after":self.desired}])
        );
        if dry_run {
            self.dry_runs += 1;
            self.receipts.push(receipts.into());
            fs::write(receipts.join("dry-run.json"), b"{\"dry_run\":true}")?;
            if matches!(
                self.outcome,
                Outcome::DryRunConflict | Outcome::DryRunUnchanged | Outcome::DryRunPermission
            ) {
                let kind = if matches!(self.outcome, Outcome::DryRunPermission) {
                    "forbidden"
                } else {
                    "conflict"
                };
                fs::write(
                    receipts.join("dry-run.json"),
                    serde_json::to_vec(&serde_json::json!({
                        "repo": REPOSITORY, "op":"ref.update-atomic", "dry_run":true, "outcome":"refused"
                    }))?,
                )?;
                fs::write(
                    receipts.join("dry-run-error.json"),
                    format!(
                        "agh: refused\n{}\n",
                        serde_json::json!({"error": {
                            "repo":REPOSITORY, "kind":kind, "exit":9, "side_effect":"none"
                        }})
                    ),
                )?;
                if !matches!(self.outcome, Outcome::DryRunUnchanged) {
                    self.fetched = self.later.clone();
                }
                bail!("dry run refused");
            }
        } else {
            self.writes += 1;
            fs::write(receipts.join("ack.json"), b"{\"acknowledged\":true}")?;
            match self.outcome {
                Outcome::LostAck => {
                    self.fetched = self.desired.clone(); // The server wrote; response was lost.
                    fs::write(receipts.join("error.json"), b"lost acknowledgement")?;
                    bail!("lost acknowledgement");
                }
                Outcome::ReadBehind => {}
                Outcome::Descendant => self.fetched = self.later.clone(),
                _ => self.fetched = self.desired.clone(),
            }
        }
        Ok(())
    }
}

#[test]
fn a_nonwriting_ref_conflict_requires_fresh_composition_without_a_push() {
    let (_temp, mut runner, base, head, later) = fixture();
    let mut peer = Peer::new(&base, &head, &later, Outcome::DryRunConflict);
    assert!(!push_with(&mut runner, &head, &base, &mut peer).unwrap());
    assert_eq!(peer.writes, 0);
    assert_eq!(peer.dry_runs, 1);
    assert_eq!(peer.fetches, 2);
    assert_eq!(runner.head().unwrap(), head);
    assert_eq!(read_ref(&mut runner, TRACKING).unwrap(), Some(later));
}

#[test]
fn permission_refusal_and_unchanged_conflict_do_not_retry() {
    for outcome in [Outcome::DryRunPermission, Outcome::DryRunUnchanged] {
        let (_temp, mut runner, base, head, later) = fixture();
        let mut peer = Peer::new(&base, &head, &later, outcome);
        assert!(push_with(&mut runner, &head, &base, &mut peer).is_err());
        assert_eq!(peer.writes, 0);
        assert_eq!(peer.dry_runs, 1);
        assert_eq!(
            peer.fetches,
            if matches!(outcome, Outcome::DryRunPermission) {
                1
            } else {
                2
            }
        );
    }
}

#[test]
fn acknowledged_or_unknown_write_never_enters_a_second_push() {
    for outcome in [
        Outcome::Ack,
        Outcome::LostAck,
        Outcome::ReadFailure,
        Outcome::ReadBehind,
        Outcome::Descendant,
    ] {
        let (_temp, mut runner, base, head, later) = fixture();
        let mut peer = Peer::new(&base, &head, &later, outcome);
        let result = push_with(&mut runner, &head, &base, &mut peer);
        assert_eq!(peer.writes, 1);
        assert_eq!(peer.dry_runs, 1);
        let receipts = &peer.receipts[0];
        assert!(receipts.join("intent.json").is_file());
        assert!(receipts.join("ack.json").is_file());
        assert!(receipts.join("dry-run.json").is_file());
        match outcome {
            Outcome::Ack | Outcome::Descendant => assert!(result.unwrap()),
            Outcome::LostAck => {
                assert!(format!("{:#}", result.unwrap_err()).contains("outcome unknown"));
                assert_eq!(peer.fetches, 1); // No readback/retry after a possibly successful write.
            }
            _ => assert!(format!("{:#}", result.unwrap_err()).contains("no second push")),
        }
    }
}

#[test]
fn fetch_is_forward_only_and_compares_the_pre_transport_tracking_identity() {
    let (_temp, mut runner, base, head, later) = fixture();
    let owner = REPOSITORY.split_once('/').unwrap().0;
    runner
        .git(&[
            "remote",
            "set-url",
            "origin",
            &format!("git@gh-{owner}:{REPOSITORY}.git"),
        ])
        .unwrap();
    let mut peer = Peer::new(&head, &head, &later, Outcome::Ack);
    peer.race = Some(later.clone());
    assert!(fetch_with(&mut runner, &mut peer).is_err());
    assert_eq!(read_ref(&mut runner, TRACKING).unwrap(), Some(later));
    runner.git(&["update-ref", TRACKING, &head]).unwrap();
    peer.fetched = base.clone();
    assert!(fetch_with(&mut runner, &mut peer).is_err());
    assert_eq!(read_ref(&mut runner, TRACKING).unwrap(), Some(head.clone()));
    // A known remote move before any write requests a fresh validated round.
    runner.git(&["update-ref", TRACKING, &base]).unwrap();
    peer.fetched = head.clone();
    assert!(!push_with(&mut runner, &head, &base, &mut peer).unwrap());
    assert_eq!(peer.writes, 0);
    assert_eq!(peer.dry_runs, 0);
}

#[test]
#[cfg(unix)]
fn unsafe_paths_symbolic_tracking_and_foreign_origins_refuse_before_transport() {
    use std::os::unix::fs::symlink;
    let (temp, mut runner, base, head, later) = fixture();
    let mut peer = Peer::new(&base, &head, &later, Outcome::Ack);
    let target = temp.path().join("outside");
    fs::write(&target, format!("{base}\n")).unwrap();
    let tracking = runner.root.join(".git").join(TRACKING);
    fs::remove_file(&tracking).unwrap();
    symlink(&target, &tracking).unwrap();
    assert!(fetch_with(&mut runner, &mut peer).is_err());
    assert_eq!(fs::read_to_string(&target).unwrap(), format!("{base}\n"));
    fs::remove_file(&tracking).unwrap();
    fs::hard_link(&target, &tracking).unwrap();
    assert!(fetch_with(&mut runner, &mut peer).is_err());
    fs::remove_file(&tracking).unwrap();
    runner
        .git(&["symbolic-ref", TRACKING, "refs/heads/topic"])
        .unwrap();
    assert!(fetch_with(&mut runner, &mut peer).is_err());
    fs::remove_file(&tracking).unwrap();
    runner.git(&["update-ref", TRACKING, &base]).unwrap();
    let log = runner.root.join(".git/logs/refs/remotes/origin/main");
    fs::remove_file(&log).unwrap();
    symlink(&target, &log).unwrap();
    assert!(fetch_with(&mut runner, &mut peer).is_err());
    fs::remove_file(&log).unwrap();
    // The private build must reject the release owner. In the public
    // projection that owner is ours, so keep the same foreign-owner control.
    let foreign = if REPOSITORY.starts_with("alabsystems/") {
        "https://github.com/example/ay.git"
    } else {
        "https://github.com/alabsystems/ay.git"
    };
    for url in [
        foreign.to_owned(),
        format!("https://github.com/not-{REPOSITORY}.git"),
        format!("https://github.com/{REPOSITORY}-other.git"),
    ] {
        runner.git(&["remote", "set-url", "origin", &url]).unwrap();
        assert!(fetch_with(&mut runner, &mut peer).is_err(), "{url}");
    }
    assert_eq!(peer.fetches, 0);
}

#[test]
fn physical_local_fixture_pushes_only_the_exact_validated_graph() {
    let (temp, mut runner, base, head, later) = fixture();
    let origin = temp.path().join("origin.git");
    fs::create_dir(&origin).unwrap();
    let mut bare = Runner::new(origin.clone());
    bare.git(&["init", "--bare", "--initial-branch=main"])
        .unwrap();
    runner
        .git(&["remote", "set-url", "origin", origin.to_str().unwrap()])
        .unwrap();
    runner
        .git(&[
            "-c",
            "protocol.allow=never",
            "-c",
            "protocol.file.allow=always",
            "push",
            origin.to_str().unwrap(),
            &format!("{base}:refs/heads/main"),
        ])
        .unwrap();
    // A Git pushurl must never redirect a fixture's graph to the network.
    runner
        .git(&[
            "remote",
            "set-url",
            "--push",
            "origin",
            "https://github.com/alabsystems/ay.git",
        ])
        .unwrap();
    let mut peer = Peer::new(&base, &head, &later, Outcome::Ack);
    assert!(push_with(&mut runner, &head, &base, &mut peer).unwrap());
    assert_eq!(
        bare.git(&["rev-parse", "refs/heads/main"]).unwrap().trim(),
        head
    );
    assert_eq!(peer.fetches, 0);
    assert_eq!(peer.writes, 0);
}
