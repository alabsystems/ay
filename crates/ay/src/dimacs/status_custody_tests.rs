// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The status reservation's custody and its exit settlement (2026-10-08).

use super::*;

/// Reserve the status transaction of `proof` in a fresh directory, as a
/// synthesized default does before its proof file exists.
fn reserve_in(dir: &Path) -> DimacsProofStatusReservation {
    let proof = dir.join("t.cnf.drat");
    reserve_dimacs_proof_status(proof.to_str().expect("UTF-8 path")).expect("reserve status")
}

fn names_in(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(dir)
        .expect("read dir")
        .map(|entry| {
            entry
                .expect("entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    names.sort();
    names
}

/// The window the memory watchdog hit: the lock exists, no registry entry
/// holds the reservation, and the run ends. The exit settles it as the
/// registry sweep would, and the run can no longer publish over it.
#[test]
fn an_exit_settles_a_reservation_no_registry_holds() {
    let dir = tempfile::tempdir().expect("tempdir");
    let reservation = reserve_in(dir.path());
    assert_eq!(names_in(dir.path()), ["t.cnf.drat.ay-status.lock"]);

    reservation
        .custody
        .settle_at_exit(true)
        .expect("settle the open reservation");
    assert_eq!(names_in(dir.path()), ["t.cnf.drat.ay-status"]);
    let marker = std::fs::read_to_string(&reservation.status_path).expect("marker");
    assert!(marker.contains("stale-not-current"), "{marker}");
    assert!(reservation.custody.settled_by_exit());

    let Err(error) = publish_reserved_dimacs_proof_status(reservation, "current-same-run", None)
    else {
        panic!("the run may not publish over an exit's marker");
    };
    assert!(error.to_string().contains("unanswered exit"), "{error}");
    let after = std::fs::read_to_string(dir.path().join("t.cnf.drat.ay-status")).expect("marker");
    assert_eq!(after, marker, "the exit's marker stands");
}

/// A settlement that keeps the run's proofs (`revoke_current` false, as the
/// process-exit sweep of a run that printed its verdict settles) leaves the
/// current marker the run published. group_cli's
/// `a_decisive_unsat_keeps_its_current_marker_through_the_exit_sweep` covers
/// the sweep itself.
#[test]
fn a_settlement_that_keeps_the_proofs_leaves_the_current_marker() {
    let dir = tempfile::tempdir().expect("tempdir");
    let reservation = reserve_in(dir.path());
    let custody = Arc::clone(&reservation.custody);
    let publication = publish_reserved_dimacs_proof_status(reservation, "current-same-run", None)
        .expect("publish the marker");
    let marker = std::fs::read_to_string(&publication.path).expect("marker");
    assert!(marker.contains("current-same-run"), "{marker}");

    custody.settle_at_exit(false).expect("nothing to settle");
    assert!(!custody.settled_by_exit());
    assert_eq!(names_in(dir.path()), ["t.cnf.drat.ay-status"]);
    assert_eq!(
        std::fs::read_to_string(&publication.path).expect("marker"),
        marker
    );
}

/// An exit that meets the run's publication in flight on another thread
/// waits for it instead of racing the rewrite and rename. The wait is a
/// minute here, not the exit's two seconds, so a slow harness cannot time it
/// out.
#[test]
fn an_exit_waits_out_a_publication_in_flight() {
    let dir = tempfile::tempdir().expect("tempdir");
    let reservation = reserve_in(dir.path());
    let custody = Arc::clone(&reservation.custody);

    let claim = custody.claim_settling().expect("claim the reservation");
    let exiting = Arc::clone(&custody);
    let settling = std::thread::spawn(move || {
        exiting.settle_at_exit_within(std::time::Duration::from_secs(60), true)
    });
    std::thread::sleep(std::time::Duration::from_millis(50));
    assert!(
        !settling.is_finished(),
        "the exit must wait for the publication to settle"
    );
    claim.finish(true);
    settling
        .join()
        .expect("exit thread")
        .expect("nothing left to settle");
    assert!(!custody.settled_by_exit());
    assert_eq!(names_in(dir.path()), ["t.cnf.drat.ay-status.lock"]);
}

/// A failed publication reopens the custody, so an exit still settles the
/// lock the failure left behind. Linux and macOS: the platforms with both a
/// `RENAME_NOREPLACE` publication and its test injector.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn a_failed_publication_leaves_the_lock_to_the_exit() {
    let dir = tempfile::tempdir().expect("tempdir");
    let reservation = reserve_in(dir.path());
    let custody = Arc::clone(&reservation.custody);
    inject_dimacs_rename_noreplace_error_once(nix::libc::EIO);
    assert!(
        publish_reserved_dimacs_proof_status(reservation, "current-same-run", None).is_err(),
        "injected rename failure"
    );
    assert_eq!(names_in(dir.path()), ["t.cnf.drat.ay-status.lock"]);

    custody
        .settle_at_exit(true)
        .expect("settle the stranded lock");
    assert!(custody.settled_by_exit());
    assert_eq!(names_in(dir.path()), ["t.cnf.drat.ay-status"]);
}

/// A lock pathname that no longer names this run's inode belongs to someone
/// else: the exit neither rewrites nor renames it.
#[test]
fn an_exit_leaves_a_replaced_lock_alone() {
    let dir = tempfile::tempdir().expect("tempdir");
    let reservation = reserve_in(dir.path());
    std::fs::remove_file(&reservation.lock_path).expect("remove the lock");
    std::fs::write(&reservation.lock_path, b"another run's transaction\n").expect("replace");

    reservation
        .custody
        .settle_at_exit(true)
        .expect("nothing of this run's to settle");
    assert_eq!(names_in(dir.path()), ["t.cnf.drat.ay-status.lock"]);
    assert_eq!(
        std::fs::read(&reservation.lock_path).expect("lock"),
        b"another run's transaction\n"
    );
}

/// The registry sweep skips a reservation an exit already settled instead
/// of reporting a failed second settlement.
#[test]
fn an_exit_settled_reservation_is_settled_for_the_registry_sweep() {
    let dir = tempfile::tempdir().expect("tempdir");
    let reservation = reserve_in(dir.path());
    reservation.custody.settle_at_exit(true).expect("settle");
    assert!(reservation.custody.settled_by_exit());
    assert!(!reservation.custody.is_live());
    assert!(reservation.custody.begin_settling().is_err());
}

/// A second reservation of a path whose marker an exit already published
/// (the memout run's main thread re-reserves to mark its proof stale) is
/// settled by removing its lock: the marker stands and no lock strands the
/// path.
#[test]
fn an_exit_removes_a_lock_whose_marker_already_exists() {
    let dir = tempfile::tempdir().expect("tempdir");
    let first = reserve_in(dir.path());
    first
        .custody
        .settle_at_exit(true)
        .expect("settle the first");
    let marker = std::fs::read_to_string(&first.status_path).expect("marker");

    let proof = dir.path().join("t.cnf.drat");
    let second = create_dimacs_status_reservation(proof.to_str().expect("UTF-8 path"))
        .expect("the lock itself is free");
    assert_eq!(
        names_in(dir.path()),
        ["t.cnf.drat.ay-status", "t.cnf.drat.ay-status.lock"]
    );
    second
        .custody
        .settle_at_exit(true)
        .expect("remove the redundant lock");
    assert_eq!(names_in(dir.path()), ["t.cnf.drat.ay-status"]);
    assert_eq!(
        std::fs::read_to_string(&second.status_path).expect("marker"),
        marker,
        "the earlier marker is never clobbered"
    );
}

fn marker_status(path: &Path) -> String {
    let marker = std::fs::read_to_string(path).expect("marker");
    marker
        .lines()
        .find_map(|line| line.strip_prefix("status="))
        .unwrap_or_else(|| panic!("a status line in {marker:?}"))
        .to_string()
}

/// The run publishes `current-same-run` before it claims its verdict. An
/// unanswered exit in between discards the proof, and the marker that names
/// it goes stale with it: it used to stay current beside no proof.
#[test]
fn an_unanswered_exit_revokes_a_current_marker_it_finds_published() {
    let dir = tempfile::tempdir().expect("tempdir");
    let reservation = reserve_in(dir.path());
    let custody = Arc::clone(&reservation.custody);
    let status_path = reservation.status_path.clone();
    publish_reserved_dimacs_proof_status(reservation, DIMACS_PROOF_STATUS_CURRENT, Some([7; 32]))
        .expect("publish the marker");
    assert_eq!(marker_status(&status_path), "current-same-run");
    assert!(custody.is_live(), "an unanswered exit may still revoke it");

    custody.settle_at_exit(true).expect("revoke the marker");
    assert_eq!(marker_status(&status_path), "stale-not-current");
    assert!(custody.settled_by_exit());
    assert_eq!(names_in(dir.path()), ["t.cnf.drat.ay-status"]);
}

/// The revocation is authenticated: a marker that is no longer this run's
/// inode is never rewritten.
#[test]
fn an_unanswered_exit_leaves_a_replaced_marker_alone() {
    let dir = tempfile::tempdir().expect("tempdir");
    let reservation = reserve_in(dir.path());
    let custody = Arc::clone(&reservation.custody);
    let status_path = reservation.status_path.clone();
    publish_reserved_dimacs_proof_status(reservation, DIMACS_PROOF_STATUS_CURRENT, None)
        .expect("publish the marker");
    std::fs::remove_file(&status_path).expect("remove the marker");
    std::fs::write(&status_path, b"another run's marker\n").expect("replace");

    custody
        .settle_at_exit(true)
        .expect("nothing of this run's to revoke");
    assert_eq!(
        std::fs::read(&status_path).expect("marker"),
        b"another run's marker\n"
    );
}

/// The interleaving the exit used to lose, driven with an injected pause:
/// the run is inside its current-marker publication, between the rewrite
/// and the rename, when an unanswered exit settles the run
/// (`discard_unanswered_dimacs_proofs`). The exit discards no proof while
/// that publication is in flight: it waits it out, rewrites the marker
/// `stale-not-current`, and only then discards the proof. Before, it
/// discarded the proof first and then left the `current-same-run` marker the
/// publication renamed into place. The wait is 45 s here, not the exit's two
/// seconds, so a slow harness cannot time it out.
#[test]
fn an_unanswered_exit_mid_publication_revokes_the_marker_before_the_proof_goes() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof = dir.path().join("t.cnf.drat");
    let proof_text = proof.to_str().expect("UTF-8 path").to_string();
    let mut file = create_owned_dimacs_proof_file(&proof_text).expect("reserve proof");
    file.write_all(b"0\n").expect("write proof");
    drop(file);
    let sealed = seal_owned_dimacs_proof(&proof_text).expect("seal proof");
    let proof_custody = owned_dimacs_proof_custody(&proof_text).expect("proof custody");
    let reservation = reserve_in(dir.path());
    let status_custody = Arc::clone(&reservation.custody);
    let status_path = reservation.status_path.clone();

    let (paused, at_pause) = std::sync::mpsc::channel();
    let (resume, resumed) = std::sync::mpsc::channel::<()>();
    let run = std::thread::spawn(move || {
        inject_dimacs_status_publication_pause_once(move || {
            paused.send(()).expect("report the pause");
            resumed.recv().expect("resume the publication");
        });
        publish_reserved_dimacs_proof_status(
            reservation,
            DIMACS_PROOF_STATUS_CURRENT,
            Some(sealed.sha256),
        )
        .map(drop)
    });
    at_pause
        .recv()
        .expect("the run paused inside its publication");

    let (listed, statuses_listed) = std::sync::mpsc::channel();
    let exit = std::thread::spawn(move || {
        discard_unanswered_dimacs_proofs_among(
            move || {
                listed.send(()).expect("report the status settlement");
                vec![status_custody]
            },
            move || vec![proof_custody],
            std::time::Duration::from_secs(45),
        );
    });
    statuses_listed
        .recv()
        .expect("the exit settles the statuses");
    assert!(
        proof.exists(),
        "no proof goes while the marker naming it is being published"
    );
    assert!(
        !exit.is_finished(),
        "the exit waits out the publication in flight"
    );
    resume.send(()).expect("resume the run");
    run.join()
        .expect("run thread")
        .expect("the claimed publication completes");
    exit.join().expect("exit thread");

    assert_eq!(marker_status(&status_path), "stale-not-current");
    assert!(!proof.exists());
    assert_eq!(names_in(dir.path()), ["t.cnf.drat.ay-status"]);
    remove_owned_dimacs_proof(&proof_text).expect("settle the registry entry");
}

/// The allocator's memory ceiling settles on the thread that crossed it,
/// which may hold a settling claim (`publish_claimed_dimacs_proof_status`
/// allocates). That exit takes the claim over at once, before or after the
/// claimed rename, instead of waiting the whole wait on itself and then
/// leaving the lock or a current marker behind. The wait here is twenty
/// seconds, which the old code spent before it failed.
#[test]
fn an_exit_on_the_claiming_thread_takes_the_claim_over() {
    for renamed in [false, true] {
        let dir = tempfile::tempdir().expect("tempdir");
        let reservation = reserve_in(dir.path());
        let claim = reservation
            .custody
            .claim_settling()
            .expect("claim the reservation");
        if renamed {
            let content = dimacs_proof_status_content(DIMACS_PROOF_STATUS_CURRENT, None);
            rewrite_reserved_dimacs_proof_status(
                &reservation.lock_descriptor,
                &reservation.lock_path,
                reservation.lock_identity,
                content.as_bytes(),
            )
            .expect("rewrite the lock");
            std::fs::rename(&reservation.lock_path, &reservation.status_path)
                .expect("rename the lock onto the marker");
        }

        let wait = std::time::Duration::from_secs(20);
        let started = std::time::Instant::now();
        reservation
            .custody
            .settle_at_exit_within(wait, true)
            .expect("the exit takes its own thread's claim over");
        assert!(started.elapsed() < wait, "renamed={renamed}");
        assert_eq!(
            marker_status(&reservation.status_path),
            "stale-not-current",
            "renamed={renamed}"
        );
        assert_eq!(names_in(dir.path()), ["t.cnf.drat.ay-status"]);

        // Never reached under the ceiling, which leaves through `_exit`; a
        // claim that ends after the takeover leaves the custody settled.
        drop(claim);
        assert!(reservation.custody.settled_by_exit(), "renamed={renamed}");
    }
}
