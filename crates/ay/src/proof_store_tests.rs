// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The proof store, the label and the sidecar list (DC-77).

use super::*;

const STATUS_TRANSACTION_HEADER: &str = "ay-dimacs-proof-status-transaction-v1";
const STATUS_MARKER_HEADER: &str = "ay-dimacs-proof-status-v1";

fn write(path: &Path, bytes: &[u8]) {
    fs::write(path, bytes).expect("write fixture");
}

/// A published proof in `slot`, labelled and sealed as ay's writers do it.
fn publish(slot: &ProofSlot, extension: &str, bytes: &[u8]) -> PathBuf {
    let path = slot.proof_path(extension);
    let mut file = File::create(&path).expect("create proof");
    label_at_creation(&file, &slot.subject()).expect("label at creation");
    file.write_all(bytes).expect("write proof");
    seal_label(&file, &hex(&Sha256::digest(bytes))).expect("seal label");
    path
}

/// A check again that set exactly one name aside and found no proof.
fn only_set_aside(slot: &ProofSlot) -> SetAside {
    let check = slot.check_stored("drat").expect("check");
    assert_eq!(check.proof, StoredProof::Absent, "{check:?}");
    let [aside] = <[SetAside; 1]>::try_from(check.set_aside).expect("one name set aside");
    aside
}

#[test]
fn a_label_round_trips_through_its_text() {
    let label = ProofLabel {
        maker: "ay".to_string(),
        class: "cache".to_string(),
        session: Some("s595dac".to_string()),
        input: "odd\nname\\.cnf".to_string(),
        input_sha256: "ab".repeat(32),
        build: build_identity().to_string(),
        build_stamp: build_stamp().to_string(),
        device: 16_777_231,
        inode: 42,
        command: "ay 'odd\nname\\.cnf'".to_string(),
        directory: Some("/corpus".to_string()),
        proof_sha256: Some("cd".repeat(32)),
    };
    let text = label.encode();
    assert!(text.starts_with(LABEL_SCHEMA));
    assert_eq!(
        text.lines().count(),
        13,
        "a newline in a value is escaped, so one field is one line: {text}"
    );
    assert_eq!(ProofLabel::parse(&text), Ok(label));
    assert!(ProofLabel::parse("ay-proof-label-v0\nmaker=ay\n").is_err());
    assert!(
        ProofLabel::parse(&format!("{LABEL_SCHEMA}\nmaker=ay\n")).is_err(),
        "a label missing its input is not ay's"
    );
}

#[test]
fn a_proof_is_labelled_at_creation_and_sealed_at_publication() {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("php.cnf");
    write(&input, b"p cnf 1 2\n1 0\n-1 0\n");
    let proof = dir.path().join("php.cnf.drat");
    let file = File::create(&proof).expect("create proof");
    label_at_creation(&file, &ProofSubject::beside(&input)).expect("label");

    let label = read_label_at(&proof).expect("read").expect("labelled");
    assert_eq!(label.maker, "ay");
    assert_eq!(label.class, "cache");
    assert_eq!(label.input, "php.cnf");
    assert_eq!(label.input_sha256, sha256_file(&input).expect("hash input"));
    assert_eq!(label.build, build_identity());
    assert_eq!(label.build_stamp, build_stamp());
    assert!(label.sits_on(&file).expect("stat"));
    assert!(!label.command.is_empty(), "the command that makes it again");
    assert!(label.directory.is_some(), "and where it ran");
    assert_eq!(label.proof_sha256, None, "unpublished until sealed");

    seal_label(&file, "ef".repeat(32).as_str()).expect("seal");
    let sealed = read_label_at(&proof).expect("read").expect("labelled");
    assert_eq!(sealed.proof_sha256, Some("ef".repeat(32)));
    assert_eq!(
        sealed.input_sha256, label.input_sha256,
        "sealing keeps the rest"
    );
}

#[test]
fn a_label_moved_to_another_file_reads_as_a_copy() {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("a.smt2");
    write(&input, b"(assert false)(check-sat)\n");
    let original = File::create(dir.path().join("a.smt2.alethe")).expect("create");
    label_at_creation(&original, &ProofSubject::beside(&input)).expect("label");
    let label = read_label(&original).expect("read").expect("labelled");

    let copy = File::create(dir.path().join("copy.alethe")).expect("create copy");
    ay_sys::fs::set_xattr(&copy, LABEL_ATTRIBUTE, label.encode().as_bytes())
        .expect("carry the label over, as cp and macOS clones do");
    let carried = read_label(&copy).expect("read").expect("labelled");
    assert!(label.sits_on(&original).expect("stat"));
    assert!(
        !carried.sits_on(&copy).expect("stat"),
        "a carried label names the inode it was written on, not this one"
    );
}

#[test]
fn an_unlabelled_file_has_no_label() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("x.drat");
    write(&path, b"1 0\n");
    assert_eq!(read_label_at(&path).expect("read"), None);
    let file = File::open(&path).expect("open");
    seal_label(&file, "00").expect("sealing an unlabelled file is a no-op");
    assert_eq!(read_label_at(&path).expect("read"), None);
}

#[test]
fn a_store_is_tagged_and_names_each_slot_by_input_hash_and_build() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path().join("store");
    let store = ProofStore::open(&root).expect("open store");
    let tag = fs::read_to_string(root.join(STORE_TAG_NAME)).expect("tag");
    assert!(tag.starts_with(CACHEDIR_TAG_SIGNATURE), "{tag}");
    ProofStore::open(&root).expect("an existing store opens again");

    let input = dir.path().join("php.cnf");
    write(&input, b"p cnf 1 2\n1 0\n-1 0\n");
    let slot = store.slot(&input).expect("slot");
    let sha256 = sha256_file(&input).expect("hash");
    assert_eq!(slot.input_sha256(), sha256);
    assert_eq!(
        slot.dir(),
        store.root().join(format!("{sha256}-{}", build_identity()))
    );
    assert!(slot.dir().is_dir());
    assert_eq!(
        slot.proof_path("drat"),
        slot.dir().join("php.cnf.drat"),
        "the proof keeps its sidecar name inside the slot"
    );
    assert_eq!(slot.subject().placement, ProofPlacement::Store);
    assert_eq!(store.slot(&input).expect("same slot"), slot);
}

#[test]
fn a_folder_with_a_foreign_tag_is_not_a_store() {
    let dir = tempfile::tempdir().expect("tempdir");
    write(&dir.path().join(STORE_TAG_NAME), b"not a cache tag\n");
    let error = ProofStore::open(dir.path()).expect_err("foreign tag");
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);

    // A real cache-directory tag another tool or a person placed is not one
    // ay made: ay neither opens the folder as a store nor labels the tag.
    let other = tempfile::tempdir().expect("tempdir");
    let tag = other.path().join(STORE_TAG_NAME);
    write(
        &tag,
        format!("{CACHEDIR_TAG_SIGNATURE}\n# made by hand\n").as_bytes(),
    );
    let error = ProofStore::open(other.path()).expect_err("a tag ay did not make");
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    assert!(error.to_string().contains("no label"), "{error}");
    assert_eq!(
        read_label_at(&tag).expect("read"),
        None,
        "never re-labelled"
    );

    // A copied store carries its tag's label onto another inode.
    let made = tempfile::tempdir().expect("tempdir");
    ProofStore::open(&made.path().join("s")).expect("store");
    let copied = tempfile::tempdir().expect("tempdir");
    let copy = File::create(copied.path().join(STORE_TAG_NAME)).expect("copy");
    let label = read_label_at(&made.path().join("s").join(STORE_TAG_NAME))
        .expect("read")
        .expect("ay labels the tag it makes");
    (&copy)
        .write_all(format!("{CACHEDIR_TAG_SIGNATURE}\n").as_bytes())
        .expect("write");
    ay_sys::fs::set_xattr(&copy, LABEL_ATTRIBUTE, label.encode().as_bytes()).expect("carry");
    let error = ProofStore::open(copied.path()).expect_err("a copied tag");
    assert!(error.to_string().contains("copy"), "{error}");
}

/// A store is a cache: ay never makes one of a folder that holds a person's
/// files, which backup tools would then skip and a cleaner could empty.
#[test]
fn a_folder_that_holds_anything_is_never_made_a_store() {
    let dir = tempfile::tempdir().expect("tempdir");
    let data = dir.path().join("mydata");
    fs::create_dir(&data).expect("mkdir");
    write(&data.join("notes.txt"), b"precious\n");
    let error = ProofStore::open(&data).expect_err("a folder with files");
    assert_eq!(error.kind(), io::ErrorKind::AlreadyExists);
    assert!(!data.join(STORE_TAG_NAME).exists(), "no tag was placed");
    assert_eq!(
        fs::read_dir(&data).expect("list").count(),
        1,
        "the folder is as it was"
    );

    // An empty folder becomes a store, and opens again once it holds slots.
    let empty = dir.path().join("empty");
    fs::create_dir(&empty).expect("mkdir");
    let store = ProofStore::open(&empty).expect("an empty folder");
    let input = dir.path().join("php.cnf");
    write(&input, b"p cnf 1 2\n1 0\n-1 0\n");
    store.slot(&input).expect("slot");
    ProofStore::open(&empty).expect("a store ay made opens again");
}

#[test]
fn a_stored_proof_counts_only_after_it_is_checked_again() {
    let dir = tempfile::tempdir().expect("tempdir");
    let store = ProofStore::open(&dir.path().join("store")).expect("store");
    let input = dir.path().join("php.cnf");
    write(&input, b"p cnf 1 2\n1 0\n-1 0\n");
    let slot = store.slot(&input).expect("slot");

    assert_eq!(
        slot.check_stored("drat").expect("check"),
        SlotCheck {
            proof: StoredProof::Absent,
            set_aside: Vec::new()
        }
    );
    let proof = publish(&slot, "drat", b"0\n");
    assert_eq!(
        slot.check_stored("drat").expect("check").proof,
        StoredProof::Reused(proof.clone())
    );
    assert_eq!(fs::read(&proof).expect("still there"), b"0\n");

    // With its marker, the marker must name it as its run's current proof.
    let marker = slot.dir().join("php.cnf.drat.ay-status");
    write(
        &marker,
        format!(
            "{STATUS_MARKER_HEADER}\n{STATUS_CURRENT}\nproducer_pid=1\nsha256={}\n",
            hex(&Sha256::digest(b"0\n"))
        )
        .as_bytes(),
    );
    assert_eq!(
        slot.check_stored("drat").expect("check").proof,
        StoredProof::Reused(proof.clone())
    );
}

#[test]
fn a_stored_proof_that_fails_its_check_is_set_aside_in_the_slot_never_removed() {
    let dir = tempfile::tempdir().expect("tempdir");
    let store = ProofStore::open(&dir.path().join("store")).expect("store");
    let input = dir.path().join("php.cnf");
    write(&input, b"p cnf 1 2\n1 0\n-1 0\n");
    let slot = store.slot(&input).expect("slot");

    // Bytes changed after publication. Its status marker moves aside with
    // it, or the DRAT writer, which never replaces a marker, could not
    // publish the fresh proof.
    let proof = publish(&slot, "drat", b"0\n");
    let marker = slot.dir().join("php.cnf.drat.ay-status");
    write(
        &marker,
        format!(
            "{STATUS_MARKER_HEADER}\n{STATUS_CURRENT}\nsha256={}\n",
            hex(&Sha256::digest(b"0\n"))
        )
        .as_bytes(),
    );
    fs::OpenOptions::new()
        .append(true)
        .open(&proof)
        .expect("open")
        .write_all(b"1 0\n")
        .expect("tamper");
    let SetAside { aside, why, .. } = only_set_aside(&slot);
    assert!(why.contains("hash"), "{why}");
    assert!(!proof.exists());
    assert_eq!(
        aside.parent(),
        Some(slot.dir()),
        "set aside inside the slot"
    );
    assert_eq!(fs::read(&aside).expect("kept"), b"0\n1 0\n");
    assert!(!marker.exists(), "the marker moved with its proof");
    let mut marker_aside = aside.clone().into_os_string();
    marker_aside.push(".ay-status");
    assert!(Path::new(&marker_aside).is_file());

    // No label at all.
    write(&slot.proof_path("drat"), b"0\n");
    let SetAside { why, .. } = only_set_aside(&slot);
    assert!(why.contains("no label"), "{why}");

    // Never published: a transaction file's label records no proof sha256.
    let unsealed = slot.proof_path("drat");
    let file = File::create(&unsealed).expect("create");
    label_at_creation(&file, &slot.subject()).expect("label");
    let SetAside { why, .. } = only_set_aside(&slot);
    assert!(why.contains("no published proof"), "{why}");

    // A label naming another input.
    let other = dir.path().join("other.cnf");
    write(&other, b"p cnf 2 1\n1 2 0\n");
    let mut subject = slot.subject();
    subject.input_sha256 = Some(sha256_file(&other).expect("hash"));
    let path = slot.proof_path("drat");
    let mut file = File::create(&path).expect("create");
    label_at_creation(&file, &subject).expect("label");
    file.write_all(b"0\n").expect("write");
    seal_label(&file, &hex(&Sha256::digest(b"0\n"))).expect("seal");
    let SetAside { why, .. } = only_set_aside(&slot);
    assert!(why.contains("names input sha256"), "{why}");

    let kept = fs::read_dir(slot.dir()).expect("list").count();
    assert_eq!(
        kept, 5,
        "every proof that failed is still in the slot, with the one marker"
    );
}

/// A live run's status transaction owns the name: a proof it published but
/// has not finished (its label not yet sealed, its marker not yet written)
/// is not judged, and nothing under the name moves.
#[test]
fn a_live_runs_transaction_is_never_judged_or_moved() {
    let dir = tempfile::tempdir().expect("tempdir");
    let store = ProofStore::open(&dir.path().join("store")).expect("store");
    let input = dir.path().join("php.cnf");
    write(&input, b"p cnf 1 2\n1 0\n-1 0\n");
    let slot = store.slot(&input).expect("slot");

    let proof = slot.proof_path("drat");
    let unsealed = File::create(&proof).expect("create");
    label_at_creation(&unsealed, &slot.subject()).expect("label");
    let lock_path = slot.dir().join("php.cnf.drat.ay-status.lock");
    let lock = File::create(&lock_path).expect("lock");
    lock.lock().expect("the live run holds its transaction");
    (&lock)
        .write_all(format!("{STATUS_TRANSACTION_HEADER}\nproducer_pid=1\n").as_bytes())
        .expect("header");
    let check = slot.check_stored("drat").expect("check");
    assert!(matches!(check.proof, StoredProof::Busy(_)), "{check:?}");
    assert!(check.set_aside.is_empty());
    assert!(proof.is_file() && lock_path.is_file(), "nothing moved");

    assert_eq!(
        slot.supersede("drat", "new proof requested".to_string())
            .expect_err("live proof cannot be superseded")
            .kind(),
        std::io::ErrorKind::WouldBlock,
    );
    assert!(proof.is_file() && lock_path.is_file());

    // The run renamed its lock onto the marker and still holds it.
    let marker = slot.dir().join("php.cnf.drat.ay-status");
    fs::rename(&lock_path, &marker).expect("publish the marker");
    let check = slot.check_stored("drat").expect("check");
    assert!(matches!(check.proof, StoredProof::Busy(_)), "{check:?}");
    assert!(proof.is_file() && marker.is_file(), "nothing moved");

    // Once the run is gone, its unsealed proof does not count.
    drop(lock);
    let SetAside { why, .. } = only_set_aside(&slot);
    assert!(why.contains("no published proof"), "{why}");
    assert!(!marker.exists(), "the marker moved with its proof");
}

/// What a killed or timed-out run leaves in a slot with no proof: its status
/// lock (a SIGKILL mid-run) or a `stale-not-current` marker. The DRAT writer
/// never replaces either, so left in place they would stop every later run
/// of the input from publishing; a check again sets them aside.
#[test]
fn a_dead_runs_lock_or_marker_is_set_aside_so_a_fresh_proof_can_publish() {
    let dir = tempfile::tempdir().expect("tempdir");
    let store = ProofStore::open(&dir.path().join("store")).expect("store");
    let input = dir.path().join("php.cnf");
    write(&input, b"p cnf 1 2\n1 0\n-1 0\n");
    let slot = store.slot(&input).expect("slot");

    let lock = slot.dir().join("php.cnf.drat.ay-status.lock");
    write(
        &lock,
        format!("{STATUS_TRANSACTION_HEADER}\nproducer_pid=1\n").as_bytes(),
    );
    let SetAside { aside, why, .. } = only_set_aside(&slot);
    assert!(why.contains("gone"), "{why}");
    assert!(!lock.exists());
    assert_eq!(
        aside
            .file_name()
            .and_then(|name| name.to_str())
            .map(|name| { name.starts_with(".php.cnf.drat.ay-status.lock.rejected-") }),
        Some(true),
        "{}",
        aside.display()
    );

    let marker = slot.dir().join("php.cnf.drat.ay-status");
    write(
        &marker,
        format!("{STATUS_MARKER_HEADER}\nstatus=stale-not-current\nproducer_pid=1\n").as_bytes(),
    );
    let SetAside { aside, why, .. } = only_set_aside(&slot);
    assert!(why.contains("stale-not-current"), "{why}");
    assert!(!marker.exists());
    assert!(aside.is_file(), "set aside, never removed");

    for partial in [b"".as_slice(), b"ay-dimacs-"] {
        write(&lock, partial);
        let aside = only_set_aside(&slot);
        assert_eq!(fs::read(aside.aside).expect("preserved lock"), partial);
        assert!(!lock.exists());
    }
}

#[test]
fn store_inspection_waits_for_the_writer_to_lock_its_new_descriptor() {
    use std::sync::mpsc;
    use std::time::Duration;
    let dir = tempfile::tempdir().expect("temporary inputs");
    let input = dir.path().join("race.cnf");
    write(&input, b"p cnf 1 2\n1 0\n-1 0\n");
    let slot = ProofStore::open(&dir.path().join("store"))
        .expect("store")
        .slot(&input)
        .expect("slot");
    let slot_guard = lock_slot_directory(slot.dir()).expect("writer holds slot");
    let path = slot.dir().join("race.cnf.drat.ay-status.lock");
    let descriptor = File::create(&path).expect("created, not yet locked");
    let (started, waiting) = mpsc::channel();
    let (done, result) = mpsc::channel();
    let reader = std::thread::spawn(move || {
        started.send(()).expect("reader started");
        done.send(slot.check_stored("drat"))
            .expect("check finished");
    });
    waiting.recv().expect("reader entering");
    assert!(matches!(
        result.recv_timeout(Duration::from_millis(100)),
        Err(mpsc::RecvTimeoutError::Timeout)
    ));
    descriptor.lock().expect("writer holds descriptor");
    drop(slot_guard);
    let check = result
        .recv_timeout(Duration::from_secs(5))
        .expect("slot released")
        .expect("check");
    assert!(matches!(check.proof, StoredProof::Busy(_)));
    assert!(check.set_aside.is_empty() && path.is_file());
    reader.join().expect("reader returned");
}

/// A proof a person named is the person's file: its label never claims the
/// class a cleaner may take.
#[test]
fn a_named_proof_is_labelled_personal_and_a_default_one_cache() {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("php.cnf");
    write(&input, b"p cnf 1 2\n1 0\n-1 0\n");
    let named = File::create(dir.path().join("mine.drat")).expect("create");
    label_at_creation(&named, &ProofSubject::named(&input)).expect("label");
    assert_eq!(
        read_label(&named).expect("read").expect("labelled").class,
        "personal"
    );
    let beside = File::create(dir.path().join("php.cnf.drat")).expect("create");
    label_at_creation(&beside, &ProofSubject::beside(&input)).expect("label");
    assert_eq!(
        read_label(&beside).expect("read").expect("labelled").class,
        "cache"
    );
}

#[test]
fn the_default_extension_follows_the_declared_pairs() {
    assert_eq!(default_proof_extension(Path::new("x/A.CNF")), Some("drat"));
    assert_eq!(default_proof_extension(Path::new("a.smt2")), Some("alethe"));
    assert_eq!(default_proof_extension(Path::new("a.opb")), None);
    assert_eq!(
        proof_extensions(Path::new("a.smt")),
        vec!["alethe", "chccert"]
    );
}

/// A pipe names no content to hash, and reading it again would take the
/// solver's bytes or block: its proof stays unlabelled, and a store refuses it
/// before the solver reads it.
#[cfg(unix)]
#[test]
fn a_pipe_input_is_never_read_for_a_label_or_a_slot() {
    let dir = tempfile::tempdir().expect("tempdir");
    let fifo = dir.path().join("in.cnf");
    nix::unistd::mkfifo(&fifo, nix::sys::stat::Mode::S_IRWXU).expect("mkfifo");
    let proof = File::create(dir.path().join("in.cnf.drat")).expect("create proof");
    label_at_creation(&proof, &ProofSubject::beside(&fifo)).expect("a pipe is skipped");
    assert_eq!(read_label(&proof).expect("read"), None);
    let store = ProofStore::open(&dir.path().join("store")).expect("store");
    let error = store.slot(&fifo).expect_err("a pipe has no slot");
    assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
}
