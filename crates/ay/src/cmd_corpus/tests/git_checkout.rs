// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `verify_git_checkout` against real repositories built by the parent module's
//! `git_checkout_fixture`.

use super::*;

#[test]
fn git_checkout_verification_requires_exact_clean_pin() {
    let fixture = git_checkout_fixture();
    assert!(verify_git_checkout(&fixture.corpus).is_ok());
    fs::write(fixture.checkout.join("asset.txt"), "modified\n").unwrap();
    assert!(verify_git_checkout(&fixture.corpus)
        .unwrap_err()
        .to_string()
        .contains("local modifications"));
}

#[test]
fn forced_git_download_verifies_staging_before_replacing_destination() {
    let directory = TempDir::new().unwrap();
    let source = directory.path().join("source");
    init_test_git_repository(&source);
    fs::write(source.join("asset.txt"), "source\n").unwrap();
    test_git(&source, &["add", "asset.txt"]);
    test_git(&source, &["commit", "--quiet", "-m", "base"]);
    let gitlink_object = test_git_stdout(&source, &["rev-parse", "HEAD"]);
    let cache_info = format!("160000,{gitlink_object},legacy/unmapped");
    test_git(
        &source,
        &["update-index", "--add", "--cacheinfo", &cache_info],
    );
    test_git(&source, &["commit", "--quiet", "-m", "unmapped gitlink"]);

    let destination = directory.path().join("destination");
    fs::create_dir(&destination).unwrap();
    fs::write(destination.join("last-good.txt"), "last-good\n").unwrap();

    let mut corpus = release_corpus();
    corpus.name = "staged-git".into();
    corpus.source = Source::Git;
    corpus.asset = None;
    corpus.sha256 = None;
    corpus.size_bytes = None;
    corpus.url = Some(source.to_string_lossy().into_owned());
    corpus.extract_to = destination.to_string_lossy().into_owned();
    corpus.commit = Some(test_git_stdout(&source, &["rev-parse", "HEAD"]));

    let error = download_git(&corpus, true)
        .expect_err("invalid staged checkout must not replace the prior destination");
    assert!(format!("{error:#}").contains("verify staged Git checkout before publication"));
    assert!(format!("{error:#}").contains("actual unmapped mode-160000 entries"));
    assert_eq!(
        fs::read_to_string(destination.join("last-good.txt")).unwrap(),
        "last-good\n"
    );
    assert!(!destination.join(".git").exists());
    assert!(corpus_work_directories(directory.path()).is_empty());
}

#[test]
fn git_checkout_verification_requires_exact_non_symlink_root() {
    let fixture = git_checkout_fixture();
    let mut nested = fixture.corpus.clone();
    nested.extract_to = fixture
        .checkout
        .join("nested")
        .to_string_lossy()
        .to_string();
    let error = verify_git_checkout(&nested).unwrap_err();
    assert!(format!("{error:#}").contains("not the exact git repository root"));

    #[cfg(unix)]
    {
        let alias = fixture._directory.path().join("checkout-alias");
        std::os::unix::fs::symlink(&fixture.checkout, &alias).unwrap();
        let mut symlinked = fixture.corpus.clone();
        symlinked.extract_to = alias.to_string_lossy().to_string();
        let error = verify_git_checkout(&symlinked).unwrap_err();
        assert!(format!("{error:#}").contains("non-symlink directory"));
    }
}

#[test]
fn git_checkout_verification_rejects_hidden_index_and_config_states() {
    let fixture = git_checkout_fixture();

    test_git(
        &fixture.checkout,
        &["update-index", "--skip-worktree", "asset.txt"],
    );
    let error = verify_git_checkout(&fixture.corpus).unwrap_err();
    assert!(format!("{error:#}").contains("unsupported index state"));
    test_git(
        &fixture.checkout,
        &["update-index", "--no-skip-worktree", "asset.txt"],
    );

    test_git(
        &fixture.checkout,
        &["update-index", "--assume-unchanged", "asset.txt"],
    );
    let error = verify_git_checkout(&fixture.corpus).unwrap_err();
    assert!(format!("{error:#}").contains("unsupported index state"));
    test_git(
        &fixture.checkout,
        &["update-index", "--no-assume-unchanged", "asset.txt"],
    );

    test_git(
        &fixture.checkout,
        &["config", "core.sparseCheckout", "true"],
    );
    let error = verify_git_checkout(&fixture.corpus).unwrap_err();
    assert!(format!("{error:#}").contains("unsupported sparse checkout"));
    test_git(
        &fixture.checkout,
        &["config", "core.sparseCheckout", "false"],
    );

    test_git(
        &fixture.checkout,
        &["config", "remote.origin.promisor", "true"],
    );
    let error = verify_git_checkout(&fixture.corpus).unwrap_err();
    assert!(format!("{error:#}").contains("partial/promisor"));
    test_git(
        &fixture.checkout,
        &["config", "--unset", "remote.origin.promisor"],
    );

    fs::write(fixture.checkout.join("ignored.tmp"), "hidden\n").unwrap();
    let error = verify_git_checkout(&fixture.corpus).unwrap_err();
    assert!(format!("{error:#}").contains("ignored extra files"));
    fs::remove_file(fixture.checkout.join("ignored.tmp")).unwrap();

    fs::write(fixture.checkout.join("untracked.txt"), "extra\n").unwrap();
    let error = verify_git_checkout(&fixture.corpus).unwrap_err();
    assert!(format!("{error:#}").contains("untracked files"));
}

#[test]
fn git_checkout_verification_rejects_unmerged_index() {
    let mut fixture = git_checkout_fixture();
    test_git(&fixture.checkout, &["checkout", "-q", "-b", "other"]);
    fs::write(fixture.checkout.join("asset.txt"), "other\n").unwrap();
    test_git(&fixture.checkout, &["commit", "-qam", "other"]);
    test_git(&fixture.checkout, &["checkout", "-q", "main"]);
    fs::write(fixture.checkout.join("asset.txt"), "main\n").unwrap();
    test_git(&fixture.checkout, &["commit", "-qam", "main"]);
    fixture.corpus.commit = Some(test_git_stdout(&fixture.checkout, &["rev-parse", "HEAD"]));
    let output = ProcCommand::new("git")
        .arg("-C")
        .arg(&fixture.checkout)
        .args(["merge", "other"])
        .output()
        .unwrap();
    assert!(!output.status.success());

    let error = verify_git_checkout(&fixture.corpus).unwrap_err();
    assert!(format!("{error:#}").contains("unmerged index entries"));
}

#[test]
fn git_checkout_verification_rejects_missing_current_tree_object() {
    let fixture = git_checkout_fixture();
    let object = test_git_stdout(&fixture.checkout, &["rev-parse", "HEAD:asset.txt"]);
    let git_directory = test_git_stdout(&fixture.checkout, &["rev-parse", "--git-dir"]);
    let object_path = fixture
        .checkout
        .join(git_directory)
        .join("objects")
        .join(&object[..2])
        .join(&object[2..]);
    fs::remove_file(object_path).unwrap();

    let error = verify_git_checkout(&fixture.corpus).unwrap_err();
    assert!(format!("{error:#}").contains("missing or corrupt objects"));
}

#[test]
fn git_checkout_verification_rejects_unresolved_lfs_pointer() {
    let mut fixture = git_checkout_fixture();
    fs::write(
        fixture.checkout.join(".gitattributes"),
        "large.bin filter=lfs diff=lfs merge=lfs -text\n",
    )
    .unwrap();
    fs::write(
        fixture.checkout.join("large.bin"),
        "version https://git-lfs.github.com/spec/v1\n\
         oid sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\n\
         size 123\n",
    )
    .unwrap();
    test_git(&fixture.checkout, &["add", ".gitattributes", "large.bin"]);
    test_git(
        &fixture.checkout,
        &["commit", "--quiet", "-m", "lfs pointer"],
    );
    fixture.corpus.commit = Some(test_git_stdout(&fixture.checkout, &["rev-parse", "HEAD"]));

    let error = verify_git_checkout(&fixture.corpus).unwrap_err();
    assert!(format!("{error:#}").contains("only an unresolved pointer"));
}

#[test]
fn git_lfs_attributes_without_pointer_blobs_do_not_require_git_lfs() {
    let mut fixture = git_checkout_fixture();
    fs::write(
        fixture.checkout.join(".gitattributes"),
        "*.mat filter=lfs diff=lfs merge=lfs -text\n",
    )
    .unwrap();
    fs::write(
        fixture.checkout.join("small.mat"),
        "ordinary tracked matrix fixture\n",
    )
    .unwrap();
    fs::write(fixture.checkout.join("large.mat"), vec![0x5a; 4096]).unwrap();
    test_git(
        &fixture.checkout,
        &["add", ".gitattributes", "small.mat", "large.mat"],
    );
    test_git(
        &fixture.checkout,
        &["commit", "--quiet", "-m", "ordinary attributed blobs"],
    );
    fixture.corpus.commit = Some(test_git_stdout(&fixture.checkout, &["rev-parse", "HEAD"]));

    verify_git_checkout(&fixture.corpus)
        .expect("LFS attributes alone must not require the git-lfs executable");
    fixture.corpus.requires_git_lfs = true;
    let error = verify_git_checkout(&fixture.corpus).unwrap_err();
    assert!(format!("{error:#}").contains("does not match the pinned tree"));
}

#[cfg(unix)]
#[test]
fn git_checkout_verification_refuses_a_symlinked_ancestor() {
    let fixture = git_checkout_fixture();
    let root = fixture.checkout.parent().unwrap();
    let alias = root.join("ancestor-alias");
    std::os::unix::fs::symlink(root, &alias).unwrap();
    let mut aliased = fixture.corpus.clone();
    aliased.extract_to = alias.join("checkout").to_string_lossy().to_string();
    let error = verify_git_checkout(&aliased).unwrap_err();
    assert!(format!("{error:#}").contains("must use its canonical non-symlink path"));
    assert!(verify_git_checkout(&fixture.corpus).is_ok());
}
