// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! KC7 (interface freeze v2): the kernel and its plug-ins are `Send`, and no
//! state of theirs lives in a thread-local or in a process-wide static keyed
//! by `TermId`. A `TermId` names a term of one store; a thread-local or a
//! static keyed by it is wrong as soon as two engines (two workers, two
//! stores) run in one process, and it silently pins an engine to a thread.
//!
//! This test is the lint: it reads every source file of the crate.

use std::path::{Path, PathBuf};

fn sources(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir).expect("source directory is readable");
    for entry in entries {
        let path = entry.expect("directory entry").path();
        if path.is_dir() {
            sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

/// Lines of `text` outside `//` comments that declare forbidden state.
fn offences(text: &str) -> Vec<String> {
    let mut found = Vec::new();
    for (n, line) in text.lines().enumerate() {
        let code = line.split("//").next().unwrap_or_default();
        let thread_local = code.contains("thread_local!");
        let keyed_static = code.trim_start().starts_with("static ") && code.contains("TermId");
        if thread_local || keyed_static {
            found.push(format!("{}: {}", n + 1, line.trim()));
        }
    }
    found
}

#[test]
fn no_thread_local_or_term_keyed_static_in_the_kernel() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    sources(&root, &mut files);
    assert!(files.len() > 10, "found only {} source files", files.len());
    let mut bad = Vec::new();
    for file in files {
        let text = std::fs::read_to_string(&file).expect("source file is readable");
        for offence in offences(&text) {
            bad.push(format!("{}:{offence}", file.display()));
        }
    }
    assert!(
        bad.is_empty(),
        "KC7: thread-local or TermId-keyed static state:\n{}",
        bad.join("\n")
    );
}

#[test]
fn the_lint_sees_what_it_bans() {
    assert_eq!(offences("thread_local! { static X: u8 = 0; }").len(), 1);
    assert_eq!(
        offences("static SEEN: Mutex<Vec<TermId>> = Mutex::new(Vec::new());").len(),
        1
    );
    assert_eq!(
        offences("// thread_local! in a comment").as_slice(),
        &[] as &[String]
    );
    assert_eq!(offences("let id: TermId = t;").as_slice(), &[] as &[String]);
}
