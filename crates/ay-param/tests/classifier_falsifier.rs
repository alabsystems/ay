// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE MIGRATION CLASSIFIER, AND ITS FALSIFIER.
//!
//! A tool that rewrites 1,160 `env::var` call sites must first be shown to read them
//! correctly. The falsifier the design specifies: run the classifier over the knobs
//! `tune.rs` ALREADY migrated and require it to reproduce the accessor that actually
//! shipped. A disagreement there is a classifier bug found before it touches
//! anything.
//!
//! This is the cheapest possible ground truth — `tune.rs` is a hand-written,
//! reviewed, measured migration of exactly this kind, so it is a labelled set that
//! cost nothing to produce.

use ay_param::Shape;
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    // crates/ay-param -> crates -> repo
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crate must live two levels below the repo root")
        .to_path_buf()
}

/// Classify one `env::var` call site from the source text that follows it.
///
/// Deliberately syntactic and deliberately CONSERVATIVE: it returns `None` rather
/// than guess. `tune.rs` records the reason a guess is unacceptable —
/// `finite_nonnegative_setting` clamps with `.max(0.0)` where the resolver rejects,
/// which is a behaviour change on one input class. Sites that match no shape are
/// LISTED for a human, never auto-rewritten.
fn classify(after: &str) -> Option<Shape> {
    // Bound the window to this statement; a fixed byte window reaches into the next
    // knob's chain, which is a mistake this repo has already made once.
    let end = after.find(';').map_or(after.len(), |n| n + 1);
    let end = (0..=end)
        .rev()
        .find(|&n| after.is_char_boundary(n))
        .unwrap_or(0);
    let stmt = &after[..end];
    let is_var_os = stmt.starts_with("_os");

    if stmt.contains(".parse::<f64>()") || stmt.contains("finite_nonnegative") {
        return Some(Shape::Real);
    }
    if stmt.contains(".parse::<") || stmt.contains(".parse()") {
        return Some(Shape::Num);
    }
    if is_var_os && (stmt.contains(".is_some()") || stmt.contains(".is_none()")) {
        return Some(Shape::On);
    }
    if stmt.contains("== Ok(\"1\")") || stmt.contains("as_deref() == Ok(\"1\")") {
        return Some(Shape::OnStrict);
    }
    if stmt.contains("!= \"0\"") || stmt.contains("v != \"0\"") {
        return Some(Shape::OnUnlessZero);
    }
    if stmt.contains("== \"1\"") {
        return Some(Shape::OnStrict);
    }
    None
}

/// GROUND TRUTH, read off the call sites rather than guessed.
///
/// The first draft of this table guessed from `tune::Knob`'s doc comments and was
/// WRONG on three of six — and the falsifier caught it, which is the falsifier
/// working. `RootProbe`, `NodeCuts` and `Plunge` are described in prose as things
/// you turn on, and are read as `var_os(..).is_some()`, `is_none()` and
/// `map_or(true, |v| v != "0")` respectively. The lesson is the one the design
/// states about nominating a feature with hindsight: the label has to come from the
/// code, not from what the code sounds like.
///
/// A knob maps to the SET of shapes its sites use, not to one shape.
fn ground_truth() -> Vec<(&'static str, Vec<Shape>)> {
    vec![
        // Presence tests: "has the operator expressed an opinion at all".
        ("AY_MILP_ROOT_PROBE", vec![Shape::On]),
        ("AY_MILP_NODE_CUTS", vec![Shape::On]),
        ("AY_MILP_DFS", vec![Shape::On]),
        // On unless explicitly "0".
        ("AY_MILP_PLUNGE", vec![Shape::OnUnlessZero]),
        // TWO SHAPES, ONE NAME. `AY_MILP_GMI_ROUNDS` is a PRESENCE test at three
        // sites in bab.rs (guarding the tiny / gi-ext / bottleneck-ext gates: "did
        // the operator override the rounds at all") and a PARSED NUMBER at
        // cuts.rs:1422 (the rounds themselves). Both are deliberate and neither is
        // redundant, which is exactly why a migration must classify PER SITE. A
        // per-name rewriter would flatten one of them and silently change what an
        // override means.
        ("AY_MILP_GMI_ROUNDS", vec![Shape::On, Shape::Num]),
        ("AY_MILP_ROOT_CUTS_PER_ROUND", vec![Shape::Num]),
    ]
}

/// The classifier must agree with the code that actually shipped, at every site.
#[test]
fn the_classifier_reproduces_the_shipped_accessor() {
    let milp = repo_root().join("crates/ay-milp/src");
    let mut sources = Vec::new();
    collect(&milp, &mut sources);

    let mut disagreements = Vec::new();
    let mut sites_seen = 0usize;
    for (name, expected) in ground_truth() {
        let mut got: Vec<Shape> = Vec::new();
        for text in &sources {
            let quoted = format!("\"{name}\"");
            let needle = "env::var";
            let mut from = 0usize;
            while let Some(i) = text[from..].find(needle) {
                let at = from + i;
                let tail = &text[at + needle.len()..];
                let cut = (0..=80.min(tail.len()))
                    .rev()
                    .find(|&n| tail.is_char_boundary(n))
                    .unwrap_or(0);
                if tail[..cut].contains(&quoted) {
                    sites_seen += 1;
                    if let Some(s) = classify(tail) {
                        if !got.contains(&s) {
                            got.push(s);
                        }
                    }
                }
                from = at + needle.len();
            }
        }
        got.sort_by_key(|s| format!("{s:?}"));
        let mut want = expected.clone();
        want.sort_by_key(|s| format!("{s:?}"));
        if got != want {
            disagreements.push(format!(
                "  {name}: classifier says {got:?}, the code does {want:?}"
            ));
        }
    }
    assert!(
        sites_seen > 0,
        "the falsifier found no sites; it is testing nothing"
    );
    assert!(
        disagreements.is_empty(),
        "the classifier disagrees with the code that actually shipped, on {} knob(s). \
         Fix the classifier BEFORE it rewrites 1,160 sites.\n{}",
        disagreements.len(),
        disagreements.join("\n")
    );
}

/// A NAME READ WITH TWO SHAPES CANNOT BE MIGRATED PER NAME.
///
/// `AY_MILP_GMI_ROUNDS` is the in-tree instance. This pins the property that makes
/// the classifier per-site: if it ever collapses to one shape here, a rewriter built
/// on it would silently change what an override means at three of the four sites.
#[test]
fn a_name_may_carry_more_than_one_shape() {
    let want = ground_truth()
        .into_iter()
        .find(|(n, _)| *n == "AY_MILP_GMI_ROUNDS")
        .map(|(_, s)| s)
        .expect("fixture");
    assert!(
        want.len() > 1,
        "GMI_ROUNDS is read as presence in bab.rs and as a number in cuts.rs; \
         a per-NAME migration would flatten that"
    );
}

/// A site the classifier cannot read must come back `None`, never a guess. This is
/// the property that keeps a mechanical migration safe: unknown shapes are listed
/// for a human instead of rewritten.
#[test]
fn an_unrecognised_site_is_not_guessed() {
    assert_eq!(classify("(\"AY_X\").ok().map(|v| weird(v));"), None);
    assert_eq!(classify("(\"AY_X\");"), None);
}

fn collect(dir: &Path, into: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect(&p, into);
        } else if p.extension().is_some_and(|x| x == "rs") {
            if let Ok(t) = std::fs::read_to_string(&p) {
                into.push(t);
            }
        }
    }
}
