// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// The width every authored screen is held to.
///
/// 79 rather than 80 so a line that lands exactly at the edge still has a column
/// to spare in a terminal that reserves one for a wrap marker. Enforced here
/// instead of trusted to the author, because the failure is invisible on the
/// wide terminal a developer writes it on and obvious on the 80-column one a
/// user reads it in.
const MAX_WIDTH: usize = 79;

#[test]
fn every_topic_page_fits_eighty_columns() {
    for topic in TOPICS {
        for (n, line) in topic.body.lines().enumerate() {
            assert!(
                line.chars().count() <= MAX_WIDTH,
                "ay help {}: line {} is {} columns (max {MAX_WIDTH}):\n{line}",
                topic.name,
                n + 1,
                line.chars().count()
            );
        }
    }
}

/// Color is applied at render time, never baked in. A page carrying its own
/// escape bytes would print them raw into a redirected file, since clap and the
/// topic renderer both pass these constants through untouched.
#[test]
fn no_topic_page_carries_ansi_escapes() {
    for topic in TOPICS {
        assert!(
            !topic.body.contains('\u{1b}'),
            "ay help {}: the page body contains an ANSI escape",
            topic.name
        );
    }
}

/// A page that opens with a usage line teaches nothing to the person who opened
/// it to find out what the thing IS. Every page leads with prose.
#[test]
fn every_topic_page_opens_with_prose() {
    for topic in TOPICS {
        let first = topic.body.lines().next().unwrap_or_default();
        assert!(
            !first.trim_start().starts_with("Usage:") && !first.trim_start().starts_with("usage:"),
            "ay help {} opens with a usage line: {first:?}",
            topic.name
        );
        assert!(
            !first.trim().is_empty(),
            "ay help {} opens with a blank line",
            topic.name
        );
    }
}

/// The pointer chain: no screen dead-ends. Every page has to hand the reader
/// somewhere to go next, and the only way to say that in these pages is to name
/// a command.
#[test]
fn every_topic_page_names_a_next_command() {
    for topic in TOPICS {
        assert!(
            topic.body.contains("ay "),
            "ay help {} never names another ay command to run next",
            topic.name
        );
    }
}

/// Topic names are what a user types. A duplicate would shadow a page
/// permanently, and the `find` in `print` would never reach the second one.
#[test]
fn topic_names_are_unique_and_typeable() {
    let mut seen = std::collections::BTreeSet::new();
    for topic in TOPICS {
        assert!(
            seen.insert(topic.name),
            "two topics are both named {:?}",
            topic.name
        );
        assert!(
            topic
                .name
                .chars()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-'),
            "topic {:?} is not typeable without shifting",
            topic.name
        );
        assert!(
            !topic.blurb.is_empty(),
            "topic {:?} has no blurb",
            topic.name
        );
    }
}

/// An unknown topic must fail as a USAGE error, not silently succeed — a script
/// that asks for a page ay does not have should hear about it.
#[test]
fn an_unknown_topic_is_a_usage_error() {
    assert_eq!(print(Some("no-such-topic-exists")), 2);
}

/// Headings are found by shape, not markup, so the constants stay plain text.
/// This pins the shape both the pages and the renderer rely on.
#[test]
fn heading_detection_matches_the_convention() {
    assert!(is_heading("Known divergences:"));
    assert!(!is_heading("  indented: not a heading"));
    assert!(!is_heading("a sentence that merely ends in prose"));
    assert!(!is_heading(""));
}

/// THE DRIFT GUARD. `ay commands` groups the commands editorially, which clap
/// cannot do for us — it knows each command's description but nothing about
/// which ones belong together. The cost of writing that by hand is that it can
/// fall behind the parser, and a command missing from the one screen that
/// claims to list them all is worse than no screen.
///
/// So: every VISIBLE subcommand must appear on the page. Hidden ones must not —
/// they are maintainer machinery, and listing them would bury the ten commands
/// a user actually wants among twenty-five they do not.
#[test]
fn the_commands_page_names_every_visible_subcommand() {
    use clap::CommandFactory;
    let page = include_str!("commands.txt");
    let root = crate::Cli::command();
    for sub in root.get_subcommands() {
        let name = sub.get_name();
        let listed = page
            .lines()
            .any(|line| line.trim_start().starts_with(&format!("{name} ")));
        if sub.is_hide_set() {
            assert!(
                !listed,
                "`{name}` is hidden but listed on the commands page"
            );
        } else {
            assert!(
                listed,
                "`{name}` is a visible command but the commands page never lists it — \
                 add it to its group in help_topics/commands.txt"
            );
        }
    }
}

/// Both self-describing screens obey the same width and cleanliness rules the
/// topic pages do; they are just reached by a different verb.
#[test]
fn the_self_describing_screens_fit_and_carry_no_escapes() {
    for (name, body) in [
        ("commands", include_str!("commands.txt")),
        ("options", include_str!("options.txt")),
    ] {
        assert!(
            !body.contains('\u{1b}'),
            "ay {name}: contains an ANSI escape"
        );
        for (n, line) in body.lines().enumerate() {
            assert!(
                line.chars().count() <= MAX_WIDTH,
                "ay {name}: line {} is {} columns (max {MAX_WIDTH}):\n{line}",
                n + 1,
                line.chars().count()
            );
        }
    }
}

/// Every AY_* variable the options page documents must actually be read
/// somewhere in the workspace. A help page naming an environment variable that
/// nothing consults is a promise the binary does not keep, and it is the exact
/// failure the page's author was most at risk of.
///
/// The search covers the whole workspace, not just this crate: the options a
/// user sets reach the engines, so `AY_DT_CERT` lives in ay-dpll and is no less
/// real for it. An earlier version of this test read four files from `ay` and
/// called that variable invented, which is the wrong answer loudly.
#[test]
fn every_documented_env_var_is_read_somewhere() {
    let page = include_str!("options.txt");
    let crates_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates/ay has a parent");

    let mut sources = String::new();
    let mut stack = vec![crates_dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                // `target` holds build output, not source, and dwarfs it.
                if path.file_name().is_some_and(|n| n == "target") {
                    continue;
                }
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                if let Ok(text) = std::fs::read_to_string(&path) {
                    sources.push_str(&text);
                }
            }
        }
    }

    let mut checked = 0;
    for word in page.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_')) {
        if !word.starts_with("AY_") || word.len() < 4 {
            continue;
        }
        checked += 1;
        assert!(
            sources.contains(word),
            "the options page documents {word}, but no source in the workspace reads it"
        );
    }
    assert!(
        checked > 0,
        "the options page documents no AY_* variable at all"
    );
}

/// `KNOWN_SUBCOMMANDS` is the argv preprocessor's idea of which first words are
/// verbs rather than filenames. It is hand-maintained beside the clap enum, so
/// it can fall behind it — and when it does the failure is silent and baffling:
/// the new verb is treated as a FILE to solve, and the user sees
///
///     (error "Error reading file 'commands': No such file or directory")
///
/// which is exactly what `ay commands` and `ay options` did on their first run.
/// A missing name costs a working command; a stale extra name costs nothing, so
/// this asserts coverage in the direction that actually breaks.
#[test]
fn the_preprocessor_knows_every_clap_subcommand() {
    use clap::CommandFactory;
    for sub in crate::Cli::command().get_subcommands() {
        let name = sub.get_name();
        assert!(
            crate::KNOWN_SUBCOMMANDS.contains(&name),
            "`{name}` is a subcommand but KNOWN_SUBCOMMANDS omits it, so \
             `ay {name}` is parsed as a filename to solve"
        );
    }
}
