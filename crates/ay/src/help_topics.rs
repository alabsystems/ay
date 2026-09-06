// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay help <topic>` — the long-form pages, and the self-describing screens.
//!
//! WHY THESE EXIST. `--help` used to end in a 47-line wall: every z3 option
//! spelling, the format-detection rules, and the compatibility no-ops, printed
//! in full to everyone who typed `ay --help` for any reason at all. Reference
//! material that long does not belong on the screen a user reaches for to
//! remember one flag — but it is real documentation, and deleting it would cost
//! a z3 user the one page they most need. So it moved here, where it is one
//! command away and can be as long as it deserves to be.
//!
//! The rule every page follows: open with prose saying what the thing IS, and
//! close by naming the exact next command. No screen in ay dead-ends.
//!
//! Pages are PLAIN TEXT. Color is applied at render time through
//! [`crate::help_style`], never baked into the constants, so a redirected
//! `ay help z3` contains no escape bytes and the NO_COLOR reader sees the same
//! words in the same places.

use crate::help_style::{header, literal};

/// A `ay help <topic>` page: the name a user types, and the text it prints.
struct Topic {
    /// The word after `ay help`.
    name: &'static str,
    /// One line, shown in the topic list.
    blurb: &'static str,
    /// The page itself, plain text, every line <= 79 columns.
    body: &'static str,
}

/// Every topic, in the order the list shows them — which is the order a user
/// meets them, not alphabetical: compatibility first because that is why most
/// people arrive, then the mechanics, then the contracts.
const TOPICS: &[Topic] = &[
    Topic {
        name: "z3",
        blurb: "z3 option spellings ay accepts, and where it deliberately differs",
        body: include_str!("help_topics/z3.txt"),
    },
    Topic {
        name: "formats",
        blurb: "how ay decides what it is reading, and every front end it has",
        body: include_str!("help_topics/formats.txt"),
    },
    Topic {
        name: "exit-codes",
        blurb: "what ay's exit codes mean, per mode",
        body: include_str!("help_topics/exit-codes.txt"),
    },
    Topic {
        name: "output",
        blurb: "the contract between ay's output and whatever reads it",
        body: include_str!("help_topics/output.txt"),
    },
];

/// Print one topic page, the topic list, or an error naming both sets.
///
/// Returns the process exit code: 0 for a page or the list, 2 for a name that
/// is neither a topic nor a command — a usage error, since the user typed
/// something ay cannot act on.
pub(crate) fn print(topic: Option<&str>) -> i32 {
    let Some(name) = topic else {
        print_list();
        return 0;
    };
    if let Some(found) = TOPICS.iter().find(|t| t.name == name) {
        print_page(found);
        return 0;
    }
    // A command name is the OTHER thing a user plausibly means by `ay help X`,
    // and clap already prints that screen better than this module could — so
    // hand it over rather than reimplementing it.
    if is_command_name(name) {
        return print_command_help(name);
    }
    safe_eprintln!("error: '{name}' is not a help topic or a command");
    safe_eprintln!();
    safe_eprintln!("  topics:   {}", topic_names().join(" "));
    safe_eprintln!("  commands: run `ay commands` for the full list");
    2
}

/// The topic names, for the list line and the error message — one source, so a
/// topic added below can never go unlisted in either place.
fn topic_names() -> Vec<&'static str> {
    TOPICS.iter().map(|t| t.name).collect()
}

/// `ay commands` — every visible command, grouped by what you are trying to do.
///
/// Grouping is editorial and lives in the page, not derived from clap: clap
/// knows each command's one-line description but nothing about which of them
/// belong together, and a list of twenty names in declaration order is a list,
/// not an answer. A drift test asserts the page names every visible subcommand,
/// so the editorial half cannot fall behind the parser.
pub(crate) fn print_commands() {
    print_body(include_str!("help_topics/commands.txt"));
}

/// `ay options` — the AY_* environment options and what each one does.
pub(crate) fn print_options() {
    print_body(include_str!("help_topics/options.txt"));
}

/// Print a plain-text screen, styling only the lines it marks as headings.
fn print_body(body: &str) {
    for line in body.lines() {
        if is_heading(line) {
            safe_println!("{}", header(line));
        } else {
            safe_println!("{line}");
        }
    }
}

fn print_list() {
    safe_println!("ay's long-form help topics. Each is one command away:");
    safe_println!();
    let width = TOPICS.iter().map(|t| t.name.len()).max().unwrap_or(0);
    for topic in TOPICS {
        safe_println!(
            "  {}  {}",
            literal(&format!("{:<width$}", topic.name, width = width)),
            topic.blurb
        );
    }
    safe_println!();
    safe_println!(
        "Read one with {}. For the commands themselves, run {}.",
        literal("ay help <topic>"),
        literal("ay commands")
    );
}

fn print_page(topic: &Topic) {
    // The body is plain text by construction; the only styling applied is to
    // the lines the page itself marks as headings, which is what keeps a
    // redirected page byte-identical to what a NO_COLOR reader sees.
    print_body(topic.body);
}

/// A heading is a non-indented line ending in a colon — the one typographic
/// convention these pages use, so the renderer can find them without the
/// constants carrying markup.
fn is_heading(line: &str) -> bool {
    !line.starts_with(' ') && line.ends_with(':') && !line.is_empty()
}

/// Whether `name` is a visible ay subcommand, so `ay help <command>` can route
/// to that command's own `--help` instead of failing.
fn is_command_name(name: &str) -> bool {
    use clap::CommandFactory;
    crate::Cli::command()
        .get_subcommands()
        .any(|sub| sub.get_name() == name && !sub.is_hide_set())
}

/// Render a subcommand's own long help, exactly as `ay <command> --help` would.
fn print_command_help(name: &str) -> i32 {
    use clap::CommandFactory;
    let mut root = crate::Cli::command();
    let Some(sub) = root.find_subcommand_mut(name) else {
        return 2;
    };
    safe_println!("{}", sub.render_long_help());
    0
}

#[cfg(test)]
mod tests;
