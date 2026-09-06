// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One color decision, shared by every surface that prints.
//!
//! clap decides color for the screens IT renders, but ay prints plenty clap
//! never sees: the interactive banner, the `ay help <topic>` pages, the hint
//! lines under a REPL error, and — critically — the `before_help`/`after_help`
//! blocks, which clap passes through UNTOUCHED. A second, independent notion of
//! "are we in color?" is how those surfaces come to disagree, and the failure is
//! ugly in the direction that matters: raw escape bytes in a redirected file.
//!
//! So the decision lives here once, in [`effective_color`], and both clap and
//! every hand-printed surface ask it.
//!
//! THE PALETTE is two hues and a dim, borrowed from cargo because a Rust user
//! already reads it fluently. Color marks STRUCTURE and TYPEABLE TEXT, nothing
//! else: green for the headings that divide a screen, cyan for the literal
//! things a user can type, dim for punctuation and asides. Prose is never
//! colored — a sentence that lights up is a sentence competing with the command
//! next to it.
//!
//! WHAT IS NEVER COLORED, in any mode: the verdict lines. `sat`, `unsat`,
//! `unknown`, `s SATISFIABLE` are a machine contract, and a contract does not
//! change bytes because a human happens to be watching.

use std::io::IsTerminal;

use clap::builder::styling::{AnsiColor, Style, Styles};

/// The `--color <WHEN>` choice, in the conventional three states.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, clap::ValueEnum)]
pub(crate) enum ColorWhen {
    /// Color when stdout is a terminal and nothing in the environment objects.
    #[default]
    Auto,
    /// Color even when redirected — for piping into a pager that renders it.
    Always,
    /// Never color.
    Never,
}

impl std::fmt::Display for ColorWhen {
    /// The spelling the user typed, so clap's `[default: auto]` annotation and
    /// its error messages name the same three words this enum accepts.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Auto => "auto",
            Self::Always => "always",
            Self::Never => "never",
        })
    }
}

/// The process-wide `--color` choice, latched once during argument parsing so
/// the surfaces that print long after (the REPL, a topic page) agree with the
/// ones that printed during it.
static COLOR_WHEN: std::sync::OnceLock<ColorWhen> = std::sync::OnceLock::new();

/// Record the parsed `--color` choice. First call wins; later calls are ignored,
/// which keeps a nested parse from changing a decision already acted on.
pub(crate) fn set_color_when(when: ColorWhen) {
    let _ = COLOR_WHEN.set(when);
}

/// Whether ay should emit ANSI styling right now.
///
/// The environment is consulted in the order the conventions themselves imply:
/// an explicit flag beats an explicit env var, which beats the terminal's own
/// answer. `NO_COLOR` is honored for ANY non-empty value, per no-color.org —
/// treating `NO_COLOR=0` as "yes, color" is a reading of that standard which
/// surprises everyone who sets it.
pub(crate) fn effective_color() -> bool {
    match COLOR_WHEN.get().copied().unwrap_or_default() {
        ColorWhen::Always => return true,
        ColorWhen::Never => return false,
        ColorWhen::Auto => {}
    }
    // CLICOLOR_FORCE is the one env var that says "yes" rather than "no", and it
    // outranks the TTY check by design: it exists for CI logs and pagers.
    if std::env::var_os("CLICOLOR_FORCE").is_some_and(|v| !v.is_empty() && v != "0") {
        return true;
    }
    if std::env::var_os("NO_COLOR").is_some_and(|v| !v.is_empty()) {
        return false;
    }
    if std::env::var_os("AY_NO_COLOR").is_some_and(|v| !v.is_empty()) {
        return false;
    }
    if std::env::var_os("CLICOLOR").is_some_and(|v| v == "0") {
        return false;
    }
    // A terminal that cannot render escapes is not a terminal for this purpose.
    if std::env::var_os("TERM").is_some_and(|t| t == "dumb") {
        return false;
    }
    std::io::stdout().is_terminal()
}

/// [`effective_color`] as clap's own enum, so the screens clap renders and the
/// screens ay renders cannot disagree.
pub(crate) fn clap_color() -> clap::ColorChoice {
    if effective_color() {
        clap::ColorChoice::Always
    } else {
        clap::ColorChoice::Never
    }
}

const HEADER: Style = AnsiColor::BrightGreen.on_default().bold();
const LITERAL: Style = AnsiColor::BrightCyan.on_default().bold();
const PLACEHOLDER: Style = AnsiColor::Cyan.on_default();
const INVALID: Style = AnsiColor::Yellow.on_default().bold();
const ERROR: Style = AnsiColor::Red.on_default().bold();

/// The style set clap renders `--help` and its errors with.
///
/// `anstyle` arrives through clap's own re-export rather than as a dependency of
/// ours: it is already in the build graph beneath clap, so this palette costs no
/// new external code — which is the whole point, given the no-outside-deps rule.
pub(crate) const STYLES: Styles = Styles::styled()
    .header(HEADER)
    .usage(HEADER)
    .literal(LITERAL)
    .placeholder(PLACEHOLDER)
    .invalid(INVALID)
    .error(ERROR);

/// Wrap `text` in `style` when color is on, and return it untouched when it is
/// off — so a caller never has to ask, and a screen printed with color off
/// contains no escape bytes at all rather than empty escape pairs.
pub(crate) fn paint(style: Style, text: &str) -> String {
    paint_when(effective_color(), style, text)
}

/// [`paint`] with the decision handed in rather than read from the process.
///
/// Split out so the styling can be tested for what it promises — that color off
/// yields the bare bytes — without a test having to reach through the
/// process-wide latch and the real environment to arrange it.
fn paint_when(color: bool, style: Style, text: &str) -> String {
    if color {
        format!("{style}{text}{style:#}")
    } else {
        text.to_string()
    }
}

/// A section heading on a hand-printed screen (`Usage:`, `Examples:`).
pub(crate) fn header(text: &str) -> String {
    paint(HEADER, text)
}

/// Something the reader can literally type: a command, a flag, an s-expression.
pub(crate) fn literal(text: &str) -> String {
    paint(LITERAL, text)
}

/// Punctuation, asides, and the annotations that must not compete with the
/// commands beside them.
pub(crate) fn dim(text: &str) -> String {
    paint(Style::new().dimmed(), text)
}

#[cfg(test)]
mod tests;
