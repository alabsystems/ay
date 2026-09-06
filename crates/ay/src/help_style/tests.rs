// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// The invariant every redirected run depends on: with color off, a painted
/// string is the plain string — not the plain string wrapped in empty escape
/// pairs, which is what a naive `format!` guard leaves behind and what shows up
/// as `ESC[0m` litter in a file someone later greps.
#[test]
fn painting_with_color_off_leaves_no_escape_bytes() {
    for (style, text) in [
        (HEADER, "Usage:"),
        (LITERAL, "ay solve"),
        (PLACEHOLDER, "<FILE>"),
    ] {
        let painted = paint_when(false, style, text);
        assert!(
            !painted.contains('\u{1b}'),
            "escape byte survived with color off: {painted:?}"
        );
        assert_eq!(painted, text, "color off must yield the bare text");
    }
}

/// Color adds bytes AROUND the text and changes none of it, or a NO_COLOR
/// reader is reading a different screen from everyone else rather than the same
/// screen in one color.
#[test]
fn color_wraps_the_text_without_altering_it() {
    let painted = paint_when(true, HEADER, "Examples:");
    assert!(painted.contains('\u{1b}'), "color on must actually style");
    assert!(
        painted.contains("Examples:"),
        "the text must survive: {painted:?}"
    );
    // Everything outside the escape sequences is exactly the original text.
    let stripped = strip_ansi(&painted);
    assert_eq!(stripped, "Examples:");
}

/// Every style in the palette must survive the strip test — a screen is
/// authored once and read in both modes, so none of them may smuggle a
/// character of its own into the text.
#[test]
fn every_palette_style_strips_back_to_its_input() {
    for style in [HEADER, LITERAL, PLACEHOLDER, INVALID, ERROR] {
        assert_eq!(strip_ansi(&paint_when(true, style, "token")), "token");
    }
}

/// Remove ANSI SGR sequences, so a test can assert on what a NO_COLOR reader
/// sees without depending on the exact escape bytes anstyle chooses.
fn strip_ansi(s: &str) -> String {
    let mut out = String::new();
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' {
            // Skip through the terminating byte of the sequence.
            for c in chars.by_ref() {
                if c.is_ascii_alphabetic() {
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}
