// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to preserve private helper paths and behavior.

/// Lexer state of the stdin buffer, fed one physical line at a time, that
/// finds the top-level item still open at the buffer's end.
///
/// z3 reads a command on across lines until it closes, so the stdin loop
/// runs the complete items of the buffer and keeps the open one to read on.
/// The scan reads the text as z3's scanner and the [`CommandStream`] lexer
/// do:
///
/// - `;` starts a comment that runs to the end of the line;
/// - `"..."` is a string literal whose only escape is `""`;
/// - `|...|` is a quoted symbol in which `\` escapes the next character, so
///   `\|` does not end it and `\\|` does;
/// - a `)` with no list open is a stray token that z3 reports and skips, so
///   it opens and closes nothing.
///
/// A plain count of `(` and `)` evens out after a stray `)` and reads a
/// command still open as complete; a scan that ends a quoted symbol at `\|`
/// counts the parentheses inside it. Either one dropped the open command,
/// and z3 read it on into the next line.
///
/// Each line is scanned once, and the buffer is read only up to the start
/// of its open item, so a command spanning thousands of lines costs time
/// linear in its bytes.
#[derive(Default)]
struct IncrementalDepth {
    /// Lists open in the current top-level item.
    depth: usize,
    in_comment: bool,
    in_string: bool,
    /// The last byte closed a string literal; a `"` right after it is the
    /// `""` escape and reopens the same literal.
    string_just_closed: bool,
    in_pipe: bool,
    /// Inside a quoted symbol, the last byte was a `\` that escapes the next
    /// one.
    pipe_escape: bool,
    /// Buffer offset where the current top-level item begins.
    item_start: usize,
    /// Bytes fed since the buffer began: the buffer offset of the next byte.
    fed: usize,
}

impl IncrementalDepth {
    /// The state after reading all of `text` from the start of a buffer.
    fn scan(text: &str) -> Self {
        let mut state = Self::default();
        state.feed(text);
        state
    }

    /// Fold freshly read text (a physical line with its newline) into the
    /// state.
    fn feed(&mut self, text: &str) {
        for (index, &byte) in text.as_bytes().iter().enumerate() {
            self.step(self.fed + index, byte);
        }
        self.fed += text.len();
    }

    fn step(&mut self, offset: usize, byte: u8) {
        let string_just_closed = std::mem::take(&mut self.string_just_closed);
        if self.in_comment {
            self.in_comment = byte != b'\n';
            return;
        }
        if self.in_string {
            if byte == b'"' {
                self.in_string = false;
                self.string_just_closed = true;
            }
            return;
        }
        if self.in_pipe {
            if self.pipe_escape {
                self.pipe_escape = false;
            } else if byte == b'\\' {
                self.pipe_escape = true;
            } else if byte == b'|' {
                self.in_pipe = false;
            }
            return;
        }
        match byte {
            b';' => self.in_comment = true,
            b'"' => {
                if self.depth == 0 && !string_just_closed {
                    self.item_start = offset;
                }
                self.in_string = true;
            }
            b'|' => {
                if self.depth == 0 {
                    self.item_start = offset;
                }
                self.in_pipe = true;
            }
            b'(' => {
                if self.depth == 0 {
                    self.item_start = offset;
                }
                self.depth += 1;
            }
            b')' => self.depth = self.depth.saturating_sub(1),
            _ => {}
        }
    }

    /// The buffer offset where the item still open at the end of the fed
    /// text begins: an unclosed list, string literal or quoted symbol.
    /// `None` when every item read so far is complete.
    fn open_item(&self) -> Option<usize> {
        (self.depth > 0 || self.in_string || self.in_pipe).then_some(self.item_start)
    }

    /// Account for the first `cut` bytes of the buffer being removed. `cut`
    /// is the start of the open item, or the whole buffer when none is open.
    fn rebase(&mut self, cut: usize) {
        if self.open_item().is_none() {
            *self = Self::default();
            return;
        }
        self.item_start -= cut.min(self.item_start);
        self.fed -= cut.min(self.fed);
    }
}

/// The line and column just past `consumed`, a prefix of the stdin buffer
/// whose first character is at `line`, `column`.
fn position_after(consumed: &str, line: usize, column: usize) -> (usize, usize) {
    match consumed.rfind('\n') {
        Some(newline) => (
            line + consumed.matches('\n').count(),
            consumed[newline + 1..].chars().count() + 1,
        ),
        None => (line, column + consumed.chars().count()),
    }
}

#[cfg(test)]
mod stdin_buffer_tests {
    use super::*;

    /// Feed `input` one physical line at a time, as the stdin loop reads it.
    fn scan_by_line(input: &str) -> IncrementalDepth {
        let mut state = IncrementalDepth::default();
        for line in input.split_inclusive('\n') {
            state.feed(line);
        }
        state
    }

    fn open(input: &str) -> Option<usize> {
        let by_line = scan_by_line(input).open_item();
        assert_eq!(
            by_line,
            IncrementalDepth::scan(input).open_item(),
            "{input:?}"
        );
        by_line
    }

    #[test]
    fn complete_commands_leave_nothing_open() {
        assert_eq!(open("(check-sat)\n"), None);
        assert_eq!(open("(assert (= x 1)) (push 1)\n(assert x)\n"), None);
        assert_eq!(open("(a (b) (c (d)))\n"), None);
    }

    #[test]
    fn a_multi_line_command_stays_open_until_it_closes() {
        let mut state = IncrementalDepth::default();
        state.feed("(assert (or\n");
        assert_eq!(state.open_item(), Some(0));
        state.feed("  (= x 1)\n");
        assert_eq!(state.open_item(), Some(0));
        state.feed("  (= y 2)))\n");
        assert_eq!(state.open_item(), None);
    }

    #[test]
    fn a_stray_close_paren_does_not_hide_an_open_command() {
        // A plain count of `(` and `)` comes out even on this line.
        assert_eq!(open("(push 1) (assert false) ) (\n"), Some(26));
        assert_eq!(open("(assert p)) (\n"), Some(12));
        assert_eq!(open(") ) (echo \"a\n"), Some(4));
        let mut state = scan_by_line("(push 1) ) (\n");
        state.feed("pop 1)\n");
        assert_eq!(state.open_item(), None);
    }

    #[test]
    fn an_escaped_bar_does_not_end_a_quoted_symbol() {
        let line = "(push 1) (assert false) (get-info |a\\|)\n";
        assert_eq!(open(line), Some(24));
        let mut state = scan_by_line(line);
        state.feed("|) (pop 1)\n");
        assert_eq!(state.open_item(), None);
        // `\\` is an escaped backslash, so the bar after it ends the symbol.
        assert_eq!(open("(echo |a\\\\|)\n"), None);
        assert_eq!(open("(declare-const |a\\|b| Bool)\n"), None);
    }

    #[test]
    fn comments_strings_and_quoted_symbols_hold_inert_parens() {
        assert_eq!(open("(echo x) ; )))(((\n"), None);
        assert_eq!(open("(assert true ; ) ) )\n"), Some(0));
        assert_eq!(open("(echo \"(((\")\n"), None);
        assert_eq!(open("(echo \"a\"\"b)\")\n"), None);
        assert_eq!(open("(set-info :source |\n  ) ( text\n"), Some(0));
        assert_eq!(open("(set-info :source |\n  ) ( text\n|)\n"), None);
    }

    #[test]
    fn a_top_level_string_or_symbol_left_open_is_kept() {
        assert_eq!(open("(echo \"x\")|\n"), Some(10));
        assert_eq!(open("(check-sat) \"a\n"), Some(12));
        // `""` continues the same literal, which still begins at its first
        // quote.
        assert_eq!(open("(check-sat) \"a\"\"b\n"), Some(12));
        assert_eq!(open("(check-sat) \"a\" \"b\n"), Some(16));
    }

    #[test]
    fn rebasing_keeps_the_open_item_at_the_buffer_start() {
        let mut state = scan_by_line("(push 1) (assert\n");
        assert_eq!(state.open_item(), Some(9));
        state.rebase(9);
        assert_eq!(state.open_item(), Some(0));
        state.feed(" false)\n");
        assert_eq!(state.open_item(), None);
        state.rebase(15);
        assert_eq!(state.fed, 0);
        state.feed("(check-sat\n");
        assert_eq!(state.open_item(), Some(0));
    }

    #[test]
    fn positions_continue_after_a_consumed_prefix() {
        assert_eq!(position_after("(push 1) ", 3, 1), (3, 10));
        assert_eq!(position_after("(a)\n(b) ", 3, 5), (4, 5));
        assert_eq!(position_after("(a)\n", 3, 5), (4, 1));
    }
}
