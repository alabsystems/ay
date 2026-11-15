// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to preserve private helper paths and behavior.

/// The sources of the items a [`CommandStream`] reads, each taken from the
/// text that item consumed. Indexing the balanced chunks of
/// [`collect_command_sources`] instead goes out of step after a stray token,
/// which has no chunk, and gives a command another command's text: a check
/// that scans the text for a label name then reads the wrong command.
struct StreamSources {
    /// Byte offset `line` and `column` describe.
    offset: usize,
    line: usize,
    column: usize,
}

impl StreamSources {
    /// Positions in a text whose first character is at `first_line`,
    /// `first_column`.
    fn new(first_line: usize, first_column: usize) -> Self {
        Self {
            offset: 0,
            line: first_line,
            column: first_column,
        }
    }

    /// The source of the item read from `input[start..end]`, from its first
    /// token to the end of its last one. Items are taken in input order.
    fn source(&mut self, input: &str, start: usize, end: usize) -> CommandSource {
        let consumed = input.get(start..end).unwrap_or_default();
        let body = skip_smt_trivia(consumed);
        let body_start = start + (consumed.len() - body.len());
        for ch in input
            .get(self.offset..body_start)
            .unwrap_or_default()
            .chars()
        {
            if ch == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
        }
        self.offset = self.offset.max(body_start);
        CommandSource {
            line: self.line,
            column: self.column,
            text: body[..end_of_last_token(body)].to_string(),
        }
    }
}

/// Byte offset just past the last token of `text`, skipping whitespace and
/// `;` comments, and reading string literals and quoted symbols as the
/// command stream does.
fn end_of_last_token(text: &str) -> usize {
    let bytes = text.as_bytes();
    let mut index = 0usize;
    let mut end = 0usize;
    while index < bytes.len() {
        match bytes[index] {
            b';' => {
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                }
            }
            byte if byte.is_ascii_whitespace() => index += 1,
            b'"' => {
                index += 1;
                while index < bytes.len() {
                    if bytes[index] == b'"' {
                        if bytes.get(index + 1) == Some(&b'"') {
                            index += 2;
                            continue;
                        }
                        index += 1;
                        break;
                    }
                    index += 1;
                }
                end = index;
            }
            b'|' => {
                index += 1;
                while index < bytes.len() {
                    match bytes[index] {
                        b'\\' => index = (index + 2).min(bytes.len()),
                        b'|' => {
                            index += 1;
                            break;
                        }
                        _ => index += 1,
                    }
                }
                end = index;
            }
            _ => {
                index += 1;
                end = index;
            }
        }
    }
    end
}

/// Make `source` the current command's source and count the command.
fn set_current_source(state: &mut SmtTranscriptState, source: CommandSource) {
    state.current_source = Some(source);
    state.current_command_ordinal = state.processed_commands;
    state.processed_commands = state.processed_commands.saturating_add(1);
}

/// One top-level item of a complete stdin buffer, in input order, with the
/// source it was read from.
enum StdinCommand {
    Parsed(Box<Command>, CommandSource),
    /// A command that failed to parse and is dropped.
    Dropped(ay_frontend::ParseError, CommandSource),
}

/// Read a stdin buffer one command at a time, as file mode reads a file.
/// z3 runs every well-formed command on a line beside a malformed one, so a
/// parse error must not drop the line's other declarations, options and
/// queries. The buffer's first character is at `first_line`,
/// `first_column`.
fn read_stdin_commands(buffer: &str, first_line: usize, first_column: usize) -> Vec<StdinCommand> {
    let mut stream = CommandStream::new(buffer);
    let mut sources = StreamSources::new(first_line, first_column);
    let mut commands = Vec::new();
    loop {
        let start = stream.position();
        let Some(item) = stream.next_command() else {
            break;
        };
        let source = sources.source(buffer, start, stream.position());
        commands.push(match item {
            CommandStreamItem::Command(cmd) => StdinCommand::Parsed(cmd, source),
            CommandStreamItem::Error(err) => StdinCommand::Dropped(err, source),
        });
    }
    commands
}

#[cfg(test)]
mod stream_sources_tests {
    use super::*;

    fn sources(input: &str) -> Vec<(usize, usize, String)> {
        read_stdin_commands(input, 3, 1)
            .into_iter()
            .map(|item| match item {
                StdinCommand::Parsed(_, source) | StdinCommand::Dropped(_, source) => {
                    (source.line, source.column, source.text)
                }
            })
            .collect()
    }

    #[test]
    fn each_item_keeps_its_own_text_after_a_stray_token() {
        let got = sources("(declare-const p Bool) ) (assert L)\n  foo (assert q) ; (x)\n");
        let want = [
            (3, 1, "(declare-const p Bool)"),
            (3, 24, ")"),
            (3, 26, "(assert L)"),
            (4, 3, "foo"),
            (4, 7, "(assert q)"),
        ];
        assert_eq!(got.len(), want.len(), "{got:?}");
        for ((line, column, text), (want_line, want_column, want_text)) in got.iter().zip(want) {
            assert_eq!(
                (*line, *column, text.as_str()),
                (want_line, want_column, want_text)
            );
        }
    }

    #[test]
    fn the_last_token_ends_before_trailing_trivia() {
        assert_eq!(end_of_last_token("(a b) ; c)\n  "), 5);
        assert_eq!(end_of_last_token("(echo \"x ; )\")  "), 14);
        assert_eq!(end_of_last_token("(f |a\\|) b|)\n"), 12);
        assert_eq!(end_of_last_token("  ; only\n"), 0);
    }
}
