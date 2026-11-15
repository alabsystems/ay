use crate::pbp_parser::utils::Position;
use colored::Colorize;
use std::fmt::Debug;
use std::io::BufRead;

/// A file/stream reader defining functions required by the VeriPB version 3 parser.
pub trait Reader: Debug {
    /// Peek at the next byte.
    fn peek(&mut self) -> Option<&u8>;
    /// Get the next byte.
    fn next(&mut self) -> Option<u8>;
    /// Get the total size of the underlying file.
    fn get_size(&self) -> Option<u64>;
    /// Get the current line.
    fn get_current_line(&self) -> &str;
    /// Print the current line.
    fn print_trace(&mut self, pos: &Position, do_print: bool);
}

/// VeriPB proof file reader from a streamed `BufRead`.
pub struct StreamReader<'a, R: BufRead> {
    reader: &'a mut R,
    len: Option<u64>,
    print_trace: bool,
    trace_pos: Position,
    trace_buffer: Vec<u8>,
    line_buffer: Vec<u8>,
}

impl<R: BufRead> std::fmt::Debug for StreamReader<'_, R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StreamReader")
            .field("len", &self.len)
            .field("print_trace", &self.print_trace)
            .field("trace_pos", &self.trace_pos)
            .field("trace_buffer", &self.trace_buffer)
            .field("line_buffer", &self.line_buffer)
            .finish_non_exhaustive() // There's no Debug for dyn BufRead :(
    }
}

impl<'a, R: BufRead> StreamReader<'a, R> {
    /// Construct a new [`StreamReader`].
    pub fn new(file_size: Option<u64>, reader: &'a mut R, print_trace: bool) -> Self {
        Self {
            reader,
            len: file_size,
            print_trace,
            trace_pos: Position {
                pos: 0,
                col: 1,
                line: 1,
            },
            trace_buffer: Vec::with_capacity(if print_trace { 16 * 1024 } else { 0 }),
            line_buffer: Vec::new(),
        }
    }
}

impl<R: BufRead> Reader for StreamReader<'_, R> {
    fn peek(&mut self) -> Option<&u8> {
        match self.reader.fill_buf() {
            Ok(buffer) => buffer.first(),
            _ => None,
        }
    }

    fn next(&mut self) -> Option<u8> {
        let c = match self.reader.fill_buf() {
            Ok(buffer) => buffer.first().copied(),
            _ => return None,
        };
        self.reader.consume(1);
        let c = c?;
        if self.print_trace {
            self.trace_buffer.push(c);
        };
        self.line_buffer.push(c);
        if c == b'\n' || c == b'\r' {
            self.line_buffer.clear();
        }
        Some(c)
    }

    fn get_size(&self) -> Option<u64> {
        self.len
    }

    /// The bytes are whatever the proof file holds on the current line, so the conversion is
    /// checked. A line that is not UTF-8 yields `""`, and the one caller
    /// ([`Lexer::report_error`](crate::pbp_parser::lexer)) already renders that as "no source
    /// line": the diagnosis, position and offending byte are in the message either way. This used
    /// to be `from_utf8_unchecked`, which produced a `&str` that is not UTF-8 — undefined
    /// behaviour — on every parse error reported on a line holding a non-UTF-8 byte, and
    /// `report_error` then ran `str::replace` and `Display` over it. See
    /// `tests/proof_bytes_are_utf8.rs`.
    ///
    /// Returning the valid prefix instead of `""` would be friendlier, but it hands
    /// [`ParserError::pbp_error`](crate::error::ParserError::pbp_error) a line shorter than the
    /// token it underlines, and its caret padding subtracts the token length from the line length.
    fn get_current_line(&self) -> &str {
        std::str::from_utf8(&self.line_buffer).unwrap_or("")
    }

    fn print_trace(&mut self, pos: &Position, do_print: bool) {
        if do_print {
            // Lossy, not checked: this is the `--trace` display of bytes the parser has already
            // accepted, so refusing to print them would turn a diagnostic aid into a failure.
            // `from_utf8_lossy` borrows when the buffer is valid, which is every real proof, so
            // the common path still does not copy. It was `from_utf8_unchecked`, which made an
            // invalid `&str` out of any traced line holding a non-UTF-8 byte and then called
            // `lines()` and `trim_ascii()` on it. That is reachable on the *accepting* path:
            // `Lexer::skip_to_semicolon` swallows the free text of an `a` rule without looking at
            // it, but every byte it consumes still lands in this buffer, and the run goes on to
            // print a verdict. See `tests/proof_bytes_are_utf8.rs`.
            let chunk = String::from_utf8_lossy(&self.trace_buffer);
            for (line_number, line) in (self.trace_pos.line..).zip(chunk.lines()) {
                let line = line.trim_ascii();
                if !line.is_empty() {
                    println!(
                        "{}",
                        format!("line {line_number:>4}: {line}").bright_black()
                    );
                };
            }
        }
        self.trace_buffer.clear();
        self.trace_pos = pos.clone();
    }
}
