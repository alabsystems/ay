// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A streaming reader of a rendered Alethe document: how many unproved
//! (`hole`/`trust`) steps it carries and the premise `assume` leaves it
//! states, keeping no other text.
//!
//! One reader for every consumer that judges a document by what an external
//! checker receives: the CLI's `--strict-proofs` admission and certificate
//! disclosure, and the executor's own publication gates (the QSAT route
//! publishes an `unsat` only with a document this reader finds complete and
//! assumed verbatim from the problem).

/// Bytes of `assume` text a scan keeps before it declares the document
/// unjudgeable. The whole document is streamed; only the leaves are retained.
const MAX_SCANNED_ASSUME_BYTES: usize = 64 * 1024 * 1024;

/// What a rendered Alethe document carries, read in one streaming pass.
#[derive(Default)]
pub struct AletheDocumentScan {
    /// `:rule hole` / `:rule trust` steps anywhere in the document.
    pub unproved: u32,
    /// Top-level (premise) `assume` terms, in order. `assume`s inside an
    /// `anchor` subproof are local hypotheses and are not premises.
    pub premise_assumes: Vec<String>,
    /// The retained `assume` text passed [`MAX_SCANNED_ASSUME_BYTES`].
    pub overflowed: bool,
    // Lexer state.
    depth: usize,
    in_string: bool,
    in_quoted_symbol: bool,
    token: String,
    /// Tokens of the current top-level command seen at depth 1, up to three.
    head: Vec<String>,
    previous_token_was_rule: bool,
    /// Bytes of the current top-level command, kept only for `assume`.
    capture: Option<Vec<u8>>,
    retained_bytes: usize,
    /// Open `anchor` subproofs, by the step id that closes them.
    anchors: Vec<String>,
}

impl AletheDocumentScan {
    fn finish_token(&mut self) {
        if self.token.is_empty() {
            return;
        }
        let token = std::mem::take(&mut self.token);
        if self.previous_token_was_rule {
            if token == "hole" || token == "trust" {
                self.unproved = self.unproved.saturating_add(1);
            }
            self.previous_token_was_rule = false;
        } else if token == ":rule" {
            self.previous_token_was_rule = true;
        }
        if self.depth == 1 && self.head.len() < 3 {
            if self.head.is_empty() && token == "assume" && self.anchors.is_empty() {
                self.capture = Some(b"(assume ".to_vec());
            }
            self.head.push(token);
        }
    }

    fn finish_command(&mut self) {
        let head = std::mem::take(&mut self.head);
        match head.first().map(String::as_str) {
            Some("anchor") => {
                // `(anchor :step ID ...)`: the subproof closes at `(step ID ...)`.
                if head.get(1).map(String::as_str) == Some(":step") {
                    if let Some(id) = head.get(2) {
                        self.anchors.push(id.clone());
                    }
                }
            }
            Some("step") => {
                if head
                    .get(1)
                    .is_some_and(|id| self.anchors.last() == Some(id))
                {
                    self.anchors.pop();
                }
            }
            _ => {}
        }
        if let Some(bytes) = self.capture.take() {
            // `(assume ID TERM)`: drop the head, the id and the closing paren.
            let text = String::from_utf8_lossy(&bytes);
            let body = text
                .strip_prefix("(assume")
                .map(str::trim_start)
                .and_then(|rest| rest.split_once(char::is_whitespace))
                .map(|(_id, term)| term.trim())
                .and_then(|term| term.strip_suffix(')'))
                .map(str::trim);
            match body {
                Some(term) => self.premise_assumes.push(term.to_string()),
                None => self.overflowed = true,
            }
        }
    }

    fn push_byte(&mut self, byte: u8) {
        if let Some(capture) = self.capture.as_mut() {
            if self.retained_bytes >= MAX_SCANNED_ASSUME_BYTES {
                self.overflowed = true;
                self.capture = None;
            } else {
                capture.push(byte);
                self.retained_bytes += 1;
            }
        }
        // Every delimiter the lexer acts on is ASCII; a non-ASCII byte can only
        // sit inside a token, a string literal or a quoted symbol, where it is
        // opaque. The token text is compared only against ASCII rule names.
        let c = char::from(byte);
        if self.in_string {
            if c == '"' {
                self.in_string = false;
            }
            self.token.push(c);
            return;
        }
        if self.in_quoted_symbol {
            if c == '|' {
                self.in_quoted_symbol = false;
            }
            self.token.push(c);
            return;
        }
        match c {
            '"' => {
                self.in_string = true;
                self.token.push(c);
            }
            '|' => {
                self.in_quoted_symbol = true;
                self.token.push(c);
            }
            '(' => {
                self.finish_token();
                self.depth += 1;
            }
            ')' => {
                self.finish_token();
                self.depth = self.depth.saturating_sub(1);
                if self.depth == 0 {
                    self.finish_command();
                }
            }
            c if c.is_ascii_whitespace() => self.finish_token(),
            _ => self.token.push(c),
        }
    }

    /// Scan the certificate already written at `path`.
    #[must_use]
    pub fn of_file(path: &str) -> Option<Self> {
        let mut scan = Self::default();
        let mut file = std::fs::File::open(path).ok()?;
        std::io::copy(&mut file, &mut scan).ok()?;
        Some(scan)
    }
}

impl std::io::Write for AletheDocumentScan {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        for &byte in buf {
            self.push_byte(byte);
        }
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
