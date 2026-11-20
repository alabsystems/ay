// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The fields the MIPLIB solution checker reads from a data line.
//!
//! ay reads an MPS data line as whitespace-separated fields (free format).
//! The checker (`MpsInput::readLine` of the organizers' `miplib2017-checker`)
//! first decides, line by line until it settles on free format, whether the
//! line is in the fixed-column layout; if so it joins the words of a name
//! field that contains blanks (`patchField`). It also ends a line at a `$`
//! comment and reads at most five fields. [`CheckerFields::read`] repeats that
//! decision and returns the checker's fields, so the reader can refuse a line
//! on which the two readings differ instead of answering about a model the
//! referee does not see.

/// Positions that must be blank for the checker to consider the fixed layout.
const FIXED_BLANKS: [usize; 12] = [12, 13, 22, 23, 36, 37, 38, 47, 48, 61, 62, 63];
/// The checker pads every line to this many columns.
const MIN_LINE_LEN: usize = 80;

/// The checker's line state: once it has decided a file is in free format it
/// never tests a later line for the fixed layout.
#[derive(Debug, Default)]
pub(super) struct CheckerFields {
    free_format: bool,
}

impl CheckerFields {
    /// Whether the checker has settled on free format: from then on its
    /// fields of a line without `$` are the line's blank-separated words (at
    /// most five), so [`Self::read`] has nothing to add.
    pub(super) fn settled(&self) -> bool {
        self.free_format
    }

    /// The checker's fields of data line `raw` (without its `\n`;
    /// `terminated` when one followed it). `data_section` is true in
    /// `COLUMNS`, `RHS`, `RANGES` and `BOUNDS`, where a line that is not in the
    /// fixed layout settles the file as free format.
    pub(super) fn read(
        &mut self,
        raw: &[u8],
        terminated: bool,
        data_section: bool,
    ) -> Vec<Vec<u8>> {
        // `strlen` of what `fgets` stored, the `\n` included.
        let len = raw.len() + usize::from(terminated);
        let mut buf: Vec<u8> = raw
            .iter()
            .map(|&b| if b == b'\t' || b == b'\r' { b' ' } else { b })
            .collect();
        if terminated {
            buf.push(b' ');
        }
        if buf.len() < MIN_LINE_LEN {
            buf.resize(MIN_LINE_LEN, b' ');
        }
        if !self.free_format {
            if buf[14] == b'$' && buf[13] == b' ' {
                buf.truncate(14);
                buf.resize(MIN_LINE_LEN, b' ');
            } else if buf[39] == b'$' && buf[38] == b' ' {
                buf.truncate(39);
                buf.resize(MIN_LINE_LEN, b' ');
            }
            if FIXED_BLANKS.iter().all(|&i| buf[i] == b' ') {
                let number = buf[24..=35].iter().any(u8::is_ascii_digit);
                if number || len < 13 {
                    patch(&mut buf, 4, 12);
                    patch(&mut buf, 14, 22);
                    patch(&mut buf, 39, 47);
                } else if data_section {
                    self.free_format = true;
                }
            } else {
                self.free_format = true;
            }
        }
        let mut fields = Vec::new();
        for (i, token) in buf[1..]
            .split(|&b| b == b' ')
            .filter(|t| !t.is_empty())
            .enumerate()
        {
            if i >= 5 || (i >= 1 && token.first() == Some(&b'$')) {
                break;
            }
            fields.push(token.to_vec());
        }
        fields
    }
}

/// The checker's `patchField`: inside `[beg, end]`, trimmed of blanks at both
/// ends, every blank becomes `_`.
fn patch(buf: &mut [u8], beg: usize, end: usize) {
    let mut lo = beg;
    let mut hi = end;
    while lo <= hi && buf[hi] == b' ' {
        if hi == 0 {
            return;
        }
        hi -= 1;
    }
    while lo <= hi && buf[lo] == b' ' {
        lo += 1;
    }
    for b in buf.iter_mut().take(hi + 1).skip(lo) {
        if *b == b' ' {
            *b = b'_';
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fields(lines: &[&str], data_section: bool) -> Vec<Vec<String>> {
        let mut reader = CheckerFields::default();
        lines
            .iter()
            .map(|line| {
                reader
                    .read(line.as_bytes(), true, data_section)
                    .into_iter()
                    .map(|f| String::from_utf8(f).expect("utf8"))
                    .collect()
            })
            .collect()
    }

    #[test]
    fn free_format_lines_read_as_whitespace_fields() {
        assert_eq!(
            fields(&["    X OBJ 1 C1 2"], true),
            vec![vec!["X", "OBJ", "1", "C1", "2"]]
        );
    }

    #[test]
    fn a_fixed_layout_name_with_a_blank_is_one_field_for_the_checker() {
        // Columns 4-12 hold "MY COL"; the checker reads one name, MY_COL.
        let line = "    MY COL    OBJ       1";
        assert_eq!(fields(&[line], true), vec![vec!["MY_COL", "OBJ", "1"]]);
    }

    #[test]
    fn a_dollar_field_ends_the_line_and_six_fields_are_five() {
        assert_eq!(
            fields(&["    X OBJ 1 $ comment", "    A B 1 C 2 D"], true),
            vec![vec!["X", "OBJ", "1"], vec!["A", "B", "1", "C", "2"]]
        );
    }
}
