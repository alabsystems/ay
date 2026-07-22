// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sort parsing for the CHC parser.
//!
//! Handles scalar sorts (Bool, Int, Real), indexed sorts (`(_ BitVec N)`),
//! parametric sorts (`(Array K V)`), and declared datatype sorts.

use super::ChcParser;
use crate::{ChcError, ChcResult, ChcSort};

/// Upper bound on a declared bitvector width.
///
/// The width sizes downstream bit-blasting, the wide-decimal-BV chunk loop
/// (`encode_wide_decimal_bv`), and `make_all_ones_bv`'s recursion (depth
/// ~width/128). An adversarial `(_ BitVec 4000000000)` would otherwise OOM or
/// overflow the stack. ~1M bits is far above any real bitvector.
pub(super) const MAX_BV_WIDTH: u32 = 1 << 20;

impl ChcParser {
    /// Parse a sort
    pub(super) fn parse_sort(&mut self) -> ChcResult<ChcSort> {
        self.skip_whitespace_and_comments();

        if self.peek_char() == Some('(') {
            // Compound sort: (_ BitVec 32) or (Array Int Int)
            self.expect_char('(')?;
            self.skip_whitespace_and_comments();

            // Check if it's indexed (_ ...) or parametric (Array ...)
            let first = self.parse_symbol()?;
            self.skip_whitespace_and_comments();

            match first.as_str() {
                "_" => {
                    // Indexed sort: (_ BitVec 32)
                    let sort_name = self.parse_symbol()?;
                    self.skip_whitespace_and_comments();

                    match sort_name.as_str() {
                        "BitVec" => {
                            let width: u32 = self
                                .parse_numeral()?
                                .parse()
                                .map_err(|_| ChcError::Parse("Invalid bitvector width".into()))?;
                            if width == 0 || width > MAX_BV_WIDTH {
                                return Err(ChcError::Parse(format!(
                                    "bitvector width {width} is outside the supported range 1..={MAX_BV_WIDTH}"
                                )));
                            }
                            self.skip_whitespace_and_comments();
                            self.expect_char(')')?;
                            Ok(ChcSort::BitVec(width))
                        }
                        _ => Err(ChcError::Parse(format!(
                            "Unknown indexed sort: {sort_name}"
                        ))),
                    }
                }
                "Array" => {
                    // Parametric sort: (Array key_sort value_sort)
                    let key_sort = self.parse_sort()?;
                    self.skip_whitespace_and_comments();
                    let value_sort = self.parse_sort()?;
                    self.skip_whitespace_and_comments();
                    self.expect_char(')')?;
                    Ok(ChcSort::Array(Box::new(key_sort), Box::new(value_sort)))
                }
                _ => Err(ChcError::Parse(format!("Unknown parametric sort: {first}"))),
            }
        } else {
            let name = self.parse_symbol()?;
            match name.as_str() {
                "Bool" => Ok(ChcSort::Bool),
                "Int" => Ok(ChcSort::Int),
                "Real" => Ok(ChcSort::Real),
                _ => {
                    // Check if it's a declared datatype sort (with metadata)
                    if let Some(dt_sort) = self.declared_datatype_sorts.get(&name) {
                        Ok(dt_sort.clone())
                    } else if self.declared_sorts.contains(&name) {
                        // Fallback for sorts registered without datatype metadata
                        Ok(ChcSort::Uninterpreted(name))
                    } else {
                        Err(ChcError::Parse(format!("Unknown sort: {name}")))
                    }
                }
            }
        }
    }
}
