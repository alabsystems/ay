// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SExpr drops quote status. Refuse quoted theory/grammar aliases BEFORE that
//! loss, rather than reinterpreting a named function as a builtin or binder.

use super::*;

pub(super) fn admit(text: &str, budget: &mut Budget) -> Option<()> {
    let bytes = text.as_bytes();
    let mut index = 0;
    while let Some(&byte) = bytes.get(index) {
        budget.charge(1, 0)?;
        index += 1;
        match byte {
            b';' => {
                while bytes
                    .get(index)
                    .is_some_and(|b| !matches!(b, b'\n' | b'\r'))
                {
                    index += 1;
                }
            }
            b'"' => loop {
                let byte = *bytes.get(index)?;
                index += 1;
                if byte == b'"' {
                    if bytes.get(index) == Some(&b'"') {
                        index += 1;
                    } else {
                        break;
                    }
                }
            },
            b'|' => {
                let start = index;
                while bytes.get(index).is_some_and(|b| *b != b'|') {
                    // Source symbol scope already excludes escaped bars and
                    // backslashes; do not introduce a second unescape policy.
                    if bytes[index] == b'\\' {
                        return None;
                    }
                    index += 1;
                }
                bytes.get(index)?;
                let name = text.get(start..index)?;
                // `_ bvN W` requires the unquoted indexed numeral spelling.
                // Do not promote a quoted function symbol into that literal.
                if name.strip_prefix("bv").is_some_and(|digits| {
                    !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
                }) {
                    return None;
                }
                budget.name(name)?;
                index += 1;
            }
            _ => {}
        }
    }
    Some(())
}
