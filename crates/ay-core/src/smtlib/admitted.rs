// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A byte sink for the existing native surface formatters. It borrows one
//! original owner and prices every copied byte and actual capacity replacement.
//! It supplies no allowance/source authority and does not meter allocations
//! hidden inside arbitrary Display implementations: those need leaf preflight.

use crate::original_query::{CountedAdmissionError, OriginalAdmissionError, QueryError};
use crate::term::{reserve_counted, reserve_string_counted, TermConstructionAdmission};
use std::fmt::{self, Write};

/// Optional borrowed admission owner for native surface construction.
pub type Owner<'a> = Option<&'a dyn TermConstructionAdmission>;

/// Charge the borrowed owner, or accept when no owner was supplied.
pub fn pay(owner: Owner<'_>, work: usize, bytes: usize) -> bool {
    owner.is_none_or(|owner| owner.admit(work, bytes).is_ok())
}

/// Retain a native surface-formatting refusal in the supplied owner.
pub fn invalid(owner: Owner<'_>) {
    if let Some(owner) = owner {
        owner.refuse(CountedAdmissionError::Original(
            OriginalAdmissionError::Query(QueryError::Invalid("native surface formatting refused")),
        ));
    }
}

/// Reserve vector growth through the supplied owner's counted allocator.
pub fn reserve<T>(values: &mut Vec<T>, additional: usize, owner: Owner<'_>) -> bool {
    if let Some(owner) = owner {
        reserve_counted(values, additional, owner).is_ok()
    } else {
        values.reserve(additional);
        true
    }
}

/// Native string sink that charges growth and writes to one borrowed owner.
pub struct Buffer<'a> {
    value: String,
    owner: Owner<'a>,
}

impl<'a> Buffer<'a> {
    /// Create an empty sink without issuing an additional allowance.
    pub fn new(owner: Owner<'a>) -> Self {
        Self {
            value: String::new(),
            owner,
        }
    }
    /// Request initial capacity, retaining any refusal in the supplied owner.
    pub fn with_capacity(owner: Owner<'a>, hint: usize) -> Self {
        if let Some(original) = owner {
            let mut value = String::new();
            let _ = reserve_string_counted(&mut value, hint, original);
            Self { value, owner }
        } else {
            Self {
                value: String::with_capacity(hint),
                owner,
            }
        }
    }
    /// Append admitted text and report whether the write succeeded.
    pub fn push(&mut self, value: &str) -> bool {
        self.write_str(value).is_ok()
    }
    /// Append one admitted character and report whether the write succeeded.
    pub fn character(&mut self, value: char) -> bool {
        self.write_char(value).is_ok()
    }
    /// Prepay and append a repeated character under the same owner.
    pub fn repeat(&mut self, value: char, count: usize) -> bool {
        let Some(bytes) = count.checked_mul(value.len_utf8()) else {
            invalid(self.owner);
            return false;
        };
        if !pay(self.owner, bytes, 0) {
            return false;
        }
        if let Some(owner) = self.owner {
            if reserve_string_counted(&mut self.value, bytes, owner).is_err() {
                return false;
            }
        }
        self.value.extend(std::iter::repeat_n(value, count));
        true
    }
    /// Write native formatting arguments and retain any formatting refusal.
    pub fn format(&mut self, arguments: fmt::Arguments<'_>) -> bool {
        if fmt::write(self, arguments).is_err() {
            invalid(self.owner);
            false
        } else {
            true
        }
    }
    /// Return accumulated bytes; the caller retains the owner's refusal state.
    pub fn finish(self) -> String {
        self.value
    }
}

impl Write for Buffer<'_> {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        if !pay(self.owner, value.len(), 0) {
            return Err(fmt::Error);
        }
        if let Some(owner) = self.owner {
            reserve_string_counted(&mut self.value, value.len(), owner).map_err(|_| fmt::Error)?;
        }
        self.value.push_str(value);
        Ok(())
    }
}

/// Format native arguments, returning empty text if the owned write refuses.
pub fn format(owner: Owner<'_>, arguments: fmt::Arguments<'_>) -> String {
    if owner.is_none() {
        return fmt::format(arguments);
    }
    let mut buffer = Buffer::new(owner);
    if !buffer.format(arguments) {
        return String::new();
    }
    buffer.finish()
}

/// Copy text through the same admitted native formatting sink.
pub fn text(owner: Owner<'_>, value: &str) -> String {
    format(owner, format_args!("{value}"))
}

/// Quote a native SMT-LIB symbol under the supplied owner.
pub fn quote(owner: Owner<'_>, value: &str) -> String {
    super::quote_symbol_owned(value, owner)
}

/// Escape and delimit a native SMT-LIB string under the supplied owner.
pub fn string_literal(owner: Owner<'_>, value: &str) -> String {
    let escaped = super::escape_string_contents_owned(value, owner);
    format(owner, format_args!("\"{escaped}\""))
}

/// Join existing strings while charging each copied byte to the same owner.
pub fn join(owner: Owner<'_>, values: &[String], separator: &str) -> String {
    if owner.is_none() {
        return values.join(separator);
    }
    let mut result = Buffer::new(owner);
    for (index, value) in values.iter().enumerate() {
        if index != 0 && !result.push(separator) {
            return String::new();
        }
        if !result.push(value) {
            return String::new();
        }
    }
    result.finish()
}

/// Use the established native stacker's 32KiB red zone / 1MiB segments. Only
/// actual growth is prepaid; rounded stack pages plus both guards match
/// stacker 0.1's mmap backend. Cumulative payment lasts through the whole call.
pub fn stacked<R>(
    owner: Owner<'_>,
    refused: impl FnOnce() -> R,
    operation: impl FnOnce() -> R,
) -> R {
    let Some(owner) = owner else {
        return operation();
    };
    if owner.check().is_err() {
        return refused();
    }
    const RED: usize = 32 * 1024;
    const SEGMENT: usize = 1024 * 1024;
    if stacker::remaining_stack().is_none_or(|remaining| remaining < RED) {
        let bytes = ay_sys::allocation_page_size().and_then(|page| {
            SEGMENT
                .checked_add(page - 1)?
                .checked_div(page)?
                .checked_add(2)?
                .checked_mul(page)
        });
        let Some(bytes) = bytes else {
            owner.refuse(CountedAdmissionError::MemoryCapture);
            return refused();
        };
        if owner.admit(1, bytes).is_err() {
            return refused();
        }
    }
    stacker::maybe_grow(RED, SEGMENT, operation)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use std::sync::Arc;
    fn original(bytes: usize) -> CountedAdmission {
        CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000, bytes),
            None,
            Arc::new(|| false),
        )
        .unwrap()
    }

    #[test]
    fn admitted_native_strings_round_trip_and_share_cumulative_refusal() {
        let owner = original(1 << 20);
        for value in ["plain", "\"quoted\"", "\\u{61}", "\u{1f600}", "\0"] {
            let escaped = super::super::escape_string_contents_owned(value, Some(&owner));
            assert_eq!(super::super::unescape_string_contents(&escaped), value);
            assert_eq!(
                quote(Some(&owner), value),
                super::super::quote_symbol(value)
            );
        }
        owner.check().unwrap();
        let tiny = original(9);
        let _ = text(Some(&tiny), "abcde");
        let _ = text(Some(&tiny), "abcde");
        assert!(tiny.check().is_err());
        assert_eq!(text(Some(&tiny), "a"), "");
    }
}
