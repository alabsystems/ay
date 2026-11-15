// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lossless wire-text ownership. No term identity or normalization is interned.
use std::borrow::Borrow;
use std::cell::{Cell, RefCell};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

use super::super::surface_tokens::next_smt_term_slice;

const RC_HEADER: usize = 2 * std::mem::size_of::<usize>();
pub(crate) const COUNTER_BYTES: usize =
    RC_HEADER + std::mem::size_of::<ChargeState>() + std::mem::align_of::<ChargeState>() - 1;

pub(crate) struct ChargeState {
    bytes: Cell<usize>,
    poisoned: Cell<bool>,
    parent: Option<Rc<ChargeState>>,
}
impl ChargeState {
    pub(crate) fn root() -> Self {
        Self {
            bytes: Cell::new(COUNTER_BYTES),
            poisoned: Cell::new(false),
            parent: None,
        }
    }
    fn child(parent: Rc<Self>) -> Self {
        Self {
            bytes: Cell::new(COUNTER_BYTES),
            poisoned: Cell::new(false),
            parent: Some(parent),
        }
    }
    pub(crate) fn get(&self) -> usize {
        self.bytes.get()
    }
    pub(crate) fn set(&self, bytes: usize) {
        self.bytes.set(bytes);
    }
    pub(crate) fn poison(&self) {
        self.poisoned.set(true);
        if let Some(parent) = &self.parent {
            parent.poison();
        }
    }
    pub(crate) fn is_poisoned(&self) -> bool {
        self.poisoned.get() || self.parent.as_ref().is_some_and(|p| p.is_poisoned())
    }
    pub(crate) fn subtract(&self, bytes: usize) -> bool {
        match self.get().checked_sub(bytes) {
            Some(left) => {
                self.set(left);
                true
            }
            None => {
                self.poison();
                false
            }
        }
    }
}

#[derive(Clone)]
pub(crate) struct TextBudget {
    pub(crate) used: Rc<ChargeState>,
    pub(crate) limit: usize,
}
impl TextBudget {
    pub(crate) fn new(limit: usize) -> Self {
        Self {
            used: Rc::new(ChargeState::root()),
            limit,
        }
    }
    pub(crate) fn with_parent(limit: usize, parent: &Rc<ChargeState>) -> Self {
        Self {
            used: Rc::new(ChargeState::child(Rc::clone(parent))),
            limit,
        }
    }
    pub(crate) fn retained(used: Rc<ChargeState>, limit: usize) -> Self {
        Self { used, limit }
    }
    pub(crate) fn reserve(&self, bytes: usize) -> Option<Reservation> {
        if self.used.is_poisoned() {
            return None;
        }
        let Some(total) = self.used.get().checked_add(bytes) else {
            self.used.poison();
            return None;
        };
        if total > self.limit {
            return None;
        }
        self.used.set(total);
        Some(Reservation {
            used: Rc::clone(&self.used),
            bytes,
        })
    }
    pub(crate) fn copy(&self, text: &str) -> Option<OwnedText> {
        let lease = self.reserve(OwnedText::cost(text.len())?)?;
        Some(OwnedText::from_reserved(text, lease))
    }
    pub(crate) fn vector<T>(&self, count: usize) -> Option<ScratchVec<T>> {
        let mut lease = self.reserve(count.checked_mul(std::mem::size_of::<T>())?)?;
        let data = Vec::with_capacity(count);
        // Vec's requested capacity is exact for these non-ZST callers. Still
        // account the actual capacity before exposing the allocation.
        let actual = data.capacity().checked_mul(std::mem::size_of::<T>())?;
        lease.resize(actual, self.limit)?;
        Some(ScratchVec {
            data,
            _lease: lease,
        })
    }
}

pub(crate) struct Reservation {
    used: Rc<ChargeState>,
    bytes: usize,
}
impl Reservation {
    pub(crate) fn resize(&mut self, bytes: usize, limit: usize) -> Option<()> {
        if self.used.is_poisoned() {
            return None;
        }
        if bytes > self.bytes {
            let Some(total) = self.used.get().checked_add(bytes - self.bytes) else {
                self.used.poison();
                return None;
            };
            if total > limit {
                return None;
            }
            self.used.set(total);
        } else if !self.used.subtract(self.bytes - bytes) {
            return None;
        }
        self.bytes = bytes;
        Some(())
    }
    pub(crate) fn precharged(used: Rc<ChargeState>, bytes: usize) -> Self {
        Self { used, bytes }
    }
}
impl Drop for Reservation {
    fn drop(&mut self) {
        self.used.subtract(self.bytes);
    }
}

struct TextAllocation {
    text: Box<str>,
    _lease: Reservation,
}
#[derive(Clone)]
pub(crate) struct OwnedText(Rc<TextAllocation>);
impl OwnedText {
    pub(crate) fn cost(len: usize) -> Option<usize> {
        len.checked_add(
            RC_HEADER
                + std::mem::size_of::<TextAllocation>()
                + std::mem::align_of::<TextAllocation>()
                - 1,
        )
    }
    fn from_reserved(text: &str, lease: Reservation) -> Self {
        Self(Rc::new(TextAllocation {
            text: Box::from(text),
            _lease: lease,
        }))
    }
    pub(crate) fn precharged(text: &str, used: Rc<ChargeState>) -> Self {
        let cost = Self::cost(text.len()).unwrap_or(usize::MAX);
        Self::from_reserved(text, Reservation::precharged(used, cost))
    }
    pub(crate) fn join(budget: &TextBudget, parts: &[&str], len: usize) -> Option<Self> {
        if parts
            .iter()
            .try_fold(0usize, |n, part| n.checked_add(part.len()))?
            != len
        {
            return None;
        }
        let lease = budget.reserve(Self::cost(len)?)?;
        let mut text = String::with_capacity(len);
        for part in parts {
            text.push_str(part);
        }
        if text.len() != len || text.capacity() != len {
            return None;
        }
        Some(Self(Rc::new(TextAllocation {
            text: text.into_boxed_str(),
            _lease: lease,
        })))
    }
    pub(crate) fn wrapped(&self, shells: usize, budget: &TextBudget) -> Option<Self> {
        if shells == 0 {
            return Some(self.clone());
        }
        let len = shells.checked_mul(6)?.checked_add(self.len())?;
        let lease = budget.reserve(Self::cost(len)?)?;
        let mut text = String::with_capacity(len);
        for _ in 0..shells {
            text.push_str("(not ");
        }
        text.push_str(self);
        for _ in 0..shells {
            text.push(')');
        }
        if text.capacity() != len {
            return None;
        }
        Some(Self(Rc::new(TextAllocation {
            text: text.into_boxed_str(),
            _lease: lease,
        })))
    }
    pub(crate) fn allocation_bytes(&self) -> usize {
        Self::cost(self.len()).unwrap_or(usize::MAX)
    }
    /// Physical allocation equality is used only to avoid charging the same
    /// owned allocation twice, never to establish a replay judgement.
    pub(crate) fn shares_allocation(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Deref for OwnedText {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0.text
    }
}
impl AsRef<str> for OwnedText {
    fn as_ref(&self) -> &str {
        self
    }
}
impl Borrow<str> for OwnedText {
    fn borrow(&self) -> &str {
        self
    }
}
impl PartialEq for OwnedText {
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}
impl Eq for OwnedText {}
impl Hash for OwnedText {
    fn hash<H: Hasher>(&self, state: &mut H) {
        str::hash(self, state);
    }
}
impl fmt::Debug for OwnedText {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_ref(), f)
    }
}
impl fmt::Display for OwnedText {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self)
    }
}

pub(crate) struct ScratchVec<T> {
    data: Vec<T>,
    _lease: Reservation,
}
impl<T> Deref for ScratchVec<T> {
    type Target = Vec<T>;
    fn deref(&self) -> &Vec<T> {
        &self.data
    }
}
impl<T> DerefMut for ScratchVec<T> {
    fn deref_mut(&mut self) -> &mut Vec<T> {
        &mut self.data
    }
}

pub(crate) struct ScratchScope<'a> {
    slot: &'a RefCell<Option<TextBudget>>,
    installed: bool,
}
impl<'a> ScratchScope<'a> {
    pub(crate) fn enter(
        slot: &'a RefCell<Option<TextBudget>>,
        limit: usize,
        parent: &Rc<ChargeState>,
    ) -> Self {
        let mut active = slot.borrow_mut();
        let installed = active.is_none();
        if installed {
            *active = Some(TextBudget::with_parent(limit, parent));
        }
        Self { slot, installed }
    }
}
impl Drop for ScratchScope<'_> {
    fn drop(&mut self) {
        if self.installed {
            self.slot.borrow_mut().take();
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) struct WireParts<'a> {
    pub(crate) body: &'a str,
    pub(crate) shells: usize,
}
impl<'a> WireParts<'a> {
    pub(crate) fn read(text: &'a str) -> Self {
        let mut body = text;
        let mut shells = 0;
        while shells < super::MAX_NORMALISED_DEPTH {
            let Some(arg) = body.strip_prefix("(not ").and_then(|s| s.strip_suffix(')')) else {
                break;
            };
            if arg.is_empty()
                || (arg.starts_with('(')
                    && arg.ends_with(')')
                    && arg[1..arg.len() - 1].trim().is_empty())
            {
                break;
            }
            let mut cursor = 0;
            let Ok(Some(complete)) = next_smt_term_slice(arg, &mut cursor) else {
                break;
            };
            // Exact bytes/arity, including the space after `not`. Unusual
            // whitespace or opaque/malformed syntax keeps its original body.
            if complete.as_ptr() != arg.as_ptr()
                || complete.len() != arg.len()
                || !matches!(next_smt_term_slice(arg, &mut cursor), Ok(None))
            {
                break;
            }
            body = arg;
            shells += 1;
        }
        Self { body, shells }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct WireLiteral {
    pub(crate) body: OwnedText,
    pub(crate) shells: usize,
}
impl WireLiteral {
    pub(crate) fn len(&self) -> Option<usize> {
        self.shells.checked_mul(6)?.checked_add(self.body.len())
    }
    pub(crate) fn materialize(&self, budget: &TextBudget) -> Option<OwnedText> {
        self.body.wrapped(self.shells, budget)
    }
}

/// Borrow the same complete `not` argument the existing decoder reads.
pub(crate) fn decoded_body(mut text: &str) -> Option<(&str, usize)> {
    text = text.trim();
    let mut depth = 0usize;
    loop {
        let Some(inner) = text.strip_prefix('(').and_then(|s| s.strip_suffix(')')) else {
            break;
        };
        let mut cursor = 0;
        let Ok(Some("not")) = next_smt_term_slice(inner, &mut cursor) else {
            break;
        };
        let Ok(Some(arg)) = next_smt_term_slice(inner, &mut cursor) else {
            break;
        };
        if !matches!(next_smt_term_slice(inner, &mut cursor), Ok(None)) {
            break;
        }
        text = arg.trim();
        depth = depth.checked_add(1)?;
    }
    Some((text, depth))
}

impl OwnedText {
    fn list(budget: &TextBudget, parts: &[OwnedText]) -> Option<Self> {
        let mut len = 2usize.checked_add(parts.len().saturating_sub(1))?;
        for part in parts {
            len = len.checked_add(part.len())?;
        }
        let lease = budget.reserve(Self::cost(len)?)?;
        let mut text = String::with_capacity(len);
        text.push('(');
        for (i, part) in parts.iter().enumerate() {
            if i != 0 {
                text.push(' ');
            }
            text.push_str(part);
        }
        text.push(')');
        if text.capacity() != len {
            return None;
        }
        Some(Self(Rc::new(TextAllocation {
            text: text.into_boxed_str(),
            _lease: lease,
        })))
    }
}

/// Same normalization and cutoffs as the legacy reader, with borrowed input
/// slices and an owner for every simultaneously live vector/text allocation.
pub(crate) fn normalise_owned(
    text: &str,
    depth: usize,
    nodes: &mut usize,
    budget: &TextBudget,
) -> Option<OwnedText> {
    let text = text.trim();
    if depth > super::MAX_NORMALISED_DEPTH || *nodes >= super::MAX_NORMALISED_NODES {
        return budget.copy(text);
    }
    *nodes += 1;
    // A pinned num-bigint conversion retains input digits, limb/quotient
    // buffers, radix digits and the formatter's String together. Keep a
    // conservative reserve around that foreign conversion; our owned result
    // and every slice/vector capacity are charged separately. Non-literals
    // never need this reserve or the conversion.
    let numeric = text.starts_with("#b")
        || text.starts_with("#x")
        || text
            .strip_prefix('(')
            .and_then(|s| s.strip_suffix(')'))
            .is_some_and(|s| s.split_whitespace().next() == Some("_"));
    if numeric {
        let _numeric_lease = budget.reserve(text.len().checked_mul(16)?.checked_add(4096)?)?;
        if let Some((value, width)) = super::super::parse_printed_bitvec_literal(text) {
            let rendered = format!("#bv{value}:{width}");
            return budget.copy(&rendered);
        }
    }
    let Some(inner) = text.strip_prefix('(').and_then(|s| s.strip_suffix(')')) else {
        return budget.copy(text);
    };
    let mut cursor = 0;
    let mut count = 0usize;
    loop {
        match next_smt_term_slice(inner, &mut cursor) {
            Ok(Some(_)) => count = count.checked_add(1)?,
            Ok(None) => break,
            Err(_) => return budget.copy(text),
        }
    }
    let mut parts = budget.vector::<OwnedText>(count)?;
    cursor = 0;
    loop {
        match next_smt_term_slice(inner, &mut cursor) {
            Ok(Some(part)) => parts.push(normalise_owned(part, depth + 1, nodes, budget)?),
            Ok(None) => break,
            Err(_) => return None,
        }
    }
    OwnedText::list(budget, &parts)
}

pub(crate) struct Tracked<T> {
    data: T,
    _lease: Reservation,
}
impl<T> Tracked<T> {
    pub(crate) fn reserved(data: T, lease: Reservation) -> Self {
        Self {
            data,
            _lease: lease,
        }
    }
}
impl<T> Deref for Tracked<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.data
    }
}
impl<T> AsRef<[T]> for Tracked<Vec<T>> {
    fn as_ref(&self) -> &[T] {
        &self.data
    }
}
impl<T> AsRef<[T]> for ScratchVec<T> {
    fn as_ref(&self) -> &[T] {
        &self.data
    }
}

pub(crate) fn matrix_bytes<T>(data: &Vec<Vec<T>>) -> Option<usize> {
    data.iter().try_fold(
        data.capacity().checked_mul(std::mem::size_of::<Vec<T>>())?,
        |n, row| n.checked_add(row.capacity().checked_mul(std::mem::size_of::<T>())?),
    )
}

impl TextBudget {
    pub(crate) fn concat(&self, parts: &[&str]) -> Option<OwnedText> {
        let len = parts
            .iter()
            .try_fold(0usize, |n, p| n.checked_add(p.len()))?;
        OwnedText::join(self, parts, len)
    }
}

impl Tracked<Vec<Vec<super::PrintedLiteral>>> {
    pub(crate) fn copy_replay(
        source: &[Vec<super::PrintedLiteral>],
        extra: usize,
        budget: &TextBudget,
    ) -> Option<Self> {
        let outer = source.len().checked_add(extra)?;
        let fields = source
            .iter()
            .try_fold(extra.checked_mul(3)?, |n, row| n.checked_add(row.len()))?;
        let lease = budget.reserve(
            outer
                .checked_mul(std::mem::size_of::<Vec<super::PrintedLiteral>>())?
                .checked_add(fields.checked_mul(std::mem::size_of::<super::PrintedLiteral>())?)?,
        )?;
        let mut data = Vec::with_capacity(outer);
        for row in source {
            data.push(row.clone());
        }
        Some(Self::reserved(data, lease))
    }
    pub(crate) fn push_replay(&mut self, row: Vec<super::PrintedLiteral>) -> Option<()> {
        if self.data.len() == self.data.capacity() || row.capacity() > 3 {
            return None;
        }
        self.data.push(row);
        Some(())
    }
    pub(crate) fn seal_replay(&mut self, budget: &TextBudget) -> Option<()> {
        self._lease.resize(matrix_bytes(&self.data)?, budget.limit)
    }
}

pub(crate) fn binary_application<'a>(text: &'a str, head: &str) -> Option<(&'a str, &'a str)> {
    let inner = text.strip_prefix('(')?.strip_suffix(')')?;
    let mut cursor = 0;
    if next_smt_term_slice(inner, &mut cursor).ok()?? != head {
        return None;
    }
    let left = next_smt_term_slice(inner, &mut cursor).ok()??;
    let right = next_smt_term_slice(inner, &mut cursor).ok()??;
    if next_smt_term_slice(inner, &mut cursor).ok()?.is_some() {
        return None;
    }
    Some((left, right))
}
