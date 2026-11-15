// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact equality for regular languages, independent of the solver.
//!
//! [`ModelValue`](crate::ModelValue) has no RegLan carrier, so a RegLan
//! equality over regex terms is decided from the terms themselves once
//! every string leaf is evaluated against the model, by the standard
//! Brzozowski derivative product over derivative-behaviour alphabet
//! classes. Every bound here fails closed.

use ay_core::kani_compat::DetHashMap;
use ay_core::term::{reserve_counted, reserve_map_counted, TermConstructionAdmission};
use ay_core::{
    smtlib_code_point, Sort, Symbol, TermData, TermId, TermStore, SMTLIB_MAX_CODE_POINT,
};

use crate::eval::error::{EvalError, EvalResource, EvalResult};
use crate::MAX_EVAL_DEPTH;
use std::cmp::Ordering;
use std::hash::{BuildHasher, Hasher};

/// Fail-closed bounds for one decision.
const EQUIV_WORK: u64 = 4_000_000;
const MAX_LANG_SIZE: usize = 8_192;
const MAX_PAIRS: usize = 8_192;
const MAX_CRITICAL: usize = 512;
const MAX_REGEX_DEPTH: usize = 256;

struct Work<'a> {
    remaining: u64,
    owner: &'a dyn TermConstructionAdmission,
}

impl Work<'_> {
    fn charge(&mut self, amount: usize) -> EvalResult<()> {
        self.owner.admit(amount, 0).map_err(stopped)?;
        let amount = u64::try_from(amount).map_err(|_| work_err())?;
        if amount > self.remaining {
            return Err(work_err());
        }
        self.remaining -= amount;
        Ok(())
    }
}

fn stopped(error: impl std::fmt::Display) -> EvalError {
    EvalError::Refused(error.to_string())
}

fn work_err() -> EvalError {
    EvalError::resource(EvalResource::Work, "regex equality work budget exhausted")
}

fn depth_err() -> EvalError {
    EvalError::resource(EvalResource::Depth, "regex term nested too deeply")
}

/// A regular language; `Lit` carries SMT-LIB code points, not Rust scalars.
#[derive(Debug)]
#[cfg_attr(test, derive(Eq, Ord, PartialEq, PartialOrd))]
enum Lang {
    Empty,
    Eps,
    Lit(Vec<u32>),
    AnyChar,
    All,
    Range(u32, u32),
    Concat(Vec<Lang>),
    Union(Vec<Lang>),
    Inter(Vec<Lang>),
    Star(Box<Lang>),
    Comp(Box<Lang>),
    Loop(Box<Lang>, u32, u32),
}

impl Lang {
    fn literal(code_points: Vec<u32>) -> Self {
        if code_points.is_empty() {
            Self::Eps
        } else {
            Self::Lit(code_points)
        }
    }

    fn concat(parts: impl IntoIterator<Item = Self>, work: &mut Work<'_>) -> EvalResult<Self> {
        let mut flat = Vec::new();
        for part in parts {
            work.charge(1)?;
            match part {
                Self::Empty => return Ok(Self::Empty),
                Self::Eps => {}
                Self::Concat(inner) => {
                    reserve_counted(&mut flat, inner.len(), work.owner).map_err(stopped)?;
                    work.charge(inner.len())?;
                    flat.extend(inner);
                }
                other => {
                    reserve_counted(&mut flat, 1, work.owner).map_err(stopped)?;
                    flat.push(other);
                }
            }
        }
        Ok(match flat.len() {
            0 => Self::Eps,
            1 => flat.pop().unwrap_or(Self::Eps),
            _ => Self::Concat(flat),
        })
    }

    fn union(parts: impl IntoIterator<Item = Self>, work: &mut Work<'_>) -> EvalResult<Self> {
        let mut flat = Vec::new();
        for part in parts {
            work.charge(1)?;
            match part {
                Self::Empty => {}
                Self::All => return Ok(Self::All),
                Self::Union(inner) => {
                    reserve_counted(&mut flat, inner.len(), work.owner).map_err(stopped)?;
                    work.charge(inner.len())?;
                    flat.extend(inner);
                }
                other => {
                    reserve_counted(&mut flat, 1, work.owner).map_err(stopped)?;
                    flat.push(other);
                }
            }
        }
        Self::canonical_set(&mut flat, work)?;
        // R ∪ ¬R = Σ* is worth folding: derivatives of complements create
        // exactly this shape, and the fold keeps their states small.
        if Self::has_complement(&flat, work)? {
            return Ok(Self::All);
        }
        Ok(match flat.len() {
            0 => Self::Empty,
            1 => flat.pop().unwrap_or(Self::Empty),
            _ => Self::Union(flat),
        })
    }

    fn inter(parts: impl IntoIterator<Item = Self>, work: &mut Work<'_>) -> EvalResult<Self> {
        let mut flat = Vec::new();
        for part in parts {
            work.charge(1)?;
            match part {
                Self::Empty => return Ok(Self::Empty),
                Self::All => {}
                Self::Inter(inner) => {
                    reserve_counted(&mut flat, inner.len(), work.owner).map_err(stopped)?;
                    work.charge(inner.len())?;
                    flat.extend(inner);
                }
                other => {
                    reserve_counted(&mut flat, 1, work.owner).map_err(stopped)?;
                    flat.push(other);
                }
            }
        }
        Self::canonical_set(&mut flat, work)?;
        // R ∩ ¬R = ∅, folded for the same reason as in `union`.
        if Self::has_complement(&flat, work)? {
            return Ok(Self::Empty);
        }
        Ok(match flat.len() {
            0 => Self::All,
            1 => flat.pop().unwrap_or(Self::All),
            _ => Self::Inter(flat),
        })
    }

    fn star(inner: Self, work: &mut Work<'_>) -> EvalResult<Self> {
        work.charge(1)?;
        Ok(match inner {
            Self::Empty | Self::Eps => Self::Eps,
            Self::All => Self::All,
            Self::Star(inner) => Self::Star(inner),
            Self::Loop(inner, 0, _) => return Self::star(*inner, work),
            other => Self::Star(other.into_box(work)?),
        })
    }

    fn comp(inner: Self, work: &mut Work<'_>) -> EvalResult<Self> {
        work.charge(1)?;
        Ok(match inner {
            Self::Empty => Self::All,
            Self::All => Self::Empty,
            Self::Comp(inner) => *inner,
            other => Self::Comp(other.into_box(work)?),
        })
    }

    fn plus(inner: Self, work: &mut Work<'_>) -> EvalResult<Self> {
        let copy = inner.clone_counted(work)?;
        let star = Self::star(inner, work)?;
        Self::concat([copy, star], work)
    }

    fn opt(inner: Self, work: &mut Work<'_>) -> EvalResult<Self> {
        Self::union([Self::Eps, inner], work)
    }

    /// `⋃_{k=lo..=hi} inner^k`, with the SMT-LIB convention that a reversed
    /// count range denotes the empty language.
    fn loop_bounded(inner: Self, lo: u32, hi: u32, work: &mut Work<'_>) -> EvalResult<Self> {
        work.charge(1)?;
        if lo > hi {
            return Ok(Self::Empty);
        }
        if hi == 0 {
            return Ok(Self::Eps);
        }
        Ok(match inner {
            Self::Empty if lo == 0 => Self::Eps,
            Self::Empty => Self::Empty,
            Self::Eps => Self::Eps,
            Self::All => Self::All,
            Self::Star(inner) => Self::Star(inner),
            other => Self::Loop(other.into_box(work)?, lo, hi),
        })
    }

    fn nullable(&self, work: &mut Work<'_>) -> EvalResult<bool> {
        work.charge(1)?;
        Ok(match self {
            Self::Empty | Self::AnyChar | Self::Range(..) => false,
            Self::Lit(chars) => chars.is_empty(),
            Self::Eps | Self::All | Self::Star(_) => true,
            Self::Concat(parts) | Self::Inter(parts) => {
                for part in parts {
                    if !part.nullable(work)? {
                        return Ok(false);
                    }
                }
                true
            }
            Self::Union(parts) => {
                for part in parts {
                    if part.nullable(work)? {
                        return Ok(true);
                    }
                }
                false
            }
            Self::Comp(inner) => !inner.nullable(work)?,
            Self::Loop(inner, lo, _) => *lo == 0 || inner.nullable(work)?,
        })
    }

    fn size(&self, work: &mut Work<'_>) -> EvalResult<usize> {
        work.charge(1)?;
        Ok(match self {
            Self::Empty | Self::Eps | Self::AnyChar | Self::All | Self::Range(..) => 1,
            Self::Lit(chars) => 1usize.saturating_add(chars.len() / 8),
            Self::Concat(parts) | Self::Union(parts) | Self::Inter(parts) => {
                let mut total = 1usize;
                for part in parts {
                    total = total.saturating_add(part.size(work)?);
                }
                total
            }
            Self::Star(inner) | Self::Comp(inner) | Self::Loop(inner, ..) => {
                1usize.saturating_add(inner.size(work)?)
            }
        })
    }

    fn collect_critical(&self, out: &mut Vec<u32>, work: &mut Work<'_>) -> EvalResult<()> {
        work.charge(1)?;
        match self {
            Self::Lit(chars) => {
                for &point in chars {
                    insert_alphabet_point(out, point, work)?;
                    if out.len() > MAX_CRITICAL {
                        return Err(work_err());
                    }
                }
            }
            Self::Range(lo, hi) => {
                insert_alphabet_point(out, *lo, work)?;
                insert_alphabet_point(out, *hi, work)?;
            }
            Self::Concat(parts) | Self::Union(parts) | Self::Inter(parts) => {
                for part in parts {
                    part.collect_critical(out, work)?;
                }
            }
            Self::Star(inner) | Self::Comp(inner) | Self::Loop(inner, ..) => {
                inner.collect_critical(out, work)?;
            }
            Self::Empty | Self::Eps | Self::AnyChar | Self::All => {}
        }
        if out.len() > MAX_CRITICAL {
            return Err(work_err());
        }
        Ok(())
    }

    /// Copy payloads only after their destination storage and traversal have
    /// been admitted by the original owner. In particular, cloning a state
    /// into `seen` must not bypass the derivative's resource accounting.
    fn clone_counted(&self, work: &mut Work<'_>) -> EvalResult<Self> {
        work.charge(1)?;
        Ok(match self {
            Self::Empty => Self::Empty,
            Self::Eps => Self::Eps,
            Self::AnyChar => Self::AnyChar,
            Self::All => Self::All,
            Self::Range(lo, hi) => Self::Range(*lo, *hi),
            Self::Lit(chars) => Self::Lit(Self::copy_points(chars, work)?),
            Self::Concat(parts) => Self::Concat(Self::copy_parts(parts, work)?),
            Self::Union(parts) => Self::Union(Self::copy_parts(parts, work)?),
            Self::Inter(parts) => Self::Inter(Self::copy_parts(parts, work)?),
            Self::Star(inner) => Self::Star(inner.copy_box(work)?),
            Self::Comp(inner) => Self::Comp(inner.copy_box(work)?),
            Self::Loop(inner, lo, hi) => Self::Loop(inner.copy_box(work)?, *lo, *hi),
        })
    }

    fn copy_box(&self, work: &mut Work<'_>) -> EvalResult<Box<Self>> {
        work.owner
            .admit(0, std::mem::size_of::<Self>())
            .map_err(stopped)?;
        Ok(Box::new(self.clone_counted(work)?))
    }

    fn into_box(self, work: &mut Work<'_>) -> EvalResult<Box<Self>> {
        work.owner
            .admit(0, std::mem::size_of::<Self>())
            .map_err(stopped)?;
        Ok(Box::new(self))
    }

    fn kind(&self) -> u8 {
        match self {
            Self::Empty => 0,
            Self::Eps => 1,
            Self::Lit(_) => 2,
            Self::AnyChar => 3,
            Self::All => 4,
            Self::Range(..) => 5,
            Self::Concat(_) => 6,
            Self::Union(_) => 7,
            Self::Inter(_) => 8,
            Self::Star(_) => 9,
            Self::Comp(_) => 10,
            Self::Loop(..) => 11,
        }
    }

    /// The prior structural order, with admission before each recursive
    /// comparison and inspected literal point. Refusal is returned directly;
    /// it is never translated into an ordering to finish an opaque sort.
    fn cmp_counted(&self, other: &Self, work: &mut Work<'_>) -> EvalResult<Ordering> {
        work.charge(1)?;
        Ok(match (self, other) {
            (Self::Lit(a), Self::Lit(b)) => {
                for (a, b) in a.iter().zip(b) {
                    work.charge(1)?;
                    let order = a.cmp(b);
                    if order != Ordering::Equal {
                        return Ok(order);
                    }
                }
                a.len().cmp(&b.len())
            }
            (Self::Range(a, b), Self::Range(c, d)) => (a, b).cmp(&(c, d)),
            (Self::Concat(a), Self::Concat(b))
            | (Self::Union(a), Self::Union(b))
            | (Self::Inter(a), Self::Inter(b)) => {
                for (a, b) in a.iter().zip(b) {
                    let order = a.cmp_counted(b, work)?;
                    if order != Ordering::Equal {
                        return Ok(order);
                    }
                }
                a.len().cmp(&b.len())
            }
            (Self::Star(a), Self::Star(b)) | (Self::Comp(a), Self::Comp(b)) => {
                a.cmp_counted(b, work)?
            }
            (Self::Loop(a, lo, hi), Self::Loop(b, other_lo, other_hi)) => {
                let order = a.cmp_counted(b, work)?;
                if order != Ordering::Equal {
                    return Ok(order);
                }
                (lo, hi).cmp(&(other_lo, other_hi))
            }
            (Self::Empty, Self::Empty)
            | (Self::Eps, Self::Eps)
            | (Self::AnyChar, Self::AnyChar)
            | (Self::All, Self::All) => Ordering::Equal,
            _ => {
                let order = self.kind().cmp(&other.kind());
                if order == Ordering::Equal {
                    return Err("regular-language comparison lacks a payload interpretation".into());
                }
                order
            }
        })
    }

    /// Only fixed-size fingerprints enter the native map. Hashing a language
    /// is an interruptible traversal; collisions still require full counted
    /// structural comparison and can never identify two product states.
    fn hash_counted(&self, hash: &mut impl Hasher, work: &mut Work<'_>) -> EvalResult<()> {
        work.charge(1)?;
        hash.write_u8(self.kind());
        match self {
            Self::Lit(points) => {
                hash.write_usize(points.len());
                for &point in points {
                    work.charge(1)?;
                    hash.write_u32(point);
                }
            }
            Self::Range(lo, hi) => {
                hash.write_u32(*lo);
                hash.write_u32(*hi);
            }
            Self::Concat(parts) | Self::Union(parts) | Self::Inter(parts) => {
                hash.write_usize(parts.len());
                for part in parts {
                    part.hash_counted(hash, work)?;
                }
            }
            Self::Star(inner) | Self::Comp(inner) => inner.hash_counted(hash, work)?,
            Self::Loop(inner, lo, hi) => {
                inner.hash_counted(hash, work)?;
                hash.write_u32(*lo);
                hash.write_u32(*hi);
            }
            Self::Empty | Self::Eps | Self::AnyChar | Self::All => {}
        }
        Ok(())
    }

    /// In-place heapsort keeps O(n log n) comparison work and no scratch
    /// allocation while allowing a comparison refusal to stop immediately.
    fn canonical_set(parts: &mut Vec<Self>, work: &mut Work<'_>) -> EvalResult<()> {
        fn sift(parts: &mut [Lang], mut root: usize, work: &mut Work<'_>) -> EvalResult<()> {
            while root < parts.len() / 2 {
                let mut child = root * 2 + 1;
                if child + 1 < parts.len()
                    && parts[child].cmp_counted(&parts[child + 1], work)? == Ordering::Less
                {
                    child += 1;
                }
                if parts[root].cmp_counted(&parts[child], work)? != Ordering::Less {
                    return Ok(());
                }
                work.charge(1)?;
                parts.swap(root, child);
                root = child;
            }
            Ok(())
        }
        for root in (0..parts.len() / 2).rev() {
            sift(parts, root, work)?;
        }
        for end in (1..parts.len()).rev() {
            work.charge(1)?;
            parts.swap(0, end);
            sift(&mut parts[..end], 0, work)?;
        }
        let mut kept = usize::from(!parts.is_empty());
        for read in 1..parts.len() {
            if parts[kept - 1].cmp_counted(&parts[read], work)? != Ordering::Equal {
                work.charge(1)?;
                parts.swap(kept, read);
                kept += 1;
            }
        }
        parts.truncate(kept);
        Ok(())
    }

    fn has_complement(parts: &[Self], work: &mut Work<'_>) -> EvalResult<bool> {
        for part in parts {
            work.charge(1)?;
            if let Self::Comp(inner) = part {
                let (mut lo, mut hi) = (0, parts.len());
                while lo < hi {
                    let mid = lo + (hi - lo) / 2;
                    match parts[mid].cmp_counted(inner, work)? {
                        Ordering::Less => lo = mid + 1,
                        Ordering::Greater => hi = mid,
                        Ordering::Equal => return Ok(true),
                    }
                }
            }
        }
        Ok(false)
    }

    fn copy_points(points: &[u32], work: &mut Work<'_>) -> EvalResult<Vec<u32>> {
        work.charge(points.len())?;
        let mut copied = Vec::new();
        reserve_counted(&mut copied, points.len(), work.owner).map_err(stopped)?;
        copied.extend_from_slice(points);
        Ok(copied)
    }

    fn copy_parts(parts: &[Self], work: &mut Work<'_>) -> EvalResult<Vec<Self>> {
        let mut copied = Vec::new();
        reserve_counted(&mut copied, parts.len(), work.owner).map_err(stopped)?;
        for part in parts {
            copied.push(part.clone_counted(work)?);
        }
        Ok(copied)
    }

    /// Brzozowski derivative with respect to one SMT-LIB code point.
    fn derive(&self, c: u32, work: &mut Work<'_>) -> EvalResult<Self> {
        work.charge(1)?;
        Ok(match self {
            Self::Empty | Self::Eps => Self::Empty,
            Self::All => Self::All,
            Self::AnyChar => Self::Eps,
            Self::Range(lo, hi) if *lo <= c && c <= *hi => Self::Eps,
            Self::Range(..) => Self::Empty,
            Self::Lit(chars) => match chars.split_first() {
                Some((&first, rest)) if first == c => Self::literal(Self::copy_points(rest, work)?),
                _ => Self::Empty,
            },
            Self::Concat(parts) => {
                let Some((first, rest)) = parts.split_first() else {
                    return Ok(Self::Empty);
                };
                let rest_lang = Self::concat(Self::copy_parts(rest, work)?, work)?;
                let head = Self::concat(
                    [first.derive(c, work)?, rest_lang.clone_counted(work)?],
                    work,
                )?;
                if first.nullable(work)? {
                    Self::union([head, rest_lang.derive(c, work)?], work)?
                } else {
                    head
                }
            }
            Self::Union(parts) | Self::Inter(parts) => {
                let mut derivatives = Vec::new();
                reserve_counted(&mut derivatives, parts.len(), work.owner).map_err(stopped)?;
                for part in parts {
                    derivatives.push(part.derive(c, work)?);
                }
                if matches!(self, Self::Union(_)) {
                    Self::union(derivatives, work)?
                } else {
                    Self::inter(derivatives, work)?
                }
            }
            Self::Star(inner) => {
                Self::concat([inner.derive(c, work)?, self.clone_counted(work)?], work)?
            }
            Self::Comp(inner) => Self::comp(inner.derive(c, work)?, work)?,
            Self::Loop(inner, lo, hi) => {
                let head = inner.derive(c, work)?;
                let rest = Self::loop_bounded(
                    inner.clone_counted(work)?,
                    lo.saturating_sub(1),
                    hi.saturating_sub(1),
                    work,
                )?;
                Self::concat([head, rest], work)?
            }
        })
    }
}

struct Translator<'a, F> {
    terms: &'a TermStore,
    eval_string: F,
    work: Work<'a>,
    base_depth: usize,
}

impl<F> Translator<'_, F>
where
    F: FnMut(TermId) -> EvalResult<String>,
{
    fn eval_code_points(&mut self, term: TermId) -> EvalResult<Vec<u32>> {
        let value = (self.eval_string)(term)?;
        // Pay for the UTF-8 scan before counting or allocating code points.
        self.work.charge(value.len())?;
        let mut points = Vec::new();
        reserve_counted(&mut points, value.chars().count(), self.work.owner).map_err(stopped)?;
        for ch in value.chars() {
            let point = smtlib_code_point(ch);
            if point > SMTLIB_MAX_CODE_POINT {
                return Err("string contains a code point outside the SMT-LIB alphabet".into());
            }
            points.push(point);
        }
        Ok(points)
    }

    fn translate_all(&mut self, args: &[TermId], depth: usize) -> EvalResult<Vec<Lang>> {
        let mut langs = Vec::new();
        reserve_counted(&mut langs, args.len(), self.work.owner).map_err(stopped)?;
        for &child in args {
            langs.push(self.translate(child, depth + 1)?);
        }
        Ok(langs)
    }

    fn checked(&mut self, lang: Lang) -> EvalResult<Lang> {
        let size = lang.size(&mut self.work)?;
        self.work.charge(size)?;
        if size > MAX_LANG_SIZE {
            return Err(work_err());
        }
        Ok(lang)
    }

    fn translate(&mut self, term: TermId, depth: usize) -> EvalResult<Lang> {
        if depth > MAX_EVAL_DEPTH || depth.saturating_sub(self.base_depth) > MAX_REGEX_DEPTH {
            return Err(depth_err());
        }
        if !matches!(self.terms.sort(term), Sort::RegLan) {
            return Err("regular-language operand has the wrong sort".into());
        }
        self.work.charge(1)?;
        let TermData::App(symbol, args) = self.terms.get(term) else {
            return Err("regular-language term is not a ground regex application".into());
        };
        self.work.charge(symbol.name().len().div_ceil(64).max(1))?;
        if matches!(symbol, Symbol::Named(name) if self.terms.is_declared_function(name)) {
            return Err(
                "declared function has no committed regular-language interpretation".into(),
            );
        }
        // The store is immutable throughout translation. Borrow its authored
        // operator and edges instead of copying an unpriced argument list.
        let name = symbol.name();
        let indexed = matches!(symbol, Symbol::Indexed(..));
        if indexed && !matches!(name, "re.loop" | "re.^") {
            return Err(format!("unsupported indexed regular-language operator {name}").into());
        }
        let lang = match (name, args.len()) {
            ("re.none", 0) => Lang::Empty,
            ("re.all", 0) => Lang::All,
            ("re.allchar", 0) => Lang::AnyChar,
            ("re.range", 2) => {
                let lo = self.eval_code_points(args[0])?;
                let hi = self.eval_code_points(args[1])?;
                match (lo.as_slice(), hi.as_slice()) {
                    ([lo], [hi]) if lo <= hi => Lang::Range(*lo, *hi),
                    _ => Lang::Empty,
                }
            }
            ("str.to_re" | "str.to.re", 1) => Lang::literal(self.eval_code_points(args[0])?),
            ("re.++", n) if n > 0 => {
                let parts = self.translate_all(args, depth)?;
                Lang::concat(parts, &mut self.work)?
            }
            ("re.union", n) if n > 0 => {
                let parts = self.translate_all(args, depth)?;
                Lang::union(parts, &mut self.work)?
            }
            ("re.inter", n) if n > 0 => {
                let parts = self.translate_all(args, depth)?;
                Lang::inter(parts, &mut self.work)?
            }
            ("re.*", 1) => {
                let inner = self.translate(args[0], depth + 1)?;
                Lang::star(inner, &mut self.work)?
            }
            ("re.+", 1) => {
                let inner = self.translate(args[0], depth + 1)?;
                Lang::plus(inner, &mut self.work)?
            }
            ("re.opt", 1) => {
                let inner = self.translate(args[0], depth + 1)?;
                Lang::opt(inner, &mut self.work)?
            }
            ("re.comp", 1) => {
                let inner = self.translate(args[0], depth + 1)?;
                Lang::comp(inner, &mut self.work)?
            }
            ("re.diff", n) if n >= 2 => {
                let mut langs = self.translate_all(args, depth)?;
                // Reuse the admitted translation buffer. Only operands after
                // the first are complemented in an n-ary difference.
                for lang in langs.iter_mut().skip(1) {
                    let inner = std::mem::replace(lang, Lang::Empty);
                    *lang = Lang::comp(inner, &mut self.work)?;
                }
                Lang::inter(langs, &mut self.work)?
            }
            ("re.loop", 1) => {
                let Symbol::Indexed(_, indices) = symbol else {
                    return Err("re.loop is missing its repetition indices".into());
                };
                let [lo, hi] = indices.as_slice() else {
                    return Err("re.loop requires exactly two repetition indices".into());
                };
                let inner = self.translate(args[0], depth + 1)?;
                Lang::loop_bounded(inner, *lo, *hi, &mut self.work)?
            }
            ("re.^", 1) => {
                let Symbol::Indexed(_, indices) = symbol else {
                    return Err("re.^ is missing its repetition index".into());
                };
                let [count] = indices.as_slice() else {
                    return Err("re.^ requires exactly one repetition index".into());
                };
                let inner = self.translate(args[0], depth + 1)?;
                Lang::loop_bounded(inner, *count, *count, &mut self.work)?
            }
            _ => {
                return Err(format!("unsupported regular-language operator {name}").into());
            }
        };
        self.checked(lang)
    }
}

fn insert_alphabet_point(points: &mut Vec<u32>, point: u32, work: &mut Work<'_>) -> EvalResult<()> {
    let (mut lo, mut hi) = (0, points.len());
    while lo < hi {
        work.charge(1)?;
        let mid = lo + (hi - lo) / 2;
        match points[mid].cmp(&point) {
            std::cmp::Ordering::Less => lo = mid + 1,
            std::cmp::Ordering::Greater => hi = mid,
            std::cmp::Ordering::Equal => return Ok(()),
        }
    }
    work.charge(points.len() - lo)?;
    reserve_counted(points, 1, work.owner).map_err(stopped)?;
    points.insert(lo, point);
    Ok(())
}

/// One representative of every derivative-behaviour class of the alphabet
/// for `left` and `right`.
fn class_alphabet(left: &Lang, right: &Lang, work: &mut Work<'_>) -> EvalResult<Vec<u32>> {
    let mut critical = Vec::new();
    left.collect_critical(&mut critical, work)?;
    right.collect_critical(&mut critical, work)?;
    if critical.is_empty() {
        insert_alphabet_point(&mut critical, 0, work)?;
        return Ok(critical);
    }
    let mentioned = Lang::copy_points(&critical, work)?;
    let mut representatives = critical;
    for pair in mentioned.windows(2) {
        work.charge(1)?;
        if pair[0] + 1 < pair[1] {
            insert_alphabet_point(&mut representatives, pair[0] + 1, work)?;
        }
    }
    if let Some(&max) = mentioned.last() {
        if max < SMTLIB_MAX_CODE_POINT {
            insert_alphabet_point(&mut representatives, max + 1, work)?;
        } else if mentioned.first().is_some_and(|&min| min > 0) {
            insert_alphabet_point(&mut representatives, 0, work)?;
        }
    }
    Ok(representatives)
}

#[derive(Default)]
struct Seen {
    buckets: DetHashMap<u64, Vec<(Lang, Lang)>>,
    states: usize,
}

impl Seen {
    fn insert(&mut self, a: &Lang, b: &Lang, work: &mut Work<'_>) -> EvalResult<bool> {
        let mut hash = self.buckets.hasher().build_hasher();
        a.hash_counted(&mut hash, work)?;
        b.hash_counted(&mut hash, work)?;
        self.insert_hashed(hash.finish(), a, b, work)
    }

    fn insert_hashed(
        &mut self,
        hash: u64,
        a: &Lang,
        b: &Lang,
        work: &mut Work<'_>,
    ) -> EvalResult<bool> {
        work.charge(1)?;
        let prior = self.buckets.get(&hash);
        let new_bucket = prior.is_none();
        if let Some(bucket) = prior {
            for (prior_a, prior_b) in bucket {
                if a.cmp_counted(prior_a, work)? == Ordering::Equal
                    && b.cmp_counted(prior_b, work)? == Ordering::Equal
                {
                    return Ok(false);
                }
            }
        }
        if self.states >= MAX_PAIRS {
            return Err(work_err());
        }
        if new_bucket {
            reserve_map_counted(&mut self.buckets, 1, work.owner).map_err(stopped)?;
        }
        work.charge(1)?;
        let bucket = self.buckets.entry(hash).or_default();
        reserve_counted(bucket, 1, work.owner).map_err(stopped)?;
        let copy = (a.clone_counted(work)?, b.clone_counted(work)?);
        bucket.push(copy);
        self.states += 1;
        Ok(true)
    }
}

fn decide_equal(left: Lang, right: Lang, work: &mut Work<'_>) -> EvalResult<bool> {
    work.charge(1)?;
    if left.cmp_counted(&right, work)? == Ordering::Equal {
        return Ok(true);
    }
    let alphabet = class_alphabet(&left, &right, work)?;
    let mut seen = Seen::default();
    let mut frontier = Vec::new();
    seen.insert(&left, &right, work)?;
    reserve_counted(&mut frontier, 1, work.owner).map_err(stopped)?;
    frontier.push((left, right));
    // Product reachability needs no breadth-first ordering. A counted stack
    // retains the same finite visited-state bound without an unpriced deque.
    while let Some((a, b)) = frontier.pop() {
        if a.nullable(work)? != b.nullable(work)? {
            return Ok(false);
        }
        work.charge(1)?;
        for &c in &alphabet {
            let size = a.size(work)?.saturating_add(b.size(work)?);
            if size > MAX_LANG_SIZE {
                return Err(work_err());
            }
            work.charge(size)?;
            let next = (a.derive(c, work)?, b.derive(c, work)?);
            if next.0.nullable(work)? != next.1.nullable(work)? {
                return Ok(false);
            }
            if next.0.cmp_counted(&next.1, work)? == Ordering::Equal {
                continue;
            }
            let next_size = next.0.size(work)?.saturating_add(next.1.size(work)?);
            if next_size > MAX_LANG_SIZE {
                return Err(work_err());
            }
            if seen.insert(&next.0, &next.1, work)? {
                reserve_counted(&mut frontier, 1, work.owner).map_err(stopped)?;
                frontier.push(next);
            }
        }
    }
    Ok(true)
}

/// Decide `[[left]] = [[right]]` for two RegLan terms whose string leaves
/// `eval_string` evaluates against the model. Any non-regex shape,
/// unsupported operator, or bound above is an `Err` (fail closed).
pub(crate) fn languages_equal(
    terms: &TermStore,
    left: TermId,
    right: TermId,
    entry_depth: usize,
    eval_string: impl FnMut(TermId) -> EvalResult<String>,
    owner: &dyn TermConstructionAdmission,
) -> EvalResult<bool> {
    owner.check().map_err(stopped)?;
    if !matches!(terms.sort(left), Sort::RegLan) || !matches!(terms.sort(right), Sort::RegLan) {
        return Err("regular-language equality operand has the wrong sort".into());
    }
    let mut translator = Translator {
        terms,
        eval_string,
        work: Work {
            remaining: EQUIV_WORK,
            owner,
        },
        base_depth: entry_depth,
    };
    let left_lang = translator.translate(left, entry_depth)?;
    let right_lang = translator.translate(right, entry_depth)?;
    let result = decide_equal(left_lang, right_lang, &mut translator.work)?;
    owner.check().map_err(stopped)?;
    Ok(result)
}

#[cfg(test)]
mod admission_tests {
    use super::*;
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use std::sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering as AtomicOrdering},
        Arc,
    };

    #[test]
    fn recursive_language_scans_observe_the_original_stop_and_short_circuit() {
        for operation in 0..2 {
            let calls = Arc::new(AtomicUsize::new(0));
            let observed = Arc::clone(&calls);
            let owner = CountedAdmission::new(
                FiniteAdmissionGrant::new(1_000_000, 1 << 20),
                None,
                Arc::new(move || observed.fetch_add(1, AtomicOrdering::Relaxed) >= 8),
            )
            .unwrap();
            let mut work = Work {
                remaining: EQUIV_WORK,
                owner: &owner,
            };
            let lang = Lang::Concat((0..4096).map(|_| Lang::Eps).collect());
            if operation == 0 {
                assert!(lang.size(&mut work).is_err());
                assert!(Lang::Eps.size(&mut work).is_err());
            } else {
                assert!(lang.nullable(&mut work).is_err());
                assert!(Lang::Eps.nullable(&mut work).is_err());
            }
            assert!(owner.usage().unwrap().work_admitted < 4096);
        }
        for (lang, expected) in [
            (Lang::Concat(vec![Lang::Empty, Lang::All]), false),
            (Lang::Union(vec![Lang::Eps, Lang::AnyChar]), true),
        ] {
            let owner =
                CountedAdmission::new(FiniteAdmissionGrant::new(2, 0), None, Arc::new(|| false))
                    .unwrap();
            let mut work = Work {
                remaining: EQUIV_WORK,
                owner: &owner,
            };
            assert_eq!(lang.nullable(&mut work).unwrap(), expected);
            assert_eq!(owner.usage().unwrap().work_admitted, 2);
        }
    }

    #[test]
    fn product_hash_collisions_require_both_structural_components() {
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(1_000_000, 1 << 20),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        let mut work = Work {
            remaining: EQUIV_WORK,
            owner: &owner,
        };
        let mut seen = Seen::default();
        let a = Lang::Lit(vec![97, 98]);
        let other = Lang::Lit(vec![97, 99]);
        // Force the real collision path, independent of the native hash seed.
        assert!(seen
            .insert_hashed(0, &a, &Lang::AnyChar, &mut work)
            .unwrap());
        assert!(seen
            .insert_hashed(0, &other, &Lang::AnyChar, &mut work)
            .unwrap());
        assert!(seen.insert_hashed(0, &a, &Lang::All, &mut work).unwrap());
        assert!(!seen
            .insert_hashed(0, &a, &Lang::AnyChar, &mut work)
            .unwrap());
        assert_eq!(seen.states, 3);
        assert_eq!(seen.buckets.len(), 1);
        assert_eq!(seen.buckets[&0].len(), 3);
        let mut normal = Seen::default();
        assert!(normal.insert(&a, &other, &mut work).unwrap());
        assert!(!normal.insert(&a, &other, &mut work).unwrap());
        assert!(normal.insert(&other, &a, &mut work).unwrap());
        assert_eq!(normal.states, 2);
    }

    #[test]
    fn product_hashing_stops_inside_a_literal_before_creating_a_bucket() {
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let active = Arc::new(AtomicBool::new(true));
        let stop = Arc::clone(&active);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(1_000_000, 1 << 20),
            None,
            Arc::new(move || {
                stop.load(AtomicOrdering::Relaxed)
                    && observed.fetch_add(1, AtomicOrdering::Relaxed) >= 8
            }),
        )
        .unwrap();
        let mut work = Work {
            remaining: EQUIV_WORK,
            owner: &owner,
        };
        let mut seen = Seen::default();
        let literal = Lang::Lit(vec![97; 4096]);
        assert!(seen.insert(&literal, &Lang::AnyChar, &mut work).is_err());
        assert!(seen.buckets.is_empty());
        assert!(owner.usage().unwrap().work_admitted < 4096);
        active.store(false, AtomicOrdering::Relaxed);
        assert!(seen.insert(&literal, &Lang::AnyChar, &mut work).is_err());
        assert!(seen.buckets.is_empty());
    }

    #[test]
    fn counted_order_and_fallible_sort_preserve_all_language_kinds() {
        fn examples() -> Vec<Lang> {
            vec![
                Lang::Loop(Box::new(Lang::AnyChar), 2, 4),
                Lang::Loop(Box::new(Lang::AnyChar), 1, 4),
                Lang::Loop(Box::new(Lang::AnyChar), 1, 3),
                Lang::Comp(Box::new(Lang::AnyChar)),
                Lang::Star(Box::new(Lang::AnyChar)),
                Lang::Inter(vec![Lang::AnyChar]),
                Lang::Union(vec![Lang::AnyChar]),
                Lang::Concat(vec![Lang::AnyChar, Lang::All]),
                Lang::Concat(vec![Lang::AnyChar]),
                Lang::Range(1, 3),
                Lang::Range(1, 2),
                Lang::Range(0, 3),
                Lang::All,
                Lang::AnyChar,
                Lang::Lit(vec![98]),
                Lang::Lit(vec![97, 98]),
                Lang::Lit(vec![97]),
                Lang::Lit(vec![]),
                Lang::Eps,
                Lang::Empty,
                Lang::Range(1, 3),
                Lang::Concat(vec![Lang::AnyChar]),
            ]
        }
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(1_000_000, 1 << 20),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        let mut work = Work {
            remaining: EQUIV_WORK,
            owner: &owner,
        };
        let cases = examples();
        // The derived order is retained only for this independent test oracle;
        // production callers cannot silently fall back to an opaque Ord sort.
        for a in &cases {
            for b in &cases {
                assert_eq!(a.cmp_counted(b, &mut work).unwrap(), a.cmp(b));
            }
        }
        let mut expected = examples();
        expected.sort_unstable();
        expected.dedup();
        for len in 0..=cases.len() {
            let mut actual = examples();
            actual.truncate(len);
            let mut reference = examples();
            reference.truncate(len);
            reference.sort_unstable();
            reference.dedup();
            Lang::canonical_set(&mut actual, &mut work).unwrap();
            assert_eq!(actual, reference);
        }
        let mut actual = examples();
        Lang::canonical_set(&mut actual, &mut work).unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn literal_comparison_observes_cancellation_inside_the_payload() {
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let stop = Arc::new(AtomicBool::new(true));
        let active = Arc::clone(&stop);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(1_000_000, 1 << 20),
            None,
            Arc::new(move || {
                active.load(AtomicOrdering::Relaxed)
                    && observed.fetch_add(1, AtomicOrdering::Relaxed) >= 8
            }),
        )
        .unwrap();
        let a = Lang::Lit(vec![97; 4096]);
        let b = Lang::Lit(vec![97; 4096]);
        let mut work = Work {
            remaining: EQUIV_WORK,
            owner: &owner,
        };
        assert!(a.cmp_counted(&b, &mut work).is_err());
        assert!(owner.usage().unwrap().work_admitted < 4096);
        stop.store(false, AtomicOrdering::Relaxed);
        assert!(a.cmp_counted(&b, &mut work).is_err());
    }

    #[test]
    fn canonicalizers_admit_flattened_buffers_and_new_boxes() {
        for bytes in [0, 1 << 20] {
            let owner = CountedAdmission::new(
                FiniteAdmissionGrant::new(1_000_000, bytes),
                None,
                Arc::new(|| false),
            )
            .unwrap();
            let mut work = Work {
                remaining: EQUIV_WORK,
                owner: &owner,
            };
            let concat = Lang::concat(
                [
                    Lang::Eps,
                    Lang::Concat(vec![Lang::AnyChar, Lang::Range(0, 42)]),
                ],
                &mut work,
            );
            if bytes == 0 {
                assert!(concat.is_err());
                assert!(Lang::star(Lang::AnyChar, &mut work).is_err());
                continue;
            }
            assert_eq!(
                concat.unwrap(),
                Lang::Concat(vec![Lang::AnyChar, Lang::Range(0, 42)])
            );
            let star = Lang::star(Lang::AnyChar, &mut work).unwrap();
            assert!(matches!(star, Lang::Star(_)));
            let complement = Lang::comp(star, &mut work).unwrap();
            let double = Lang::comp(complement, &mut work).unwrap();
            assert!(matches!(double, Lang::Star(_)));
            let repeated = Lang::loop_bounded(Lang::AnyChar, 2, 4, &mut work).unwrap();
            assert!(matches!(repeated, Lang::Loop(_, 2, 4)));
            let union = Lang::union(
                [
                    Lang::Empty,
                    Lang::Union(vec![Lang::AnyChar, Lang::Range(0, 42)]),
                    Lang::AnyChar,
                ],
                &mut work,
            )
            .unwrap();
            assert_eq!(union, Lang::Union(vec![Lang::AnyChar, Lang::Range(0, 42)]));
            let opposite = Lang::comp(Lang::AnyChar, &mut work).unwrap();
            assert_eq!(
                Lang::inter([Lang::AnyChar, opposite], &mut work).unwrap(),
                Lang::Empty
            );
            assert!(owner.usage().unwrap().storage_admitted > 0);
        }
        // Each boxing constructor must refuse independently, before the
        // allocation, rather than merely inheriting the concat's refusal.
        for operation in 0..3 {
            let owner = CountedAdmission::new(
                FiniteAdmissionGrant::new(1_000_000, 0),
                None,
                Arc::new(|| false),
            )
            .unwrap();
            let mut work = Work {
                remaining: EQUIV_WORK,
                owner: &owner,
            };
            let result = match operation {
                0 => Lang::star(Lang::AnyChar, &mut work),
                1 => Lang::comp(Lang::AnyChar, &mut work),
                _ => Lang::loop_bounded(Lang::AnyChar, 1, 2, &mut work),
            };
            assert!(result.is_err());
        }
    }

    #[test]
    fn counted_alphabet_preserves_boundary_and_interior_counterexamples() {
        for (left, expected) in [
            (
                Lang::Union(vec![
                    Lang::Range(0, 42),
                    Lang::Range(43, SMTLIB_MAX_CODE_POINT),
                ]),
                true,
            ),
            (Lang::Range(1, SMTLIB_MAX_CODE_POINT), false),
            (Lang::Range(0, SMTLIB_MAX_CODE_POINT - 1), false),
            (
                Lang::Union(vec![
                    Lang::Range(0, 42),
                    Lang::Range(44, SMTLIB_MAX_CODE_POINT),
                ]),
                false,
            ),
        ] {
            let owner = CountedAdmission::new(
                FiniteAdmissionGrant::new(1_000_000, 1 << 20),
                None,
                Arc::new(|| false),
            )
            .unwrap();
            assert_eq!(
                decide_equal(
                    left,
                    Lang::AnyChar,
                    &mut Work {
                        remaining: EQUIV_WORK,
                        owner: &owner,
                    },
                )
                .unwrap(),
                expected
            );
        }
    }

    #[test]
    fn derivative_state_copies_share_the_original_cumulative_limits() {
        let owner = |work, bytes| {
            CountedAdmission::new(
                FiniteAdmissionGrant::new(work, bytes),
                None,
                Arc::new(|| false),
            )
            .unwrap()
        };
        // Equivalent but structurally different languages require actual
        // derivatives and state copies, rather than the identity fast path.
        let decide = |owner: &CountedAdmission| {
            let left = Lang::Union(vec![Lang::Lit(vec![97, 98]), Lang::Lit(vec![97, 99])]);
            let right = Lang::Concat(vec![
                Lang::Lit(vec![97]),
                Lang::Union(vec![Lang::Lit(vec![98]), Lang::Lit(vec![99])]),
            ]);
            decide_equal(
                left,
                right,
                &mut Work {
                    remaining: EQUIV_WORK,
                    owner,
                },
            )
        };
        let paid = owner(1_000_000, 1 << 20);
        assert!(decide(&paid).unwrap());
        let usage = paid.usage().unwrap();
        assert!(usage.storage_admitted > 0);
        assert!(decide(&owner(usage.work_admitted, usage.storage_admitted)).unwrap());
        for limited in [
            owner(usage.work_admitted - 1, 1 << 20),
            owner(1_000_000, usage.storage_admitted - 1),
        ] {
            assert!(decide(&limited).is_err());
            assert!(decide(&limited).is_err());
        }
        let stopped = owner(1_000_000, 0);
        let nested = Lang::Loop(Box::new(Lang::Star(Box::new(Lang::Lit(vec![97])))), 1, 3);
        assert!(nested
            .clone_counted(&mut Work {
                remaining: EQUIV_WORK,
                owner: &stopped,
            })
            .is_err());
    }

    #[test]
    fn equality_translation_cannot_refresh_original_work_or_storage() {
        let mut terms = TermStore::new();
        let text = terms.mk_string("abcdefgh".into());
        let regex = terms.mk_app_structural(Symbol::named("str.to_re"), &[text], Sort::RegLan);
        let owner = |work, bytes| {
            CountedAdmission::new(
                FiniteAdmissionGrant::new(work, bytes),
                None,
                Arc::new(|| false),
            )
            .unwrap()
        };
        let decide = |admission: &CountedAdmission| {
            languages_equal(
                &terms,
                regex,
                regex,
                0,
                |_| Ok("abcdefgh".into()),
                admission,
            )
        };
        let paid = owner(1_000_000, 1 << 20);
        assert!(decide(&paid).unwrap());
        let usage = paid.usage().unwrap();
        assert!(usage.work_admitted > 0 && usage.storage_admitted > 0);
        for limited in [
            owner(usage.work_admitted - 1, 1 << 20),
            owner(1_000_000, usage.storage_admitted - 1),
        ] {
            assert!(decide(&limited).is_err());
            assert!(decide(&limited).is_err());
        }
    }

    #[test]
    fn equality_leaf_stop_survives_a_new_derivative_decision() {
        let mut terms = TermStore::new();
        let text = terms.mk_string("abc".into());
        let regex = terms.mk_app_structural(Symbol::named("str.to_re"), &[text], Sort::RegLan);
        let stop = Arc::new(AtomicBool::new(false));
        let observed = Arc::clone(&stop);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(1_000_000, 1 << 20),
            None,
            Arc::new(move || observed.load(AtomicOrdering::Relaxed)),
        )
        .unwrap();
        assert!(languages_equal(
            &terms,
            regex,
            regex,
            0,
            |_| {
                stop.store(true, AtomicOrdering::Relaxed);
                Ok("abc".into())
            },
            &owner,
        )
        .is_err());
        stop.store(false, AtomicOrdering::Relaxed);
        assert!(languages_equal(&terms, regex, regex, 0, |_| Ok("abc".into()), &owner).is_err());
    }
}
