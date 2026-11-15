// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact one-word zero-bit facts from an authored range or alignment guard.

use super::*;

pub(crate) enum GuardKind {
    Range { bound: TermId },
    Mask,
}

pub(crate) struct Frame {
    pub(crate) shared: TermId,
    pub(crate) changing: usize,
}

pub(crate) struct GuardedMask {
    pub(crate) root: TermId,
    pub(crate) guard: TermId,
    pub(crate) guard_position: usize,
    pub(crate) equality: TermId,
    pub(crate) left: TermId,
    pub(crate) right: TermId,
    pub(crate) source: TermId,
    pub(crate) width: u32,
    pub(crate) zeros: u128,
    pub(crate) frames: Vec<Frame>,
    pub(crate) kind: GuardKind,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Bit {
    Zero,
    One,
    Source(u32),
}

fn data(terms: &TermStore, term: TermId) -> Option<&TermData> {
    terms.entry_stamp(term)?;
    Some(terms.get(term))
}

fn application<'a>(terms: &'a TermStore, term: TermId, name: &str) -> Option<&'a [TermId]> {
    let TermData::App(Symbol::Named(op), args) = data(terms, term)? else {
        return None;
    };
    (op == name).then_some(args)
}

/// The two arguments of `name` applied to exactly two terms.
///
/// Read through `first`/`get` rather than a `[a, b]` slice pattern: the
/// pattern's element reads are not tied to the slice's length, so each one
/// was refuted as an unchecked index.
fn binary(terms: &TermStore, term: TermId, name: &str) -> Option<(TermId, TermId)> {
    two_args(application(terms, term, name)?)
}

/// Both elements of a two-element argument list, or `None` for any other length.
fn two_args(args: &[TermId]) -> Option<(TermId, TermId)> {
    match (args.len(), args.first(), args.get(1)) {
        (2, Some(&left), Some(&right)) => Some((left, right)),
        _ => None,
    }
}

/// The low `width` bits set, or `None` outside the admitted widths `1..=128`.
///
/// Every width reaching here comes from `equality`, which admits exactly
/// `1..=128`; the checked forms state that bound instead of assuming it (a
/// zero width would shift by 128, which `checked_shr` refuses).
fn width_mask(width: u32) -> Option<u128> {
    u128::MAX.checked_shr(128_u32.checked_sub(width)?)
}

fn literal(terms: &TermStore, term: TermId) -> Option<u128> {
    let TermData::Const(Constant::BitVec { value, .. }) = data(terms, term)? else {
        return None;
    };
    value.to_u128()
}

/// The only admitted clause is the negation of one two-conjunct authored
/// assertion. No premise is dropped: the guard supplies exact zero bits and
/// the other conjunct is the negation of the equality proved under those bits.
pub(crate) fn guarded_mask_identity(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Option<GuardedMask>, ProofCheckError> {
    let [negated] = clause else { return Ok(None) };
    let Some(TermData::Not(root)) = data(terms, *negated) else {
        return Ok(None);
    };
    let Some([a, b]) = application(terms, *root, "and") else {
        return Ok(None);
    };
    if terms.sort(*negated) != &Sort::Bool || terms.sort(*root) != &Sort::Bool {
        return Ok(None);
    }
    if !progress(MAX_WORK, MAX_ALLOCATION) {
        return Err(ProofCheckError::ResourceLimit);
    }
    for (position, guard, negated_equality) in [(0, *a, *b), (1, *b, *a)] {
        let Some(TermData::Not(eq)) = data(terms, negated_equality) else {
            continue;
        };
        let Some((left, right, width)) = equality(terms, &[*eq]) else {
            continue;
        };
        if terms.sort(negated_equality) != &Sort::Bool {
            continue;
        }
        if let Some(result) = check_guard(terms, *root, guard, position, *eq, left, right, width) {
            return Ok(Some(result));
        }
    }
    Ok(None)
}

fn parse_guard(
    terms: &TermStore,
    guard: TermId,
    width: u32,
) -> Option<(TermId, u128, [TermId; 2], GuardKind)> {
    data(terms, guard)?;
    if terms.sort(guard) != &Sort::Bool {
        return None;
    }
    let mask = width_mask(width)?;
    Some(if let Some((x, bound)) = binary(terms, guard, "bvult") {
        let bound_value = literal(terms, bound)?;
        if !bound_value.is_power_of_two() || bound_value > mask {
            return None;
        }
        // A power of two is at least one, so the subtraction never fails.
        (
            x,
            mask ^ bound_value.checked_sub(1)?,
            [x, bound],
            GuardKind::Range { bound },
        )
    } else {
        let (a, b, guard_width) = equality(terms, &[guard])?;
        if guard_width != width {
            return None;
        }
        let masked = if literal(terms, b) == Some(0) {
            a
        } else if literal(terms, a) == Some(0) {
            b
        } else {
            return None;
        };
        let (x, y) = binary(terms, masked, "bvand")?;
        let (source, zeros) = if let Some(value) = literal(terms, x) {
            (y, value)
        } else {
            (x, literal(terms, y)?)
        };
        (source, zeros, [a, b], GuardKind::Mask)
    })
}

fn check_guard(
    terms: &TermStore,
    root: TermId,
    guard: TermId,
    guard_position: usize,
    eq: TermId,
    left: TermId,
    right: TermId,
    width: u32,
) -> Option<GuardedMask> {
    let (source, zeros, children, kind) = parse_guard(terms, guard, width)?;
    let mask = width_mask(width)?;
    let mut normalizer = Normalizer {
        terms,
        width,
        mask,
        nodes: 0,
        work: 0,
        scale_constant_products: false,
        accept_elaborated_shifts: false,
    };
    for term in [left, right, children[0], children[1]] {
        normalizer.validate(term, 0)?;
    }
    let mut left_core = left;
    let mut right_core = right;
    let mut frames = Vec::new();
    while let (Some((a, b)), Some((c, d))) = (
        binary(terms, left_core, "bvadd"),
        binary(terms, right_core, "bvadd"),
    ) {
        if frames.len() >= MAX_DEPTH {
            return None;
        }
        if a == c {
            frames.push(Frame {
                shared: a,
                changing: 1,
            });
            left_core = b;
            right_core = d;
        } else if b == d {
            frames.push(Frame {
                shared: b,
                changing: 0,
            });
            left_core = a;
            right_core = c;
        } else {
            break;
        }
    }
    if left_core != source && right_core != source {
        return None;
    }
    let mut mapper = Mapper {
        normalizer: &mut normalizer,
        source,
        zeros,
    };
    if mapper.bits(left_core, 0)? != mapper.bits(right_core, 0)? {
        return None;
    }
    Some(GuardedMask {
        root,
        guard,
        guard_position,
        equality: eq,
        left: left_core,
        right: right_core,
        source,
        width,
        zeros,
        frames,
        kind,
    })
}

struct Mapper<'a, 'terms> {
    normalizer: &'a mut Normalizer<'terms>,
    source: TermId,
    zeros: u128,
}

impl Mapper<'_, '_> {
    fn bits(&mut self, term: TermId, depth: usize) -> Option<Vec<Bit>> {
        self.normalizer.visit(term, depth)?;
        let width = self.normalizer.width;
        // Every width here is an `equality` width in `1..=128`. Stating the
        // bound bounds each per-bit vector below and every bit position.
        if width == 0 || width > 128 {
            return None;
        }
        if term == self.source {
            let mut out = Vec::new();
            for i in 0..width {
                // `i < width <= 128`, so the shift is in range.
                let zero = self.zeros.checked_shr(i)? & 1 != 0;
                out.push(if zero { Bit::Zero } else { Bit::Source(i) });
            }
            return Some(out);
        }
        let terms = self.normalizer.terms;
        if let Some(value) = literal(terms, term) {
            let mut out = Vec::new();
            for i in 0..width {
                let one = value.checked_shr(i)? & 1 != 0;
                out.push(if one { Bit::One } else { Bit::Zero });
            }
            return Some(out);
        }
        let TermData::App(Symbol::Named(op), args) = data(terms, term)? else {
            return None;
        };
        let (left, right) = two_args(args)?;
        let next_depth = depth.checked_add(1)?;
        let a = self.bits(left, next_depth)?;
        if matches!(op.as_str(), "bvshl" | "bvlshr") {
            let amount = usize::try_from(literal(terms, right)?).ok()?;
            if amount > 128 {
                return None;
            }
            let mut out = Vec::new();
            for i in 0..width as usize {
                let bit = if op == "bvshl" {
                    // `j <= i < width == a.len()`: the read is always in
                    // range, and a shorter vector is refused, not padded.
                    match i.checked_sub(amount) {
                        Some(j) => *a.get(j)?,
                        None => Bit::Zero,
                    }
                } else {
                    // Bits shifted in from above the width are zero.
                    i.checked_add(amount)
                        .and_then(|j| a.get(j).copied())
                        .unwrap_or(Bit::Zero)
                };
                out.push(bit);
            }
            return Some(out);
        }
        let b = self.bits(right, next_depth)?;
        // Built bit by bit, like the vectors above: the pairs number at most
        // `width <= 128`, and the first pair with no bit refuses the term.
        let mut out = Vec::new();
        for (a, b) in a.into_iter().zip(b) {
            let bit = match (op.as_str(), a, b) {
                ("bvand", Bit::Zero, _) | ("bvand", _, Bit::Zero) => Bit::Zero,
                ("bvand", Bit::One, b) | ("bvand", b, Bit::One) => b,
                ("bvor", Bit::One, _) | ("bvor", _, Bit::One) => Bit::One,
                ("bvor" | "bvadd", Bit::Zero, b) | ("bvor" | "bvadd", b, Bit::Zero) => b,
                ("bvand" | "bvor", a, b) if a == b => a,
                _ => return None,
            };
            out.push(bit);
        }
        Some(out)
    }
}
