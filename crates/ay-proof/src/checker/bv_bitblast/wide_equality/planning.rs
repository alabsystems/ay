// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-only slices, bounded before building a producer expression. Limb
//! arithmetic follows SMT-LIB's modular word semantics:
//! https://smt-lib.org/theories-FixedSizeBitVectors.shtml
//! A k-bit limb uses k+1 bits: the top bit is carry for addition and borrow
//! for subtraction. Newly constructed arithmetic intermediates need at most
//! 65 bits; ordinary source words retain their existing 128-bit limit.

use super::*;

#[derive(Debug, thiserror::Error)]
pub(super) enum Error {
    #[error("{0}")]
    Unsupported(String),
    #[error("{0}")]
    Resource(String),
}

#[derive(Clone, Copy)]
struct Slice {
    high: u32,
    low: u32,
}

impl Slice {
    fn width(self) -> u32 {
        self.high - self.low + 1
    }
}

#[derive(Clone, Copy)]
enum Extension {
    Zero,
    Sign,
}

struct Planner<'t, 'p> {
    terms: &'t TermStore,
    poll: &'p mut dyn FnMut() -> Result<(), String>,
    pieces: usize,
    partition: Partition,
}

pub(super) fn plan(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
    partition: Partition,
    poll: &mut dyn FnMut() -> Result<(), String>,
) -> Result<Vec<(Piece, Piece)>, Error> {
    let mut planner = Planner {
        terms,
        poll,
        pieces: 0,
        partition,
    };
    let mut slices = Vec::new();
    planner.equalities(lhs, rhs, 0, &mut slices)?;
    Ok(slices)
}

impl Planner<'_, '_> {
    /// Concat is injective in its two equal-width fields. Honor matching
    /// field boundaries before fixed-size slicing, so common padding is its
    /// own validated reflexive equality rather than part of an arithmetic VC.
    fn equalities(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        depth: usize,
        out: &mut Vec<(Piece, Piece)>,
    ) -> Result<(), Error> {
        (self.poll)().map_err(Error::Resource)?;
        if depth > MAX_WIDE_WIDTH as usize {
            return Err(Error::Resource(
                "wide equality field planning exceeds its source-depth bound".into(),
            ));
        }
        let width = self.width(lhs)?;
        if self.width(rhs)? != width {
            return Err(Error::Unsupported(
                "wide equality operands have different sorts".into(),
            ));
        }
        if matches!(self.partition, Partition::Fields) && lhs != rhs {
            if let Some(fields) = self.matching_fields(lhs, rhs, width)? {
                for (left, right) in fields {
                    self.equalities(left, right, depth + 1, out)?;
                }
                return Ok(());
            }
        }
        let mut low = 0;
        while low < width {
            let high = low.saturating_add(SLICE - 1).min(width - 1);
            let slice = Slice { high, low };
            out.push((self.piece(lhs, slice, 0)?, self.piece(rhs, slice, 0)?));
            low = high + 1;
        }
        Ok(())
    }

    fn matching_fields(
        &self,
        lhs: TermId,
        rhs: TermId,
        width: u32,
    ) -> Result<Option<[(TermId, TermId); 2]>, Error> {
        let (TermData::App(Symbol::Named(a), left), TermData::App(Symbol::Named(b), right)) =
            (self.terms.get(lhs), self.terms.get(rhs))
        else {
            return Ok(None);
        };
        let ([al, ar], [bl, br], "concat", "concat") =
            (left.as_slice(), right.as_slice(), a.as_str(), b.as_str())
        else {
            return Ok(None);
        };
        let (alw, arw, blw, brw) = (
            self.width(*al)?,
            self.width(*ar)?,
            self.width(*bl)?,
            self.width(*br)?,
        );
        if alw.checked_add(arw) != Some(width) || blw.checked_add(brw) != Some(width) {
            return Err(Error::Unsupported(
                "wide concat operand widths do not match its sort".into(),
            ));
        }
        Ok((arw == brw).then_some([(*ar, *br), (*al, *bl)]))
    }

    fn width(&self, term: TermId) -> Result<u32, Error> {
        if self.terms.entry_stamp(term).is_none() {
            return Err(Error::Unsupported(
                "wide slice term is outside the live term store".into(),
            ));
        }
        match self.terms.sort(term) {
            Sort::BitVec(sort) if sort.width > 0 && sort.width <= MAX_WIDE_WIDTH => Ok(sort.width),
            _ => Err(Error::Unsupported(format!(
                "wide slice requires a word in 1..={MAX_WIDE_WIDTH}"
            ))),
        }
    }

    fn keep(&mut self, piece: Piece) -> Result<Piece, Error> {
        (self.poll)().map_err(Error::Resource)?;
        self.pieces = self.pieces.saturating_add(1);
        if self.pieces > MAX_PROOF_PRODUCING_CONSTRUCTED_EXPR_NODES {
            return Err(Error::Resource(
                "wide slice planning exceeds the construction-node bound".into(),
            ));
        }
        Ok(piece)
    }

    fn piece(&mut self, term: TermId, slice: Slice, depth: usize) -> Result<Piece, Error> {
        (self.poll)().map_err(Error::Resource)?;
        // The old concat-only planner already allowed a decreasing-width
        // path this deep. Arithmetic must not introduce an unbounded path
        // whose width stays constant. The node and global walk caps also stay.
        if depth > MAX_WIDE_WIDTH as usize {
            return Err(Error::Resource(
                "wide slice planning exceeds its source-depth bound".into(),
            ));
        }
        let width = self.width(term)?;
        if slice.low > slice.high || slice.high >= width || slice.width() > SLICE {
            return Err(Error::Unsupported("invalid wide slice range".into()));
        }
        if width <= MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH {
            return self.keep(Piece::Narrow {
                term,
                high: slice.high,
                low: slice.low,
            });
        }
        match self.terms.get(term) {
            TermData::Const(Constant::BitVec {
                value,
                width: declared,
            }) => {
                if *declared != width
                    || value.sign() == num_bigint::Sign::Minus
                    || value.bits() > u64::from(width)
                {
                    return Err(Error::Unsupported(
                        "wide constant does not match its declared sort".into(),
                    ));
                }
                // The validated source is at most 1024 bits. Retain only
                // this at-most-64-bit slice, never a wider producer word.
                let mask = num_bigint::BigInt::from((1u128 << slice.width()) - 1);
                let value = ((value >> slice.low) & mask).to_u128().ok_or_else(|| {
                    Error::Unsupported("wide constant slice does not fit its limb".into())
                })?;
                self.keep(Piece::Constant {
                    value,
                    width: slice.width(),
                })
            }
            TermData::App(Symbol::Named(name), args) => self.named(name, args, slice, depth, width),
            TermData::App(Symbol::Indexed(name, indices), args) => {
                match (name.as_str(), indices.as_slice(), args.as_slice()) {
                    ("zero_extend", [added], [inner]) => {
                        self.extension(*inner, *added, Extension::Zero, slice, depth, width)
                    }
                    ("sign_extend", [added], [inner]) => {
                        self.extension(*inner, *added, Extension::Sign, slice, depth, width)
                    }
                    _ => Err(Error::Unsupported("unsupported indexed wide word".into())),
                }
            }
            _ => Err(Error::Unsupported(
                "unsupported wide bit-vector leaf".into(),
            )),
        }
    }

    fn named(
        &mut self,
        name: &str,
        args: &[TermId],
        slice: Slice,
        depth: usize,
        width: u32,
    ) -> Result<Piece, Error> {
        let [left, right] = args else {
            return Err(Error::Unsupported(
                "wide word operator requires two operands".into(),
            ));
        };
        if name == "concat" {
            return self.concat(*left, *right, slice, depth, width);
        }
        let operation = match name {
            "bvadd" => Arithmetic::Add,
            "bvsub" => Arithmetic::Sub,
            _ => {
                return Err(Error::Unsupported(format!(
                    "unsupported wide operator {name}"
                )))
            }
        };
        if self.width(*left)? != width || self.width(*right)? != width {
            return Err(Error::Unsupported(
                "wide arithmetic operand widths differ".into(),
            ));
        }
        self.arithmetic_slice(operation, *left, *right, slice, depth, width)
    }

    fn concat(
        &mut self,
        left: TermId,
        right: TermId,
        slice: Slice,
        depth: usize,
        width: u32,
    ) -> Result<Piece, Error> {
        let right_width = self.width(right)?;
        if self.width(left)?.checked_add(right_width) != Some(width) {
            return Err(Error::Unsupported(
                "wide concat operand widths do not match its sort".into(),
            ));
        }
        if slice.high < right_width {
            return self.piece(right, slice, depth + 1);
        }
        if slice.low >= right_width {
            return self.piece(
                left,
                Slice {
                    high: slice.high - right_width,
                    low: slice.low - right_width,
                },
                depth + 1,
            );
        }
        let upper = self.piece(
            left,
            Slice {
                high: slice.high - right_width,
                low: 0,
            },
            depth + 1,
        )?;
        let lower = self.piece(
            right,
            Slice {
                high: right_width - 1,
                low: slice.low,
            },
            depth + 1,
        )?;
        self.keep(Piece::Join {
            upper: Box::new(upper),
            lower: Box::new(lower),
            lower_width: right_width - slice.low,
        })
    }

    fn padding(
        &mut self,
        inner: TermId,
        kind: Extension,
        width: u32,
        depth: usize,
    ) -> Result<Piece, Error> {
        match kind {
            Extension::Zero => self.keep(Piece::Constant { value: 0, width }),
            Extension::Sign => {
                let bit = self.width(inner)? - 1;
                let bit = self.piece(
                    inner,
                    Slice {
                        high: bit,
                        low: bit,
                    },
                    depth + 1,
                )?;
                self.keep(Piece::Splat {
                    bit: Box::new(bit),
                    width,
                })
            }
        }
    }

    fn extension(
        &mut self,
        inner: TermId,
        added: u32,
        kind: Extension,
        slice: Slice,
        depth: usize,
        width: u32,
    ) -> Result<Piece, Error> {
        let inner_width = self.width(inner)?;
        if inner_width.checked_add(added) != Some(width) {
            return Err(Error::Unsupported(
                "wide extension width does not match its sort".into(),
            ));
        }
        if slice.high < inner_width {
            return self.piece(inner, slice, depth + 1);
        }
        if slice.low >= inner_width {
            return self.padding(inner, kind, slice.width(), depth);
        }
        let upper = self.padding(inner, kind, slice.high - inner_width + 1, depth)?;
        let lower = self.piece(
            inner,
            Slice {
                high: inner_width - 1,
                low: slice.low,
            },
            depth + 1,
        )?;
        self.keep(Piece::Join {
            upper: Box::new(upper),
            lower: Box::new(lower),
            lower_width: inner_width - slice.low,
        })
    }

    /// Always use the same arithmetic limb boundaries, even if an enclosing
    /// concat requests an unaligned window. Extracting from these words lets
    /// the circuit interner share their carry chains across all windows.
    fn arithmetic_slice(
        &mut self,
        operation: Arithmetic,
        left: TermId,
        right: TermId,
        slice: Slice,
        depth: usize,
        width: u32,
    ) -> Result<Piece, Error> {
        let low = (slice.low / SLICE) * SLICE;
        let high = (low + SLICE - 1).min(width - 1);
        if slice.high > high {
            let upper = self.arithmetic_slice(
                operation,
                left,
                right,
                Slice {
                    high: slice.high,
                    low: high + 1,
                },
                depth + 1,
                width,
            )?;
            let lower = self.arithmetic_slice(
                operation,
                left,
                right,
                Slice {
                    high,
                    low: slice.low,
                },
                depth + 1,
                width,
            )?;
            return self.keep(Piece::Join {
                upper: Box::new(upper),
                lower: Box::new(lower),
                lower_width: high - slice.low + 1,
            });
        }
        let word = self.arithmetic(
            operation,
            left,
            right,
            Slice { high, low },
            Part::Value,
            depth,
        )?;
        if slice.low == low && slice.high == high {
            return Ok(word);
        }
        self.keep(Piece::Extract {
            inner: Box::new(word),
            high: slice.high - low,
            low: slice.low - low,
        })
    }

    fn arithmetic(
        &mut self,
        operation: Arithmetic,
        left: TermId,
        right: TermId,
        slice: Slice,
        part: Part,
        depth: usize,
    ) -> Result<Piece, Error> {
        (self.poll)().map_err(Error::Resource)?;
        if depth > MAX_WIDE_WIDTH as usize {
            return Err(Error::Resource(
                "wide arithmetic planning exceeds its source-depth bound".into(),
            ));
        }
        let lhs = self.piece(left, slice, depth + 1)?;
        let rhs = self.piece(right, slice, depth + 1)?;
        let carry = if slice.low == 0 {
            None
        } else {
            let prefix = Slice {
                high: slice.low - 1,
                low: slice.low.saturating_sub(SLICE),
            };
            Some(Box::new(self.arithmetic(
                operation,
                left,
                right,
                prefix,
                Part::Carry,
                depth + 1,
            )?))
        };
        self.keep(Piece::Arithmetic {
            operation,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            carry,
            width: slice.width(),
            part,
        })
    }
}
