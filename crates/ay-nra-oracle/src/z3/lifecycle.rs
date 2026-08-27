// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `z3` to preserve existing item DefPaths.

static NEXT_OWNER: AtomicU64 = AtomicU64::new(1);

fn next_owner() -> Result<u64, Z3Error> {
    NEXT_OWNER
        .fetch_update(AtomicOrdering::Relaxed, AtomicOrdering::Relaxed, |next| {
            next.checked_add(1)
        })
        .map_err(|_| Z3Error::OwnerExhausted)
}

impl Drop for Z3 {
    fn drop(&mut self) {
        // SAFETY: the context is live and no AST from it is used afterwards.
        unsafe {
            for v in self.held_vectors.borrow_mut().drain(..) {
                (self.api.ast_vector_dec_ref)(self.ctx, v);
                let _ = self.errored();
            }
            (self.api.del_context)(self.ctx);
        }
    }
}

impl Z3 {
    /// Tear down the context and stand up a fresh one, releasing every AST
    /// created so far. Called periodically by the fuzz driver so a long run
    /// does not accumulate the whole history in one context.
    pub(crate) fn recycle(&mut self) -> Result<(), Z3Error> {
        let next_generation = self
            .generation
            .checked_add(1)
            .ok_or(Z3Error::GenerationExhausted)?;
        // Build the replacement completely before invalidating the current
        // context. A failed constructor therefore leaves `self` usable.
        let replacement = create_context(&self.api)?;
        let mut release_error = None;
        // SAFETY: `self.ctx` was produced by `Z3_mk_context`; each retained
        // vector is released before the old context, and each release's error
        // code is read before another native call can overwrite it.
        unsafe {
            for v in self.held_vectors.borrow_mut().drain(..) {
                (self.api.ast_vector_dec_ref)(self.ctx, v);
                let code = (self.api.get_error_code)(self.ctx);
                if code != 0 {
                    self.record_reference_failure();
                    release_error.get_or_insert(code);
                }
            }
            (self.api.del_context)(self.ctx);
        }
        self.ctx = replacement.ctx;
        self.real = replacement.real;
        self.x_bound = replacement.x_bound;
        self.bound = replacement.bound;
        self.x_const = replacement.x_const;
        self.generation = next_generation;
        match release_error {
            Some(code) => Err(Z3Error::Api {
                operation: "Z3_ast_vector_dec_ref",
                code,
            }),
            None => Ok(()),
        }
    }

    fn record_reference_failure(&self) {
        self.reference_failures
            .set(self.reference_failures.get().saturating_add(1));
    }

    fn failed<T>(&self) -> Option<T> {
        self.record_reference_failure();
        None
    }

    fn checked_handle<T: NullableHandle>(&self, handle: T) -> Option<T> {
        if handle.is_null() {
            return self.failed();
        }
        (!self.errored()).then_some(handle)
    }

    fn checked_algebraic_value(&self, raw: RawAst, is_value: bool) -> Option<RawAst> {
        if self.errored() {
            None
        } else if is_value {
            Some(raw)
        } else {
            self.failed()
        }
    }

    fn checked_sign(&self, sign: c_int) -> Option<i32> {
        if self.errored() {
            None
        } else if (-1..=1).contains(&sign) {
            Some(sign)
        } else {
            self.failed()
        }
    }

    pub(crate) fn reference_failure_count(&self) -> u64 {
        self.reference_failures.get()
    }
}

/// Parse z3's numeral rendering (`"3"`, `"-7/2"`, `"(- 5)"`, `"1.5"`).
pub(crate) fn parse_rational(s: &str) -> Option<BigRational> {
    let t = s.trim();
    // The numeral string API normally returns plain forms, but accept the
    // parenthesized arithmetic forms used by other z3 renderers as well.
    if let Some(rest) = t.strip_prefix("(-").and_then(|s| s.strip_suffix(')')) {
        let inner = rest.trim();
        return parse_rational(inner).map(|r| -r);
    }
    if let Some(rest) = t.strip_prefix("(/").and_then(|s| s.strip_suffix(')')) {
        let mut operands = rest.split_whitespace();
        let numerator = parse_rational(operands.next()?)?;
        let denominator = parse_rational(operands.next()?)?;
        if operands.next().is_some() || denominator.is_zero() {
            return None;
        }
        return Some(numerator / denominator);
    }
    if let Some((n, d)) = t.split_once('/') {
        let num: BigInt = n.trim().parse().ok()?;
        let den: BigInt = d.trim().parse().ok()?;
        if den.is_zero() {
            return None;
        }
        return Some(BigRational::new(num, den));
    }
    if let Some((int_part, frac)) = t.split_once('.') {
        let neg = int_part.trim_start().starts_with('-');
        let ip: BigInt = int_part.trim().parse().ok()?;
        let scale = BigInt::from(10u32).pow(u32::try_from(frac.len()).ok()?);
        let fp: BigInt = if frac.is_empty() {
            BigInt::zero()
        } else {
            frac.parse().ok()?
        };
        let mag = ip.abs() * &scale + fp;
        let signed = if neg { -mag } else { mag };
        return Some(BigRational::new(signed, scale));
    }
    t.parse::<BigInt>().ok().map(BigRational::from_integer)
}

#[cfg(test)]
mod tests {
    use super::{parse_rational, Ast, AstKind};
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use std::ptr::NonNull;

    #[test]
    fn ast_owner_and_generation_validation_rejects_mismatches() {
        let ast = Ast {
            raw: NonNull::dangling(),
            owner: 7,
            generation: 11,
            kind: AstKind::AlgebraicValue,
        };
        assert!(ast.raw_for(7, 11).is_some());
        assert!(ast.raw_for(8, 11).is_none());
        assert!(ast.raw_for(7, 12).is_none());
    }

    #[test]
    fn parses_z3_numeral_renderings() {
        let r = |n: i64, d: i64| BigRational::new(BigInt::from(n), BigInt::from(d));
        assert_eq!(parse_rational("3"), Some(r(3, 1)));
        assert_eq!(parse_rational("-7/2"), Some(r(-7, 2)));
        assert_eq!(parse_rational("(- 5)"), Some(r(-5, 1)));
        assert_eq!(parse_rational("(/ 1.0 2.0)"), Some(r(1, 2)));
        assert_eq!(parse_rational("(- (/ 1.0 2.0))"), Some(r(-1, 2)));
        assert_eq!(parse_rational("1.5"), Some(r(3, 2)));
        assert_eq!(parse_rational("-1.25"), Some(r(-5, 4)));
        assert_eq!(parse_rational("(/ 1 0)"), None);
        assert_eq!(parse_rational("(/ 1 2 3)"), None);
        assert_eq!(parse_rational("nonsense"), None);
    }
}
