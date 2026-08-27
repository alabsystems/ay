// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `z3` to preserve existing item DefPaths.

impl Z3 {
    /// `a < b` on current algebraic values.
    ///
    /// Stale, foreign, wrong-kind, or native-rejected handles return `None`.
    pub(crate) fn lt(&self, a: Ast, b: Ast) -> Option<bool> {
        let a = self.algebraic_raw(a)?;
        let b = self.algebraic_raw(b)?;
        // SAFETY: both operands are algebraic values from this context.
        let result = unsafe { (self.api.algebraic_lt)(self.ctx, a, b) };
        (!self.errored()).then_some(result)
    }

    /// `a > b` on current algebraic values.
    ///
    /// Stale, foreign, wrong-kind, or native-rejected handles return `None`.
    pub(crate) fn gt(&self, a: Ast, b: Ast) -> Option<bool> {
        let a = self.algebraic_raw(a)?;
        let b = self.algebraic_raw(b)?;
        // SAFETY: both operands are algebraic values from this context.
        let result = unsafe { (self.api.algebraic_gt)(self.ctx, a, b) };
        (!self.errored()).then_some(result)
    }

    /// `a == b` on current algebraic values.
    ///
    /// Stale, foreign, wrong-kind, or native-rejected handles return `None`.
    pub(crate) fn eq(&self, a: Ast, b: Ast) -> Option<bool> {
        let a = self.algebraic_raw(a)?;
        let b = self.algebraic_raw(b)?;
        // SAFETY: both operands are algebraic values from this context.
        let result = unsafe { (self.api.algebraic_eq)(self.ctx, a, b) };
        (!self.errored()).then_some(result)
    }

    /// Exact sum of two algebraic values.
    pub(crate) fn add(&self, a: Ast, b: Ast) -> Option<Ast> {
        let a = self.algebraic_raw(a)?;
        let b = self.algebraic_raw(b)?;
        // SAFETY: both operands are algebraic values from this context.
        let raw = unsafe { (self.api.algebraic_add)(self.ctx, a, b) };
        if self.errored() {
            return None;
        }
        let ast = self.wrap_ast(raw, AstKind::AlgebraicValue)?;
        self.algebraic_raw(ast).map(|_| ast)
    }

    /// Exact product of two algebraic values.
    pub(crate) fn mul(&self, a: Ast, b: Ast) -> Option<Ast> {
        let a = self.algebraic_raw(a)?;
        let b = self.algebraic_raw(b)?;
        // SAFETY: both operands are algebraic values from this context.
        let raw = unsafe { (self.api.algebraic_mul)(self.ctx, a, b) };
        if self.errored() {
            return None;
        }
        let ast = self.wrap_ast(raw, AstKind::AlgebraicValue)?;
        self.algebraic_raw(ast).map(|_| ast)
    }

    /// Root index z3 assigns to an IRRATIONAL algebraic value.
    ///
    /// Returns `None` for rational, stale, foreign, wrong-kind, or rejected
    /// handles. The irrationality check is essential because calling
    /// `Z3_algebraic_get_i` on a rational lets a C++ exception escape the C ABI.
    pub(crate) fn root_index(&self, a: Ast) -> Option<u32> {
        let raw = self.algebraic_raw(a)?;
        // SAFETY: `raw` is a current algebraic value. Although z3 documents
        // `Z3_algebraic_is_value` as `Z3_algebraic_get_i`'s precondition, its
        // implementation crashes on rational values; this stronger predicate
        // distinguishes irrational algebraic numbers from rational numerals.
        let irrational = unsafe { (self.api.is_algebraic_number)(self.ctx, raw) };
        if self.errored() || !irrational {
            return None;
        }
        // SAFETY: the stronger implementation guard above established that
        // this live-context value is an irrational algebraic number.
        let index = unsafe { (self.api.algebraic_get_i)(self.ctx, raw) };
        (!self.errored()).then_some(index)
    }

    /// Coefficients of z3's defining polynomial for an algebraic value, as
    /// printed rationals (low-to-high, per `Z3_algebraic_get_poly`).
    pub(crate) fn defining_poly(&self, a: Ast) -> Option<Vec<BigRational>> {
        let a = self.algebraic_raw(a)?;
        // SAFETY: `a` is an algebraic value from this context.
        let vec = unsafe { (self.api.algebraic_get_poly)(self.ctx, a) };
        let vec = self.checked_handle(vec)?;
        let asts = self.drain_vector(vec, AstKind::Term)?;
        asts.iter().map(|a| self.numeral_value(*a)).collect()
    }

    /// Decode a numeral AST into an exact rational; `None` when the AST is not
    /// a numeral.
    pub(crate) fn numeral_value(&self, a: Ast) -> Option<BigRational> {
        let a = self.current_raw(a)?;
        // SAFETY: `a` is a current, non-null AST. This predicate makes a
        // non-numeral a clean `None` rather than violating the getter's
        // precondition or treating a diagnostic fallback as a native failure.
        let is_numeral = unsafe { (self.api.is_numeral_ast)(self.ctx, a) };
        if self.errored() || !is_numeral {
            return None;
        }
        // SAFETY: `Z3_get_numeral_string` returns a context-owned C string; we
        // copy it before any further z3 call.
        let s = unsafe {
            let p = (self.api.get_numeral_string)(self.ctx, a);
            if p.is_null() {
                self.record_reference_failure();
                return None;
            }
            if self.errored() {
                return None;
            }
            CStr::from_ptr(p).to_string_lossy().into_owned()
        };
        parse_rational(&s).or_else(|| self.failed())
    }

    /// Render an AST for reproducer dumps.
    pub(crate) fn ast_string(&self, a: Ast) -> Option<String> {
        let a = self.current_raw(a)?;
        // SAFETY: `Z3_ast_to_string` returns a context-owned C string; copied
        // immediately.
        unsafe {
            let p = (self.api.ast_to_string)(self.ctx, a);
            if p.is_null() {
                self.record_reference_failure();
                return None;
            }
            if self.errored() {
                return None;
            }
            Some(CStr::from_ptr(p).to_string_lossy().into_owned())
        }
    }

    /// Is `a` usable as an algebraic value?
    pub(crate) fn is_value(&self, a: Ast) -> Option<bool> {
        if a.kind != AstKind::AlgebraicValue {
            return None;
        }
        let raw = self.current_raw(a)?;
        // SAFETY: `raw` is a current, non-null AST created by this binding.
        let result = unsafe { (self.api.algebraic_is_value)(self.ctx, raw) };
        self.checked_algebraic_value(raw, result).map(|_| true)
    }

    /// Bracket an algebraic value between two rationals by binary search on
    /// z3's own exact comparison. Returns `(lo, hi)` with `lo < v < hi`, or the
    /// exact value twice when `v` turns out to be that rational.
    ///
    /// This is the oracle's universal comparison primitive: it converts *any*
    /// z3 real algebraic number into a rational enclosure that AY's exact
    /// comparison can be tested against, with no shared representation and no
    /// floating point anywhere.
    pub(crate) fn bracket(&self, v: Ast, steps: u32) -> Option<(BigRational, BigRational)> {
        self.algebraic_raw(v)?;
        let two = BigRational::from_integer(BigInt::from(2));
        // Expand outward from [-1, 1] until the value is strictly inside.
        let mut lo = -BigRational::one();
        let mut hi = BigRational::one();
        let mut enclosed = false;
        for expansion in 0..=256 {
            let lo_ast = self.rational(&lo)?;
            let hi_ast = self.rational(&hi)?;
            let at_lo = self.eq(v, lo_ast)?;
            if self.errored() {
                return None;
            }
            let at_hi = self.eq(v, hi_ast)?;
            if self.errored() {
                return None;
            }
            if at_lo || at_hi {
                let exact = if at_lo { lo } else { hi };
                return Some((exact.clone(), exact));
            }
            let above_lo = self.gt(v, lo_ast)?;
            if self.errored() {
                return None;
            }
            let below_hi = self.lt(v, hi_ast)?;
            if self.errored() {
                return None;
            }
            if above_lo && below_hi {
                enclosed = true;
                break;
            }
            if expansion == 256 {
                // Never return an enclosure unless exact comparison proved
                // containment. In particular, values outside +/-2^256 used
                // to fall through and receive a false bracket.
                return self.failed();
            }
            lo *= &two;
            hi *= &two;
        }
        debug_assert!(enclosed);
        for _ in 0..steps {
            let mid = (&lo + &hi) / &two;
            let mid_ast = self.rational(&mid)?;
            let at_mid = self.eq(v, mid_ast)?;
            if self.errored() {
                return None;
            }
            if at_mid {
                return Some((mid.clone(), mid));
            }
            let below_mid = self.lt(v, mid_ast)?;
            if self.errored() {
                return None;
            }
            if below_mid {
                hi = mid;
            } else {
                lo = mid;
            }
        }
        Some((lo, hi))
    }
}
