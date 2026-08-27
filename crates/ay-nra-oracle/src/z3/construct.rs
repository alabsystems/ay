// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `z3` to preserve existing item DefPaths.

impl Z3 {
    fn rational_raw(&self, r: &BigRational) -> Option<RawAst> {
        let s = format!("{}/{}", r.numer(), r.denom());
        let c = CString::new(s).ok()?;
        // SAFETY: `Z3_mk_numeral` with a well-formed rational literal.
        let raw = unsafe { (self.api.mk_numeral)(self.ctx, c.as_ptr(), self.real) };
        self.checked_handle(raw)
    }

    /// A rational algebraic-value AST, or `None` when libz3 rejects it.
    pub(crate) fn rational(&self, r: &BigRational) -> Option<Ast> {
        self.rational_raw(r)
            .and_then(|raw| self.wrap_ast(raw, AstKind::AlgebraicValue))
    }

    /// Build `sum_i coeffs[i] * x^i` over the *bound* variable 0, which is what
    /// `Z3_algebraic_roots` / `Z3_algebraic_eval` expect as the indeterminate.
    pub(crate) fn poly_bound(&self, coeffs: &[BigRational]) -> Option<Ast> {
        self.poly_over(coeffs, self.x_bound)
    }

    /// Build the same polynomial over the free constant `x`, which is what
    /// `Z3_polynomial_subresultants` expects.
    pub(crate) fn poly_const(&self, coeffs: &[BigRational]) -> Option<Ast> {
        self.poly_over(coeffs, self.x_const)
    }

    fn poly_over(&self, coeffs: &[BigRational], x: RawAst) -> Option<Ast> {
        if coeffs.is_empty() {
            let raw = self.rational_raw(&BigRational::zero())?;
            return self.wrap_ast(raw, AstKind::Polynomial);
        }
        let mut terms: Vec<RawAst> = Vec::with_capacity(coeffs.len());
        for (i, c) in coeffs.iter().enumerate() {
            if c.is_zero() {
                continue;
            }
            let coeff = self.rational_raw(c)?;
            if i == 0 {
                terms.push(coeff);
                continue;
            }
            // x^i as an explicit product; avoids any `^` interpretation subtlety.
            let mut factors: Vec<RawAst> = Vec::with_capacity(i + 1);
            factors.push(coeff);
            for _ in 0..i {
                factors.push(x);
            }
            // SAFETY: `Z3_mk_mul` over a non-empty array of real-sorted ASTs.
            let term = unsafe {
                (self.api.mk_mul)(
                    self.ctx,
                    u32::try_from(factors.len()).expect("term arity fits in u32"),
                    factors.as_ptr(),
                )
            };
            let term = self.checked_handle(term)?;
            terms.push(term);
        }
        if terms.is_empty() {
            let raw = self.rational_raw(&BigRational::zero())?;
            return self.wrap_ast(raw, AstKind::Polynomial);
        }
        if terms.len() == 1 {
            return self.wrap_ast(terms[0], AstKind::Polynomial);
        }
        // SAFETY: `Z3_mk_add` over a non-empty array of real-sorted ASTs.
        let raw = unsafe {
            (self.api.mk_add)(
                self.ctx,
                u32::try_from(terms.len()).expect("sum arity fits in u32"),
                terms.as_ptr(),
            )
        };
        let raw = self.checked_handle(raw)?;
        self.wrap_ast(raw, AstKind::Polynomial)
    }

    /// Real roots of a univariate polynomial, ascending. `None` when z3 raised
    /// an error.
    pub(crate) fn roots(&self, coeffs: &[BigRational]) -> Option<Vec<Ast>> {
        let p = self.poly_bound(coeffs)?;
        let p = self.polynomial_raw(p)?;
        // SAFETY: `Z3_algebraic_roots` with n = 0, i.e. the polynomial is
        // univariate in bound variable 0.
        let vec = unsafe { (self.api.algebraic_roots)(self.ctx, p, 0, std::ptr::null()) };
        let vec = self.checked_handle(vec)?;
        let out = self.drain_vector(vec, AstKind::AlgebraicValue)?;
        self.sort_values(out)
    }

    /// Sign of `coeffs(alpha)` where `alpha` is an algebraic value AST.
    /// `None` when z3 raised an error.
    pub(crate) fn eval_sign(&self, coeffs: &[BigRational], alpha: Ast) -> Option<i32> {
        let p = self.poly_bound(coeffs)?;
        let p = self.polynomial_raw(p)?;
        let args = [self.algebraic_raw(alpha)?];
        // SAFETY: `Z3_algebraic_eval` with n = 1 binds variable 0 to `alpha`.
        let s = unsafe { (self.api.algebraic_eval)(self.ctx, p, 1, args.as_ptr()) };
        self.checked_sign(s)
    }

    /// Build a MULTIVARIATE polynomial over the bound variables `x_0, x_1, ...`
    /// from `(exponent vector, coefficient)` terms.
    ///
    /// The exponent vector is indexed by variable; entries past its end are
    /// zero. `None` when a term mentions a variable at or past
    /// [`MAX_MV_VARS`].
    pub(crate) fn mpoly_bound(&self, terms: &[(Vec<u32>, BigRational)]) -> Option<Ast> {
        let mut sum: Vec<RawAst> = Vec::with_capacity(terms.len());
        for (exps, c) in terms {
            if c.is_zero() {
                continue;
            }
            if exps.len() > self.bound.len() {
                return None;
            }
            let mut factors: Vec<RawAst> = vec![self.rational_raw(c)?];
            for (v, &e) in exps.iter().enumerate() {
                for _ in 0..e {
                    factors.push(self.bound[v]);
                }
            }
            if factors.len() == 1 {
                sum.push(factors[0]);
                continue;
            }
            // SAFETY: `Z3_mk_mul` over a non-empty array of real-sorted ASTs.
            let term = unsafe {
                (self.api.mk_mul)(
                    self.ctx,
                    u32::try_from(factors.len()).expect("term arity fits in u32"),
                    factors.as_ptr(),
                )
            };
            let term = self.checked_handle(term)?;
            sum.push(term);
        }
        if sum.is_empty() {
            let raw = self.rational_raw(&BigRational::zero())?;
            return self.wrap_ast(raw, AstKind::Polynomial);
        }
        if sum.len() == 1 {
            return self.wrap_ast(sum[0], AstKind::Polynomial);
        }
        // SAFETY: `Z3_mk_add` over a non-empty array of real-sorted ASTs.
        let raw = unsafe {
            (self.api.mk_add)(
                self.ctx,
                u32::try_from(sum.len()).expect("sum arity fits in u32"),
                sum.as_ptr(),
            )
        };
        let raw = self.checked_handle(raw)?;
        self.wrap_ast(raw, AstKind::Polynomial)
    }

    /// `Z3_algebraic_roots(p, n, a)` — the roots of `p(a_0, .., a_{n-1}, x_n)`
    /// in its LAST variable, ascending. This is z3's
    /// `algebraic_numbers::manager::isolate_roots(p, x2v, roots)` verbatim
    /// (`api_algebraic.cpp:352`), i.e. exactly the entry point
    /// `ay_nra::oracle_api::isolate_roots_at` reimplements.
    ///
    /// `None` when z3 raised an error (an out-of-fragment polynomial, a
    /// timeout, or its own `algebraic_exception` on a vanishing resultant).
    pub(crate) fn roots_at(&self, p: Ast, values: &[Ast]) -> Option<Vec<Ast>> {
        let p = self.polynomial_raw(p)?;
        let values: Vec<RawAst> = values
            .iter()
            .map(|value| self.algebraic_raw(*value))
            .collect::<Option<_>>()?;
        // SAFETY: `p` is an AST of this context over bound variables
        // `0 ..= values.len()`, and every `values[i]` is an algebraic value.
        let vec = unsafe {
            (self.api.algebraic_roots)(
                self.ctx,
                p,
                u32::try_from(values.len()).expect("arity fits in u32"),
                values.as_ptr(),
            )
        };
        let vec = self.checked_handle(vec)?;
        let out = self.drain_vector(vec, AstKind::AlgebraicValue)?;
        self.sort_values(out)
    }

    /// `Z3_algebraic_eval(p, n, a)` — the sign of `p(a_0, .., a_{n-1})`, i.e.
    /// z3's `eval_sign_at`. Every variable of `p` must be assigned.
    pub(crate) fn eval_sign_at(&self, p: Ast, values: &[Ast]) -> Option<i32> {
        let p = self.polynomial_raw(p)?;
        let values: Vec<RawAst> = values
            .iter()
            .map(|value| self.algebraic_raw(*value))
            .collect::<Option<_>>()?;
        // SAFETY: `p` is an AST of this context over bound variables
        // `0 .. values.len()`, and every `values[i]` is an algebraic value.
        let s = unsafe {
            (self.api.algebraic_eval)(
                self.ctx,
                p,
                u32::try_from(values.len()).expect("arity fits in u32"),
                values.as_ptr(),
            )
        };
        self.checked_sign(s)
    }

    /// The nonzero subresultants of `f` and `g` with respect to `x`, as ASTs.
    pub(crate) fn subresultants(&self, f: &[BigRational], g: &[BigRational]) -> Option<Vec<Ast>> {
        let fp = self.polynomial_raw(self.poly_const(f)?)?;
        let gp = self.polynomial_raw(self.poly_const(g)?)?;
        // SAFETY: `Z3_polynomial_subresultants` over two arithmetic terms and a
        // free real constant.
        let vec = unsafe { (self.api.polynomial_subresultants)(self.ctx, fp, gp, self.x_const) };
        let vec = self.checked_handle(vec)?;
        self.drain_vector(vec, AstKind::Term)
    }

    /// Read out an `ast_vector`'s elements and KEEP the vector alive.
    ///
    /// See [`Z3::held_vectors`] for why the reference is never dropped here:
    /// the vector owns the algebraic-numeral ASTs it returned, and releasing
    /// it repoints every handle the caller is still holding.
    fn drain_vector(&self, vec: RawAstVector, kind: AstKind) -> Option<Vec<Ast>> {
        // SAFETY: `vec` is a live `Z3_ast_vector` from this context. The
        // reference taken here is released only at `recycle` / `drop`.
        unsafe { (self.api.ast_vector_inc_ref)(self.ctx, vec) };
        if self.errored() {
            return None;
        }
        self.held_vectors.borrow_mut().push(vec);
        // SAFETY: the successfully retained vector remains live in this
        // context, and each access is checked before another Z3 call can
        // overwrite the context's last error code.
        let n = unsafe { (self.api.ast_vector_size)(self.ctx, vec) };
        if self.errored() {
            return None;
        }
        let mut out = Vec::with_capacity(n as usize);
        for i in 0..n {
            // SAFETY: `i < n` for the live retained vector.
            let ast = unsafe { (self.api.ast_vector_get)(self.ctx, vec, i) };
            if self.errored() {
                return None;
            }
            out.push(self.wrap_ast(ast, kind)?);
        }
        Some(out)
    }

    /// Sort algebraic values ascending using z3's own exact comparison. z3
    /// already returns roots in order; sorting is defensive, and it means the
    /// oracle never reports a divergence that is really an ordering assumption.
    fn sort_values(&self, mut values: Vec<Ast>) -> Option<Vec<Ast>> {
        // Z3 already returns roots in order. A small fallible insertion sort
        // retains the defensive check without mapping a failed comparison to
        // fabricated equality.
        for i in 1..values.len() {
            let mut j = i;
            while j > 0 {
                if !self.lt(values[j], values[j - 1])? {
                    break;
                }
                values.swap(j, j - 1);
                j -= 1;
            }
        }
        Some(values)
    }
}
