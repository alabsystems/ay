// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Runtime binding to the real libz3's algebraic-number and polynomial C API.
//!
//! Nothing is linked at build time: the dylib is `dlopen`'d with
//! `RTLD_NOW | RTLD_LOCAL` exactly as `ay-z3-parity` does, so that AY's own
//! `Z3_*` exports (`ay-ffi` ships a drop-in libz3 ABI) can never be resolved
//! by accident. The oracle is therefore *guaranteed* to be talking to the
//! reference implementation and not to AY wearing a z3 mask.
//!
//! Memory model: contexts are created with `Z3_mk_context` (no reference
//! counting), every AST lives until the context dies, and the driver recycles
//! the context every few hundred cases. That is deliberate — refcount bugs in
//! the harness would show up as z3 crashes and be mistaken for divergences.

use std::ffi::{c_void, CStr, CString};
use std::os::raw::{c_char, c_int, c_uint};
use std::path::Path;
use std::sync::atomic::{AtomicU32, Ordering as AtomicOrdering};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

#[cfg(unix)]
use libloading::os::unix::Library;
#[cfg(windows)]
use libloading::os::windows::Library;

/// Opaque `Z3_context` / `Z3_config` / `Z3_ast` / `Z3_sort` handle.
pub(crate) type Ptr = *mut c_void;

/// Error code last reported by z3's error handler (0 == `Z3_OK`).
static LAST_ERROR: AtomicU32 = AtomicU32::new(0);

unsafe extern "C" fn error_handler(_c: Ptr, e: c_uint) {
    LAST_ERROR.store(e, AtomicOrdering::SeqCst);
}

/// Clear the recorded z3 error code.
pub(crate) fn clear_error() {
    LAST_ERROR.store(0, AtomicOrdering::SeqCst);
}

macro_rules! decl_api {
    ($( $field:ident : $sym:literal : $ty:ty ),+ $(,)?) => {
        /// Raw entry points resolved out of the loaded libz3.
        #[allow(non_snake_case)]
        #[derive(Clone, Copy)]
        pub(crate) struct Api {
            $( pub(crate) $field: $ty, )+
        }

        impl Api {
            fn resolve(lib: &Library) -> Result<Self, String> {
                // SAFETY: each symbol is looked up by its documented C name and
                // transmuted to the signature published in `z3_api.h` /
                // `z3_algebraic.h` / `z3_polynomial.h`.
                unsafe {
                    $(
                        let $field: $ty = *lib
                            .get::<$ty>($sym)
                            .map_err(|e| format!("dlsym {}: {e}", ::std::str::from_utf8($sym).unwrap_or("?")))?;
                    )+
                    Ok(Self { $( $field, )+ })
                }
            }
        }
    };
}

decl_api! {
    mk_config: b"Z3_mk_config\0": unsafe extern "C" fn() -> Ptr,
    del_config: b"Z3_del_config\0": unsafe extern "C" fn(Ptr),
    set_param_value: b"Z3_set_param_value\0": unsafe extern "C" fn(Ptr, *const c_char, *const c_char),
    mk_context: b"Z3_mk_context\0": unsafe extern "C" fn(Ptr) -> Ptr,
    del_context: b"Z3_del_context\0": unsafe extern "C" fn(Ptr),
    set_error_handler: b"Z3_set_error_handler\0": unsafe extern "C" fn(Ptr, unsafe extern "C" fn(Ptr, c_uint)),
    get_error_code: b"Z3_get_error_code\0": unsafe extern "C" fn(Ptr) -> c_uint,
    get_full_version: b"Z3_get_full_version\0": unsafe extern "C" fn() -> *const c_char,

    mk_real_sort: b"Z3_mk_real_sort\0": unsafe extern "C" fn(Ptr) -> Ptr,
    mk_numeral: b"Z3_mk_numeral\0": unsafe extern "C" fn(Ptr, *const c_char, Ptr) -> Ptr,
    mk_bound: b"Z3_mk_bound\0": unsafe extern "C" fn(Ptr, c_uint, Ptr) -> Ptr,
    mk_string_symbol: b"Z3_mk_string_symbol\0": unsafe extern "C" fn(Ptr, *const c_char) -> Ptr,
    mk_const: b"Z3_mk_const\0": unsafe extern "C" fn(Ptr, Ptr, Ptr) -> Ptr,
    mk_add: b"Z3_mk_add\0": unsafe extern "C" fn(Ptr, c_uint, *const Ptr) -> Ptr,
    mk_mul: b"Z3_mk_mul\0": unsafe extern "C" fn(Ptr, c_uint, *const Ptr) -> Ptr,
    get_numeral_string: b"Z3_get_numeral_string\0": unsafe extern "C" fn(Ptr, Ptr) -> *const c_char,
    ast_to_string: b"Z3_ast_to_string\0": unsafe extern "C" fn(Ptr, Ptr) -> *const c_char,

    ast_vector_size: b"Z3_ast_vector_size\0": unsafe extern "C" fn(Ptr, Ptr) -> c_uint,
    ast_vector_get: b"Z3_ast_vector_get\0": unsafe extern "C" fn(Ptr, Ptr, c_uint) -> Ptr,
    ast_vector_inc_ref: b"Z3_ast_vector_inc_ref\0": unsafe extern "C" fn(Ptr, Ptr),
    ast_vector_dec_ref: b"Z3_ast_vector_dec_ref\0": unsafe extern "C" fn(Ptr, Ptr),

    algebraic_is_value: b"Z3_algebraic_is_value\0": unsafe extern "C" fn(Ptr, Ptr) -> bool,
    algebraic_add: b"Z3_algebraic_add\0": unsafe extern "C" fn(Ptr, Ptr, Ptr) -> Ptr,
    algebraic_mul: b"Z3_algebraic_mul\0": unsafe extern "C" fn(Ptr, Ptr, Ptr) -> Ptr,
    algebraic_lt: b"Z3_algebraic_lt\0": unsafe extern "C" fn(Ptr, Ptr, Ptr) -> bool,
    algebraic_gt: b"Z3_algebraic_gt\0": unsafe extern "C" fn(Ptr, Ptr, Ptr) -> bool,
    algebraic_eq: b"Z3_algebraic_eq\0": unsafe extern "C" fn(Ptr, Ptr, Ptr) -> bool,
    algebraic_roots: b"Z3_algebraic_roots\0": unsafe extern "C" fn(Ptr, Ptr, c_uint, *const Ptr) -> Ptr,
    algebraic_eval: b"Z3_algebraic_eval\0": unsafe extern "C" fn(Ptr, Ptr, c_uint, *const Ptr) -> c_int,
    algebraic_get_i: b"Z3_algebraic_get_i\0": unsafe extern "C" fn(Ptr, Ptr) -> c_uint,
    algebraic_get_poly: b"Z3_algebraic_get_poly\0": unsafe extern "C" fn(Ptr, Ptr) -> Ptr,

    polynomial_subresultants: b"Z3_polynomial_subresultants\0": unsafe extern "C" fn(Ptr, Ptr, Ptr, Ptr) -> Ptr,
}

/// How many bound variables the multivariate builders can address.
///
/// The multivariate checks never draw more than a couple of assigned
/// coordinates plus the unknown; this is the hard ceiling, and
/// [`Z3::mpoly_bound`] refuses rather than reaching past it.
pub(crate) const MAX_MV_VARS: u32 = 6;

/// An open libz3 plus a live context.
pub(crate) struct Z3 {
    // Kept alive for the lifetime of every function pointer in `api`.
    _lib: Library,
    api: Api,
    ctx: Ptr,
    real: Ptr,
    /// Bound variable 0 of real sort — the polynomial indeterminate.
    x_bound: Ptr,
    /// Bound variables `0 .. MAX_MV_VARS` of real sort, for the MULTIVARIATE
    /// entry points. `Z3_algebraic_roots(c, p, n, a)` reads `p` as a
    /// polynomial in `x_0 .. x_n`, assigns `x_0 .. x_{n-1}` from `a`, and
    /// solves for `x_n`, so a check of `isolate_roots` at a sample point has
    /// to be able to build a polynomial over several bound variables at once.
    bound: Vec<Ptr>,
    /// A real constant named `x`, for `Z3_polynomial_subresultants`.
    x_const: Ptr,
    /// Every `Z3_ast_vector` this context has produced, held with a live
    /// reference until the context is torn down.
    ///
    /// This is NOT tidiness — it is a correctness requirement, and getting it
    /// wrong is the single most dangerous failure mode an oracle can have,
    /// because it manufactures divergences that look exactly like real ones.
    ///
    /// `Z3_algebraic_roots` (`src/api/api_algebraic.cpp:379`) allocates a
    /// `Z3_ast_vector_ref`, fills it with `arith_util::mk_numeral(am, root)`
    /// applications, and returns it WITHOUT calling `save_ast_trail` on the
    /// elements — unlike `Z3_algebraic_add` and friends, which do
    /// (`api_algebraic.cpp:157`). The vector is therefore the only owner of
    /// those ASTs. Release it and the irrational-numeral slots inside the
    /// `arith_decl_plugin` are freed and REUSED by the next call, so every
    /// previously returned `Z3_ast` silently starts denoting a different real
    /// number.
    ///
    /// That is not hypothetical: dropping the vectors made this oracle report
    /// ~15% of `square-free` and `gcd` cases as AY divergences, all of them
    /// fictional. Holding the vectors makes them vanish.
    held_vectors: std::cell::RefCell<Vec<Ptr>>,
    /// libz3's self-reported version string.
    pub(crate) version: String,
}

impl Z3 {
    /// `dlopen` the given libz3 and stand up a fresh context.
    pub(crate) fn open(path: &Path) -> Result<Self, String> {
        // SAFETY: dlopen of a caller-supplied path; the library is treated as
        // an opaque Z3-ABI provider. RTLD_LOCAL keeps its `Z3_*` exports out of
        // the global namespace so they cannot collide with AY's own.
        #[cfg(unix)]
        let lib = unsafe {
            Library::open(Some(path), libc::RTLD_NOW | libc::RTLD_LOCAL)
                .map_err(|e| format!("dlopen {}: {e}", path.display()))?
        };
        // SAFETY: loading the user-named z3 shared library; `Library::new` is
        // unsafe because arbitrary initializers run on load — accepted for
        // this dev-only differential oracle, same contract as the unix arm.
        #[cfg(windows)]
        let lib = unsafe {
            Library::new(path).map_err(|e| format!("LoadLibrary {}: {e}", path.display()))?
        };

        let api = Api::resolve(&lib)?;
        // SAFETY: all calls below use the signatures declared in `decl_api!`.
        let (ctx, real, x_bound, bound, x_const, version) = unsafe {
            let version = CStr::from_ptr((api.get_full_version)())
                .to_string_lossy()
                .into_owned();
            let cfg = (api.mk_config)();
            // Deterministic, no proof/model overhead.
            let k = CString::new("model").unwrap();
            let v = CString::new("false").unwrap();
            (api.set_param_value)(cfg, k.as_ptr(), v.as_ptr());
            let ctx = (api.mk_context)(cfg);
            (api.del_config)(cfg);
            (api.set_error_handler)(ctx, error_handler);
            let real = (api.mk_real_sort)(ctx);
            let x_bound = (api.mk_bound)(ctx, 0, real);
            let bound: Vec<Ptr> = (0..MAX_MV_VARS)
                .map(|i| (api.mk_bound)(ctx, i, real))
                .collect();
            let name = CString::new("x").unwrap();
            let sym = (api.mk_string_symbol)(ctx, name.as_ptr());
            let x_const = (api.mk_const)(ctx, sym, real);
            (ctx, real, x_bound, bound, x_const, version)
        };
        clear_error();
        Ok(Self {
            _lib: lib,
            api,
            ctx,
            real,
            x_bound,
            bound,
            x_const,
            held_vectors: std::cell::RefCell::new(Vec::new()),
            version,
        })
    }

    /// Tear down the context and stand up a fresh one, releasing every AST
    /// created so far. Called periodically by the fuzz driver so a long run
    /// does not accumulate the whole history in one context.
    pub(crate) fn recycle(&mut self) {
        // SAFETY: `self.ctx` was produced by `Z3_mk_context` and no AST from it
        // is used after this point. The held ast_vectors are released first so
        // the context tears down with a zero object count.
        unsafe {
            for v in self.held_vectors.borrow_mut().drain(..) {
                (self.api.ast_vector_dec_ref)(self.ctx, v);
            }
            (self.api.del_context)(self.ctx);
            let cfg = (self.api.mk_config)();
            let ctx = (self.api.mk_context)(cfg);
            (self.api.del_config)(cfg);
            (self.api.set_error_handler)(ctx, error_handler);
            self.ctx = ctx;
            self.real = (self.api.mk_real_sort)(ctx);
            self.x_bound = (self.api.mk_bound)(ctx, 0, self.real);
            self.bound = (0..MAX_MV_VARS)
                .map(|i| (self.api.mk_bound)(ctx, i, self.real))
                .collect();
            let name = CString::new("x").unwrap();
            let sym = (self.api.mk_string_symbol)(ctx, name.as_ptr());
            self.x_const = (self.api.mk_const)(ctx, sym, self.real);
        }
        clear_error();
    }

    /// True when z3 has flagged an error since the last [`clear_error`].
    pub(crate) fn errored(&self) -> bool {
        // SAFETY: reading the error code of a live context.
        let code = unsafe { (self.api.get_error_code)(self.ctx) };
        code != 0 || LAST_ERROR.load(AtomicOrdering::SeqCst) != 0
    }

    /// A rational numeral AST.
    pub(crate) fn rational(&self, r: &BigRational) -> Ptr {
        let s = format!("{}/{}", r.numer(), r.denom());
        let c = CString::new(s).expect("rational string has no interior NUL");
        // SAFETY: `Z3_mk_numeral` with a well-formed rational literal.
        unsafe { (self.api.mk_numeral)(self.ctx, c.as_ptr(), self.real) }
    }

    /// Build `sum_i coeffs[i] * x^i` over the *bound* variable 0, which is what
    /// `Z3_algebraic_roots` / `Z3_algebraic_eval` expect as the indeterminate.
    pub(crate) fn poly_bound(&self, coeffs: &[BigRational]) -> Ptr {
        self.poly_over(coeffs, self.x_bound)
    }

    /// Build the same polynomial over the free constant `x`, which is what
    /// `Z3_polynomial_subresultants` expects.
    pub(crate) fn poly_const(&self, coeffs: &[BigRational]) -> Ptr {
        self.poly_over(coeffs, self.x_const)
    }

    fn poly_over(&self, coeffs: &[BigRational], x: Ptr) -> Ptr {
        if coeffs.is_empty() {
            return self.rational(&BigRational::zero());
        }
        let mut terms: Vec<Ptr> = Vec::with_capacity(coeffs.len());
        for (i, c) in coeffs.iter().enumerate() {
            if c.is_zero() {
                continue;
            }
            let coeff = self.rational(c);
            if i == 0 {
                terms.push(coeff);
                continue;
            }
            // x^i as an explicit product; avoids any `^` interpretation subtlety.
            let mut factors: Vec<Ptr> = Vec::with_capacity(i + 1);
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
            terms.push(term);
        }
        if terms.is_empty() {
            return self.rational(&BigRational::zero());
        }
        if terms.len() == 1 {
            return terms[0];
        }
        // SAFETY: `Z3_mk_add` over a non-empty array of real-sorted ASTs.
        unsafe {
            (self.api.mk_add)(
                self.ctx,
                u32::try_from(terms.len()).expect("sum arity fits in u32"),
                terms.as_ptr(),
            )
        }
    }

    /// Real roots of a univariate polynomial, ascending. `None` when z3 raised
    /// an error.
    pub(crate) fn roots(&self, coeffs: &[BigRational]) -> Option<Vec<Ptr>> {
        clear_error();
        let p = self.poly_bound(coeffs);
        // SAFETY: `Z3_algebraic_roots` with n = 0, i.e. the polynomial is
        // univariate in bound variable 0.
        let vec = unsafe { (self.api.algebraic_roots)(self.ctx, p, 0, std::ptr::null()) };
        if vec.is_null() || self.errored() {
            return None;
        }
        let out = self.drain_vector(vec);
        Some(self.sort_values(out))
    }

    /// Sign of `coeffs(alpha)` where `alpha` is an algebraic value AST.
    /// `None` when z3 raised an error.
    pub(crate) fn eval_sign(&self, coeffs: &[BigRational], alpha: Ptr) -> Option<i32> {
        clear_error();
        let p = self.poly_bound(coeffs);
        let args = [alpha];
        // SAFETY: `Z3_algebraic_eval` with n = 1 binds variable 0 to `alpha`.
        let s = unsafe { (self.api.algebraic_eval)(self.ctx, p, 1, args.as_ptr()) };
        if self.errored() {
            return None;
        }
        Some(s)
    }

    /// Build a MULTIVARIATE polynomial over the bound variables `x_0, x_1, ...`
    /// from `(exponent vector, coefficient)` terms.
    ///
    /// The exponent vector is indexed by variable; entries past its end are
    /// zero. `None` when a term mentions a variable at or past
    /// [`MAX_MV_VARS`].
    pub(crate) fn mpoly_bound(&self, terms: &[(Vec<u32>, BigRational)]) -> Option<Ptr> {
        let mut sum: Vec<Ptr> = Vec::with_capacity(terms.len());
        for (exps, c) in terms {
            if c.is_zero() {
                continue;
            }
            if exps.len() > self.bound.len() {
                return None;
            }
            let mut factors: Vec<Ptr> = vec![self.rational(c)];
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
            sum.push(unsafe {
                (self.api.mk_mul)(
                    self.ctx,
                    u32::try_from(factors.len()).expect("term arity fits in u32"),
                    factors.as_ptr(),
                )
            });
        }
        if sum.is_empty() {
            return Some(self.rational(&BigRational::zero()));
        }
        if sum.len() == 1 {
            return Some(sum[0]);
        }
        // SAFETY: `Z3_mk_add` over a non-empty array of real-sorted ASTs.
        Some(unsafe {
            (self.api.mk_add)(
                self.ctx,
                u32::try_from(sum.len()).expect("sum arity fits in u32"),
                sum.as_ptr(),
            )
        })
    }

    /// `Z3_algebraic_roots(p, n, a)` — the roots of `p(a_0, .., a_{n-1}, x_n)`
    /// in its LAST variable, ascending. This is z3's
    /// `algebraic_numbers::manager::isolate_roots(p, x2v, roots)` verbatim
    /// (`api_algebraic.cpp:352`), i.e. exactly the entry point
    /// `ay_nra::oracle_api::isolate_roots_at` reimplements.
    ///
    /// `None` when z3 raised an error (an out-of-fragment polynomial, a
    /// timeout, or its own `algebraic_exception` on a vanishing resultant).
    pub(crate) fn roots_at(&self, p: Ptr, values: &[Ptr]) -> Option<Vec<Ptr>> {
        clear_error();
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
        if vec.is_null() || self.errored() {
            return None;
        }
        let out = self.drain_vector(vec);
        Some(self.sort_values(out))
    }

    /// `Z3_algebraic_eval(p, n, a)` — the sign of `p(a_0, .., a_{n-1})`, i.e.
    /// z3's `eval_sign_at`. Every variable of `p` must be assigned.
    pub(crate) fn eval_sign_at(&self, p: Ptr, values: &[Ptr]) -> Option<i32> {
        clear_error();
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
        if self.errored() {
            return None;
        }
        Some(s)
    }

    /// The nonzero subresultants of `f` and `g` with respect to `x`, as ASTs.
    pub(crate) fn subresultants(&self, f: &[BigRational], g: &[BigRational]) -> Option<Vec<Ptr>> {
        clear_error();
        let fp = self.poly_const(f);
        let gp = self.poly_const(g);
        // SAFETY: `Z3_polynomial_subresultants` over two arithmetic terms and a
        // free real constant.
        let vec = unsafe { (self.api.polynomial_subresultants)(self.ctx, fp, gp, self.x_const) };
        if vec.is_null() || self.errored() {
            return None;
        }
        Some(self.drain_vector(vec))
    }

    /// Read out an `ast_vector`'s elements and KEEP the vector alive.
    ///
    /// See [`Z3::held_vectors`] for why the reference is never dropped here:
    /// the vector owns the algebraic-numeral ASTs it returned, and releasing
    /// it repoints every handle the caller is still holding.
    fn drain_vector(&self, vec: Ptr) -> Vec<Ptr> {
        // SAFETY: `vec` is a live `Z3_ast_vector` from this context. The
        // reference taken here is released only at `recycle` / `drop`.
        unsafe {
            (self.api.ast_vector_inc_ref)(self.ctx, vec);
            let n = (self.api.ast_vector_size)(self.ctx, vec);
            let mut out = Vec::with_capacity(n as usize);
            for i in 0..n {
                out.push((self.api.ast_vector_get)(self.ctx, vec, i));
            }
            self.held_vectors.borrow_mut().push(vec);
            out
        }
    }

    /// Sort algebraic values ascending using z3's own exact comparison. z3
    /// already returns roots in order; sorting is defensive, and it means the
    /// oracle never reports a divergence that is really an ordering assumption.
    fn sort_values(&self, mut v: Vec<Ptr>) -> Vec<Ptr> {
        v.sort_by(|a, b| {
            if self.lt(*a, *b) {
                std::cmp::Ordering::Less
            } else if self.lt(*b, *a) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        });
        v
    }

    /// `a < b` on algebraic values.
    pub(crate) fn lt(&self, a: Ptr, b: Ptr) -> bool {
        // SAFETY: both operands are algebraic values from this context.
        unsafe { (self.api.algebraic_lt)(self.ctx, a, b) }
    }

    /// `a > b` on algebraic values.
    pub(crate) fn gt(&self, a: Ptr, b: Ptr) -> bool {
        // SAFETY: both operands are algebraic values from this context.
        unsafe { (self.api.algebraic_gt)(self.ctx, a, b) }
    }

    /// `a == b` on algebraic values.
    pub(crate) fn eq(&self, a: Ptr, b: Ptr) -> bool {
        // SAFETY: both operands are algebraic values from this context.
        unsafe { (self.api.algebraic_eq)(self.ctx, a, b) }
    }

    /// Exact sum of two algebraic values.
    pub(crate) fn add(&self, a: Ptr, b: Ptr) -> Ptr {
        // SAFETY: both operands are algebraic values from this context.
        unsafe { (self.api.algebraic_add)(self.ctx, a, b) }
    }

    /// Exact product of two algebraic values.
    pub(crate) fn mul(&self, a: Ptr, b: Ptr) -> Ptr {
        // SAFETY: both operands are algebraic values from this context.
        unsafe { (self.api.algebraic_mul)(self.ctx, a, b) }
    }

    /// Root index z3 assigns to an IRRATIONAL algebraic value.
    ///
    /// Precondition: `a` must be irrational. `Z3_algebraic_get_i` reaches
    /// `get_irrational` (`src/api/api_algebraic.cpp:446`) with no rational
    /// guard, and on a rational numeral the C++ exception escapes the `extern
    /// "C"` frame and aborts the process with "Rust cannot catch foreign
    /// exceptions" — observed while triaging this oracle. Callers screen with
    /// [`Z3::numeral_value`] first; only `probe` uses it, on `sqrt(2)`.
    pub(crate) fn root_index(&self, a: Ptr) -> u32 {
        // SAFETY: `a` is an irrational algebraic value from this context.
        unsafe { (self.api.algebraic_get_i)(self.ctx, a) }
    }

    /// Coefficients of z3's defining polynomial for an algebraic value, as
    /// printed rationals (low-to-high, per `Z3_algebraic_get_poly`).
    pub(crate) fn defining_poly(&self, a: Ptr) -> Option<Vec<BigRational>> {
        clear_error();
        // SAFETY: `a` is an algebraic value from this context.
        let vec = unsafe { (self.api.algebraic_get_poly)(self.ctx, a) };
        if vec.is_null() || self.errored() {
            return None;
        }
        let asts = self.drain_vector(vec);
        asts.iter().map(|a| self.numeral_value(*a)).collect()
    }

    /// Decode a numeral AST into an exact rational; `None` when the AST is not
    /// a numeral.
    pub(crate) fn numeral_value(&self, a: Ptr) -> Option<BigRational> {
        clear_error();
        // SAFETY: `Z3_get_numeral_string` returns a context-owned C string; we
        // copy it before any further z3 call.
        let s = unsafe {
            let p = (self.api.get_numeral_string)(self.ctx, a);
            if p.is_null() || self.errored() {
                return None;
            }
            CStr::from_ptr(p).to_string_lossy().into_owned()
        };
        parse_rational(&s)
    }

    /// Render an AST for reproducer dumps.
    pub(crate) fn ast_string(&self, a: Ptr) -> String {
        // SAFETY: `Z3_ast_to_string` returns a context-owned C string; copied
        // immediately.
        unsafe {
            let p = (self.api.ast_to_string)(self.ctx, a);
            if p.is_null() {
                return "<null>".to_string();
            }
            CStr::from_ptr(p).to_string_lossy().into_owned()
        }
    }

    /// Is `a` usable as an algebraic value?
    pub(crate) fn is_value(&self, a: Ptr) -> bool {
        // SAFETY: `a` is an AST handle minted by this very context (`self.ctx`)
        // and the signature matches the `decl_api!` declaration.
        unsafe { (self.api.algebraic_is_value)(self.ctx, a) }
    }

    /// Bracket an algebraic value between two rationals by binary search on
    /// z3's own exact comparison. Returns `(lo, hi)` with `lo < v < hi`, or the
    /// exact value twice when `v` turns out to be that rational.
    ///
    /// This is the oracle's universal comparison primitive: it converts *any*
    /// z3 real algebraic number into a rational enclosure that AY's exact
    /// comparison can be tested against, with no shared representation and no
    /// floating point anywhere.
    pub(crate) fn bracket(&self, v: Ptr, steps: u32) -> Option<(BigRational, BigRational)> {
        let two = BigRational::from_integer(BigInt::from(2));
        // Expand outward from [-1, 1] until the value is strictly inside.
        let mut lo = -BigRational::one();
        let mut hi = BigRational::one();
        for _ in 0..256 {
            let lo_ast = self.rational(&lo);
            let hi_ast = self.rational(&hi);
            if self.eq(v, lo_ast) || self.eq(v, hi_ast) {
                let exact = if self.eq(v, lo_ast) { lo } else { hi };
                return Some((exact.clone(), exact));
            }
            if self.gt(v, lo_ast) && self.lt(v, hi_ast) {
                break;
            }
            lo *= &two;
            hi *= &two;
            if self.errored() {
                return None;
            }
        }
        for _ in 0..steps {
            let mid = (&lo + &hi) / &two;
            let mid_ast = self.rational(&mid);
            if self.eq(v, mid_ast) {
                return Some((mid.clone(), mid));
            }
            if self.lt(v, mid_ast) {
                hi = mid;
            } else {
                lo = mid;
            }
            if self.errored() {
                return None;
            }
        }
        Some((lo, hi))
    }
}

impl Drop for Z3 {
    fn drop(&mut self) {
        // SAFETY: the context is live and no AST from it is used afterwards.
        unsafe {
            for v in self.held_vectors.borrow_mut().drain(..) {
                (self.api.ast_vector_dec_ref)(self.ctx, v);
            }
            (self.api.del_context)(self.ctx);
        }
    }
}

/// Parse z3's numeral rendering (`"3"`, `"-7/2"`, `"(- 5)"`, `"1.5"`).
pub(crate) fn parse_rational(s: &str) -> Option<BigRational> {
    let t = s.trim();
    // z3 sometimes prints negatives as `(- 5)` / `(/ 1.0 2.0)`; the numeral
    // string API returns plain forms, but be tolerant.
    if let Some(rest) = t.strip_prefix("(-") {
        let inner = rest.trim_end_matches(')').trim();
        return parse_rational(inner).map(|r| -r);
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
    use super::parse_rational;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    #[test]
    fn parses_z3_numeral_renderings() {
        let r = |n: i64, d: i64| BigRational::new(BigInt::from(n), BigInt::from(d));
        assert_eq!(parse_rational("3"), Some(r(3, 1)));
        assert_eq!(parse_rational("-7/2"), Some(r(-7, 2)));
        assert_eq!(parse_rational("(- 5)"), Some(r(-5, 1)));
        assert_eq!(parse_rational("1.5"), Some(r(3, 2)));
        assert_eq!(parse_rational("-1.25"), Some(r(-5, 4)));
        assert_eq!(parse_rational("nonsense"), None);
    }
}
