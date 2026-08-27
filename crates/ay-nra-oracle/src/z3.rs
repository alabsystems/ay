// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(unsafe_code)] // Audited runtime C-ABI boundary; every block states its local invariant.

//! Runtime binding to the real libz3's algebraic-number and polynomial C API.
//!
//! Nothing is linked at build time: the dylib is `dlopen`'d with
//! `RTLD_NOW | RTLD_LOCAL` exactly as `ay-z3-parity` does, so that AY's own
//! `Z3_*` exports (`ay-ffi` ships a drop-in libz3 ABI) are not resolved from
//! the process-global namespace. The selected path remains a native-code trust
//! boundary and must name an ABI-compatible reference libz3.
//!
//! Memory model: contexts are created with `Z3_mk_context` (no reference
//! counting), every AST lives until the context dies, and the driver recycles
//! the context every few hundred cases. That is deliberate — refcount bugs in
//! the harness would show up as z3 crashes and be mistaken for divergences.

use std::ffi::{c_void, CStr, CString};
use std::os::raw::{c_char, c_int, c_uint};
use std::path::{Path, PathBuf};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

#[cfg(unix)]
use libloading::os::unix::Library;
#[cfg(windows)]
use libloading::os::windows::Library;

include!("z3/handles.rs");

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AstKind {
    AlgebraicValue,
    Polynomial,
    Term,
}

/// An AST owned by one live generation of one [`Z3`] instance.
///
/// The fields are private so code outside this binding cannot manufacture a
/// null, foreign-context, wrong-generation, or wrong-kind C handle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Ast {
    raw: NonNull<c_void>,
    owner: u64,
    generation: u64,
    kind: AstKind,
}

impl Ast {
    fn raw_for(self, owner: u64, generation: u64) -> Option<RawAst> {
        (self.owner == owner && self.generation == generation).then_some(RawAst(self.raw.as_ptr()))
    }
}

/// A failure while loading or initializing the reference Z3 instance.
#[derive(Debug, thiserror::Error)]
pub(crate) enum Z3Error {
    #[error("could not load reference libz3 at {path:?}: {source}")]
    Load {
        path: PathBuf,
        #[source]
        source: libloading::Error,
    },
    #[error("could not resolve libz3 symbol {symbol}: {source}")]
    Symbol {
        symbol: String,
        #[source]
        source: libloading::Error,
    },
    #[error("libz3 operation {operation} returned a null handle")]
    Null { operation: &'static str },
    #[error("libz3 operation {operation} failed with error code {code}")]
    Api {
        operation: &'static str,
        code: c_uint,
    },
    #[error("exhausted unique Z3 owner identifiers")]
    OwnerExhausted,
    #[error("exhausted recycle generations for this Z3 owner")]
    GenerationExhausted,
}

/// Suppress Z3's process-terminating default handler. Errors are read from the
/// context immediately through `Z3_get_error_code`, rather than a global that
/// can mix failures from independently owned contexts on different threads.
unsafe extern "C" fn error_handler(_c: RawContext, _e: c_uint) {}

macro_rules! decl_api {
    ($( $field:ident : $sym:literal : $ty:ty ),+ $(,)?) => {
        /// Raw entry points resolved out of the loaded libz3.
        #[derive(Clone, Copy)]
        struct Api {
            $( $field: $ty, )+
        }

        impl Api {
            /// # Safety
            ///
            /// `lib` must be trusted native code implementing every named
            /// function with the matching libz3 C ABI signature below.
            unsafe fn resolve(lib: &Library) -> Result<Self, Z3Error> {
                // SAFETY: the caller supplies the native-code/ABI trust that
                // symbol names alone cannot establish. Each lookup uses the
                // corresponding published libz3 header signature.
                unsafe {
                    $(
                        let $field: $ty = *lib
                            .get::<$ty>($sym)
                            .map_err(|source| Z3Error::Symbol {
                                symbol: ::std::str::from_utf8($sym)
                                    .unwrap_or("?")
                                    .trim_end_matches('\0')
                                    .to_owned(),
                                source,
                            })?;
                    )+
                    Ok(Self { $( $field, )+ })
                }
            }
        }
    };
}

decl_api! {
    mk_config: b"Z3_mk_config\0": unsafe extern "C" fn() -> RawConfig,
    del_config: b"Z3_del_config\0": unsafe extern "C" fn(RawConfig),
    set_param_value: b"Z3_set_param_value\0": unsafe extern "C" fn(RawConfig, *const c_char, *const c_char),
    mk_context: b"Z3_mk_context\0": unsafe extern "C" fn(RawConfig) -> RawContext,
    del_context: b"Z3_del_context\0": unsafe extern "C" fn(RawContext),
    set_error_handler: b"Z3_set_error_handler\0": unsafe extern "C" fn(RawContext, unsafe extern "C" fn(RawContext, c_uint)),
    get_error_code: b"Z3_get_error_code\0": unsafe extern "C" fn(RawContext) -> c_uint,
    get_full_version: b"Z3_get_full_version\0": unsafe extern "C" fn() -> *const c_char,

    mk_real_sort: b"Z3_mk_real_sort\0": unsafe extern "C" fn(RawContext) -> RawSort,
    mk_numeral: b"Z3_mk_numeral\0": unsafe extern "C" fn(RawContext, *const c_char, RawSort) -> RawAst,
    mk_bound: b"Z3_mk_bound\0": unsafe extern "C" fn(RawContext, c_uint, RawSort) -> RawAst,
    mk_string_symbol: b"Z3_mk_string_symbol\0": unsafe extern "C" fn(RawContext, *const c_char) -> RawSymbol,
    mk_const: b"Z3_mk_const\0": unsafe extern "C" fn(RawContext, RawSymbol, RawSort) -> RawAst,
    mk_add: b"Z3_mk_add\0": unsafe extern "C" fn(RawContext, c_uint, *const RawAst) -> RawAst,
    mk_mul: b"Z3_mk_mul\0": unsafe extern "C" fn(RawContext, c_uint, *const RawAst) -> RawAst,
    get_numeral_string: b"Z3_get_numeral_string\0": unsafe extern "C" fn(RawContext, RawAst) -> *const c_char,
    is_numeral_ast: b"Z3_is_numeral_ast\0": unsafe extern "C" fn(RawContext, RawAst) -> bool,
    ast_to_string: b"Z3_ast_to_string\0": unsafe extern "C" fn(RawContext, RawAst) -> *const c_char,
    is_algebraic_number: b"Z3_is_algebraic_number\0": unsafe extern "C" fn(RawContext, RawAst) -> bool,

    ast_vector_size: b"Z3_ast_vector_size\0": unsafe extern "C" fn(RawContext, RawAstVector) -> c_uint,
    ast_vector_get: b"Z3_ast_vector_get\0": unsafe extern "C" fn(RawContext, RawAstVector, c_uint) -> RawAst,
    ast_vector_inc_ref: b"Z3_ast_vector_inc_ref\0": unsafe extern "C" fn(RawContext, RawAstVector),
    ast_vector_dec_ref: b"Z3_ast_vector_dec_ref\0": unsafe extern "C" fn(RawContext, RawAstVector),

    algebraic_is_value: b"Z3_algebraic_is_value\0": unsafe extern "C" fn(RawContext, RawAst) -> bool,
    algebraic_add: b"Z3_algebraic_add\0": unsafe extern "C" fn(RawContext, RawAst, RawAst) -> RawAst,
    algebraic_mul: b"Z3_algebraic_mul\0": unsafe extern "C" fn(RawContext, RawAst, RawAst) -> RawAst,
    algebraic_lt: b"Z3_algebraic_lt\0": unsafe extern "C" fn(RawContext, RawAst, RawAst) -> bool,
    algebraic_gt: b"Z3_algebraic_gt\0": unsafe extern "C" fn(RawContext, RawAst, RawAst) -> bool,
    algebraic_eq: b"Z3_algebraic_eq\0": unsafe extern "C" fn(RawContext, RawAst, RawAst) -> bool,
    algebraic_roots: b"Z3_algebraic_roots\0": unsafe extern "C" fn(RawContext, RawAst, c_uint, *const RawAst) -> RawAstVector,
    algebraic_eval: b"Z3_algebraic_eval\0": unsafe extern "C" fn(RawContext, RawAst, c_uint, *const RawAst) -> c_int,
    algebraic_get_i: b"Z3_algebraic_get_i\0": unsafe extern "C" fn(RawContext, RawAst) -> c_uint,
    algebraic_get_poly: b"Z3_algebraic_get_poly\0": unsafe extern "C" fn(RawContext, RawAst) -> RawAstVector,

    polynomial_subresultants: b"Z3_polynomial_subresultants\0": unsafe extern "C" fn(RawContext, RawAst, RawAst, RawAst) -> RawAstVector,
}

/// How many bound variables the multivariate builders can address.
///
/// The multivariate checks never draw more than a couple of assigned
/// coordinates plus the unknown; this is the hard ceiling, and
/// [`Z3::mpoly_bound`] refuses rather than reaching past it.
const MAX_MV_VARS: u32 = 6;

struct ConfigGuard<'a> {
    api: &'a Api,
    ptr: RawConfig,
}

impl Drop for ConfigGuard<'_> {
    fn drop(&mut self) {
        // SAFETY: `ptr` is the live config returned by this `api`'s
        // `Z3_mk_config`, and this guard owns its sole deletion.
        unsafe { (self.api.del_config)(self.ptr) };
    }
}

struct ContextGuard<'a> {
    api: &'a Api,
    ptr: RawContext,
}

impl ContextGuard<'_> {
    fn into_raw(mut self) -> RawContext {
        let ptr = self.ptr;
        self.ptr = RawContext(std::ptr::null_mut());
        ptr
    }
}

impl Drop for ContextGuard<'_> {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            // SAFETY: `ptr` is the live context returned by this `api`'s
            // `Z3_mk_context`, and this guard owns it until `into_raw`.
            unsafe { (self.api.del_context)(self.ptr) };
        }
    }
}

struct ContextState {
    ctx: RawContext,
    real: RawSort,
    x_bound: RawAst,
    bound: Vec<RawAst>,
    x_const: RawAst,
}

fn check_context(api: &Api, ctx: RawContext, operation: &'static str) -> Result<(), Z3Error> {
    // SAFETY: callers pass the live context currently being initialized.
    let code = unsafe { (api.get_error_code)(ctx) };
    if code == 0 {
        Ok(())
    } else {
        Err(Z3Error::Api { operation, code })
    }
}

fn checked_context_ptr<T: NullableHandle>(
    api: &Api,
    ctx: RawContext,
    ptr: T,
    operation: &'static str,
) -> Result<T, Z3Error> {
    check_context(api, ctx, operation)?;
    if ptr.is_null() {
        Err(Z3Error::Null { operation })
    } else {
        Ok(ptr)
    }
}

fn create_context(api: &Api) -> Result<ContextState, Z3Error> {
    // SAFETY: the function pointer was resolved as `Z3_mk_config`.
    let cfg = unsafe { (api.mk_config)() };
    if cfg.is_null() {
        return Err(Z3Error::Null {
            operation: "Z3_mk_config",
        });
    }
    let cfg = ConfigGuard { api, ptr: cfg };

    // SAFETY: both C string literals are static and NUL-terminated, and
    // `cfg.ptr` is a live Z3 configuration.
    unsafe {
        (api.set_param_value)(cfg.ptr, c"model".as_ptr(), c"false".as_ptr());
    }
    // SAFETY: `cfg.ptr` is a live configuration created by this API.
    let ctx = unsafe { (api.mk_context)(cfg.ptr) };
    if ctx.is_null() {
        return Err(Z3Error::Null {
            operation: "Z3_mk_context",
        });
    }
    let ctx = ContextGuard { api, ptr: ctx };
    drop(cfg);

    // SAFETY: `ctx.ptr` is live and the callback has the declared Z3 ABI.
    unsafe { (api.set_error_handler)(ctx.ptr, error_handler) };
    check_context(api, ctx.ptr, "Z3_set_error_handler")?;

    // SAFETY: each constructor receives this same live context, and every
    // returned handle is checked before it is retained or reused.
    let real = unsafe { (api.mk_real_sort)(ctx.ptr) };
    let real = checked_context_ptr(api, ctx.ptr, real, "Z3_mk_real_sort")?;
    // SAFETY: `real` is the checked real sort owned by `ctx.ptr`.
    let x_bound = unsafe { (api.mk_bound)(ctx.ptr, 0, real) };
    let x_bound = checked_context_ptr(api, ctx.ptr, x_bound, "Z3_mk_bound")?;
    let mut bound = Vec::with_capacity(MAX_MV_VARS as usize);
    for i in 0..MAX_MV_VARS {
        // SAFETY: `real` is the checked real sort owned by `ctx.ptr`.
        let ast = unsafe { (api.mk_bound)(ctx.ptr, i, real) };
        bound.push(checked_context_ptr(api, ctx.ptr, ast, "Z3_mk_bound")?);
    }
    // SAFETY: the C string literal is static and NUL-terminated, and `ctx.ptr`
    // is live.
    let symbol = unsafe { (api.mk_string_symbol)(ctx.ptr, c"x".as_ptr()) };
    let symbol = checked_context_ptr(api, ctx.ptr, symbol, "Z3_mk_string_symbol")?;
    // SAFETY: `symbol` and `real` are checked handles from `ctx.ptr`.
    let x_const = unsafe { (api.mk_const)(ctx.ptr, symbol, real) };
    let x_const = checked_context_ptr(api, ctx.ptr, x_const, "Z3_mk_const")?;

    Ok(ContextState {
        ctx: ctx.into_raw(),
        real,
        x_bound,
        bound,
        x_const,
    })
}

/// An open libz3 plus a live context.
pub(crate) struct Z3 {
    // Kept alive for the lifetime of every function pointer in `api`.
    _lib: Library,
    api: Api,
    ctx: RawContext,
    real: RawSort,
    /// Bound variable 0 of real sort — the polynomial indeterminate.
    x_bound: RawAst,
    /// Bound variables `0 .. MAX_MV_VARS` of real sort, for the MULTIVARIATE
    /// entry points. `Z3_algebraic_roots(c, p, n, a)` reads `p` as a
    /// polynomial in `x_0 .. x_n`, assigns `x_0 .. x_{n-1}` from `a`, and
    /// solves for `x_n`, so a check of `isolate_roots` at a sample point has
    /// to be able to build a polynomial over several bound variables at once.
    bound: Vec<RawAst>,
    /// A real constant named `x`, for `Z3_polynomial_subresultants`.
    x_const: RawAst,
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
    held_vectors: std::cell::RefCell<Vec<RawAstVector>>,
    reference_failures: std::cell::Cell<u64>,
    owner: u64,
    generation: u64,
    /// libz3's self-reported version string.
    pub(crate) version: String,
}

impl Z3 {
    /// Load a trusted reference libz3 and stand up a fresh context.
    ///
    /// This function verifies symbol presence and returned handles, not the
    /// provenance or behavior of native code at `path`.
    ///
    /// # Safety
    ///
    /// `path` must identify native code trusted by the caller and implementing
    /// the libz3 C ABI used by every symbol in [`Api`] for the current target.
    /// Loading a library may execute its initialization code, and neither
    /// symbol lookup nor handle validation can make a malicious library or an
    /// ABI-incompatible function implementation safe to call.
    pub(crate) unsafe fn open_trusted_reference(path: &Path) -> Result<Self, Z3Error> {
        // SAFETY: loading may execute arbitrary native initializers; the
        // caller's trust contract accepts that risk and requires a genuine
        // ABI-compatible libz3. RTLD_LOCAL keeps its `Z3_*` exports local.
        #[cfg(unix)]
        let lib = unsafe {
            Library::open(Some(path), libc::RTLD_NOW | libc::RTLD_LOCAL).map_err(|source| {
                Z3Error::Load {
                    path: path.to_path_buf(),
                    source,
                }
            })?
        };
        #[cfg(windows)]
        // SAFETY: loading may execute arbitrary native initializers; the
        // caller's trust contract accepts that risk and guarantees `path`
        // implements the libz3 ABI below. Later checks catch only absent
        // symbols and null handles, not malicious code or ABI mismatch.
        let lib = unsafe {
            Library::new(path).map_err(|source| Z3Error::Load {
                path: path.to_path_buf(),
                source,
            })?
        };

        // SAFETY: `open_trusted_reference` requires the caller to guarantee
        // that this library implements the matching libz3 C ABI.
        let api = unsafe { Api::resolve(&lib) }?;
        // SAFETY: the symbol has the checked `Z3_get_full_version` signature;
        // the returned pointer is validated before `CStr` observes it.
        let version = unsafe { (api.get_full_version)() };
        if version.is_null() {
            return Err(Z3Error::Null {
                operation: "Z3_get_full_version",
            });
        }
        // SAFETY: the non-null version pointer is owned by the still-live
        // library and Z3 documents it as a NUL-terminated string.
        let version = unsafe { CStr::from_ptr(version) }
            .to_string_lossy()
            .into_owned();
        let owner = next_owner()?;
        let state = create_context(&api)?;
        Ok(Self {
            _lib: lib,
            api,
            ctx: state.ctx,
            real: state.real,
            x_bound: state.x_bound,
            bound: state.bound,
            x_const: state.x_const,
            held_vectors: std::cell::RefCell::new(Vec::new()),
            reference_failures: std::cell::Cell::new(0),
            owner,
            generation: 0,
            version,
        })
    }

    /// True when z3 has flagged an error on this context.
    pub(crate) fn errored(&self) -> bool {
        // SAFETY: reading the error code of a live context.
        let code = unsafe { (self.api.get_error_code)(self.ctx) };
        if code != 0 {
            self.record_reference_failure();
        }
        code != 0
    }

    fn wrap_ast(&self, raw: RawAst, kind: AstKind) -> Option<Ast> {
        let raw = NonNull::new(raw.0).or_else(|| self.failed())?;
        Some(Ast {
            raw,
            owner: self.owner,
            generation: self.generation,
            kind,
        })
    }

    fn current_raw(&self, ast: Ast) -> Option<RawAst> {
        ast.raw_for(self.owner, self.generation)
    }

    fn polynomial_raw(&self, ast: Ast) -> Option<RawAst> {
        (ast.kind == AstKind::Polynomial)
            .then(|| self.current_raw(ast))
            .flatten()
    }

    fn algebraic_raw(&self, ast: Ast) -> Option<RawAst> {
        if ast.kind != AstKind::AlgebraicValue {
            return None;
        }
        let raw = self.current_raw(ast)?;
        // SAFETY: `raw` is non-null and belongs to this live context
        // generation. The handle's kind restricts this dynamic check to ASTs
        // constructed by algebraic-value-producing Z3 operations.
        let is_value = unsafe { (self.api.algebraic_is_value)(self.ctx, raw) };
        self.checked_algebraic_value(raw, is_value)
    }
}

include!("z3/construct.rs");
include!("z3/values.rs");
include!("z3/lifecycle.rs");
