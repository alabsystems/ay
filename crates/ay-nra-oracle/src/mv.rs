// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential checks for `crates/ay-theories/nra/src/mroot.rs` — real-root
//! isolation of a MULTIVARIATE polynomial at an algebraic sample point.
//!
//! # Why these are the strongest checks in the oracle
//!
//! Every other comparison in this binary is indirect. The univariate checks
//! compare AY against a z3 primitive that answers a NEARBY question; the
//! bivariate subresultant checks compare AY's multivariate answer against z3's
//! univariate one through a specialization theorem, because z3's C API will
//! not hand back a multivariate subresultant in a form an oracle can read
//! without writing its own normalizer.
//!
//! Here there is no gap at all. `Z3_algebraic_roots(c, p, n, a)` is a thin
//! wrapper (`api/api_algebraic.cpp:352`) around
//!
//! ```text
//!     algebraic_numbers::manager::isolate_roots(p, x2v, roots)
//! ```
//!
//! and `Z3_algebraic_eval(c, p, n, a)` around `eval_sign_at(p, x2v)` — the two
//! functions `mroot.rs` reimplements, called with the same polynomial and the
//! same sample point. The reference is answering the identical question.
//!
//! # How the sample point is agreed on without sharing a representation
//!
//! Neither side is told the other's algebraic numbers. Both are given the same
//! DEFINING POLYNOMIAL and the same ROOT INDEX:
//!
//! * AY isolates that polynomial's real roots with its own univariate
//!   machinery and takes the `i`-th ascending one;
//! * z3 is asked for the same polynomial's roots via `Z3_algebraic_roots` with
//!   no assignment, and the `i`-th ascending one is used.
//!
//! If the two lists differ in length the case is SKIPPED, not diverged — that
//! is the univariate `roots` check's business and reporting it here would
//! double-count one bug as two.
//!
//! Answers are then compared through [`crate::z3::Z3::bracket`], which turns a
//! z3 algebraic number into a rational enclosure using z3's own exact
//! comparisons, and AY's exact `cmp_rational` decides whether its root lies
//! inside. No representation, no floating point, and no normalizer is shared.
//!
//! # What the generator deliberately reaches
//!
//! Random polynomials never trigger `mroot.rs`'s hardest branch: the
//! VANISHING RESULTANT, which needs the polynomial and the coordinate's
//! defining polynomial to share a factor. One generated shape forces it —
//! a linear factor `(y - c)` is multiplied into BOTH — so the escape path
//! (fresh variable bound to the leading coefficient's value, recursive call)
//! is exercised against z3 rather than only against unit tests.

use std::cmp::Ordering;

use ay_nra::oracle_api::{OAlg, OAnum, OMPoly, OPoly, ORoot, OVar2Anum};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use crate::checks::{Divergence, Outcome, Sabotage};
use crate::polygen::Rng;
use crate::z3::{Ast, Z3};

/// Bisection steps used to bracket a z3 root before comparing it to AY's.
///
/// `40` puts the enclosure at `2^-40` of its initial width, far below any
/// separation these degrees produce, so a containment result is an equality
/// result in practice — and a genuinely equal pair can never fail it, since
/// AY's root is exactly inside every enclosure of itself.
const BRACKET_STEPS: u32 = 40;

/// Maximum degree of a coordinate's defining polynomial.
///
/// The elimination multiplies degrees: with `k` assigned coordinates of degree
/// `d` and an unknown of degree `e`, the resultant chain reaches `e * d^k`.
/// At `3` and two coordinates that is a degree-27 univariate isolation per
/// case, which is measured at milliseconds; at `5` it is degree-125 and the
/// case time is dominated by `BigRational` Sturm sequences rather than by
/// anything either implementation gets wrong.
const MAX_DEF_DEG: usize = 3;

/// Maximum degree of the generated polynomial in the unknown.
const MAX_X_DEG: usize = 3;

/// Maximum degree of the generated polynomial in any assigned coordinate.
const MAX_Y_DEG: usize = 2;

/// Work budget for one multivariate case, in units of the degree of the
/// univariate polynomial the elimination produces:
/// `deg_x(p) * prod_i deg(m_i)` (see [`GenMv::elimination_degree`]).
///
/// MEASURED, not guessed. At seed 5 without this guard, case #47 — two
/// coordinates of defining degree 3 and 4 against a cubic in `x`, an
/// elimination degree of 36 — ran for **32.97 s**, entirely inside AY (z3
/// answered promptly), and dominated a 400-case run whose other 399 cases took
/// 41 s together. The cost is AY's own known heavy tail: `isolate_roots` on
/// the eliminated polynomial runs a `BigRational` Sturm sequence whose
/// coefficients are the resultant's, and both degree and bit-width grow
/// multiplicatively through the chain.
///
/// At `24` the measured worst mv case is under a second. Raising it does not
/// reach any new BRANCH of `mroot.rs` — every path is already covered at lower
/// degree, and the unit tests pin the degenerate ones — it only buys larger
/// numbers through the same code, at a cost that would consume the campaign.
/// A case over budget is reported as inapplicable, never silently dropped.
const MAX_ELIM_DEGREE: usize = 24;

include!("mv/generator.rs");
include!("mv/root_check.rs");
include!("mv/selection_checks.rs");
