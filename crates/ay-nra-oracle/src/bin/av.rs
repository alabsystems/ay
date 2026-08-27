// ADVERSARIAL VERIFICATION HARNESS for the `anum` lane.
//
// Written from scratch by the verifier; it shares NO code with
// `crates/ay-nra-oracle/src/anum.rs` (the lane's own checks) beyond the z3
// binding. Run it with:
//
//     cargo build --release -p ay-nra-oracle --bin av
//     ./target/release/av --only a|e
//     ./target/release/av --only b|c|d --z3 /path/to/libz3 [--cases N] [--seed S]
//     ./target/release/av --z3 /path/to/libz3 [--cases N] [--seed S]
//
// The default run covers A-D; the especially heavy E suite is opt-in.
//
//   A  equality / liveness on analytic ground truth (11 spellings of sqrt(2),
//      conjugates, overlapping intervals, numbers 2^-258 apart, algebraic zero)
//   B  randomized comparison vs z3 AND vs an independent BigRational model
//   C  add / mul / sign / neg vs z3
//   D  the DERIVED separation bound vs z3's actual root gaps
//   E  growth: mixed-degree chains and the sign evaluation nlsat's inner loop
//      repeats
//
// Potentially long AY operations below run under a watchdog thread. Native
// reference calls run directly; use an external process timeout to bound a
// hung libz3.
//
// Independent of `crates/ay-nra-oracle/src/anum.rs`. Three opinions per case:
//   1. AY's `anum` (the code under test)
//   2. z3's `Z3_algebraic_*` through the same dlopen binding
//   3. a SECOND AY implementation: `univariate`'s BigRational Euclidean Sturm
//      chain + `algebraic.rs`, reached through the facade. Different code, same
//      question.

#![allow(clippy::all, dead_code, unused_imports)]

use std::cmp::Ordering;
use std::sync::{
    atomic::{AtomicU64, Ordering as AtomicOrdering},
    mpsc,
};
use std::time::{Duration, Instant};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use ay_nra::oracle_api::{
    anum_binop_diag, anum_cauchy_bound, anum_max_separation_bits, anum_normalize_defining,
    anum_root_separation_exponent, anum_sturm_count_in, obq_enclose_rational, OAnumOpDiag, OBq,
    OBqInterval, ODyadicAnum, OPoly, ORoot,
};

#[path = "../z3.rs"]
mod z3;
use z3::{Ast, Z3};

include!("av/support.rs");
include!("av/suite_a.rs");
include!("av/model.rs");
include!("av/suite_b.rs");
include!("av/suite_c.rs");
include!("av/suite_d.rs");
include!("av/suite_e.rs");
include!("av/cli.rs");
