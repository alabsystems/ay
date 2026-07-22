//! `R*` — the rationals extended with an infinitesimal `ε`, used to make
//! *strict* rational difference constraints exact.
//!
//! An element is `a + b·ε` written `(a, b)` where `a` is the rational part and
//! `b ∈ ℤ` counts infinitesimals. `ε` is positive and smaller than every
//! positive rational, so ordering is lexicographic: compare `a` first, then `b`.
//! Addition is component-wise. This is the standard delta/epsilon trick used by
//! SMT real-arithmetic solvers to encode strict inequalities without choosing a
//! concrete slack.
//!
//! `x - y < c` becomes `x - y <= c − ε`, i.e. an edge weight `(c, -1)`. A
//! non-strict `x - y <= c` is `(c, 0)`. A negative cycle in `R*` (sum `< (0,0)`)
//! is a genuine contradiction: either the rational sum is negative, or it is
//! zero with a negative ε-count, meaning the strict constraints alone force
//! `0 < 0`.
//!
//! ## Model extraction
//!
//! Shortest-path distances live in `R*`. To produce a concrete rational model we
//! pick a single small positive `δ` and evaluate `a + b·δ`. Any `δ` strictly
//! smaller than the least positive gap between distinct rational parts works;
//! [`RStar::realize_with`] takes the `δ` and [`pick_delta`] computes a safe one
//! from the set of distances actually used.

use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::atom::Negate;
use crate::weight::Weight;

/// A value in `ℚ[ε]` ordered lexicographically: `(rational, ε-coefficient)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RStar {
    /// The standard rational part.
    pub q: BigRational,
    /// The infinitesimal coefficient (count of `ε`s); `ε` is positive.
    pub eps: i64,
}

impl RStar {
    /// `q + eps·ε`.
    pub fn new(q: BigRational, eps: i64) -> Self {
        Self { q, eps }
    }

    /// A finite (no-ε) rational value.
    pub fn finite(q: BigRational) -> Self {
        Self { q, eps: 0 }
    }

    /// Realize as a concrete rational by substituting `ε := delta`. Sound only
    /// when `delta` is smaller than the least positive rational gap among the
    /// values being compared; use [`pick_delta`] to obtain such a `delta`.
    pub fn realize_with(&self, delta: &BigRational) -> BigRational {
        &self.q + BigRational::from_integer(self.eps.into()) * delta
    }
}

impl PartialOrd for RStar {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RStar {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.q.cmp(&other.q) {
            std::cmp::Ordering::Equal => self.eps.cmp(&other.eps),
            ord => ord,
        }
    }
}

impl Weight for RStar {
    #[inline]
    fn zero() -> Self {
        Self {
            q: <BigRational as Zero>::zero(),
            eps: 0,
        }
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        Self {
            q: &self.q + &other.q,
            eps: self
                .eps
                .checked_add(other.eps)
                .expect("RStar epsilon-count overflow (i64); pathologically deep strict chain"),
        }
    }
}

impl Negate for RStar {
    #[inline]
    fn negate(&self) -> Self {
        Self {
            q: -&self.q,
            eps: -self.eps,
        }
    }
}

/// Choose a positive `δ` such that substituting `ε := δ` turns every symbolic
/// `R*` slack `(g, k)` (with `(g, k) >= (0, 0)` lexicographically) into a
/// non-negative concrete rational `g + k·δ`.
///
/// The model returned by Bellman-Ford satisfies, for each constraint edge
/// `from → to : w`, the `R*` inequality `dist[to] <= dist[from] + w`, i.e. the
/// slack `s = dist[from] + w − dist[to]` is `R*`-nonnegative. Each slack is some
/// `(g, k)`:
///
/// * `g > 0`  — realizes to `g + k·δ`. If `k >= 0` any `δ > 0` keeps it `>= 0`.
///   If `k < 0` we need `δ < g / (−k)`.
/// * `g = 0`  — then `R*`-nonnegativity forces `k >= 0`, so `k·δ >= 0` for any
///   `δ > 0`. No constraint on `δ`.
/// * `g < 0`  — impossible for a valid model (would mean the slack is `R*`-
///   negative); such an input is a bug and is ignored here.
///
/// We therefore take `δ = (1/2)·min{ g / (−k) : slack (g,k), g > 0, k < 0 }`,
/// or `1` when no such slack exists. The half-margin guarantees strict
/// inequalities (`δ < g/(−k)`), so realized strict constraints stay strict.
///
/// `slacks` are the `(rational, eps)` pairs of every constraint's slack.
pub fn pick_delta_from_slacks(slacks: &[(BigRational, i64)]) -> BigRational {
    let mut bound: Option<BigRational> = None;
    for (g, k) in slacks {
        if g.is_positive() && *k < 0 {
            // need δ < g / (-k)
            let limit = g / BigRational::from_integer((-*k).into());
            bound = Some(match bound {
                Some(b) if b <= limit => b,
                _ => limit,
            });
        }
    }
    match bound {
        Some(b) => b / BigRational::from_integer(2.into()),
        None => <BigRational as One>::one(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::FromPrimitive;

    fn r(n: i64, d: i64) -> BigRational {
        BigRational::new(n.into(), d.into())
    }

    #[test]
    fn lex_order_rational_dominates() {
        assert!(RStar::new(r(1, 2), -100) < RStar::new(r(3, 4), 0));
        assert!(RStar::new(r(1, 1), 0) > RStar::new(r(0, 1), 1000));
    }

    #[test]
    fn lex_order_eps_breaks_ties() {
        assert!(RStar::new(r(1, 2), -1) < RStar::new(r(1, 2), 0));
        assert!(RStar::new(r(1, 2), 0) < RStar::new(r(1, 2), 1));
    }

    #[test]
    fn add_is_componentwise() {
        let a = RStar::new(r(1, 2), 1);
        let b = RStar::new(r(1, 4), -3);
        let s = Weight::add(&a, &b);
        assert_eq!(s.q, r(3, 4));
        assert_eq!(s.eps, -2);
    }

    #[test]
    fn negative_cycle_via_eps_only() {
        // sum (0, -1) means 0 - ε < 0  -> contradiction.
        let s = RStar::new(<BigRational as Zero>::zero(), -1);
        assert!(s < RStar::zero());
    }

    #[test]
    fn pick_delta_undercuts_tightest_slack() {
        // slack (1/3, -1) needs δ < 1/3; slack (1/2, -1) needs δ < 1/2.
        // tightest is 1/3 ⇒ δ = 1/6.
        let slacks = vec![(r(1, 3), -1), (r(1, 2), -1), (r(0, 1), 2)];
        let d = pick_delta_from_slacks(&slacks);
        assert!(d > <BigRational as Zero>::zero());
        assert!(d < r(1, 3));
        assert_eq!(d, r(1, 6));
    }

    #[test]
    fn pick_delta_no_strict_slacks_is_one() {
        // No (g>0, k<0) slack ⇒ δ defaults to 1.
        let slacks = vec![(r(2, 1), 0), (r(0, 1), 3)];
        assert_eq!(pick_delta_from_slacks(&slacks), <BigRational as One>::one());
    }

    #[test]
    fn pick_delta_scales_with_eps_count() {
        // slack (1, -2): need δ < 1/2 ⇒ δ = 1/4.
        let slacks = vec![(r(1, 1), -2)];
        assert_eq!(pick_delta_from_slacks(&slacks), r(1, 4));
    }

    #[test]
    fn realize_preserves_strict() {
        // a = (1, 0), b = (1, -1) [meaning 1 - ε], with delta 1/2 -> b < a still.
        let a = RStar::finite(BigRational::from_f64(1.0).unwrap());
        let b = RStar::new(BigRational::from_f64(1.0).unwrap(), -1);
        let d = r(1, 2);
        assert!(b.realize_with(&d) < a.realize_with(&d));
    }
}
