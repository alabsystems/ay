//! Difference-logic atoms and their *strict, fail-closed* translation to graph
//! edges.
//!
//! # Recognised atom shapes
//!
//! A difference-logic atom relates a single *difference of two variables* (or a
//! degenerate single variable, treated as a difference against an implicit zero
//! variable `Z`) to a constant:
//!
//! ```text
//!     x - y  ⋈  c        (two-variable form)
//!     x      ⋈  c        (var-vs-const form,  ==  x - Z ⋈ c)
//! ```
//!
//! where `⋈ ∈ { <= , < , = , >= , > }`. Anything else — three or more distinct
//! variables, non-unit coefficients, products, etc. — is **not** a difference
//! atom and the builder rejects the whole system (returns `None`). We never
//! "approximate" a non-DL atom into the graph; mis-modeling is the one outcome
//! worse than saying *unknown*.
//!
//! # Edge encoding
//!
//! The standard difference-logic graph encodes `x - y <= c` as a directed edge
//! `y → x` with weight `c`. A path `v0 → v1 → … → vk` of total weight `W` then
//! certifies `vk - v0 <= W`, and a negative cycle `v0 → … → v0` certifies
//! `0 = v0 - v0 <= W < 0`, a contradiction ⇒ UNSAT.
//!
//! # Exact translation (integer / IDL — uses `strict_pred`)
//!
//! | atom            | rewritten as              | edges produced (`y→x : w`)          |
//! |-----------------|---------------------------|-------------------------------------|
//! | `x - y <= c`    | `x - y <= c`              | `y→x : c`                            |
//! | `x - y <  c`    | `x - y <= c-1`            | `y→x : c-1`                         |
//! | `x - y >= c`    | `y - x <= -c`             | `x→y : -c`                          |
//! | `x - y >  c`    | `y - x <= -c-1`           | `x→y : -c-1` (= `-(c+1)`)          |
//! | `x - y =  c`    | `x-y<=c ∧ y-x<=-c`        | `y→x : c`  and  `x→y : -c`          |
//!
//! # Exact translation (rational / RDL — strict bounds widened by ε)
//!
//! The rationals are dense, so `x - y < c` is **not** equivalent to any
//! non-strict `<=` bound. We model strict rational constraints soundly with an
//! infinitesimal `ε > 0`: `x - y < c` becomes `x - y <= c − ε`, i.e. the edge
//! weight is `(c, -1)` in the `(rational, ε-coeff)` lexicographic group. See
//! [`crate::rstar`]. A `<=` edge has ε-coeff `0`. This makes RDL strictness
//! exact rather than rejected.
//!
//! | atom            | rewritten as              | edge weight `(c, εk)`               |
//! |-----------------|---------------------------|-------------------------------------|
//! | `x - y <= c`    | —                         | `y→x : (c, 0)`                      |
//! | `x - y <  c`    | `x - y <= c − ε`          | `y→x : (c, -1)`                     |
//! | `x - y >= c`    | `y - x <= -c`             | `x→y : (-c, 0)`                     |
//! | `x - y >  c`    | `y - x <= -c − ε`         | `x→y : (-c, -1)`                    |
//! | `x - y =  c`    | two `<=` (both ε 0)       | `y→x : (c,0)` and `x→y : (-c,0)`   |

use crate::weight::IntWeight;

/// A comparison operator usable in a difference-logic atom.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Le,
    Lt,
    Eq,
    Ge,
    Gt,
}

/// A parsed difference-logic atom: `lhs - rhs ⋈ c`.
///
/// `rhs == None` encodes the var-vs-const degenerate form `lhs ⋈ c`, which is
/// translated as if `rhs` were the implicit zero variable `Z` (kept pinned to 0
/// by the engine). Variables are identified by an opaque `usize` index assigned
/// by the caller (e.g. a symbol-interning table). The implicit zero variable is
/// *not* one of these indices — the builder introduces it internally.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiffAtom<W> {
    /// The variable on the left of the difference (`x`).
    pub lhs: usize,
    /// The variable on the right of the difference (`y`); `None` for the
    /// var-vs-const form `x ⋈ c`.
    pub rhs: Option<usize>,
    /// The comparison operator.
    pub op: Op,
    /// The right-hand-side constant `c`.
    pub c: W,
}

impl<W> DiffAtom<W> {
    /// `x - y <= c`.
    pub fn diff_le(x: usize, y: usize, c: W) -> Self {
        Self {
            lhs: x,
            rhs: Some(y),
            op: Op::Le,
            c,
        }
    }

    /// `x - y ⋈ c` for an arbitrary operator.
    pub fn diff(x: usize, y: usize, op: Op, c: W) -> Self {
        Self {
            lhs: x,
            rhs: Some(y),
            op,
            c,
        }
    }

    /// `x ⋈ c` (var-vs-const degenerate form).
    pub fn var_const(x: usize, op: Op, c: W) -> Self {
        Self {
            lhs: x,
            rhs: None,
            op,
            c,
        }
    }
}

/// A single normalised difference edge `to - from <= weight` (graph edge
/// `from → to`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edge<W> {
    pub from: usize,
    pub to: usize,
    pub weight: W,
}

/// A difference constraint kept verbatim alongside its edges, so the engine can
/// re-check the *original* atom under a model (self-certification) rather than
/// trusting the translation.
#[derive(Clone, Debug)]
pub struct NormalizedConstraint<W> {
    /// `to - from <= weight` — the canonical `<=` form of (one half of) the atom.
    pub to: usize,
    pub from: usize,
    pub weight: W,
}

/// Lower a single integer/IDL atom to its `<=`-edge constraints, or `None` if
/// the atom is not a difference-logic atom.
///
/// Returns one constraint for `<=,<,>=,>`, two for `=`. The implicit zero
/// variable is supplied as `zero_var`.
pub fn lower_int_atom<W: IntWeight + Negate>(
    atom: &DiffAtom<W>,
    zero_var: usize,
) -> Option<Vec<NormalizedConstraint<W>>> {
    let x = atom.lhs;
    let y = atom.rhs.unwrap_or(zero_var);
    // A difference between a variable and itself is degenerate but well-formed:
    // x - x ⋈ c reduces to 0 ⋈ c. Keep it — the engine handles self-loops
    // (a self-loop with negative weight is a 1-edge negative cycle = UNSAT, and
    // a non-negative self-loop is trivially satisfiable / ignorable). It is a
    // genuine DL atom, so do not reject it.
    let c = atom.c.clone();
    Some(match atom.op {
        // x - y <= c   ⇒  to=x, from=y, w=c
        Op::Le => vec![NormalizedConstraint {
            to: x,
            from: y,
            weight: c,
        }],
        // x - y < c    ⇒  x - y <= c-1
        Op::Lt => vec![NormalizedConstraint {
            to: x,
            from: y,
            weight: c.strict_pred(),
        }],
        // x - y >= c   ⇒  y - x <= -c
        Op::Ge => vec![NormalizedConstraint {
            to: y,
            from: x,
            weight: neg_int(&c),
        }],
        // x - y > c    ⇒  y - x < -c  ⇒  y - x <= -c-1
        Op::Gt => vec![NormalizedConstraint {
            to: y,
            from: x,
            weight: neg_int(&c).strict_pred(),
        }],
        // x - y = c    ⇒  x - y <= c  AND  y - x <= -c
        Op::Eq => vec![
            NormalizedConstraint {
                to: x,
                from: y,
                weight: c.clone(),
            },
            NormalizedConstraint {
                to: y,
                from: x,
                weight: neg_int(&c),
            },
        ],
    })
}

/// Negate an integer weight via the group identity `-c = zero - ... ` — but we
/// implement it directly per concrete type below through a small helper so we do
/// not need a `Neg` bound on `Weight`. We obtain `-c` as `0 - c` using the fact
/// that `IntWeight` types are exactly `i64` / `BigInt`.
///
/// To stay generic we route through `strict_pred`/`add` only, which is not
/// enough for negation; instead require negation explicitly. We add it as a
/// free function specialised by a tiny trait to keep `Weight` minimal.
fn neg_int<W: IntWeight + Negate>(c: &W) -> W {
    c.negate()
}

/// Negation, factored out so [`Weight`](crate::weight::Weight) itself stays
/// limited to the ordered-monoid operations the SSSP core needs.
pub trait Negate {
    fn negate(&self) -> Self;
}

impl Negate for i64 {
    #[inline]
    fn negate(&self) -> Self {
        self.checked_neg()
            .expect("i64 difference-logic weight negation overflow; use BigInt")
    }
}

impl Negate for num_bigint::BigInt {
    #[inline]
    fn negate(&self) -> Self {
        -self
    }
}

impl Negate for num_rational::BigRational {
    #[inline]
    fn negate(&self) -> Self {
        -self
    }
}

/// Lower a single rational/RDL atom to `<=`-edge constraints over [`RStar`],
/// or `None` if the atom is not a difference-logic atom.
///
/// Strict bounds are widened by an infinitesimal `ε` (encoded as ε-coeff `-1`)
/// rather than rejected, making RDL strictness exact. See [`crate::rstar`] and
/// the rational translation table in this module's documentation.
///
/// [`RStar`]: crate::rstar::RStar
pub fn lower_rational_atom(
    atom: &DiffAtom<num_rational::BigRational>,
    zero_var: usize,
) -> Option<Vec<NormalizedConstraint<crate::rstar::RStar>>> {
    use crate::rstar::RStar;
    let x = atom.lhs;
    let y = atom.rhs.unwrap_or(zero_var);
    let c = atom.c.clone();
    let neg_c = -&c;
    Some(match atom.op {
        // x - y <= c  ⇒  edge to=x from=y weight (c, 0)
        Op::Le => vec![NormalizedConstraint {
            to: x,
            from: y,
            weight: RStar::finite(c),
        }],
        // x - y <  c  ⇒  x - y <= c - ε  ⇒  weight (c, -1)
        Op::Lt => vec![NormalizedConstraint {
            to: x,
            from: y,
            weight: RStar::new(c, -1),
        }],
        // x - y >= c  ⇒  y - x <= -c  ⇒  weight (-c, 0)
        Op::Ge => vec![NormalizedConstraint {
            to: y,
            from: x,
            weight: RStar::finite(neg_c),
        }],
        // x - y >  c  ⇒  y - x <= -c - ε  ⇒  weight (-c, -1)
        Op::Gt => vec![NormalizedConstraint {
            to: y,
            from: x,
            weight: RStar::new(neg_c, -1),
        }],
        // x - y =  c  ⇒  both non-strict halves, ε 0
        Op::Eq => vec![
            NormalizedConstraint {
                to: x,
                from: y,
                weight: RStar::finite(c),
            },
            NormalizedConstraint {
                to: y,
                from: x,
                weight: RStar::finite(neg_c),
            },
        ],
    })
}

/// Fast-lane twin of [`lower_rational_atom`], producing [`crate::istar::IStar`]
/// weights instead of [`crate::rstar::RStar`].
///
/// The table is IDENTICAL — same edge directions, same `ε` placement — because
/// `IStar` is the same `ℚ[ε]` group with the rational part narrowed to `i128`.
/// The only added behaviour is admission: any constant that is not an integer
/// within [`crate::istar::FAST_LANE_LIMIT`] returns `None`, so the caller falls
/// back to the exact lane rather than rounding. A differential test pins the two
/// lowerings against each other so the tables cannot drift apart.
pub fn lower_istar_atom(
    atom: &DiffAtom<num_rational::BigRational>,
    zero_var: usize,
) -> Option<Vec<NormalizedConstraint<crate::istar::IStar>>> {
    use crate::istar::IStar;
    let x = atom.lhs;
    let y = atom.rhs.unwrap_or(zero_var);
    let c = IStar::fits_fast_lane(&atom.c)?;
    let neg_c = c.checked_neg()?;
    Some(match atom.op {
        Op::Le => vec![NormalizedConstraint {
            to: x,
            from: y,
            weight: IStar::finite(c),
        }],
        Op::Lt => vec![NormalizedConstraint {
            to: x,
            from: y,
            weight: IStar::new(c, -1),
        }],
        Op::Ge => vec![NormalizedConstraint {
            to: y,
            from: x,
            weight: IStar::finite(neg_c),
        }],
        Op::Gt => vec![NormalizedConstraint {
            to: y,
            from: x,
            weight: IStar::new(neg_c, -1),
        }],
        Op::Eq => vec![
            NormalizedConstraint {
                to: x,
                from: y,
                weight: IStar::finite(c),
            },
            NormalizedConstraint {
                to: y,
                from: x,
                weight: IStar::finite(neg_c),
            },
        ],
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const Z: usize = 100; // stand-in zero var for tests

    fn one(cs: Vec<NormalizedConstraint<i64>>) -> (usize, usize, i64) {
        assert_eq!(cs.len(), 1);
        (cs[0].to, cs[0].from, cs[0].weight)
    }

    #[test]
    fn le_is_identity_edge() {
        // x - y <= 5  ⇒ edge y→x weight 5  (to=x, from=y)
        let a = DiffAtom::diff(0, 1, Op::Le, 5i64);
        assert_eq!(one(lower_int_atom(&a, Z).unwrap()), (0, 1, 5));
    }

    #[test]
    fn lt_subtracts_one_over_integers() {
        // x - y < 5  ⇒  x - y <= 4
        let a = DiffAtom::diff(0, 1, Op::Lt, 5i64);
        assert_eq!(one(lower_int_atom(&a, Z).unwrap()), (0, 1, 4));
    }

    #[test]
    fn ge_flips() {
        // x - y >= 5  ⇒  y - x <= -5  (to=y, from=x)
        let a = DiffAtom::diff(0, 1, Op::Ge, 5i64);
        assert_eq!(one(lower_int_atom(&a, Z).unwrap()), (1, 0, -5));
    }

    #[test]
    fn gt_flips_and_subtracts_one() {
        // x - y > 5  ⇒  y - x <= -6
        let a = DiffAtom::diff(0, 1, Op::Gt, 5i64);
        assert_eq!(one(lower_int_atom(&a, Z).unwrap()), (1, 0, -6));
    }

    #[test]
    fn eq_yields_two_edges() {
        // x - y = 5  ⇒  {x-y<=5, y-x<=-5}
        let a = DiffAtom::diff(0, 1, Op::Eq, 5i64);
        let cs = lower_int_atom(&a, Z).unwrap();
        assert_eq!(cs.len(), 2);
        assert_eq!((cs[0].to, cs[0].from, cs[0].weight), (0, 1, 5));
        assert_eq!((cs[1].to, cs[1].from, cs[1].weight), (1, 0, -5));
    }

    #[test]
    fn var_const_uses_zero_var() {
        // x <= 7  ⇒  x - Z <= 7
        let a = DiffAtom::var_const(0, Op::Le, 7i64);
        assert_eq!(one(lower_int_atom(&a, Z).unwrap()), (0, Z, 7));
    }
}
