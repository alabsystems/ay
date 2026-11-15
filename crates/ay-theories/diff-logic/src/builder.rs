//! `from_atoms` builders: turn a list of [`DiffAtom`]s into a feasibility
//! verdict, fail-closed.
//!
//! The builder owns the implicit zero variable. Callers number their real
//! variables `0..n`; the builder reserves index `n` (one past the largest
//! variable mentioned) as the zero variable `Z`. `Z` needs no explicit pinning:
//! difference logic only ever constrains *differences*, so a model is unique
//! only up to a global additive shift. The var-vs-const form `x <= c` lowers to
//! `x - Z <= c`; the returned model is then *shifted* so that `Z` reads exactly
//! `0`, which makes the var-vs-const readings absolute (`x`'s value really is
//! its bound-relative value, not an arbitrary offset).

use crate::atom::{lower_int_atom, lower_rational_atom, DiffAtom, Negate};
use crate::graph::{DiffGraph, DiffResult};
use crate::rstar::{pick_delta_from_slacks, RStar};
use crate::weight::{IntWeight, Weight};

use num_rational::BigRational;

/// Outcome of building and checking a system of atoms.
#[derive(Clone, Debug)]
pub enum BuildResult<W> {
    /// All atoms were valid difference-logic atoms and the system is `Sat`,
    /// carrying a per-variable model over the caller's variable indices
    /// `0..n_vars` (the implicit zero variable is dropped and the model is
    /// shifted so its reading would be `0`).
    Sat { model: Vec<W> },
    /// All atoms valid, system `Unsat`. `cycle` indexes into the *internal*
    /// edge list; use [`crate::graph::DiffGraph`] directly if you need the edge
    /// detail. Here it is reported as the count for convenience.
    Unsat { cycle_len: usize },
    /// At least one atom was not a pure difference-logic atom, or the system
    /// is beyond the engine's limits (a variable index too large for the
    /// implicit zero variable to follow it, or [`crate::graph::VAR_LIMIT`] or
    /// more vertices); the system was rejected (fail-closed) and nothing was
    /// decided.
    Rejected,
}

/// Highest variable index mentioned by any atom (real vars only), or `None` if
/// no atom references a variable.
fn max_var<W>(atoms: &[DiffAtom<W>]) -> Option<usize> {
    atoms
        .iter()
        .flat_map(|a| std::iter::once(a.lhs).chain(a.rhs))
        .max()
}

/// The implicit zero variable (`max + 1`, or `0` when no atom names a
/// variable) and the vertex count (`zero_var + 1`), or `None` when the largest
/// variable index leaves no room for them.
fn zero_var_and_count<W>(atoms: &[DiffAtom<W>]) -> Option<(usize, usize)> {
    let zero_var = match max_var(atoms) {
        Some(m) => m.checked_add(1)?,
        None => 0,
    };
    let n_vars = zero_var.checked_add(1)?;
    Some((zero_var, n_vars))
}

/// Build and check an integer / IDL system. Variables are `0..=max`; the zero
/// variable is `max+1` internally.
pub fn solve_int_atoms<W>(atoms: &[DiffAtom<W>]) -> BuildResult<W>
where
    W: IntWeight + Negate,
{
    let Some((zero_var, n_vars)) = zero_var_and_count(atoms) else {
        return BuildResult::Rejected;
    };
    let mut g = DiffGraph::<W>::new(n_vars);

    for a in atoms {
        match lower_int_atom(a, zero_var) {
            Some(cs) => {
                for c in cs {
                    // c.to - c.from <= c.weight  ⇒ add_constraint(x=to, y=from, w)
                    g.add_constraint(c.to, c.from, c.weight);
                }
            }
            None => return BuildResult::Rejected,
        }
    }

    finish_int(g, zero_var)
}

fn finish_int<W>(g: DiffGraph<W>, zero_var: usize) -> BuildResult<W>
where
    W: Weight + Negate,
{
    match g.check() {
        DiffResult::Sat { model } => {
            // Shift so zero_var reads 0, then drop it. The model has one entry
            // per vertex and zero_var is the last vertex, so both reads exist;
            // a model without them is refused rather than trusted.
            let (Some(shift), Some(real_part)) = (model.get(zero_var), model.get(..zero_var))
            else {
                return BuildResult::Rejected;
            };
            // A shift with no negation in the weight's width (`i64::MIN`)
            // cannot be subtracted: refuse rather than report a wrong model.
            let Some(neg_shift) = shift.negate() else {
                return BuildResult::Rejected;
            };
            let real: Vec<W> = real_part.iter().map(|v| v.add(&neg_shift)).collect();
            BuildResult::Sat { model: real }
        }
        DiffResult::Unsat { cycle } => BuildResult::Unsat {
            cycle_len: cycle.len(),
        },
        DiffResult::Refused => BuildResult::Rejected,
    }
}

/// Build and check a rational / RDL system over [`RStar`] weights.
///
/// Strict bounds are handled via the infinitesimal `ε`. On `Sat`, the [`RStar`]
/// potentials are realized into concrete rationals using a safe `δ` chosen by
/// [`pick_delta_from_slacks`].
pub fn solve_rational_atoms(atoms: &[DiffAtom<BigRational>]) -> BuildResult<BigRational> {
    let Some((zero_var, n_vars)) = zero_var_and_count(atoms) else {
        return BuildResult::Rejected;
    };
    let mut g = DiffGraph::<RStar>::new(n_vars);

    for a in atoms {
        match lower_rational_atom(a, zero_var) {
            Some(cs) => {
                for c in cs {
                    g.add_constraint(c.to, c.from, c.weight);
                }
            }
            None => return BuildResult::Rejected,
        }
    }

    match g.check() {
        DiffResult::Sat { model } => {
            // Choose δ from the *actual constraint slacks* so realizing ε := δ
            // keeps every (possibly strict) constraint satisfied. For edge
            // from→to : w the slack is dist[from] + w − dist[to], an R*-nonneg
            // value (g, k); see pick_delta_from_slacks. An endpoint missing
            // from the model, or an ε-count difference outside i64, is refused
            // rather than realized with a wrong δ.
            let mut slacks: Vec<(BigRational, i64)> = Vec::new();
            for e in g.edges() {
                let (Some(from), Some(to)) = (model.get(e.from), model.get(e.to)) else {
                    return BuildResult::Rejected;
                };
                let s = Weight::add(from, &e.weight);
                // s − model[e.to]
                let Some(eps) = s.eps.checked_sub(to.eps) else {
                    return BuildResult::Rejected;
                };
                slacks.push((&s.q - &to.q, eps));
            }
            let delta = pick_delta_from_slacks(&slacks);
            let realized: Vec<BigRational> = model.iter().map(|r| r.realize_with(&delta)).collect();
            let (Some(shift), Some(real_part)) = (realized.get(zero_var), realized.get(..zero_var))
            else {
                return BuildResult::Rejected;
            };
            let real: Vec<BigRational> = real_part.iter().map(|v| v - shift).collect();
            BuildResult::Sat { model: real }
        }
        DiffResult::Unsat { cycle } => BuildResult::Unsat {
            cycle_len: cycle.len(),
        },
        DiffResult::Refused => BuildResult::Rejected,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::Op;
    use num_traits::FromPrimitive;

    fn ratom(x: usize, y: usize, op: Op, n: i64, d: i64) -> DiffAtom<BigRational> {
        DiffAtom::diff(x, y, op, BigRational::new(n.into(), d.into()))
    }

    #[test]
    fn int_sat_with_var_const_absolute_model() {
        // x <= 3, y <= 4, x - y <= 1
        let atoms = vec![
            DiffAtom::var_const(0, Op::Le, 3i64),
            DiffAtom::var_const(1, Op::Le, 4i64),
            DiffAtom::diff(0, 1, Op::Le, 1i64),
        ];
        match solve_int_atoms(&atoms) {
            BuildResult::Sat { model } => {
                assert!(model[0] <= 3, "x={} should be <=3", model[0]);
                assert!(model[1] <= 4, "y={} should be <=4", model[1]);
                assert!(model[0] - model[1] <= 1);
            }
            other => panic!("expected sat, got {other:?}"),
        }
    }

    #[test]
    fn int_unsat_eq_chain() {
        // x - y = 1, y - z = 1, z - x = 1  ⇒ sum 3 ≠ 0 ⇒ unsat
        let atoms = vec![
            DiffAtom::diff(0, 1, Op::Eq, 1i64),
            DiffAtom::diff(1, 2, Op::Eq, 1i64),
            DiffAtom::diff(2, 0, Op::Eq, 1i64),
        ];
        assert!(matches!(solve_int_atoms(&atoms), BuildResult::Unsat { .. }));
    }

    #[test]
    fn int_strict_makes_unsat() {
        // x - y < 1 and y - x < 0 over integers: x-y<=0, y-x<=-1 ⇒ cycle -1 unsat
        let atoms = vec![
            DiffAtom::diff(0, 1, Op::Lt, 1i64),
            DiffAtom::diff(1, 0, Op::Lt, 0i64),
        ];
        assert!(matches!(solve_int_atoms(&atoms), BuildResult::Unsat { .. }));
    }

    #[test]
    fn rational_strict_sat() {
        // x - y < 1, y - x < 0  over rationals: feasible (e.g. x-y = 0.5)
        let atoms = vec![ratom(0, 1, Op::Lt, 1, 1), ratom(1, 0, Op::Lt, 0, 1)];
        match solve_rational_atoms(&atoms) {
            BuildResult::Sat { model } => {
                let diff = &model[0] - &model[1];
                assert!(diff < BigRational::from_f64(1.0).unwrap());
                assert!(diff > BigRational::from_f64(0.0).unwrap());
            }
            other => panic!("expected sat, got {other:?}"),
        }
    }

    #[test]
    fn rational_strict_unsat() {
        // x - y < 1 and y - x <= -1  ⇒ x-y<1 and x-y>=1 ⇒ unsat
        let atoms = vec![ratom(0, 1, Op::Lt, 1, 1), ratom(1, 0, Op::Le, -1, 1)];
        assert!(matches!(
            solve_rational_atoms(&atoms),
            BuildResult::Unsat { .. }
        ));
    }

    #[test]
    fn variable_index_with_no_room_for_the_zero_variable_is_rejected() {
        // `max + 1` (the zero variable) or `zero_var + 1` (the vertex count)
        // overflowed here; the system is now rejected, not decided.
        for v in [usize::MAX, usize::MAX - 1] {
            let int = vec![DiffAtom::diff(v, 0, Op::Le, 1i64)];
            assert!(matches!(solve_int_atoms(&int), BuildResult::Rejected));
            let rat = vec![ratom(v, 0, Op::Le, 1, 1)];
            assert!(matches!(solve_rational_atoms(&rat), BuildResult::Rejected));
        }
    }

    #[test]
    fn system_at_the_vertex_limit_is_rejected() {
        // Variable `VAR_LIMIT` makes the zero variable `VAR_LIMIT + 1` and the
        // vertex count `VAR_LIMIT + 2`: refused by the graph, rejected here.
        let v = crate::graph::VAR_LIMIT;
        let int = vec![DiffAtom::diff(v, 0, Op::Le, 1i64)];
        assert!(matches!(solve_int_atoms(&int), BuildResult::Rejected));
        let rat = vec![ratom(v, 0, Op::Le, 1, 1)];
        assert!(matches!(solve_rational_atoms(&rat), BuildResult::Rejected));
    }
}
