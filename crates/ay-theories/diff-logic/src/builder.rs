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
    /// At least one atom was not a pure difference-logic atom; the system was
    /// rejected (fail-closed) and nothing was decided.
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

/// Build and check an integer / IDL system. Variables are `0..=max`; the zero
/// variable is `max+1` internally.
pub fn solve_int_atoms<W>(atoms: &[DiffAtom<W>]) -> BuildResult<W>
where
    W: IntWeight + Negate,
{
    let max = max_var(atoms);
    let zero_var = max.map_or(0, |m| m + 1);
    let n_vars = zero_var + 1;
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
            // Shift so zero_var reads 0, then drop it.
            let shift = model[zero_var].clone();
            let neg_shift = shift.negate();
            let real: Vec<W> = model[..zero_var]
                .iter()
                .map(|v| v.add(&neg_shift))
                .collect();
            BuildResult::Sat { model: real }
        }
        DiffResult::Unsat { cycle } => BuildResult::Unsat {
            cycle_len: cycle.len(),
        },
    }
}

/// Build and check a rational / RDL system over [`RStar`] weights.
///
/// Strict bounds are handled via the infinitesimal `ε`. On `Sat`, the [`RStar`]
/// potentials are realized into concrete rationals using a safe `δ` chosen by
/// [`pick_delta_from_slacks`].
pub fn solve_rational_atoms(atoms: &[DiffAtom<BigRational>]) -> BuildResult<BigRational> {
    let max = max_var(atoms);
    let zero_var = max.map_or(0, |m| m + 1);
    let n_vars = zero_var + 1;
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
            // value (g, k); see pick_delta_from_slacks.
            let slacks: Vec<(BigRational, i64)> = g
                .edges()
                .iter()
                .map(|e| {
                    let s = Weight::add(&model[e.from], &e.weight);
                    // s − model[e.to]
                    (&s.q - &model[e.to].q, s.eps - model[e.to].eps)
                })
                .collect();
            let delta = pick_delta_from_slacks(&slacks);
            let realized: Vec<BigRational> = model.iter().map(|r| r.realize_with(&delta)).collect();
            let shift = realized[zero_var].clone();
            let real: Vec<BigRational> = realized[..zero_var].iter().map(|v| v - &shift).collect();
            BuildResult::Sat { model: real }
        }
        DiffResult::Unsat { cycle } => BuildResult::Unsat {
            cycle_len: cycle.len(),
        },
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
}
