//! Deterministic property tests for the difference-logic engine, independent of
//! any external oracle.
//!
//! These rely on the engine's *self-certification*: a `Sat` verdict's model is
//! re-substituted into every original atom here (a second, independent check on
//! top of the engine's internal `debug_assert!`s), and an `Unsat` verdict is
//! sanity-checked for being a genuinely over-constrained system where possible.
//! Self-certification alone guarantees soundness even without z3.

use ay_diff_logic::atom::{lower_int_atom, Op};
use ay_diff_logic::{solve_int_atoms, solve_rational_atoms, BuildResult, DiffAtom};
use num_rational::BigRational;
use proptest::prelude::*;

/// Directly check that an integer model satisfies an atom `x − y ⋈ c`.
fn int_atom_holds(atom: &DiffAtom<i64>, model: &[i64]) -> bool {
    let x = model[atom.lhs];
    // var-vs-const: rhs is the implicit zero var, value 0 (model is shifted so).
    let y = atom.rhs.map_or(0, |r| model[r]);
    let d = x - y;
    match atom.op {
        Op::Le => d <= atom.c,
        Op::Lt => d < atom.c,
        Op::Eq => d == atom.c,
        Op::Ge => d >= atom.c,
        Op::Gt => d > atom.c,
    }
}

/// Directly check that a rational model satisfies an atom.
fn rat_atom_holds(atom: &DiffAtom<BigRational>, model: &[BigRational]) -> bool {
    let x = &model[atom.lhs];
    let zero = BigRational::from_integer(0.into());
    let y = atom.rhs.map_or(&zero, |r| &model[r]);
    let d = x - y;
    match atom.op {
        Op::Le => d <= atom.c,
        Op::Lt => d < atom.c,
        Op::Eq => d == atom.c,
        Op::Ge => d >= atom.c,
        Op::Gt => d > atom.c,
    }
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        Just(Op::Le),
        Just(Op::Lt),
        Just(Op::Eq),
        Just(Op::Ge),
        Just(Op::Gt),
    ]
}

/// Random integer atom over `n_vars` variables, occasionally var-vs-const.
fn int_atom_strategy(n_vars: usize) -> impl Strategy<Value = DiffAtom<i64>> {
    (
        0..n_vars,
        0..n_vars,
        op_strategy(),
        -20i64..=20,
        any::<bool>(),
    )
        .prop_map(move |(x, y, op, c, var_const)| {
            if var_const {
                DiffAtom::var_const(x, op, c)
            } else {
                DiffAtom::diff(x, y, op, c)
            }
        })
}

fn rat_atom_strategy(n_vars: usize) -> impl Strategy<Value = DiffAtom<BigRational>> {
    (
        0..n_vars,
        0..n_vars,
        op_strategy(),
        -20i64..=20,
        1i64..=8,
        any::<bool>(),
    )
        .prop_map(move |(x, y, op, num, den, var_const)| {
            let c = BigRational::new(num.into(), den.into());
            if var_const {
                DiffAtom::var_const(x, op, c)
            } else {
                DiffAtom::diff(x, y, op, c)
            }
        })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    /// On a random IDL system, a Sat model must satisfy every original atom
    /// (independent re-check beyond the engine's internal self-cert).
    #[test]
    fn idl_sat_model_satisfies_all_atoms(
        atoms in prop::collection::vec(int_atom_strategy(5), 0..15)
    ) {
        if let BuildResult::Sat { model } = solve_int_atoms(&atoms) {
            for a in &atoms {
                prop_assert!(
                    int_atom_holds(a, &model),
                    "model {:?} violates atom {:?}", model, a
                );
            }
        }
    }

    /// On a random RDL system, a Sat model must satisfy every original atom.
    #[test]
    fn rdl_sat_model_satisfies_all_atoms(
        atoms in prop::collection::vec(rat_atom_strategy(5), 0..15)
    ) {
        if let BuildResult::Sat { model } = solve_rational_atoms(&atoms) {
            for a in &atoms {
                prop_assert!(
                    rat_atom_holds(a, &model),
                    "rational model {:?} violates atom {:?}", model, a
                );
            }
        }
    }

    /// Adding more constraints can only move sat→unsat, never unsat→sat
    /// (monotonicity). If a prefix is unsat, the whole system is unsat.
    #[test]
    fn idl_unsat_is_monotone(
        atoms in prop::collection::vec(int_atom_strategy(5), 1..15),
        cut in 1usize..15,
    ) {
        let cut = cut.min(atoms.len());
        let prefix = &atoms[..cut];
        if let BuildResult::Unsat { .. } = solve_int_atoms(prefix) {
            prop_assert!(
                matches!(solve_int_atoms(&atoms), BuildResult::Unsat { .. }),
                "prefix unsat but full system not unsat"
            );
        }
    }

    /// `=` is exactly the conjunction of `<=` and `>=` (translation sanity).
    #[test]
    fn idl_eq_equals_le_and_ge(
        x in 0usize..4, y in 0usize..4, c in -10i64..=10,
        extra in prop::collection::vec(int_atom_strategy(4), 0..8),
    ) {
        let mut with_eq = extra.clone();
        with_eq.push(DiffAtom::diff(x, y, Op::Eq, c));

        let mut with_le_ge = extra;
        with_le_ge.push(DiffAtom::diff(x, y, Op::Le, c));
        with_le_ge.push(DiffAtom::diff(x, y, Op::Ge, c));

        let a = matches!(solve_int_atoms(&with_eq), BuildResult::Unsat { .. });
        let b = matches!(solve_int_atoms(&with_le_ge), BuildResult::Unsat { .. });
        prop_assert_eq!(a, b, "Eq and (Le∧Ge) disagree on sat/unsat");
    }
}

/// The atom translator must never reject a well-formed difference atom (every
/// op, both forms). This pins the fail-closed boundary to *non*-DL atoms only.
#[test]
fn all_well_formed_int_atoms_lower() {
    for op in [Op::Le, Op::Lt, Op::Eq, Op::Ge, Op::Gt] {
        let two = DiffAtom::diff(0, 1, op, 3i64);
        assert!(
            lower_int_atom(&two, 99).is_some(),
            "rejected two-var {op:?}"
        );
        let one = DiffAtom::var_const(0, op, 3i64);
        assert!(
            lower_int_atom(&one, 99).is_some(),
            "rejected var-const {op:?}"
        );
    }
}
