//! The database-evolution driver: the proved kernel as a complete
//! stand-alone refutation checker.
//!
//! | Rust | Clean |
//! |---|---|
//! | [`Db`] (`Vec<Option<Constraint>>`) | the `List (Option Constraint)` database |
//! | [`Db::init`] | `VeriPbCore.liftDB` / `DbOk.init` |
//! | [`Db::get`] | `VeriPbCore.getO` |
//! | [`Db::delete`] | `VeriPbCore.setNone` / `DbOk.delete` |
//! | [`Db::derive`] | `VeriPbCore.DbOk.derive` |
//! | [`Op`] | `VeriPbCore.DStep` (one constructor per variant) |
//!
//! The mapping is one-way: every [`Op`] variant has a `DStep` constructor,
//! but `DStep` has two more — `mirS` and `mirVarS`, the two MIR cuts — with
//! no `Op` variant. A MIR step is therefore covered by `checker_sound` but
//! cannot yet be replayed through this stand-alone driver; the live checker
//! reaches those theorems through `veripb-checker`'s kernel bridge instead.
//! | [`Db::contradiction_at`] | the hypotheses of `VeriPbCore.checker_sound` |
//! | [`formula_satisfied`] | `VeriPbCore.holdsAllB` / `sat_of_witness` |
//!
//! `VeriPbCore.checker_sound` is the top-level theorem: a database reached
//! from `init` by `derive`/`delete` steps only, containing a stored
//! constraint with nonnegative coefficients and `coeffSum < degree`, refutes
//! the formula. [`Db`] maintains exactly that discipline: the only mutators
//! are [`Db::derive`] (which evaluates an [`Op`] tree through the guarded
//! rules, refusing to store anything a guard rejects) and [`Db::delete`].
//!
//! The mapping from a `pol` proof line's stack program to an [`Op`] tree is
//! direct (the stack machine is a post-order traversal of the tree).

use crate::{
    CoeffDomain, Constraint, GuardError, Lit, add, divide, literal_axiom, multiply,
    normalize::normalize, rup, saturate, weaken_degree,
};

/// One derivation step, as a tree over database references.
/// Mirrors `VeriPbCore.DStep`.
#[derive(Clone, Debug)]
pub enum Op<C = crate::Coeff> {
    /// A constraint already in the database (`DStep.ax`).
    FromDb(usize),
    /// The literal axiom `l + ~l >= 1` (`DStep.lit`).
    LiteralAxiom(Lit),
    /// A trivially-true constraint: nonnegative coefficients and degree at
    /// most zero (`DStep.trivS`, sound by `entails_trivial`). This is the
    /// shape of the pol literal axiom `l >= 0`.
    TrivialAxiom(Constraint<C>),
    /// Addition (`DStep.addS`).
    Add(Box<Op<C>>, Box<Op<C>>),
    /// Multiplication by a positive constant (`DStep.mulS`).
    Multiply(C, Box<Op<C>>),
    /// Ceiling division by a positive constant (`DStep.divS`).
    Divide(C, Box<Op<C>>),
    /// Saturation (`DStep.satS`).
    Saturate(Box<Op<C>>),
    /// Weaken the degree downward by a nonnegative amount (`DStep.wkS`).
    WeakenDegree(C, Box<Op<C>>),
    /// Normalize (`DStep.normS`, sound by `entails_normC`).
    Normalize(Box<Op<C>>),
    /// Reverse unit propagation with a checked trail certificate
    /// (`DStep.rupS`). `steps` and `conflict` index the RUP view: `0` is the
    /// negated target, `i + 1` is database id `db_ids[i]`.
    Rup {
        /// The claimed derived constraint (already normalized by the caller
        /// if desired); the replay validates it as written.
        target: Constraint<C>,
        /// Database ids of the constraints the trail references, in the
        /// order the certificate's indices assume.
        db_ids: Vec<usize>,
        /// The propagation trail: `(view index, literal)` pairs.
        steps: Vec<(usize, Lit)>,
        /// View index of the conflicting constraint.
        conflict: usize,
    },
}

/// Why a derivation was refused.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DeriveError {
    /// An `Op::FromDb` or RUP database id referenced an empty or
    /// out-of-range slot.
    MissingConstraint,
    /// A rule guard refused (overflow, non-positive factor, ...).
    Guard(GuardError),
    /// A RUP certificate failed its replay.
    Rup(rup::RupError),
}

impl From<GuardError> for DeriveError {
    fn from(e: GuardError) -> Self {
        DeriveError::Guard(e)
    }
}

/// An id-indexed constraint database with deletion holes.
#[derive(Clone, Debug)]
pub struct Db<C = crate::Coeff> {
    slots: Vec<Option<Constraint<C>>>,
}

impl<C> Default for Db<C> {
    fn default() -> Self {
        Db { slots: Vec::new() }
    }
}

impl<C: CoeffDomain> Db<C> {
    /// Load a formula: slot `i` holds formula constraint `i`.
    /// Mirrors `liftDB` (`DbOk.init`).
    pub fn init(formula: &[Constraint<C>]) -> Db<C> {
        Db {
            slots: formula.iter().cloned().map(Some).collect(),
        }
    }

    /// Fetch by id. Mirrors `getO`.
    pub fn get(&self, i: usize) -> Option<&Constraint<C>> {
        // Explicit length test rather than `.get(i)`. `slice::get` is opaque
        // to the verifier, so it hands back no `len` fact and the bounds
        // obligation is reported FAILED with a fabricated counterexample; the
        // comparison gives it the fact directly. Same access, same result.
        //
        // This pays only on an OWNED `Vec` field. On a `&[&T]` field the two
        // reads are independent and the prover cannot equate them -- measured,
        // it makes things worse -- which is why `RupCheck::get` keeps `.get`.
        if i < self.slots.len() {
            self.slots[i].as_ref()
        } else {
            None
        }
    }

    /// Number of slots (deleted ones included).
    pub fn len(&self) -> usize {
        self.slots.len()
    }

    /// True when no slot exists at all.
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    /// Delete a constraint. Mirrors `setNone` (`DbOk.delete`); out-of-range
    /// ids are a no-op, exactly as in the Clean definition.
    pub fn delete(&mut self, i: usize) {
        if i < self.slots.len() {
            self.slots[i] = None;
        }
    }

    /// Evaluate an [`Op`] tree against the current database.
    fn eval(&self, op: &Op<C>) -> Result<Constraint<C>, DeriveError> {
        match op {
            Op::FromDb(i) => self.get(*i).cloned().ok_or(DeriveError::MissingConstraint),
            Op::LiteralAxiom(l) => Ok(literal_axiom(*l)),
            Op::TrivialAxiom(c) => {
                if c.degree <= C::zero() && c.all_nonneg() {
                    Ok(c.clone())
                } else {
                    Err(DeriveError::Guard(GuardError::NotNormalized))
                }
            }
            Op::Add(a, b) => Ok(add(&self.eval(a)?, &self.eval(b)?)?),
            Op::Multiply(k, a) => Ok(multiply(k.clone(), &self.eval(a)?)?),
            Op::Divide(k, a) => Ok(divide(k.clone(), &self.eval(a)?)?),
            Op::Saturate(a) => Ok(saturate(&self.eval(a)?)?),
            Op::WeakenDegree(w, a) => Ok(weaken_degree(&self.eval(a)?, w.clone())?),
            Op::Normalize(a) => Ok(normalize(&self.eval(a)?)?),
            Op::Rup {
                target,
                db_ids,
                steps,
                conflict,
            } => {
                let view: Vec<&Constraint<C>> = db_ids
                    .iter()
                    .map(|&i| self.get(i).ok_or(DeriveError::MissingConstraint))
                    .collect::<Result<_, _>>()?;
                rup::check_rup(target, &view, steps, *conflict).map_err(DeriveError::Rup)?;
                Ok(target.clone())
            }
        }
    }

    /// Derive a constraint and store it in a fresh slot, returning its id.
    /// Mirrors `DbOk.derive`. Nothing enters the database except through
    /// the guarded rules.
    /// The id is taken BEFORE the push, not recovered as `len() - 1` after it.
    /// Both spell the same index, but `Vec::push` is opaque to the verifier, so
    /// nothing supplies `len >= 1` afterwards and the subtraction raised an
    /// `[overflow:sub]` obligation that FAILED — the one failing obligation in
    /// this module. Reading the length first needs no such fact: the id is the
    /// index the pushed element lands at, by definition of `push`.
    pub fn derive(&mut self, op: &Op<C>) -> Result<usize, DeriveError> {
        let c = self.eval(op)?;
        let id = self.slots.len();
        self.slots.push(Some(c));
        Ok(id)
    }

    /// Does slot `i` hold a stored contradiction? These are exactly the
    /// hypotheses of `VeriPbCore.checker_sound`: all coefficients
    /// nonnegative and `coeffSum < degree`, both judged in [`Wide`].
    pub fn contradiction_at(&self, i: usize) -> bool {
        match self.get(i) {
            None => false,
            Some(c) => c.all_nonneg() && c.coeff_sum() < c.degree.widen(),
        }
    }

    /// Scan for any stored contradiction.
    pub fn find_contradiction(&self) -> Option<usize> {
        (0..self.slots.len()).find(|&i| self.contradiction_at(i))
    }
}

/// Decide `HoldsAll` for a total assignment — the SAT-verdict leg.
/// Mirrors `VeriPbCore.holdsAllB`; a `true` result plus
/// `VeriPbCore.sat_of_witness` is the proof the formula is satisfiable.
pub fn formula_satisfied<C: CoeffDomain>(
    formula: &[Constraint<C>],
    assignment: &dyn Fn(u32) -> bool,
) -> bool {
    formula.iter().all(|c| c.holds(assignment))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Term;

    fn x() -> Lit {
        Lit::pos(0)
    }

    fn unit(l: Lit) -> Constraint {
        Constraint::new(vec![Term { coeff: 1, lit: l }], 1)
    }

    #[test]
    fn end_to_end_refutation_through_the_driver() {
        // The Rust image of VeriPbCore.ctrl_rup_refutation_end_to_end.
        let formula = [unit(x()), unit(x().negate())];
        let mut db = Db::init(&formula);
        let id = db
            .derive(&Op::Rup {
                target: Constraint::contradiction(),
                db_ids: vec![0, 1],
                steps: vec![(1, x())],
                conflict: 2,
            })
            .unwrap();
        assert_eq!(id, 2);
        assert!(db.contradiction_at(id));
        assert_eq!(db.find_contradiction(), Some(2));
    }

    #[test]
    fn pol_style_tree_derivation() {
        // x + y >= 2, divide by 2 after adding the literal axiom for z:
        // exercise a nontrivial Op tree end to end.
        let c0 = Constraint::new(
            vec![
                Term {
                    coeff: 1,
                    lit: Lit::pos(0),
                },
                Term {
                    coeff: 1,
                    lit: Lit::pos(1),
                },
            ],
            2,
        );
        let mut db = Db::init(std::slice::from_ref(&c0));
        let id = db
            .derive(&Op::Divide(
                2,
                Box::new(Op::Multiply(2, Box::new(Op::FromDb(0)))),
            ))
            .unwrap();
        let got = db.get(id).unwrap();
        assert_eq!(got, &c0);
    }

    #[test]
    fn deletion_leaves_a_hole_and_derivations_see_it() {
        let formula = [unit(x())];
        let mut db = Db::init(&formula);
        db.delete(0);
        assert!(db.get(0).is_none());
        assert_eq!(
            db.derive(&Op::FromDb(0)),
            Err(DeriveError::MissingConstraint)
        );
    }

    #[test]
    fn bad_rup_certificate_is_refused_and_stores_nothing() {
        let formula = [unit(x())];
        let mut db = Db::init(&formula);
        let before = db.len();
        let err = db.derive(&Op::Rup {
            target: Constraint::contradiction(),
            db_ids: vec![0],
            steps: vec![],
            conflict: 1,
        });
        assert_eq!(err, Err(DeriveError::Rup(rup::RupError::NoConflict)));
        assert_eq!(db.len(), before);
    }

    #[test]
    fn trivial_axiom_is_gated() {
        let mut db = Db::init(&[]);
        // l >= 0 is fine; l >= 1 is not an axiom; -1 l >= 0 is not normalized.
        let ok = Constraint::new(vec![Term { coeff: 1, lit: x() }], 0);
        assert!(db.derive(&Op::TrivialAxiom(ok)).is_ok());
        let not_trivial = Constraint::new(vec![Term { coeff: 1, lit: x() }], 1);
        assert!(db.derive(&Op::TrivialAxiom(not_trivial)).is_err());
        let negative = Constraint::new(
            vec![Term {
                coeff: -1,
                lit: x(),
            }],
            0,
        );
        assert!(db.derive(&Op::TrivialAxiom(negative)).is_err());
    }

    #[test]
    fn sat_leg_checks_the_whole_formula() {
        let formula = [unit(x()), unit(Lit::pos(1))];
        assert!(formula_satisfied(&formula, &|_| true));
        assert!(!formula_satisfied(&formula, &|v| v != 0));
    }
}
