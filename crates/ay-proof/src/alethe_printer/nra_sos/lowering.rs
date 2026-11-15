// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked Alethe lowering of a native SOS certificate.
//!
//! The strict checker accepts `Σ c_k·F_k + bᵀ·G·b = rhs` with `rhs <= 0`
//! (and a strict factor with a positive multiplier when `rhs = 0`), where
//! every `F_k` is the oriented negation of a clause literal or the product of
//! two, `c_k >= 0` on inequalities and `G` is PSD. Under the negation of the
//! clause the left side is nonnegative (positive), a contradiction. Pinned
//! carcara 1.1.0 has every piece of that argument except the NONLINEAR steps:
//! `la_generic` reads a product of two non-constant terms as one opaque atom.
//! So each product and each Gram square is derived as its own comparison
//! over such an atom (`la_mult_pos`/`la_mult_neg`, see `facts`), every atom
//! is rewritten to one shared normal form by `poly_simp`, and one final
//! `la_generic` with the certificate's own coefficients refutes the negated
//! clause. The id's step is a resolution concluding exactly the clause.
//!
//! The lowering renders a step only after the strict checker accepts it. It
//! then derives every row from the PRINTED clause (the text the step's `hole`
//! would otherwise assert, authored spellings included), and every
//! arithmetic step it writes is replayed over its exact text by the
//! pinned-checker judgements AND must refute its hypotheses over the reals on
//! its own (see `emit`), so no shipped step leans on the pinned checker's
//! sort-blind integer strengthening and no spelling channel can make it ship
//! a step that is not a theorem. Anything it cannot render (mixed
//! `Int`/`Real` rows, an unreadable literal, the output cap) returns `None`,
//! and the caller prints the honest `hole`.

mod emit;
mod facts;

use crate::alethe_printer::{la_generic_surface, split_application, AlethePrinter};
use ay_core::{NraSosCertificate, NraSosOrigin, NraSosRational, ProofId, Sort, TermData, TermId};
use emit::{negated, Emitter};
use facts::Factor;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::BTreeMap;

/// The step(s) that close the lowering under the step's own id: one
/// `resolution` over the refutation and its derived facts, or, when the
/// refutation is the only premise, [`lone_refutation_tail`].
fn closing_steps(id: ProofId, literals: &[String], kept: &[usize], premises: &[String]) -> String {
    match premises {
        [refutation] => lone_refutation_tail(id, literals, kept, refutation),
        _ => format!(
            "(step {id} (cl {}) :rule resolution :premises ({}))",
            literals.join(" "),
            premises.join(" ")
        ),
    }
}

/// The closing steps when the refutation is the only premise.
///
/// Carcara's `resolution` needs at least two premises, so a lone `la_generic`
/// refutation cannot be closed by one: `(- a b c)` against three pins printed
/// `(step t4 .. :rule resolution :premises (t4.sos.g0))`, which carcara
/// rejects. The refutation concludes the clause literals at `kept` (the
/// readable ones, in clause order), so `weakening` appends the dropped ones
/// and `reordering` restores the clause order under the step's own id.
fn lone_refutation_tail(
    id: ProofId,
    literals: &[String],
    kept: &[usize],
    refutation: &str,
) -> String {
    let mut out = String::new();
    let mut premise = refutation.to_string();
    if kept.len() < literals.len() {
        let mut weakened: Vec<&str> = kept.iter().map(|&at| literals[at].as_str()).collect();
        weakened.extend(
            (0..literals.len())
                .filter(|at| !kept.contains(at))
                .map(|at| literals[at].as_str()),
        );
        let name = format!("{id}.sos.w");
        out.push_str(&format!(
            "(step {name} (cl {}) :rule weakening :premises ({premise}))\n",
            weakened.join(" ")
        ));
        premise = name;
    }
    out.push_str(&format!(
        "(step {id} (cl {}) :rule reordering :premises ({premise}))",
        literals.join(" ")
    ));
    out
}

fn decode(value: &NraSosRational) -> Option<BigRational> {
    (!value.denominator.is_zero())
        .then(|| BigRational::new(value.numerator.clone(), value.denominator.clone()))
}

/// The printed source comparison `(op a b)` a clause literal is the negation
/// of, as the pinned `la_generic` reads it.
fn printed_source(literal: &str) -> Option<(&'static str, String, String)> {
    const RELATIONS: [&str; 5] = ["<=", "<", ">=", ">", "="];
    let sides = |text: &str, relation: &str| match split_application(text, relation)?.as_slice() {
        [left, right] => Some((left.clone(), right.clone())),
        _ => None,
    };
    if let Some(inner) = split_application(literal, "not") {
        let [inner] = inner.as_slice() else {
            return None;
        };
        return RELATIONS.iter().find_map(|relation| {
            sides(inner, relation).map(|(left, right)| (*relation, left, right))
        });
    }
    let (relation, negation) = [("<=", ">"), ("<", ">="), (">=", "<"), (">", "<=")]
        .into_iter()
        .find(|(relation, _)| sides(literal, relation).is_some())?;
    let (left, right) = sides(literal, relation)?;
    Some((negation, left, right))
}

/// The certificate's rows, decoded and aggregated, in the lowering's one
/// arithmetic sort.
struct Plan {
    literal_coefficients: Vec<BigRational>,
    products: BTreeMap<(usize, usize), BigRational>,
    /// `(weight, form)`: each Gram square with an integral, non-constant form.
    squares: Vec<(BigRational, Vec<BigRational>)>,
    real: bool,
}

impl AlethePrinter<'_> {
    /// The checked multi-step rendering of one native SOS step, or `None`.
    pub(super) fn format_nra_sos_lowering(
        &self,
        id: ProofId,
        clause: &[TermId],
        certificate: &NraSosCertificate,
    ) -> Option<String> {
        // Render only what the strict checker authenticates. Its exact replay
        // is printer work: it is charged to, and stopped by, this printer's
        // budget (its own fixed meters still bound it when none is set).
        crate::checker::validate_nra_sos_with_progress(
            self.terms,
            id,
            clause,
            certificate,
            &mut |work, _| {
                self.charge(work as u64);
                !self.work_budget_exhausted()
            },
        )
        .ok()?;
        let mut plan = self.nra_sos_plan(clause, certificate)?;
        let literals: Vec<String> = clause
            .iter()
            .map(|&literal| {
                let mut text = String::new();
                self.write_derived_literal_into(&mut text, literal);
                text
            })
            .collect();
        self.nra_sos_orient_equalities(&mut plan.literal_coefficients, clause, &literals);
        let mut emitter = Emitter::new(format!("{id}.sos"), plan.real);
        // Each product factor, and the bridge from its clause literal.
        let mut factors: BTreeMap<usize, Factor> = BTreeMap::new();
        let mut bridges = Vec::new();
        for &(left, right) in plan.products.keys() {
            for position in [left, right] {
                if factors.contains_key(&position) {
                    continue;
                }
                let factor = self.nra_sos_factor(&emitter, &literals[position])?;
                let bridge = emitter.la_generic(vec![
                    (literals[position].clone(), BigRational::one()),
                    (factor.fact.clone(), BigRational::one()),
                ])?;
                bridges.push(bridge.name);
                factors.insert(position, factor);
            }
        }
        let mut rows: Vec<(String, BigRational)> = Vec::new();
        let mut kept = Vec::with_capacity(literals.len());
        for (position, (literal, coefficient)) in
            literals.iter().zip(&plan.literal_coefficients).enumerate()
        {
            // A literal `la_generic` cannot read can only be an unused one (a
            // used source is an order comparison or a negated equality); the
            // final resolution weakens it back in.
            if la_generic_surface::readings::printed_la_generic_atom_residual(
                &[literal.as_str()],
                &[BigRational::one()],
            )
            .is_some()
            {
                rows.push((literal.clone(), coefficient.clone()));
                kept.push(position);
            } else if !coefficient.is_zero() {
                return None;
            }
        }
        // Premise order keeps the final resolution a greedy chain: each
        // product clause is cut by the refutation before its bridges cut it.
        let mut derived = Vec::new();
        for (&(left, right), coefficient) in &plan.products {
            let product = facts::product(&mut emitter, factors.get(&left)?, factors.get(&right)?)?;
            rows.push((negated(&product.literal), coefficient.clone()));
            derived.push(product.step);
        }
        derived.extend(bridges);
        for (weight, form) in &plan.squares {
            let form = self.nra_sos_form(&emitter, &certificate.basis, form)?;
            let square = facts::square(&mut emitter, &form)?;
            rows.push((negated(&square.literal), weight.clone()));
            derived.push(square.step);
        }
        let refutation = emitter.la_generic(rows)?;
        let mut premises = vec![refutation.name];
        premises.extend(derived);
        premises.extend(refutation.equalities);
        let mut out = format!(
            "; {id} ay-nra-sos: native certificate lowered to checked la_mult/la_generic/poly_simp steps\n"
        );
        out.push_str(&emitter.finish());
        out.push_str(&closing_steps(id, &literals, &kept, &premises));
        self.charge(out.len() as u64);
        Some(out)
    }

    /// Decode and aggregate the certificate, and fix its one arithmetic sort.
    fn nra_sos_plan(&self, clause: &[TermId], certificate: &NraSosCertificate) -> Option<Plan> {
        let mut literal_coefficients = vec![BigRational::zero(); clause.len()];
        let mut products: BTreeMap<(usize, usize), BigRational> = BTreeMap::new();
        for term in &certificate.terms {
            let coefficient = decode(&term.multiplier)?;
            match term.origin {
                NraSosOrigin::ClauseLiteral { position } => {
                    *literal_coefficients.get_mut(position as usize)? += coefficient;
                }
                NraSosOrigin::Product { left, right } => {
                    let key = (left.min(right) as usize, left.max(right) as usize);
                    *products.entry(key).or_insert_with(BigRational::zero) += coefficient;
                }
            }
        }
        products.retain(|_, coefficient| !coefficient.is_zero());
        let gram = certificate
            .gram
            .iter()
            .map(|row| row.iter().map(decode).collect::<Option<Vec<_>>>())
            .collect::<Option<Vec<_>>>()?;
        // A square of a constant form only adds a positive constant; dropping
        // it keeps the combination contradictory.
        let squares: Vec<(BigRational, Vec<BigRational>)> = facts::gram_squares(&gram)?
            .into_iter()
            .filter(|(_, form)| form.iter().skip(1).any(|value| !value.is_zero()))
            .map(|(weight, form)| facts::integral(weight, form))
            .collect();
        let mut sorts: Vec<Sort> = Vec::new();
        for (position, coefficient) in literal_coefficients.iter().enumerate() {
            if !coefficient.is_zero() {
                sorts.push(self.nra_sos_literal_sort(*clause.get(position)?)?);
            }
        }
        for &(left, right) in products.keys() {
            sorts.push(self.nra_sos_literal_sort(*clause.get(left)?)?);
            sorts.push(self.nra_sos_literal_sort(*clause.get(right)?)?);
        }
        for (_, form) in &squares {
            for (index, value) in form.iter().enumerate() {
                if !value.is_zero() {
                    for &variable in certificate.basis.get(index)? {
                        sorts.push(self.terms.sort(variable).clone());
                    }
                }
            }
        }
        let sort = sorts.first()?.clone();
        if sorts.iter().any(|other| *other != sort) || !matches!(sort, Sort::Int | Sort::Real) {
            return None;
        }
        Some(Plan {
            literal_coefficients,
            products,
            squares,
            real: sort == Sort::Real,
        })
    }

    /// The arithmetic sort of the comparison a clause literal negates.
    fn nra_sos_literal_sort(&self, literal: TermId) -> Option<Sort> {
        let mut atom = literal;
        while let TermData::Not(inner) = self.terms.get(atom) {
            atom = *inner;
        }
        match self.terms.get(atom) {
            TermData::App(_, args) => Some(self.terms.sort(*args.first()?).clone()),
            _ => None,
        }
    }

    /// The certificate signs an equality row by the TERM DAG's side order,
    /// but the pinned `la_generic` reads the PRINTED literal, and an authored
    /// spelling may state the sides the other way round (`(= (* x y) 2)` for
    /// the DAG's `(= 2 (* x y))`): that row is the negation, so its
    /// multiplier is negated with it.
    fn nra_sos_orient_equalities(
        &self,
        coefficients: &mut [BigRational],
        clause: &[TermId],
        literals: &[String],
    ) {
        for ((coefficient, &literal), printed) in coefficients.iter_mut().zip(clause).zip(literals)
        {
            if !coefficient.is_zero() && self.nra_sos_equality_reversed(literal, printed) {
                *coefficient = -coefficient.clone();
            }
        }
    }

    /// Whether a literal's PRINTED equality source states its term DAG
    /// source's two sides the other way round: `left - right` of each, read
    /// as a polynomial over the printed atoms, is exactly the other's
    /// negation (a zero row reads as both, and its sign is immaterial).
    /// Anything else keeps the certificate's sign; the replayed `la_generic`
    /// still decides every row.
    fn nra_sos_equality_reversed(&self, literal: TermId, printed: &str) -> bool {
        let mut atom = literal;
        while let TermData::Not(inner) = self.terms.get(atom) {
            atom = *inner;
        }
        let TermData::App(symbol, args) = self.terms.get(atom) else {
            return false;
        };
        let ([left, right], Some(("=", shown_left, shown_right))) =
            (args.as_slice(), printed_source(printed))
        else {
            return false;
        };
        if symbol.name() != "=" {
            return false;
        }
        let difference = |left: &str, right: &str| {
            la_generic_surface::readings::printed_polynomial(&format!("(- {left} {right})"))
        };
        let (Some((dag, dag_constant)), Some((shown, shown_constant))) = (
            difference(&self.format_term(*left), &self.format_term(*right)),
            difference(&shown_left, &shown_right),
        ) else {
            return false;
        };
        dag.len() == shown.len()
            && dag
                .iter()
                .all(|(monomial, value)| shown.get(monomial) == Some(&-value))
            && shown_constant == -dag_constant
    }

    /// The oriented factor of an inequality source: `(- a b) >= 0` for
    /// `a >= b`, `(- b a) >= 0` for `a <= b`, strict for `>` / `<`.
    fn nra_sos_factor(&self, emitter: &Emitter, literal: &str) -> Option<Factor> {
        let (relation, left, right) = printed_source(literal)?;
        let (oriented, strict) = match relation {
            ">=" => (format!("(- {left} {right})"), false),
            ">" => (format!("(- {left} {right})"), true),
            "<=" => (format!("(- {right} {left})"), false),
            "<" => (format!("(- {right} {left})"), true),
            _ => return None,
        };
        let fact = format!(
            "({} {oriented} {})",
            if strict { ">" } else { ">=" },
            emitter.zero()
        );
        Some(Factor {
            oriented,
            strict,
            fact,
        })
    }

    /// `Σ form_j·basis_j` spelled over the printed basis variables.
    fn nra_sos_form(
        &self,
        emitter: &Emitter,
        basis: &[Vec<TermId>],
        form: &[BigRational],
    ) -> Option<String> {
        let mut parts = Vec::new();
        for (monomial, coefficient) in basis.iter().zip(form) {
            if coefficient.is_zero() {
                continue;
            }
            let variables: Vec<String> = monomial.iter().map(|&v| self.format_term(v)).collect();
            let product = match variables.as_slice() {
                [] => {
                    parts.push(emitter.numeral(coefficient)?);
                    continue;
                }
                [single] => single.clone(),
                _ => format!("(* {})", variables.join(" ")),
            };
            parts.push(if coefficient.is_one() {
                product
            } else if (-coefficient).is_one() {
                format!("(- {product})")
            } else {
                format!("(* {} {product})", emitter.numeral(coefficient)?)
            });
        }
        match parts.len() {
            0 => None,
            1 => parts.pop(),
            _ => Some(format!("(+ {})", parts.join(" "))),
        }
    }
}
