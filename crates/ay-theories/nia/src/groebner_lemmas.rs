// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver integration for the bounded Groebner pass (#nia-groebner):
//! polynomial extraction from the asserted equality atoms and emission
//! of the derived equalities as reason-carrying cuts. The Buchberger
//! core lives in `groebner.rs`.

use num_traits::{One, Zero};

use super::groebner::{
    buchberger, buchberger_seeded, integer_signature, mono_mul, GPoly, Mono, PolyTerms, MAX_DEGREE,
    MAX_EXTRACT_DEPTH, MAX_INPUT_POLYS, MAX_TERMS,
};
use super::*;

impl NiaSolver<'_> {
    /// Groebner consequences of the asserted equality atoms
    /// (#nia-groebner): asserts every derived polynomial that is linear
    /// over the tracked monomials as a reason-carrying equality cut
    /// pair into the inner LIA solver. Returns the conflict literals
    /// directly when the basis contains a nonzero constant (its
    /// provenance). Exact theorems of the asserted literals — like the
    /// congruence and zero-bound lemmas, these are not approximations.
    pub(crate) fn add_groebner_equality_lemmas(&mut self) -> Option<Vec<TheoryLit>> {
        let inputs = self.collect_equality_polys()?;
        // Memo: `buchberger` is a pure function of the ordered inputs
        // (terms AND provenance), and consecutive checks under the lazy
        // split loop re-present a near-identical asserted equality set
        // thousands of times (measured on Certora 65782_8: ~3,200
        // recomputations at ~3ms each in 20s, dominating the run). An
        // exact input replay therefore reuses the stored outcome; cut
        // emission is still re-attempted because monomial aux
        // availability can have grown since the stored run.
        if Self::groebner_inputs_eq(&inputs, &self.groebner_memo_inputs) {
            self.groebner_memo_hits = self.groebner_memo_hits.saturating_add(1);
            if let Some(conflict) = &self.groebner_memo_conflict {
                return Some(conflict.clone());
            }
            let derived = std::mem::take(&mut self.groebner_memo_derived);
            for (sig, provenance) in &derived {
                if self.groebner_emitted.contains(sig) {
                    continue;
                }
                if self.emit_groebner_cut(sig, provenance) {
                    self.groebner_emitted.insert(sig.clone());
                }
            }
            self.groebner_memo_derived = derived;
            return None;
        }
        // Superset growth (the trail lengthened since the memoized
        // run): a stored constant conflict still refutes, its
        // provenance being a subset of the current inputs; otherwise
        // seed Buchberger with the stored basis and queue only the
        // new polynomials.
        let seeded = self.groebner_superset_delta(&inputs);
        if let Some(conflict) = &self.groebner_memo_conflict {
            if seeded.is_some() {
                self.groebner_memo_hits = self.groebner_memo_hits.saturating_add(1);
                return Some(conflict.clone());
            }
        }
        let input_sigs: HashSet<Vec<(Mono, BigInt)>> = inputs
            .iter()
            .filter_map(|p| integer_signature(&p.terms))
            .collect();
        let memo_key = inputs.clone();
        let extended = seeded.and_then(|delta| {
            let seed = std::mem::take(&mut self.groebner_memo_basis);
            buchberger_seeded(seed, delta)
        });
        let basis = match extended {
            Some(basis) => {
                self.groebner_memo_seeded = self.groebner_memo_seeded.saturating_add(1);
                basis
            }
            None => buchberger(inputs),
        };
        for poly in &basis {
            if poly.is_constant() {
                let conflict: Vec<TheoryLit> = poly
                    .provenance
                    .iter()
                    .map(|&(term, value)| TheoryLit { term, value })
                    .collect();
                self.groebner_memo_inputs = memo_key;
                self.groebner_memo_derived = Vec::new();
                self.groebner_memo_basis = Vec::new();
                self.groebner_memo_conflict = Some(conflict.clone());
                return Some(conflict);
            }
        }
        let mut derived: Vec<(Vec<(Mono, BigInt)>, Vec<(TermId, bool)>)> = Vec::new();
        for poly in &basis {
            let Some(sig) = integer_signature(&poly.terms) else {
                continue;
            };
            if input_sigs.contains(&sig) {
                continue;
            }
            derived.push((sig, poly.provenance.clone()));
        }
        for (sig, provenance) in &derived {
            if self.groebner_emitted.contains(sig) {
                continue;
            }
            if self.emit_groebner_cut(sig, provenance) {
                self.groebner_emitted.insert(sig.clone());
            }
        }
        self.groebner_memo_inputs = memo_key;
        self.groebner_memo_derived = derived;
        self.groebner_memo_basis = basis;
        self.groebner_memo_conflict = None;
        None
    }

    /// When the memoized input list is a strict subset of `inputs`
    /// (by exact terms+provenance key), the polynomials in `inputs`
    /// beyond the memoized ones; `None` otherwise. Tries the common
    /// append-only prefix shape first (asserted trails mostly grow by
    /// appending), then falls back to multiset difference.
    fn groebner_superset_delta(&self, inputs: &[GPoly]) -> Option<Vec<GPoly>> {
        let memo = &self.groebner_memo_inputs;
        if memo.is_empty() || inputs.len() <= memo.len() {
            return None;
        }
        if Self::groebner_inputs_eq(&inputs[..memo.len()], memo) {
            return Some(inputs[memo.len()..].to_vec());
        }
        let mut remaining: std::collections::HashMap<(Vec<(TermId, bool)>, PolyTerms), usize> =
            std::collections::HashMap::new();
        for p in memo {
            *remaining
                .entry((p.provenance.clone(), p.terms.clone()))
                .or_insert(0) += 1;
        }
        let mut delta = Vec::new();
        for p in inputs {
            let key = (p.provenance.clone(), p.terms.clone());
            match remaining.get_mut(&key) {
                Some(n) if *n > 0 => *n -= 1,
                _ => delta.push(p.clone()),
            }
        }
        if remaining.values().all(|&n| n == 0) && !delta.is_empty() {
            Some(delta)
        } else {
            None
        }
    }

    /// Exact equality of two Groebner input lists (polynomial terms and
    /// provenance, in order) — the memo key. `buchberger`'s result can
    /// depend on input order, so the key is order-sensitive.
    fn groebner_inputs_eq(a: &[GPoly], b: &[GPoly]) -> bool {
        a.len() == b.len()
            && a.iter()
                .zip(b.iter())
                .all(|(x, y)| x.terms == y.terms && x.provenance == y.provenance)
    }

    /// Drop the Groebner memo (scope discipline: called wherever
    /// `groebner_emitted` is cleared).
    pub(crate) fn clear_groebner_memo(&mut self) {
        self.groebner_memo_inputs = Vec::new();
        self.groebner_memo_derived = Vec::new();
        self.groebner_memo_basis = Vec::new();
        self.groebner_memo_conflict = None;
    }

    /// Polynomials of the true equality atoms, or `None` when the pass
    /// cannot apply (fewer than two extractable equalities, no
    /// nonlinear input — a purely linear system is the LIA's job — or
    /// the input cap is exceeded anywhere).
    fn collect_equality_polys(&self) -> Option<Vec<GPoly>> {
        let mut polys = Vec::new();
        let mut any_nonlinear = false;
        for &(term, value) in &self.asserted {
            if !value {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            let (Some(mut poly), Some(rhs_poly)) =
                (self.poly_of_term(lhs, 0), self.poly_of_term(rhs, 0))
            else {
                continue;
            };
            for (mono, coeff) in rhs_poly {
                *poly.entry(mono).or_insert_with(BigRational::zero) -= &coeff;
            }
            poly.retain(|_, c| !c.is_zero());
            if poly.is_empty() {
                continue;
            }
            if poly.keys().any(|m| m.len() >= 2) {
                any_nonlinear = true;
            }
            polys.push(GPoly {
                terms: poly,
                provenance: vec![(term, true)],
            });
            if polys.len() > MAX_INPUT_POLYS {
                return None;
            }
        }
        (polys.len() >= 2 && any_nonlinear).then_some(polys)
    }

    /// Assert the derived equality `sig == 0` as `>=`/`<=` cuts when
    /// every monomial is a base variable or a tracked monomial.
    fn emit_groebner_cut(&mut self, sig: &[(Mono, BigInt)], provenance: &[(TermId, bool)]) -> bool {
        let mut coeffs: Vec<(u32, BigRational)> = Vec::new();
        let mut constant = BigRational::zero();
        let mut anchor: Option<TermId> = None;
        for (mono, coeff) in sig {
            let coeff = BigRational::from_integer(coeff.clone());
            let var = match mono.len() {
                0 => {
                    constant = coeff;
                    continue;
                }
                1 => mono[0],
                _ => match self.monomials.get(mono) {
                    Some(mon) => mon.aux_var,
                    None => return false,
                },
            };
            anchor.get_or_insert(var);
            let lra_var = self.lia.lra_solver_mut().ensure_var_registered(var);
            coeffs.push((lra_var, coeff));
        }
        let Some(anchor) = anchor else { return false };
        for is_lower in [true, false] {
            self.lia.lra_solver_mut().add_gomory_cut(
                &GomoryCut {
                    coeffs: coeffs.clone(),
                    bound: -constant.clone(),
                    is_lower,
                    reasons: provenance.to_vec(),
                    source_term: None,
                },
                anchor,
            );
        }
        if self.debug {
            safe_eprintln!(
                "[NIA] Groebner derived equality over {} terms (reasons={:?})",
                coeffs.len(),
                provenance
            );
        }
        true
    }

    /// Exact polynomial of an integer term over base variables, or
    /// `None` for shapes outside `+`/`-`/`*`/constants/variables/
    /// monomial auxes and for anything over the size caps.
    fn poly_of_term(&self, term: TermId, depth: usize) -> Option<PolyTerms> {
        if depth > MAX_EXTRACT_DEPTH {
            return None;
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => {
                Some(const_poly(BigRational::from_integer(n.clone())))
            }
            TermData::Const(Constant::Rational(r)) => Some(const_poly(r.0.clone())),
            TermData::Var(_, _) => {
                let mono = self.mono_of_var(term, depth)?;
                let mut poly = PolyTerms::new();
                poly.insert(mono, BigRational::one());
                Some(poly)
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    let mut acc = PolyTerms::new();
                    for &arg in args {
                        add_poly_into(&mut acc, self.poly_of_term(arg, depth + 1)?)?;
                    }
                    Some(acc)
                }
                "-" if args.len() == 1 => {
                    let inner = self.poly_of_term(args[0], depth + 1)?;
                    Some(inner.into_iter().map(|(m, c)| (m, -c)).collect())
                }
                "-" if args.len() == 2 => {
                    let mut acc = self.poly_of_term(args[0], depth + 1)?;
                    let rhs = self.poly_of_term(args[1], depth + 1)?;
                    for (mono, coeff) in rhs {
                        *acc.entry(mono).or_insert_with(BigRational::zero) -= &coeff;
                    }
                    acc.retain(|_, c| !c.is_zero());
                    Some(acc)
                }
                "*" => {
                    let mut acc = const_poly(BigRational::one());
                    for &arg in args {
                        acc = mul_polys(&acc, &self.poly_of_term(arg, depth + 1)?)?;
                    }
                    Some(acc)
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// The monomial a variable denotes: itself for a base variable, or
    /// the factor multiset for a monomial aux variable (each factor
    /// must itself denote a monomial).
    fn mono_of_var(&self, var: TermId, depth: usize) -> Option<Mono> {
        let Some(factors) = self.aux_to_monomial.get(&var) else {
            return Some(vec![var]);
        };
        if depth > MAX_EXTRACT_DEPTH {
            return None;
        }
        let mut mono: Mono = Vec::new();
        for &factor in factors {
            match self.terms.get(factor) {
                TermData::Var(_, _) => mono.extend(self.mono_of_var(factor, depth + 1)?),
                _ => return None,
            }
        }
        mono.sort_unstable_by_key(|t| t.0);
        (mono.len() <= MAX_DEGREE).then_some(mono)
    }
}

fn const_poly(value: BigRational) -> PolyTerms {
    let mut poly = PolyTerms::new();
    if !value.is_zero() {
        poly.insert(Vec::new(), value);
    }
    poly
}

fn add_poly_into(acc: &mut PolyTerms, other: PolyTerms) -> Option<()> {
    for (mono, coeff) in other {
        *acc.entry(mono).or_insert_with(BigRational::zero) += &coeff;
    }
    acc.retain(|_, c| !c.is_zero());
    (acc.len() <= MAX_TERMS).then_some(())
}

fn mul_polys(a: &PolyTerms, b: &PolyTerms) -> Option<PolyTerms> {
    let mut out = PolyTerms::new();
    for (ma, ca) in a {
        for (mb, cb) in b {
            if ma.len() + mb.len() > MAX_DEGREE {
                return None;
            }
            *out.entry(mono_mul(ma, mb))
                .or_insert_with(BigRational::zero) += ca * cb;
        }
    }
    out.retain(|_, c| !c.is_zero());
    (out.len() <= MAX_TERMS).then_some(out)
}
