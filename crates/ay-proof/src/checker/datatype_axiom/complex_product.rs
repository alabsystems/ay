// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The nominal builtin Complex product has one constructor, so its eta law
//! is unconditional and needs no user datatype declaration authority.

use ay_core::{Sort, TermData, TermId, TermStore};

pub(crate) fn recognizes(terms: &TermStore, clause: &[TermId]) -> bool {
    if ["=", "complex.make", "complex.real", "complex.imag"]
        .iter()
        .any(|name| terms.is_declared_function(name))
    {
        return false;
    }
    let [literal] = clause else { return false };
    let TermData::App(op, sides) = terms.get(*literal) else {
        return false;
    };
    if op.name() != "=" || sides.len() != 2 || terms.sort(*literal) != &Sort::Bool {
        return false;
    }
    [(sides[0], sides[1]), (sides[1], sides[0])]
        .into_iter()
        .any(|(value, rebuilt)| {
            if terms.sort(value) != &Sort::Complex || terms.sort(rebuilt) != &Sort::Complex {
                return false;
            }
            let TermData::App(constructor, fields) = terms.get(rebuilt) else {
                return false;
            };
            if constructor.name() != "complex.make" || fields.len() != 2 {
                return false;
            }
            fields
                .iter()
                .zip(["complex.real", "complex.imag"])
                .all(|(field, name)| {
                    if terms.sort(*field) != &Sort::Real {
                        return false;
                    }
                    matches!(terms.get(*field), TermData::App(selector, args)
                if selector.name() == name && args.as_slice() == [value])
                })
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::Symbol;

    fn clause(terms: &mut TermStore, value: TermId, receiver: TermId, names: [&str; 2]) -> TermId {
        let fields: Vec<_> = names
            .into_iter()
            .map(|name| terms.mk_app(Symbol::named(name), [receiver], Sort::Real))
            .collect();
        let rebuilt = terms.mk_app(Symbol::named("complex.make"), fields, Sort::Complex);
        terms.mk_app(Symbol::named("="), [value, rebuilt], Sort::Bool)
    }

    #[test]
    fn complex_eta_requires_nominal_sort_ordered_exact_projections() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Complex);
        let y = terms.mk_var("y", Sort::Complex);
        let fake = terms.mk_var("fake", Sort::Uninterpreted("Complex".into()));
        let valid = clause(&mut terms, x, x, ["complex.real", "complex.imag"]);
        assert!(recognizes(&terms, &[valid]));
        for (value, receiver, names) in [
            (x, y, ["complex.real", "complex.imag"]),
            (x, x, ["complex.imag", "complex.real"]),
            (x, x, ["complex.real", "complex.real"]),
            (fake, fake, ["complex.real", "complex.imag"]),
            (x, x, ["foreign", "complex.imag"]),
        ] {
            let forged = clause(&mut terms, value, receiver, names);
            assert!(!recognizes(&terms, &[forged]));
        }
        assert!(!recognizes(&terms, &[valid, valid]));
        assert!(!recognizes(&terms, &[]));
        for owned in ["=", "complex.make", "complex.real", "complex.imag"] {
            let mut owned_terms = terms.clone();
            owned_terms.register_declared_function(owned);
            assert!(!recognizes(&owned_terms, &[valid]));
        }
    }
}
