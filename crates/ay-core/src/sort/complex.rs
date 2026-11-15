// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The nominal Complex sort and its exact product-of-Reals carrier.
//! Reference: Z3 5.3.3, src/ast/arith_decl_plugin.cpp, complex sort declaration.

use super::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use std::sync::OnceLock;

impl Sort {
    /// Whether this is the builtin Complex sort, independent of user sort names.
    #[must_use]
    pub fn is_complex(&self) -> bool {
        matches!(self, Self::Complex)
    }

    /// Constructor/selector semantics for a datatype or the builtin Complex
    /// product. Complex remains nominally distinct from a user datatype with
    /// the same printed name; this descriptor supplies its theory encoding.
    #[must_use]
    pub fn datatype_definition(&self) -> Option<&DatatypeSort> {
        match self {
            Self::Datatype(definition) => Some(definition),
            Self::Complex => Some(complex_definition()),
            _ => None,
        }
    }
}

fn complex_definition() -> &'static DatatypeSort {
    static DEFINITION: OnceLock<DatatypeSort> = OnceLock::new();
    DEFINITION.get_or_init(|| {
        DatatypeSort::new(
            "Complex",
            vec![DatatypeConstructor::new(
                "complex.make",
                vec![
                    DatatypeField::new("complex.real", Sort::Real),
                    DatatypeField::new("complex.imag", Sort::Real),
                ],
            )],
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn complex_sort_is_nominal_and_round_trips() {
        assert!(Sort::Complex.is_complex());
        assert_ne!(Sort::Complex, Sort::Uninterpreted("Complex".to_string()));
        let definition = Sort::Complex.datatype_definition().unwrap().clone();
        assert_ne!(Sort::Complex, Sort::Datatype(definition.clone()));
        assert_eq!(definition.constructors.len(), 1);
        assert_eq!(definition.constructors[0].fields.len(), 2);
        assert!(definition.constructors[0]
            .fields
            .iter()
            .all(|field| field.sort == Sort::Real));
        let text = serde_json::to_string(&Sort::Complex).unwrap();
        assert_eq!(text, "\"Complex\"");
        assert_eq!(serde_json::from_str::<Sort>(&text).unwrap(), Sort::Complex);
    }
}
