// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conversions between binding-layer and core sort representations.

use super::{Sort, SortInner};

impl From<&ay_core::Sort> for Sort {
    fn from(s: &ay_core::Sort) -> Self {
        match s {
            ay_core::Sort::Bool => Sort::bool(),
            ay_core::Sort::Int => Sort::int(),
            ay_core::Sort::Real => Sort::real(),
            ay_core::Sort::BitVec(bv) => Sort::bitvec(bv.width),
            ay_core::Sort::Array(arr) => {
                Sort::array(Sort::from(&arr.index_sort), Sort::from(&arr.element_sort))
            }
            ay_core::Sort::Datatype(dt) => {
                let constructors: Vec<_> = dt
                    .constructors
                    .iter()
                    .map(|ctor| {
                        let fields: Vec<(String, Sort)> = ctor
                            .fields
                            .iter()
                            .map(|f| (f.name.clone(), Sort::from(&f.sort)))
                            .collect();
                        (ctor.name.clone(), fields)
                    })
                    .collect();
                Sort::enum_type(&dt.name, constructors)
            }
            ay_core::Sort::String => Sort::string(),
            ay_core::Sort::FloatingPoint(eb, sb) => Sort::floating_point(*eb, *sb),
            ay_core::Sort::Uninterpreted(name) => Sort::uninterpreted(name),
            ay_core::Sort::RegLan => Sort::reglan(),
            ay_core::Sort::Seq(elem) => Sort::seq(Sort::from(elem.as_ref())),
            other => Sort::uninterpreted(&format!("{other:?}")),
        }
    }
}

impl From<&Sort> for ay_core::Sort {
    fn from(s: &Sort) -> Self {
        match s.inner() {
            SortInner::Bool => ay_core::Sort::Bool,
            SortInner::Int => ay_core::Sort::Int,
            SortInner::Real => ay_core::Sort::Real,
            SortInner::BitVec(bv) => ay_core::Sort::bitvec(bv.width),
            SortInner::Array(arr) => ay_core::Sort::array(
                ay_core::Sort::from(&arr.index_sort),
                ay_core::Sort::from(&arr.element_sort),
            ),
            SortInner::Datatype(dt) => {
                let constructors = dt
                    .constructors
                    .iter()
                    .map(|ctor| {
                        ay_core::DatatypeConstructor::new(
                            &ctor.name,
                            ctor.fields
                                .iter()
                                .map(|f| {
                                    ay_core::DatatypeField::new(
                                        &f.name,
                                        ay_core::Sort::from(&f.sort),
                                    )
                                })
                                .collect(),
                        )
                    })
                    .collect();
                ay_core::Sort::Datatype(ay_core::DatatypeSort::new(&dt.name, constructors))
            }
            SortInner::String => ay_core::Sort::String,
            SortInner::FloatingPoint(eb, sb) => ay_core::Sort::FloatingPoint(*eb, *sb),
            SortInner::Uninterpreted(name) => ay_core::Sort::Uninterpreted(name.clone()),
            SortInner::RegLan => ay_core::Sort::RegLan,
            SortInner::Seq(elem) => ay_core::Sort::seq(ay_core::Sort::from(elem.as_ref())),
        }
    }
}
