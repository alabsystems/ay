// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use crate::{ChcOp, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

mod bv_interval;
mod core_implicant;
mod datatype;
mod eval_bv;
mod extended_theories;

/// Helper: create a simple Option-like DT sort with None and Some(Int).
fn option_int_sort() -> ChcSort {
    use crate::expr::ChcDtConstructor;
    use crate::expr::ChcDtSelector;
    ChcSort::Datatype {
        name: "OptionInt".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "None".to_string(),
                selectors: vec![],
            },
            ChcDtConstructor {
                name: "Some".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "val".to_string(),
                    sort: ChcSort::Int,
                }],
            },
        ]),
    }
}

/// Helper: create a Pair(Int, Int) DT sort with single constructor mkpair.
fn pair_int_sort() -> ChcSort {
    use crate::expr::ChcDtConstructor;
    use crate::expr::ChcDtSelector;
    ChcSort::Datatype {
        name: "Pair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkpair".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "fst".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "snd".to_string(),
                    sort: ChcSort::Int,
                },
            ],
        }]),
    }
}
