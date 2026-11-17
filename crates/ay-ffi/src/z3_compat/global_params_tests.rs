// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, FiniteAdmissionGrant};
use ay_core::term::TermConstructionAdmission;
use std::{cell::Cell, sync::Arc};

fn data(value: String) -> Mutex<Option<HashMap<String, String>>> {
    Mutex::new(Some(HashMap::from([(
        "rewriter.max_power_expansion".into(),
        value,
    )])))
}

#[test]
fn sequence_power_global_read_prices_actual_bytes_cumulatively() {
    let store = data(format!("{}4", "0".repeat(4096)));
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(6000, 4096),
        None,
        Arc::new(|| false),
    )
    .expect("test admission controls must initialize");
    assert_eq!(sequence_power_from(&store, &owner), Ok(4));
    assert!(sequence_power_from(&store, &owner).is_err());
    assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
    assert!(sequence_power_from(&store, &owner).is_err());
}

#[test]
fn sequence_power_global_read_allows_callback_reentry_but_not_unpaid_growth() {
    struct Reenter<'a> {
        store: &'a Mutex<Option<HashMap<String, String>>>,
        calls: Cell<usize>,
    }
    impl TermConstructionAdmission for Reenter<'_> {
        fn admit(&self, _: usize, _: usize) -> Result<(), CountedAdmissionError> {
            let n = self.calls.get() + 1;
            self.calls.set(n);
            if n == 2 {
                self.store
                    .lock()
                    .expect("test global-parameter store must remain available")
                    .as_mut()
                    .expect("test global-parameter store must remain initialized")
                    .insert("rewriter.max_power_expansion".into(), "00004".into());
            }
            Ok(())
        }
        fn refuse(&self, e: CountedAdmissionError) -> CountedAdmissionError {
            e
        }
    }
    let store = data("4".into());
    let owner = Reenter {
        store: &store,
        calls: Cell::new(0),
    };
    assert_eq!(
        sequence_power_from(&store, &owner),
        Err("global parameter changed during admission")
    );
}
