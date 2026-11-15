// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{control, TransportOutcome};
use super::*;
use ay_core::time::Instant;
use std::{cell::Cell, mem::size_of, time::Duration};

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn raw(text: &str) -> RawSlice<'_> {
    RawSlice::from_raw(serde_json::from_str::<&RawValue>(text).unwrap())
}

fn checked<'a, T>(
    text: &'a str,
    decode: impl FnOnce(RawSlice<'a>, &mut Control<'_>) -> Result<T, TransportError>,
) -> TransportOutcome<T> {
    control::run(deadline(), &mut |_, _| true, |control| {
        decode(raw(text), control)
    })
}

#[test]
fn scalar_leaves_match_pinned_serde_integer_boolean_and_unit_semantics() {
    for text in [
        "0",
        "-0",
        "-0.0",
        "1",
        "-1",
        "127",
        "128",
        "-128",
        "-129",
        "4294967295",
        "4294967296",
        "9223372036854775807",
        "9223372036854775808",
        "-9223372036854775808",
        "-9223372036854775809",
        "18446744073709551615",
        "18446744073709551616",
        "1e0",
        "1.0",
        "true",
        "false",
        "null",
        "\"1\"",
        "[]",
        "{}",
        "\"\\ud800\"",
    ] {
        macro_rules! parity {
            ($ty:ty, $decode:path) => {
                let actual = checked(text, $decode);
                let expected = serde_json::from_str::<$ty>(text);
                assert_eq!(actual.result.is_ok(), expected.is_ok(), "{text}");
                assert_eq!(actual.result.ok(), expected.ok(), "{text}");
                assert_eq!(actual.usage.charged_bytes, 0);
            };
        }
        parity!(u32, u32_value);
        parity!(u64, u64_value);
        parity!(i64, i64_value);
        parity!(i8, i8_value);
        parity!(bool, bool_value);
        parity!((), null);
    }
    assert_eq!(checked(" \n 1\t", u32_value).result, Ok(1));
}

#[test]
fn fixed_nested_vectors_preserve_order_duplicates_empty_rows_and_capacity_charges() {
    let text = "[ [1, -2,1], [], [9223372036854775807,-9223372036854775808] ]";
    let outcome = checked(text, |raw, control| {
        vector(raw, 3, control, |row, control| {
            vector(row, 3, control, i64_value)
        })
    });
    let rows = outcome.result.unwrap();
    assert_eq!(rows, serde_json::from_str::<Vec<Vec<i64>>>(text).unwrap());
    let bytes = rows.capacity() * size_of::<Vec<i64>>()
        + rows
            .iter()
            .map(|row| row.capacity() * size_of::<i64>())
            .sum::<usize>();
    assert_eq!(outcome.usage.charged_bytes, bytes);
    assert_eq!(outcome.usage.returned_owned_bytes, 0); // Enclosing owner settles this.
    let empty = checked("[]", |raw, control| vector(raw, 0, control, u32_value));
    assert!(empty.result.unwrap().is_empty());
    assert_eq!(empty.usage.charged_bytes, 0);
}

#[test]
fn borrowed_cursor_preserves_nested_escaped_and_unicode_element_boundaries() {
    let text = r#"[ " comma,] and \" quote ", {"x":[1,2],"s":"é🚀"}, null, [true, false] ]"#;
    let outcome = checked(text, |raw, control| {
        vector(raw, 4, control, |element, control| {
            control.charge(1, 0)?;
            Ok(element.as_str())
        })
    });
    let pieces = outcome.result.unwrap();
    let expected: Vec<&RawValue> = serde_json::from_str(text).unwrap();
    assert_eq!(
        pieces,
        expected.iter().map(|value| value.get()).collect::<Vec<_>>()
    );
    for piece in &pieces {
        let start = piece.as_ptr() as usize;
        assert!((text.as_ptr() as usize..text.as_ptr() as usize + text.len()).contains(&start));
    }
    assert_eq!(
        outcome.usage.charged_bytes,
        pieces.capacity() * size_of::<&str>()
    );
}

#[test]
fn element_count_ceiling_precedes_slot_allocation_and_any_element_decoder() {
    let decodes = Cell::new(0);
    let outcome = checked("[1,2,3]", |raw, control| {
        vector(raw, 2, control, |element, control| {
            decodes.set(decodes.get() + 1);
            u32_value(element, control)
        })
    });
    assert_eq!(decodes.get(), 0);
    assert_eq!(outcome.usage.charged_bytes, 0);
    assert!(matches!(
        outcome.result,
        Err(TransportError::Limit {
            resource: "owned vector elements",
            limit: 2,
            actual: 3,
        })
    ));
    assert!(
        checked("[1,2,3]", |raw, control| vector(raw, 3, control, u32_value))
            .result
            .is_ok()
    );
    for text in ["null", "{}", "\"[]\"", "1"] {
        let outcome = checked(text, |raw, control| vector(raw, 3, control, u32_value));
        assert!(matches!(
            outcome.result,
            Err(TransportError::InvalidShape("expected array"))
        ));
        assert_eq!(outcome.usage.charged_bytes, 0);
    }
}

#[test]
fn local_and_cumulative_exact_work_and_bytes_admission_are_not_renewed() {
    let text = "[0,1,4294967295]";
    let baseline = checked(text, |raw, control| vector(raw, 3, control, u32_value));
    assert!(baseline.result.is_ok());
    let (work, bytes) = (baseline.usage.charged_work, baseline.usage.charged_bytes);
    assert!(work > 0 && bytes > 0);
    for (max_work, max_bytes, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, bytes, false),
        (work, 0, false),
    ] {
        let outcome = control::run(deadline(), &mut |_, _| true, |control| {
            control.constrain(max_work as u64, max_bytes)?;
            vector(raw(text), 3, control, u32_value)
        });
        assert_eq!(outcome.result.is_ok(), accepted);
        if !accepted {
            assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
        }
    }
    let used = Cell::new(0);
    let outcome = control::run(
        deadline(),
        &mut |cost, _| {
            used.set(used.get() + cost);
            used.get() <= work
        },
        |control| {
            let first = vector(raw(text), 3, control, u32_value)?;
            let second = vector(raw(text), 3, control, u32_value)?;
            Ok((first, second))
        },
    );
    assert!(matches!(outcome.result, Err(TransportError::Refused)));
    assert!(outcome.usage.charged_work > work);
}

#[test]
fn every_success_and_partial_value_failure_poll_refuses_including_final_cleanup() {
    for (text, accepted) in [("[1,2,3]", true), ("[1,true,3]", false)] {
        let calls = Cell::new(0);
        let baseline = control::run(
            deadline(),
            &mut |_, _| {
                calls.set(calls.get() + 1);
                true
            },
            |control| vector(raw(text), 3, control, u32_value),
        );
        assert_eq!(baseline.result.is_ok(), accepted);
        let total = calls.get();
        assert!(total > 5);
        for stop in 1..=total {
            calls.set(0);
            let outcome = control::run(
                deadline(),
                &mut |_, _| {
                    calls.set(calls.get() + 1);
                    calls.get() != stop
                },
                |control| vector(raw(text), 3, control, u32_value),
            );
            assert!(matches!(outcome.result, Err(TransportError::Refused)));
            assert_eq!(calls.get(), stop);
            assert_eq!(outcome.usage.returned_owned_bytes, 0);
            if stop == total {
                assert_eq!(outcome.usage, baseline.usage);
            }
        }
    }
}

#[test]
fn long_whitespace_scans_are_chunk_polled_and_invalid_type_cannot_restart() {
    let text = format!("[{}1,2]", " ".repeat(WINDOW * 5));
    let scan_polls = Cell::new(0);
    let outcome = control::run(
        deadline(),
        &mut |work, _| {
            if work == WINDOW {
                scan_polls.set(scan_polls.get() + 1);
            }
            scan_polls.get() < 3
        },
        |control| vector(raw(&text), 2, control, u32_value),
    );
    assert!(matches!(outcome.result, Err(TransportError::Refused)));
    assert_eq!(scan_polls.get(), 3);
    assert_eq!(outcome.usage.charged_bytes, 0);
    let outcome = control::run(deadline(), &mut |_, _| true, |control| {
        let error = vector(raw("[1,false]"), 2, control, u32_value).unwrap_err();
        let usage = control.usage;
        assert_eq!(
            vector(raw("[1,2]"), 2, control, u32_value).unwrap_err(),
            error
        );
        assert_eq!(control.usage, usage);
        Ok(())
    });
    assert!(matches!(
        outcome.result,
        Err(TransportError::InvalidShape(_))
    ));
}

#[test]
fn expired_original_deadline_precedes_decoder_and_progress() {
    let outcome = control::run(
        Instant::now() - Duration::from_secs(1),
        &mut |_, _| -> bool { panic!("expired before callback") },
        |control| vector(raw("[1]"), 1, control, u32_value),
    );
    assert!(matches!(outcome.result, Err(TransportError::Deadline)));
    assert_eq!(outcome.usage.charged_work, 0);
    assert_eq!(outcome.usage.charged_bytes, 0);
}

#[test]
fn caught_progress_panic_and_swallowed_refusal_cannot_publish_vectors() {
    let calls = Cell::new(0);
    let outcome = control::run(
        deadline(),
        &mut |_, bytes| {
            calls.set(calls.get() + 1);
            if bytes != 0 {
                panic!("slot admission panic");
            }
            true
        },
        |control| {
            let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                vector(raw("[1]"), 1, control, u32_value)
            }));
            assert!(caught.is_err());
            let old_calls = calls.get();
            assert!(matches!(
                vector(raw("[1]"), 1, control, u32_value),
                Err(TransportError::Refused)
            ));
            assert_eq!(calls.get(), old_calls);
            Ok(())
        },
    );
    assert!(matches!(outcome.result, Err(TransportError::Refused)));
    let outcome = checked("[1]", |raw, control| {
        vector(raw, 1, control, |_, control| {
            let _ = control.fail::<()>(TransportError::InvalidShape("swallowed"));
            Ok(1_u32)
        })
    });
    assert_eq!(
        outcome.result,
        Err(TransportError::InvalidShape("swallowed"))
    );
}

#[test]
fn element_decoder_cannot_catch_callback_panic_then_publish_success() {
    let panics = Cell::new(0);
    let outcome = control::run(
        deadline(),
        &mut |work, _| {
            if work == 99 {
                panics.set(panics.get() + 1);
                panic!("caught inside decoder");
            }
            assert_eq!(panics.get(), 0, "no callback after poison");
            true
        },
        |control| {
            vector(raw("[1]"), 1, control, |_, control| {
                let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    control.charge(99, 0)
                }));
                assert!(caught.is_err());
                Ok(1_u32)
            })
        },
    );
    assert_eq!(outcome.result, Err(TransportError::Refused));
    assert_eq!(panics.get(), 1);
}

#[test]
fn element_failure_drops_partial_owners_before_failure_cleanup_observation() {
    struct Owned<'a>(&'a Cell<usize>);
    impl Drop for Owned<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    let dropped = Cell::new(0);
    let failing = Cell::new(false);
    let cleanup = Cell::new(0);
    let outcome = control::run(
        deadline(),
        &mut |_, _| {
            if failing.get() {
                assert_eq!(dropped.get(), 1);
                cleanup.set(cleanup.get() + 1);
            }
            true
        },
        |control| {
            vector(raw("[1,2]"), 2, control, |element, control| {
                if u32_value(element, control)? == 2 {
                    failing.set(true);
                    // Test that a decoder's bare Err is also latched by vector.
                    Err(TransportError::InvalidShape("element refused"))
                } else {
                    Ok(Owned(&dropped))
                }
            })
        },
    );
    assert!(matches!(
        outcome.result,
        Err(TransportError::InvalidShape("element refused"))
    ));
    assert_eq!(dropped.get(), 1);
    assert_eq!(cleanup.get(), 1);
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}
