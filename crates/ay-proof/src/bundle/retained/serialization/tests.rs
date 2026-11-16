// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{control, TransportOutcome};
use super::*;
use ay_core::time::Instant;
use serde::ser::SerializeSeq;
use std::{cell::Cell, collections::BTreeMap, io, time::Duration};

fn attempt<T: Serialize + ?Sized>(
    value: &T,
    maximum: usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> (TransportOutcome<()>, Vec<u8>) {
    let mut output = Vec::new();
    let outcome = control::run(
        Instant::now() + Duration::from_secs(30),
        progress,
        |control| {
            let shared = RefCell::new(control);
            serde_json::to_writer(
                &mut output,
                &Guarded {
                    value,
                    control: &shared,
                    max_string_bytes: maximum,
                },
            )
            .map_err(|_| TransportError::InvalidJson)
        },
    );
    (outcome, output)
}

fn same_bytes<T: Serialize + ?Sized>(value: &T) {
    let (outcome, output) = attempt(value, 4096, &mut |_, _| true);
    assert_eq!(outcome.result, Ok(()));
    assert_eq!(output, serde_json::to_vec(value).unwrap());
    assert!(outcome.usage.charged_work > 0);
    assert_eq!(outcome.usage.charged_bytes, 0);
}

#[derive(Serialize)]
enum Shapes<'a> {
    Unit,
    New(&'a str),
    Tuple(u32, Option<&'a str>),
    Named { nested: Vec<&'a str> },
}

#[derive(Serialize)]
struct TupleShape(u8, u16);

#[derive(Serialize)]
struct UnitShape;

struct Bytes<'a>(&'a [u8]);

impl Serialize for Bytes<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(self.0)
    }
}

#[test]
fn scalar_and_compound_bytes_match_unguarded_serde() {
    same_bytes(&(true, -1i8, -2i16, -3i32, -4i64, -5i128));
    same_bytes(&(1u8, 2u16, 3u32, 4u64, 5u128, 0.5f32, 0.25f64, 'λ'));
    same_bytes(&((), UnitShape, TupleShape(1, 2), None::<u8>, Some(3u8)));
    same_bytes(&[
        Shapes::Unit,
        Shapes::New("quotes\" and \\ escapes"),
        Shapes::Tuple(7, Some("λ")),
        Shapes::Named {
            nested: vec!["a", "b"],
        },
    ]);
    same_bytes(&BTreeMap::from([
        ("first", vec![1u32, 2]),
        ("second", vec![3]),
    ]));
    same_bytes(&Bytes(&[0, 128, 255]));
}

#[test]
fn raw_json_special_struct_preserves_original_bytes() {
    let raw: &serde_json::value::RawValue =
        serde_json::from_str("{ \"rows\" : [1, 2], \"flag\" : true }").unwrap();
    same_bytes(&BTreeMap::from([("payload", raw)]));
}

#[test]
fn nested_string_is_charged_before_serde_emits_or_scans_it() {
    let value = vec!["x".repeat(4096)];
    let (outcome, output) = attempt(&value, 4096, &mut |work, _| work < 4096);
    assert_eq!(outcome.result, Err(TransportError::Refused));
    assert_eq!(output, b"[");
}

#[test]
fn source_length_cap_applies_to_strings_keys_and_bytes_before_delegation() {
    let value = "x".repeat(128);
    for output in [
        attempt(&vec![value.as_str()], 127, &mut |_, _| true),
        attempt(
            &BTreeMap::from([(value.as_str(), 1u8)]),
            127,
            &mut |_, _| true,
        ),
        attempt(&Bytes(value.as_bytes()), 127, &mut |_, _| true),
    ] {
        assert_eq!(
            output.0.result,
            Err(TransportError::Limit {
                resource: "source string bytes",
                limit: 127,
                actual: 128,
            })
        );
        assert!(output.1.len() <= 1);
    }
    same_bytes(&value);
    assert_eq!(attempt(&value, 128, &mut |_, _| true).0.result, Ok(()));
}

struct DisplayProbe<'a>(&'a Cell<usize>);

impl fmt::Display for DisplayProbe<'_> {
    fn fmt(&self, output: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.set(self.0.get() + 1);
        output.write_str("must not be formatted")
    }
}

impl Serialize for DisplayProbe<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

#[test]
fn unbounded_display_refuses_without_calling_display() {
    let calls = Cell::new(0);
    let (outcome, output) = attempt(&DisplayProbe(&calls), 4096, &mut |_, _| true);
    assert_eq!(
        outcome.result,
        Err(TransportError::InvalidShape("unbounded collect_str"))
    );
    assert_eq!(calls.get(), 0);
    assert_eq!(output.as_slice(), &[] as &[u8]);
}

struct CatchElementError;

impl Serialize for CatchElementError {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut sequence = serializer.serialize_seq(Some(1))?;
        let _ = sequence.serialize_element(&true);
        sequence.end()
    }
}

struct FailSecondWrite<'a>(&'a Cell<usize>);

impl io::Write for FailSecondWrite<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.0.set(self.0.get() + 1);
        if self.0.get() == 1 {
            Ok(bytes.len())
        } else {
            Err(io::ErrorKind::Other.into())
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn swallowed_writer_failure_is_sticky_and_does_not_retry_writer() {
    let writes = Cell::new(0);
    let outcome = control::run(
        Instant::now() + Duration::from_secs(30),
        &mut |_, _| true,
        |control| {
            let shared = RefCell::new(control);
            serde_json::to_writer(
                FailSecondWrite(&writes),
                &Guarded {
                    value: &CatchElementError,
                    control: &shared,
                    max_string_bytes: 4096,
                },
            )
            .map_err(|_| TransportError::InvalidJson)
        },
    );
    assert_eq!(outcome.result, Err(TransportError::InvalidJson));
    assert_eq!(writes.get(), 2);
}

#[test]
fn every_callback_refusal_is_terminal() {
    let value = Shapes::Named {
        nested: vec!["one", "two"],
    };
    let mut total = 0;
    assert_eq!(
        attempt(&value, 4096, &mut |_, _| {
            total += 1;
            true
        })
        .0
        .result,
        Ok(())
    );
    for stop in 1..=total {
        let mut calls = 0;
        let (outcome, _) = attempt(&value, 4096, &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert_eq!(outcome.result, Err(TransportError::Refused));
        assert_eq!(calls, stop);
    }
}
