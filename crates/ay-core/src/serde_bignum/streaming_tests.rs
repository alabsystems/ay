// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::WireDigitsRef;
use num_bigint::BigUint;
use serde::ser::{Impossible, SerializeSeq};
use serde::{Serialize, Serializer};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Event {
    Begin(Option<usize>),
    Limb(u32),
    End,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
enum TestError {
    #[error("injected serializer refusal")]
    Injected,
    #[error("unexpected serialization method")]
    Unexpected,
}

impl serde::ser::Error for TestError {
    fn custom<T: fmt::Display>(_: T) -> Self {
        Self::Unexpected
    }
}

#[derive(Default)]
struct Recorder {
    events: Vec<Event>,
    fail_at: Option<usize>,
}

impl Recorder {
    fn event(&mut self, event: Event) -> Result<(), TestError> {
        let position = self.events.len();
        self.events.push(event);
        if self.fail_at == Some(position) {
            Err(TestError::Injected)
        } else {
            Ok(())
        }
    }
}

// Only a sequence of u32 values is admitted. A tuple, byte buffer, different
// integer width or accidentally inserted wrapper must fail these tests.
macro_rules! reject_methods {
    ($($name:ident($($arg:ident: $ty:ty),*) -> $output:ty;)*) => {
        $(
            fn $name(self, $($arg: $ty),*) -> Result<$output, Self::Error> {
                let _ = ($($arg,)*);
                Err(TestError::Unexpected)
            }
        )*
    };
}

impl Serializer for &mut Recorder {
    type Ok = ();
    type Error = TestError;
    type SerializeSeq = Self;
    type SerializeTuple = Impossible<(), TestError>;
    type SerializeTupleStruct = Impossible<(), TestError>;
    type SerializeTupleVariant = Impossible<(), TestError>;
    type SerializeMap = Impossible<(), TestError>;
    type SerializeStruct = Impossible<(), TestError>;
    type SerializeStructVariant = Impossible<(), TestError>;

    fn serialize_u32(self, value: u32) -> Result<(), TestError> {
        self.event(Event::Limb(value))
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self, TestError> {
        self.event(Event::Begin(len))?;
        Ok(self)
    }

    reject_methods! {
        serialize_bool(value: bool) -> ();
        serialize_i8(value: i8) -> ();
        serialize_i16(value: i16) -> ();
        serialize_i32(value: i32) -> ();
        serialize_i64(value: i64) -> ();
        serialize_i128(value: i128) -> ();
        serialize_u8(value: u8) -> ();
        serialize_u16(value: u16) -> ();
        serialize_u64(value: u64) -> ();
        serialize_u128(value: u128) -> ();
        serialize_f32(value: f32) -> ();
        serialize_f64(value: f64) -> ();
        serialize_char(value: char) -> ();
        serialize_str(value: &str) -> ();
        serialize_bytes(value: &[u8]) -> ();
        serialize_none() -> ();
        serialize_unit() -> ();
        serialize_unit_struct(name: &'static str) -> ();
        serialize_unit_variant(name: &'static str, index: u32, variant: &'static str) -> ();
        serialize_tuple(len: usize) -> Self::SerializeTuple;
        serialize_tuple_struct(name: &'static str, len: usize) -> Self::SerializeTupleStruct;
        serialize_tuple_variant(name: &'static str, index: u32, variant: &'static str, len: usize) -> Self::SerializeTupleVariant;
        serialize_map(len: Option<usize>) -> Self::SerializeMap;
        serialize_struct(name: &'static str, len: usize) -> Self::SerializeStruct;
        serialize_struct_variant(name: &'static str, index: u32, variant: &'static str, len: usize) -> Self::SerializeStructVariant;
    }

    fn serialize_some<T: ?Sized + Serialize>(self, _: &T) -> Result<(), TestError> {
        Err(TestError::Unexpected)
    }

    fn serialize_newtype_struct<T: ?Sized + Serialize>(
        self,
        _: &'static str,
        _: &T,
    ) -> Result<(), TestError> {
        Err(TestError::Unexpected)
    }

    fn serialize_newtype_variant<T: ?Sized + Serialize>(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: &T,
    ) -> Result<(), TestError> {
        Err(TestError::Unexpected)
    }
}

impl SerializeSeq for &mut Recorder {
    type Ok = ();
    type Error = TestError;

    fn serialize_element<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), TestError> {
        value.serialize(&mut **self)
    }

    fn end(self) -> Result<(), TestError> {
        self.event(Event::End)
    }
}

fn expected_events(limbs: &[u32]) -> Vec<Event> {
    let mut events = vec![Event::Begin(Some(limbs.len()))];
    events.extend(limbs.iter().copied().map(Event::Limb));
    events.push(Event::End);
    events
}

#[test]
fn streamed_digits_preserve_exact_sequence_length_and_limb_order() {
    let cases: &[&[u32]] = &[
        &[],
        &[1],
        &[u32::MAX],
        &[0, 1],
        &[u32::MAX, u32::MAX],
        &[0, 0, 1],
        &[1, 0, 1],
        &[1, 0, 0, 0, 1],
        &[u32::MAX, 0, u32::MAX, 0, 1],
    ];
    for &limbs in cases {
        let value = BigUint::from_slice(limbs);
        let mut streamed = Recorder::default();
        assert_eq!(WireDigitsRef(&value).serialize(&mut streamed), Ok(()));
        assert_eq!(streamed.events, expected_events(limbs));

        // Compare the previous Vec serializer's complete event stream too,
        // including Some(0), which JSON bytes alone cannot distinguish from None.
        let mut previous = Recorder::default();
        assert_eq!(value.to_u32_digits().serialize(&mut previous), Ok(()));
        assert_eq!(streamed.events, previous.events);
    }
}

#[test]
fn streamed_digits_begin_failure_emits_no_elements_or_end() {
    for limbs in [Vec::new(), vec![1, 0, 1]] {
        let value = BigUint::from_slice(&limbs);
        let mut recorder = Recorder {
            fail_at: Some(0),
            ..Recorder::default()
        };
        assert_eq!(
            WireDigitsRef(&value).serialize(&mut recorder),
            Err(TestError::Injected)
        );
        assert_eq!(recorder.events, vec![Event::Begin(Some(limbs.len()))]);
    }
}

#[test]
fn streamed_digits_element_failure_stops_at_each_limb() {
    let limbs = [u32::MAX, 0, 1, 0, u32::MAX];
    let value = BigUint::from_slice(&limbs);
    let complete = expected_events(&limbs);
    for index in 0..limbs.len() {
        let mut recorder = Recorder {
            fail_at: Some(index + 1),
            ..Recorder::default()
        };
        assert_eq!(
            WireDigitsRef(&value).serialize(&mut recorder),
            Err(TestError::Injected)
        );
        assert_eq!(recorder.events.as_slice(), &complete[..index + 2]);
    }
}

#[test]
fn streamed_digits_end_failure_is_returned_without_more_events() {
    for limbs in [Vec::new(), vec![1, 0, 1]] {
        let value = BigUint::from_slice(&limbs);
        let mut recorder = Recorder {
            fail_at: Some(limbs.len() + 1),
            ..Recorder::default()
        };
        assert_eq!(
            WireDigitsRef(&value).serialize(&mut recorder),
            Err(TestError::Injected)
        );
        assert_eq!(recorder.events, expected_events(&limbs));
    }
}
