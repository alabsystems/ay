// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use control::{de_result, Item};
use serde::de::{DeserializeSeed, MapAccess, SeqAccess, Visitor};
use std::cell::RefCell;
use std::fmt;
use std::io::{self, Read};

mod fields;
mod sequences;
mod visitors;

type Shared<'a, 'b, 'p> = &'a RefCell<&'b mut Control<'p>>;

pub(super) fn read(
    bytes: &[u8],
    control: &mut Control<'_>,
) -> Result<RetainedBvRefutation, WireError> {
    lexical::admit(bytes, control)?;
    let borrowed_and_scratch = control.storage;
    control.retain(size_of::<RetainedBvRefutation>())?;
    let result = {
        let shared = RefCell::new(&mut *control);
        let input = Input {
            bytes,
            position: 0,
            grant: 0,
            control: &shared,
        };
        let mut deserializer = serde_json::Deserializer::from_reader(input);
        let result = visitors::Root(&shared).deserialize(&mut deserializer);
        // Do not continue parsing after an observed visitor/parser refusal.
        match result {
            Ok(payload) => deserializer.end().map(|()| payload),
            Err(error) => Err(error),
        }
    }; // Drop parser, its scratch and the borrowed input adapter before admission.
    let payload = match result {
        Ok(payload) => payload,
        Err(error) => {
            drop(error); // Never Display/Debug attacker-influenced diagnostics.
            return Err(control.serde_error());
        }
    };
    shape::validate(&payload, control)?;
    control.poll()?;
    control.usage.returned_owned_bytes = control.storage - borrowed_and_scratch;
    Ok(payload)
}

/// No owned input copy. serde's IoRead tracks line/column incrementally, so
/// error-position queries cannot rescan an unbounded already-consumed prefix.
struct Input<'d, 'a, 'b, 'p> {
    bytes: &'d [u8],
    position: usize,
    grant: usize,
    control: Shared<'a, 'b, 'p>,
}

impl Read for Input<'_, '_, '_, '_> {
    fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
        let mut control = self.control.borrow_mut();
        let refused = |_| io::Error::from(io::ErrorKind::Other);
        control.status().map_err(refused)?;
        if output.is_empty() || self.position == self.bytes.len() {
            return Ok(0);
        }
        if self.grant == 0 {
            self.grant = (self.bytes.len() - self.position).min(lexical::WINDOW);
            let work = control
                .product(self.grant, lexical::PARSER_PASSES)
                .map_err(refused)?;
            control.charge(work).map_err(refused)?;
        }
        let count = output.len().min(self.grant);
        output[..count].copy_from_slice(&self.bytes[self.position..self.position + count]);
        self.position += count;
        self.grant -= count;
        Ok(count)
    }
}

fn invalid<E: serde::de::Error>(control: Shared<'_, '_, '_>, message: &'static str) -> E {
    let _ = control
        .borrow_mut()
        .fail::<()>(WireError::InvalidPayload(message));
    E::custom("invalid retained wire payload")
}

struct Number<'a, 'b, 'p>(Shared<'a, 'b, 'p>);

impl<'de> DeserializeSeed<'de> for Number<'_, '_, '_> {
    type Value = u64;
    fn deserialize<D: serde::Deserializer<'de>>(self, de: D) -> Result<u64, D::Error> {
        de_result(self.0.borrow_mut().charge(1))?;
        u64::deserialize(de)
    }
}

#[cfg(test)]
mod tests;
