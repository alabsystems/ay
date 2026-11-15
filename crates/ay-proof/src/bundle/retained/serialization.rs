// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pre-delegation control for the complete bundle writer's serde traversal.
//!
//! Write callbacks alone are too late: serde_json scans a string before its
//! next write. Admit its entire borrowed length first, and wrap every nested
//! value so compound serializers cannot bypass that boundary. This adapter
//! owns no payload, creates no allowance and refreshes no deadline. Arbitrary
//! work inside a custom Serialize implementation is outside these boundaries;
//! reachable implementations still require source audit. JSON nesting and
//! output allocation admission belong to the enclosing controlled writer.

use super::{Control, TransportError};
use serde::{ser, Serialize, Serializer};
use std::{cell::RefCell, fmt};

type SharedControl<'scope, 'progress> = RefCell<&'scope mut Control<'progress>>;

pub(super) struct Guarded<'a, 'scope, 'progress, T: ?Sized> {
    pub(super) value: &'a T,
    pub(super) control: &'a SharedControl<'scope, 'progress>,
    pub(super) max_string_bytes: usize,
}

impl<T: Serialize + ?Sized> Serialize for Guarded<'_, '_, '_, T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        charge(self.control, 1)?;
        returned(
            self.control,
            self.value.serialize(Adapter {
                inner: serializer,
                control: self.control,
                max_string_bytes: self.max_string_bytes,
            }),
        )
    }
}

fn charge<E: ser::Error>(control: &SharedControl<'_, '_>, work: usize) -> Result<(), E> {
    // The mutable borrow must end before the serializer can call its writer.
    let admitted = control.borrow_mut().charge(work, 0);
    admitted.map_err(|_| E::custom("controlled serialization refused"))
}

fn text<E: ser::Error>(
    control: &SharedControl<'_, '_>,
    value: &str,
    maximum: usize,
) -> Result<(), E> {
    let admitted = {
        let mut control = control.borrow_mut();
        control
            .cap("source string bytes", value.len(), maximum)
            .and_then(|()| control.add(value.len(), 1))
            .and_then(|work| control.charge(work, 0))
    };
    admitted.map_err(|_| E::custom("controlled serialization refused"))
}

fn returned<T, E>(control: &SharedControl<'_, '_>, result: Result<T, E>) -> Result<T, E> {
    if result.is_err() {
        // A custom Serialize implementation may catch an inner error. It must
        // not turn a partial writer failure into successful publication.
        let _ = control.borrow_mut().fail::<()>(TransportError::InvalidJson);
    }
    result
}

struct Adapter<'a, 'scope, 'progress, S> {
    inner: S,
    control: &'a SharedControl<'scope, 'progress>,
    max_string_bytes: usize,
}

struct Compound<'a, 'scope, 'progress, C> {
    inner: C,
    control: &'a SharedControl<'scope, 'progress>,
    max_string_bytes: usize,
}

macro_rules! scalars {
    ($($method:ident: $ty:ty),* $(,)?) => {$ (
        fn $method(self, value: $ty) -> Result<Self::Ok, Self::Error> {
            charge(self.control, 1)?;
            returned(self.control, self.inner.$method(value))
        }
    )*};
}

impl<'a, 'scope, 'progress, S: Serializer> Serializer for Adapter<'a, 'scope, 'progress, S> {
    type Ok = S::Ok;
    type Error = S::Error;
    type SerializeSeq = Compound<'a, 'scope, 'progress, S::SerializeSeq>;
    type SerializeTuple = Compound<'a, 'scope, 'progress, S::SerializeTuple>;
    type SerializeTupleStruct = Compound<'a, 'scope, 'progress, S::SerializeTupleStruct>;
    type SerializeTupleVariant = Compound<'a, 'scope, 'progress, S::SerializeTupleVariant>;
    type SerializeMap = Compound<'a, 'scope, 'progress, S::SerializeMap>;
    type SerializeStruct = Compound<'a, 'scope, 'progress, S::SerializeStruct>;
    type SerializeStructVariant = Compound<'a, 'scope, 'progress, S::SerializeStructVariant>;

    scalars! {
        serialize_bool: bool, serialize_i8: i8, serialize_i16: i16,
        serialize_i32: i32, serialize_i64: i64, serialize_i128: i128,
        serialize_u8: u8, serialize_u16: u16, serialize_u32: u32,
        serialize_u64: u64, serialize_u128: u128, serialize_f32: f32,
        serialize_f64: f64, serialize_char: char,
    }

    fn serialize_str(self, value: &str) -> Result<Self::Ok, Self::Error> {
        text(self.control, value, self.max_string_bytes)?;
        returned(self.control, self.inner.serialize_str(value))
    }

    fn serialize_bytes(self, value: &[u8]) -> Result<Self::Ok, Self::Error> {
        charge(self.control, 1)?;
        let admitted = self.control.borrow_mut().cap(
            "source string bytes",
            value.len(),
            self.max_string_bytes,
        );
        admitted
            .map_err(|_| <Self::Error as ser::Error>::custom("controlled serialization refused"))?;
        charge(self.control, value.len())?;
        returned(self.control, self.inner.serialize_bytes(value))
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        charge(self.control, 1)?;
        returned(self.control, self.inner.serialize_none())
    }

    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error> {
        charge(self.control, 1)?;
        returned(
            self.control,
            self.inner.serialize_some(&Guarded {
                value,
                control: self.control,
                max_string_bytes: self.max_string_bytes,
            }),
        )
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        charge(self.control, 1)?;
        returned(self.control, self.inner.serialize_unit())
    }

    fn serialize_unit_struct(self, name: &'static str) -> Result<Self::Ok, Self::Error> {
        text(self.control, name, self.max_string_bytes)?;
        returned(self.control, self.inner.serialize_unit_struct(name))
    }

    fn serialize_unit_variant(
        self,
        name: &'static str,
        index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        text(self.control, name, self.max_string_bytes)?;
        text(self.control, variant, self.max_string_bytes)?;
        returned(
            self.control,
            self.inner.serialize_unit_variant(name, index, variant),
        )
    }

    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error> {
        text(self.control, name, self.max_string_bytes)?;
        returned(
            self.control,
            self.inner.serialize_newtype_struct(
                name,
                &Guarded {
                    value,
                    control: self.control,
                    max_string_bytes: self.max_string_bytes,
                },
            ),
        )
    }

    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        name: &'static str,
        index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error> {
        text(self.control, name, self.max_string_bytes)?;
        text(self.control, variant, self.max_string_bytes)?;
        returned(
            self.control,
            self.inner.serialize_newtype_variant(
                name,
                index,
                variant,
                &Guarded {
                    value,
                    control: self.control,
                    max_string_bytes: self.max_string_bytes,
                },
            ),
        )
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        charge(self.control, 1)?;
        let inner = returned(self.control, self.inner.serialize_seq(len))?;
        Ok(Compound {
            inner,
            control: self.control,
            max_string_bytes: self.max_string_bytes,
        })
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        charge(self.control, 1)?;
        let inner = returned(self.control, self.inner.serialize_tuple(len))?;
        Ok(Compound {
            inner,
            control: self.control,
            max_string_bytes: self.max_string_bytes,
        })
    }

    fn serialize_tuple_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        text(self.control, name, self.max_string_bytes)?;
        let inner = returned(self.control, self.inner.serialize_tuple_struct(name, len))?;
        Ok(Compound {
            inner,
            control: self.control,
            max_string_bytes: self.max_string_bytes,
        })
    }

    fn serialize_tuple_variant(
        self,
        name: &'static str,
        index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        text(self.control, name, self.max_string_bytes)?;
        text(self.control, variant, self.max_string_bytes)?;
        let inner = returned(
            self.control,
            self.inner
                .serialize_tuple_variant(name, index, variant, len),
        )?;
        Ok(Compound {
            inner,
            control: self.control,
            max_string_bytes: self.max_string_bytes,
        })
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        charge(self.control, 1)?;
        let inner = returned(self.control, self.inner.serialize_map(len))?;
        Ok(Compound {
            inner,
            control: self.control,
            max_string_bytes: self.max_string_bytes,
        })
    }

    fn serialize_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        text(self.control, name, self.max_string_bytes)?;
        // Preserve serde_json's RawValue special struct name verbatim.
        let inner = returned(self.control, self.inner.serialize_struct(name, len))?;
        Ok(Compound {
            inner,
            control: self.control,
            max_string_bytes: self.max_string_bytes,
        })
    }

    fn serialize_struct_variant(
        self,
        name: &'static str,
        index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        text(self.control, name, self.max_string_bytes)?;
        text(self.control, variant, self.max_string_bytes)?;
        let inner = returned(
            self.control,
            self.inner
                .serialize_struct_variant(name, index, variant, len),
        )?;
        Ok(Compound {
            inner,
            control: self.control,
            max_string_bytes: self.max_string_bytes,
        })
    }

    fn collect_str<T: fmt::Display + ?Sized>(self, _value: &T) -> Result<Self::Ok, Self::Error> {
        let _ = self
            .control
            .borrow_mut()
            .fail::<()>(TransportError::InvalidShape("unbounded collect_str"));
        Err(ser::Error::custom("controlled serialization refused"))
    }

    fn is_human_readable(&self) -> bool {
        self.inner.is_human_readable()
    }
}

macro_rules! sequences {
    ($($trait:ident: $method:ident),* $(,)?) => {$ (
        impl<C: ser::$trait> ser::$trait for Compound<'_, '_, '_, C> {
            type Ok = C::Ok;
            type Error = C::Error;
            fn $method<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
                charge(self.control, 1)?;
                returned(self.control, self.inner.$method(&Guarded { value, control: self.control, max_string_bytes: self.max_string_bytes }))
            }
            fn end(self) -> Result<Self::Ok, Self::Error> {
                charge(self.control, 1)?;
                returned(self.control, self.inner.end())
            }
        }
    )*};
}

sequences! {
    SerializeSeq: serialize_element, SerializeTuple: serialize_element,
    SerializeTupleStruct: serialize_field, SerializeTupleVariant: serialize_field,
}

impl<C: ser::SerializeMap> ser::SerializeMap for Compound<'_, '_, '_, C> {
    type Ok = C::Ok;
    type Error = C::Error;
    fn serialize_key<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        charge(self.control, 1)?;
        returned(
            self.control,
            self.inner.serialize_key(&Guarded {
                value,
                control: self.control,
                max_string_bytes: self.max_string_bytes,
            }),
        )
    }
    fn serialize_value<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        charge(self.control, 1)?;
        returned(
            self.control,
            self.inner.serialize_value(&Guarded {
                value,
                control: self.control,
                max_string_bytes: self.max_string_bytes,
            }),
        )
    }
    fn end(self) -> Result<Self::Ok, Self::Error> {
        charge(self.control, 1)?;
        returned(self.control, self.inner.end())
    }
}

macro_rules! structures {
    ($($trait:ident),* $(,)?) => {$ (
        impl<C: ser::$trait> ser::$trait for Compound<'_, '_, '_, C> {
            type Ok = C::Ok;
            type Error = C::Error;
            fn serialize_field<T: Serialize + ?Sized>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error> {
                text(self.control, key, self.max_string_bytes)?;
                returned(self.control, self.inner.serialize_field(key, &Guarded { value, control: self.control, max_string_bytes: self.max_string_bytes }))
            }
            fn skip_field(&mut self, key: &'static str) -> Result<(), Self::Error> {
                text(self.control, key, self.max_string_bytes)?;
                returned(self.control, self.inner.skip_field(key))
            }
            fn end(self) -> Result<Self::Ok, Self::Error> {
                charge(self.control, 1)?;
                returned(self.control, self.inner.end())
            }
        }
    )*};
}

structures! { SerializeStruct, SerializeStructVariant }

#[cfg(test)]
mod tests;
