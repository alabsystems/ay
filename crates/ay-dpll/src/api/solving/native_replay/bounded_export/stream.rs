// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact v1 JSON, streamed twice from borrowed records. The first pass has no
//! output buffer; the second cannot grow beyond its admitted exact byte count.

use std::fmt::{self, Write as _};

use ay_core::{Constant, DatatypeSort, Sort, Symbol, TermData, TermId};
use ay_frontend::PublicSort;

use super::super::{symbol_kind_json, NativeReplayEventKind, NATIVE_REPLAY_SCHEMA};
use super::meter::{Meter, Result};
use super::plan::{ApiSort, Domain, Name, Plan};
use crate::api::{NativeReplayExportError as Error, NativeReplayExportResource as Resource};

enum Sink {
    Count(usize),
    Bytes { value: Vec<u8>, admitted: usize },
}

struct Json<'a, 'b> {
    meter: &'a mut Meter<'b>,
    sink: Sink,
    depth: usize,
}

impl Json<'_, '_> {
    fn bytes(&mut self, value: &[u8]) -> Result<()> {
        let length = match &self.sink {
            Sink::Count(length) => *length,
            Sink::Bytes { value, .. } => value.len(),
        };
        let next = match length.checked_add(value.len()) {
            Some(next) => next,
            None => return self.meter.fail(Error::Allocation),
        };
        let remaining = self
            .meter
            .budget
            .limits
            .max_output_bytes
            .saturating_sub(self.meter.budget.usage.output_bytes);
        if next > remaining && matches!(self.sink, Sink::Count(_)) {
            return self.meter.fail(Error::Limit {
                resource: Resource::Output,
                limit: self.meter.budget.limits.max_output_bytes,
                requested: self.meter.budget.usage.output_bytes.saturating_add(next),
            });
        }
        match &mut self.sink {
            Sink::Count(length) => {
                self.meter.charge(value.len(), 0)?;
                *length = next;
            }
            Sink::Bytes {
                value: output,
                admitted,
            } => {
                if next > *admitted || next > output.capacity() {
                    return self.meter.fail(Error::Encoding);
                }
                self.meter.output(value.len())?;
                output.extend_from_slice(value);
            }
        }
        Ok(())
    }

    fn raw(&mut self, value: &str) -> Result<()> {
        self.bytes(value.as_bytes())
    }
    fn null(&mut self) -> Result<()> {
        self.raw("null")
    }
    fn boolean(&mut self, value: bool) -> Result<()> {
        self.raw(if value { "true" } else { "false" })
    }

    fn escaped(&mut self, value: &str) -> Result<()> {
        self.meter.charge(value.len(), 0)?;
        let mut start = 0usize;
        for (index, &byte) in value.as_bytes().iter().enumerate() {
            let escape = match byte {
                b'"' => Some("\\\""),
                b'\\' => Some("\\\\"),
                b'\n' => Some("\\n"),
                b'\r' => Some("\\r"),
                b'\t' => Some("\\t"),
                8 => Some("\\b"),
                12 => Some("\\f"),
                _ => None,
            };
            if let Some(escape) = escape {
                self.bytes(&value.as_bytes()[start..index])?;
                self.raw(escape)?;
                start = index + 1;
            } else if byte < 32 {
                const HEX: &[u8; 16] = b"0123456789abcdef";
                self.bytes(&value.as_bytes()[start..index])?;
                self.bytes(&[
                    b'\\',
                    b'u',
                    b'0',
                    b'0',
                    HEX[usize::from(byte >> 4)],
                    HEX[usize::from(byte & 15)],
                ])?;
                start = index + 1;
            }
        }
        self.bytes(&value.as_bytes()[start..])
    }
    fn string(&mut self, value: &str) -> Result<()> {
        self.raw("\"")?;
        self.escaped(value)?;
        self.raw("\"")
    }
    fn name(&mut self, name: Name<'_>) -> Result<()> {
        self.raw("\"")?;
        match name {
            Name::Direct(value) => self.escaped(value)?,
            Name::Tester(value) => {
                self.raw("is-")?;
                self.escaped(value)?;
            }
        }
        self.raw("\"")
    }
    fn optional(&mut self, value: Option<&str>) -> Result<()> {
        match value {
            Some(value) => self.string(value),
            None => self.null(),
        }
    }
    fn display(&mut self, value: &impl fmt::Display, quoted: bool) -> Result<()> {
        if quoted {
            self.raw("\"")?;
        }
        struct Adapter<'a, 'b, 'c> {
            json: &'a mut Json<'b, 'c>,
            quoted: bool,
        }
        impl fmt::Write for Adapter<'_, '_, '_> {
            fn write_str(&mut self, value: &str) -> fmt::Result {
                (if self.quoted {
                    self.json.escaped(value)
                } else {
                    self.json.raw(value)
                })
                .map_err(|_| fmt::Error)
            }
        }
        if write!(Adapter { json: self, quoted }, "{value}").is_err() {
            return self.meter.fail(Error::Encoding);
        }
        if quoted {
            self.raw("\"")?;
        }
        Ok(())
    }
    fn number(&mut self, value: impl fmt::Display) -> Result<()> {
        self.display(&value, false)
    }

    fn enter(&mut self) -> Result<()> {
        let next = self.depth.saturating_add(1);
        self.meter.depth(next)?;
        // The existing v1 JSON reader has serde_json's default finite nesting
        // envelope. Never emit a document that its own reader cannot consume.
        if next > 128 {
            return self.meter.fail(Error::Limit {
                resource: Resource::Depth,
                limit: 128,
                requested: next,
            });
        }
        self.depth = next;
        Ok(())
    }
    fn object(&mut self, emit: impl FnOnce(&mut Object<'_, '_, '_>) -> Result<()>) -> Result<()> {
        self.enter()?;
        self.raw("{")?;
        emit(&mut Object {
            json: self,
            first: true,
        })?;
        self.raw("}")?;
        self.depth -= 1;
        Ok(())
    }
    fn array<T>(
        &mut self,
        values: impl IntoIterator<Item = T>,
        mut emit: impl FnMut(&mut Self, T) -> Result<()>,
    ) -> Result<()> {
        self.enter()?;
        self.raw("[")?;
        let mut first = true;
        for value in values {
            self.meter.poll()?;
            if !first {
                self.raw(",")?;
            }
            first = false;
            emit(self, value)?;
        }
        self.raw("]")?;
        self.depth -= 1;
        Ok(())
    }
    fn ids(&mut self, values: &[TermId]) -> Result<()> {
        self.array(values, |json, term| json.number(term.0))
    }
    fn sorts(&mut self, values: &[Sort], textual: bool) -> Result<()> {
        self.array(values, |json, sort| {
            if textual {
                json.display(sort, true)
            } else {
                json.sort(sort)
            }
        })
    }
    fn api_sort(&mut self, sort: ApiSort<'_>) -> Result<()> {
        match sort {
            ApiSort::Core(sort) => self.sort(sort),
            ApiSort::Datatype(datatype) => self.object(|o| {
                o.field("kind", |j| j.string("datatype"))?;
                o.field("datatype", |j| j.datatype(datatype))
            }),
            ApiSort::Bool => self.object(|o| o.field("kind", |j| j.string("bool"))),
        }
    }
    fn domain(&mut self, domain: Domain<'_>) -> Result<()> {
        match domain {
            Domain::Empty => self.array(std::iter::empty::<()>(), |_, _| Ok(())),
            Domain::Sorts(sorts) => self.sorts(sorts, false),
            Domain::Fields(fields) => self.array(fields, |j, field| j.sort(&field.sort)),
            Domain::Datatype(datatype) => self.array(std::iter::once(datatype), |j, datatype| {
                j.api_sort(ApiSort::Datatype(datatype))
            }),
        }
    }
    fn sort(&mut self, sort: &Sort) -> Result<()> {
        self.object(|o| match sort {
            Sort::Bool => o.field("kind", |j| j.string("bool")),
            Sort::Int => o.field("kind", |j| j.string("int")),
            Sort::Real => o.field("kind", |j| j.string("real")),
            Sort::String => o.field("kind", |j| j.string("string")),
            Sort::RegLan => o.field("kind", |j| j.string("reglan")),
            Sort::Char => o.field("kind", |j| j.string("char")),
            Sort::BitVec(sort) => {
                o.field("kind", |j| j.string("bitvec"))?;
                o.field("width", |j| j.number(sort.width))
            }
            Sort::Array(sort) => {
                o.field("kind", |j| j.string("array"))?;
                o.field("index", |j| j.sort(&sort.index_sort))?;
                o.field("element", |j| j.sort(&sort.element_sort))
            }
            Sort::FloatingPoint(exponent, significand) => {
                o.field("kind", |j| j.string("floating_point"))?;
                o.field("exponent", |j| j.number(exponent))?;
                o.field("significand", |j| j.number(significand))
            }
            Sort::Uninterpreted(name) | Sort::TypeVar(name) => {
                o.field("kind", |j| {
                    j.string(if matches!(sort, Sort::Uninterpreted(_)) {
                        "uninterpreted"
                    } else {
                        "type_var"
                    })
                })?;
                o.field("name", |j| j.string(name))
            }
            Sort::Datatype(datatype) => {
                o.field("kind", |j| j.string("datatype"))?;
                o.field("datatype", |j| j.datatype(datatype))
            }
            Sort::Seq(element) => {
                o.field("kind", |j| j.string("seq"))?;
                o.field("element", |j| j.sort(element))
            }
            Sort::FiniteDomain(name, size) => {
                o.field("kind", |j| j.string("finite_domain"))?;
                o.field("name", |j| j.string(name))?;
                o.field("size", |j| j.number(size))
            }
            _ => o.json.meter.fail(Error::UnsupportedSource {
                shape: "sort outside native v1",
            }),
        })
    }
    fn datatype(&mut self, datatype: &DatatypeSort) -> Result<()> {
        self.object(|o| {
            o.field("name", |j| j.string(&datatype.name))?;
            o.field("constructors", |j| {
                j.array(&datatype.constructors, |j, constructor| {
                    j.object(|o| {
                        o.field("name", |j| j.string(&constructor.name))?;
                        o.field("fields", |j| {
                            j.array(&constructor.fields, |j, field| {
                                j.object(|o| {
                                    o.field("name", |j| j.string(&field.name))?;
                                    o.field("sort", |j| j.display(&field.sort, true))?;
                                    o.field("sort_data", |j| j.sort(&field.sort))
                                })
                            })
                        })
                    })
                })
            })
        })
    }
    fn public_sort(&mut self, sort: &PublicSort) -> Result<()> {
        self.object(|o| match sort {
            PublicSort::Core(sort) => {
                o.field("kind", |j| j.string("core"))?;
                o.field("sort", |j| j.sort(sort))
            }
            PublicSort::Array(index, element) => {
                o.field("kind", |j| j.string("array"))?;
                o.field("index", |j| j.public_sort(index))?;
                o.field("element", |j| j.public_sort(element))
            }
            PublicSort::Seq(element)
            | PublicSort::FiniteSet(element)
            | PublicSort::AmbiguousSet(element) => {
                let kind = match sort {
                    PublicSort::Seq(_) => "seq",
                    PublicSort::FiniteSet(_) => "finite_set",
                    _ => "ambiguous_set",
                };
                o.field("kind", |j| j.string(kind))?;
                o.field("element", |j| j.public_sort(element))
            }
            PublicSort::Unknown => o.field("kind", |j| j.string("unknown")),
            _ => o.json.meter.fail(Error::UnsupportedSource {
                shape: "public sort outside native v1",
            }),
        })
    }
    fn symbol(&mut self, symbol: &Symbol) -> Result<()> {
        self.object(|o| match symbol {
            Symbol::Named(name) => {
                o.field("kind", |j| j.string("named"))?;
                o.field("name", |j| j.string(name.as_str()))
            }
            Symbol::Indexed(name, indices) => {
                o.field("kind", |j| j.string("indexed"))?;
                o.field("name", |j| j.string(name.as_str()))?;
                o.field("indices", |j| j.array(indices, |j, index| j.number(index)))
            }
            _ => o.json.meter.fail(Error::UnsupportedSource {
                shape: "symbol outside native v1",
            }),
        })
    }
    fn constant(&mut self, value: &Constant) -> Result<()> {
        self.object(|o| match value {
            Constant::Bool(value) => {
                o.field("kind", |j| j.string("bool"))?;
                o.field("value", |j| j.boolean(*value))
            }
            Constant::Int(value) => {
                o.field("kind", |j| j.string("int"))?;
                o.field("value", |j| j.display(value, true))
            }
            Constant::Rational(value) => {
                o.field("kind", |j| j.string("rational"))?;
                o.field("numerator", |j| j.display(value.0.numer(), true))?;
                o.field("denominator", |j| j.display(value.0.denom(), true))
            }
            Constant::BitVec { value, width } => {
                o.field("kind", |j| j.string("bitvec"))?;
                o.field("value", |j| j.display(value, true))?;
                o.field("width", |j| j.number(width))
            }
            Constant::String(value) => {
                o.field("kind", |j| j.string("string"))?;
                o.field("value", |j| j.string(value))
            }
            _ => o.json.meter.fail(Error::UnsupportedSource {
                shape: "constant outside native v1",
            }),
        })
    }
    fn term_data(&mut self, data: &TermData) -> Result<()> {
        self.object(|o| match data {
            TermData::Const(value) => {
                o.field("kind", |j| j.string("const"))?;
                o.field("value", |j| j.constant(value))
            }
            TermData::Var(name, id) => {
                o.field("kind", |j| j.string("var"))?;
                o.field("name", |j| j.string(name))?;
                o.field("var_id", |j| j.number(id))
            }
            TermData::App(symbol, args) => {
                o.field("kind", |j| j.string("app"))?;
                o.field("symbol", |j| j.symbol(symbol))?;
                o.field("args", |j| j.ids(args))
            }
            TermData::Let(bindings, body) => {
                o.field("kind", |j| j.string("let"))?;
                o.field("bindings", |j| {
                    j.array(bindings, |j, (name, term)| {
                        j.object(|o| {
                            o.field("name", |j| j.string(name))?;
                            o.field("term", |j| j.number(term.0))
                        })
                    })
                })?;
                o.field("body", |j| j.number(body.0))
            }
            TermData::Not(inner) => {
                o.field("kind", |j| j.string("not"))?;
                o.field("inner", |j| j.number(inner.0))
            }
            TermData::Ite(cond, yes, no) => {
                o.field("kind", |j| j.string("ite"))?;
                o.field("cond", |j| j.number(cond.0))?;
                o.field("then", |j| j.number(yes.0))?;
                o.field("else", |j| j.number(no.0))
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                o.field("kind", |j| {
                    j.string(if matches!(data, TermData::Forall(..)) {
                        "forall"
                    } else {
                        "exists"
                    })
                })?;
                o.field("vars", |j| {
                    j.array(vars, |j, (name, sort)| {
                        j.object(|o| {
                            o.field("name", |j| j.string(name))?;
                            o.field("sort", |j| j.display(sort, true))?;
                            o.field("sort_data", |j| j.sort(sort))
                        })
                    })
                })?;
                o.field("body", |j| j.number(body.0))?;
                o.field("triggers", |j| {
                    j.array(triggers, |j, trigger| j.ids(trigger))
                })
            }
            _ => o.json.meter.fail(Error::UnsupportedSource {
                shape: "term outside native v1",
            }),
        })
    }
    fn event_kind(&mut self, event: &NativeReplayEventKind) -> Result<()> {
        self.object(|o| {
            let kind = match event {
                NativeReplayEventKind::SetLogic { .. } => "set_logic",
                NativeReplayEventKind::DeclareSort { .. } => "declare_sort",
                NativeReplayEventKind::DeclareConst { .. } => "declare_const",
                NativeReplayEventKind::DeclareFun { .. } => "declare_fun",
                NativeReplayEventKind::DeclareDatatype { .. } => "declare_datatype",
                NativeReplayEventKind::DeclareDatatypes { .. } => "declare_datatypes",
                NativeReplayEventKind::Assert { .. } => "assert",
                NativeReplayEventKind::Push => "push",
                NativeReplayEventKind::Pop => "pop",
                NativeReplayEventKind::Reset => "reset",
                NativeReplayEventKind::ResetAssertions => "reset_assertions",
                NativeReplayEventKind::CheckSat => "check_sat",
                NativeReplayEventKind::CheckSatAssuming { .. } => "check_sat_assuming",
            };
            o.field("event", |j| j.string(kind))?;
            match event {
                NativeReplayEventKind::SetLogic { logic } => o.field("logic", |j| j.string(logic)),
                NativeReplayEventKind::DeclareSort { name, core_name } => {
                    o.field("name", |j| j.string(name))?;
                    o.field("core_name", |j| j.string(core_name))
                }
                NativeReplayEventKind::DeclareConst { name, term, sort } => {
                    o.field("name", |j| j.string(name))?;
                    o.field("term", |j| j.number(term.0))?;
                    o.field("sort", |j| j.display(sort, true))?;
                    o.field("sort_data", |j| j.sort(sort))
                }
                NativeReplayEventKind::DeclareFun {
                    name,
                    domain,
                    range,
                } => {
                    o.field("name", |j| j.string(name))?;
                    o.field("domain", |j| j.sorts(domain, true))?;
                    o.field("domain_data", |j| j.sorts(domain, false))?;
                    o.field("range", |j| j.display(range, true))?;
                    o.field("range_data", |j| j.sort(range))
                }
                NativeReplayEventKind::DeclareDatatype { datatype } => {
                    o.field("name", |j| j.string(&datatype.name))?;
                    o.field("constructors", |j| {
                        j.array(&datatype.constructors, |j, constructor| {
                            j.object(|o| {
                                o.field("name", |j| j.string(&constructor.name))?;
                                o.field("fields", |j| {
                                    j.array(&constructor.fields, |j, field| {
                                        j.object(|o| {
                                            o.field("name", |j| j.string(&field.name))?;
                                            o.field("sort", |j| j.display(&field.sort, true))?;
                                            o.field("sort_data", |j| j.sort(&field.sort))
                                        })
                                    })
                                })
                            })
                        })
                    })
                }
                NativeReplayEventKind::DeclareDatatypes { datatypes } => o
                    .field("datatypes", |j| {
                        j.array(datatypes, |j, datatype| j.datatype(datatype))
                    }),
                NativeReplayEventKind::Assert { term, name } => {
                    o.field("term", |j| j.number(term.0))?;
                    o.field("name", |j| j.optional(name.as_deref()))
                }
                NativeReplayEventKind::CheckSatAssuming { assumptions } => {
                    o.field("assumptions", |j| j.ids(assumptions))
                }
                _ => Ok(()),
            }
        })
    }
}

struct Object<'a, 'b, 'c> {
    json: &'a mut Json<'b, 'c>,
    first: bool,
}
impl Object<'_, '_, '_> {
    fn field(
        &mut self,
        name: &str,
        emit: impl FnOnce(&mut Json<'_, '_>) -> Result<()>,
    ) -> Result<()> {
        if !self.first {
            self.json.raw(",")?;
        }
        self.first = false;
        self.json.string(name)?;
        self.json.raw(":")?;
        emit(self.json)
    }
}

fn emit(plan: &Plan<'_>, json: &mut Json<'_, '_>) -> Result<()> {
    json.object(|o| {
        o.field("schema", |j| j.string(NATIVE_REPLAY_SCHEMA))?;
        o.field("ay_revision", |j| {
            j.string(
                option_env!("AY_BUILD_COMMIT")
                    .or(option_env!("VERGEN_GIT_SHA"))
                    .or(option_env!("GIT_SHA"))
                    .unwrap_or("unknown"),
            )
        })?;
        o.field("ay_version", |j| j.string(env!("CARGO_PKG_VERSION")))?;
        o.field("created_unix_ms", |j| {
            j.display(&plan.created_unix_ms, true)
        })?;
        o.field("metadata", |j| {
            j.object(|o| {
                let metadata = plan.metadata;
                for (key, value) in [
                    ("consumer", &metadata.consumer),
                    ("consumer_revision", &metadata.consumer_revision),
                    ("fixture_path", &metadata.fixture_path),
                    ("function_path", &metadata.function_path),
                    ("source_span", &metadata.source_span),
                    ("obligation_kind", &metadata.obligation_kind),
                    ("notes", &metadata.notes),
                ] {
                    o.field(key, |j| j.optional(value.as_deref()))?;
                }
                Ok(())
            })
        })?;
        o.field("logic", |j| j.optional(plan.logic))?;
        o.field("selected_route", |j| {
            if let Some(logic) = plan.logic {
                j.raw("\"")?;
                j.raw("native-api:")?;
                j.escaped(logic)?;
                j.raw("\"")
            } else {
                j.null()
            }
        })?;
        o.field("scope_depth", |j| j.number(plan.solver.scope_level))?;
        o.field("timeout_ms", |j| match plan.solver.timeout {
            Some(timeout) => j.display(&timeout.as_millis(), true),
            None => j.null(),
        })?;
        o.field("events", |j| {
            j.array(&plan.solver.native_replay_events, |j, event| {
                j.object(|o| {
                    o.field("index", |j| j.number(event.index))?;
                    o.field("scope_depth", |j| j.number(event.scope_depth))?;
                    o.field("kind", |j| j.event_kind(&event.kind))
                })
            })
        })?;
        o.field("declarations", |j| {
            j.array(&plan.declarations, |j, declaration| {
                j.object(|o| {
                    o.field("name", |j| j.string(declaration.name))?;
                    o.field("core_name", |j| j.string(declaration.core))?;
                    o.field("term", |j| j.number(declaration.term.0))?;
                    o.field("sort", |j| j.display(declaration.sort, true))?;
                    o.field("sort_data", |j| j.sort(declaration.sort))
                })
            })
        })?;
        o.field("sort_declarations", |j| {
            j.array(&plan.sort_declarations, |j, declaration| {
                j.object(|o| {
                    o.field("name", |j| j.string(declaration.name))?;
                    o.field("core_name", |j| j.string(declaration.core))
                })
            })
        })?;
        o.field("function_declarations", |j| {
            j.array(&plan.functions, |j, function| {
                j.object(|o| {
                    o.field("name", |j| j.string(function.name))?;
                    o.field("core_name", |j| j.string(function.core))?;
                    o.field("domain", |j| j.sorts(function.domain, true))?;
                    o.field("domain_data", |j| j.sorts(function.domain, false))?;
                    o.field("range", |j| j.display(function.range, true))?;
                    o.field("range_data", |j| j.sort(function.range))
                })
            })
        })?;
        o.field("symbol_identities", |j| {
            j.array(&plan.identities, |j, identity| {
                j.object(|o| {
                    o.field("surface_name", |j| j.name(identity.surface))?;
                    o.field("core_name", |j| j.string(identity.core))?;
                    o.field("api_domain", |j| j.domain(identity.domain))?;
                    o.field("api_range", |j| j.api_sort(identity.range))?;
                    o.field("public_domain", |j| {
                        j.array(&identity.info.public_arg_sorts, |j, sort| {
                            j.public_sort(sort)
                        })
                    })?;
                    o.field("public_range", |j| {
                        j.public_sort(&identity.info.public_sort)
                    })?;
                    o.field("engine_domain", |j| {
                        j.sorts(&identity.info.arg_sorts, false)
                    })?;
                    o.field("engine_range", |j| j.sort(&identity.info.sort))?;
                    o.field("kind", |j| j.string(symbol_kind_json(identity.kind)))?;
                    o.field("datatype_surface", |j| {
                        j.optional(identity.datatype.map(|(surface, _)| surface))
                    })?;
                    o.field("datatype_core", |j| {
                        j.optional(identity.datatype.map(|(_, core)| core))
                    })
                })
            })
        })?;
        o.field("assertions", |j| {
            j.array(
                plan.assertions.iter().enumerate(),
                |j, (index, assertion)| {
                    j.object(|o| {
                        o.field("index", |j| j.number(index))?;
                        o.field("term", |j| j.number(assertion.term.0))?;
                        o.field("name", |j| j.optional(assertion.name))?;
                        o.field("scope_depth", |j| j.number(assertion.scope_depth))
                    })
                },
            )
        })?;
        o.field("terms", |j| {
            j.array(&plan.terms, |j, &term| {
                j.object(|o| {
                    let data = plan.solver.terms().get(term);
                    let constructor = match data {
                        TermData::Var(name, _) => {
                            let context = plan.solver.executor.context();
                            super::meter::constructor_lookup(context, name, o.json.meter)?;
                            context.constructor_metadata(name).is_some()
                                && context
                                    .symbol_info_by_identity(name)
                                    .is_some_and(|info| info.term == Some(term))
                        }
                        _ => false,
                    };
                    o.field("id", |j| j.number(term.0))?;
                    o.field("sort", |j| j.display(plan.solver.terms().sort(term), true))?;
                    o.field("sort_data", |j| j.sort(plan.solver.terms().sort(term)))?;
                    o.field("data", |j| j.term_data(data))?;
                    o.field("is_datatype_constructor", |j| j.boolean(constructor))
                })
            })
        })?;
        for field in ["solve", "checked_replay", "panic_payload"] {
            o.field(field, |j| j.null())?;
        }
        o.field("unsupported_atoms", |j| {
            j.array(std::iter::empty::<()>(), |_, _| Ok(()))
        })?;
        o.field("replay_gaps", |j| {
            j.array(["solve details were not captured"], |j, gap| j.string(gap))
        })
    })
}

pub(super) fn input(plan: &Plan<'_>, meter: &mut Meter<'_>) -> Result<String> {
    let mut count = Json {
        meter,
        sink: Sink::Count(0),
        depth: 0,
    };
    emit(plan, &mut count)?;
    let Sink::Count(length) = count.sink else {
        return count.meter.fail(Error::Encoding);
    };
    // Charge before the sole JSON output allocation. No artifact or Value tree
    // exists, and every subsequent append checks this exact admitted length.
    count.meter.charge(0, length)?;
    let mut value = Vec::new();
    if value.try_reserve_exact(length).is_err() {
        return count.meter.fail(Error::Allocation);
    }
    let mut output = Json {
        meter: count.meter,
        sink: Sink::Bytes {
            value,
            admitted: length,
        },
        depth: 0,
    };
    emit(plan, &mut output)?;
    let Sink::Bytes { value, .. } = output.sink else {
        return output.meter.fail(Error::Encoding);
    };
    if value.len() != length {
        return output.meter.fail(Error::Encoding);
    }
    match String::from_utf8(value) {
        Ok(value) => Ok(value),
        Err(_) => output.meter.fail(Error::Encoding),
    }
}
