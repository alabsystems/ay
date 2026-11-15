// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;

use crate::command::{self, QualifiedIdentifier, Term as ParsedTerm};
use ay_core::{Sort, Symbol, TermData, TermId};

use super::{Context, ElaborateError, Result};

impl Context {
    /// Elaborate a qualified application `(as <id> <sort>)` with args.
    ///
    /// Handles structured qualified identifiers parsed by `command.rs`,
    /// avoiding the string-prefix matching that `elaborate_app` uses for
    /// legacy `App` nodes with stringified qualified names.
    pub(super) fn elaborate_qualified_app(
        &mut self,
        identifier: &QualifiedIdentifier,
        parsed_sort: &command::Sort,
        args: &[ParsedTerm],
        env: &HashMap<String, TermId>,
    ) -> Result<TermId> {
        let name = match identifier {
            QualifiedIdentifier::Symbol(name) => name.as_str(),
            QualifiedIdentifier::Indexed(name, indices) => {
                return Err(ElaborateError::Unsupported(format!(
                    "qualified indexed identifier is unsupported: (_ {name} {})",
                    indices
                        .iter()
                        .map(command::Index::text)
                        .collect::<Vec<_>>()
                        .join(" ")
                )));
            }
        };
        let sort = self.elaborate_sort(parsed_sort)?;
        let mut arg_ids: Vec<TermId> = args
            .iter()
            .map(|a| self.elaborate_term(a, env))
            .collect::<Result<Vec<_>>>()?;

        match name {
            "seq.empty" => {
                self.expect_exact_arity("seq.empty", &arg_ids, 0)?;
                if !matches!(sort, Sort::Seq(_)) {
                    return Err(ElaborateError::SortMismatch {
                        expected: "(Seq _)".to_string(),
                        actual: sort.to_string(),
                    });
                }
                Ok(self.terms.mk_app(Symbol::named("seq.empty"), vec![], sort))
            }
            // `(as set.empty (Set T))` and Z3 5.0.0's
            // `(as set.empty (FiniteSet T))` are the empty set over the
            // membership carrier `Array(T -> Bool)`: the constant-false array.
            // This is sound and array-decidable:
            // `select(empty, e) = false` for all `e` with no quantifier
            // instantiation.
            "set.empty" => {
                self.expect_exact_arity("set.empty", &arg_ids, 0)?;
                let index_sort = sort.array_index().cloned().ok_or_else(|| {
                    ElaborateError::InvalidConstant(format!(
                        "set.empty requires a (Set T), (FiniteSet T), or Array(_, Bool) sort annotation, got: {sort:?}"
                    ))
                })?;
                if sort.array_element() != Some(&Sort::Bool) {
                    return Err(ElaborateError::SortMismatch {
                        expected: "(Set _) / (FiniteSet _) carried as (Array _ Bool)".to_string(),
                        actual: sort.to_string(),
                    });
                }
                let false_t = self.terms.false_term();
                Ok(self.terms.mk_const_array(index_sort, false_t))
            }
            // `(as multiset.empty (Multiset T))` is the empty multiset over the
            // count carrier `Array(T -> Int)`: the constant-0 array. Sound and
            // array-decidable: `count(empty, e) = select(empty, e) = 0` for all
            // `e` with no quantifier instantiation.
            "multiset.empty" => {
                self.expect_exact_arity("multiset.empty", &arg_ids, 0)?;
                let index_sort = sort.array_index().cloned().ok_or_else(|| {
                    ElaborateError::InvalidConstant(format!(
                        "multiset.empty requires a (Multiset T) / Array sort annotation, got: {sort:?}"
                    ))
                })?;
                if sort.array_element() != Some(&Sort::Int) {
                    return Err(ElaborateError::SortMismatch {
                        expected: "(Multiset _) carried as (Array _ Int)".to_string(),
                        actual: sort.to_string(),
                    });
                }
                let zero = self.terms.mk_int(num_bigint::BigInt::from(0));
                Ok(self.terms.mk_const_array(index_sort, zero))
            }
            // `(as map.empty (Map K V))` is the empty map: the sort's one
            // unconstrained value array, whose domain `map.dom` elaborates to
            // the constant-false array (see `Context::native_empty_map`).
            "map.empty" => {
                self.expect_exact_arity("map.empty", &arg_ids, 0)?;
                if sort.array_index().is_none() {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "map.empty requires a (Map K V) / Array sort annotation, got: {sort:?}"
                    )));
                }
                self.mark_uses_map();
                Ok(self.native_empty_map(sort))
            }
            // Constant array: ((as const (Array T1 T2)) value).
            //
            // Guarded on `const` NOT being a declared user symbol: unlike the
            // dotted ay-extension names above (set.empty/…, which are
            // statically reserved), `const` IS legitimately user-declarable —
            // real-world QF_UF benchmarks declare it (the B-method CLEARSY
            // fixtures declare `(declare-fun |const| (U U) U)`). When the user
            // has declared `const`, every use — bare application AND `(as
            // const <sort>)` — must denote THEIR symbol (the `_` fallback arm
            // below, a plain uninterpreted application; nothing in the term
            // layer matches bare `const` structurally), never the builtin
            // constant array. Matching the builtin here regardless of the
            // declaration was a confirmed wrong-UNSAT (rc_const_as.smt2: a
            // declared `const` used under `(as const (Array Int Int))` was
            // folded to the builtin all-7 array). Scripts that want the
            // builtin constant array simply do not declare `const`.
            "const"
                if !self.symbols.contains_key("const") && !self.fun_defs.contains_key("const") =>
            {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "constant array requires exactly 1 argument".to_string(),
                    ));
                }
                let index_sort = sort.array_index().cloned().ok_or_else(|| {
                    ElaborateError::InvalidConstant(format!(
                        "expected Array sort in const, got: {sort:?}"
                    ))
                })?;
                let expected = sort.array_element().cloned().ok_or_else(|| {
                    ElaborateError::InvalidConstant(format!(
                        "expected Array sort in const, got: {sort:?}"
                    ))
                })?;
                let actual = self.terms.sort(arg_ids[0]).clone();
                if self.int_real_coercions() && actual == Sort::Int && expected == Sort::Real {
                    arg_ids[0] = self.coerce_int_to_real(arg_ids[0]);
                } else if actual != expected {
                    return Err(ElaborateError::SortMismatch {
                        expected: expected.to_string(),
                        actual: actual.to_string(),
                    });
                }
                // At a map sort this is no map the encoding has a domain for
                // (it is not the empty map); the native-map gate withholds a
                // `sat` that rests on it (#map-value-semantics).
                if self.parsed_sort_is_map(parsed_sort) {
                    self.map_constant_array = true;
                }
                Ok(self.terms.mk_const_array(index_sort, arg_ids[0]))
            }
            _ => {
                // Definitions are macros, not free declarations. A generic
                // qualified application must still expand the body, after
                // checking that the result ascription selects that definition.
                if let Some((_params, result_sort, _body)) = self.fun_defs.get(name) {
                    if result_sort != &sort {
                        return Err(ElaborateError::SortMismatch {
                            expected: result_sort.to_string(),
                            actual: sort.to_string(),
                        });
                    }
                    return self.elaborate_app(name, args, env);
                }

                // Resolve the whole signature, including the result ascription.
                // This covers ordinary declarations and datatype members. It is
                // also what preserves the selected private identity for native
                // aliases and instance-mangled parametric constructors.
                let declared = self.resolve_qualified_declared_symbol(name, &sort, &arg_ids)?;
                if declared.is_none() {
                    if let Sort::FiniteField(field) = sort {
                        if let Some(value) = name.strip_prefix("ff") {
                            if !arg_ids.is_empty() {
                                return Err(ElaborateError::InvalidConstant(
                                    "field numeral requires no arguments".into(),
                                ));
                            }
                            let n: num_bigint::BigInt = value
                                .parse()
                                .map_err(|_| ElaborateError::InvalidConstant(name.into()))?;
                            let p = num_bigint::BigInt::from(field.modulus());
                            use num_traits::ToPrimitive;
                            let residue = ((n % &p + &p) % &p)
                                .to_u32()
                                .ok_or_else(|| ElaborateError::InvalidConstant(name.into()))?;
                            return Ok(self.terms.mk_finite_field(residue, field));
                        }
                    }
                }
                let info=declared.ok_or_else(||ElaborateError::InvalidConstant(format!(
                    "no declaration of '{name}' matches qualified result {sort} and the supplied arguments"
                )))?;
                self.validate_application_signature(name, &info.arg_sorts, &mut arg_ids)?;

                // A qualified nullary constructor/constant denotes the exact
                // same bound term as its bare spelling. In particular, datatype
                // axiom recognition depends on the TermId identity here.
                if arg_ids.is_empty() {
                    if let Some(term) = info.term {
                        return Ok(term);
                    }
                }

                if name == "to_real" {
                    self.terms.mark_to_real_shadowed();
                }
                if name == "is_int" {
                    self.terms.mark_is_int_shadowed();
                }
                let internal = info.internal_name.as_deref().unwrap_or(name);
                // Preserve the fully validated, result-qualified identity. Fold
                // only a constructor-owned selector; wrong constructors and
                // ordinary functions stay opaque. Restrict this to App arguments
                // so the helper cannot enter its recursive ITE-distribution path.
                if arg_ids.len() == 1 && matches!(self.terms.get(arg_ids[0]), TermData::App(..)) {
                    return Ok(self.mk_datatype_selector(internal, &sort, arg_ids[0]));
                }
                Ok(self.terms.mk_app(Symbol::named(internal), arg_ids, sort))
            }
        }
    }
}
