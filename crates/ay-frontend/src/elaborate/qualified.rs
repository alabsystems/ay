// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;

use crate::command::{self, Term as ParsedTerm};
use ay_core::{Symbol, TermId};

use super::{Context, ElaborateError, Result};

impl Context {
    /// Elaborate a qualified application `(as <id> <sort>)` with args.
    ///
    /// Handles structured qualified identifiers parsed by `command.rs`,
    /// avoiding the string-prefix matching that `elaborate_app` uses for
    /// legacy `App` nodes with stringified qualified names.
    pub(super) fn elaborate_qualified_app(
        &mut self,
        name: &str,
        parsed_sort: &command::Sort,
        args: &[ParsedTerm],
        env: &HashMap<String, TermId>,
    ) -> Result<TermId> {
        let sort = self.elaborate_sort(parsed_sort)?;
        let arg_ids: Vec<TermId> = args
            .iter()
            .map(|a| self.elaborate_term(a, env))
            .collect::<Result<Vec<_>>>()?;

        match name {
            "seq.empty" => Ok(self.terms.mk_app(Symbol::named("seq.empty"), vec![], sort)),
            // `(as set.empty (Set T))` is the empty set over the membership
            // carrier `Array(T -> Bool)`: the constant-false array. This is
            // sound and array-decidable: `select(empty, e) = false` for all `e`
            // with no quantifier instantiation.
            "set.empty" => {
                self.expect_exact_arity("set.empty", &arg_ids, 0)?;
                let index_sort = sort.array_index().cloned().ok_or_else(|| {
                    ElaborateError::InvalidConstant(format!(
                        "set.empty requires a (Set T) / Array sort annotation, got: {sort:?}"
                    ))
                })?;
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
                let zero = self.terms.mk_int(num_bigint::BigInt::from(0));
                Ok(self.terms.mk_const_array(index_sort, zero))
            }
            // `(as map.empty (Map K V))` is the empty map. Its value carrier is a
            // const array over an arbitrary V default (never observed: the empty
            // map's domain is all-false, so `(map.dom empty) = const-false` gates
            // every read). A const-array value carrier marks the empty map so
            // `map.dom` elaborates its domain to the constant-false array. Sound
            // and array-decidable with no quantifier instantiation.
            "map.empty" => {
                self.expect_exact_arity("map.empty", &arg_ids, 0)?;
                let index_sort = sort.array_index().cloned().ok_or_else(|| {
                    ElaborateError::InvalidConstant(format!(
                        "map.empty requires a (Map K V) / Array sort annotation, got: {sort:?}"
                    ))
                })?;
                let value_sort = sort.array_element().cloned().ok_or_else(|| {
                    ElaborateError::InvalidConstant(format!(
                        "map.empty requires a (Map K V) / Array sort annotation, got: {sort:?}"
                    ))
                })?;
                // Arbitrary default value of sort V: unobserved (dom is false).
                let default = self.terms.mk_fresh_var("map_empty_default", value_sort);
                Ok(self.terms.mk_const_array(index_sort, default))
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
                Ok(self.terms.mk_const_array(index_sort, arg_ids[0]))
            }
            _ => {
                // A qualified nullary application `(as <name> <sort>)` with no
                // arguments must elaborate to the SAME term as the bare
                // identifier `<name>`. In particular a nullary datatype
                // constructor is stored as a `Var` term, not a 0-ary `App`
                // (#1745); emitting `App(name, [])` here yields a term the DT
                // axiom machinery does not recognize as that constructor, leaving
                // construct/select/equality goals `unknown` (e.g. the Rust
                // unit-variant pattern `(as A E)`). Reuse the declared symbol's
                // bound term when it exists and matches the ascribed sort.
                if arg_ids.is_empty() {
                    // A nullary symbol may be overloaded across datatype instances
                    // (e.g. `nil` for both `(Lst Int)` and `(Lst Bool)`); pick the
                    // overload whose result sort matches the ascription so two
                    // parametric instantiations coexist.
                    if let Some(term) = self.nullary_overload_with_sort(name, &sort) {
                        return Ok(term);
                    }
                    if let Some(term) = self.symbols.get(name).and_then(|info| info.term) {
                        if *self.terms.sort(term) == sort {
                            return Ok(term);
                        }
                    }
                }
                // A non-nullary parametric-datatype constructor ascribed with its
                // instance sort (`((as osome (Opt Bool)) x)`) must build the
                // instance-internal (mangled) symbol so the DT theory recognizes
                // it as that instance's constructor. The ascribed result sort
                // selects the instance.
                let internal = self
                    .ctor_internal_for_result_sort(name, &sort)
                    .unwrap_or_else(|| name.to_string());
                // Generic qualified identifier: use sort as return type
                Ok(self.terms.mk_app(Symbol::named(&internal), arg_ids, sort))
            }
        }
    }
}
