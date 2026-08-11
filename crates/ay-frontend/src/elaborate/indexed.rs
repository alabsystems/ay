// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;

use crate::command::Index as ParsedIndex;
use crate::command::Sort as CmdSort;
use crate::command::Term as ParsedTerm;
use ay_core::{Sort, Symbol, TermId};
use num_bigint::{BigInt, Sign};
use num_rational::BigRational;

use super::{Context, ElaborateError, Result, SymbolInfo, MAX_FUN_EXPANSION_DEPTH};

/// Indexed identifiers whose indices must all be u32 numerals. Used by the
/// up-front index validation in [`Context::elaborate_indexed_app`]; symbol- and
/// `BigInt`-indexed identifiers must stay off this list.
const NUMERAL_INDEXED: &[&str] = &[
    "extract",
    "int2bv",
    "zero_extend",
    "sign_extend",
    "rotate_left",
    "rotate_right",
    "repeat",
    "re.loop",
    "re.^",
    "to_fp",
    "to_fp_unsigned",
    "fp.to_ubv",
    "fp.to_sbv",
    "divisible",
];

/// Z3 5.0.0 installs its pseudo-Boolean declaration plugin only in the null,
/// QF_FD, ALL, and HORN signatures.
const PB_INDEXED: &[&str] = &["at-most", "at-least", "pble", "pbge", "pbeq"];

/// Comparison operator for a pseudo-boolean / cardinality constraint.
#[derive(Clone, Copy)]
enum PbCmp {
    /// `sum <= k`  (`pble`, `at-most`)
    Le,
    /// `sum >= k`  (`pbge`, `at-least`)
    Ge,
    /// `sum = k`   (`pbeq`)
    Eq,
}

impl Context {
    /// Elaborate an indexed application `((_ name idx...) arg1 arg2 ...)`.
    ///
    /// Handles structured indexed identifiers parsed by `command.rs` as
    /// `IndexedApp(name, indices, args)`, avoiding the stringify-then-reparse
    /// anti-pattern where `(_ extract 7 0)` was encoded as `App("(_ extract 7 0)", args)`
    /// and re-parsed via `name.starts_with("(_ ")` + `split_whitespace`.
    pub(super) fn elaborate_indexed_app(
        &mut self,
        name: &str,
        parsed_indices: &[ParsedIndex],
        args: &[ParsedTerm],
        env: &HashMap<String, TermId>,
    ) -> Result<TermId> {
        // SMT-LIB datatype tester: (_ is Constructor) → normalize to "is-Ctor"
        // and delegate to elaborate_app which handles function defs and symbol lookup.
        if name == "is" {
            let [ParsedIndex::Symbol(ctor_name)] = parsed_indices else {
                return Err(ElaborateError::InvalidConstant(
                    "datatype tester requires exactly one constructor-symbol index".to_string(),
                ));
            };
            // Sole-constructor fold: `((_ is C) x)` is DEFINITIONALLY `true` when C
            // is the unique constructor of x's datatype — every value of a
            // single-constructor type satisfies its only recognizer. Folding it
            // lets a guard `(ite ((_ is C) x) a b)` collapse to its then-branch,
            // which the standalone DT occurs-check needs in order to detect a cycle
            // through the guarded branch (fuzzer-found QF_DT false-SAT: a forced-true
            // tester guard hid `v = left(v)`). Sound + general.
            if args.len() == 1 {
                let arg_id = self.elaborate_term(&args[0], env)?;
                let dt_name = match self.terms.sort(arg_id) {
                    Sort::Uninterpreted(n) => Some(n.clone()),
                    Sort::Datatype(dt) => Some(dt.name.clone()),
                    _ => None,
                };
                let is_sole_ctor = dt_name.as_deref().is_some_and(|dt| {
                    self.datatypes
                        .get(dt)
                        .is_some_and(|ctors| ctors.len() == 1 && ctors[0] == *ctor_name)
                });
                if is_sole_ctor {
                    return Ok(self.terms.true_term());
                }
            }
            let tester_name = format!("is-{ctor_name}");
            return self.elaborate_app(&tester_name, args, env);
        }

        if PB_INDEXED.contains(&name)
            && self
                .logic
                .as_deref()
                .is_some_and(|logic| !matches!(logic, "QF_FD" | "ALL" | "HORN"))
        {
            return Err(ElaborateError::UndefinedSymbol(name.to_string()));
        }

        let arg_ids: Vec<TermId> = args
            .iter()
            .map(|a| self.elaborate_term(a, env))
            .collect::<Result<Vec<_>>>()?;

        let indices: Vec<u32> = parsed_indices
            .iter()
            .filter_map(|index| index.as_numeral()?.parse().ok())
            .collect();

        // Arms below that consume `indices` require every index to be a u32
        // numeral. Reject unparseable/overflowing indices up front so the user
        // gets an accurate message instead of a misleading arity error (the
        // filter_map above silently drops indices that fail to parse). Arms
        // taking symbol indices (map/as-array, the special orders, the `_`
        // fallback) or BigInt numerals (the PB/cardinality operators) are
        // deliberately excluded.
        if NUMERAL_INDEXED.contains(&name) {
            if let Some(bad) = parsed_indices.iter().find(|index| {
                index
                    .as_numeral()
                    .and_then(|s| s.parse::<u32>().ok())
                    .is_none()
            }) {
                return Err(ElaborateError::InvalidConstant(format!(
                    "index '{}' of (_ {name} ...) must be a numeral fitting in u32",
                    bad.text()
                )));
            }
        }

        // Standalone indexed constants have no arguments. Keep this dispatch
        // on the structured parse variant so their spelling cannot alias a
        // legal quoted symbol such as `|(_ bv0 8)|`.
        if arg_ids.is_empty() {
            match name {
                "+zero" | "-zero" | "+oo" | "-oo" | "NaN" => {
                    if parsed_indices.len() != 2 {
                        return Err(ElaborateError::InvalidConstant(format!(
                            "FloatingPoint literal (_ {name} ...) requires exponent and significand widths"
                        )));
                    }
                    let eb_text = parsed_indices[0].as_numeral().ok_or_else(|| {
                        ElaborateError::InvalidConstant(format!(
                            "FloatingPoint exponent width `{}` must be a numeral",
                            parsed_indices[0].text()
                        ))
                    })?;
                    let eb = eb_text.parse::<u32>().map_err(|_| {
                        ElaborateError::InvalidConstant(format!(
                            "invalid FloatingPoint exponent width `{eb_text}`"
                        ))
                    })?;
                    let sb_text = parsed_indices[1].as_numeral().ok_or_else(|| {
                        ElaborateError::InvalidConstant(format!(
                            "FloatingPoint significand width `{}` must be a numeral",
                            parsed_indices[1].text()
                        ))
                    })?;
                    let sb = sb_text.parse::<u32>().map_err(|_| {
                        ElaborateError::InvalidConstant(format!(
                            "invalid FloatingPoint significand width `{sb_text}`"
                        ))
                    })?;
                    let fp_sort = Self::checked_floating_point_sort(eb, sb)?;
                    return Ok(self.terms.mk_app(
                        Symbol::indexed(name, vec![eb, sb]),
                        vec![],
                        fp_sort,
                    ));
                }
                _ => {}
            }

            if let Some(value_text) = name.strip_prefix("bv") {
                if value_text.is_empty()
                    || !value_text.chars().all(|c| c.is_ascii_digit())
                    || parsed_indices.len() != 1
                {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "malformed bitvector numeral: (_ {name} {})",
                        parsed_indices
                            .iter()
                            .map(ParsedIndex::text)
                            .collect::<Vec<_>>()
                            .join(" ")
                    )));
                }
                let value = value_text
                    .parse::<BigInt>()
                    .map_err(|_| ElaborateError::InvalidConstant(name.to_string()))?;
                let width = parsed_indices[0]
                    .as_numeral()
                    .and_then(|width| width.parse::<u32>().ok())
                    .ok_or_else(|| ElaborateError::InvalidConstant(name.to_string()))?;
                Self::checked_bitvector_sort(width)?;
                return Ok(self.terms.mk_bitvec(value, width));
            }

            if name == "Char" || name == "char" {
                if parsed_indices.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "character literal requires exactly one index, got {}",
                        parsed_indices.len()
                    )));
                }
                let raw = parsed_indices[0].text();
                let code = match &parsed_indices[0] {
                    ParsedIndex::Numeral(decimal) => decimal.parse::<BigInt>().ok(),
                    ParsedIndex::Hexadecimal(hexadecimal) => hexadecimal
                        .strip_prefix("#x")
                        .and_then(|hex| BigInt::parse_bytes(hex.as_bytes(), 16)),
                    ParsedIndex::Binary(binary) => binary
                        .strip_prefix("#b")
                        .and_then(|bits| BigInt::parse_bytes(bits.as_bytes(), 2)),
                    _ => None,
                }
                .ok_or_else(|| ElaborateError::InvalidConstant(format!("(_ {name} {raw})")))?;
                if code.sign() == Sign::Minus || code > BigInt::from(0x2_FFFFu32) {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "character code point `{raw}` is outside 0..=196607"
                    )));
                }
                return Ok(self.terms.mk_int(code));
            }
        }

        match name {
            // Datatype field update: `((_ update-field <sel>) record value)` —
            // z3's OP_DT_UPDATE_FIELD. Returns `record` with the field selected
            // by `<sel>` set to `value`, and `record` UNCHANGED when its
            // constructor lacks that field. A selector belongs to exactly one
            // constructor C (SMT-LIB selector names are per-datatype unique), so
            // this desugars to `ite(is-C record, C(f1(record), … value@sel …,
            // fn(record)), record)`; the selector-over-constructor reduction then
            // evaluates it. MONOMORPHIC datatypes only — anything uncertain
            // (parametric/mangled, non-datatype/unknown sort, `sel` not a
            // selector of the sort, or a `value` whose sort disagrees with the
            // field) falls back to an error the CLI fails closed to `unknown`,
            // never a wrong reconstruction. Verified EXACT vs z3. (was: hard
            // "unknown indexed identifier" error → unknown.)
            "update-field" => {
                if parsed_indices.len() != 1 || arg_ids.len() != 2 {
                    return Err(ElaborateError::Unsupported(
                        "update-field requires 1 selector index and 2 arguments".to_string(),
                    ));
                }
                let sel = parsed_indices[0].as_symbol().ok_or_else(|| {
                    ElaborateError::Unsupported(
                        "update-field selector index must be a symbol".to_string(),
                    )
                })?;
                let (record, value) = (arg_ids[0], arg_ids[1]);
                let record_sort = self.terms.sort(record).clone();
                let dt_name = match &record_sort {
                    Sort::Uninterpreted(n) => n.clone(),
                    Sort::Datatype(dt) => dt.name.clone(),
                    _ => {
                        return Err(ElaborateError::Unsupported(
                            "update-field on a non-datatype term".to_string(),
                        ))
                    }
                };
                // Parametric instances carry mangled constructor/selector names
                // we don't reconstruct here — fall back so they fail closed.
                if self.parametric_datatypes.contains_key(&dt_name) {
                    return Err(ElaborateError::Unsupported(
                        "update-field over a parametric datatype".to_string(),
                    ));
                }
                let Some(ctor_names) = self.datatypes.get(&dt_name).cloned() else {
                    return Err(ElaborateError::Unsupported(
                        "update-field over an unknown datatype".to_string(),
                    ));
                };
                // Find the unique constructor owning `sel`; clone its (name,sort)
                // field list to release the &self borrow before building terms.
                let mut owner: Option<(String, Vec<(String, Sort)>)> = None;
                for c in &ctor_names {
                    if let Some(fields) = self.constructor_selector_info(c) {
                        if fields.iter().any(|(fname, _)| fname == sel) {
                            owner = Some((c.clone(), fields.to_vec()));
                            break;
                        }
                    }
                }
                let Some((ctor, fields)) = owner else {
                    return Err(ElaborateError::Unsupported(format!(
                        "update-field: '{sel}' is not a selector of datatype '{dt_name}'"
                    )));
                };
                // The value must match the field's declared sort, else the
                // rebuilt constructor is ill-sorted — fail closed instead.
                let value_sort = self.terms.sort(value).clone();
                let sel_sort = fields
                    .iter()
                    .find(|(f, _)| f == sel)
                    .map(|(_, s)| s.clone());
                if sel_sort.as_ref() != Some(&value_sort) {
                    return Err(ElaborateError::SortMismatch {
                        expected: sel_sort.map(|s| s.to_string()).unwrap_or_default(),
                        actual: value_sort.to_string(),
                    });
                }
                // Rebuild C: the selected field becomes `value`, every other
                // field is taken from `record` via its selector.
                let mut field_args: Vec<TermId> = Vec::with_capacity(fields.len());
                for (fname, fsort) in &fields {
                    if fname == sel {
                        field_args.push(value);
                    } else {
                        field_args.push(self.terms.mk_app(
                            Symbol::named(fname.as_str()),
                            [record],
                            fsort.clone(),
                        ));
                    }
                }
                let reconstructed = self.terms.mk_app(
                    Symbol::named(ctor.as_str()),
                    &field_args,
                    record_sort.clone(),
                );
                if ctor_names.len() == 1 {
                    // `record` is always C — no tester guard needed.
                    Ok(reconstructed)
                } else {
                    // Unchanged when `record` is a different constructor.
                    let tester = self.terms.mk_app(
                        Symbol::named(format!("is-{ctor}").as_str()),
                        [record],
                        Sort::Bool,
                    );
                    Ok(self.terms.mk_ite(tester, reconstructed, record))
                }
            }
            // Array map: ((_ map f) a1 a2 ... an)
            // Applies function f pointwise: select(map[f](a1,...,an), i) = f(select(a1,i),...,select(an,i))
            // The "index" is the function name f (a symbol, not a numeral).
            // Z3 ref: array_decl_plugin.cpp:458-463, OP_ARRAY_MAP
            "map" => {
                if parsed_indices.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "map requires exactly 1 index (the function name)".to_string(),
                    ));
                }
                let func_name = parsed_indices[0].as_symbol().ok_or_else(|| {
                    ElaborateError::InvalidConstant(
                        "map index must be a function symbol".to_string(),
                    )
                })?;

                if arg_ids.is_empty() {
                    return Err(ElaborateError::InvalidConstant(
                        "map requires at least 1 array argument".to_string(),
                    ));
                }

                // Validate: all arguments must be arrays
                let mut index_sort: Option<Sort> = None;
                let mut element_sorts = Vec::with_capacity(arg_ids.len());
                for (i, &arg) in arg_ids.iter().enumerate() {
                    let arg_sort = self.terms.sort(arg).clone();
                    match &arg_sort {
                        Sort::Array(arr) => {
                            // All arrays must have the same index sort
                            if let Some(ref expected_idx) = index_sort {
                                if *expected_idx != arr.index_sort {
                                    return Err(ElaborateError::SortMismatch {
                                        expected: expected_idx.to_string(),
                                        actual: arr.index_sort.to_string(),
                                    });
                                }
                            } else {
                                index_sort = Some(arr.index_sort.clone());
                            }
                            element_sorts.push(arr.element_sort.clone());
                        }
                        _ => {
                            return Err(ElaborateError::InvalidConstant(format!(
                                "map[{func_name}] argument {i} must be an array, got {arg_sort:?}"
                            )));
                        }
                    }
                }

                let idx_sort = index_sort.ok_or_else(|| {
                    ElaborateError::InvalidConstant(
                        "map requires at least one array argument".to_string(),
                    )
                })?;
                if let Some((params, result_sort, body)) = self.fun_defs.get(func_name).cloned() {
                    let index = self.terms.mk_fresh_var("array_map_index", idx_sort.clone());
                    let point_args = arg_ids
                        .iter()
                        .map(|&array| self.terms.mk_select(array, index))
                        .collect::<Vec<_>>();
                    let body = self.elaborate_defined_array_function_body(
                        func_name,
                        &params,
                        &result_sort,
                        &body,
                        point_args,
                    )?;
                    return Ok(self.terms.mk_lambda_array(index, body));
                }

                let func_info = self
                    .resolve_declared_symbol_for_domain(func_name, &element_sorts)?
                    .ok_or_else(|| {
                        ElaborateError::InvalidConstant(format!(
                            "function '{func_name}' has no declaration matching array-map domain ({})",
                            element_sorts
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join(", ")
                        ))
                    })?;

                let result_sort = Sort::array(idx_sort, func_info.sort);
                let internal_name = func_info.internal_name.as_deref().unwrap_or(func_name);

                Ok(self.terms.mk_array_map(internal_name, arg_ids, result_sort))
            }
            // as-array: (_ as-array f)
            // Converts a declared function to an array value.
            // The "index" is the function name (a symbol, not a numeral).
            // select(as-array(f), i) = f(i)
            // Z3 ref: array_decl_plugin.cpp:531 (OP_AS_ARRAY)
            "as-array" => {
                if parsed_indices.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "as-array requires exactly 1 index (the function name)".to_string(),
                    ));
                }
                if !arg_ids.is_empty() {
                    return Err(ElaborateError::InvalidConstant(
                        "as-array takes no arguments".to_string(),
                    ));
                }
                let func_name = parsed_indices[0].as_symbol().ok_or_else(|| {
                    ElaborateError::InvalidConstant(
                        "as-array index must be a function symbol".to_string(),
                    )
                })?;

                if let Some((params, result_sort, body)) = self.fun_defs.get(func_name).cloned() {
                    if params.len() != 1 {
                        return Err(ElaborateError::InvalidConstant(format!(
                            "function '{func_name}' used in (_ as-array {func_name}) requires 1 argument, got {}",
                            params.len()
                        )));
                    }
                    let index = self
                        .terms
                        .mk_fresh_var("as_array_index", params[0].1.clone());
                    let body = self.elaborate_defined_array_function_body(
                        func_name,
                        &params,
                        &result_sort,
                        &body,
                        vec![index],
                    )?;
                    return Ok(self.terms.mk_lambda_array(index, body));
                }

                let func_info = self
                    .resolve_declared_symbol_with_arity(func_name, 1)?
                    .ok_or_else(|| {
                        ElaborateError::UndefinedSymbol(format!(
                            "function '{func_name}' used in (_ as-array {func_name}) has no unary declaration"
                        ))
                    })?;

                let index_sort = func_info.arg_sorts[0].clone();
                let element_sort = func_info.sort;
                let array_sort = Sort::array(index_sort, element_sort);
                let internal_name = func_info.internal_name.as_deref().unwrap_or(func_name);

                Ok(self.terms.mk_as_array(internal_name, array_sort))
            }
            "extract" => {
                if indices.len() != 2 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "extract requires 2 indices and 1 argument".to_string(),
                    ));
                }
                self.checked_bv_extract(indices[0], indices[1], arg_ids[0])
            }
            "int2bv" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "int2bv requires 1 index and 1 argument".to_string(),
                    ));
                }
                Self::checked_bitvector_sort(indices[0])?;
                self.expect_int_operand("int2bv", arg_ids[0])?;
                Ok(self.terms.mk_int2bv(indices[0], arg_ids[0]))
            }
            "zero_extend" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "zero_extend requires 1 index and 1 argument".to_string(),
                    ));
                }
                self.check_bv_extension_width("zero_extend", indices[0], arg_ids[0])?;
                Ok(self.terms.mk_bvzero_extend(indices[0], arg_ids[0]))
            }
            "sign_extend" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "sign_extend requires 1 index and 1 argument".to_string(),
                    ));
                }
                self.check_bv_extension_width("sign_extend", indices[0], arg_ids[0])?;
                Ok(self.terms.mk_bvsign_extend(indices[0], arg_ids[0]))
            }
            "rotate_left" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "rotate_left requires 1 index and 1 argument".to_string(),
                    ));
                }
                self.expect_bv_operand_width("rotate_left", arg_ids[0])?;
                Ok(self.terms.mk_bvrotate_left(indices[0], arg_ids[0]))
            }
            "rotate_right" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "rotate_right requires 1 index and 1 argument".to_string(),
                    ));
                }
                self.expect_bv_operand_width("rotate_right", arg_ids[0])?;
                Ok(self.terms.mk_bvrotate_right(indices[0], arg_ids[0]))
            }
            "repeat" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "repeat requires 1 index and 1 argument".to_string(),
                    ));
                }
                self.check_bv_repeat_width(indices[0], arg_ids[0])?;
                Ok(self.terms.mk_bvrepeat(indices[0], arg_ids[0]))
            }
            "re.loop" => {
                if indices.len() != 2 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "re.loop requires 2 indices and 1 argument".to_string(),
                    ));
                }
                self.expect_arg_sort(arg_ids[0], &Sort::RegLan)?;
                if indices[0] > indices[1] {
                    // SMT-LIB 2.6: `((_ re.loop i n) e)` denotes
                    // `⋃_{k=i}^{n} L(e)^k`. When `i > n` the index set is
                    // EMPTY, so the term denotes the empty language — it is a
                    // perfectly well-formed term, NOT an invalid constant.
                    // Rejecting it made AY refuse a conformant input (it is
                    // fail-closed, so never a wrong answer, but it is a
                    // capability gap: the formula is decidable and AY declined
                    // to decide it). Fold to `re.none`, which every downstream
                    // consumer already handles — and which is exactly what
                    // `WeRegex::loop_bounded` / `evaluate` / `accepted_lengths`
                    // already computed for this shape
                    // (#regex-loop-degenerate-bounds).
                    return Ok(self
                        .terms
                        .mk_app(Symbol::named("re.none"), vec![], Sort::RegLan));
                }
                Ok(self.terms.mk_app(
                    Symbol::indexed("re.loop", indices),
                    vec![arg_ids[0]],
                    Sort::RegLan,
                ))
            }
            "re.^" => {
                if indices.len() != 1 || arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "re.^ requires 1 index and 1 argument".to_string(),
                    ));
                }
                self.expect_arg_sort(arg_ids[0], &Sort::RegLan)?;
                let n = indices[0];
                Ok(self.terms.mk_app(
                    Symbol::indexed("re.loop", vec![n, n]),
                    vec![arg_ids[0]],
                    Sort::RegLan,
                ))
            }
            "to_fp" => {
                let fp_sort = self.validate_indexed_fp_application("to_fp", &indices, &arg_ids)?;
                Ok(self
                    .terms
                    .mk_app(Symbol::indexed("to_fp", indices), arg_ids, fp_sort))
            }
            "to_fp_unsigned" => {
                let fp_sort =
                    self.validate_indexed_fp_application("to_fp_unsigned", &indices, &arg_ids)?;
                Ok(self
                    .terms
                    .mk_app(Symbol::indexed("to_fp_unsigned", indices), arg_ids, fp_sort))
            }
            "fp.to_ubv" | "fp.to_sbv" => {
                let bv_sort = self.validate_indexed_fp_application(name, &indices, &arg_ids)?;
                Ok(self
                    .terms
                    .mk_app(Symbol::indexed(name, indices), arg_ids, bv_sort))
            }
            // SMT-LIB Int theory divisibility predicate: `((_ divisible n) t)`
            // holds iff n divides t. Desugar to the existing, tested arithmetic
            // primitives rather than introduce a new term kind: for a positive
            // numeral n this is `(= (mod t n) 0)` (SMT-LIB `mod` is the
            // non-negative Euclidean remainder, so `mod t n = 0` iff n | t); the
            // degenerate `(_ divisible 0)` means `t = 0`. Re-elaborating the
            // constructed parse tree reuses the audited `mod`/`=` elaboration and
            // keeps this purely definitional (no soundness surface of its own).
            "divisible" => {
                if parsed_indices.len() != 1 || indices.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "divisible requires exactly 1 numeral index (the divisor)".to_string(),
                    ));
                }
                if args.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "divisible expects exactly 1 argument".to_string(),
                    ));
                }
                // Z3 5.0.0 does not apply its general Bool-to-Int arithmetic
                // coercion at the indexed `divisible` boundary. Validate the
                // declared Int rank before desugaring; otherwise the `mod`
                // coercion below would incorrectly accept a Bool operand.
                self.expect_arg_sort(arg_ids[0], &Sort::Int)?;
                use crate::command::{Constant as PConst, Term as PTerm};
                let zero = PTerm::Const(PConst::Numeral("0".to_string()));
                let desugared = if indices[0] == 0 {
                    // (_ divisible 0) t  ===  (= t 0)
                    PTerm::App("=".to_string(), vec![args[0].clone(), zero])
                } else {
                    // (_ divisible n) t  ===  (= (mod t n) 0)
                    let n = PTerm::Const(PConst::Numeral(parsed_indices[0].text().to_string()));
                    let modt = PTerm::App("mod".to_string(), vec![args[0].clone(), n]);
                    PTerm::App("=".to_string(), vec![modt, zero])
                };
                self.elaborate_term(&desugared, env)
            }
            // SMT-LIB / Z3 cardinality operators over Bool literals.
            //   ((_ at-most k)  x_1 ... x_n)  ===  (<= (x_1 + ... + x_n) k)
            //   ((_ at-least k) x_1 ... x_n)  ===  (>= (x_1 + ... + x_n) k)
            // where each x_i contributes 1 to the sum when true, 0 when false.
            // Desugared to the exact integer-arithmetic semantics and decided by
            // the audited LIA path (equisatisfiable, purely definitional).
            // Z3 ref: pb_decl_plugin.cpp (OP_AT_MOST_K / OP_AT_LEAST_K).
            "at-most" | "at-least" => {
                if arg_ids.is_empty() {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires at least 1 argument"
                    )));
                }
                if parsed_indices.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires exactly 1 index (the bound k)"
                    )));
                }
                let k = parse_cardinality_index(&parsed_indices[0], name)?;
                let coeffs = vec![BigInt::from(1); arg_ids.len()];
                let cmp = if name == "at-most" {
                    PbCmp::Le
                } else {
                    PbCmp::Ge
                };
                self.build_pb_constraint(&coeffs, k, &arg_ids, cmp)
            }
            // SMT-LIB / Z3 pseudo-boolean operators with explicit coefficients.
            //   ((_ pble k c_1 ... c_n) x_1 ... x_n)  ===  (<= (Σ c_i·x_i) k)
            //   ((_ pbge k c_1 ... c_n) x_1 ... x_n)  ===  (>= (Σ c_i·x_i) k)
            //   ((_ pbeq k c_1 ... c_n) x_1 ... x_n)  ===  (=  (Σ c_i·x_i) k)
            // The FIRST index is the threshold k; the remaining n indices are the
            // per-literal coefficients (one per Bool argument). Z3 ref:
            // pb_decl_plugin.cpp (OP_PB_LE / OP_PB_GE / OP_PB_EQ).
            "pble" | "pbge" | "pbeq" => {
                if arg_ids.is_empty() {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires at least 1 argument"
                    )));
                }
                // One threshold index + one coefficient per Bool argument.
                if parsed_indices.len() != arg_ids.len() + 1 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires {} indices (threshold k followed by one \
                        coefficient per argument), got {}",
                        arg_ids.len() + 1,
                        parsed_indices.len()
                    )));
                }
                let parsed_rationals = parsed_indices
                    .iter()
                    .map(|index| parse_pb_rational_index(index, name))
                    .collect::<Result<Vec<_>>>()?;
                let (coeffs, k) =
                    integerize_pb_parameters(&parsed_rationals[1..], &parsed_rationals[0]);
                let cmp = match name {
                    "pble" => PbCmp::Le,
                    "pbge" => PbCmp::Ge,
                    _ => PbCmp::Eq,
                };
                self.build_pb_constraint(&coeffs, k, &arg_ids, cmp)
            }
            // Z3 special-relations indexed identifiers (special_relations plugin):
            //   ((_ partial-order N) a b)           reflexive+antisym+transitive
            //   ((_ linear-order N) a b)            partial + total
            //   ((_ tree-order N) a b)              partial + left-linear
            //   ((_ piecewise-linear-order N) a b)  partial + left- + right-linear
            // Each (kind, index, argument-sort) denotes a DISTINCT uninterpreted
            // binary relation constrained by the order axioms for its kind. This is
            // exactly the encoding Verus's prelude emits for its well-founded height
            // ordering (`height_le = (_ partial-order 0)`), so it sits on the hot
            // path of EVERY Verus decreases/termination proof. The realized
            // semantics mirror ay's own libz3-4.16.0-verified FFI constructors
            // (`Z3_mk_partial_order` &c., `build_order_axioms` in ay-ffi).
            "partial-order" | "linear-order" | "tree-order" | "piecewise-linear-order" => {
                self.elaborate_special_order(name, parsed_indices, &arg_ids)
            }
            _ => {
                // There is no sound generic declaration model for an indexed
                // identifier here. The legacy fallback looked up the string
                // spelling only for a result sort, silently dropped nonnumeric
                // indices, ignored arity/domain/internal identity, and then
                // built a different `Symbol::Indexed`. A quoted symbol whose
                // text resembles `(_ f i)` is not that indexed identifier.
                Err(ElaborateError::Unsupported(format!(
                    "unknown indexed identifier: {name}"
                )))
            }
        }
    }

    /// Expand a `define-fun` body used by `(_ map f)` or `(_ as-array f)`.
    ///
    /// The environment contains only the definition's parameters, never the
    /// indexed identifier's use-site binders. This is the same capture-avoiding
    /// rule as ordinary macro application in `elaborate_app`. The shared depth
    /// counter also makes recursive definitions fail closed at the established
    /// expansion limit instead of recursing without bound.
    fn elaborate_defined_array_function_body(
        &mut self,
        name: &str,
        params: &[(String, Sort)],
        result_sort: &Sort,
        body: &ParsedTerm,
        mut args: Vec<TermId>,
    ) -> Result<TermId> {
        if self.fun_expansion_depth >= MAX_FUN_EXPANSION_DEPTH {
            return Err(ElaborateError::RecursionDepthExceeded(
                MAX_FUN_EXPANSION_DEPTH,
            ));
        }
        self.fun_expansion_depth += 1;
        let result = (|| {
            let expected_sorts = params
                .iter()
                .map(|(_, sort)| sort.clone())
                .collect::<Vec<_>>();
            self.validate_application_signature(name, &expected_sorts, &mut args)?;

            let mut definition_env = HashMap::default();
            for ((parameter, _), argument) in params.iter().zip(args) {
                definition_env.insert(parameter.clone(), argument);
            }
            let body = self.elaborate_term(body, &definition_env)?;
            let actual = self.terms.sort(body).clone();
            if &actual == result_sort {
                Ok(body)
            } else if self.int_real_coercions() && actual == Sort::Int && result_sort == &Sort::Real
            {
                Ok(self.coerce_int_to_real(body))
            } else {
                Err(ElaborateError::SortMismatch {
                    expected: result_sort.to_string(),
                    actual: actual.to_string(),
                })
            }
        })();
        self.fun_expansion_depth -= 1;
        result
    }

    /// Resolve a Z3 special-relation application `((_ kind id) a b)` to an
    /// application of the fresh uninterpreted predicate that realizes it.
    ///
    /// `kind` is one of the special-relations names dispatched at the call site.
    /// The two arguments must share a sort; the relation is that sort's binary
    /// predicate. Declares the predicate and injects its order axioms on first
    /// use (see [`Context::special_order_predicate`]).
    fn elaborate_special_order(
        &mut self,
        kind: &str,
        parsed_indices: &[ParsedIndex],
        arg_ids: &[TermId],
    ) -> Result<TermId> {
        if parsed_indices.len() != 1 {
            return Err(ElaborateError::InvalidConstant(format!(
                "(_ {kind} ..) requires exactly 1 index (the relation id), got {}",
                parsed_indices.len()
            )));
        }
        let relation_id = parsed_indices[0].as_numeral().ok_or_else(|| {
            ElaborateError::InvalidConstant(format!(
                "(_ {kind} ..) relation id must be a numeral token"
            ))
        })?;
        if arg_ids.len() != 2 {
            return Err(ElaborateError::InvalidConstant(format!(
                "(_ {kind} {}) is a binary relation and requires exactly 2 arguments, got {}",
                relation_id,
                arg_ids.len()
            )));
        }
        let sort = self.terms.sort(arg_ids[0]).clone();
        let sort_rhs = self.terms.sort(arg_ids[1]).clone();
        if sort != sort_rhs {
            return Err(ElaborateError::InvalidConstant(format!(
                "(_ {kind} {relation_id}) arguments must share a sort, got {sort} and {sort_rhs}"
            )));
        }
        let pred = self.special_order_predicate(kind, &sort, relation_id)?;
        Ok(self
            .terms
            .mk_app(Symbol::named(&pred), [arg_ids[0], arg_ids[1]], Sort::Bool))
    }

    /// Return (declaring on first use) the uninterpreted predicate realizing the
    /// `(kind, sort, id)` special relation, injecting its order axioms exactly
    /// once. Reuses the memoized predicate only while its symbol is still in
    /// scope — a `pop` that removed it forces a sound re-declaration.
    fn special_order_predicate(&mut self, kind: &str, sort: &Sort, id: &str) -> Result<String> {
        let key = (kind.to_string(), sort.to_string(), id.to_string());
        if let Some(existing) = self.special_relations.get(&key).cloned() {
            if self.symbols.contains_key(&existing) {
                return Ok(existing);
            }
        }
        let surface = surface_sort(sort).ok_or_else(|| {
            ElaborateError::Unsupported(format!(
                "special relation (_ {kind} {id}) over sort {sort} is not supported"
            ))
        })?;
        // Fresh, collision-proof predicate name. The app path resolves an internal
        // `__ay_`-prefixed symbol by table lookup; only *declaring* such a name
        // from user input is rejected, so using one here is safe.
        let pred = self.terms.mk_internal_symbol("order");
        self.track_scoped_symbol(&pred);
        self.symbols.insert(
            pred.clone(),
            SymbolInfo {
                term: None,
                sort: Sort::Bool,
                arg_sorts: vec![sort.clone(), sort.clone()],
                public_sort: super::PublicSort::Core(Sort::Bool),
                public_arg_sorts: vec![
                    super::PublicSort::from_engine(&sort),
                    super::PublicSort::from_engine(&sort),
                ],
                internal_name: None,
            },
        );
        // Assert the property axioms through the surface path so `assertions` and
        // `assertions_parsed` stay aligned and the axioms are push/pop-scoped
        // exactly like the predicate symbol.
        for axiom in order_axioms(&pred, &surface, kind) {
            self.assert(&axiom)?;
        }
        self.special_relations.insert(key, pred.clone());
        Ok(pred)
    }

    /// Build the integer-arithmetic term for a pseudo-boolean / cardinality
    /// constraint `(cmp (Σ coeff_i · [arg_i]) k)`, where `[arg_i]` is the 0/1
    /// indicator of the Bool literal `arg_i`.
    ///
    /// Each summand is `(ite arg_i coeff_i 0)`, so the whole constraint is the
    /// literal SMT-LIB semantics of Z3's PB operators and is decided by the LIA
    /// solver — no new soundness surface. Requires every argument to be Bool.
    fn build_pb_constraint(
        &mut self,
        coeffs: &[BigInt],
        k: BigInt,
        arg_ids: &[TermId],
        cmp: PbCmp,
    ) -> Result<TermId> {
        debug_assert_eq!(coeffs.len(), arg_ids.len());
        let zero = self.terms.mk_int(BigInt::from(0));
        let mut summands = Vec::with_capacity(arg_ids.len());
        for (&arg, coeff) in arg_ids.iter().zip(coeffs) {
            // PB / cardinality literals must be Bool (matches Z3, which rejects
            // non-Bool arguments to these operators).
            if self.terms.sort(arg) != &Sort::Bool {
                return Err(ElaborateError::SortMismatch {
                    expected: "Bool".to_string(),
                    actual: self.terms.sort(arg).to_string(),
                });
            }
            let coeff_term = self.terms.mk_int(coeff.clone());
            // (ite arg coeff 0): contributes `coeff` when the literal holds.
            summands.push(self.terms.mk_ite(arg, coeff_term, zero));
        }
        let sum = self.terms.mk_add(summands);
        let bound = self.terms.mk_int(k);
        Ok(match cmp {
            PbCmp::Le => self.terms.mk_le(sum, bound),
            PbCmp::Ge => self.terms.mk_ge(sum, bound),
            PbCmp::Eq => self.terms.mk_eq(sum, bound),
        })
    }
}

/// Parse the sole `at-most` / `at-least` parameter exactly as Z3 5.0.0 does.
/// Its declaration plugin requires a non-negative machine `int`; decimals,
/// negative values, and values above `INT_MAX` are rejected.
fn parse_cardinality_index(index: &ParsedIndex, op: &str) -> Result<BigInt> {
    let value = parse_unsigned_index_value(index).ok_or_else(|| {
        ElaborateError::InvalidConstant(format!(
            "{op}: expected one non-negative integer parameter, got '{}'",
            index.text()
        ))
    })?;
    if value > BigInt::from(i32::MAX) {
        return Err(ElaborateError::InvalidConstant(format!(
            "{op}: parameter '{}' does not fit Z3's non-negative machine int",
            index.text()
        )));
    }
    Ok(value)
}

/// Parse one `pble` / `pbge` / `pbeq` parameter as the rational value produced
/// by Z3 5.0.0's SMT2 indexed-identifier parser. Unsigned numeral/bitvector
/// indices that fit `unsigned` are first stored in a signed `int` parameter,
/// including the 2^31..2^32-1 wraparound of that exact release. Larger values,
/// decimals, and negative numeric tokens remain exact rationals.
fn parse_pb_rational_index(index: &ParsedIndex, op: &str) -> Result<BigRational> {
    if let Some(value) = parse_unsigned_index_value(index) {
        if value <= BigInt::from(u32::MAX) {
            let unsigned = value.to_u32_digits().1.first().copied().unwrap_or(0);
            return Ok(BigRational::from_integer(BigInt::from(unsigned as i32)));
        }
        return Ok(BigRational::from_integer(value));
    }

    let text = match index {
        ParsedIndex::Decimal(text) => text.as_str(),
        ParsedIndex::Symbol(text) if is_negative_decimal_text(text) => text.as_str(),
        _ => {
            return Err(ElaborateError::InvalidConstant(format!(
                "{op}: expected a rational parameter, got '{}'",
                index.text()
            )));
        }
    };
    parse_decimal_rational(text).ok_or_else(|| {
        ElaborateError::InvalidConstant(format!("{op}: invalid rational parameter '{text}'"))
    })
}

fn parse_unsigned_index_value(index: &ParsedIndex) -> Option<BigInt> {
    match index {
        ParsedIndex::Numeral(text) => text.parse().ok(),
        ParsedIndex::Hexadecimal(text) => {
            BigInt::parse_bytes(text.strip_prefix("#x")?.as_bytes(), 16)
        }
        ParsedIndex::Binary(text) => BigInt::parse_bytes(text.strip_prefix("#b")?.as_bytes(), 2),
        _ => None,
    }
}

fn is_negative_decimal_text(text: &str) -> bool {
    let Some(magnitude) = text.strip_prefix('-') else {
        return false;
    };
    let mut parts = magnitude.split('.');
    let Some(integer) = parts.next() else {
        return false;
    };
    let fraction = parts.next();
    parts.next().is_none()
        && !integer.is_empty()
        && integer.bytes().all(|byte| byte.is_ascii_digit())
        && fraction.is_none_or(|digits| {
            !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
        })
}

fn parse_decimal_rational(text: &str) -> Option<BigRational> {
    let (negative, magnitude) = text
        .strip_prefix('-')
        .map_or((false, text), |magnitude| (true, magnitude));
    let (integer, fraction) = magnitude.split_once('.').unwrap_or((magnitude, ""));
    let integer = integer.parse::<BigInt>().ok()?;
    let denominator = BigInt::from(10).pow(u32::try_from(fraction.len()).ok()?);
    let fraction = if fraction.is_empty() {
        BigInt::from(0)
    } else {
        fraction.parse::<BigInt>().ok()?
    };
    let numerator = integer * &denominator + fraction;
    Some(BigRational::new(
        if negative { -numerator } else { numerator },
        denominator,
    ))
}

/// Multiply a PB inequality/equality by a positive common denominator so the
/// existing exact integer-arithmetic lowering can decide rational parameters.
fn integerize_pb_parameters(
    coefficients: &[BigRational],
    bound: &BigRational,
) -> (Vec<BigInt>, BigInt) {
    let scale = coefficients
        .iter()
        .chain(std::iter::once(bound))
        .fold(BigInt::from(1), |product, value| product * value.denom());
    let scaled = |value: &BigRational| value.numer() * (&scale / value.denom());
    (coefficients.iter().map(scaled).collect(), scaled(bound))
}

/// Map an elaborated argument sort back to the surface sort that round-trips
/// through `elaborate_sort`, for the sorts a special relation can range over.
///
/// Returns `None` (fail-closed) for sorts without a faithful one-liner surface
/// form here — the caller then rejects the special relation as unsupported
/// rather than mis-encoding it. Covers the scalar sorts plus the declared
/// uninterpreted/datatype sorts that name themselves (Verus's `Height` is a
/// declared sort, so it lands in the `Uninterpreted`/`Datatype` arm).
fn surface_sort(sort: &Sort) -> Option<CmdSort> {
    Some(match sort {
        Sort::Bool => CmdSort::Simple("Bool".to_string()),
        Sort::Int => CmdSort::Simple("Int".to_string()),
        Sort::Real => CmdSort::Simple("Real".to_string()),
        Sort::String => CmdSort::Simple("String".to_string()),
        Sort::Uninterpreted(name) => CmdSort::Simple(name.clone()),
        Sort::Datatype(dt) => CmdSort::Simple(dt.name.clone()),
        _ => return None,
    })
}

/// The property axioms for special relation `kind` over predicate `pred`
/// (`sort*sort -> Bool`), as surface terms bound over `sort`. Mirrors ay-ffi's
/// libz3-4.16.0-verified `build_order_axioms`:
///
///   partial   = reflexive + antisymmetric + transitive
///   linear    = partial + total
///   tree      = partial + left-linear (down-set of every node linearly ordered)
///   piecewise = partial + left-linear + right-linear (up-set too)
///
/// Bound-variable names `x`,`y`,`z` are resolved against the quantifier scope by
/// the elaborator, never against user symbols.
fn order_axioms(pred: &str, sort: &CmdSort, kind: &str) -> Vec<ParsedTerm> {
    let sym = |v: &str| ParsedTerm::Symbol(v.to_string());
    let r = |a: &str, b: &str| ParsedTerm::App(pred.to_string(), vec![sym(a), sym(b)]);
    let and = |a, b| ParsedTerm::App("and".to_string(), vec![a, b]);
    let or = |a, b| ParsedTerm::App("or".to_string(), vec![a, b]);
    let implies = |a, b| ParsedTerm::App("=>".to_string(), vec![a, b]);
    let eq = |a: &str, b: &str| ParsedTerm::App("=".to_string(), vec![sym(a), sym(b)]);
    let forall = |vars: &[&str], body| {
        let binders = vars.iter().map(|v| (v.to_string(), sort.clone())).collect();
        ParsedTerm::Forall(binders, Box::new(body))
    };

    // partial order: reflexive + antisymmetric + transitive (all kinds include).
    let mut axioms = vec![
        forall(&["x"], r("x", "x")),
        forall(
            &["x", "y"],
            implies(and(r("x", "y"), r("y", "x")), eq("x", "y")),
        ),
        forall(
            &["x", "y", "z"],
            implies(and(r("x", "y"), r("y", "z")), r("x", "z")),
        ),
    ];
    // linear: + totality.
    if kind == "linear-order" {
        axioms.push(forall(&["x", "y"], or(r("x", "y"), r("y", "x"))));
    }
    // tree / piecewise: + left-linearity (the down-set of any node is a chain).
    if kind == "tree-order" || kind == "piecewise-linear-order" {
        axioms.push(forall(
            &["x", "y", "z"],
            implies(and(r("y", "x"), r("z", "x")), or(r("y", "z"), r("z", "y"))),
        ));
    }
    // piecewise: + right-linearity (the up-set of any node is a chain).
    if kind == "piecewise-linear-order" {
        axioms.push(forall(
            &["x", "y", "z"],
            implies(and(r("x", "y"), r("x", "z")), or(r("y", "z"), r("z", "y"))),
        ));
    }
    axioms
}
