// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compound-expression structure parsing.
//!
//! Handles expression shapes (compound, indexed, as, let, quantifier) and
//! leaf atom parsing (numerals, symbols). Delegates operator interpretation
//! to `application.rs` and BV literals to `bitvector.rs`.

use super::ChcParser;
use crate::expr::maybe_grow_expr_stack;
use crate::{ChcError, ChcExpr, ChcResult, ChcSort, ChcVar};
use num_bigint::BigInt;
use std::sync::Arc;

impl ChcParser {
    /// Parse an expression
    pub(super) fn parse_expr(&mut self) -> ChcResult<ChcExpr> {
        // Stacker protection: CHC formulas with many predicates and args can
        // produce deeply nested S-expressions after preprocessing (#6847).
        maybe_grow_expr_stack(|| {
            self.skip_whitespace_and_comments();

            match self.peek_char() {
                Some('(') => self.parse_compound_expr(),
                Some('#') => self.parse_bv_literal(),
                Some(c) if c.is_ascii_digit() || c == '-' => self.parse_numeral_expr(),
                Some(_) => self.parse_symbol_expr(),
                None => Err(ChcError::Parse("Unexpected end of input".into())),
            }
        })
    }

    /// Parse a compound expression (function application)
    fn parse_compound_expr(&mut self) -> ChcResult<ChcExpr> {
        self.expect_char('(')?;
        self.skip_whitespace_and_comments();

        // Check for special forms: indexed identifier `(_ <name> <indices>...)`.
        // SMT-LIB `_` is only an indexed identifier marker when followed by whitespace.
        // Symbols starting with `_` (e.g., `__VERIFIER_nondet_int`) are regular function names.
        if self.peek_char() == Some('_') {
            let next = self.input[self.pos..].chars().nth(1);
            if next.map_or(true, char::is_whitespace) {
                return self.parse_indexed_expr();
            }
        }

        // Check for nested compound expression (e.g., ((as const ...) value))
        if self.peek_char() == Some('(') {
            return self.parse_higher_order_application();
        }

        // Check for let
        let first = self.parse_symbol()?;
        self.skip_whitespace_and_comments();

        match first.as_str() {
            "let" => self.parse_let_expr(),
            "forall" | "exists" => self.parse_quantifier_expr(&first),
            "as" => self.parse_as_expr(),
            _ => self.parse_application(&first),
        }
    }

    /// Parse higher-order application like ((as const (Array Int Int)) value)
    fn parse_higher_order_application(&mut self) -> ChcResult<ChcExpr> {
        // Parse the "function" which is itself a compound expression
        let func_expr = self.parse_compound_expr()?;
        self.skip_whitespace_and_comments();

        // Parse arguments
        let mut args = Vec::new();
        while self.peek_char() != Some(')') {
            args.push(self.parse_expr()?);
            self.skip_whitespace_and_comments();
        }
        self.expect_char(')')?;

        // Handle (as const ...) applied to a value
        if let ChcExpr::ConstArrayMarker(key_sort) = &func_expr {
            if args.len() != 1 {
                return Err(ChcError::Parse(
                    "(as const ...) requires exactly 1 argument".into(),
                ));
            }
            let mut iter = args.into_iter();
            let value = Self::next_checked(&mut iter, "as const")?;
            return Ok(ChcExpr::const_array(key_sort.clone(), value));
        }

        // Handle indexed BV ops and (_ is Ctor) testers.
        match func_expr {
            ChcExpr::Op(op, ref existing_args) if existing_args.is_empty() => {
                let args_arc: Vec<Arc<ChcExpr>> = args.into_iter().map(Arc::new).collect();
                Ok(ChcExpr::Op(op, args_arc))
            }
            ChcExpr::IsTesterMarker(ref ctor_name) => {
                if args.len() != 1 {
                    return Err(ChcError::Parse(
                        "(_ is ...) requires exactly 1 argument".into(),
                    ));
                }
                let ctor = ctor_name.clone();
                let arg_arc = Arc::new(
                    args.into_iter()
                        .next()
                        .expect("invariant: length checked above"),
                );
                Ok(ChcExpr::FuncApp(
                    format!("is-{ctor}"),
                    ChcSort::Bool,
                    vec![arg_arc],
                ))
            }
            // ((as Constructor Sort) arg1 arg2 ...) — qualified constructor application (#3362)
            ChcExpr::FuncApp(ref name, ref sort, ref existing_args) if existing_args.is_empty() => {
                let args_arc: Vec<Arc<ChcExpr>> = args.into_iter().map(Arc::new).collect();
                Ok(ChcExpr::FuncApp(name.clone(), sort.clone(), args_arc))
            }
            _ => Err(ChcError::Parse(
                "Unsupported higher-order application".into(),
            )),
        }
    }

    /// Parse (as const ...) expression for SMT-LIB2 array constants
    /// Syntax: (as const (Array IndexSort ElemSort))
    /// Returns a marker that will be applied to a value to create a constant array
    fn parse_as_expr(&mut self) -> ChcResult<ChcExpr> {
        self.skip_whitespace_and_comments();
        let name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();

        match name.as_str() {
            "const" => {
                // Parse the array sort: (Array IndexSort ElemSort)
                self.expect_char('(')?;
                self.skip_whitespace_and_comments();
                let array_kw = self.parse_symbol()?;
                if array_kw != "Array" {
                    return Err(ChcError::Parse(format!(
                        "Expected 'Array' in (as const ...), got: {array_kw}"
                    )));
                }
                self.skip_whitespace_and_comments();
                let index_sort = self.parse_sort()?;
                self.skip_whitespace_and_comments();
                let _elem_sort = self.parse_sort()?;
                self.skip_whitespace_and_comments();
                self.expect_char(')')?;
                self.skip_whitespace_and_comments();
                self.expect_char(')')?;

                // Now we need to parse the value that follows in the outer application
                // The syntax is: ((as const (Array Int Int)) value)
                // At this point we've parsed "(as const (Array Int Int))"
                // The caller should handle applying this to the value
                // Return a special marker that const_array will be created when applied
                Ok(ChcExpr::ConstArrayMarker(index_sort))
            }
            _ => {
                // (as <constructor> <sort>) — qualified datatype constructor (#3362)
                // Parse the sort, then create a FuncApp with Uninterpreted return sort.
                let sort = self.parse_sort()?;
                self.skip_whitespace_and_comments();
                self.expect_char(')')?;
                Ok(ChcExpr::FuncApp(name, sort, Vec::new()))
            }
        }
    }

    /// Parse let expression
    fn parse_let_expr(&mut self) -> ChcResult<ChcExpr> {
        self.skip_whitespace_and_comments();
        self.expect_char('(')?;

        // Parse bindings
        let mut bindings = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            self.expect_char('(')?;
            self.skip_whitespace_and_comments();
            let var_name = self.parse_symbol()?;
            self.skip_whitespace_and_comments();
            let value = self.parse_expr()?;
            self.skip_whitespace_and_comments();
            self.expect_char(')')?;
            bindings.push((var_name, value));
        }
        self.expect_char(')')?;

        // Add let-bound variables to the variable map before parsing body
        // This ensures that references to these variables get the correct sort
        let mut old_values = Vec::new();
        for (name, value) in &bindings {
            let sort = value.sort();
            let old = self.variables.insert(name.clone(), sort);
            old_values.push((name.clone(), old));
        }

        self.skip_whitespace_and_comments();
        let body = self.parse_expr()?;
        self.skip_whitespace_and_comments();
        self.expect_char(')')?;

        // Restore original variable bindings
        for (name, old) in old_values {
            match old {
                Some(sort) => {
                    self.variables.insert(name, sort);
                }
                None => {
                    self.variables.remove(&name);
                }
            }
        }

        // Substitute bindings in body, PRESERVING structural sharing (#9074):
        // each bound value is inserted as a shared Arc, so nested `let`s expand
        // into a linear DAG instead of an exponential tree of distinct Arcs
        // (which blows up parse-time simplify_constants and every later tree
        // walk on heavily let-nested inputs, e.g. sally/oral_messages).
        let bound: Vec<(ChcVar, Arc<ChcExpr>)> = bindings
            .into_iter()
            .map(|(name, value)| {
                let sort = value.sort();
                (ChcVar::new(name, sort), Arc::new(value))
            })
            .collect();
        let map: ay_core::kani_compat::DetHashMap<&ChcVar, Arc<ChcExpr>> =
            bound.iter().map(|(v, e)| (v, Arc::clone(e))).collect();
        let result = ChcExpr::substitute_let_shared(&Arc::new(body), &map);
        Ok(Arc::try_unwrap(result).unwrap_or_else(|arc| (*arc).clone()))
    }

    /// Parse quantifier expression (forall/exists)
    fn parse_quantifier_expr(&mut self, quantifier: &str) -> ChcResult<ChcExpr> {
        self.skip_whitespace_and_comments();
        self.expect_char('(')?;

        // Parse variable declarations and register them
        //
        // CAPTURE: stripping hoists each binder into the FLAT clause scope, so
        // two binders in one clause sharing a name become ONE clause variable
        // and two independent quantifications collapse into one. That is a
        // wrong-answer bug, not a cosmetic one -- it weakens or strengthens the
        // clause depending on polarity, and AY's verdict then depends on the
        // NAME of a bound variable:
        //
        //   (=> (and (exists ((y Int)) (P y)) (exists ((y Int)) (R y))) false)  -> sat   WRONG
        //   (=> (and (exists ((y Int)) (P y)) (exists ((z Int)) (R z))) false)  -> unsat correct
        //
        // (the development design notes, z3-cross-checked
        // in both directions.)
        //
        // Rename ONLY on a binder-vs-binder collision inside the SAME clause.
        // A binder shadowing a file-scoped `declare-var` is the ordinary
        // `(declare-var x Int)` + `(forall ((x Int)) ...)` idiom: there is only
        // one binding of `x` in the clause, so nothing is captured and the name
        // must be left alone. An earlier attempt renamed on ANY shadow and cost
        // five regressions in name-dependent machinery (BMC witness replay,
        // formula-form round trips) plus a 1.8x suite slowdown.
        let renames_before = self.active_renames.len();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            self.expect_char('(')?;
            self.skip_whitespace_and_comments();
            let var_name = self.parse_symbol()?;
            self.skip_whitespace_and_comments();
            let sort = self.parse_sort()?;
            self.skip_whitespace_and_comments();
            self.expect_char(')')?;

            // Register variable in scope (CHC treats quantifiers as implicit)
            if self.clause_binder_names.contains(&var_name)
                || self.declared_var_names.contains(&var_name)
            {
                let fresh = self.fresh_binder_name(&var_name);
                self.variables.insert(fresh.clone(), sort);
                self.clause_binder_names.insert(fresh.clone());
                self.active_renames.push((var_name, fresh));
            } else {
                self.clause_binder_names.insert(var_name.clone());
                self.variables.insert(var_name, sort);
            }
        }
        self.expect_char(')')?;

        self.skip_whitespace_and_comments();
        let body = self.parse_expr()?;
        // This binder group's renames end with its body. Renaming during the
        // parse rather than substituting afterwards means no extra walk over
        // the body and no fail-closed post-check.
        self.active_renames.truncate(renames_before);
        self.skip_whitespace_and_comments();
        self.expect_char(')')?;

        // Stripping the binder hoists its variable into the FLAT clause scope,
        // where it becomes universally quantified over the whole clause. That
        // is equivalence-preserving in only two of the four cases:
        //
        //   forall @ positive  -- the implicit-universal wrapper. Sound.
        //   exists @ negative  -- `(exists x. B(x)) -> H` == `forall x. B(x) -> H`. Sound.
        //   forall @ negative  -- `forall i. (B(i) -> H)` becomes `(exists i. B(i)) -> H`:
        //                         the antecedent is WEAKENED. Sound for proofs
        //                         (an unsat stays valid a fortiori) but it can
        //                         FABRICATE a counterexample, so flag it and let
        //                         the caller downgrade Sat/Unsafe to Unknown.
        //   exists @ positive  -- `B -> exists x. H(x)` becomes `forall x. B -> H(x)`:
        //                         STRICTLY STRONGER, so facts the input never
        //                         entailed become derivable. That is a false-proof
        //                         route, and no downgrade can repair it -> reject.
        //
        // Mixed polarity (0: `ite` conditions, Bool `=`/`distinct`/`xor`) is not
        // safely strippable either way; `forall` there is treated as the
        // over-approximating case, `exists` is rejected.
        match (quantifier, self.polarity) {
            ("forall", p) if p > 0 => {}
            ("exists", p) if p < 0 => {}
            ("forall", _) => self.problem.mark_stripped_body_forall(),
            _ => {
                return Err(ChcError::Parse(format!(
                    "unsupported CHC input: `{quantifier}` in a non-negative                      (head/mixed) position would be STRENGTHENED to `forall` by                      implicit-universal stripping, which can derive facts the                      input does not entail; hoist it out or Skolemise it before                      HORN solving"
                )));
            }
        }

        // The variables are already registered.
        Ok(body)
    }

    /// Parse a numeral expression
    pub(super) fn parse_numeral_expr(&mut self) -> ChcResult<ChcExpr> {
        let num_str = self.parse_numeric_literal()?;
        if num_str.contains('.') {
            return Self::parse_decimal_real(&num_str);
        }
        // Try i64 first (common case, zero allocation)
        if let Ok(n) = num_str.parse::<i64>() {
            return Ok(ChcExpr::int(n));
        }
        // Fall back to BigInt for large numbers (e.g., 256-bit EVM constants)
        // and encode as a small decimal-chunk arithmetic tree (#381, #7040).
        let n: BigInt = num_str
            .parse()
            .map_err(|_| ChcError::Parse(format!("Invalid numeral: {num_str}")))?;
        Ok(Self::encode_large_int(n))
    }

    pub(super) fn normalize_rational_i128(numer: i128, denom: i128) -> ChcResult<ChcExpr> {
        if denom == 0 {
            return Err(ChcError::Parse("Real numeral has zero denominator".into()));
        }
        let mut numer = numer;
        let mut denom = denom;
        if denom < 0 {
            numer = numer
                .checked_neg()
                .ok_or_else(|| ChcError::Parse("Real numeral numerator overflow".into()))?;
            denom = denom
                .checked_neg()
                .ok_or_else(|| ChcError::Parse("Real numeral denominator overflow".into()))?;
        }
        let gcd = gcd_i128(numer, denom);
        let numer = numer / gcd;
        let denom = denom / gcd;
        let numer = i64::try_from(numer)
            .map_err(|_| ChcError::Parse("Real numerator does not fit in i64".into()))?;
        let denom = i64::try_from(denom)
            .map_err(|_| ChcError::Parse("Real denominator does not fit in i64".into()))?;
        Ok(ChcExpr::Real(numer, denom))
    }

    fn parse_decimal_real(num_str: &str) -> ChcResult<ChcExpr> {
        let (negative, unsigned) = match num_str.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, num_str),
        };
        let (whole, frac) = unsigned
            .split_once('.')
            .ok_or_else(|| ChcError::Parse(format!("Invalid decimal numeral: {num_str}")))?;
        if whole.is_empty() || frac.is_empty() {
            return Err(ChcError::Parse(format!(
                "Invalid decimal numeral: {num_str}"
            )));
        }

        let whole_val = whole
            .parse::<i128>()
            .map_err(|_| ChcError::Parse(format!("Invalid decimal numeral: {num_str}")))?;
        let frac_val = frac
            .parse::<i128>()
            .map_err(|_| ChcError::Parse(format!("Invalid decimal numeral: {num_str}")))?;
        let frac_len = u32::try_from(frac.len())
            .map_err(|_| ChcError::Parse("Decimal literal is too long".into()))?;
        let denom = 10_i128
            .checked_pow(frac_len)
            .ok_or_else(|| ChcError::Parse("Decimal denominator overflow".into()))?;
        let mut numer = whole_val
            .checked_mul(denom)
            .and_then(|n| n.checked_add(frac_val))
            .ok_or_else(|| ChcError::Parse("Decimal numerator overflow".into()))?;
        if negative {
            numer = numer
                .checked_neg()
                .ok_or_else(|| ChcError::Parse("Decimal numerator overflow".into()))?;
        }

        Self::normalize_rational_i128(numer, denom)
    }

    /// Encode a BigInt value as a `ChcExpr`.
    ///
    /// Thin delegate to [`ChcExpr::from_bigint`] (Int-if-fits, else the
    /// sign-aware Horner base-10^9 encoding), which is shared with term→expr
    /// back-conversion in `smt/model_extract.rs`.
    pub(super) fn encode_large_int(n: BigInt) -> ChcExpr {
        ChcExpr::from_bigint(n)
    }

    /// Parse a symbol expression (variable or constant)
    pub(super) fn parse_symbol_expr(&mut self) -> ChcResult<ChcExpr> {
        let name = self.parse_symbol()?;

        match name.as_str() {
            "true" => Ok(ChcExpr::Bool(true)),
            "false" => Ok(ChcExpr::Bool(false)),
            _ => {
                // Check if it's a nullary predicate application first
                if let Some((pred_id, sorts)) = self.predicates.get(&name).cloned() {
                    if sorts.is_empty() {
                        // Nullary predicate - create a PredicateApp with no arguments
                        return Ok(ChcExpr::predicate_app(&name, pred_id, Vec::new()));
                    }
                }
                // Check if it's a nullary constructor (e.g., Nil for a list datatype)
                if let Some((ret_sort, arg_sorts)) = self
                    .resolve_function_signature(&name, &[])?
                    .or_else(|| self.functions.get(&name).cloned())
                {
                    if arg_sorts.is_empty() {
                        // Nullary constructor/function - create a FuncApp with no arguments
                        return Ok(ChcExpr::FuncApp(name, ret_sort, Vec::new()));
                    }
                }
                // An active binder rename shadows everything else: inside a
                // renamed binder's body this name denotes THAT binder, not the
                // outer binding of the same name. Innermost wins, so scan back.
                // `active_renames` is empty unless a capture actually occurred.
                let name = if self.active_renames.is_empty() {
                    name
                } else {
                    match self
                        .active_renames
                        .iter()
                        .rev()
                        .find(|(from, _)| *from == name)
                    {
                        Some((_, to)) => to.clone(),
                        None => name,
                    }
                };
                // Look up variable
                if let Some(sort) = self.variables.get(&name).cloned() {
                    Ok(ChcExpr::var(ChcVar::new(name, sort)))
                } else {
                    // Assume it's an integer variable if not declared
                    Ok(ChcExpr::var(ChcVar::new(name, ChcSort::Int)))
                }
            }
        }
    }
}

fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = match a.checked_abs() {
        Some(value) => value,
        None => return 1,
    };
    b = match b.checked_abs() {
        Some(value) => value,
        None => return 1,
    };
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    if a == 0 {
        1
    } else {
        a
    }
}
