// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lean term exporter: converts AY terms to Lean syntax.
//!
//! Extracted from `lib.rs` as part of code-health module split.
//! The `LeanError` type remains in `lib.rs`.

use super::{escape_lean_string, export_sort_to_lean, sanitize_lean_name, LeanError};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use std::fmt::Write;

/// Exports AY terms to Lean syntax.
///
/// Handles term export with precedence-aware parenthesization,
/// constant export, function application export (including indexed),
/// and SAT/UNSAT verification code generation.
#[non_exhaustive]
pub struct LeanExporter<'a> {
    store: &'a TermStore,
}

impl<'a> LeanExporter<'a> {
    /// Create a new exporter with a reference to a term store.
    pub fn new(store: &'a TermStore) -> Self {
        Self { store }
    }

    /// Export a term to Lean syntax.
    pub fn export_term(&self, term: TermId) -> Result<String, LeanError> {
        self.export_term_inner(term, 0)
    }

    /// Export a term with precedence tracking for parenthesization.
    fn export_term_inner(&self, term: TermId, parent_prec: u8) -> Result<String, LeanError> {
        let data = self.store.get(term).clone();
        let sort = self.store.sort(term);

        let (result, prec) = match &data {
            TermData::Const(c) => (Self::export_constant(c)?, 100),
            TermData::Var(name, _) => (sanitize_lean_name(name), 100),
            TermData::Not(inner) => {
                let inner_str = self.export_term_inner(*inner, 90)?;
                (format!("!{inner_str}"), 90)
            }
            TermData::Ite(cond, then_br, else_br) => {
                let cond_str = self.export_term_inner(*cond, 0)?;
                let then_str = self.export_term_inner(*then_br, 0)?;
                let else_str = self.export_term_inner(*else_br, 0)?;
                (format!("if {cond_str} then {then_str} else {else_str}"), 10)
            }
            TermData::App(sym, args) => self.export_app(sym, args, sort)?,
            TermData::Let(bindings, body) => {
                let mut result = String::new();
                for (name, value) in bindings {
                    let value_str = self.export_term_inner(*value, 0)?;
                    let _ = write!(
                        result,
                        "let {} := {} in ",
                        sanitize_lean_name(name),
                        value_str
                    );
                }
                let body_str = self.export_term_inner(*body, 0)?;
                result.push_str(&body_str);
                (result, 5)
            }
            TermData::Forall(vars, body, _triggers) => {
                let vars_str: Vec<String> = vars
                    .iter()
                    .map(|(name, sort)| {
                        self.export_sort(sort)
                            .map(|s| format!("({} : {})", sanitize_lean_name(name), s))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let body_str = self.export_term_inner(*body, 0)?;
                (format!("∀ {}, {}", vars_str.join(" "), body_str), 5)
            }
            TermData::Exists(vars, body, _triggers) => {
                let vars_str: Vec<String> = vars
                    .iter()
                    .map(|(name, sort)| {
                        self.export_sort(sort)
                            .map(|s| format!("({} : {})", sanitize_lean_name(name), s))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let body_str = self.export_term_inner(*body, 0)?;
                (format!("∃ {}, {}", vars_str.join(" "), body_str), 5)
            }
            // `TermData` is `#[non_exhaustive]` in ay-core. Return a typed
            // error for unhandled variants rather than panicking at runtime.
            _ => {
                return Err(LeanError::Unsupported {
                    kind: "TermData::<unhandled-variant>",
                });
            }
        };

        // Add parentheses if needed
        if prec < parent_prec {
            Ok(format!("({result})"))
        } else {
            Ok(result)
        }
    }

    /// Export a constant to Lean syntax.
    ///
    /// Returns `LeanError::Unsupported` if `ay_core::Constant` grows a new
    /// variant that this bridge does not handle yet. `Constant` is
    /// `#[non_exhaustive]`, so we must route unknown variants through a typed
    /// error rather than panicking at runtime.
    pub(crate) fn export_constant(c: &Constant) -> Result<String, LeanError> {
        let rendered = match c {
            Constant::Bool(true) => "true".to_string(),
            Constant::Bool(false) => "false".to_string(),
            Constant::Int(i) => {
                if i.sign() == num_bigint::Sign::Minus {
                    format!("({i})")
                } else {
                    i.to_string()
                }
            }
            Constant::Rational(r) => {
                let numer = r.0.numer();
                let denom = r.0.denom();
                if denom == &num_bigint::BigInt::from(1) {
                    if numer.sign() == num_bigint::Sign::Minus {
                        format!("({numer})")
                    } else {
                        numer.to_string()
                    }
                } else {
                    format!("({numer} / {denom})")
                }
            }
            Constant::BitVec { value, width } => format!("(BitVec.ofNat {width} {value})"),
            Constant::String(s) => format!("\"{}\"", escape_lean_string(s)),
            _ => {
                return Err(LeanError::Unsupported {
                    kind: "Constant::<unhandled-variant>",
                });
            }
        };
        Ok(rendered)
    }

    /// Export a function application to Lean syntax.
    fn export_app(
        &self,
        sym: &Symbol,
        args: &[TermId],
        _sort: &Sort,
    ) -> Result<(String, u8), LeanError> {
        let name = sym.name();

        // Handle indexed symbols (like extract, repeat)
        if let Symbol::Indexed(base, indices) = sym {
            return self.export_indexed_app(base, indices, args);
        }

        // Handle common SMT-LIB operations
        match (name, args.len()) {
            // Boolean operations
            ("and", _) => {
                let parts: Result<Vec<_>, _> = args
                    .iter()
                    .map(|a| self.export_term_inner(*a, 35))
                    .collect();
                Ok((parts?.join(" && "), 35))
            }
            ("or", _) => {
                let parts: Result<Vec<_>, _> = args
                    .iter()
                    .map(|a| self.export_term_inner(*a, 30))
                    .collect();
                Ok((parts?.join(" || "), 30))
            }
            ("=>" | "implies", 2) => {
                let lhs = self.export_term_inner(args[0], 25)?;
                let rhs = self.export_term_inner(args[1], 24)?;
                Ok((format!("{lhs} -> {rhs}"), 25))
            }
            ("xor", 2) => {
                let lhs = self.export_term_inner(args[0], 50)?;
                let rhs = self.export_term_inner(args[1], 50)?;
                Ok((format!("{lhs} ^^ {rhs}"), 50))
            }

            // Equality
            ("=", 2) => {
                let lhs = self.export_term_inner(args[0], 50)?;
                let rhs = self.export_term_inner(args[1], 50)?;
                Ok((format!("{lhs} = {rhs}"), 50))
            }
            ("distinct", _) => {
                // Generate pairwise inequalities
                let mut parts = Vec::new();
                for i in 0..args.len() {
                    for j in (i + 1)..args.len() {
                        let lhs = self.export_term_inner(args[i], 50)?;
                        let rhs = self.export_term_inner(args[j], 50)?;
                        parts.push(format!("{lhs} != {rhs}"));
                    }
                }
                Ok((parts.join(" && "), 35))
            }

            // Arithmetic operations
            ("+", _) => {
                let parts: Result<Vec<_>, _> = args
                    .iter()
                    .map(|a| self.export_term_inner(*a, 65))
                    .collect();
                Ok((parts?.join(" + "), 65))
            }
            ("-" | "bvneg", 1) => {
                let inner = self.export_term_inner(args[0], 70)?;
                Ok((format!("-{inner}"), 70))
            }
            ("-" | "bvsub", 2) => {
                let lhs = self.export_term_inner(args[0], 65)?;
                let rhs = self.export_term_inner(args[1], 66)?;
                Ok((format!("{lhs} - {rhs}"), 65))
            }
            ("*", _) => {
                let parts: Result<Vec<_>, _> = args
                    .iter()
                    .map(|a| self.export_term_inner(*a, 70))
                    .collect();
                Ok((parts?.join(" * "), 70))
            }
            ("div" | "/", 2) => {
                let lhs = self.export_term_inner(args[0], 70)?;
                let rhs = self.export_term_inner(args[1], 71)?;
                Ok((format!("{lhs} / {rhs}"), 70))
            }
            ("mod", 2) => {
                let lhs = self.export_term_inner(args[0], 70)?;
                let rhs = self.export_term_inner(args[1], 71)?;
                Ok((format!("{lhs} % {rhs}"), 70))
            }

            // Comparisons
            ("<", 2) => {
                let lhs = self.export_term_inner(args[0], 50)?;
                let rhs = self.export_term_inner(args[1], 50)?;
                Ok((format!("{lhs} < {rhs}"), 50))
            }
            ("<=", 2) => {
                let lhs = self.export_term_inner(args[0], 50)?;
                let rhs = self.export_term_inner(args[1], 50)?;
                Ok((format!("{lhs} <= {rhs}"), 50))
            }
            (">", 2) => {
                let lhs = self.export_term_inner(args[0], 50)?;
                let rhs = self.export_term_inner(args[1], 50)?;
                Ok((format!("{lhs} > {rhs}"), 50))
            }
            (">=", 2) => {
                let lhs = self.export_term_inner(args[0], 50)?;
                let rhs = self.export_term_inner(args[1], 50)?;
                Ok((format!("{lhs} >= {rhs}"), 50))
            }

            // Bitvector operations
            ("bvadd", 2) => {
                let lhs = self.export_term_inner(args[0], 65)?;
                let rhs = self.export_term_inner(args[1], 65)?;
                Ok((format!("{lhs} + {rhs}"), 65))
            }
            ("bvmul", 2) => {
                let lhs = self.export_term_inner(args[0], 70)?;
                let rhs = self.export_term_inner(args[1], 70)?;
                Ok((format!("{lhs} * {rhs}"), 70))
            }
            ("bvand", 2) => {
                let lhs = self.export_term_inner(args[0], 56)?;
                let rhs = self.export_term_inner(args[1], 56)?;
                Ok((format!("{lhs} &&& {rhs}"), 56))
            }
            ("bvor", 2) => {
                let lhs = self.export_term_inner(args[0], 55)?;
                let rhs = self.export_term_inner(args[1], 55)?;
                Ok((format!("{lhs} ||| {rhs}"), 55))
            }
            ("bvxor", 2) => {
                let lhs = self.export_term_inner(args[0], 58)?;
                let rhs = self.export_term_inner(args[1], 58)?;
                Ok((format!("{lhs} ^^^ {rhs}"), 58))
            }
            ("bvnot", 1) => {
                let inner = self.export_term_inner(args[0], 90)?;
                Ok((format!("~~~{inner}"), 90))
            }
            ("bvult", 2) => {
                let lhs = self.export_term_inner(args[0], 50)?;
                let rhs = self.export_term_inner(args[1], 50)?;
                Ok((format!("BitVec.ult {lhs} {rhs}"), 50))
            }
            ("bvule", 2) => {
                let lhs = self.export_term_inner(args[0], 50)?;
                let rhs = self.export_term_inner(args[1], 50)?;
                Ok((format!("BitVec.ule {lhs} {rhs}"), 50))
            }
            ("bvslt", 2) => {
                let lhs = self.export_term_inner(args[0], 50)?;
                let rhs = self.export_term_inner(args[1], 50)?;
                Ok((format!("BitVec.slt {lhs} {rhs}"), 50))
            }
            ("bvsle", 2) => {
                let lhs = self.export_term_inner(args[0], 50)?;
                let rhs = self.export_term_inner(args[1], 50)?;
                Ok((format!("BitVec.sle {lhs} {rhs}"), 50))
            }

            // Array operations
            ("select", 2) => {
                let arr = self.export_term_inner(args[0], 100)?;
                let idx = self.export_term_inner(args[1], 0)?;
                Ok((format!("{arr}[{idx}]"), 100))
            }
            ("store", 3) => {
                let arr = self.export_term_inner(args[0], 100)?;
                let idx = self.export_term_inner(args[1], 0)?;
                let val = self.export_term_inner(args[2], 0)?;
                Ok((format!("Array.set {arr} {idx} {val}"), 80))
            }

            // Default: function application
            _ => {
                let lean_name = sanitize_lean_name(name);
                if args.is_empty() {
                    Ok((lean_name, 100))
                } else {
                    let arg_strs: Result<Vec<_>, _> = args
                        .iter()
                        .map(|a| self.export_term_inner(*a, 100))
                        .collect();
                    Ok((format!("{} {}", lean_name, arg_strs?.join(" ")), 80))
                }
            }
        }
    }

    /// Export an indexed function application (like extract, repeat).
    fn export_indexed_app(
        &self,
        base: &str,
        indices: &[u32],
        args: &[TermId],
    ) -> Result<(String, u8), LeanError> {
        match (base, indices.len(), args.len()) {
            ("extract", 2, 1) => {
                let hi = indices[0];
                let lo = indices[1];
                let inner = self.export_term_inner(args[0], 100)?;
                Ok((format!("BitVec.extractLsb {hi} {lo} {inner}"), 80))
            }
            ("repeat", 1, 1) => {
                let n = indices[0];
                let inner = self.export_term_inner(args[0], 100)?;
                Ok((format!("BitVec.replicate {n} {inner}"), 80))
            }
            ("zero_extend", 1, 1) => {
                let n = indices[0];
                let inner = self.export_term_inner(args[0], 100)?;
                Ok((format!("BitVec.zeroExtend {n} {inner}"), 80))
            }
            ("sign_extend", 1, 1) => {
                let n = indices[0];
                let inner = self.export_term_inner(args[0], 100)?;
                Ok((format!("BitVec.signExtend {n} {inner}"), 80))
            }
            _ => {
                // Generic indexed function
                let arg_strs: Result<Vec<_>, _> = args
                    .iter()
                    .map(|a| self.export_term_inner(*a, 100))
                    .collect();
                let idx_str = indices
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" ");
                Ok((format!("{}_{} {}", base, idx_str, arg_strs?.join(" ")), 80))
            }
        }
    }

    /// Export a sort to Lean type syntax.
    ///
    /// Returns `LeanError::Unsupported` if the sort is a `ay_core::Sort`
    /// variant the bridge does not handle yet (e.g. added upstream without
    /// a matching arm here).
    pub fn export_sort(&self, sort: &Sort) -> Result<String, LeanError> {
        export_sort_to_lean(sort)
    }

    /// Generate Lean code to verify a SAT model.
    pub fn generate_sat_verification(
        &self,
        formula: TermId,
        model: &[(String, bool)],
    ) -> Result<String, LeanError> {
        let mut code = String::new();

        // Header
        code.push_str("-- AY SAT Verification\n");
        code.push_str("-- Auto-generated by ay-lean-bridge\n\n");

        // Define the variables with their values from the model
        for (name, value) in model {
            let lean_name = sanitize_lean_name(name);
            let _ = writeln!(code, "def {lean_name} : Bool := {value}");
        }
        code.push('\n');

        // Export the formula
        let formula_str = self.export_term(formula)?;

        // Create a theorem that the formula evaluates to true
        let _ = writeln!(
            code,
            "theorem sat_verification : {formula_str} = true := by native_decide"
        );

        Ok(code)
    }

    /// Generate Lean code to check an UNSAT claim.
    ///
    /// Note: This only checks that the formula is well-typed and
    /// semantically valid Lean code. Full UNSAT verification requires
    /// DRAT proof checking.
    pub fn generate_unsat_check(&self, formula: TermId) -> Result<String, LeanError> {
        let mut code = String::new();

        // Header
        code.push_str("-- AY UNSAT Check\n");
        code.push_str("-- Auto-generated by ay-lean-bridge\n\n");

        // Collect free variables
        let vars = self.collect_variables(formula)?;

        // Declare variables
        for (name, sort) in &vars {
            let lean_name = sanitize_lean_name(name);
            let lean_sort = self.export_sort(sort)?;
            let _ = writeln!(code, "variable ({lean_name} : {lean_sort})");
        }
        if !vars.is_empty() {
            code.push('\n');
        }

        // Export the formula
        let formula_str = self.export_term(formula)?;

        // Create a #check to verify the formula is well-typed
        let _ = writeln!(code, "#check ({formula_str} : Bool)");

        Ok(code)
    }

    /// Collect all free variables in a term.
    fn collect_variables(&self, term: TermId) -> Result<Vec<(String, Sort)>, LeanError> {
        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        self.collect_variables_inner(term, &mut vars, &mut seen)?;
        Ok(vars)
    }

    fn collect_variables_inner(
        &self,
        term: TermId,
        vars: &mut Vec<(String, Sort)>,
        seen: &mut std::collections::HashSet<String>,
    ) -> Result<(), LeanError> {
        let data = self.store.get(term).clone();
        let sort = self.store.sort(term).clone();

        match &data {
            TermData::Var(name, _) => {
                if !seen.contains(name) {
                    seen.insert(name.clone());
                    vars.push((name.clone(), sort));
                }
            }
            TermData::Const(_) => {}
            TermData::Not(inner) => {
                self.collect_variables_inner(*inner, vars, seen)?;
            }
            TermData::Ite(c, t, e) => {
                self.collect_variables_inner(*c, vars, seen)?;
                self.collect_variables_inner(*t, vars, seen)?;
                self.collect_variables_inner(*e, vars, seen)?;
            }
            TermData::App(_, args) => {
                for arg in args {
                    self.collect_variables_inner(*arg, vars, seen)?;
                }
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    self.collect_variables_inner(*value, vars, seen)?;
                }
                self.collect_variables_inner(*body, vars, seen)?;
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                // Note: bound variables in quantifiers are not free variables
                // Only collect from body (they won't be added due to shadowing)
                self.collect_variables_inner(*body, vars, seen)?;
            }
            // `TermData` is `#[non_exhaustive]` in ay-core. Return a typed
            // error for unhandled variants rather than panicking at runtime.
            _ => {
                return Err(LeanError::Unsupported {
                    kind: "TermData::<unhandled-variant>",
                });
            }
        }
        Ok(())
    }
}
