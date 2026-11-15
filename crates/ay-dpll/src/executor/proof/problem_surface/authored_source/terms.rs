// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pinned Carcara's parse of one authored term: `Parser::parse_term`,
//! `parse_application`, `parse_indexed_operator`, `make_qualified_op`,
//! `make_app`, `parse_let_term`, `parse_binder` and `parse_annotated_term`
//! (`carcara/src/parser/mod.rs` at 9a352ee), which sort-check as they parse.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_frontend::command::{
    Constant, Index, QualifiedIdentifier, Sort as ParsedSort, Term as ParsedTerm,
};
use ay_frontend::SExpr;

use super::operators::{builtin, is_builtin};
use super::sorts::{resolve, CarcaraSort as S};
use super::{spelling_gap, ProblemScope};

const TERM_STACK_RED_ZONE: usize = 32 * 1024;
const TERM_STACK_SIZE: usize = 1024 * 1024;

/// One term walk: the problem's signature plus the variables bound around
/// the current subterm (each name maps to its shadowing stack).
pub(super) struct TermCheck<'a> {
    scope: &'a mut ProblemScope,
    bound: HashMap<String, Vec<S>>,
}

impl<'a> TermCheck<'a> {
    pub(super) fn new(scope: &'a mut ProblemScope) -> Self {
        Self {
            scope,
            bound: HashMap::default(),
        }
    }

    /// Bind `name` for the rest of this walk (a `define-fun` parameter), or
    /// for the subterm until [`Self::unbind`].
    pub(super) fn bind(&mut self, name: &str, sort: S) -> Result<(), String> {
        spelling_gap(name)?;
        self.bound.entry(name.to_string()).or_default().push(sort);
        Ok(())
    }

    fn unbind(&mut self, name: &str) {
        if let Some(stack) = self.bound.get_mut(name) {
            stack.pop();
        }
    }

    fn resolve(&self, sort: &ParsedSort) -> Result<S, String> {
        if self.scope.real_only_logic && super::sorts::has_indexed(sort) {
            return Err(super::REAL_ONLY_NUMERAL.to_string());
        }
        resolve(&self.scope.sorts, &[], sort)
    }

    /// The sort pinned Carcara gives `term`, or why its parser refuses it.
    pub(super) fn infer(&mut self, term: &ParsedTerm) -> Result<S, String> {
        stacker::maybe_grow(TERM_STACK_RED_ZONE, TERM_STACK_SIZE, || {
            self.infer_unguarded(term)
        })
    }

    fn infer_all(&mut self, terms: &[ParsedTerm]) -> Result<Vec<S>, String> {
        terms.iter().map(|term| self.infer(term)).collect()
    }

    fn infer_unguarded(&mut self, term: &ParsedTerm) -> Result<S, String> {
        match term {
            ParsedTerm::Const(constant) => self.constant(constant),
            ParsedTerm::Symbol(name) => self.symbol(name),
            ParsedTerm::App(name, args) => {
                let args = self.infer_all(args)?;
                self.application(name, &args)
            }
            ParsedTerm::IndexedApp(name, indices, args) => {
                let args = self.infer_all(args)?;
                self.indexed(name, indices, &args)
            }
            ParsedTerm::QualifiedApp(identifier, sort, args) => {
                let args = self.infer_all(args)?;
                self.qualified(identifier, sort, &args)
            }
            ParsedTerm::Let(bindings, _) if bindings.is_empty() => Err(EMPTY_BINDINGS.to_string()),
            ParsedTerm::Forall(bindings, _) | ParsedTerm::Exists(bindings, _)
                if bindings.is_empty() =>
            {
                Err(EMPTY_BINDINGS.to_string())
            }
            ParsedTerm::Let(bindings, body) => {
                let values = bindings
                    .iter()
                    .map(|(_, value)| self.infer(value))
                    .collect::<Result<Vec<_>, _>>()?;
                let names: Vec<&str> = bindings.iter().map(|(name, _)| name.as_str()).collect();
                self.scoped(&names, values, body)
            }
            ParsedTerm::Forall(bindings, body) | ParsedTerm::Exists(bindings, body) => {
                let sorts = bindings
                    .iter()
                    .map(|(_, sort)| self.resolve(sort))
                    .collect::<Result<Vec<_>, _>>()?;
                let names: Vec<&str> = bindings.iter().map(|(name, _)| name.as_str()).collect();
                match self.scoped(&names, sorts, body)? {
                    S::Bool => Ok(S::Bool),
                    other => Err(format!(
                        "a quantifier body has sort {other}; pinned Carcara 1.1.0 requires Bool"
                    )),
                }
            }
            ParsedTerm::Lambda(..) => Err("the problem uses `lambda`, which pinned Carcara \
                 1.1.0 sorts as a function, never as the Array AY reads it as"
                .to_string()),
            ParsedTerm::Match(..) => Err("the problem uses `match`: pinned Carcara 1.1.0 \
                 panics on a constructor pattern with fields and rejects the legacy `case` \
                 spelling, which AY does not retain"
                .to_string()),
            ParsedTerm::Annotated(inner, attributes) => self.annotated(inner, attributes),
            _ => {
                Err("the problem uses a term form pinned Carcara 1.1.0 does not parse".to_string())
            }
        }
    }

    /// `body` with `names` bound to `sorts`.
    fn scoped(&mut self, names: &[&str], sorts: Vec<S>, body: &ParsedTerm) -> Result<S, String> {
        let mut bound = 0;
        let mut result = Ok(());
        for (name, sort) in names.iter().zip(sorts) {
            result = self.bind(name, sort);
            if result.is_err() {
                break;
            }
            bound += 1;
        }
        let result = result.and_then(|()| self.infer(body));
        for name in &names[..bound] {
            self.unbind(name);
        }
        result
    }

    fn constant(&self, constant: &Constant) -> Result<S, String> {
        Ok(match constant {
            Constant::True | Constant::False => S::Bool,
            Constant::Numeral(text) | Constant::Decimal(text) if !carcara_reads_number(text) => {
                return Err(format!(
                    "the problem writes the number `{text}` with a leading zero, which pinned \
                     Carcara 1.1.0's lexer rejects"
                ));
            }
            Constant::Numeral(_) if self.scope.real_only_logic => S::Real,
            Constant::Numeral(_) => S::Int,
            Constant::Decimal(_) => S::Real,
            // AY carries a surrogate escape (`\u{d800}`) as one character;
            // Carcara's lexer stops at it (`invalid Unicode value`).
            Constant::String(value) if ay_core::first_surrogate_carrier(value).is_some() => {
                return Err(
                    "the problem spells a surrogate code point in a string literal, \
                     which pinned Carcara 1.1.0's lexer rejects"
                        .to_string(),
                );
            }
            Constant::String(_) => S::Str,
            Constant::Hexadecimal(digits) => S::BitVec(literal_width(digits, 4)?),
            Constant::Binary(digits) => S::BitVec(literal_width(digits, 1)?),
            _ => {
                return Err("the problem uses a literal pinned Carcara 1.1.0 does not parse".into())
            }
        })
    }

    /// `parse_term` on a bare symbol: a `:named` label, then a builtin, then a
    /// bound variable or declared nullary function, in Carcara's order.
    fn symbol(&self, name: &str) -> Result<S, String> {
        if let Some(sort) = self.scope.named.get(name) {
            return Ok(sort.clone());
        }
        if let Some(outcome) = builtin(name, &[]) {
            return outcome;
        }
        if let Some(sort) = self.bound.get(name).and_then(|stack| stack.last()) {
            return Ok(sort.clone());
        }
        match self.scope.functions.get(name) {
            Some(signature) if signature.args.is_empty() && signature.params.is_empty() => {
                Ok(signature.result.clone())
            }
            Some(signature) if signature.args.is_empty() => Err(format!(
                "the problem uses `{name}`, a nullary constructor of a parametric datatype, \
                 without `(as {name} <sort>)`, so pinned Carcara 1.1.0 leaves its sort open"
            )),
            Some(_) => Err(format!(
                "the problem uses the function `{name}` without arguments"
            )),
            // An unquoted `-5` is a `Numeral` already; a symbol spelled `-5`
            // is the quoted `|-5|`, a symbol to Carcara as well.
            None => Err(self.undefined(name)),
        }
    }

    /// `parse_application` on `(name args...)`. Carcara reads the arguments
    /// as a NON-empty sequence, so `(c)` stops its parse whatever `c` is.
    fn application(&self, name: &str, args: &[S]) -> Result<S, String> {
        if args.is_empty() {
            return Err(format!(
                "the problem writes `({name})` with no arguments, which pinned Carcara 1.1.0 \
                 does not parse"
            ));
        }
        if self.scope.named.contains_key(name) {
            return Err(format!(
                "the problem applies the `:named` label `{name}` to arguments"
            ));
        }
        if let Some(outcome) = builtin(name, args) {
            return outcome;
        }
        if name == "eo" || self.bound.get(name).is_some_and(|stack| !stack.is_empty()) {
            return Err(format!(
                "the problem applies `{name}`, which is not a function"
            ));
        }
        let Some(signature) = self.scope.functions.get(name) else {
            return Err(self.undefined(name));
        };
        if args.len() != signature.args.len() {
            return Err(format!(
                "the problem applies `{name}` to {} argument(s), not its {}",
                args.len(),
                signature.args.len()
            ));
        }
        let mut binding = HashMap::default();
        for (index, (expected, actual)) in signature.args.iter().zip(args).enumerate() {
            if !expected.matches(actual, &mut binding) {
                return Err(format!(
                    "argument {} of `{name}` has sort {actual}; pinned Carcara 1.1.0 requires \
                     {expected} (it coerces no Int/Real, Bool/Int or bit-vector width)",
                    index + 1
                ));
            }
        }
        Ok(signature.result.substitute(&binding))
    }

    /// `parse_indexed_operator` and `make_indexed_op` on `((_ name i...) args)`.
    fn indexed(&self, name: &str, indices: &[Index], args: &[S]) -> Result<S, String> {
        let refuse = || {
            format!(
                "the problem uses the indexed operator `(_ {name} ...)` with these indices or \
                 arguments, which pinned Carcara 1.1.0 does not parse"
            )
        };
        if name != "is" && self.scope.real_only_logic {
            return Err(super::REAL_ONLY_NUMERAL.to_string());
        }
        if name == "is" {
            return match (indices, args) {
                ([Index::Symbol(constructor)], [S::Named(..)])
                    if self
                        .scope
                        .functions
                        .get(constructor)
                        .is_some_and(|signature| signature.constructor) =>
                {
                    Ok(S::Bool)
                }
                _ => Err(refuse()),
            };
        }
        let numbers = indices
            .iter()
            .map(|index| index.as_numeral().and_then(|text| text.parse::<u64>().ok()))
            .collect::<Option<Vec<_>>>()
            .ok_or_else(refuse)?;
        if let Some(value) = name.strip_prefix("bv") {
            let literal = value.bytes().all(|byte| byte.is_ascii_digit()) && !value.is_empty();
            return match (numbers.as_slice(), args) {
                ([width], []) if literal && *width > 0 => Ok(S::BitVec(*width)),
                _ => Err(refuse()),
            };
        }
        let width = |index: usize| match args.get(index) {
            Some(S::BitVec(width)) => Some(*width),
            _ => None,
        };
        let sort = match (name, numbers.as_slice(), args.len()) {
            ("extract", [high, low], 1) => width(0)
                .filter(|m| m > high && high >= low)
                .map(|_| S::BitVec(high - low + 1)),
            ("zero_extend" | "sign_extend", [extra], 1) => {
                width(0).and_then(|m| m.checked_add(*extra)).map(S::BitVec)
            }
            ("rotate_left" | "rotate_right", [_], 1) => width(0).map(S::BitVec),
            ("repeat", [count], 1) => width(0)
                .and_then(|m| m.checked_mul(*count))
                .filter(|total| *total > 0)
                .map(S::BitVec),
            ("int_to_bv", [bits], 1) if *bits > 0 => {
                (args[0] == S::Int).then_some(S::BitVec(*bits))
            }
            ("re.^", [_], 1) | ("re.loop", [_, _], 1) => {
                (args[0] == S::RegLan).then_some(S::RegLan)
            }
            _ => None,
        };
        sort.ok_or_else(refuse)
    }

    /// `(as id sort)` and `((as id sort) args)`: pinned Carcara accepts `const`
    /// over an Array sort, and a constructor of a PARAMETRIC datatype; every
    /// other qualified identifier stops the parse (`not a valid qualified
    /// operator`), however AY's frontend reads it.
    fn qualified(
        &self,
        identifier: &QualifiedIdentifier,
        sort: &ParsedSort,
        args: &[S],
    ) -> Result<S, String> {
        let Some(name) = identifier.as_symbol() else {
            return Err(
                "the problem qualifies an indexed identifier with `as`, which pinned \
                 Carcara 1.1.0 does not parse"
                    .to_string(),
            );
        };
        let sort = self.resolve(sort)?;
        if name == "const" {
            return match (&sort, args) {
                (S::Array(_, element), [value]) if **element == *value => Ok(sort.clone()),
                _ => Err(format!(
                    "`(as const {sort})` is applied to arguments of sorts that pinned Carcara \
                     1.1.0 does not accept (exactly one, of the array's element sort)"
                )),
            };
        }
        let parametric_constructor = self
            .scope
            .functions
            .get(name)
            .filter(|signature| signature.constructor && !signature.params.is_empty());
        let Some(signature) = parametric_constructor else {
            return Err(format!(
                "the problem uses `(as {name} {sort})`: pinned Carcara 1.1.0 accepts a \
                 qualified identifier only for `const` or a constructor of a parametric \
                 datatype, so its parser stops at `{name}` (not a valid qualified operator)"
            ));
        };
        let mut binding = HashMap::default();
        if !signature.result.matches(&sort, &mut binding) || signature.args.len() != args.len() {
            return Err(format!(
                "the problem uses `(as {name} {sort})` with a sort or argument count pinned \
                 Carcara 1.1.0 does not accept"
            ));
        }
        for (expected, actual) in signature.args.iter().zip(args) {
            if expected.substitute(&binding) != *actual {
                return Err(format!(
                    "an argument of `(as {name} {sort})` has sort {actual}, not {}",
                    expected.substitute(&binding)
                ));
            }
        }
        Ok(sort)
    }

    /// Why Carcara stops at `name`, which is neither bound, declared nor a
    /// builtin it accepts with these arguments.
    fn undefined(&self, name: &str) -> String {
        if self.scope.skipped.contains(name) {
            return format!(
                "the problem uses `{name}`, which it defines with `define-const`: pinned \
                 Carcara 1.1.0's problem parser skips that command, so `{name}` is undefined"
            );
        }
        undefined(name)
    }

    /// `parse_annotated_term`: `:named` defines a nullary label; every other
    /// attribute is skipped token by token.
    fn annotated(
        &mut self,
        inner: &ParsedTerm,
        attributes: &[(String, SExpr)],
    ) -> Result<S, String> {
        if attributes.is_empty() {
            return Err(
                "the problem writes `(! t)` with no attribute; pinned Carcara 1.1.0 \
                 requires at least one (`expected non-empty sequence`)"
                    .to_string(),
            );
        }
        let sort = self.infer(inner)?;
        for (keyword, value) in attributes {
            if keyword == ":named" {
                let SExpr::Symbol(label) = value else {
                    return Err("a `:named` attribute's value is not a symbol".to_string());
                };
                spelling_gap(label)?;
                self.scope.named.insert(label.clone(), sort.clone());
            }
        }
        Ok(sort)
    }
}

/// `(let () t)`, `(forall () t)` and `(exists () t)`: AY's frontend reads an
/// empty binder list, and SMT-LIB and pinned Carcara 1.1.0 require at least
/// one binder.
const EMPTY_BINDINGS: &str = "the problem writes a `let`, `forall` or `exists` with no \
     binder; pinned Carcara 1.1.0 requires at least one (`expected non-empty sequence`)";

fn literal_width(literal: &str, bits_per_digit: u64) -> Result<u64, String> {
    let digits = literal
        .strip_prefix("#x")
        .or_else(|| literal.strip_prefix("#b"))
        .unwrap_or(literal);
    u64::try_from(digits.len())
        .ok()
        .and_then(|count| count.checked_mul(bits_per_digit))
        .filter(|width| *width > 0)
        .ok_or_else(|| format!("bit-vector literal `{literal}` has no width"))
}

/// Whether pinned Carcara 1.1.0's lexer reads the numeral or decimal `text`.
/// AY's lexer refuses a leading zero in an unsigned numeral itself, but reads
/// the signed `-007` as -7, as z3 does; Carcara's `Lexer::read_number` refuses
/// it.
fn carcara_reads_number(text: &str) -> bool {
    let magnitude = text.strip_prefix('-').unwrap_or(text);
    let whole = magnitude
        .split_once('.')
        .map_or(magnitude, |(whole, _)| whole);
    whole == "0" || !whole.starts_with('0')
}

fn undefined(name: &str) -> String {
    if is_builtin(name) {
        return format!(
            "the problem uses the builtin `{name}` with a shape pinned Carcara rejects"
        );
    }
    format!(
        "the problem uses `{name}`, which pinned Carcara 1.1.0 does not define (not a builtin \
         of its grammar, and not a symbol the problem declares)"
    )
}
