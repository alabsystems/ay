// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What the lane ground model reads from the other printers, and how a
//! printed value comes back as a [`Ground`] (#dt-fd-ground-model,
//! #dt-fd-foreign-get-value).

use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId};

use super::{Ground, GroundEval, MAX_DEPTH, READING_PRINTED};

impl GroundEval<'_> {
    /// A term the lane evaluator does not value, read from the other
    /// printers (#dt-fd-foreign-get-value): only when it mentions nothing the
    /// lane values (no lane constant, constructor, selector or tester), so
    /// the value cannot disagree with the lane model, and only for a sort
    /// whose printed values are canonical (Bool, Int, Real, bit-vector,
    /// String, or a datatype value built from those). Such terms are what
    /// the lane never sees and the other printers value on their own: an
    /// arithmetic comparison, a record with an Int field, a sum sort
    /// preprocessing dropped. Without this a `(get-value)` of a Boolean
    /// combination of them and lane terms had no value at all after a lane
    /// `sat`.
    pub(super) fn printed_value(&mut self, t: TermId, fuel: u32) -> Option<Ground> {
        let scalar = match self.exec.ctx.terms.sort(t) {
            Sort::Bool | Sort::Datatype(_) | Sort::Uninterpreted(_) => false,
            Sort::Int | Sort::Real | Sort::BitVec(_) | Sort::String => true,
            _ => return None,
        };
        if self.mentions_lane(t, fuel) {
            return None;
        }
        let text = self.read_printed(t)?;
        if scalar {
            return Some(Ground::Opaque(normalized(&tokens(&text))));
        }
        self.parse(&text)
    }

    /// Whether `t` contains anything the lane model values.
    fn mentions_lane(&self, t: TermId, fuel: u32) -> bool {
        let mut stack = vec![t];
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        while let Some(u) = stack.pop() {
            if !seen.insert(u) {
                continue;
            }
            if seen.len() > fuel as usize * 64 {
                return true;
            }
            if self.lane.consts.contains_key(&u) || self.lane.substitutions.contains_key(&u) {
                return true;
            }
            let name = match self.exec.ctx.terms.get(u) {
                TermData::Var(name, _) => Some(name.as_str()),
                TermData::App(sym, _) => Some(sym.name()),
                _ => None,
            };
            if let Some(name) = name {
                let tested = name.strip_prefix("is-").unwrap_or(name);
                if self.lane.ctor_of.contains_key(name)
                    || self.lane.sel_of.contains_key(name)
                    || self.lane.ctor_of.contains_key(tested)
                {
                    return true;
                }
            }
            stack.extend(self.exec.ctx.terms.children(u));
        }
        false
    }

    /// `name` (a selector) applied to `value`, a value of a datatype
    /// outside the lane signature that another constructor built, read at
    /// `t` (#dt-fd-foreign-get-value). The other printers value each such
    /// application term by term, so `(tl nil)` and `(tl (tl k))` with
    /// `(tl k) = nil` could print different values (E13 round 6,
    /// `both_gv_congruence_dropped_sort_lane_sat`). Here the value is a
    /// FUNCTION of `value`: the printed value of the store's own `(name
    /// value)` term when it exists (what those printers give that term
    /// directly), else of `t`, and every later read agrees with the first.
    pub(super) fn foreign_wrong_ctor(
        &mut self,
        t: TermId,
        name: &str,
        value: &Ground,
    ) -> Option<Ground> {
        let key = (name.to_string(), value.clone());
        if let Some(v) = self.lane.foreign_wrong_ctor.borrow().get(&key) {
            return v.clone();
        }
        let canonical = self
            .ground_term(value, MAX_DEPTH)
            .and_then(|arg| self.exec.ctx.terms.find_app_named(name, &[arg]));
        let read = match canonical {
            Some(c) => self.read_printed(c),
            None if !self.mentions_lane(t, MAX_DEPTH) => self.read_printed(t),
            None => None,
        };
        let v = read.and_then(|text| self.parse(&text));
        self.lane
            .foreign_wrong_ctor
            .borrow_mut()
            .insert(key, v.clone());
        v
    }

    /// The existing term that spells `value`, if the store has one.
    fn ground_term(&self, value: &Ground, fuel: u32) -> Option<TermId> {
        if fuel == 0 {
            return None;
        }
        let terms = &self.exec.ctx.terms;
        let (ctor, args) = match value {
            Ground::Bool(b) => return terms.find_interned(&TermData::Const(Constant::Bool(*b))),
            Ground::Opaque(_) => return None,
            Ground::Ctor { sort, ctor, args } => {
                (self.lane.sorts.get(*sort as usize)?.ctors.get(*ctor)?, args)
            }
            Ground::Foreign { ctor, args } => (ctor, args),
        };
        if args.is_empty() {
            return terms
                .find_var(ctor)
                .filter(|&v| matches!(terms.get(v), TermData::Var(n, _) if n == ctor))
                .or_else(|| terms.find_app_named(ctor, &[]));
        }
        let ids = args
            .iter()
            .map(|a| self.ground_term(a, fuel - 1))
            .collect::<Option<Vec<_>>>()?;
        terms.find_app_named(ctor, &ids)
    }

    /// What the other printers print for `t` (never the lane model): a
    /// wrong-constructor selector application the query never mentions
    /// reads the printed selector table, as `(get-value)` does.
    pub(super) fn read_printed(&self, t: TermId) -> Option<String> {
        READING_PRINTED.with(|r| r.set(true));
        let printed = match self.exec.wrong_ctor_selector_case_value(self.printed, t) {
            Ok(Some(value)) => Ok(value),
            Ok(None) => self.exec.term_value_string_unstopped(self.printed, t),
            Err(error) => Err(error),
        };
        READING_PRINTED.with(|r| r.set(false));
        printed.ok()
    }

    /// A printed ground value of the lane signature, back as a [`Ground`].
    pub(super) fn parse(&self, text: &str) -> Option<Ground> {
        let tokens = tokens(text);
        let mut pos = 0;
        let value = self.parse_at(&tokens, &mut pos, MAX_DEPTH)?;
        (pos == tokens.len()).then_some(value)
    }

    fn parse_at(&self, tokens: &[String], pos: &mut usize, fuel: u32) -> Option<Ground> {
        if fuel == 0 {
            return None;
        }
        let start = *pos;
        let token = tokens.get(*pos)?;
        *pos += 1;
        if token == "true" || token == "false" {
            return Some(Ground::Bool(token == "true"));
        }
        if token != "(" {
            if let Some(name) = self.ctor_by_surface(token) {
                return self.constructed(&name, Vec::new());
            }
            // A scalar field of a datatype value outside the lane signature.
            return scalar_literal(token).then(|| Ground::Opaque(token.clone()));
        }
        let head = tokens.get(*pos)?;
        if scalar_head(head, tokens.get(*pos + 1)) {
            // `(- 3)`, `(/ 1 2)`, `(_ bv5 8)`: one scalar literal.
            let mut depth = 1usize;
            while depth > 0 {
                let t = tokens.get(*pos)?;
                *pos += 1;
                match t.as_str() {
                    "(" => depth += 1,
                    ")" => depth -= 1,
                    _ => {}
                }
            }
            return Some(Ground::Opaque(normalized(&tokens[start..*pos])));
        }
        *pos += 1;
        let name = self.ctor_by_surface(head)?;
        let mut args = Vec::new();
        while tokens.get(*pos)? != ")" {
            args.push(self.parse_at(tokens, pos, fuel - 1)?);
        }
        *pos += 1;
        self.constructed(&name, args)
    }
}

/// The tokens of a printed value: parentheses, and atoms (a `|quoted|`
/// symbol or a `"string"` literal is one atom, spaces included).
fn tokens(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut word = String::new();
    let mut quote: Option<char> = None;
    // Whether the previous character, inside a `|quoted|` symbol, is the `\`
    // of a `\|` or `\\` escape.
    let mut escaped = false;
    for c in text.chars() {
        match (quote, c) {
            (Some(q), c) => {
                word.push(c);
                if escaped {
                    escaped = false;
                } else if q == '|' && c == '\\' {
                    escaped = true;
                } else if c == q {
                    quote = None;
                }
            }
            (None, '|' | '"') => {
                word.push(c);
                quote = Some(c);
            }
            (None, '(' | ')') => {
                if !word.is_empty() {
                    tokens.push(std::mem::take(&mut word));
                }
                tokens.push(c.to_string());
            }
            (None, c) if c.is_whitespace() => {
                if !word.is_empty() {
                    tokens.push(std::mem::take(&mut word));
                }
            }
            (None, c) => word.push(c),
        }
    }
    if !word.is_empty() {
        tokens.push(word);
    }
    tokens
}

/// Tokens back as one canonical text: single spaces between atoms, none
/// inside parentheses.
fn normalized(tokens: &[String]) -> String {
    let mut out = String::new();
    for t in tokens {
        if t != ")" && !out.is_empty() && !out.ends_with('(') {
            out.push(' ');
        }
        out.push_str(t);
    }
    out
}

/// A numeral, decimal, bit-vector or string literal.
fn scalar_literal(token: &str) -> bool {
    token.starts_with(|c: char| c.is_ascii_digit())
        || token.starts_with('#')
        || token.starts_with('"')
}

/// The head of a parenthesized scalar literal: a negative or rational
/// number, or an indexed bit-vector literal.
fn scalar_head(head: &str, next: Option<&String>) -> bool {
    match head {
        "-" | "/" => true,
        "_" => next.is_some_and(|n| n.starts_with("bv")),
        _ => false,
    }
}
