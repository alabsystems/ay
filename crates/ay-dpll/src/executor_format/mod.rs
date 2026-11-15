// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Formatting helpers for SMT-LIB output.
//!
//! These helpers are shared between the `Executor` and combined theory solvers
//! for rendering numeric model values and sorts.

use ay_core::render_admission::{self as output, Owner};
use ay_core::term::Symbol;
use ay_core::{quote_symbol, Sort};
use num_rational::BigRational;

mod admission;

/// Format a `Sort` as an SMT-LIB sort string.
pub(crate) fn format_sort(sort: &Sort) -> String {
    match sort {
        Sort::Bool => "Bool".to_string(),
        Sort::Int => "Int".to_string(),
        Sort::Real => "Real".to_string(),
        Sort::Complex => "Complex".to_string(),
        Sort::FiniteField(field) => format!("(_ FiniteField {})", field.modulus()),
        Sort::String => "String".to_string(),
        Sort::RegLan => "RegLan".to_string(),
        Sort::BitVec(bv) => format!("(_ BitVec {})", bv.width),
        Sort::FloatingPoint(eb, sb) => format!("(_ FloatingPoint {eb} {sb})"),
        Sort::Array(arr) => format!(
            "(Array {} {})",
            format_sort(&arr.index_sort),
            format_sort(&arr.element_sort)
        ),
        Sort::Uninterpreted(name) => quote_symbol(name),
        Sort::Datatype(dt) => quote_symbol(&dt.name),
        Sort::Seq(elem) => format!("(Seq {})", format_sort(elem)),
        // All current Sort variants handled above (#5692).
        // Wildcard covers future variants from #[non_exhaustive].
        other => unreachable!("unhandled Sort variant in format_sort(): {other:?}"),
    }
}

/// Format an engine sort at an SMT-LIB boundary using the owning frontend
/// context's sticky nominal-carrier metadata.
pub(crate) fn format_sort_surface(ctx: &ay_frontend::Context, sort: &Sort) -> String {
    ctx.format_sort_surface(sort)
        .unwrap_or_else(|| format_sort(sort))
}

pub(crate) fn format_sort_surface_owned(
    ctx: &ay_frontend::Context,
    sort: &Sort,
    owner: Owner<'_>,
) -> String {
    if let Some(owner) = owner {
        match ctx.format_sort_surface_admitted(sort, owner) {
            Some(value) => value,
            None => {
                output::invalid(Some(owner));
                String::new()
            }
        }
    } else {
        format_sort_surface(ctx, sort)
    }
}

/// Format a `Symbol` (function/constant name) for SMT-LIB output.
pub(crate) fn format_symbol(sym: &Symbol) -> String {
    format_symbol_owned(sym, None)
}

pub(crate) fn format_symbol_owned(sym: &Symbol, owner: Owner<'_>) -> String {
    match sym {
        Symbol::Named(name) => output::quote(owner, name),
        Symbol::Indexed(name, indices) => {
            let mut indices_str = Vec::new();
            if !output::reserve(&mut indices_str, indices.len(), owner) {
                return String::new();
            }
            for value in indices {
                indices_str.push(output::format(owner, format_args!("{value}")));
            }
            let name = output::quote(owner, name);
            let joined = output::join(owner, &indices_str, " ");
            output::format(owner, format_args!("(_ {name} {joined})"))
        }
        // All current Symbol variants handled above (#5692).
        // Wildcard covers future variants from #[non_exhaustive].
        other => unreachable!("unhandled Symbol variant in format_symbol(): {other:?}"),
    }
}

/// Format a model atom for SMT-LIB output.
///
/// An ABSTRACT value of an uninterpreted sort (an internal `@Sort!n`
/// representative) is sort-ascribed: `(as @U!0 U)`. The bare token is not a
/// declared constant, so SMT-LIB model validators reject it as an unbound
/// identifier; the `as`-cast form is the standard abstract-value syntax
/// (cvc5-style) and validates (#mv-abstract-value-ascription). Constructor
/// names and user-declared element names print bare as before.
pub(crate) fn format_model_atom(sort: &Sort, value: &str) -> String {
    match sort {
        Sort::Uninterpreted(_) | Sort::Datatype(_) => {
            if value.starts_with('@') {
                format!("(as {} {})", quote_symbol(value), format_sort(sort))
            } else {
                quote_symbol(value)
            }
        }
        _ => value.to_string(),
    }
}

/// Context-aware model-atom formatter for public SMT-LIB output.
pub(crate) fn format_model_atom_surface(
    ctx: &ay_frontend::Context,
    sort: &Sort,
    value: &str,
) -> String {
    match sort {
        Sort::Uninterpreted(_) | Sort::Datatype(_) => {
            if value.starts_with('@') {
                format!(
                    "(as {} {})",
                    quote_symbol(value),
                    format_sort_surface(ctx, sort)
                )
            } else {
                quote_symbol(value)
            }
        }
        _ => value.to_string(),
    }
}

/// Strip a sort ascription from an INTERNAL abstract-atom spelling:
/// `(as @Sort!n S)` -> `@Sort!n`, including the PIPE-QUOTED printing
/// `(as |@Sort!n| |S|)` -> `@Sort!n`.
///
/// [`format_model_atom`] sort-ascribes abstract `@`-atoms for PRINTED models
/// (#mv-abstract-value-ascription) — external validators need the `as`-cast.
/// The internal model dialect (EUF `term_values`, `ArrayInterpretation`
/// stores/defaults, `eval_value_to_model_atom`) uses the BARE token, and every
/// internal consumer compares these strings for value identity. A printed
/// spelling leaking into internal state makes ONE value look like TWO (a
/// phantom array cell that falsifies a valid witness at the independent gate —
/// QF_AX storeinv fail-close). This is the inverse boundary map; it returns
/// `None` for anything that is not exactly an ascribed `@`-atom, so datatype
/// constructor ascriptions like `(as nil (List Int))` are never touched.
///
/// PIPE-QUOTING (#closure-capture-uninterp-range): when the sort NAME needs
/// quoting (`quote_symbol` — e.g. the verification-consumer `&mut` carrier sort
/// `__verification_consumer_mutref::int`, whose `::` is outside the simple-symbol
/// alphabet), the printer emits `(as |@__verification_consumer_mutref::int!0|
/// |__verification_consumer_mutref::int|)`. The former token check (`starts_with('@')`)
/// saw the leading `|` and bailed, so the quoted spelling escaped
/// canonicalization: a datatype field holding such an element compared
/// UNEQUAL to the same element's bare leaf value, and the independent gate
/// falsely refuted asserted capture-projection equalities (closures/09
/// `bx == closure_capture_1(f)` fail-closed Sat -> Unknown). Unquote the
/// token and return the BARE spelling — the internal dialect never stores
/// the pipes. Sound: `|@S!n|` in the printer's own output denotes exactly
/// the element `@S!n`, so unquoting can only merge true identities, never
/// conflate distinct elements.
pub(crate) fn strip_abstract_atom_ascription(s: &str) -> Option<&str> {
    let inner = s.trim().strip_prefix("(as ")?.strip_suffix(')')?;
    let inner = inner.trim_start();
    // Take the leading atom: a `|…|` quoted symbol (which may contain
    // whitespace) or a run up to the next whitespace.
    let (token, rest) = if let Some(quoted) = inner.strip_prefix('|') {
        let end = quoted.find('|')?;
        (&quoted[..end], &quoted[end + 1..])
    } else {
        let end = inner.find(char::is_whitespace).unwrap_or(inner.len());
        inner.split_at(end)
    };
    if !token.starts_with('@') {
        return None;
    }
    // Require a sort part after the token (otherwise the shape is not an
    // `as`-cast) and no nested parens inside the token itself.
    let rest = rest.trim();
    if rest.is_empty() || token.contains('(') {
        return None;
    }
    Some(token)
}

/// Canonicalize a model-atom string to the INTERNAL bare dialect: ascribed
/// abstract atoms lose their `(as .. ..)` wrapper, everything else is
/// returned unchanged. See [`strip_abstract_atom_ascription`].
pub(crate) fn canonical_internal_atom(s: &str) -> String {
    match strip_abstract_atom_ascription(s) {
        Some(token) => token.to_string(),
        None => s.to_string(),
    }
}

/// Binding-aware field literal shared by assertions, values and model defaults.
/// At most 1024 name probes share the native field slice's bounded work posture.
/// Refusal is explicit, never an approximate/rebound residue.
pub(crate) fn format_field_literal_surface(
    ctx: &ay_frontend::Context,
    value: u32,
    field: ay_core::FiniteFieldSort,
    poll: impl FnMut() -> bool,
) -> Option<String> {
    format_field_literal_in_namespace(ctx, value, field, poll, |_| false)
}

pub(crate) fn format_field_literal_in_namespace(
    ctx: &ay_frontend::Context,
    value: u32,
    field: ay_core::FiniteFieldSort,
    mut poll: impl FnMut() -> bool,
    mut occupied: impl FnMut(&str) -> bool,
) -> Option<String> {
    format_field_literal_owned(ctx, value, field, None, &mut poll, &mut occupied)
}

pub(crate) fn format_field_literal_owned(
    ctx: &ay_frontend::Context,
    value: u32,
    field: ay_core::FiniteFieldSort,
    owner: Owner<'_>,
    mut poll: impl FnMut() -> bool,
    mut occupied: impl FnMut(&str) -> bool,
) -> Option<String> {
    if !poll() {
        return None;
    }
    if value >= field.modulus() {
        return None;
    }
    let canonical = output::format(owner, format_args!("ff{value}"));
    if !output::pay(owner, canonical.len(), 0) {
        return None;
    }
    if !ctx.has_symbol_binding(&canonical) && !occupied(&canonical) {
        let result = output::format(
            owner,
            format_args!("(as ff{value} (_ FiniteField {}))", field.modulus()),
        );
        return output::pay(owner, 0, 0).then_some(result);
    }
    let mut representative = u64::from(value);
    for _ in 0..1024 {
        if !poll() {
            return None;
        }
        let name = output::format(
            owner,
            format_args!("#f{representative}m{}", field.modulus()),
        );
        if !output::pay(owner, name.len(), 0) {
            return None;
        }
        if !ctx.has_symbol_binding(&name) && !occupied(&name) {
            return Some(name);
        }
        representative = representative.checked_add(u64::from(field.modulus()))?;
    }
    None
}

/// Canonical default value of a sort at a public SMT-LIB boundary.
/// Nominal sorts require their owning context so private carrier identities
/// never leak. This is only for genuinely unconstrained model slots, never a
/// fallback for failed evaluation.
pub(crate) fn format_default_value_surface(
    ctx: &ay_frontend::Context,
    sort: &Sort,
) -> Option<String> {
    format_default_value_surface_with_poll(ctx, sort, &mut || true)
}

pub(crate) fn format_default_value_surface_with_poll(
    ctx: &ay_frontend::Context,
    sort: &Sort,
    poll: &mut impl FnMut() -> bool,
) -> Option<String> {
    if !poll() {
        return None;
    }
    Some(match sort {
        Sort::Bool => "false".to_string(),
        Sort::Int => "0".to_string(),
        Sort::Real => "0.0".to_string(),
        Sort::Complex => "(complex.make 0.0 0.0)".to_string(),
        Sort::FiniteField(field) => return format_field_literal_surface(ctx, 0, *field, poll),
        Sort::String => "\"\"".to_string(),
        Sort::RegLan => "re.none".to_string(),
        Sort::BitVec(width) => format_bitvec(&num_bigint::BigInt::from(0), width.width),
        Sort::FloatingPoint(exponent, significand) => {
            format!("(_ +zero {exponent} {significand})")
        }
        Sort::Array(array) => format!(
            "((as const {}) {})",
            format_sort_surface(ctx, sort),
            format_default_value_surface_with_poll(ctx, &array.element_sort, poll)?
        ),
        Sort::Uninterpreted(name) if name == "RoundingMode" => {
            format_model_atom_surface(ctx, sort, "roundNearestTiesToEven")
        }
        Sort::Uninterpreted(name) => format_model_atom_surface(ctx, sort, &format!("@{name}!0")),
        Sort::Datatype(datatype) => {
            format_model_atom_surface(ctx, sort, &format!("@{}!0", datatype.name))
        }
        Sort::Seq(_) => format!("(as seq.empty {})", format_sort_surface(ctx, sort)),
        other => {
            unreachable!("unhandled Sort variant in format_default_value_surface(): {other:?}")
        }
    })
}

/// Format a `BigRational` as an SMT-LIB Real value.
pub(crate) fn format_rational(val: &BigRational) -> String {
    format_rational_owned(val, None)
}

pub(crate) fn format_rational_owned(val: &BigRational, owner: Owner<'_>) -> String {
    if !output::pay(owner, 1, 0) {
        return String::new();
    }
    if owner.is_some() && val.denom().sign() != num_bigint::Sign::Plus {
        output::invalid(owner);
        return String::new();
    }
    let Some(numer) = admission::decimal(val.numer(), owner) else {
        return String::new();
    };
    let negative = val.numer().sign() == num_bigint::Sign::Minus;
    if val.is_integer() {
        if negative {
            output::format(owner, format_args!("(- {numer}.0)"))
        } else {
            output::format(owner, format_args!("{numer}.0"))
        }
    } else {
        let Some(mut denom) = admission::decimal(val.denom(), owner) else {
            return String::new();
        };
        // Preserve the legacy representation even for a caller's raw negative
        // denominator; admitted producer data above requires a positive one.
        if val.denom().sign() == num_bigint::Sign::Minus {
            denom = output::format(owner, format_args!("-{denom}"));
        }
        if negative {
            output::format(owner, format_args!("(- (/ {numer} {denom}))"))
        } else {
            output::format(owner, format_args!("(/ {numer} {denom})"))
        }
    }
}

/// Format a `BigRational` as a USER-FACING SMT-LIB Real value, z3-exactly:
/// `5.0`, `(- 5.0)`, `(/ 7.0 2.0)`, `(- (/ 7.0 2.0))`.
///
/// This is the stdout-boundary twin of [`format_rational`]: the integer arm
/// is identical, the fraction arm uses z3's decimal-literal components
/// (`(/ n.0 d.0)`) instead of `(/ n d)`. [`format_rational`] must stay
/// byte-stable — its output is stored in `euf_model.term_values`
/// (combined_solvers/models.rs), string-compared against
/// `eval_value_to_model_atom` output, and re-parsed by `parse_real_string` —
/// so only the user-facing printers route through this function (#real-fmt).
pub(crate) fn format_real(val: &BigRational) -> String {
    if val.is_integer() {
        // Integer value: format as decimal
        let numer = val.numer();
        if numer.sign() == num_bigint::Sign::Minus {
            format!("(- {}.0)", numer.magnitude())
        } else {
            format!("{numer}.0")
        }
    } else {
        // Fractional value: format as (/ num.0 denom.0), sign hoisted out
        let numer = val.numer();
        let denom = val.denom();
        if numer.sign() == num_bigint::Sign::Minus {
            format!("(- (/ {}.0 {}.0))", numer.magnitude(), denom)
        } else {
            format!("(/ {numer}.0 {denom}.0)")
        }
    }
}

/// Format a `BigInt` as an SMT-LIB Int value.
pub(crate) fn format_bigint(val: &num_bigint::BigInt) -> String {
    format_bigint_owned(val, None)
}

pub(crate) fn format_bigint_owned(val: &num_bigint::BigInt, owner: Owner<'_>) -> String {
    use num_bigint::Sign;
    let Some(digits) = admission::decimal(val, owner) else {
        return String::new();
    };
    match val.sign() {
        Sign::Minus => output::format(owner, format_args!("(- {digits})")),
        Sign::NoSign | Sign::Plus => digits,
    }
}

/// Render a borrowed integer through the existing counted radix kernel and
/// UTF-8 sink. The caller supplies its original owner; this creates no grant.
pub fn format_bigint_with_admission(
    value: &num_bigint::BigInt,
    owner: &dyn ay_core::term::TermConstructionAdmission,
) -> Result<String, ay_core::original_query::CountedAdmissionError> {
    let text = format_bigint_owned(value, Some(owner));
    owner.check()?;
    Ok(text)
}

/// The same original-owned native formatter for an exact rational value.
pub fn format_rational_with_admission(
    value: &BigRational,
    owner: &dyn ay_core::term::TermConstructionAdmission,
) -> Result<String, ay_core::original_query::CountedAdmissionError> {
    let text = format_rational_owned(value, Some(owner));
    owner.check()?;
    Ok(text)
}

/// The canonical width-preserving BV printer with its original owner.
pub fn format_bitvec_with_admission(
    value: &num_bigint::BigInt,
    width: u32,
    owner: &dyn ay_core::term::TermConstructionAdmission,
) -> Result<String, ay_core::original_query::CountedAdmissionError> {
    let text = format_bitvec_owned(value, width, Some(owner));
    owner.check()?;
    Ok(text)
}

/// Format a `BigInt` as an SMT-LIB BitVec literal.
///
/// This is the single canonical BV-numeral printer for the whole workspace:
/// the CLI model/`get-value` path, the executor's term printer (which backs the
/// Z3-compatible C API's `Z3_ast_to_string`), and every model renderer must go
/// through it. A BV numeral's *printed form encodes its sort*, so getting this
/// wrong silently changes the width of the term that a consumer reparses.
///
/// SMT-LIB 2.6 hex literals (`#x...`) denote exactly 4 bits per digit, so they
/// are well-formed only when the width is a multiple of 4. Every other width
/// must print in binary (`#b...`), which denotes exactly 1 bit per digit. This
/// matches z3 5.0.0 exactly, at every width (measured: `BV1/1 -> #b1`,
/// `BV5/17 -> #b10001`, `BV65/1 -> #b0..01`, `BV8/255 -> #xff`).
///
/// The indexed `(_ bv<value> <width>)` form is deliberately NOT used: it is
/// legal SMT-LIB but z3 never emits it, so it would be a gratuitous parity
/// break. (#1793)
pub fn format_bitvec(val: &num_bigint::BigInt, width: u32) -> String {
    format_bitvec_owned(val, width, None)
}

pub(crate) fn format_bitvec_owned(
    val: &num_bigint::BigInt,
    width: u32,
    owner: Owner<'_>,
) -> String {
    use std::borrow::Cow;
    let canonical = val.sign() != num_bigint::Sign::Minus && val.bits() <= u64::from(width);
    if owner.is_some() && (!canonical || width == 0) {
        output::invalid(owner);
        return String::new();
    }
    // Reduce into [0, 2^width) so negative inputs print their two's-complement
    // bit pattern. `&` with the mask is only correct for non-negative values in
    // sign-magnitude BigInt, so use a true modular reduction.
    let unsigned_val = if canonical {
        Cow::Borrowed(val)
    } else {
        let modulus = num_bigint::BigInt::from(1u8) << width;
        Cow::Owned(((val % &modulus) + &modulus) % &modulus)
    };

    // Hex only when one hex digit maps to a whole number of bits.
    if width.is_multiple_of(4) {
        let hex_digits = (width / 4) as usize;
        if !admission::bitwise(unsigned_val.bits(), 4, owner) {
            return String::new();
        }
        let hex_str = unsigned_val.to_str_radix(16);
        let mut result = output::Buffer::new(owner);
        if !result.push("#x")
            || !result.repeat('0', hex_digits.saturating_sub(hex_str.len()))
            || !result.push(&hex_str)
        {
            return String::new();
        }
        return result.finish();
    }

    // Every other width: binary, one digit per bit, zero-padded to the width.
    if !admission::bitwise(unsigned_val.bits(), 1, owner) {
        return String::new();
    }
    let bin_str = unsigned_val.to_str_radix(2);
    let bin_digits = width as usize;
    let mut result = output::Buffer::new(owner);
    if !result.push("#b")
        || !result.repeat('0', bin_digits.saturating_sub(bin_str.len()))
        || !result.push(&bin_str)
    {
        return String::new();
    }
    result.finish()
}

pub(crate) mod array_cell;

#[cfg(test)]
mod tests;
