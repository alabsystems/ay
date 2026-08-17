// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Faithful surface-term matchers and bit-vector/array reconstruction.

use super::*;
use ay_frontend::command::ParsedSort;

/// Match `(and P (not (= P' true)))` — the external-codegen dom-bounds contradiction
/// shape — returning the two `P` occurrences for the caller to prove
/// identical. The `true` must be the literal boolean constant in the SECOND
/// equality slot (exactly the shape the external-codegen renderer emits); any other
/// shape returns `None` (fail-closed).
pub(super) fn match_and_true_eq_contradiction(
    asrt: &FrontendTerm,
) -> Option<(&FrontendTerm, &FrontendTerm)> {
    let FrontendTerm::App(and_op, and_args) = asrt else {
        return None;
    };
    if and_op != "and" || and_args.len() != 2 {
        return None;
    }
    let FrontendTerm::App(not_op, not_args) = &and_args[1] else {
        return None;
    };
    if not_op != "not" || not_args.len() != 1 {
        return None;
    }
    let FrontendTerm::App(eq_op, eq_args) = &not_args[0] else {
        return None;
    };
    if eq_op != "=" || eq_args.len() != 2 {
        return None;
    }
    if !matches!(&eq_args[1], FrontendTerm::Const(FrontendConstant::True)) {
        return None;
    }
    Some((&and_args[0], &eq_args[0]))
}

/// Re-parse one RENDERED assertion back into the frontend AST. Wrapping the
/// text in `(assert …)` is the public parse entry point for a bare term;
/// anything that does not come back as exactly one `assert` fails closed.
pub(super) fn parse_rendered_assertion(rendered: &str) -> Option<FrontendTerm> {
    let commands = ay_frontend::parse(&format!("(assert {rendered})")).ok()?;
    let [Command::Assert(term)] = commands.as_slice() else {
        return None;
    };
    Some(term.clone())
}

/// Match `(and P (not (= X X')))` — a side condition conjoined with a
/// self-equality refutation — returning `(P, X, X')` for the caller to rebuild
/// and to prove `X`/`X'` identical. This is the external-codegen guarded-division
/// obligation family: the `(not (= b 0))` guard survives as `P` while the two
/// encoders of `a - (a / b) * b` coincide syntactically. Exactly two conjuncts,
/// the negated equality SECOND (the shape the obligation renderer emits); any
/// other shape returns `None` (fail-closed).
pub(super) fn match_and_self_eq_contradiction(
    asrt: &FrontendTerm,
) -> Option<(&FrontendTerm, &FrontendTerm, &FrontendTerm)> {
    let FrontendTerm::App(and_op, and_args) = asrt else {
        return None;
    };
    if and_op != "and" || and_args.len() != 2 {
        return None;
    }
    let (lhs, rhs) = match_eq_negation(&and_args[1])?;
    Some((&and_args[0], lhs, rhs))
}

/// Faithfully rebuild a Bool-sorted BITVECTOR ATOM — a BV comparison
/// (`bvult`/`bvule`/`bvugt`/`bvuge`/`bvslt`/`bvsle`/`bvsgt`/`bvsge`) or a BV
/// equality — whose sides go through the fold-guarded [`build_bv_pterm`].
/// Returns `None` (fail-closed) for any other op, a sort mismatch, or — the
/// soundness guard — an application `mk_app` FOLDED (so the rebuilt atom no
/// longer mirrors the surface term).
pub(super) fn build_bv_atom_pterm(terms: &mut TermStore, pt: &FrontendTerm) -> Option<TermId> {
    let FrontendTerm::App(op, args) = pt else {
        return None;
    };
    if args.len() != 2
        || !matches!(
            op.as_str(),
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" | "="
        )
    {
        return None;
    }
    let a = build_bv_pterm(terms, &args[0])?;
    let b = build_bv_pterm(terms, &args[1])?;
    if terms.sort(a) != terms.sort(b) || !matches!(terms.sort(a), Sort::BitVec(_)) {
        return None;
    }
    let atom = terms.mk_app(Symbol::named(op), vec![a, b], Sort::Bool);
    matches!(
        terms.get(atom),
        TermData::App(sym, ar) if sym.name() == op && ar.as_slice() == [a, b]
    )
    .then_some(atom)
}

/// Match an equality negation `(not (= L R))` (theory-agnostic), returning the
/// two sides `(L, R)` of the frontend AST. Returns `None` for any other shape.
pub(super) fn match_eq_negation(asrt: &FrontendTerm) -> Option<(&FrontendTerm, &FrontendTerm)> {
    let FrontendTerm::App(not_op, not_args) = asrt else {
        return None;
    };
    if not_op != "not" || not_args.len() != 1 {
        return None;
    }
    let FrontendTerm::App(eq_op, eq_args) = &not_args[0] else {
        return None;
    };
    if eq_op != "=" || eq_args.len() != 2 {
        return None;
    }
    Some((&eq_args[0], &eq_args[1]))
}

/// Faithfully translate a bitvector frontend term into a `TermId` — the same
/// translation the elaborator performs, MINUS the simplifying folds (it builds
/// through raw `mk_app`/`mk_bitvec`). Handles BV-sorted symbols (declared
/// consts), hex/binary literals, same-width unary/binary BV ops, and the
/// width-changing ops (`concat`, `(_ extract …)`, `(_ zero_extend k)`,
/// `(_ sign_extend k)`, `(_ rotate_left/right k)`, `(_ repeat k)`), recursively.
///
/// Returns `None` (fail-closed) for anything outside this fragment — a non-BV
/// symbol, a non-BV literal, a width-changing or unknown op, an arity mismatch,
/// or — the load-bearing soundness guard — an op application that `mk_app`
/// FOLDED away (so the rebuilt term is no longer the raw `(op args..)` and would
/// silently change the reconstructed assertion). Because every accepted node is a
/// structure-preserving rebuild, the resulting term faithfully represents the
/// surface assertion, so an `assume` built from it matches the real input.
pub(super) fn build_bv_pterm(terms: &mut TermStore, pt: &FrontendTerm) -> Option<TermId> {
    match pt {
        FrontendTerm::Symbol(s) => {
            // The surface snapshot stringifies a standalone indexed BV numeral
            // `(_ bvN W)` into a SYMBOL of that spelling (it is an identifier,
            // not an application). Recognize it before the declared-constant
            // lookup; built via the same `mk_bitvec` the elaborator uses, so
            // the rebuilt constant is definitionally the surface term.
            if let Some((value, width)) = parse_indexed_bv_numeral(s) {
                return Some(terms.mk_bitvec(value, width));
            }
            let id = terms.lookup(s)?;
            matches!(terms.sort(id), Sort::BitVec(_)).then_some(id)
        }
        FrontendTerm::Const(c) => build_bv_const(terms, c),
        FrontendTerm::IndexedApp(name, indices, args) if args.is_empty() => {
            build_bv_decimal_indexed(terms, name, indices)
        }
        FrontendTerm::App(op, args) if op == "concat" => build_bv_concat_pterm(terms, args),
        FrontendTerm::App(op, args) if op == "select" => build_bv_select_pterm(terms, args),
        // Same-width unary/binary BV ops.
        FrontendTerm::App(op, args) => {
            let arity = bv_samewidth_op_arity(op)?;
            if args.len() != arity {
                return None;
            }
            let arg_ids: Vec<TermId> = args
                .iter()
                .map(|a| build_bv_pterm(terms, a))
                .collect::<Option<_>>()?;
            let sort = terms.sort(arg_ids[0]).clone();
            if !matches!(sort, Sort::BitVec(_)) {
                return None;
            }
            let t = terms.mk_app(Symbol::named(op), arg_ids.clone(), sort);
            // Faithfulness guard: the rebuilt term must be the RAW application; if
            // `mk_app` folded it (e.g. `bvnot (bvnot x) → x`), it no longer mirrors
            // the surface term, so we decline rather than change the assertion.
            matches!(
                terms.get(t),
                TermData::App(sym, a) if sym.name() == op && a.as_slice() == arg_ids.as_slice()
            )
            .then_some(t)
        }
        // Indexed width-changing BV ops: `(_ extract hi lo)`, `(_ zero_extend k)`,
        // `(_ sign_extend k)`, `(_ rotate_left k)`, `(_ rotate_right k)`,
        // `(_ repeat k)`. The result width is computed to match the strict
        // checker's `eval_indexed_bv`; a mismatch only fails closed (the equality's
        // two sides get different sorts → declined), never unsound.
        FrontendTerm::IndexedApp(name, idx_strs, args) if args.len() == 1 => {
            let indices: Vec<u32> = idx_strs
                .iter()
                .map(|index| index.as_numeral()?.parse::<u32>().ok())
                .collect::<Option<_>>()?;
            let arg = build_bv_pterm(terms, &args[0])?;
            let src_width = terms.sort(arg).bitvec_width()?;
            let width = bv_indexed_result_width(name, &indices, src_width)?;
            let sym = Symbol::indexed(name, indices.clone());
            let t = terms.mk_app(sym, vec![arg], Sort::bitvec(width));
            matches!(
                terms.get(t),
                TermData::App(Symbol::Indexed(n, idx), ar)
                    if n == name && idx.as_slice() == indices.as_slice() && ar.as_slice() == [arg]
            )
            .then_some(t)
        }
        // Indexed BV NUMERAL `(_ bvN W)` — a nullary indexed identifier
        // denoting the width-`W` constant `N` (SMT-LIB 2.6 §3.5.1; the
        // external-codegen obligation renderer's literal form, e.g. `(_ bv1024 64)`).
        // Built via the same `mk_bitvec` the elaborator and `build_bv_const`
        // use, so the rebuilt constant is definitionally the surface term —
        // no fold guard needed on a literal. A malformed numeral or width
        // fails closed.
        FrontendTerm::IndexedApp(name, idx_strs, args)
            if args.is_empty() && idx_strs.len() == 1 && name.starts_with("bv") =>
        {
            let digits = &name[2..];
            if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
                return None;
            }
            let value = BigInt::parse_bytes(digits.as_bytes(), 10)?;
            // The width index must be a NUMERAL token specifically. `Index` is
            // deliberately token-kind-typed — the numeral `8` and the quoted
            // symbol `|8|` are distinct indices and must not collapse to the
            // same string — so match the variant rather than stringifying.
            let [FrontendIndex::Numeral(width_str)] = idx_strs.as_slice() else {
                return None;
            };
            let width = width_str.parse::<u32>().ok()?;
            if width == 0 {
                return None;
            }
            Some(terms.mk_bitvec(value, width))
        }
        _ => None,
    }
}

/// Translate the parser-level sort AST into the native sort, over exactly the
/// fragment the faithful rebuilds admit: `Bool`, `(_ BitVec W)`, and `(Array I
/// E)` over those. Fail-closed everywhere else, so an annotation this module
/// does not fully understand can never mint a wrong-sorted term (the callers
/// additionally re-check the produced sort against the terms they built).
fn parsed_core_sort(sort: &ParsedSort) -> Option<Sort> {
    match sort {
        ParsedSort::Simple(name) if name == "Bool" => Some(Sort::Bool),
        ParsedSort::Indexed(name, indices) if name == "BitVec" => {
            let [FrontendIndex::Numeral(width)] = indices.as_slice() else {
                return None;
            };
            let width = width.parse::<u32>().ok()?;
            (width > 0).then(|| Sort::bitvec(width))
        }
        ParsedSort::Parameterized(name, params) if name == "Array" && params.len() == 2 => Some(
            Sort::array(parsed_core_sort(&params[0])?, parsed_core_sort(&params[1])?),
        ),
        _ => None,
    }
}

/// Faithfully rebuild an ARRAY-sorted frontend term — the elaborator's
/// translation MINUS the simplifying folds. This is the load-bearing
/// difference from `mk_select`/`mk_store`: those apply read-over-write,
/// read-over-const-array, store-over-store and sort-store rewrites, so an
/// elaborated `(select (store a i v) i)` is no longer a `select` at all. A
/// reconstructed `assume` has to print like the PROBLEM FILE, so every node
/// here is interned raw through `mk_app` (which does not rewrite) and then
/// re-read to confirm it stayed the raw `(op args..)`.
///
/// Handles array-sorted declared symbols, `(store a i v)`, and the constant
/// array `((as const (Array I E)) v)`. `build_element` is the caller's own
/// fold-guarded builder for the index and value positions, threaded through so
/// the BV-only ([`build_bv_pterm`]) and boolean-layer ([`build_qfbv_pterm`])
/// callers each keep their exact fragment.
///
/// Returns `None` (fail-closed) for any other shape, for an index/value whose
/// sort disagrees with the array's own index/element sort, or for a node the
/// term store did not intern raw.
fn build_array_pterm(
    terms: &mut TermStore,
    pt: &FrontendTerm,
    build_element: fn(&mut TermStore, &FrontendTerm) -> Option<TermId>,
) -> Option<TermId> {
    match pt {
        FrontendTerm::Symbol(s) => {
            let id = terms.lookup(s)?;
            matches!(terms.sort(id), Sort::Array(_)).then_some(id)
        }
        FrontendTerm::App(op, args) if op == "store" && args.len() == 3 => {
            let array = build_array_pterm(terms, &args[0], build_element)?;
            let Sort::Array(array_sort) = terms.sort(array).clone() else {
                return None;
            };
            let index = build_element(terms, &args[1])?;
            let value = build_element(terms, &args[2])?;
            if *terms.sort(index) != array_sort.index_sort
                || *terms.sort(value) != array_sort.element_sort
            {
                return None;
            }
            let t = terms.mk_app(
                Symbol::named("store"),
                vec![array, index, value],
                Sort::Array(array_sort),
            );
            matches!(
                terms.get(t),
                TermData::App(sym, a)
                    if sym.name() == "store" && a.as_slice() == [array, index, value]
            )
            .then_some(t)
        }
        // `((as const (Array I E)) v)` — the SMT-LIB constant array. AY stores
        // it as the internal `(const-array v)` application; the sort comes from
        // the source annotation, not from inference, and the value's own sort
        // must match the annotated element sort or this fails closed.
        FrontendTerm::QualifiedApp(identifier, sort, args)
            if identifier.as_symbol() == Some("const") && args.len() == 1 =>
        {
            let Some(Sort::Array(array_sort)) = parsed_core_sort(sort) else {
                return None;
            };
            let value = build_element(terms, &args[0])?;
            if *terms.sort(value) != array_sort.element_sort {
                return None;
            }
            let t = terms.mk_const_array(array_sort.index_sort.clone(), value);
            (matches!(
                terms.get(t),
                TermData::App(sym, a) if sym.name() == "const-array" && a.as_slice() == [value]
            ) && *terms.sort(t) == Sort::Array(array_sort))
            .then_some(t)
        }
        _ => None,
    }
}

/// Faithfully rebuild an array read `(select a i)` — the element-sorted bridge
/// out of [`build_array_pterm`]. Raw-interned for the same reason: `mk_select`
/// would collapse a read over a matching write straight to the stored value,
/// which no longer prints like the problem file. Fail-closed on a non-array
/// first argument, an index whose sort disagrees with the array's, or a node
/// the term store did not intern raw.
fn build_select_pterm(
    terms: &mut TermStore,
    array_pt: &FrontendTerm,
    index_pt: &FrontendTerm,
    build_element: fn(&mut TermStore, &FrontendTerm) -> Option<TermId>,
) -> Option<TermId> {
    let array = build_array_pterm(terms, array_pt, build_element)?;
    let Sort::Array(array_sort) = terms.sort(array).clone() else {
        return None;
    };
    let index = build_element(terms, index_pt)?;
    if *terms.sort(index) != array_sort.index_sort {
        return None;
    }
    let t = terms.mk_app(
        Symbol::named("select"),
        vec![array, index],
        array_sort.element_sort.clone(),
    );
    matches!(
        terms.get(t),
        TermData::App(sym, a) if sym.name() == "select" && a.as_slice() == [array, index]
    )
    .then_some(t)
}

/// Parse the SMT-LIB indexed BV numeral spelling `(_ bvN W)` (SMT-LIB 2.6
/// §3.5.1) into `(N, W)`. Whitespace-tolerant between the three tokens;
/// anything else — malformed digits, a zero width, extra tokens — returns
/// `None` (fail-closed).
fn parse_indexed_bv_numeral(s: &str) -> Option<(BigInt, u32)> {
    let inner = s.trim().strip_prefix('(')?.strip_suffix(')')?;
    let mut tokens = inner.split_whitespace();
    if tokens.next()? != "_" {
        return None;
    }
    let bv_name = tokens.next()?;
    let width_str = tokens.next()?;
    if tokens.next().is_some() {
        return None;
    }
    let digits = bv_name.strip_prefix("bv")?;
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let value = BigInt::parse_bytes(digits.as_bytes(), 10)?;
    let width = width_str.parse::<u32>().ok()?;
    if width == 0 {
        return None;
    }
    Some((value, width))
}

/// Build a bitvector constant term from a hex/binary frontend literal, mirroring
/// the elaborator's parsing exactly (`#xAB` → width `len*4`, `#b101` → width
/// `len`). Returns `None` for non-bitvector constants.
pub(super) fn build_bv_const(terms: &mut TermStore, c: &FrontendConstant) -> Option<TermId> {
    match c {
        FrontendConstant::Hexadecimal(s) => {
            let hex = s.trim_start_matches("#x");
            let value = BigInt::parse_bytes(hex.as_bytes(), 16)?;
            let width = (hex.len() * 4) as u32;
            Some(terms.mk_bitvec(value, width))
        }
        FrontendConstant::Binary(s) => {
            let bin = s.trim_start_matches("#b");
            let value = BigInt::parse_bytes(bin.as_bytes(), 2)?;
            let width = bin.len() as u32;
            Some(terms.mk_bitvec(value, width))
        }
        _ => None,
    }
}

/// Rebuild width-changing `concat`, with the result width equal to the operand
/// width sum. Malformed arities and non-bit-vector operands fail closed.
fn build_bv_concat_pterm(terms: &mut TermStore, args: &[FrontendTerm]) -> Option<TermId> {
    let [a, b] = args else {
        return None;
    };
    let a = build_bv_pterm(terms, a)?;
    let b = build_bv_pterm(terms, b)?;
    let width = terms
        .sort(a)
        .bitvec_width()?
        .checked_add(terms.sort(b).bitvec_width()?)?;
    let t = terms.mk_app(Symbol::named("concat"), vec![a, b], Sort::bitvec(width));
    matches!(
        terms.get(t),
        TermData::App(sym, ar) if sym.name() == "concat" && ar.as_slice() == [a, b]
    )
    .then_some(t)
}

/// Rebuild an array read whose result must be bit-vector sorted.
fn build_bv_select_pterm(terms: &mut TermStore, args: &[FrontendTerm]) -> Option<TermId> {
    let [array, index] = args else {
        return None;
    };
    let t = build_select_pterm(terms, array, index, build_bv_pterm)?;
    matches!(terms.sort(t), Sort::BitVec(_)).then_some(t)
}

/// Rebuild a QF_BV `ite`, retaining its exact raw application shape.
pub(super) fn build_qfbv_ite_pterm(terms: &mut TermStore, args: &[FrontendTerm]) -> Option<TermId> {
    let [condition, then_term, else_term] = args else {
        return None;
    };
    let c = build_qfbv_pterm(terms, condition)?;
    let x = build_qfbv_pterm(terms, then_term)?;
    let y = build_qfbv_pterm(terms, else_term)?;
    if !matches!(terms.sort(c), Sort::Bool)
        || terms.sort(x) != terms.sort(y)
        || !matches!(terms.sort(x), Sort::Bool | Sort::BitVec(_))
    {
        return None;
    }
    let t = terms.mk_ite_raw(c, x, y);
    matches!(terms.get(t), TermData::Ite(tc, tx, ty) if (*tc, *tx, *ty) == (c, x, y)).then_some(t)
}

/// Rebuild an array read whose result may be boolean or bit-vector sorted.
pub(super) fn build_qfbv_select_pterm(
    terms: &mut TermStore,
    args: &[FrontendTerm],
) -> Option<TermId> {
    let [array, index] = args else {
        return None;
    };
    let t = build_select_pterm(terms, array, index, build_qfbv_pterm)?;
    matches!(terms.sort(t), Sort::Bool | Sort::BitVec(_)).then_some(t)
}
