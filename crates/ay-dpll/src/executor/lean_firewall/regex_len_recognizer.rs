// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// `k ∣ n` with Lean's `Nat.dvd` convention: `0 ∣ n` holds only for `n = 0`.
///
/// `u64::is_multiple_of` already agrees at `k = 0` (it answers `n == 0` rather
/// than dividing), which is the case the emitter relies on for a regex whose
/// every member is the empty string.
fn divides(k: u64, n: u64) -> bool {
    n.is_multiple_of(k)
}

const fn gcd(a: u64, b: u64) -> u64 {
    let (mut a, mut b) = (a, b);
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// The asserted bound on `str.len X`, normalised to the three shapes the Lean
/// corollaries take. `<` and `>` are normalised to `Le`/`Ge` by the `± 1` that
/// is exact over the non-negative integers `str.len` ranges over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LenPin {
    /// `str.len X = c`.
    Eq(u64),
    /// `str.len X ≤ b`.
    Le(u64),
    /// `b ≤ str.len X`.
    Ge(u64),
}

/// Which verified conflict corollary closes this (regex, pin) pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RegexLenTier {
    /// `regex_len_mod_conflict` with modulus `k`.
    Mod(u64),
    /// `regex_len_min_conflict` (equality pin below `minLen`).
    Min,
    /// `regex_len_max_conflict` with bound `n` (equality pin above `maxLen`).
    Max(u64),
    /// `regex_len_min_conflict_le` (upper-bound pin below `minLen`).
    MinLe,
    /// `regex_len_max_conflict_ge` with bound `n` (lower-bound pin above it).
    MaxGe(u64),
}

/// Pick the verified corollary that refutes `(re, pin)`, or `None`.
///
/// NOTE the deliberate absence of a modular tier for the inequality pins:
/// `k ∣ len s` is compatible with every open interval that contains a multiple
/// of `k`, and `AySoundness.RegexThy` proves no inequality form of
/// `mem_len_dvd`. Firing `Mod` on an inequality would be unsound.
fn regex_len_tier(re: &ReAst, pin: LenPin) -> Option<RegexLenTier> {
    match pin {
        LenPin::Eq(c) => {
            if re.min_len()? > c {
                return Some(RegexLenTier::Min);
            }
            if let Some(n) = re.max_len() {
                if n < c {
                    return Some(RegexLenTier::Max(n));
                }
            }
            let k = re.modulus();
            (re.kdvd(k) && !divides(k, c)).then_some(RegexLenTier::Mod(k))
        }
        LenPin::Le(b) => (re.min_len()? > b).then_some(RegexLenTier::MinLe),
        LenPin::Ge(b) => re.max_len().filter(|n| *n < b).map(RegexLenTier::MaxGe),
    }
}

/// Decode a `str.to_re` literal into SMT-LIB code points.
///
/// The literal arrives ALREADY decoded: `ay_frontend::sexp` runs
/// `ay_core::unescape_string_contents` (exact 1-5 hex digits, value ≤ 0x2FFFF,
/// non-escapes literal, surrogates rejected) on every string token, and fails
/// the whole parse on a literal it cannot represent. So this cannot disagree
/// with the solver's own reading of the literal — there is no second decoder
/// here to get out of step. The only remaining check is that every code point
/// is inside the SMT-LIB alphabet the `Re` model describes.
fn regex_literal_code_points(lit: &str) -> Option<Vec<u32>> {
    let mut out = Vec::new();
    for ch in lit.chars() {
        let cp = ch as u32;
        if cp > SMTLIB_MAX_CODE_POINT || out.len() >= REGEX_LEN_MAX_LITERAL_CHARS {
            return None;
        }
        out.push(cp);
    }
    Some(out)
}

/// Parse an SMT-LIB regular expression into [`ReAst`], or `None` to decline.
///
/// Declines (never guesses) on: `re.comp` / `re.diff` / `re.loop` / `re.^`
/// (see [`REGEX_LEN_DECLINED_OPS`]), any operator not in
/// [`REGEX_LEN_INTERPRETED_OPS`], any non-literal `str.to_re` operand, and any
/// nesting past `depth`.
fn parse_regex_ast(t: &PTerm, depth: u32) -> Option<ReAst> {
    if depth == 0 {
        return None;
    }
    match t {
        // Nullary regex constants also reach the parser as bare symbols. They
        // are reserved names, so a bare `re.none` cannot be a user constant.
        PTerm::Symbol(name) => nullary_regex(name),
        PTerm::App(op, args) => {
            if REGEX_LEN_DECLINED_OPS.iter().any(|(name, _)| name == op) {
                return None;
            }
            if args.is_empty() {
                return nullary_regex(op);
            }
            match op.as_str() {
                "str.to_re" | "str.to.re" if args.len() == 1 => match &args[0] {
                    PTerm::Const(PConst::String(lit)) => {
                        regex_literal_code_points(lit).map(ReAst::Lit)
                    }
                    _ => None,
                },
                // n-ary, min arity 1 — exactly the frontend's arity rule. Fold
                // RIGHT so `(re.++ a b c)` is `cat a (cat b c)`; both foldings
                // denote the same language and `Re` is binary.
                "re.++" | "re.union" | "re.inter" => {
                    let mut acc = parse_regex_ast(args.last()?, depth - 1)?;
                    for arg in args[..args.len() - 1].iter().rev() {
                        let head = parse_regex_ast(arg, depth - 1)?;
                        acc = bounded(match op.as_str() {
                            "re.++" => ReAst::Cat(Box::new(head), Box::new(acc)),
                            "re.union" => ReAst::Union(Box::new(head), Box::new(acc)),
                            _ => ReAst::Inter(Box::new(head), Box::new(acc)),
                        })?;
                    }
                    Some(acc)
                }
                "re.*" if args.len() == 1 => {
                    bounded(ReAst::Star(Box::new(parse_regex_ast(&args[0], depth - 1)?)))
                }
                // `AySoundness.RegexThy.plus r = cat r (star r)` — exact. This
                // is the one arm that DUPLICATES its operand, so nested `re.+`
                // doubles the node count per level; `bounded` is what keeps
                // `(re.+ (re.+ … ))` from allocating `2^depth` nodes before the
                // caller's size check ever runs.
                "re.+" if args.len() == 1 => {
                    let inner = parse_regex_ast(&args[0], depth - 1)?;
                    bounded(ReAst::Cat(
                        Box::new(inner.clone()),
                        Box::new(ReAst::Star(Box::new(inner))),
                    ))
                }
                // `AySoundness.RegexThy.opt r = union (lit []) r` — exact.
                "re.opt" if args.len() == 1 => bounded(ReAst::Union(
                    Box::new(ReAst::Lit(Vec::new())),
                    Box::new(parse_regex_ast(&args[0], depth - 1)?),
                )),
                // ONE-SIDED: `L(re.range l u) ⊆ Σ¹ = L(anyChar)` for every
                // `l`, `u` (an ill-formed or inverted range denotes ∅ ⊆ Σ¹).
                // Weakening an asserted atom is sound for a REFUTATION — the
                // real assertion implies the rendered one — but it does mean
                // the emitted atom is not a byte-mirror of the source, which
                // the artifact header states explicitly.
                "re.range" if args.len() == 2 => Some(ReAst::AnyChar),
                _ => None,
            }
        }
        // `((_ re.loop n m) r)` and `((_ re.^ n) r)`.
        PTerm::IndexedApp(_, _, _) => None,
        _ => None,
    }
}

/// Enforce the size caps at EVERY construction point, not just on the finished
/// tree: the `re.+` desugaring duplicates its operand, so a deep nest would
/// otherwise allocate exponentially before any post-hoc check could reject it.
/// Bailing here caps live allocation at roughly twice the node budget.
fn bounded(re: ReAst) -> Option<ReAst> {
    (re.node_count() <= REGEX_LEN_MAX_NODES && re.literal_chars() <= REGEX_LEN_MAX_LITERAL_CHARS)
        .then_some(re)
}

/// `re.none` / `re.all` / `re.allchar`, in either the bare-symbol or the
/// zero-argument application form.
fn nullary_regex(name: &str) -> Option<ReAst> {
    match name {
        "re.none" => Some(ReAst::Empty),
        // `L(re.all) = Σ*` is exactly `L(star anyChar)`.
        "re.all" => Some(ReAst::Star(Box::new(ReAst::AnyChar))),
        "re.allchar" => Some(ReAst::AnyChar),
        _ => None,
    }
}

/// `(str.in_re X R)` with `X` a bare symbol → `(X, R)`.
fn parsed_str_in_re(t: &PTerm) -> Option<(&str, &PTerm)> {
    match t {
        PTerm::App(op, args) if (op == "str.in_re" || op == "str.in.re") && args.len() == 2 => {
            match &args[0] {
                PTerm::Symbol(s) => Some((s.as_str(), &args[1])),
                _ => None,
            }
        }
        _ => None,
    }
}

/// A top-level length pin on some symbol: `(OP (str.len X) N)` or the flipped
/// `(OP N (str.len X))`, normalised to [`LenPin`].
fn parsed_len_pin(t: &PTerm) -> Option<(String, LenPin)> {
    let PTerm::App(op, args) = t else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let left_len = parsed_str_len_arg(&args[0]);
    let right_len = parsed_str_len_arg(&args[1]);
    // `str.len` on BOTH sides is a relation between two lengths, not a pin.
    let (sym, bound, len_on_left) = match (left_len, right_len) {
        (Some(s), None) => (s, parsed_numeral(&args[1])?, true),
        (None, Some(s)) => (s, parsed_numeral(&args[0])?, false),
        _ => return None,
    };
    let bound = u64::try_from(bound).ok()?;
    let pin = match (op.as_str(), len_on_left) {
        ("=", _) => LenPin::Eq(bound),
        ("<=", true) | (">=", false) => LenPin::Le(bound),
        (">=", true) | ("<=", false) => LenPin::Ge(bound),
        // `len < b` ⟺ `len ≤ b - 1`; `b = 0` makes the assertion `len < 0`,
        // which the `Nat` model cannot express, so decline.
        ("<", true) | (">", false) => LenPin::Le(bound.checked_sub(1)?),
        // `len > b` ⟺ `b + 1 ≤ len`.
        (">", true) | ("<", false) => LenPin::Ge(bound.checked_add(1)?),
        _ => return None,
    };
    Some((sym, pin))
}

/// Neutralise text spliced into an emitted Lean block comment: a `/-` opens a
/// NESTED comment and a `-/` closes the header early, either of which breaks
/// the file. Non-printable and non-ASCII characters are replaced so the header
/// cannot smuggle in a directive or an unbalanced delimiter.
fn lean_comment_safe(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut prev_slash = false;
    let mut prev_dash = false;
    for ch in s.chars() {
        let c = if ch.is_ascii_graphic() || ch == ' ' {
            ch
        } else {
            '?'
        };
        if (prev_slash && c == '-') || (prev_dash && c == '/') {
            out.push(' ');
        }
        out.push(c);
        prev_slash = c == '/';
        prev_dash = c == '-';
    }
    out
}

/// Emit a verified-firewall Lean proof for a `str.in_re` + `str.len` conflict
/// found among the PARSED (frontend) assertions.
///
/// `single_shot_query` must be the frontend's
/// [`ay_frontend::Context::is_single_shot_query`]: the emitter DECLINES unless
/// the query used no `push`/`pop` and reached exactly one `check-sat`. Without
/// that, a membership asserted inside a scope that was later popped could be
/// rendered into a certificate for a `check-sat` at which it is not asserted —
/// an artifact that kernel-checks while certifying a query that is `sat`.
pub(crate) fn emit_str_in_re_len_firewall_lean_from_parsed(
    parsed: &[PTerm],
    single_shot_query: bool,
) -> Option<String> {
    if !single_shot_query {
        return None;
    }
    // Fail closed if any name this emitter interprets structurally has become
    // user-declarable: matching it would then conflate a user function with the
    // builtin (the `bvf`/`bv` prefix-classification defect, one table over).
    if !REGEX_LEN_INTERPRETED_OPS
        .iter()
        .all(|name| ay_frontend::is_reserved_op_name(name))
    {
        return None;
    }

    let mut pins: Vec<(String, LenPin)> = Vec::new();
    for asrt in parsed {
        if let Some(pin) = parsed_len_pin(asrt) {
            pins.push(pin);
        }
    }
    if pins.is_empty() {
        return None;
    }

    for asrt in parsed {
        let Some((sym, re_term)) = parsed_str_in_re(asrt) else {
            continue;
        };
        let Some(re) = parse_regex_ast(re_term, 32) else {
            continue;
        };
        if re.node_count() > REGEX_LEN_MAX_NODES || re.literal_chars() > REGEX_LEN_MAX_LITERAL_CHARS
        {
            continue;
        }
        for (pin_sym, pin) in &pins {
            if pin_sym != sym {
                continue;
            }
            if let Some(tier) = regex_len_tier(&re, *pin) {
                return Some(render_str_in_re_len_lean(sym, &re, *pin, tier));
            }
        }
    }
    None
}

/// The Lean `Prop` for the length pin, and the human-readable SMT form.
fn len_pin_lean(pin: LenPin) -> (String, String) {
    match pin {
        LenPin::Eq(c) => (
            format!("StringThy.len m = {c}"),
            format!("(= (str.len X) {c})"),
        ),
        LenPin::Le(b) => (
            format!("StringThy.len m ≤ {b}"),
            format!("(<= (str.len X) {b})"),
        ),
        LenPin::Ge(b) => (
            format!("{b} ≤ StringThy.len m"),
            format!("(>= (str.len X) {b})"),
        ),
    }
}

/// The `False`-producing term for the chosen tier, given `hm : Mem re1 m` and
/// `h` : the length pin.
fn regex_len_conflict_term(tier: RegexLenTier) -> String {
    match tier {
        RegexLenTier::Mod(k) => {
            format!("RegexThy.regex_len_mod_conflict (k := {k}) (by decide) hm h (by decide)")
        }
        RegexLenTier::Min => "RegexThy.regex_len_min_conflict hm h (by decide)".to_string(),
        RegexLenTier::Max(n) => {
            format!("RegexThy.regex_len_max_conflict (n := {n}) (by decide) hm h (by decide)")
        }
        RegexLenTier::MinLe => "RegexThy.regex_len_min_conflict_le hm h (by decide)".to_string(),
        RegexLenTier::MaxGe(n) => {
            format!("RegexThy.regex_len_max_conflict_ge (n := {n}) (by decide) hm h (by decide)")
        }
    }
}

/// A one-line description of the verified invariant the artifact rests on.
fn regex_len_tier_note(tier: RegexLenTier) -> String {
    match tier {
        RegexLenTier::Mod(k) => format!(
            "MODULAR (`mem_len_dvd`): every member of the regex has length divisible \
             by {k}, and the pinned length is not."
        ),
        RegexLenTier::Min | RegexLenTier::MinLe => {
            "TOO SHORT (`mem_minLen_le`): the pinned length is below the regex's \
             structural minimum member length."
                .to_string()
        }
        RegexLenTier::Max(n) | RegexLenTier::MaxGe(n) => format!(
            "TOO LONG (`mem_maxLen_ge`): the regex denotes a FINITE language whose \
             members are at most {n} characters, and the pinned length exceeds that."
        ),
    }
}
