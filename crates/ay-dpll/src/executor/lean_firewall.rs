// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Automatic emitter for the datatype-theory "import-the-verified-theorem"
//! Lean shape (#8419 / formally-verifying-ay half (1)).
//!
//! Given a `DatatypeDistinct` theory lemma `(not (= c C1)) (not (= c C2))` (two
//! distinct constructors of one datatype), this reconstructs the minimal
//! firewall instance — `c = C1`, `c = C2` ⊢ ⊥ — and emits a self-contained Lean
//! file that discharges it through the verified `firewall_combined_unsat`
//! (resolution by `decide`) with the lemma validity carried by datatype
//! constructor distinctness. The emitted file is the runtime counterpart of the
//! hand-written `AySoundness.CombinedDatatype` proof-of-concept; it must
//! `lake build` and kernel-check (axioms ⊆ {propext, Classical.choice,
//! Quot.sound}).
//!
//! Runtime authority boundary: these emitters prove the proposition rendered
//! into each local file. They do not independently bind that proposition's
//! premises to the complete frontend query or refutation. The files are useful
//! diagnostics, but must not authorize a user-visible UNSAT verdict until a
//! query-binding certificate layer is added.
//!
//! Faithful abstraction: the datatype's constructors are emitted as a Lean
//! `inductive` of NULLARY constructors. Distinctness depends only on the
//! constructors being pairwise distinct — which the kernel guarantees for any
//! `inductive` — so dropping constructor arguments does not weaken the
//! certificate (it is exactly the fact `C1 ≠ C2`).

use ay_core::{Sort, Symbol, TermData, TermId, TermStore};
use ay_frontend::command::{Constant as PConst, Index as PIndex, Term as PTerm};

mod array_store_commute;
pub(crate) use array_store_commute::emit_array_store_commute_firewall_lean_from_parsed;

/// A datatype declaration: `(name, [constructor_name, ..])`.
pub(crate) type DatatypeDecls<'a> = &'a [(String, Vec<String>)];

/// Emit a verified-firewall Lean proof for a string length-vs-literal conflict
/// found among the PARSED (frontend) assertions: `(= s L)` and `(= (str.len s)
/// K)` over the same symbol `s`, with `L.length ≠ K`.
///
/// ay's string conflict lemma — and even the `TermId`-level assertions — are
/// surface-rewrite-trivialized before emit, so the structure is recovered from
/// the FRONTEND parsed AST (`ctx.assertions_parsed()`), where it survives intact.
/// Grounds the tautology `¬(s = L) ∨ ¬(str.len s = K)` (`s = L ⟹ len = |L| ≠ K`)
/// through the verified firewall over `Val = String`. `None` if no such conflict.
pub(crate) fn emit_string_length_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    // s -> asserted string literal; s -> asserted str.len value.
    let mut lit_of: Vec<(String, String)> = Vec::new();
    let mut len_of: Vec<(String, i64)> = Vec::new();
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        for (p, q) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            // (= s L): p a symbol, q a string literal.
            if let (PTerm::Symbol(s), PTerm::Const(PConst::String(l))) = (p, q) {
                lit_of.push((s.clone(), l.clone()));
            }
            // (= (str.len s) K): p is `(str.len s)`, q an integer numeral.
            if let (Some(s), Some(k)) = (parsed_str_len_arg(p), parsed_numeral(q)) {
                len_of.push((s, k));
            }
        }
    }
    for (s_lit, lit) in &lit_of {
        for (s_len, k) in &len_of {
            if s_lit == s_len && *k >= 0 && lit.chars().count() as i64 != *k {
                return Some(render_string_length_lean(lit, *k));
            }
        }
    }
    None
}

/// The single operand of `(seq.len ARG)`, else `None`.
fn parsed_seq_len_arg(t: &PTerm) -> Option<&PTerm> {
    match t {
        PTerm::App(op, args) if op == "seq.len" && args.len() == 1 => Some(&args[0]),
        _ => None,
    }
}

/// The single operand of `(str.len ARG)`, else `None`.
fn parsed_str_len_arg_pterm(t: &PTerm) -> Option<&PTerm> {
    match t {
        PTerm::App(op, args) if op == "str.len" && args.len() == 1 => Some(&args[0]),
        _ => None,
    }
}

/// The two operands of a BINARY `(str.++ X Y)`, else `None`.
fn parsed_str_concat2(t: &PTerm) -> Option<(&PTerm, &PTerm)> {
    match t {
        PTerm::App(op, args) if op == "str.++" && args.len() == 2 => Some((&args[0], &args[1])),
        _ => None,
    }
}

/// The two operands of a BINARY `(seq.++ X Y)`, else `None`.
fn parsed_seq_concat2(t: &PTerm) -> Option<(&PTerm, &PTerm)> {
    match t {
        PTerm::App(op, args) if op == "seq.++" && args.len() == 2 => Some((&args[0], &args[1])),
        _ => None,
    }
}

/// Emit a verified-firewall Lean proof for a SEQUENCE length-over-concat conflict
/// found among the PARSED (frontend) assertions:
/// `(= (seq.len (seq.++ X Y)) (+ (seq.len X) (seq.len Y) K))` with a NON-ZERO
/// positive constant offset `K`.
///
/// This is the sequence analogue of the string length emitter. The verified
/// axiom `SeqThy.len_concat` gives `len (concat X Y) = len X + len Y`, so the
/// assertion demands `len X + len Y = len X + len Y + K` — impossible for `K > 0`.
/// ay's QF_SEQ pipeline reduces `seq.len`/`seq.++` eagerly (the theory lemma and
/// the `TermId`-level assertions are surface-rewrite-trivialized before emit), so
/// the structure is recovered from the frontend parsed assertions, exactly like
/// the string / BV / array-ROW1 emitters. Grounded through the verified
/// `firewall_combined_unsat` over `Val = Seq Int × Seq Int`; kernel-checks with
/// axioms ⊆ {propext, Quot.sound}. `None` if no such conflict.
///
/// Soundness note: the certificate is proved for ALL independent model components
/// `(m.1, m.2)`, so it covers the diagonal `X = Y` case too (the general fact
/// implies the specific instance). The `K > 0` restriction keeps the `Nat`-length
/// model faithful (a `K ≤ 0` offset is declined — still sound, just uncertified).
pub(crate) fn emit_seq_len_concat_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        for (lhs, rhs) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            // lhs = (seq.len (seq.++ X Y))
            let Some(concat) = parsed_seq_len_arg(lhs) else {
                continue;
            };
            let Some((x, y)) = parsed_seq_concat2(concat) else {
                continue;
            };
            // rhs = (+ addend ...): partition into seq.len operands and a
            // constant offset K. Any other addend shape declines this assertion.
            let PTerm::App(sop, addends) = rhs else {
                continue;
            };
            if sop != "+" || addends.len() < 2 {
                continue;
            }
            let mut len_args: Vec<&PTerm> = Vec::new();
            let mut k: i64 = 0;
            let mut well_formed = true;
            for a in addends {
                if let Some(arg) = parsed_seq_len_arg(a) {
                    len_args.push(arg);
                } else if let Some(n) = parsed_numeral(a) {
                    k += n;
                } else {
                    well_formed = false;
                    break;
                }
            }
            if !well_formed || len_args.len() != 2 || k <= 0 {
                continue;
            }
            // The two non-constant addends must be exactly seq.len X and
            // seq.len Y (order-independent).
            let (p, q) = (len_args[0], len_args[1]);
            let matches = (p == x && q == y) || (p == y && q == x);
            if matches {
                return Some(render_seq_len_concat_lean(k));
            }
        }
    }
    None
}

/// Emit a verified-firewall Lean proof for a STRING length-over-concat conflict
/// found among the PARSED (frontend) assertions:
/// `(= (str.len (str.++ X Y)) (+ (str.len X) (str.len Y) K))` with a NON-ZERO
/// positive constant offset `K`.
///
/// This is the string analogue of the sequence length emitter. The verified
/// axiom `StringThy.len_cat` gives `len (cat X Y) = len X + len Y` in the standard
/// `List Nat` sequence model, so the assertion demands `len X + len Y =
/// len X + len Y + K` — impossible for `K > 0`. ay reduces `str.len`/`str.++`
/// eagerly (the theory lemma and the `TermId`-level assertions are
/// surface-rewrite-trivialized before emit), so the structure is recovered from
/// the frontend parsed assertions, exactly like the sequence / string / BV /
/// array-ROW1 emitters. Grounded through the verified `firewall_combined_unsat`
/// over `Val = StringThy.Str × StringThy.Str`; kernel-checks with axioms ⊆
/// {propext, Quot.sound}. `None` if no such conflict.
///
/// Soundness note: the certificate is proved for ALL independent model components
/// `(m.1, m.2)`, so it covers the diagonal `X = Y` case too (the general fact
/// implies the specific instance). The `K > 0` restriction keeps the `Nat`-length
/// model faithful (a `K ≤ 0` offset is declined — still sound, just uncertified).
pub(crate) fn emit_str_len_concat_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        for (lhs, rhs) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            // lhs = (str.len (str.++ X Y))
            let Some(concat) = parsed_str_len_arg_pterm(lhs) else {
                continue;
            };
            let Some((x, y)) = parsed_str_concat2(concat) else {
                continue;
            };
            // rhs = (+ addend ...): partition into str.len operands and a
            // constant offset K. Any other addend shape declines this assertion.
            let PTerm::App(sop, addends) = rhs else {
                continue;
            };
            if sop != "+" || addends.len() < 2 {
                continue;
            }
            let mut len_args: Vec<&PTerm> = Vec::new();
            let mut k: i64 = 0;
            let mut well_formed = true;
            for a in addends {
                if let Some(arg) = parsed_str_len_arg_pterm(a) {
                    len_args.push(arg);
                } else if let Some(n) = parsed_numeral(a) {
                    k += n;
                } else {
                    well_formed = false;
                    break;
                }
            }
            if !well_formed || len_args.len() != 2 || k <= 0 {
                continue;
            }
            // The two non-constant addends must be exactly str.len X and
            // str.len Y (order-independent).
            let (p, q) = (len_args[0], len_args[1]);
            let matches = (p == x && q == y) || (p == y && q == x);
            if matches {
                return Some(render_str_len_concat_lean(k));
            }
        }
    }
    None
}

/// Emit a verified-firewall Lean proof for a STRING empty-length conflict found
/// among the PARSED (frontend) assertions: a symbol `s` constrained by BOTH
/// `(= (str.len s) 0)` and `(not (= s ""))` (in either operand order). This is
/// unsatisfiable: the verified axiom `StringThy.len_zero_iff` gives
/// `len s = 0 ↔ s = ε`, so `len s = 0` forces `s = ""`, contradicting `s ≠ ""`.
///
/// ay reduces `str.len` over strings eagerly (bare-trust refutation), so the
/// structure is recovered from the frontend parsed assertions, like the other
/// from-parsed string/sequence emitters. Grounded through the verified
/// `firewall_combined_unsat` over `Val = StringThy.Str`; kernel-checks with
/// axioms ⊆ {propext, Quot.sound}. `None` if no single symbol carries both
/// literals.
pub(crate) fn emit_str_len_zero_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    // s with an asserted `str.len s = 0`.
    let mut len_zero: Vec<String> = Vec::new();
    // s with an asserted `s ≠ ""`.
    let mut nonempty: Vec<String> = Vec::new();
    let is_empty_str = |t: &PTerm| matches!(t, PTerm::Const(PConst::String(l)) if l.is_empty());
    for asrt in parsed {
        match asrt {
            // (not (= s "")) / (not (= "" s))
            PTerm::App(op, args) if op == "not" && args.len() == 1 => {
                if let PTerm::App(eq, eargs) = &args[0] {
                    if eq == "=" && eargs.len() == 2 {
                        for (a, b) in [(&eargs[0], &eargs[1]), (&eargs[1], &eargs[0])] {
                            if let PTerm::Symbol(s) = a {
                                if is_empty_str(b) {
                                    nonempty.push(s.clone());
                                }
                            }
                        }
                    }
                }
            }
            // (= (str.len s) 0) / (= 0 (str.len s))
            PTerm::App(op, args) if op == "=" && args.len() == 2 => {
                for (a, b) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    if let (Some(s), Some(0)) = (parsed_str_len_arg(a), parsed_numeral(b)) {
                        len_zero.push(s);
                    }
                }
            }
            _ => {}
        }
    }
    for s in &len_zero {
        if nonempty.contains(s) {
            return Some(render_str_len_zero_lean(s));
        }
    }
    None
}

/// Emit a verified-firewall Lean proof for a SMALL-WIDTH bit-vector conflict
/// found among the PARSED assertions. ay bit-blasts BV eagerly (its refutation
/// is a bare `(cl) :rule trust`), so the BV structure is recovered from the
/// frontend assertions; for small widths the conflict is decidable, so the whole
/// problem is refuted directly: `∀ vars, ¬(⋀ assertions)`, grounded in
/// `firewall_combined_unsat` over a `BitVec w` (×2) model with curried `decide`.
///
/// Bounded: at most 2 BV variables sharing one width inferred from a literal,
/// supported ops (`bvand/bvor/bvxor/bvnot/bvadd/bvsub/bvmul`), and a case-count
/// gate (`(2^w)^vars ≤ 4096`) to keep `decide` feasible. Returns `None` otherwise.
pub(crate) fn emit_bv_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    // Substitute bit-vector variables pinned to a constant by a `(= v const)`
    // assertion (e.g. `x = #x02`). This is a SOUND rewrite (substituting an
    // asserted equality preserves (un)satisfiability) and DROPS the pinned
    // variable from the free-variable count, bringing larger-width problems with
    // constant operands (e.g. `bvmul x y = #x07 ∧ x = #x02`, 8-bit) under the
    // `decide` case-count gate (256 cases for the single remaining `y`, not the
    // 65536 of two free 8-bit vars — which times out the kernel).
    let substituted = substitute_bv_pinned_vars(parsed);
    let parsed: &[PTerm] = &substituted;

    let mut vars: Vec<String> = Vec::new();
    let mut width: Option<u32> = None;
    // (rendered atom prop, asserted polarity: true = asserted positive)
    let mut atoms: Vec<(String, bool)> = Vec::new();
    for asrt in parsed {
        let (eq_term, asserted_pos) = match asrt {
            PTerm::App(op, args) if op == "not" && args.len() == 1 => (&args[0], false),
            other => (other, true),
        };
        let PTerm::App(op, args) = eq_term else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let l = render_bv(&args[0], &mut vars, &mut width)?;
        let r = render_bv(&args[1], &mut vars, &mut width)?;
        // Equality, or a BV comparison predicate (Bool-valued). For unsigned/
        // signed `>`/`≥`, swap the operands to reuse `.ult/.ule/.slt/.sle`.
        let atom = match op.as_str() {
            "=" => format!("{l} = {r}"),
            "bvult" => format!("{l}.ult {r} = true"),
            "bvule" => format!("{l}.ule {r} = true"),
            "bvslt" => format!("{l}.slt {r} = true"),
            "bvsle" => format!("{l}.sle {r} = true"),
            "bvugt" => format!("{r}.ult {l} = true"),
            "bvuge" => format!("{r}.ule {l} = true"),
            "bvsgt" => format!("{r}.slt {l} = true"),
            "bvsge" => format!("{r}.sle {l} = true"),
            _ => return None,
        };
        atoms.push((atom, asserted_pos));
    }
    let w = width?;
    if atoms.is_empty() || vars.is_empty() || vars.len() > 2 {
        return None;
    }
    // Case-count gate: (2^w)^|vars| ≤ 4096 keeps the kernel `decide` feasible.
    let cases = (1u64 << w).checked_pow(vars.len() as u32)?;
    if cases > 4096 {
        return None;
    }
    Some(render_bv_lean(&atoms, &vars, w))
}

/// Emit a firewall-grounded Lean file for a propositional CONTRADICTION — a
/// purely-Boolean assertion set over `Bool` variables that is unsatisfiable
/// (e.g. `(not (= (not (not p)) p))`, `(= p (not p))`). The conjunction is
/// refuted directly by `decide` over the `Bool`(× …) model; pure Lean 4 core.
/// `None` for anything outside the propositional fragment (non-Bool symbol,
/// unknown connective) or with more than 2 free Bool variables (the projection
/// only models `Bool` / `Bool × Bool`).
pub(crate) fn emit_bool_tautology_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    let mut vars: Vec<String> = Vec::new();
    let mut atoms: Vec<(String, bool)> = Vec::new();
    for asrt in parsed {
        // Strip a top-level `not` for the asserted polarity (mirrors the BV
        // emitter): `(not A)` asserts atom `A` negatively, bare `A` positively.
        let (inner, asserted_pos) = match asrt {
            PTerm::App(op, args) if op == "not" && args.len() == 1 => (&args[0], false),
            other => (other, true),
        };
        let e = render_bool(inner, &mut vars)?;
        atoms.push((format!("{e} = true"), asserted_pos));
    }
    if atoms.is_empty() || vars.is_empty() || vars.len() > 2 {
        return None;
    }
    Some(render_bool_lean(&atoms, &vars))
}

/// Render a parsed propositional term to a Lean `Bool` expression over the model.
/// Boolean variables become `\x01<idx>\x01` placeholders (resolved to `m` / `m.1`
/// / `m.2` by [`render_bool_lean`]); connectives map to Lean `Bool` operators.
/// `None` on any non-propositional shape.
fn render_bool(pt: &PTerm, vars: &mut Vec<String>) -> Option<String> {
    match pt {
        PTerm::Const(c) => match c {
            PConst::True => Some("true".to_string()),
            PConst::False => Some("false".to_string()),
            _ => None,
        },
        PTerm::Symbol(s) => {
            let idx = vars.iter().position(|v| v == s).unwrap_or_else(|| {
                vars.push(s.clone());
                vars.len() - 1
            });
            Some(format!("\u{1}{idx}\u{1}"))
        }
        PTerm::App(op, args) => {
            let r = |a: &PTerm, vars: &mut Vec<String>| render_bool(a, vars);
            match (op.as_str(), args.len()) {
                ("not", 1) => Some(format!("(!{})", r(&args[0], vars)?)),
                ("=", 2) | ("xor", 2) => {
                    let a = r(&args[0], vars)?;
                    let b = r(&args[1], vars)?;
                    Some(if op == "=" {
                        format!("({a} == {b})")
                    } else {
                        format!("({a} != {b})")
                    })
                }
                ("=>", 2) => {
                    let a = r(&args[0], vars)?;
                    let b = r(&args[1], vars)?;
                    Some(format!("(!{a} || {b})"))
                }
                ("and", _) if !args.is_empty() => {
                    let parts: Option<Vec<String>> =
                        args.iter().map(|a| render_bool(a, vars)).collect();
                    Some(format!("({})", parts?.join(" && ")))
                }
                ("or", _) if !args.is_empty() => {
                    let parts: Option<Vec<String>> =
                        args.iter().map(|a| render_bool(a, vars)).collect();
                    Some(format!("({})", parts?.join(" || ")))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Render the firewall Lean file for a propositional contradiction over a
/// `Bool`(× `Bool`) model — structurally identical to [`render_bv_lean`] but with
/// `decide` over `Bool` instead of `BitVec`.
fn render_bool_lean(atoms: &[(String, bool)], vars: &[String]) -> String {
    let proj = |idx: usize| -> String {
        if vars.len() == 1 {
            "m".to_string()
        } else if idx == 0 {
            "m.1".to_string()
        } else {
            "m.2".to_string()
        }
    };
    let resolve = |s: &str| -> String {
        let mut out = String::new();
        let mut rest = s;
        while let Some(start) = rest.find('\u{1}') {
            out.push_str(&rest[..start]);
            let after = &rest[start + 1..];
            let end = after.find('\u{1}').expect("balanced placeholder");
            let idx: usize = after[..end].parse().expect("numeric idx");
            out.push_str(&proj(idx));
            rest = &after[end + 1..];
        }
        out.push_str(rest);
        out
    };
    let resolved: Vec<(String, bool)> = atoms.iter().map(|(s, p)| (resolve(s), *p)).collect();
    let n = resolved.len();
    let hash = fnv_hex(
        &resolved
            .iter()
            .map(|(s, p)| format!("{p}:{s}"))
            .collect::<Vec<_>>()
            .join("\u{1}"),
    );
    let arms = resolved
        .iter()
        .enumerate()
        .map(|(i, (s, _))| format!("  | {} => decide ({s})", i + 1))
        .collect::<Vec<_>>()
        .join("\n");
    let orig = resolved
        .iter()
        .enumerate()
        .map(|(i, (_, pos))| {
            let lit = if *pos {
                format!("{}", i + 1)
            } else {
                format!("-{}", i + 1)
            };
            format!("({}, [{lit}])", i + 1)
        })
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_lits = resolved
        .iter()
        .enumerate()
        .map(|(i, (_, pos))| {
            if *pos {
                format!("-{}", i + 1)
            } else {
                format!("{}", i + 1)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = n + 1;
    let proof_hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let val_ty = if vars.len() == 1 {
        "Bool".to_string()
    } else {
        "Bool × Bool".to_string()
    };
    let validity = if vars.len() == 1 {
        "  revert m\n  decide".to_string()
    } else {
        "  obtain ⟨v0, v1⟩ := m\n  revert v0 v1\n  decide".to_string()
    };
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — propositional contradiction grounded in
  the verified `firewall_combined_unsat`. ay refutes the Boolean conflict eagerly
  (bare-trust); the structure is reconstructed from the frontend assertions and
  the conjunction refuted directly by `decide` over the `Bool` model. Pure Lean 4
  core.
-/
namespace AySoundness.Emitted.Bool_{hash}
open AySoundness

abbrev Val := {val_ty}

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof2}, [], [{proof_hints}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
{validity}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No assignment satisfies the asserted propositional constraints — via the
    firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.Bool_{hash}
"#,
        hash = hash,
        val_ty = val_ty,
        arms = arms,
        orig = orig,
        lemma_lits = lemma_lits,
        lemma_id = lemma_id,
        proof2 = lemma_id + 1,
        proof_hints = proof_hints,
        validity = validity,
    )
}

/// Emit a firewall-grounded Lean file for a small-width bit-vector IDENTITY
/// lemma `(= L R)` over `BitVec` variables (e.g. `(= (bvand x x) x)`,
/// `(= (bvxor x x) #x0)`) — the `BvBitBlast` kind for an all-variable identity,
/// which the from-parsed BV emitter cannot reach (it infers width from a constant
/// operand, absent here). With TermStore access the width comes from the
/// variable's sort; the conjunction is refuted by `decide` over the `BitVec w`
/// model (reusing [`render_bv_lean`]). `None` if the lemma is not a BV equality
/// the model supports, or too wide (≤2 vars, `(2^w)^vars ≤ 4096`).
pub(crate) fn emit_bv_identity_firewall_lean(
    terms: &TermStore,
    lemma_clause: &[TermId],
) -> Option<String> {
    if lemma_clause.len() != 1 {
        return None;
    }
    let TermData::App(eq_sym, eq_args) = terms.get(lemma_clause[0]) else {
        return None;
    };
    if eq_sym.name() != "=" || eq_args.len() != 2 {
        return None;
    }
    let mut vars: Vec<String> = Vec::new();
    let mut width: Option<u32> = None;
    let l = render_bv_term(terms, eq_args[0], &mut vars, &mut width)?;
    let r = render_bv_term(terms, eq_args[1], &mut vars, &mut width)?;
    let w = width?;
    if vars.is_empty() || vars.len() > 2 {
        return None;
    }
    let cases = (1u64 << w).checked_pow(vars.len() as u32)?;
    if cases > 4096 {
        return None;
    }
    // The lemma `(= L R)` is the tautology; the original assertion asserted its
    // negation, so the atom carries `asserted_pos = false`.
    Some(render_bv_lean(&[(format!("{l} = {r}"), false)], &vars, w))
}

/// Render an interned bit-vector term to a Lean `BitVec` expression — the
/// TermId-level twin of [`render_bv`]. A BV variable records its sort width and
/// becomes a `\x01idx\x01` placeholder; a BV constant becomes `0x..#w`; ops map
/// to Lean `BitVec` operators. `None` on unsupported shapes / width disagreement.
fn render_bv_term(
    terms: &TermStore,
    t: TermId,
    vars: &mut Vec<String>,
    width: &mut Option<u32>,
) -> Option<String> {
    match terms.get(t) {
        TermData::Var(name, _) => {
            let Sort::BitVec(bv) = terms.sort(t) else {
                return None;
            };
            set_width(width, bv.width)?;
            let idx = vars.iter().position(|x| x == name).unwrap_or_else(|| {
                vars.push(name.clone());
                vars.len() - 1
            });
            Some(format!("\u{1}{idx}\u{1}"))
        }
        TermData::Const(ay_core::Constant::BitVec { value, width: w }) => {
            set_width(width, *w)?;
            Some(format!("(0x{value:x}#{w})"))
        }
        TermData::App(sym, args) => {
            let bin =
                |s: &str, a: TermId, b: TermId, vars: &mut Vec<String>, width: &mut Option<u32>| {
                    Some(format!(
                        "({} {s} {})",
                        render_bv_term(terms, a, vars, width)?,
                        render_bv_term(terms, b, vars, width)?
                    ))
                };
            match (sym.name(), args.len()) {
                ("bvand", 2) => bin("&&&", args[0], args[1], vars, width),
                ("bvor", 2) => bin("|||", args[0], args[1], vars, width),
                ("bvxor", 2) => bin("^^^", args[0], args[1], vars, width),
                ("bvadd", 2) => bin("+", args[0], args[1], vars, width),
                ("bvsub", 2) => bin("-", args[0], args[1], vars, width),
                ("bvmul", 2) => bin("*", args[0], args[1], vars, width),
                ("bvnot", 1) => Some(format!(
                    "(~~~{})",
                    render_bv_term(terms, args[0], vars, width)?
                )),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Emit a firewall-grounded Lean file for a single-variable linear-arithmetic
/// IDENTITY lemma `(= L R)` over `Int` (e.g. `(= (* x 0) 0)`, `(= (* x 1) x)`) —
/// the `LiaGeneric`/`LinearIdentity` kind. Modeled over `Val = Int`; since the
/// branch is unbounded the validity is by `simp` (which discharges `mul_zero` /
/// `mul_one` / the identically-zero linear form), not `decide`. Restricted to a
/// SINGLE integer variable (the closed cases); multi-variable declines.
pub(crate) fn emit_nia_identity_firewall_lean(
    terms: &TermStore,
    lemma_clause: &[TermId],
) -> Option<String> {
    if lemma_clause.len() != 1 {
        return None;
    }
    let TermData::App(eq_sym, eq_args) = terms.get(lemma_clause[0]) else {
        return None;
    };
    if eq_sym.name() != "=" || eq_args.len() != 2 {
        return None;
    }
    let mut var: Option<TermId> = None;
    let l = render_int_term(terms, eq_args[0], &mut var)?;
    let r = render_int_term(terms, eq_args[1], &mut var)?;
    // Presence check only — must mention exactly one Int variable (the
    // renderers fail closed on a second distinct one); the id itself is unused.
    let _ = var?;
    let hash = fnv_hex(&format!("{l}\u{1}{r}"));
    Some(format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — single-variable linear-arithmetic
  identity `{l} = {r}` over `Int`, grounded in `firewall_combined_unsat` and
  discharged by `simp`. Pure Lean 4 core.
-/
namespace AySoundness.Emitted.NiaIdent_{hash}
open AySoundness

abbrev Val := Int

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ({l} = {r})
  | _ => false

def original : List (Cid × Clause) := [(1, [-1])]
def lemmas   : List (Cid × Clause) := [(2, [1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [1] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  simp

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.NiaIdent_{hash}
"#,
    ))
}

/// Render an interned integer-arithmetic term to a Lean `Int` expression over a
/// single model variable `m`. `+`/`-`/`*` map to Lean ops; a numeral to its
/// value; the (single) integer variable to `m`. `None` on a second distinct
/// variable or any other shape.
fn render_int_term(terms: &TermStore, t: TermId, var: &mut Option<TermId>) -> Option<String> {
    match terms.get(t) {
        TermData::Const(ay_core::Constant::Int(n)) => Some(format!("({n} : Int)")),
        TermData::Var(_, _) if matches!(terms.sort(t), Sort::Int) => match var {
            Some(v) if *v == t => Some("m".to_string()),
            Some(_) => None,
            None => {
                *var = Some(t);
                Some("m".to_string())
            }
        },
        TermData::App(sym, args) if args.len() == 2 => {
            let op = match sym.name() {
                "+" => "+",
                "-" => "-",
                "*" => "*",
                _ => return None,
            };
            let a = render_int_term(terms, args[0], var)?;
            let b = render_int_term(terms, args[1], var)?;
            Some(format!("({a} {op} {b})"))
        }
        _ => None,
    }
}

/// Emit a firewall-grounded Lean file for a datatype SELECTOR-PROJECTION lemma
/// `(= (sel_i (C f0 .. fn)) f_i)` (the `DatatypeSelectorProject` kind) over a
/// TWO-field constructor. The datatype is modeled as a product `T0 × T1`, the
/// constructor as the tuple, and the selector as the matching projection (`.1` /
/// `.2`); `(C f0 f1).i = f_i` by `simp`. `None` for non-binary constructors or
/// field sorts not in the firewall model (`Int`/`Bool`/`BitVec`).
pub(crate) fn emit_dt_selector_projection_firewall_lean(
    terms: &TermStore,
    lemma_clause: &[TermId],
) -> Option<String> {
    if lemma_clause.len() != 1 {
        return None;
    }
    let TermData::App(eq_sym, eq_args) = terms.get(lemma_clause[0]) else {
        return None;
    };
    if eq_sym.name() != "=" || eq_args.len() != 2 {
        return None;
    }
    // One side is `(sel (C f0 f1))`; the other is the projected field `f_i`.
    for (sel_side, val) in [(eq_args[0], eq_args[1]), (eq_args[1], eq_args[0])] {
        let TermData::App(_sel, sel_args) = terms.get(sel_side) else {
            continue;
        };
        if sel_args.len() != 1 {
            continue;
        }
        let TermData::App(_ctor, ctor_args) = terms.get(sel_args[0]) else {
            continue;
        };
        if ctor_args.len() != 2 {
            continue;
        }
        // Which field does the selector project? It must be `val` (id-equal).
        let idx = ctor_args.iter().position(|&f| f == val)?;
        let t0 = sort_to_lean(terms.sort(ctor_args[0]))?;
        let t1 = sort_to_lean(terms.sort(ctor_args[1]))?;
        let proj = if idx == 0 { "1" } else { "2" };
        let hash = fnv_hex(&format!("{t0}\u{1}{t1}\u{1}{proj}"));
        return Some(format!(
            r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — datatype selector projection
  `(sel_i (C f0 f1)) = f_i`, grounded in `firewall_combined_unsat`. The datatype
  is modeled as a product, the constructor as the tuple and the selector as the
  matching projection; the identity is closed by `simp`. Pure Lean 4 core.
-/
namespace AySoundness.Emitted.DtSel_{hash}
open AySoundness

abbrev Val := {t0} × {t1}   -- the two constructor fields (f0, f1)

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((m.1, m.2).{proj} = m.{proj})
  | _ => false

def original : List (Cid × Clause) := [(1, [-1])]
def lemmas   : List (Cid × Clause) := [(2, [1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [1] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  simp

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtSel_{hash}
"#,
        ));
    }
    None
}

/// Emit a firewall-grounded Lean file for an if-then-else IDENTICAL-BRANCHES
/// identity lemma `(= (ite c x x) x)` (the `IteSame` theory lemma kind). The
/// identity holds for ANY condition and ANY branch sort (Lean `ite_self`), so the
/// condition is modeled as an arbitrary `Bool` and the branch at its real sort;
/// validity is by `simp [ite_self]` (no enumeration — the branch may be
/// unbounded). `None` if the clause is not the ROW-same schema or the branch sort
/// is not one this models (`Int` / `Bool` / `BitVec`).
pub(crate) fn emit_ite_same_firewall_lean(
    terms: &TermStore,
    lemma_clause: &[TermId],
) -> Option<String> {
    if lemma_clause.len() != 1 {
        return None;
    }
    let TermData::App(eq_sym, eq_args) = terms.get(lemma_clause[0]) else {
        return None;
    };
    if eq_sym.name() != "=" || eq_args.len() != 2 {
        return None;
    }
    // One side is `(ite c x x)` with identical branches; the other is that `x`.
    let (a, b) = (eq_args[0], eq_args[1]);
    let branch = [(a, b), (b, a)].into_iter().find_map(|(ite_id, val)| {
        let TermData::Ite(_cond, t, e) = terms.get(ite_id) else {
            return None;
        };
        (t == e && *t == val).then_some(val)
    })?;
    let branch_ty = sort_to_lean(terms.sort(branch))?;
    Some(render_ite_same_lean(&branch_ty))
}

/// Emit a firewall-grounded Lean file for a floating-point SIGN-bit identity
/// lemma — `(= (fp.abs (fp.abs x)) (fp.abs x))` (abs idempotence) or
/// `(= (fp.neg (fp.neg x)) x)` (neg involution), and nestings thereof over a
/// single FP variable. `fp.abs` clears the sign bit and `fp.neg` flips it, so the
/// identities are bit-level facts; grounded by `decide` over the `BitVec 5` FP
/// carrier (matching the existing FP-classification firewall — the identities are
/// width-uniform, so the small carrier is representative). `None` for any other
/// FP lemma shape (classification exclusivity is handled by the from-parsed
/// emitter; arithmetic / comparisons decline).
pub(crate) fn emit_fp_identity_firewall_lean(
    terms: &TermStore,
    lemma_clause: &[TermId],
) -> Option<String> {
    if lemma_clause.len() != 1 {
        return None;
    }
    let TermData::App(eq_sym, eq_args) = terms.get(lemma_clause[0]) else {
        return None;
    };
    if eq_sym.name() != "=" || eq_args.len() != 2 {
        return None;
    }
    let mut var: Option<TermId> = None;
    let l = render_fp_bits(terms, eq_args[0], &mut var)?;
    let r = render_fp_bits(terms, eq_args[1], &mut var)?;
    // Must mention exactly one FP variable, and at least one side must apply a
    // sign op (a bare `(= x x)` is not the schema this emitter is for). The
    // variable's id itself is unused — this is a presence check only.
    let _ = var?;
    if !(l.contains("absBits")
        || l.contains("negBits")
        || r.contains("absBits")
        || r.contains("negBits"))
    {
        return None;
    }
    Some(render_fp_identity_lean(&l, &r))
}

/// Render an FP sign-identity term to a Lean `BitVec 5` expression: a single FP
/// variable becomes `m`, `fp.abs`→`absBits`, `fp.neg`→`negBits`. Records the
/// variable and fails closed if a second distinct variable or any other op
/// appears.
fn render_fp_bits(terms: &TermStore, t: TermId, var: &mut Option<TermId>) -> Option<String> {
    match terms.get(t) {
        TermData::App(sym, args) if sym.name() == "fp.abs" && args.len() == 1 => Some(format!(
            "(absBits {})",
            render_fp_bits(terms, args[0], var)?
        )),
        TermData::App(sym, args) if sym.name() == "fp.neg" && args.len() == 1 => Some(format!(
            "(negBits {})",
            render_fp_bits(terms, args[0], var)?
        )),
        TermData::Var(_, _) => {
            // Single FP variable, modeled as `m`.
            match var {
                Some(v) if *v == t => Some("m".to_string()),
                Some(_) => None,
                None => {
                    *var = Some(t);
                    Some("m".to_string())
                }
            }
        }
        _ => None,
    }
}

/// Render the firewall Lean file for an FP sign-bit identity `l = r` over the
/// `BitVec 5` FP carrier, with `absBits`/`negBits` (clear/flip the sign bit) and
/// `decide` validity.
fn render_fp_identity_lean(l: &str, r: &str) -> String {
    let hash = fnv_hex(&format!("{l}\u{1}{r}"));
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — floating-point SIGN-bit identity
  (`fp.abs` idempotence / `fp.neg` involution), grounded in the verified
  `firewall_combined_unsat`. `fp.abs` clears the sign bit, `fp.neg` flips it, so
  the identity is a bit-level fact, refuted by `decide` over the `BitVec 5` FP
  carrier (the existing FP-classification carrier; the identity is width-uniform).
  Pure Lean 4 core.
-/
namespace AySoundness.Emitted.FpIdent_{hash}
open AySoundness

abbrev Val := BitVec 5                              -- eb=2, sb=2; sign bit = idx 4
def absBits (x : BitVec 5) : BitVec 5 := x &&& 0xf#5
def negBits (x : BitVec 5) : BitVec 5 := x ^^^ 0x10#5

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ({l} = {r})
  | _ => false

def original : List (Cid × Clause) := [(1, [-1])]
def lemmas   : List (Cid × Clause) := [(2, [1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [1] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  revert m
  decide

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No FP value violates the sign-bit identity — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.FpIdent_{hash}
"#,
    )
}

/// Map an ay sort to the Lean type used in the firewall model. Only the sorts
/// with a directly-usable, inhabited Lean core type are supported.
fn sort_to_lean(sort: &Sort) -> Option<String> {
    match sort {
        Sort::Int => Some("Int".to_string()),
        Sort::Bool => Some("Bool".to_string()),
        Sort::BitVec(bv) => Some(format!("BitVec {}", bv.width)),
        _ => None,
    }
}

/// Render the firewall Lean file for `(ite c x x) = x` over `Val = T × Bool`
/// (`m.1` = the branch, `m.2` = the arbitrary condition). Validity is carried by
/// `simp [ite_self]`, so the branch type `T` may be unbounded.
fn render_ite_same_lean(branch_ty: &str) -> String {
    let hash = fnv_hex(branch_ty);
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — `ite` with identical branches:
  `(ite c x x) = x`, grounded in the verified `firewall_combined_unsat`. ay
  refutes the conflict eagerly (bare-trust); the identity holds for ANY condition
  and ANY branch (Lean `ite_self`), so the condition is an arbitrary `Bool` and
  the branch is modeled at its real sort, with validity by `simp [ite_self]` (no
  enumeration). Pure Lean 4 core.
-/
namespace AySoundness.Emitted.IteSame_{hash}
open AySoundness

abbrev Val := {branch_ty} × Bool   -- (branch x, arbitrary condition c)

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((if m.2 then m.1 else m.1) = m.1)
  | _ => false

def original : List (Cid × Clause) := [(1, [-1])]
def lemmas   : List (Cid × Clause) := [(2, [1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [1] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  simp [ite_self]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No assignment satisfies `(ite c x x) ≠ x` — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.IteSame_{hash}
"#,
    )
}

/// Substitute integer variables pinned to a numeral by a `(= v n)` assertion
/// with that numeral, throughout all assertions. Sound (substituting an asserted
/// equality preserves (un)satisfiability).
fn substitute_nia_pinned_vars(parsed: &[PTerm]) -> Vec<PTerm> {
    let mut pins: Vec<(String, PTerm)> = Vec::new();
    for a in parsed {
        let PTerm::App(op, args) = a else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        let is_num = |t: &PTerm| matches!(t, PTerm::Const(PConst::Numeral(_)));
        match (&args[0], &args[1]) {
            (PTerm::Symbol(v), c) if is_num(c) => pins.push((v.clone(), c.clone())),
            (c, PTerm::Symbol(v)) if is_num(c) => pins.push((v.clone(), c.clone())),
            _ => {}
        }
    }
    if pins.is_empty() {
        return parsed.to_vec();
    }
    fn subst(t: &PTerm, pins: &[(String, PTerm)]) -> PTerm {
        match t {
            PTerm::Symbol(v) => pins
                .iter()
                .find(|(p, _)| p == v)
                .map(|(_, c)| c.clone())
                .unwrap_or_else(|| t.clone()),
            PTerm::App(op, args) => {
                PTerm::App(op.clone(), args.iter().map(|a| subst(a, pins)).collect())
            }
            other => other.clone(),
        }
    }
    parsed.iter().map(|a| subst(a, &pins)).collect()
}

/// Render a frontend integer term as a Lean `Int` expression, with the single
/// remaining free variable rendered as `m`. Returns `(expr, references_var)`.
/// Multiplications require at least one CONSTANT operand (linearity); a second
/// distinct variable, or a nonlinear product, returns `None`.
fn render_int_linear(t: &PTerm, var: &mut Option<String>) -> Option<(String, bool)> {
    match t {
        PTerm::Symbol(v) => {
            match var {
                Some(existing) if existing == v => {}
                Some(_) => return None, // a second distinct variable — decline
                None => *var = Some(v.clone()),
            }
            Some(("v.m".to_string(), true))
        }
        PTerm::Const(PConst::Numeral(n)) => {
            n.parse::<i64>().ok()?;
            Some((format!("({n} : Int)"), false))
        }
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("+", 2) => {
                let (a, av) = render_int_linear(&args[0], var)?;
                let (b, bv) = render_int_linear(&args[1], var)?;
                Some((format!("({a} + {b})"), av || bv))
            }
            ("-", 2) => {
                let (a, av) = render_int_linear(&args[0], var)?;
                let (b, bv) = render_int_linear(&args[1], var)?;
                Some((format!("({a} - {b})"), av || bv))
            }
            ("-", 1) => {
                let (a, av) = render_int_linear(&args[0], var)?;
                Some((format!("(- {a})"), av))
            }
            ("*", 2) => {
                let (a, av) = render_int_linear(&args[0], var)?;
                let (b, bv) = render_int_linear(&args[1], var)?;
                if av && bv {
                    return None; // nonlinear product of two variable terms
                }
                Some((format!("({a} * {b})"), av || bv))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Emit a verified-firewall Lean proof for a NONLINEAR-INTEGER conflict that
/// becomes a single unsatisfiable LINEAR EQUALITY after substituting
/// constant-pinned variables — e.g. `(* x y) = 7 ∧ x = 2` ⟶ `2 * y = 7`.
///
/// ay treats `x * y` as nonlinear and refutes it eagerly (bare trust), so this
/// reconstructs from the frontend assertions: substitute the pins (sound), then
/// if exactly ONE assertion is a positive equality over ONE remaining variable
/// that is linear, ground the theory conflict `¬(L = R)` by `omega` (a Lean-CORE
/// tactic) through `firewall_combined_unsat`. Runtime counterpart of
/// `AySoundness.CombinedNiaLinear`; axioms ⊆ {propext, Quot.sound}.
pub(crate) fn emit_nia_linear_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    let substituted = substitute_nia_pinned_vars(parsed);
    // Exactly one positive equality mentioning a (single) variable; all other
    // assertions must be variable-free (trivially-true `const = const` etc.).
    let mut conflict: Option<String> = None;
    for asrt in &substituted {
        // Only positive equalities are handled here.
        let PTerm::App(op, args) = asrt else {
            return None;
        };
        if op != "=" || args.len() != 2 {
            return None;
        }
        let mut var: Option<String> = None;
        let (l, lv) = render_int_linear(&args[0], &mut var)?;
        let (r, rv) = render_int_linear(&args[1], &mut var)?;
        if lv || rv {
            // An assertion mentioning a variable: must be the unique conflict.
            if conflict.is_some() {
                return None;
            }
            conflict = Some(format!("{l} = {r}"));
        }
        // variable-free assertions are ignored (the pinned `v = n` collapses to
        // `n = n`, trivially true, contributing nothing to the conflict).
    }
    let atom = conflict?;
    Some(render_nia_linear_lean(&atom, fnv_hex(&atom)))
}

/// Render the `AySoundness.CombinedNiaLinear`-shaped Lean for a single linear
/// integer-equality conflict `atom` (e.g. `2 * m = 7`), discharged by `omega`.
fn render_nia_linear_lean(atom: &str, hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — NONLINEAR-INTEGER conflict that is
  LINEAR after constant folding, grounded in the verified `firewall_combined_unsat`.
  After substituting constant-pinned variables, the constraint `{atom}` has no
  integer solution; the theory conflict is discharged by `omega` (a Lean-CORE
  tactic — no Mathlib). axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.NiaLinear_{hash}
open AySoundness

structure Val where
  m : Int

/-- Atom `1 ↦ {atom}` (the constraint after substituting the pinned variables). -/
def atomVal (v : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ({atom})
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem linear_lemma_valid (v : Val) : clauseSat (atomVal v) [-1] = true := by
  simp only [clauseSat, litSat, atomVal, List.any_cons, List.any_nil, Bool.or_false]
  have h : ¬ ({atom}) := by omega
  simp [h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ v : Val, clauseSat (atomVal v) cl = true := by
  intro cl hcl v
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact linear_lemma_valid v

/-- `{atom}` has no integer solution — via the verified firewall. -/
theorem no_model : ∀ v : Val, ¬ Sat (atomVal v) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.NiaLinear_{hash}
"#,
    )
}

/// Substitute every BV variable pinned to a constant by a `(= v const)`
/// assertion with that constant, throughout all assertions. Sound (substituting
/// an asserted equality preserves (un)satisfiability); the pinned `(= v const)`
/// assertion becomes the trivial `(= const const)`, and the variable disappears
/// from the free-variable count.
fn substitute_bv_pinned_vars(parsed: &[PTerm]) -> Vec<PTerm> {
    let is_bv_const = |t: &PTerm| {
        matches!(
            t,
            PTerm::Const(PConst::Hexadecimal(_)) | PTerm::Const(PConst::Binary(_))
        )
    };
    // Collect `var → const` pins from `(= v c)` / `(= c v)`.
    let mut pins: Vec<(String, PTerm)> = Vec::new();
    for a in parsed {
        let PTerm::App(op, args) = a else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        match (&args[0], &args[1]) {
            (PTerm::Symbol(v), c) if is_bv_const(c) => pins.push((v.clone(), c.clone())),
            (c, PTerm::Symbol(v)) if is_bv_const(c) => pins.push((v.clone(), c.clone())),
            _ => {}
        }
    }
    if pins.is_empty() {
        return parsed.to_vec();
    }
    fn subst(t: &PTerm, pins: &[(String, PTerm)]) -> PTerm {
        match t {
            PTerm::Symbol(v) => pins
                .iter()
                .find(|(p, _)| p == v)
                .map(|(_, c)| c.clone())
                .unwrap_or_else(|| t.clone()),
            PTerm::App(op, args) => {
                PTerm::App(op.clone(), args.iter().map(|a| subst(a, pins)).collect())
            }
            other => other.clone(),
        }
    }
    parsed.iter().map(|a| subst(a, &pins)).collect()
}

/// Render a parsed BV term to Lean (over a `BitVec w` model): variables become
/// the model projection (`m` for 1 var, `m.1`/`m.2` for 2), literals become
/// `0x..#w` / `0b..#w`, ops map to Lean `BitVec` operators. Infers/checks `width`
/// from literals. `None` on unsupported shapes or width disagreement.
fn render_bv(t: &PTerm, vars: &mut Vec<String>, width: &mut Option<u32>) -> Option<String> {
    match t {
        PTerm::Symbol(v) => {
            let idx = vars.iter().position(|x| x == v).unwrap_or_else(|| {
                vars.push(v.clone());
                vars.len() - 1
            });
            // Projection chosen later once the var count is known; use a
            // placeholder token resolved in `render_bv_lean`.
            Some(format!("\u{1}{idx}\u{1}"))
        }
        PTerm::Const(PConst::Hexadecimal(h)) => {
            // Frontend stores the literal WITH its `#x` prefix (e.g. "#xF").
            let digits = h.strip_prefix("#x").unwrap_or(h);
            if digits.is_empty() {
                return None;
            }
            let w = (digits.len() as u32) * 4;
            set_width(width, w)?;
            Some(format!("(0x{digits}#{w})"))
        }
        PTerm::Const(PConst::Binary(b)) => {
            let bits = b.strip_prefix("#b").unwrap_or(b);
            if bits.is_empty() {
                return None;
            }
            let w = bits.len() as u32;
            set_width(width, w)?;
            Some(format!("(0b{bits}#{w})"))
        }
        PTerm::App(op, args) => {
            let bin = |sym: &str,
                       a: &PTerm,
                       b: &PTerm,
                       vars: &mut Vec<String>,
                       width: &mut Option<u32>| {
                Some(format!(
                    "({} {sym} {})",
                    render_bv(a, vars, width)?,
                    render_bv(b, vars, width)?
                ))
            };
            match (op.as_str(), args.len()) {
                ("bvand", 2) => bin("&&&", &args[0], &args[1], vars, width),
                ("bvor", 2) => bin("|||", &args[0], &args[1], vars, width),
                ("bvxor", 2) => bin("^^^", &args[0], &args[1], vars, width),
                ("bvadd", 2) => bin("+", &args[0], &args[1], vars, width),
                ("bvsub", 2) => bin("-", &args[0], &args[1], vars, width),
                ("bvmul", 2) => bin("*", &args[0], &args[1], vars, width),
                ("bvnot", 1) => Some(format!("(~~~{})", render_bv(&args[0], vars, width)?)),
                _ => None,
            }
        }
        _ => None,
    }
}

fn set_width(width: &mut Option<u32>, w: u32) -> Option<()> {
    match width {
        Some(existing) if *existing != w => None,
        _ => {
            *width = Some(w);
            Some(())
        }
    }
}

fn render_bv_lean(atoms: &[(String, bool)], vars: &[String], w: u32) -> String {
    // Resolve var-index placeholders (`\x01<idx>\x01`) to model projections.
    let proj = |idx: usize| -> String {
        if vars.len() == 1 {
            "m".to_string()
        } else if idx == 0 {
            "m.1".to_string()
        } else {
            "m.2".to_string()
        }
    };
    let resolve = |s: &str| -> String {
        let mut out = String::new();
        let mut rest = s;
        while let Some(start) = rest.find('\u{1}') {
            out.push_str(&rest[..start]);
            let after = &rest[start + 1..];
            let end = after.find('\u{1}').expect("balanced placeholder");
            let idx: usize = after[..end].parse().expect("numeric idx");
            out.push_str(&proj(idx));
            rest = &after[end + 1..];
        }
        out.push_str(rest);
        out
    };
    let resolved: Vec<(String, bool)> = atoms.iter().map(|(s, p)| (resolve(s), *p)).collect();
    let n = resolved.len();
    let hash = fnv_hex(
        &resolved
            .iter()
            .map(|(s, p)| format!("{p}:{s}"))
            .collect::<Vec<_>>()
            .join("\u{1}"),
    );
    let arms = resolved
        .iter()
        .enumerate()
        .map(|(i, (s, _))| format!("  | {} => decide ({s})", i + 1))
        .collect::<Vec<_>>()
        .join("\n");
    // original asserts each atom with its asserted polarity.
    let orig = resolved
        .iter()
        .enumerate()
        .map(|(i, (_, pos))| {
            let lit = if *pos {
                format!("{}", i + 1)
            } else {
                format!("-{}", i + 1)
            };
            format!("({}, [{lit}])", i + 1)
        })
        .collect::<Vec<_>>()
        .join(", ");
    // lemma = negation of the asserted conjunction.
    let lemma_lits = resolved
        .iter()
        .enumerate()
        .map(|(i, (_, pos))| {
            if *pos {
                format!("-{}", i + 1)
            } else {
                format!("{}", i + 1)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = n + 1;
    let proof_hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let val_ty = if vars.len() == 1 {
        format!("BitVec {w}")
    } else {
        format!("BitVec {w} × BitVec {w}")
    };
    let validity = if vars.len() == 1 {
        "  revert m\n  decide".to_string()
    } else {
        "  obtain ⟨v0, v1⟩ := m\n  revert v0 v1\n  decide".to_string()
    };
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — small-width bit-vector conflict grounded
  in the verified `firewall_combined_unsat`. ay bit-blasts BV eagerly (bare-trust
  refutation), so the structure is reconstructed from the frontend assertions; for
  small widths the conjunction is refuted directly by curried `decide` over the
  `BitVec {w}` model (destructure the product, enumerate each factor — no Mathlib
  `Fintype`). Pure Lean 4 core.
-/
namespace AySoundness.Emitted.Bv_{hash}
open AySoundness

abbrev Val := {val_ty}

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof2}, [], [{proof_hints}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
{validity}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No small-width assignment satisfies the asserted BV constraints — via the
    firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.Bv_{hash}
"#,
        w = w,
        hash = hash,
        val_ty = val_ty,
        arms = arms,
        orig = orig,
        lemma_lits = lemma_lits,
        lemma_id = lemma_id,
        proof2 = lemma_id + 1,
        proof_hints = proof_hints,
        validity = validity,
    )
}

/// Emit a verified-firewall Lean proof for a direct array read-over-write-SAME
/// conflict among the PARSED assertions: `(not (= (select (store a i v) i) v))`
/// (the store and read indices coincide and the read disagrees with the stored
/// value) — which ay refutes as bare-trust (eager), so it is recovered from the
/// frontend assertions. `select (store a i v) i = v` is the McCarthy ROW-same
/// axiom (holds for ALL `a, i, v`), so `a/i/v` are modeled as opaque components
/// (`(Nat → Nat) × (Nat → Nat)` = array × scalar valuation; `store` is an
/// `if`-update) and the generic theorem is emitted; validity is `simp` (`i = i`).
pub(crate) fn emit_array_row1_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    for asrt in parsed {
        // (not (= SEL RHS))
        let PTerm::App(op, args) = asrt else { continue };
        if op != "not" || args.len() != 1 {
            continue;
        }
        let PTerm::App(eqop, eqargs) = &args[0] else {
            continue;
        };
        if eqop != "=" || eqargs.len() != 2 {
            continue;
        }
        // Try both orderings of the equality.
        for (sel, rhs) in [(&eqargs[0], &eqargs[1]), (&eqargs[1], &eqargs[0])] {
            // SEL = (select (store a i v) i)
            let PTerm::App(s1, sargs) = sel else { continue };
            if s1 != "select" || sargs.len() != 2 {
                continue;
            }
            let (store_t, ridx) = (&sargs[0], &sargs[1]);
            let PTerm::App(s2, stargs) = store_t else {
                continue;
            };
            if s2 != "store" || stargs.len() != 3 {
                continue;
            }
            let (_a, sidx, sval) = (&stargs[0], &stargs[1], &stargs[2]);
            // Read index == store index, and RHS == stored value: the negated
            // McCarthy ROW-same axiom — a genuine bare-trust ROW1 conflict.
            if sidx == ridx && rhs == sval {
                return Some(render_array_row1_lean(fnv_hex(&format!("{asrt:?}"))));
            }
        }
    }
    None
}

fn render_array_row1_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — array read-over-write-SAME, grounded in
  the verified `firewall_combined_unsat`. The assertion `select (store a i v) i ≠ v`
  contradicts the McCarthy ROW-same axiom `select (store a i v) i = v` (holds for
  ALL a, i, v). Reconstructed from the frontend assertions (ay refutes BV/array
  eagerly as bare-trust). Model: `(Nat → Nat) × (Nat → Nat)` = array × scalar
  valuation (`i = s 0`, `v = s 1`); `store` is an `if`-update; `select (store …) i`
  reduces to `v` since `i = i`. Generic ROW1 theorem. Pure Lean 4 core.
-/
namespace AySoundness.Emitted.ArrRow1_{hash}
open AySoundness

abbrev Val := (Nat → Nat) × (Nat → Nat)

-- atom 1 = (select (store a i v) i = v) = (if i = i then v else a i) = v.
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((if (m.2 0) = (m.2 0) then (m.2 1) else (m.1 (m.2 0))) = (m.2 1))
  | _ => false

def original : List (Cid × Clause) := [(1, [-1])]
def lemmas   : List (Cid × Clause) := [(2, [1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [1] = true := by
  simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- `select (store a i v) i ≠ v` is unsatisfiable — via the firewall (ROW-same). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrRow1_{hash}
"#,
    )
}

/// State threaded through the nested-store read-over-write translation: the
/// scalar valuation registry (`m.2 k` for each distinct index/element name), the
/// single base-array name (`m.1`), and the non-reflexive `if`-conditions
/// (`(read_idx, store_idx)` valuation-index pairs) that arise while unfolding
/// `select`-over-`store` into nested `if`-updates.
struct NestedStoreCtx {
    /// Distinct index/element constant identities, in first-appearance order; the
    /// position is the valuation index used as `m.2 <idx>`.
    scalars: Vec<NestedScalarKey>,
    /// The single named base array (`m.1`); a second distinct base ⇒ decline.
    base: Option<String>,
    /// Non-reflexive `if`-conditions `(read_idx, store_idx)`, deduplicated,
    /// oriented exactly as emitted (`(m.2 read) = (m.2 store)`).
    conds: Vec<(usize, usize)>,
}

impl NestedStoreCtx {
    fn new() -> Self {
        NestedStoreCtx {
            scalars: Vec::new(),
            base: None,
            conds: Vec::new(),
        }
    }

    fn scalar_idx(&mut self, key: NestedScalarKey) -> usize {
        if let Some(p) = self.scalars.iter().position(|scalar| scalar == &key) {
            p
        } else {
            self.scalars.push(key);
            self.scalars.len() - 1
        }
    }

    fn record_cond(&mut self, r: usize, s: usize) {
        if r != s && !self.conds.contains(&(r, s)) {
            self.conds.push((r, s));
        }
    }
}

/// Identity of an opaque scalar in the emitted array model. Named constants and
/// literal constants must occupy disjoint namespaces: SMT-LIB permits quoted
/// symbols whose spelling equals a literal's debug rendering.
#[derive(Clone, PartialEq, Eq)]
enum NestedScalarKey {
    Named(String),
    Literal(PConst),
    IndexedLiteral(String, Vec<PIndex>),
}

/// Extract a scalar (index/element) identity: a `Symbol`, a nullary
/// application, or a literal constant. `None` for a compound term.
fn nested_scalar_key(t: &PTerm) -> Option<NestedScalarKey> {
    match t {
        PTerm::Symbol(s) => Some(NestedScalarKey::Named(s.clone())),
        PTerm::App(f, args) if args.is_empty() => Some(NestedScalarKey::Named(f.clone())),
        PTerm::Const(c) => Some(NestedScalarKey::Literal(c.clone())),
        PTerm::IndexedApp(name, indices, args)
            if args.is_empty()
                && (name.strip_prefix("bv").is_some_and(|value| {
                    !value.is_empty() && value.bytes().all(|b| b.is_ascii_digit())
                }) || matches!(
                    name.as_str(),
                    "Char" | "char" | "+zero" | "-zero" | "+oo" | "-oo" | "NaN"
                )) =>
        {
            Some(NestedScalarKey::IndexedLiteral(
                name.clone(),
                indices.clone(),
            ))
        }
        _ => None,
    }
}

/// Extract a named base-array leaf. Literal constants cannot denote arrays, so
/// accepting one here would make the untyped parsed-AST reconstruction less
/// conservative than the frontend's sorted term.
fn nested_base_name(t: &PTerm) -> Option<String> {
    match t {
        PTerm::Symbol(s) => Some(s.clone()),
        PTerm::App(f, args) if args.is_empty() => Some(f.clone()),
        _ => None,
    }
}

/// Translate an element-sorted term to a Lean `Nat` expression over the model
/// `(Nat → Nat) × (Nat → Nat)` (base array × scalar valuation), recording the
/// `if`-conditions encountered. `None` for a shape outside the `select`/`store`
/// read-over-write fragment (compound index, second base array, …).
fn nested_elem_expr(t: &PTerm, ctx: &mut NestedStoreCtx) -> Option<String> {
    match t {
        PTerm::App(op, args) if op == "select" && args.len() == 2 => {
            let r = nested_index_idx(&args[1], ctx)?;
            nested_sel_expr(&args[0], r, ctx)
        }
        _ => {
            let key = nested_scalar_key(t)?;
            let k = ctx.scalar_idx(key);
            Some(format!("(m.2 {k})"))
        }
    }
}

/// A `select`'s index argument must be a scalar; return its valuation index.
fn nested_index_idx(t: &PTerm, ctx: &mut NestedStoreCtx) -> Option<usize> {
    let key = nested_scalar_key(t)?;
    Some(ctx.scalar_idx(key))
}

/// Unfold `select(arr, r)` over a `store`-chain into nested `if`-updates,
/// bottoming out at `m.1 (m.2 r)` for the single base array. `r` is the read
/// index's valuation index.
fn nested_sel_expr(arr: &PTerm, r: usize, ctx: &mut NestedStoreCtx) -> Option<String> {
    match arr {
        PTerm::App(op, args) if op == "store" && args.len() == 3 => {
            let i = nested_index_idx(&args[1], ctx)?;
            let v = nested_elem_expr(&args[2], ctx)?;
            let inner = nested_sel_expr(&args[0], r, ctx)?;
            ctx.record_cond(r, i);
            Some(format!("(if (m.2 {r}) = (m.2 {i}) then {v} else {inner})"))
        }
        _ => {
            let name = nested_base_name(arr)?;
            match &ctx.base {
                Some(base) if base != &name => return None,
                _ => ctx.base = Some(name),
            }
            Some(format!("(m.1 (m.2 {r}))"))
        }
    }
}

/// Symbolic normal form of an element under the "all distinct indices" branch
/// (every non-reflexive `if`-condition false, reflexive ones true) — the value
/// the emitted `if`-tree reduces to when no guard fires. Mirrors
/// `nested_elem_expr` structurally so the two agree.
#[derive(PartialEq, Eq)]
enum NestedNf {
    /// A scalar valuation `m.2 k`.
    Scalar(usize),
    /// A base-array read `m.1 (m.2 r)`.
    BaseRead(usize),
}

fn nested_elem_nf(t: &PTerm, ctx: &mut NestedStoreCtx) -> Option<NestedNf> {
    match t {
        PTerm::App(op, args) if op == "select" && args.len() == 2 => {
            let r = nested_index_idx(&args[1], ctx)?;
            nested_sel_nf(&args[0], r, ctx)
        }
        _ => {
            let key = nested_scalar_key(t)?;
            Some(NestedNf::Scalar(ctx.scalar_idx(key)))
        }
    }
}

fn nested_sel_nf(arr: &PTerm, r: usize, ctx: &mut NestedStoreCtx) -> Option<NestedNf> {
    match arr {
        PTerm::App(op, args) if op == "store" && args.len() == 3 => {
            let i = nested_index_idx(&args[1], ctx)?;
            if i == r {
                nested_elem_nf(&args[2], ctx)
            } else {
                nested_sel_nf(&args[0], r, ctx)
            }
        }
        _ => {
            // Require a named base-array leaf; identity was checked while
            // constructing the emitted expression and is irrelevant to NF.
            nested_base_name(arr)?;
            Some(NestedNf::BaseRead(r))
        }
    }
}

/// `true` if the term is `(select (store …) idx)` — the nested read-over-write
/// shape this emitter targets (distinguishing it from a plain scalar side).
fn is_select_over_store(t: &PTerm) -> bool {
    matches!(t, PTerm::App(op, args)
        if op == "select" && args.len() == 2
            && matches!(&args[0], PTerm::App(o2, a2) if o2 == "store" && a2.len() == 3))
}

/// Emit a verified-firewall Lean proof for a NESTED / multi-`store`
/// read-over-write conflict among the PARSED assertions:
/// `(not (= LHS RHS))` where at least one side is `(select (store … ) r)` over a
/// `store`-chain and, under the asserted index disequalities, both sides reduce
/// (by the McCarthy axioms) to the SAME value — e.g.
/// `select (store (store a i v1) i v2) j` vs `select (store a i v2) j` with
/// `i ≠ j`. ay refutes arrays eagerly (bare-trust), so the conflict is
/// reconstructed from the frontend assertions.
///
/// Grounding: the same verified `firewall_combined_unsat` and the standard
/// functional array model as the single-store ROW1/ROW2 emitters. `a/i/j/v` are
/// modeled as opaque components (`(Nat → Nat) × (Nat → Nat)` = base array ×
/// scalar valuation); `select`-over-`store` unfolds to nested raw `if`-updates
/// that mirror the McCarthy read-over-write axioms. The guarded clause
/// `row_eq ∨ (⋁ index-coincidences)` is proved directly by `by_cases` on each
/// non-reflexive `if`-condition plus `simp`; the generated artifact does not
/// import or invoke `AySoundness.ArrayThy`.
///
/// Fail-closed: declines (`None`) unless there is a single base array, every
/// non-reflexive `if`-condition is backed by an asserted disequality (so the
/// clause is valid), and both sides share the same reduced normal form (so the
/// all-distinct branch closes). NO verdict/clause change on decline.
pub(crate) fn emit_array_nested_store_row_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    // Pass 1: collect asserted index disequalities `(not (= x y))` as unordered
    // scalar-name pairs — these back the guard literals.
    let mut diseqs: Vec<(NestedScalarKey, NestedScalarKey)> = Vec::new();
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        // `(distinct t1 … tn)` (n ≥ 2) asserts every pair unequal — expand into
        // the pairwise scalar disequalities that back the guard literals, exactly
        // as if `n·(n−1)/2` separate `(not (= ti tj))` had been asserted. Common
        // in QF_AX store-commute benchmarks (`(distinct i0 i1 …)`), where the
        // pairwise index inequalities are what make the read-over-write conflict
        // valid.
        if op == "distinct" && args.len() >= 2 {
            let keys: Vec<Option<NestedScalarKey>> = args.iter().map(nested_scalar_key).collect();
            for a in 0..keys.len() {
                for b in (a + 1)..keys.len() {
                    if let (Some(x), Some(y)) = (keys[a].clone(), keys[b].clone()) {
                        diseqs.push((x, y));
                    }
                }
            }
            continue;
        }
        if op != "not" || args.len() != 1 {
            continue;
        }
        let PTerm::App(eq, eargs) = &args[0] else {
            continue;
        };
        if eq != "=" || eargs.len() != 2 {
            continue;
        }
        if let (Some(x), Some(y)) = (nested_scalar_key(&eargs[0]), nested_scalar_key(&eargs[1])) {
            diseqs.push((x, y));
        }
    }
    let backed = |a: &NestedScalarKey, b: &NestedScalarKey| -> bool {
        diseqs
            .iter()
            .any(|(x, y)| (x == a && y == b) || (x == b && y == a))
    };

    // Pass 2: find the main read-over-write disequality and reconstruct it.
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "not" || args.len() != 1 {
            continue;
        }
        let PTerm::App(eq, eargs) = &args[0] else {
            continue;
        };
        if eq != "=" || eargs.len() != 2 {
            continue;
        }
        let (lhs, rhs) = (&eargs[0], &eargs[1]);
        // At least one side must be a genuine select-over-store (else it is a
        // plain disequality or a single ROW1, handled elsewhere).
        if !is_select_over_store(lhs) && !is_select_over_store(rhs) {
            continue;
        }
        let mut ctx = NestedStoreCtx::new();
        let Some(lhs_expr) = nested_elem_expr(lhs, &mut ctx) else {
            continue;
        };
        let Some(rhs_expr) = nested_elem_expr(rhs, &mut ctx) else {
            continue;
        };
        // Both sides must reduce to the SAME value under all-distinct indices,
        // and every non-reflexive if-condition must be a backed disequality.
        let Some(lhs_nf) = nested_elem_nf(lhs, &mut ctx) else {
            continue;
        };
        let Some(rhs_nf) = nested_elem_nf(rhs, &mut ctx) else {
            continue;
        };
        if lhs_nf != rhs_nf {
            continue;
        }
        let all_backed = ctx
            .conds
            .iter()
            .all(|&(r, s)| backed(&ctx.scalars[r], &ctx.scalars[s]));
        if !ctx.conds.is_empty() && all_backed {
            // GUARDED conflict: `row_eq ∨ (⋁ index-coincidences)`, valid because
            // every non-reflexive `if`-condition is a backed disequality (the
            // all-distinct branch closes to the shared normal form).
            return Some(render_array_nested_store_lean(
                &lhs_expr,
                &rhs_expr,
                &ctx.conds,
                fnv_hex(&format!("nested_store:{asrt:?}")),
            ));
        }
        // No backing disequalities (empty guard, or an unbacked `if`-condition):
        // the guarded clause need not be valid, BUT `LHS = RHS` may still hold
        // UNCONDITIONALLY — the two `if`-trees can be provably equal for every
        // truth-assignment of the guards (e.g. `store` idempotence, or a plain
        // reflexive ROW1 exposed after inlining an array-let). Emit only when a
        // full enumeration confirms the two trees agree under EVERY guard
        // assignment; then the lemma is the unconditional `row_eq` (clause `[1]`),
        // proved by `by_cases` on each guard `<;> simp`. Fail closed otherwise.
        if nested_trees_unconditionally_equal(lhs, rhs, &mut ctx) {
            return Some(render_array_unconditional_lean(
                &lhs_expr,
                &rhs_expr,
                &ctx.conds,
                fnv_hex(&format!("nested_uncond:{asrt:?}")),
            ));
        }
    }
    None
}

/// Cap on the number of non-reflexive `if`-conditions for the UNCONDITIONAL
/// equality enumeration (and the `2^g`-branch `by_cases <;> simp` it emits): the
/// check reduces both `if`-trees under all `2^g` guard assignments, so `g` must
/// stay small. Backed guarded conflicts (the common storecomm case) never reach
/// this path, so the cap only bounds the unconditional fragment.
const NESTED_UNCOND_MAX_GUARDS: usize = 4;

/// `true` when `LHS` and `RHS` reduce to the SAME symbolic normal form under
/// EVERY truth-assignment of the recorded non-reflexive `if`-conditions
/// (`ctx.conds`). Each guard is an independent equality the model can realize
/// freely, so agreement across all `2^g` assignments proves `LHS = RHS` holds in
/// every model — the exact obligation the emitted `by_cases <;> simp` proof
/// discharges. Reflexive `if`-conditions (`read = store` at the same valuation
/// index) are always-then in both this reducer and Lean's `simp`, so they are not
/// enumerated. Declines (`false`) when `g` exceeds the enumeration cap, or when
/// any assignment makes the two normal forms differ (fail closed — a differing
/// assignment is a genuine countermodel unless it is unrealizable, and we do not
/// attempt to prove unrealizability).
fn nested_trees_unconditionally_equal(lhs: &PTerm, rhs: &PTerm, ctx: &mut NestedStoreCtx) -> bool {
    let g = ctx.conds.len();
    if g > NESTED_UNCOND_MAX_GUARDS {
        return false;
    }
    // Snapshot the recorded conditions so the reducer can look up guard positions
    // without borrowing `ctx.conds` while it may extend `ctx.scalars`.
    let conds = ctx.conds.clone();
    for mask in 0u32..(1u32 << g) {
        let assign = |r: usize, s: usize| -> bool {
            match conds.iter().position(|&(cr, cs)| cr == r && cs == s) {
                Some(pos) => (mask >> pos) & 1 == 1,
                // A non-reflexive condition that was not recorded cannot occur
                // (every one is recorded while building the expr); treat a miss
                // conservatively as the all-distinct (false) branch.
                None => false,
            }
        };
        let Some(l) = nested_elem_nf_under(lhs, ctx, &assign) else {
            return false;
        };
        let Some(r) = nested_elem_nf_under(rhs, ctx, &assign) else {
            return false;
        };
        if l != r {
            return false;
        }
    }
    true
}

/// Assignment-parameterized twin of `nested_elem_nf`: reduce an element-sorted
/// term to its normal form where each non-reflexive `if`-condition's truth is
/// supplied by `assign(read_idx, store_idx)`. Mirrors the emitted `if`-tree so
/// the Rust enumeration and the Lean `by_cases <;> simp` agree branch-for-branch.
fn nested_elem_nf_under(
    t: &PTerm,
    ctx: &mut NestedStoreCtx,
    assign: &dyn Fn(usize, usize) -> bool,
) -> Option<NestedNf> {
    match t {
        PTerm::App(op, args) if op == "select" && args.len() == 2 => {
            let r = nested_index_idx(&args[1], ctx)?;
            nested_sel_nf_under(&args[0], r, ctx, assign)
        }
        _ => {
            let key = nested_scalar_key(t)?;
            Some(NestedNf::Scalar(ctx.scalar_idx(key)))
        }
    }
}

fn nested_sel_nf_under(
    arr: &PTerm,
    r: usize,
    ctx: &mut NestedStoreCtx,
    assign: &dyn Fn(usize, usize) -> bool,
) -> Option<NestedNf> {
    match arr {
        PTerm::App(op, args) if op == "store" && args.len() == 3 => {
            let i = nested_index_idx(&args[1], ctx)?;
            if i == r {
                // Reflexive `if (m.2 r) = (m.2 r)` — always the stored value.
                nested_elem_nf_under(&args[2], ctx, assign)
            } else if assign(r, i) {
                nested_elem_nf_under(&args[2], ctx, assign)
            } else {
                nested_sel_nf_under(&args[0], r, ctx, assign)
            }
        }
        _ => {
            nested_base_name(arr)?;
            Some(NestedNf::BaseRead(r))
        }
    }
}

/// Guard count at/below which the guarded lemma uses the compact
/// `by_cases … <;> … <;> simp` product form (`2^g` `simp` leaves). Above it, the
/// linear `render_guard_cascade` is used instead — `2^g` leaves would exhaust the
/// Lean heartbeat budget. `2^5 = 32` leaves compile comfortably; the historical
/// small-`g` output is preserved unchanged.
const NESTED_GUARD_PRODUCT_MAX: usize = 5;

/// Build the LINEAR cascade tactic proving the guard clause
/// `row_eq ∨ guard₂ ∨ … ∨ guard₁₊g`: case on each guard in turn; a TRUE guard
/// satisfies its own disjunct (`simp [hk]` closes), and the single all-false spine
/// reduces the `if`-tree to `row_eq` (`simp [¬all]` closes). `g + 1` leaves, each a
/// bounded `simp`. `ind` is the indentation of the outermost `by_cases` (aligned
/// under the enclosing `by`). Assumes `conds` is non-empty.
fn render_guard_cascade(conds: &[(usize, usize)], ind: &str) -> String {
    let g = conds.len();
    let all_hyps: String = (0..g)
        .map(|k| format!("h{}", 2 + k))
        .collect::<Vec<_>>()
        .join(", ");
    // Emit from the innermost guard outward so each level can embed the next.
    // `block` is the tactic text for "case on guards d..g-1", every line already
    // indented by `cur_ind`.
    fn build(d: usize, conds: &[(usize, usize)], cur_ind: &str, all_hyps: &str) -> String {
        let g = conds.len();
        let id = 2 + d;
        let (r, s) = conds[d];
        let header = format!("{cur_ind}by_cases h{id} : (m.2 {r}) = (m.2 {s})\n");
        let true_arm = format!("{cur_ind}· simp [h{id}]\n");
        let false_arm = if d + 1 == g {
            // All guards cased; the remaining goal is `row_eq` under every guard
            // false — reduce the `if`-tree with all negated hypotheses.
            format!("{cur_ind}· simp [{all_hyps}]\n")
        } else {
            // Nest the next guard's cascade under this `·`. Its own lines are
            // indented two further; the leading `by_cases` rides the bullet.
            let inner_ind = format!("{cur_ind}  ");
            let inner = build(d + 1, conds, &inner_ind, all_hyps);
            let inner_trimmed = inner
                .strip_prefix(inner_ind.as_str())
                .unwrap_or(inner.as_str());
            format!("{cur_ind}· {inner_trimmed}")
        };
        format!("{header}{true_arm}{false_arm}")
    }
    // Strip the trailing newline so the caller controls block termination.
    let body = build(0, conds, ind, &all_hyps);
    body.trim_end_matches('\n').to_string()
}

fn render_array_nested_store_lean(
    lhs_expr: &str,
    rhs_expr: &str,
    conds: &[(usize, usize)],
    hash: String,
) -> String {
    use std::fmt::Write as _;

    let g = conds.len();
    // Guard atoms occupy ids 2..=1+g; row_eq is atom 1.
    let mut guard_arms = String::new();
    for (k, (r, s)) in conds.iter().enumerate() {
        // Writing to a `String` is infallible.
        let _ = writeln!(
            &mut guard_arms,
            "  | {id} => decide ((m.2 {r}) = (m.2 {s}))",
            id = 2 + k
        );
    }
    let original: String = std::iter::once("(1, [-1])".to_string())
        .chain((0..g).map(|k| format!("({id}, [-{id}])", id = 2 + k)))
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_lits: String = (1..=1 + g)
        .map(|n| n.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = 2 + g;
    let proof_id = 3 + g;
    let proof_prems: String = (1..=lemma_id)
        .map(|n| n.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    // The guard clause `row_eq ∨ (⋁ guards)` is discharged by casing on the
    // non-reflexive `if`-conditions. For a SMALL number of guards the compact
    // product form `by_cases … <;> by_cases … <;> simp [hyps]` (2^g leaves) is
    // fine and matches the historical output; beyond the cap its 2^g `simp`
    // leaves blow the Lean heartbeat budget (e.g. a 10-store store-commute chain
    // has g = 9 → 512 leaves), so switch to a LINEAR cascade: each guard's
    // true-branch closes immediately (that disjunct is satisfied), and only the
    // single all-guards-false spine reduces the full `if`-tree to `row_eq`. O(g)
    // leaves instead of O(2^g).
    let proof_body = if g <= NESTED_GUARD_PRODUCT_MAX {
        let bycases: String = conds
            .iter()
            .enumerate()
            .map(|(k, (r, s))| format!("by_cases h{id} : (m.2 {r}) = (m.2 {s})", id = 2 + k))
            .collect::<Vec<_>>()
            .join(" <;> ");
        let hyps: String = (0..g)
            .map(|k| format!("h{}", 2 + k))
            .collect::<Vec<_>>()
            .join(", ");
        format!("  {bycases} <;>\n    simp [{hyps}]")
    } else {
        render_guard_cascade(conds, "  ")
    };
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — NESTED / multi-store array
  read-over-write conflict, grounded in the verified `firewall_combined_unsat`.
  `select` over a `store`-chain unfolds to nested raw `if`-updates that mirror
  the McCarthy read-over-write axioms; under the asserted index disequalities
  both sides reduce to the same value, so `LHS ≠ RHS` is refuted. Reconstructed
  from the frontend assertions
  (ay refutes arrays eagerly as bare-trust). Model: `(Nat → Nat) × (Nat → Nat)` =
  base array × scalar valuation (`m.1` the array, `m.2 k` the k-th index/element).
  The theory lemma is the guarded clause `row_eq ∨ (⋁ index-coincidences)`, valid
  by `by_cases` on each non-reflexive `if`-condition + `simp`. Pure Lean 4 core.
-/
namespace AySoundness.Emitted.ArrNested_{hash}
open AySoundness

abbrev Val := (Nat → Nat) × (Nat → Nat)

-- atom 1 = (LHS = RHS) after unfolding select-over-store to nested if-updates;
-- atoms 2.. = the non-reflexive index coincidences (read = store) that guard it.
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ({lhs_expr} = {rhs_expr})
{guard_arms}  | _ => false

def original : List (Cid × Clause) := [{original}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof_id}, [], [{proof_prems}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
{proof_body}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- The nested read-over-write conflict has no model — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrNested_{hash}
"#,
    )
}

/// Render the Lean for an UNCONDITIONAL array read-over-write identity: the two
/// `select`-over-`store` `if`-trees `LHS`/`RHS` are provably equal for EVERY model
/// (the caller has confirmed agreement under all guard assignments via
/// `nested_trees_unconditionally_equal`). Unlike the guarded emitter, there is NO
/// index-coincidence guard clause — the theory lemma is the bare `row_eq`
/// (clause `[1]`), discharged by `by_cases` on each non-reflexive `if`-condition
/// `<;> simp` (or a single `simp` when the tree is fully reflexive, `g = 0`).
/// Same verified `firewall_combined_unsat` grounding and functional array model
/// `(Nat → Nat) × (Nat → Nat)` as the ROW1 / guarded emitters. Covers
/// `store`-idempotence (`select (store (store a i v) i v) j = select (store a i v) j`)
/// and reflexive single-store ROW1 shapes exposed after inlining an array-let /
/// macro (`select (store a i e) i = e`).
fn render_array_unconditional_lean(
    lhs_expr: &str,
    rhs_expr: &str,
    conds: &[(usize, usize)],
    hash: String,
) -> String {
    let proof_body = if conds.is_empty() {
        // Fully reflexive: `if x = x then a else b` reduces by `simp` directly.
        "  simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]".to_string()
    } else {
        let bycases: String = conds
            .iter()
            .enumerate()
            .map(|(k, (r, s))| format!("by_cases h{id} : (m.2 {r}) = (m.2 {s})", id = 2 + k))
            .collect::<Vec<_>>()
            .join(" <;> ");
        let hyps: String = (0..conds.len())
            .map(|k| format!("h{}", 2 + k))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]\n  {bycases} <;>\n    simp [{hyps}]"
        )
    };
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — UNCONDITIONAL array read-over-write
  identity, grounded in the verified `firewall_combined_unsat`. `select` over a
  `store`-chain unfolds to nested raw `if`-updates; the two sides reduce to the
  SAME value for EVERY index valuation (e.g. `store` idempotence, or a reflexive
  single-store ROW1 `select (store a i e) i = e`), so `LHS ≠ RHS` is refuted with
  NO guarding disequality. Reconstructed from the frontend assertions (ay refutes
  arrays eagerly as bare-trust). Model: `(Nat → Nat) × (Nat → Nat)` = base array ×
  scalar valuation. The theory lemma is the unconditional `row_eq` (clause `[1]`),
  valid by `by_cases` on each non-reflexive `if`-condition + `simp`. Pure Lean 4
  core.
-/
namespace AySoundness.Emitted.ArrUncond_{hash}
open AySoundness

abbrev Val := (Nat → Nat) × (Nat → Nat)

-- atom 1 = (LHS = RHS) after unfolding select-over-store to nested if-updates;
-- the equality holds for ALL m (no index-coincidence guard is needed).
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ({lhs_expr} = {rhs_expr})
  | _ => false

def original : List (Cid × Clause) := [(1, [-1])]
def lemmas   : List (Cid × Clause) := [(2, [1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [1] = true := by
{proof_body}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- The unconditional read-over-write identity has no countermodel — via the
    firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrUncond_{hash}
"#,
    )
}

/// A `Symbol` / nullary-application array name.
fn ax_sym_name(t: &PTerm) -> Option<&str> {
    match t {
        PTerm::Symbol(s) => Some(s.as_str()),
        PTerm::App(f, a) if a.is_empty() => Some(f.as_str()),
        _ => None,
    }
}

/// All `(symbol, store-term)` bindings from `(= sym (store …))` /
/// `(= (store …) sym)` assertions — the array-let facts a transitive
/// read-over-write conflict is reconstructed through.
fn ax_array_store_bindings(parsed: &[PTerm]) -> Vec<(&str, &PTerm)> {
    let mut out: Vec<(&str, &PTerm)> = Vec::new();
    for asrt in parsed {
        let Some((p, q)) = ax_as_eq2(asrt) else {
            continue;
        };
        for (s, store) in [(p, q), (q, p)] {
            if let Some(name) = ax_sym_name(s) {
                if ax_as_store3(store).is_some() {
                    out.push((name, store));
                }
            }
        }
    }
    out
}

/// `(not (= p q))` asserted (either orientation)?
fn ax_has_diseq(parsed: &[PTerm], p: &PTerm, q: &PTerm) -> bool {
    parsed.iter().any(
        |t| matches!(ax_as_not_eq2(t), Some((x, y)) if (x == p && y == q) || (x == q && y == p)),
    )
}

/// **conflicting stores** (ROW-1 through a shared array variable,
/// `ArrayThy.sel_upd_same`): a variable bound to two stores at the SAME index
/// with distinct values — `X = store b i e1`, `X = store b i e2`, `e1 ≠ e2` —
/// forces `store b i e1 = store b i e2`, whose read at `i` gives `e1 = e2`.
/// Covers `conflicting_stores.smt2`.
pub(crate) fn emit_array_conflicting_stores_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    let bindings = ax_array_store_bindings(parsed);
    for a in 0..bindings.len() {
        for b in (a + 1)..bindings.len() {
            let (x1, s1) = bindings[a];
            let (x2, s2) = bindings[b];
            if x1 != x2 {
                continue; // must be the SAME array variable to force `s1 = s2`
            }
            let (Some((_, i1, e1)), Some((_, i2, e2))) = (ax_as_store3(s1), ax_as_store3(s2))
            else {
                continue;
            };
            // Same store index (else `e1 = e2` does not follow) and an asserted
            // value disequality to contradict.
            if i1 == i2 && e1 != e2 && ax_has_diseq(parsed, e1, e2) {
                return Some(render_array_conflicting_stores_lean(fnv_hex(&format!(
                    "conflicting_stores:{x1}:{s1:?}{s2:?}"
                ))));
            }
        }
    }
    None
}

fn render_array_conflicting_stores_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — CONFLICTING STORES (ROW-1 through a
  shared array variable), grounded in the verified `firewall_combined_unsat`.
  `x = store b1 i e1`, `x = store b2 i e2`, `e1 ≠ e2` are unsatisfiable: the two
  bindings force `store b1 i e1 = store b2 i e2`, and reading index `i` gives
  `e1 = sel (upd b1 i e1) i = sel (upd b2 i e2) i = e2` (the mirror of
  `AySoundness.ArrayThy.sel_upd_same`). Reconstructed from the frontend assertions
  (ay refutes arrays eagerly as bare-trust). Arrays are `Nat → Nat`, `store` the
  `if`-update; the store equalities are function equalities (`decide` over
  `Classical.propDecidable`). Axioms ⊆ {{propext, Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.ArrConflStores_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
  x : Nat -> Nat
  b1 : Nat -> Nat
  b2 : Nat -> Nat
  i : Nat
  e1 : Nat
  e2 : Nat

-- atom 1 = (x = store b1 i e1); atom 2 = (x = store b2 i e2); atom 3 = (e1 = e2).
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.x = (fun j => if j = m.i then m.e1 else m.b1 j))
  | 2 => decide (m.x = (fun j => if j = m.i then m.e2 else m.b2 j))
  | 3 => decide (m.e1 = m.e2)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]
def lemmas   : List (Cid × Clause) := [(4, [-1, -2, 3])]
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1, -2, 3] = true := by
  by_cases h1 : m.x = (fun j => if j = m.i then m.e1 else m.b1 j)
  · by_cases h2 : m.x = (fun j => if j = m.i then m.e2 else m.b2 j)
    · have he : m.e1 = m.e2 := by
        have hc := congrFun (h1.symm.trans h2) m.i
        simpa using hc
      simp [clauseSat, litSat, atomVal, he]
    · simp [clauseSat, litSat, atomVal, h2]
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- `x = store b1 i e1 ∧ x = store b2 i e2 ∧ e1 ≠ e2` is unsatisfiable — via the
    firewall (ROW-1). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrConflStores_{hash}
"#,
    )
}

/// **diamond conflict** (store-eq ⇒ ROW-1 vs ROW-2 at one index): two variables
/// bound to stores over a COMMON base that are asserted equal —
/// `b = store a i v`, `c = store a j w`, `b = c`, `i ≠ j` — force
/// `store a i v = store a j w`; reading index `i` gives
/// `v = sel (upd a i v) i = sel (upd a j w) i = sel a i` (ROW-1 on the left,
/// ROW-2 on the right under `i ≠ j`), contradicting `v ≠ select a i`.
/// Covers `diamond_conflict.smt2`.
pub(crate) fn emit_array_diamond_conflict_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    let bindings = ax_array_store_bindings(parsed);
    let binding_of = |name: &str| -> Option<&PTerm> {
        bindings.iter().find(|(n, _)| *n == name).map(|(_, s)| *s)
    };
    for asrt in parsed {
        // `(= b c)` between two DISTINCT array symbols, each bound to a store.
        let Some((p, q)) = ax_as_eq2(asrt) else {
            continue;
        };
        let (Some(bn), Some(cn)) = (ax_sym_name(p), ax_sym_name(q)) else {
            continue;
        };
        if bn == cn {
            continue;
        }
        let (Some(sb), Some(sc)) = (binding_of(bn), binding_of(cn)) else {
            continue;
        };
        let (Some((ab, ib, vb)), Some((ac, ic, vc))) = (ax_as_store3(sb), ax_as_store3(sc)) else {
            continue;
        };
        // Same base array and an asserted index disequality (so ROW-2 leaves the
        // base at the other index).
        if ab != ac || ib == ic || !ax_has_diseq(parsed, ib, ic) {
            continue;
        }
        // One side asserts its stored value differs from the base read at its own
        // index — the contradiction ROW forces to equality.
        for (base, idx, val) in [(ab, ib, vb), (ac, ic, vc)] {
            let sel = PTerm::App("select".to_string(), vec![base.clone(), idx.clone()]);
            if ax_has_diseq(parsed, val, &sel) {
                return Some(render_array_diamond_conflict_lean(fnv_hex(&format!(
                    "diamond:{asrt:?}{sb:?}{sc:?}"
                ))));
            }
        }
    }
    None
}

fn render_array_diamond_conflict_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DIAMOND conflict (store-equality ⇒ ROW-1
  vs ROW-2 at one index), grounded in the verified `firewall_combined_unsat`.
  `b = store a i v`, `c = store a j w`, `b = c`, `i ≠ j`, `v ≠ select a i` are
  unsatisfiable: the bindings force `store a i v = store a j w`, and reading index
  `i` gives `v = sel (upd a i v) i = sel (upd a j w) i = sel a i` (ROW-1 on the
  left; ROW-2 on the right, since `i ≠ j` — the mirror of
  `AySoundness.ArrayThy.sel_upd_same`/`sel_upd_other`), contradicting
  `v ≠ select a i`. Reconstructed from the frontend assertions (ay refutes arrays
  eagerly as bare-trust). Arrays are `Nat → Nat`, `store` the `if`-update; the
  store equality is a function equality (`decide` over `Classical.propDecidable`).
  Axioms ⊆ {{propext, Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.ArrDiamond_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
  a : Nat -> Nat
  i : Nat
  j : Nat
  v : Nat
  w : Nat

-- atom 1 = (store a i v = store a j w); atom 2 = (i = j); atom 3 = (v = select a i).
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((fun t => if t = m.i then m.v else m.a t) = (fun t => if t = m.j then m.w else m.a t))
  | 2 => decide (m.i = m.j)
  | 3 => decide (m.v = m.a m.i)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [-2]), (3, [-3])]
def lemmas   : List (Cid × Clause) := [(4, [-1, 2, 3])]
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2, 3] = true := by
  by_cases h1 : (fun t => if t = m.i then m.v else m.a t) = (fun t => if t = m.j then m.w else m.a t)
  · by_cases h2 : m.i = m.j
    · simp [clauseSat, litSat, atomVal, h2]
    · have hv : m.v = m.a m.i := by
        have hc := congrFun h1 m.i
        simp [h2] at hc
        exact hc
      simp [clauseSat, litSat, atomVal, hv]
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- `store a i v = store a j w ∧ i ≠ j ∧ v ≠ select a i` is unsatisfiable — via
    the firewall (ROW-1 / ROW-2). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrDiamond_{hash}
"#,
    )
}

// ===========================================================================
// QF_AX extensionality / read-over-write / congruence firewall emitters.
//
// Six fail-closed matchers over the FRONTEND parsed assertions, each grounding
// the corresponding McCarthy-array conflict through the verified
// `firewall_combined_unsat`. Arrays are the standard functional model
// (`Nat → Nat`, `select` = application, `store` = `if`-update), indices/values
// are `Nat`; extensionality atoms are function equalities (`decide` over the
// `Classical.propDecidable` instance, hence `noncomputable atomVal`). Every
// rendered theorem kernel-checks with axioms ⊆ {propext, Classical.choice,
// Quot.sound} — the mirror of `AySoundness.ArrayThy`
// (`ext_nonvacuous` / `sel_upd_same` / `sel_upd_other`), whose own proofs
// discharge exactly these obligations.
// ===========================================================================

/// `(= X Y)` → `(X, Y)`.
fn ax_as_eq2(t: &PTerm) -> Option<(&PTerm, &PTerm)> {
    let PTerm::App(op, a) = t else { return None };
    (op == "=" && a.len() == 2).then(|| (&a[0], &a[1]))
}

/// `(not (= X Y))` → `(X, Y)`.
fn ax_as_not_eq2(t: &PTerm) -> Option<(&PTerm, &PTerm)> {
    let PTerm::App(op, a) = t else { return None };
    if op != "not" || a.len() != 1 {
        return None;
    }
    ax_as_eq2(&a[0])
}

/// `(store A I V)` → `(A, I, V)`.
fn ax_as_store3(t: &PTerm) -> Option<(&PTerm, &PTerm, &PTerm)> {
    let PTerm::App(op, a) = t else { return None };
    (op == "store" && a.len() == 3).then(|| (&a[0], &a[1], &a[2]))
}

/// `(select A I)` → `(A, I)`.
fn ax_as_select2(t: &PTerm) -> Option<(&PTerm, &PTerm)> {
    let PTerm::App(op, a) = t else { return None };
    (op == "select" && a.len() == 2).then(|| (&a[0], &a[1]))
}

/// **write-back identity** (`ArrayThy.ext_nonvacuous`):
/// `(not (= (store a i (select a i)) a))` — storing the value already present is
/// a no-op, refuted by extensionality with the bounded `j = i` / `j ≠ i` split.
/// Covers `write_back_identity.smt2`, `storeinv_minimal.smt2`,
/// `store_select_inverse.smt2` (byte-identical assertion).
pub(crate) fn emit_array_write_back_identity_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    for asrt in parsed {
        let Some((lhs, rhs)) = ax_as_not_eq2(asrt) else {
            continue;
        };
        // `(store a i (select a i)) = a` in either orientation.
        for (store_side, a_side) in [(lhs, rhs), (rhs, lhs)] {
            let Some((sa, si, sv)) = ax_as_store3(store_side) else {
                continue;
            };
            let Some((va, vi)) = ax_as_select2(sv) else {
                continue;
            };
            // stored value is `select a i` over the SAME base + index, and the
            // other side of the disequality is that same base array.
            if sa == va && si == vi && a_side == sa {
                return Some(render_array_write_back_lean(fnv_hex(&format!("{asrt:?}"))));
            }
        }
    }
    None
}

fn render_array_write_back_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — array WRITE-BACK identity, grounded in
  the verified `firewall_combined_unsat`. The assertion
  `store a i (select a i) ≠ a` contradicts extensionality: storing the value
  already present at `i` is a no-op (`upd a i (sel a i) = a`, the mirror of
  `AySoundness.ArrayThy.ext_nonvacuous`, whose proof does the same `j = i` /
  `j ≠ i` by_cases). Reconstructed from the frontend assertions (ay refutes
  arrays eagerly as bare-trust). Arrays are `Nat → Nat`, `select` application,
  `store` the `if`-update; the extension equality is a function equality (`decide`
  over `Classical.propDecidable`). Axioms ⊆ {{propext, Classical.choice,
  Quot.sound}}.
-/
namespace AySoundness.Emitted.ArrWriteBack_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
  a : Nat -> Nat
  i : Nat

-- atom 1 = (store a i (select a i) = a) = ((fun j => if j = i then a i else a j) = a).
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((fun j => if j = m.i then m.a m.i else m.a j) = m.a)
  | _ => false

def original : List (Cid × Clause) := [(1, [-1])]
def lemmas   : List (Cid × Clause) := [(2, [1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [1] = true := by
  have hp : (fun j => if j = m.i then m.a m.i else m.a j) = m.a := by
    funext j
    by_cases h : j = m.i
    · subst h; simp
    · simp [h]
  simp [clauseSat, litSat, atomVal, hp]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- `store a i (select a i) ≠ a` is unsatisfiable — via the firewall (extensionality). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrWriteBack_{hash}
"#,
    )
}

/// **store-eq ⇒ value-eq** (ROW-1 on both sides, `ArrayThy.sel_upd_same`):
/// `(= (store a i v) (store b i w))` with `(not (= v w))` — applying `select` at
/// the shared index `i` reduces both sides to the stored value, so `v = w`.
/// Covers `store_eq_implies_select_eq.smt2`, `conflicting_stores.smt2`.
pub(crate) fn emit_array_store_eq_select_eq_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    for eq_asrt in parsed {
        let Some((x, y)) = ax_as_eq2(eq_asrt) else {
            continue;
        };
        let (Some((_a, i1, v)), Some((_b, i2, w))) = (ax_as_store3(x), ax_as_store3(y)) else {
            continue;
        };
        // The two stores MUST be at the same index — otherwise `v = w` does not
        // follow (declining is fail-closed).
        if i1 != i2 {
            continue;
        }
        let has_diseq = parsed.iter().any(|t| {
            matches!(ax_as_not_eq2(t), Some((p, q)) if (p == v && q == w) || (p == w && q == v))
        });
        if has_diseq {
            return Some(render_array_store_eq_select_eq_lean(fnv_hex(&format!(
                "{eq_asrt:?}"
            ))));
        }
    }
    None
}

fn render_array_store_eq_select_eq_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — store-equality ⇒ value-equality
  (ROW-1 on both sides), grounded in the verified `firewall_combined_unsat`.
  `store a i v = store b i w` with `v ≠ w` is unsatisfiable: reading index `i`
  gives `v = sel (upd a i v) i = sel (upd b i w) i = w` (the mirror of
  `AySoundness.ArrayThy.sel_upd_same`). Reconstructed from the frontend
  assertions (ay refutes arrays eagerly as bare-trust). Arrays are `Nat → Nat`,
  `store` the `if`-update; the store equality is a function equality (`decide`
  over `Classical.propDecidable`). Axioms ⊆ {{propext, Classical.choice,
  Quot.sound}}.
-/
namespace AySoundness.Emitted.ArrStoreEqSel_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
  a : Nat -> Nat
  b : Nat -> Nat
  i : Nat
  v : Nat
  w : Nat

-- atom 1 = (store a i v = store b i w); atom 2 = (v = w).
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((fun j => if j = m.i then m.v else m.a j) = (fun j => if j = m.i then m.w else m.b j))
  | 2 => decide (m.v = m.w)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [-2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, 2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2] = true := by
  by_cases h1 : (fun j => if j = m.i then m.v else m.a j) = (fun j => if j = m.i then m.w else m.b j)
  · have hi : m.v = m.w := by have h := congrFun h1 m.i; simpa using h
    simp [clauseSat, litSat, atomVal, hi]
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- `store a i v = store b i w ∧ v ≠ w` is unsatisfiable — via the firewall (ROW-1). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrStoreEqSel_{hash}
"#,
    )
}

/// **store-eq ⇒ base-eq at other index** (ROW-2 on both sides,
/// `ArrayThy.sel_upd_other`): `(= (store a i v) (store b i w))`, `(not (= i j))`,
/// `(not (= (select a j) (select b j)))` — under `i ≠ j`, reading index `j`
/// leaves both bases, so `select a j = select b j`.
/// Covers `store_eq_implies_base_eq_at_other.smt2`.
pub(crate) fn emit_array_store_eq_base_other_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    for eq_asrt in parsed {
        let Some((x, y)) = ax_as_eq2(eq_asrt) else {
            continue;
        };
        let (Some((a, i1, _v)), Some((b, i2, _w))) = (ax_as_store3(x), ax_as_store3(y)) else {
            continue;
        };
        if i1 != i2 {
            continue;
        }
        let i = i1;
        for neg in parsed {
            let Some((p, q)) = ax_as_not_eq2(neg) else {
                continue;
            };
            // `(not (= i j))` — one operand is the store index `i`, the other is
            // the distinct read index `j`.
            let j = if p == i {
                q
            } else if q == i {
                p
            } else {
                continue;
            };
            if j == i {
                continue;
            }
            // `(not (= (select a j) (select b j)))` over the two store bases.
            let has_sel = parsed.iter().any(|t| {
                let Some((s1, s2)) = ax_as_not_eq2(t) else {
                    return false;
                };
                let (Some((sa, sj1)), Some((sb, sj2))) = (ax_as_select2(s1), ax_as_select2(s2))
                else {
                    return false;
                };
                sj1 == j && sj2 == j && ((sa == a && sb == b) || (sa == b && sb == a))
            });
            if has_sel {
                return Some(render_array_store_eq_base_other_lean(fnv_hex(&format!(
                    "{eq_asrt:?}{neg:?}"
                ))));
            }
        }
    }
    None
}

fn render_array_store_eq_base_other_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — store-equality ⇒ base-equality at a
  DISTINCT index (ROW-2 on both sides), grounded in the verified
  `firewall_combined_unsat`. `store a i v = store b i w` with `i ≠ j` forces
  `select a j = select b j`: reading the untouched index `j` leaves each base
  (the mirror of `AySoundness.ArrayThy.sel_upd_other`), so the asserted
  disequality is refuted. Reconstructed from the frontend assertions (ay refutes
  arrays eagerly as bare-trust). Arrays are `Nat → Nat`, `store` the `if`-update;
  the store equality is a function equality (`decide` over
  `Classical.propDecidable`). Axioms ⊆ {{propext, Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.ArrStoreEqOther_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
  a : Nat -> Nat
  b : Nat -> Nat
  i : Nat
  j : Nat
  v : Nat
  w : Nat

-- atom 1 = (store a i v = store b i w); atom 2 = (i = j); atom 3 = (select a j = select b j).
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((fun k => if k = m.i then m.v else m.a k) = (fun k => if k = m.i then m.w else m.b k))
  | 2 => decide (m.i = m.j)
  | 3 => decide (m.a m.j = m.b m.j)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [-2]), (3, [-3])]
def lemmas   : List (Cid × Clause) := [(4, [-1, 2, 3])]
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2, 3] = true := by
  by_cases h2 : m.i = m.j
  · simp [clauseSat, litSat, atomVal, h2]
  · by_cases h1 : (fun k => if k = m.i then m.v else m.a k) = (fun k => if k = m.i then m.w else m.b k)
    · have hj := congrFun h1 m.j
      rw [if_neg (fun hji => h2 hji.symm), if_neg (fun hji => h2 hji.symm)] at hj
      simp [clauseSat, litSat, atomVal, hj]
    · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- `store a i v = store b i w ∧ i ≠ j ∧ select a j ≠ select b j` is unsatisfiable
    — via the firewall (ROW-2). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrStoreEqOther_{hash}
"#,
    )
}

/// **array-eq ⇒ select-eq** (select congruence, `ArrayThy.sel`/`congrFun`):
/// `(= a b)`, `(not (= (select a i) (select b i)))` — `a = b` forces
/// `select a i = select b i`. Covers `array_eq_select.smt2`.
pub(crate) fn emit_array_eq_select_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    for neg in parsed {
        let Some((s1, s2)) = ax_as_not_eq2(neg) else {
            continue;
        };
        let (Some((a, i1)), Some((b, i2))) = (ax_as_select2(s1), ax_as_select2(s2)) else {
            continue;
        };
        // Distinct arrays, shared read index; the array equality must be asserted.
        if i1 != i2 || a == b {
            continue;
        }
        let has_eq = parsed.iter().any(
            |t| matches!(ax_as_eq2(t), Some((p, q)) if (p == a && q == b) || (p == b && q == a)),
        );
        if has_eq {
            return Some(render_array_eq_select_lean(fnv_hex(&format!("{neg:?}"))));
        }
    }
    None
}

fn render_array_eq_select_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — array-equality ⇒ select-equality
  (select congruence), grounded in the verified `firewall_combined_unsat`.
  `a = b` with `select a i ≠ select b i` is unsatisfiable: equal arrays read
  equally at every index (`congrFun` over the functional `sel = ·`). Reconstructed
  from the frontend assertions (ay refutes arrays eagerly as bare-trust). Arrays
  are `Nat → Nat`, `select` application; the array equality is a function
  equality (`decide` over `Classical.propDecidable`). Axioms ⊆ {{propext,
  Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.ArrEqSel_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
  a : Nat -> Nat
  b : Nat -> Nat
  i : Nat

-- atom 1 = (a = b); atom 2 = (select a i = select b i).
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.a = m.b)
  | 2 => decide (m.a m.i = m.b m.i)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [-2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, 2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2] = true := by
  by_cases h1 : m.a = m.b
  · have hi := congrFun h1 m.i
    simp [clauseSat, litSat, atomVal, hi]
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- `a = b ∧ select a i ≠ select b i` is unsatisfiable — via the firewall (congruence). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrEqSel_{hash}
"#,
    )
}

/// **array-eq ⇒ store-eq** (store congruence, `ArrayThy.upd`/`congrArg`):
/// `(= a b)`, `(not (= (store a i v) (store b i v)))` — `a = b` forces the two
/// updates equal. Covers `ext_congruence.smt2`.
pub(crate) fn emit_array_store_congruence_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    for neg in parsed {
        let Some((x, y)) = ax_as_not_eq2(neg) else {
            continue;
        };
        let (Some((a, i1, v1)), Some((b, i2, v2))) = (ax_as_store3(x), ax_as_store3(y)) else {
            continue;
        };
        // Same index + same stored value + distinct bases; `a = b` must be asserted.
        if i1 != i2 || v1 != v2 || a == b {
            continue;
        }
        let has_eq = parsed.iter().any(
            |t| matches!(ax_as_eq2(t), Some((p, q)) if (p == a && q == b) || (p == b && q == a)),
        );
        if has_eq {
            return Some(render_array_store_congruence_lean(fnv_hex(&format!(
                "{neg:?}"
            ))));
        }
    }
    None
}

fn render_array_store_congruence_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — array-equality ⇒ store-equality
  (store congruence), grounded in the verified `firewall_combined_unsat`.
  `a = b` with `store a i v ≠ store b i v` is unsatisfiable: equal arrays give
  equal updates (`congrArg` over the functional `upd`). Reconstructed from the
  frontend assertions (ay refutes arrays eagerly as bare-trust). Arrays are
  `Nat → Nat`, `store` the `if`-update; the (dis)equalities are function
  equalities (`decide` over `Classical.propDecidable`). Axioms ⊆ {{propext,
  Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.ArrStoreCong_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
  a : Nat -> Nat
  b : Nat -> Nat
  i : Nat
  v : Nat

-- atom 1 = (a = b); atom 2 = (store a i v = store b i v).
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.a = m.b)
  | 2 => decide ((fun j => if j = m.i then m.v else m.a j) = (fun j => if j = m.i then m.v else m.b j))
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [-2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, 2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2] = true := by
  by_cases h1 : m.a = m.b
  · have h2 : (fun j => if j = m.i then m.v else m.a j) = (fun j => if j = m.i then m.v else m.b j) := by
      rw [h1]
    simp [clauseSat, litSat, atomVal, h2]
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- `a = b ∧ store a i v ≠ store b i v` is unsatisfiable — via the firewall (congruence). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrStoreCong_{hash}
"#,
    )
}

/// State for the equality-chain ROW-1 emitter: registries assigning a distinct
/// model field to each array-symbol / scalar-symbol leaf, in first-appearance
/// order. Array leaves become `m.arr{k}` (`Nat → Nat`); scalar leaves become
/// `m.sca{k}` (`Nat`). The two namespaces are disjoint (a QF_AX symbol has a
/// single sort); a name appearing in both aborts the render (fail-closed).
struct ChainCtx {
    arrs: Vec<String>,
    scalars: Vec<String>,
    collision: bool,
}

impl ChainCtx {
    fn new() -> Self {
        ChainCtx {
            arrs: Vec::new(),
            scalars: Vec::new(),
            collision: false,
        }
    }

    fn arr_field(&mut self, name: &str) -> String {
        if self.scalars.iter().any(|s| s == name) {
            self.collision = true;
        }
        let k = if let Some(p) = self.arrs.iter().position(|s| s == name) {
            p
        } else {
            self.arrs.push(name.to_string());
            self.arrs.len() - 1
        };
        format!("m.arr{k}")
    }

    fn scalar_field(&mut self, name: &str) -> String {
        if self.arrs.iter().any(|s| s == name) {
            self.collision = true;
        }
        let k = if let Some(p) = self.scalars.iter().position(|s| s == name) {
            p
        } else {
            self.scalars.push(name.to_string());
            self.scalars.len() - 1
        };
        format!("m.sca{k}")
    }
}

/// Leaf symbol name (a `Symbol` or a nullary application); `None` for a compound.
fn ax_leaf_name(t: &PTerm) -> Option<&str> {
    match t {
        PTerm::Symbol(s) => Some(s.as_str()),
        PTerm::App(f, args) if args.is_empty() => Some(f.as_str()),
        _ => None,
    }
}

/// Render an array-valued term into a Lean expression over the model fields:
/// a leaf → its `m.arr{k}` field; a `(store A I V)` → the raw `if`-update
/// `(fun j => if j = <I> then <V> else <A> j)`. `None` for any other shape.
fn ax_render_arr(t: &PTerm, ctx: &mut ChainCtx) -> Option<String> {
    if let Some((a, i, v)) = ax_as_store3(t) {
        let ia = ax_render_scalar(i, ctx)?;
        let va = ax_render_scalar(v, ctx)?;
        let aa = ax_render_arr(a, ctx)?;
        Some(format!("(fun j => if j = {ia} then {va} else {aa} j)"))
    } else {
        ax_leaf_name(t).map(|name| ctx.arr_field(name))
    }
}

/// Render a scalar (index/element) leaf into its `m.sca{k}` field. Only leaf
/// symbols are supported (declines compound scalar terms — fail-closed).
fn ax_render_scalar(t: &PTerm, ctx: &mut ChainCtx) -> Option<String> {
    ax_leaf_name(t).map(|name| ctx.scalar_field(name))
}

/// **equality-chain ⇒ ROW-1** (`Eq.trans` chain + `ArrayThy.sel_upd_same`):
/// `(not (= (select a i) v))` where `a` reaches a `(store c i v)` term through a
/// chain of asserted array equalities (e.g. `a = b`, `b = store c i v`). Follows
/// the chain, rewrites the read array to the store, and discharges by ROW-1.
/// Covers `eq_chain_four_arrays.smt2`.
pub(crate) fn emit_array_eq_chain_row1_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    for neg in parsed {
        let Some((p, q)) = ax_as_not_eq2(neg) else {
            continue;
        };
        for (sel_t, val_t) in [(p, q), (q, p)] {
            let Some((arr0, idx)) = ax_as_select2(sel_t) else {
                continue;
            };
            // BFS over the asserted array equalities from `arr0` to a
            // `(store _ idx val_t)` term.
            let mut nodes: Vec<&PTerm> = vec![arr0];
            let mut pred: Vec<Option<usize>> = vec![None];
            let mut found: Option<usize> = None;
            let mut head = 0;
            while head < nodes.len() {
                let cur = nodes[head];
                if let Some((_c, si, sv)) = ax_as_store3(cur) {
                    if si == idx && sv == val_t {
                        found = Some(head);
                        break;
                    }
                }
                for t in parsed {
                    if let Some((x, y)) = ax_as_eq2(t) {
                        for (from, to) in [(x, y), (y, x)] {
                            if from == cur && !nodes.iter().any(|n| *n == to) {
                                nodes.push(to);
                                pred.push(Some(head));
                            }
                        }
                    }
                }
                head += 1;
            }
            let Some(mut fi) = found else {
                continue;
            };
            // Reconstruct the oriented path arr0 = … = store.
            let mut path: Vec<usize> = vec![fi];
            while let Some(pp) = pred[fi] {
                path.push(pp);
                fi = pp;
            }
            path.reverse();
            // Require at least one equality edge (a direct `select (store …) i`
            // is the ROW-1 emitter's job — decline here, fail-closed).
            if path.len() < 2 {
                continue;
            }
            if let Some(lean) = render_array_eq_chain_row1_lean(
                &path.iter().map(|&pi| nodes[pi]).collect::<Vec<_>>(),
                idx,
                val_t,
                fnv_hex(&format!("{neg:?}")),
            ) {
                return Some(lean);
            }
        }
    }
    None
}

fn render_array_eq_chain_row1_lean(
    path: &[&PTerm],
    idx: &PTerm,
    val: &PTerm,
    hash: String,
) -> Option<String> {
    use std::fmt::Write as _;
    let mut ctx = ChainCtx::new();
    // Render every path node once; edges relate consecutive nodes.
    let node_exprs: Vec<String> = path
        .iter()
        .map(|t| ax_render_arr(t, &mut ctx))
        .collect::<Option<Vec<_>>>()?;
    let idx_field = ax_render_scalar(idx, &mut ctx)?;
    let val_field = ax_render_scalar(val, &mut ctx)?;
    if ctx.collision {
        return None;
    }
    let k = node_exprs.len() - 1; // number of edges
    if k == 0 {
        return None;
    }
    let sel_atom = k + 1;

    // Struct fields.
    let mut fields = String::new();
    for a in 0..ctx.arrs.len() {
        let _ = writeln!(&mut fields, "  arr{a} : Nat -> Nat");
    }
    for s in 0..ctx.scalars.len() {
        let _ = writeln!(&mut fields, "  sca{s} : Nat");
    }

    // atomVal arms: edges 1..k, then the select-value atom.
    let mut arms = String::new();
    for m in 1..=k {
        let _ = writeln!(
            &mut arms,
            "  | {m} => decide ({lhs} = {rhs})",
            lhs = node_exprs[m - 1],
            rhs = node_exprs[m]
        );
    }
    let arr0 = &node_exprs[0];
    let _ = writeln!(
        &mut arms,
        "  | {sel_atom} => decide ({arr0} {idx_field} = {val_field})"
    );

    // Clauses.
    let original: String = (1..=k)
        .map(|m| format!("({m}, [{m}])"))
        .chain(std::iter::once(format!("({sel_atom}, [-{sel_atom}])")))
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = sel_atom + 1;
    let proof_id = lemma_id + 1;
    let lemma_lits: String = (1..=k)
        .map(|m| format!("-{m}"))
        .chain(std::iter::once(sel_atom.to_string()))
        .collect::<Vec<_>>()
        .join(", ");
    let proof_prems: String = (1..=k)
        .map(|m| m.to_string())
        .chain([sel_atom.to_string(), lemma_id.to_string()])
        .collect::<Vec<_>>()
        .join(", ");

    // lemma_valid: cascade of by_cases on each edge; all-true leaf chains the
    // equalities (Eq.trans) then reads at `idx` (ROW-1).
    let trans_chain: String = if k == 1 {
        "h1".to_string()
    } else {
        let mut s = format!("h{k}");
        for m in (1..k).rev() {
            s = format!("h{m}.trans ({s})");
        }
        s
    };
    let store_expr = &node_exprs[k];
    // The all-edges-true leaf: chain the equalities and read at `idx` (ROW-1).
    // Rendered as three lines at a given indent (the first line rides the `·`
    // bullet at the call site).
    let leaf_at = |ind: &str| -> String {
        format!(
            "{ind}have hchain : {arr0} = {store_expr} := {trans_chain}\n\
             {ind}have hi : {arr0} {idx_field} = {val_field} := by have h := congrFun hchain {idx_field}; simpa using h\n\
             {ind}simp [clauseSat, litSat, atomVal, hi]\n"
        )
    };
    // Recursive by_cases cascade: each edge's TRUE branch continues to the next
    // edge (or the leaf); its FALSE branch closes immediately (that negative
    // disjunct is satisfied). Every returned line is prefixed with `ind`.
    fn build(
        d: usize,
        k: usize,
        ind: &str,
        edge_props: &[String],
        leaf_at: &dyn Fn(&str) -> String,
    ) -> String {
        let inner_ind = format!("{ind}  ");
        let header = format!("{ind}by_cases h{d} : ({})\n", edge_props[d - 1]);
        // TRUE branch: the nested cascade / leaf, first line riding the bullet.
        let true_block = if d == k {
            leaf_at(&inner_ind)
        } else {
            build(d + 1, k, &inner_ind, edge_props, leaf_at)
        };
        let true_trimmed = true_block
            .strip_prefix(inner_ind.as_str())
            .unwrap_or(true_block.as_str());
        let true_arm = format!("{ind}· {true_trimmed}");
        // FALSE branch: that edge is false ⇒ `-d` literal satisfied.
        let false_arm = format!("{ind}· simp [clauseSat, litSat, atomVal, h{d}]\n");
        format!("{header}{true_arm}{false_arm}")
    }
    let edge_props: Vec<String> = (1..=k)
        .map(|m| format!("{} = {}", node_exprs[m - 1], node_exprs[m]))
        .collect();
    let proof_body = build(1, k, "  ", &edge_props, &leaf_at);
    let proof_body = proof_body.trim_end_matches('\n');

    Some(format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — equality-chain ⇒ ROW-1, grounded in the
  verified `firewall_combined_unsat`. A chain of asserted array equalities carries
  the read array to a `store … idx val` term; reading `idx` then yields `val`
  (the mirror of `AySoundness.ArrayThy.sel_upd_same`), contradicting
  `select a idx ≠ val`. Reconstructed from the frontend assertions (ay refutes
  arrays eagerly as bare-trust). Arrays are `Nat → Nat`, `store` the `if`-update;
  each chain equality is a function equality (`decide` over
  `Classical.propDecidable`). Axioms ⊆ {{propext, Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.ArrEqChain_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
{fields}
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}  | _ => false

def original : List (Cid × Clause) := [{original}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof_id}, [], [{proof_prems}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
{proof_body}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- The equality-chain read-over-write conflict has no model — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrEqChain_{hash}
"#,
    ))
}

/// Emit a verified-firewall Lean proof for a SET subset refutation found among
/// the PARSED (frontend) assertions: `(set.member x s)`, `(not (set.member x t))`,
/// `(set.subset s t)` over a shared ground witness `x` and sets `s`, `t`.
///
/// This is the VALID-LEMMA fragment of QF_SET: the theory lemma is the subset
/// definition instantiated at the GROUND witness `x` —
/// `¬(s⊆t) ∨ ¬(x∈s) ∨ (x∈t)` — which holds in EVERY set model, so it discharges
/// `firewall_combined_unsat`'s `hvalid` premise directly with NO Skolemization.
/// (The transitivity case `A⊆B ∧ B⊆C ∧ ¬(A⊆C)` needs a fresh witness for the
/// NEGATED subset — a Skolem clause, not valid — and is out of scope until the
/// firewall gains a Skolemization extension.)
///
/// Runtime counterpart of the hand-written `AySoundness.CombinedSetSubset` PoC;
/// kernel-checks with axioms ⊆ {propext, Classical.choice, Quot.sound}. The
/// `∀ e` over the (infinite) element domain makes atom 3 noncomputable via
/// `Classical.propDecidable`; `lratCheck`/`tableWf`/`proofWf` never touch
/// `atomVal`, so the `by decide` obligations are unaffected.
pub(crate) fn emit_set_subset_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    for sub_asrt in parsed {
        // (set.subset s t)
        let PTerm::App(op, sa) = sub_asrt else {
            continue;
        };
        if op != "set.subset" || sa.len() != 2 {
            continue;
        }
        let (s, t) = (&sa[0], &sa[1]);
        if s == t {
            continue; // reflexive — not the ground-witness refutation pattern
        }
        for mem_asrt in parsed {
            // (set.member x s) — a positive membership in the subset's LHS
            let PTerm::App(mop, ma) = mem_asrt else {
                continue;
            };
            if mop != "set.member" || ma.len() != 2 {
                continue;
            }
            let (x, set_of) = (&ma[0], &ma[1]);
            if set_of != s {
                continue;
            }
            // (not (set.member x t)) — the same witness is NOT in the superset
            let has_neg = parsed.iter().any(|a| {
                let PTerm::App(nop, na) = a else { return false };
                if nop != "not" || na.len() != 1 {
                    return false;
                }
                let PTerm::App(iop, ia) = &na[0] else {
                    return false;
                };
                iop == "set.member" && ia.len() == 2 && &ia[0] == x && &ia[1] == t
            });
            if has_neg {
                return Some(render_set_subset_lean(fnv_hex(&format!(
                    "{sub_asrt:?}{mem_asrt:?}"
                ))));
            }
        }
    }
    None
}

/// Render the `AySoundness.CombinedSetSubset`-shaped Lean for a ground-witness
/// subset refutation. Atoms are fixed (`1 ↦ x∈s`, `2 ↦ x∈t`, `3 ↦ s⊆t`) and the
/// model components opaque, so the body is a constant template up to the
/// namespace hash.
fn render_set_subset_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — SET subset refutation, grounded in the
  verified `firewall_combined_unsat`. The assertions `x∈s`, `x∉t`, `s⊆t` are
  unsatisfiable: the subset definition at the GROUND witness `x` gives
  `s⊆t → (x∈s → x∈t)`, contradicting `x∉t`. Reconstructed from the frontend
  assertions (ay decides set.subset via member saturation; the lemma is not a
  proof-step). Sets are `Nat → Bool`; subset is the `∀`-implication (atom 3 uses
  `Classical.propDecidable`, hence `noncomputable atomVal`). Pure Lean 4 core;
  axioms ⊆ {{propext, Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.SetSubset_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
  s : Nat -> Bool
  t : Nat -> Bool
  x : Nat

/-- Atoms: `1 ↦ x ∈ s`, `2 ↦ x ∈ t`, `3 ↦ s ⊆ t`. -/
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => m.s m.x
  | 2 => m.t m.x
  | 3 => decide (∀ e, m.s e = true → m.t e = true)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [-2]), (3, [3])]
def lemmas   : List (Cid × Clause) := [(4, [-3, -1, 2])]
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

theorem subset_lemma_valid (m : Val) : clauseSat (atomVal m) [-3, -1, 2] = true := by
  by_cases h3 : (∀ e, m.s e = true → m.t e = true)
  · by_cases h1 : m.s m.x = true
    · have h2 : m.t m.x = true := h3 m.x h1
      simp [clauseSat, litSat, atomVal, h2]
    · simp [clauseSat, litSat, atomVal, h1]
  · simp [clauseSat, litSat, atomVal, h3]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact subset_lemma_valid m

/-- `x∈s ∧ x∉t ∧ s⊆t` is unsatisfiable — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.SetSubset_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a SET subset TRANSITIVITY refutation
/// found among the PARSED (frontend) assertions: `(set.subset A B)`,
/// `(set.subset B C)`, `(not (set.subset A C))`.
///
/// The half-(1) certificate needs NO Skolemization (unlike the half-(2) Alethe
/// proof): subset transitivity `A ⊆ B ∧ B ⊆ C → A ⊆ C` is a VALID lemma under the
/// set interpretation, grounded directly through `firewall_combined_unsat`.
/// Runtime counterpart of `AySoundness.CombinedSetTransitivity`; axioms ⊆
/// {propext, Classical.choice, Quot.sound} (the `∀ e` subset atom is
/// noncomputable via `Classical.propDecidable`).
pub(crate) fn emit_set_subset_transitivity_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    for neg in parsed {
        // (not (set.subset A C))
        let PTerm::App(nop, na) = neg else { continue };
        if nop != "not" || na.len() != 1 {
            continue;
        }
        let PTerm::App(sop, sa) = &na[0] else {
            continue;
        };
        if sop != "set.subset" || sa.len() != 2 {
            continue;
        }
        let (a, c) = (&sa[0], &sa[1]);
        if a == c {
            continue;
        }
        // A middle set B with (set.subset A B) and (set.subset B C).
        for asrt in parsed {
            let PTerm::App(s1, s1a) = asrt else { continue };
            if s1 != "set.subset" || s1a.len() != 2 || &s1a[0] != a {
                continue;
            }
            let b = &s1a[1];
            if b == a || b == c {
                continue;
            }
            let has_bc = parsed.iter().any(|x| {
                let PTerm::App(s2, s2a) = x else { return false };
                s2 == "set.subset" && s2a.len() == 2 && &s2a[0] == b && &s2a[1] == c
            });
            if has_bc {
                return Some(render_set_subset_transitivity_lean(fnv_hex(&format!(
                    "{neg:?}"
                ))));
            }
        }
    }
    None
}

/// Render the `AySoundness.CombinedSetTransitivity`-shaped Lean for a subset
/// transitivity refutation. Atoms fixed (`1 ↦ A⊆B`, `2 ↦ B⊆C`, `3 ↦ A⊆C`);
/// constant template up to the namespace hash.
fn render_set_subset_transitivity_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — SET subset TRANSITIVITY, grounded in the
  verified `firewall_combined_unsat`. `A⊆B`, `B⊆C`, `¬(A⊆C)` are unsatisfiable:
  composing the two subset implications gives `A⊆C`. NO Skolemization needed for
  the certificate (transitivity is a valid lemma). Sets are `Nat → Bool`, `⊆` the
  ∀-implication (atom noncomputable via Classical.propDecidable); axioms ⊆
  {{propext, Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.SetTrans_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
  A : Nat -> Bool
  B : Nat -> Bool
  C : Nat -> Bool

def sub (X Y : Nat -> Bool) : Prop := ∀ e, X e = true -> Y e = true

/-- Atoms: `1 ↦ A ⊆ B`, `2 ↦ B ⊆ C`, `3 ↦ A ⊆ C`. -/
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (sub m.A m.B)
  | 2 => decide (sub m.B m.C)
  | 3 => decide (sub m.A m.C)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]
def lemmas   : List (Cid × Clause) := [(4, [-1, -2, 3])]
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

theorem trans_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, -2, 3] = true := by
  by_cases h1 : sub m.A m.B
  · by_cases h2 : sub m.B m.C
    · have h3 : sub m.A m.C := fun e hae => h2 e (h1 e hae)
      simp [clauseSat, litSat, atomVal, h3]
    · simp [clauseSat, litSat, atomVal, h2]
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact trans_lemma_valid m

/-- `A⊆B ∧ B⊆C ∧ ¬(A⊆C)` is unsatisfiable — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.SetTrans_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a DATATYPE SELECTOR congruence
/// refutation found among the PARSED (frontend) assertions: `(= (sel A) v)`,
/// `(= A B)`, `(not (= (sel B) v))` over a shared unary selector `sel`, a
/// substitution `A = B`, and a value `v`.
///
/// ay's QF_DT pipeline refutes eagerly and folds the term structure away (the
/// Alethe proof is a bare `(cl …) :rule trust` and `self.ctx.assertions` is
/// trivialized too — empirically confirmed), so this reconstructs from the
/// frontend assertions (which retain the structure), exactly like the
/// string / BV / array ROW1 emitters. The grounding is the selector-congruence
/// lemma `A = B ∧ sel A = v → sel B = v`, valid in every model (congruence on
/// `sel` + transitivity), discharged through the verified
/// `firewall_combined_unsat`. Runtime counterpart of the hand-written
/// `AySoundness.CombinedDtSelector` PoC; kernel-checks with axioms ⊆
/// {propext, Quot.sound} (fully computable — `Int`/`Nat` `DecidableEq`).
pub(crate) fn emit_dt_selector_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    for neg_asrt in parsed {
        // (not (= (sel B) v))
        let PTerm::App(nop, nargs) = neg_asrt else {
            continue;
        };
        if nop != "not" || nargs.len() != 1 {
            continue;
        }
        let PTerm::App(neqop, neqa) = &nargs[0] else {
            continue;
        };
        if neqop != "=" || neqa.len() != 2 {
            continue;
        }
        for (sel_b_app, v) in [(&neqa[0], &neqa[1]), (&neqa[1], &neqa[0])] {
            let PTerm::App(sel, sb_args) = sel_b_app else {
                continue;
            };
            if sb_args.len() != 1 {
                continue; // unary selector only
            }
            let b = &sb_args[0];
            // (= (sel A) v): same selector + value, with A ≠ B.
            let pos = parsed.iter().find_map(|a| {
                let PTerm::App(eqop, eqa) = a else {
                    return None;
                };
                if eqop != "=" || eqa.len() != 2 {
                    return None;
                }
                for (sel_a_app, vv) in [(&eqa[0], &eqa[1]), (&eqa[1], &eqa[0])] {
                    if vv != v {
                        continue;
                    }
                    let PTerm::App(sel2, sa_args) = sel_a_app else {
                        continue;
                    };
                    if sel2 != sel || sa_args.len() != 1 {
                        continue;
                    }
                    let a_arg = &sa_args[0];
                    if a_arg != b {
                        return Some(a_arg.clone());
                    }
                }
                None
            });
            let Some(a_arg) = pos else { continue };
            // (= A B) or (= B A) substitution.
            let has_sub = parsed.iter().any(|s| {
                let PTerm::App(eqop, eqa) = s else {
                    return false;
                };
                eqop == "="
                    && eqa.len() == 2
                    && ((eqa[0] == a_arg && &eqa[1] == b) || (&eqa[0] == b && eqa[1] == a_arg))
            });
            if has_sub {
                return Some(render_dt_selector_lean(fnv_hex(&format!(
                    "{neg_asrt:?}{sel:?}"
                ))));
            }
        }
    }
    None
}

/// Render the `AySoundness.CombinedDtSelector`-shaped Lean for a selector
/// congruence refutation. Atoms are fixed (`1 ↦ sel A = v`, `2 ↦ A = B`,
/// `3 ↦ sel B = v`) and the model components opaque, so the body is a constant
/// template up to the namespace hash.
fn render_dt_selector_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE SELECTOR congruence, grounded
  in the verified `firewall_combined_unsat`. The assertions `sel A = v`, `A = B`,
  `sel B ≠ v` are unsatisfiable: `A = B` gives `sel A = sel B` (congruence), and
  with `sel A = v` transitivity yields `sel B = v`, contradicting `sel B ≠ v`.
  Reconstructed from the frontend assertions (ay's QF_DT pipeline refutes eagerly
  and folds the structure away). Datatype values modeled as an opaque carrier
  (`Nat`), the selector as a function `Nat → Int`; fully computable, axioms ⊆
  {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtSelector_{hash}
open AySoundness

structure Val where
  p : Nat
  q : Nat
  sel : Nat -> Int
  v : Int

/-- Atoms: `1 ↦ sel p = v`, `2 ↦ p = q`, `3 ↦ sel q = v`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.sel m.p = m.v)
  | 2 => decide (m.p = m.q)
  | 3 => decide (m.sel m.q = m.v)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]
def lemmas   : List (Cid × Clause) := [(4, [-2, -1, 3])]
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

theorem selector_lemma_valid (m : Val) : clauseSat (atomVal m) [-2, -1, 3] = true := by
  by_cases h2 : m.p = m.q
  · by_cases h1 : m.sel m.p = m.v
    · have h3 : m.sel m.q = m.v := by rw [← h2]; exact h1
      simp [clauseSat, litSat, atomVal, h3]
    · simp [clauseSat, litSat, atomVal, h1]
  · simp [clauseSat, litSat, atomVal, h2]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact selector_lemma_valid m

/-- `sel p = v ∧ p = q ∧ sel q ≠ v` is unsatisfiable — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtSelector_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a DATATYPE CONSTRUCTOR INJECTIVITY
/// refutation found among the PARSED (frontend) assertions:
/// `(= (C a …) (C c …))` and `(not (= a c))` where `C` is a genuine datatype
/// CONSTRUCTOR (checked against `constructors`) and the FIRST arguments differ.
///
/// Constructors are injective, so two equal applications must agree on the first
/// argument — contradicting `a ≠ c`. ay's QF_DT pipeline folds the structure away
/// (bare `(cl …) :rule trust`), so this reconstructs from the frontend assertions
/// like the selector / string / BV / ROW1 emitters. The constructor is modeled as
/// a genuine binary inductive constructor `Pr.mk` (so injectivity holds — an
/// opaque function would not be injective); collapsing any extra arguments into
/// the single opaque second field is sound for FIRST-field injectivity. Grounded
/// via the verified `firewall_combined_unsat`; runtime counterpart of
/// `AySoundness.CombinedDtInjective`; axioms ⊆ {propext, Quot.sound}.
///
/// SOUND: fires ONLY when `C` is in `constructors` (a real datatype constructor —
/// injectivity is a datatype-theory axiom); never for an arbitrary function.
pub(crate) fn emit_dt_injective_firewall_lean_from_parsed(
    parsed: &[PTerm],
    constructors: &[String],
) -> Option<String> {
    for eq_asrt in parsed {
        // (= (C a …) (C c …))
        let PTerm::App(eqop, eqa) = eq_asrt else {
            continue;
        };
        if eqop != "=" || eqa.len() != 2 {
            continue;
        }
        let (PTerm::App(c1, args1), PTerm::App(c2, args2)) = (&eqa[0], &eqa[1]) else {
            continue;
        };
        if c1 != c2 || args1.is_empty() || args1.len() != args2.len() {
            continue;
        }
        if !constructors.iter().any(|c| c == c1) {
            continue; // genuine datatype constructor only — injectivity is its axiom
        }
        let a = &args1[0];
        let c = &args2[0];
        if a == c {
            continue;
        }
        // (not (= a c))  — the first arguments are asserted distinct.
        let has_neg = parsed.iter().any(|s| {
            let PTerm::App(nop, na) = s else { return false };
            if nop != "not" || na.len() != 1 {
                return false;
            }
            let PTerm::App(ieq, ia) = &na[0] else {
                return false;
            };
            ieq == "="
                && ia.len() == 2
                && ((&ia[0] == a && &ia[1] == c) || (&ia[0] == c && &ia[1] == a))
        });
        if has_neg {
            return Some(render_dt_injective_lean(fnv_hex(&format!("{eq_asrt:?}"))));
        }
    }
    None
}

/// Emit a verified-firewall Lean proof for a DATATYPE ACYCLICITY / OCCURS-CHECK
/// conflict found among the PARSED (frontend) assertions: an equality
/// `t = C(… t …)` (either orientation) where the variable `t` occurs as a PROPER
/// subterm of the other side reachable through ONLY datatype constructor
/// applications — at any depth ≥ 1, but NOT through a selector, `ite`, or any
/// non-constructor function (those genuinely require selector/case normalization
/// and are declined, fail-closed).
///
/// Such an equality is unsatisfiable in EVERY datatype model: Lean's auto-derived
/// structural `sizeOf` strictly increases across each constructor layer, so
/// `sizeOf t < sizeOf (C(… t …))`, and equal terms have equal `sizeOf`, so
/// `t = C(… t …)` is impossible. ay refutes QF_DT eagerly (bare `(cl) :rule
/// trust`) and folds the term structure away, so the shape is reconstructed from
/// the frontend assertions like the other datatype emitters and grounded in
/// `AySoundness.Datatype.acyclic_conflict_generic`.
///
/// Faithful abstraction: the constructor layers on the occurrence path are each
/// modeled by a single self-recursive constructor `wrap : DtT → DtT`; every
/// genuine datatype constructor strictly increases the derived `sizeOf` exactly
/// as `wrap` does, so collapsing the (element-typed / sibling) fields and the
/// specific constructors down to `wrap` preserves the acyclicity conflict — the
/// datatype analog of the nullary-constructor abstraction in
/// `emit_datatype_distinct_firewall_lean`. The number of `wrap` layers is the
/// occurrence DEPTH, so depth-≥2 nestings (`x = cons(h, cons(h, x))`) are handled
/// uniformly.
///
/// SOUND: fires ONLY when every symbol on the occurrence path is a registered
/// datatype constructor AND `t` itself is NOT a constructor (a genuine variable,
/// so the top-level shape is an occurs-check, not constructor distinctness).
///
/// In addition to the pure-constructor shape, two further shapes are reduced to
/// the same `t = C(… t …)` occurs-check by SOUND, UNCONDITIONAL rewrites
/// (reconstruction only — no new Lean lemma; the render is unchanged):
///
///   (B) SELECTOR-MEDIATED occurs-check: `x = C(… (sel_i x) …)` where `sel_i` is
///       `C`'s field-`i` selector. Applying `sel_i` to both sides projects
///       `sel_i x = arg_i` (the selector-over-own-constructor axiom holds for the
///       matching constructor), and `t := sel_i x` occurs in `arg_i` through pure
///       constructors — a `t = C(… t …)` occurs-check. E.g. `x = cons(cons(tl x))`
///       ⟶ `tl x = cons(tl x)`.
///
///   (C) TAUTOLOGICAL-TESTER `ite` + selector-self-eq under an asserted tester:
///       `ite((_ is D) r) t e = sel_j t` where `D` is the SOLE constructor of its
///       datatype (so the tester is a tautology and the `ite` const-folds to `t`),
///       `sel_j` is a field selector of constructor `C`, and `(_ is C) t` is
///       asserted. The tester gives `t = C(sel_0 t, …, sel_{n-1} t)`; substituting
///       the equation `sel_j t = t` into field `j` yields `t = C(… t …)` — a
///       depth-1 occurs-check. E.g. `ite((_ is mkRec) r) v12 v11 = left v12` with
///       `(_ is node) v12` ⟶ `v12 = node(v12, right v12)`.
///
/// Both extra shapes decline (fail-closed) unless every soundness precondition is
/// met with the supplied datatype metadata (`decls`, `ctor_selectors`).
pub(crate) fn emit_dt_occurs_check_firewall_lean_from_parsed(
    parsed: &[PTerm],
    constructors: &[String],
    decls: &[(String, Vec<String>)],
    ctor_selectors: &[(String, Vec<String>)],
) -> Option<String> {
    let is_ctor = |name: &str| constructors.iter().any(|c| c == name);
    let selectors_of = |ctor: &str| -> Option<&Vec<String>> {
        ctor_selectors
            .iter()
            .find(|(c, _)| c == ctor)
            .map(|(_, s)| s)
    };
    // Is `ctor` the SOLE constructor of its datatype (so `(_ is ctor) _` is a
    // tautology and can const-fold an `ite`)?
    let is_sole_ctor =
        |ctor: &str| -> bool { decls.iter().any(|(_, cs)| cs.len() == 1 && cs[0] == ctor) };

    // ---- Shape (A): pure-constructor occurs-check `t = C(… t …)`. ----
    for asrt in parsed {
        let PTerm::App(eqop, eqa) = asrt else {
            continue;
        };
        if eqop != "=" || eqa.len() != 2 {
            continue;
        }
        for (lhs, rhs) in [(&eqa[0], &eqa[1]), (&eqa[1], &eqa[0])] {
            let PTerm::Symbol(t) = lhs else {
                continue;
            };
            // `t` must be a genuine variable, not a (nullary) constructor — else
            // the conflict is constructor DISTINCTNESS, not acyclicity.
            if is_ctor(t) {
                continue;
            }
            // The other side must be a constructor application …
            let PTerm::App(head, _) = rhs else {
                continue;
            };
            if !is_ctor(head) {
                continue;
            }
            // … with `t` occurring under ≥1 pure-constructor layer.
            if let Some(depth) = occurs_ctor_depth(rhs, t, &is_ctor) {
                if depth >= 1 {
                    return Some(render_dt_occurs_check_lean(
                        depth,
                        fnv_hex(&format!("dtoccurs:{asrt:?}:{t}")),
                    ));
                }
            }
        }
    }

    // ---- Shape (B): selector-mediated occurs-check. ----
    // `x = C(args)` where `t := (sel_i x)` (the projection of field `i` via `C`'s
    // own field-`i` selector) occurs in `args[i]` through pure constructors.
    for asrt in parsed {
        let PTerm::App(eqop, eqa) = asrt else {
            continue;
        };
        if eqop != "=" || eqa.len() != 2 {
            continue;
        }
        for (lhs, rhs) in [(&eqa[0], &eqa[1]), (&eqa[1], &eqa[0])] {
            let PTerm::Symbol(x) = lhs else {
                continue;
            };
            if is_ctor(x) {
                continue;
            }
            let PTerm::App(head, args) = rhs else {
                continue;
            };
            if !is_ctor(head) {
                continue;
            }
            // Need `C`'s field selectors, one per argument, to project.
            let Some(sels) = selectors_of(head) else {
                continue;
            };
            if sels.len() != args.len() {
                continue;
            }
            for (i, sel) in sels.iter().enumerate() {
                // `t := (sel_i x)` — the field-`i` projection of `x`. Under the
                // equation `x = C(args)` the selector axiom gives `t = args[i]`.
                let t_term = PTerm::App(sel.clone(), vec![PTerm::Symbol(x.clone())]);
                if let Some(depth) = occurs_ctor_depth_term(&args[i], &t_term, &is_ctor) {
                    if depth >= 1 {
                        return Some(render_dt_occurs_check_lean(
                            depth,
                            fnv_hex(&format!("dtoccurs-sel:{asrt:?}:{x}:{sel}")),
                        ));
                    }
                }
            }
        }
    }

    // ---- Shape (C): tautological-tester `ite` + selector-self-eq. ----
    // `ite((_ is D) …) t e = sel_j t`, `D` sole ctor of its datatype (tautology,
    // fold to `t`), with `(_ is C) t` asserted and `sel_j` a selector of `C`.
    let fold_taut_ite = |term: &PTerm| -> PTerm {
        if let PTerm::App(op, a) = term {
            if op == "ite" && a.len() == 3 {
                if let PTerm::IndexedApp(name, idx, _) = &a[0] {
                    if name == "is" && idx.len() == 1 {
                        if let Some(cname) = idx[0].as_symbol() {
                            if is_sole_ctor(cname) {
                                return a[1].clone();
                            }
                        }
                    }
                }
            }
        }
        term.clone()
    };
    let tester_asserted = |ctor: &str, on: &str| -> bool {
        parsed.iter().any(|p| {
            let PTerm::IndexedApp(name, idx, targs) = p else {
                return false;
            };
            name == "is"
                && idx.len() == 1
                && idx[0].as_symbol() == Some(ctor)
                && targs.len() == 1
                && matches!(&targs[0], PTerm::Symbol(s) if s == on)
        })
    };
    for asrt in parsed {
        let PTerm::App(eqop, eqa) = asrt else {
            continue;
        };
        if eqop != "=" || eqa.len() != 2 {
            continue;
        }
        let l = fold_taut_ite(&eqa[0]);
        let r = fold_taut_ite(&eqa[1]);
        for (a, b) in [(&l, &r), (&r, &l)] {
            // One side reduces to a bare variable `t` …
            let PTerm::Symbol(t) = a else {
                continue;
            };
            if is_ctor(t) {
                continue;
            }
            // … the other to `(sel t)`, a unary selector on that same variable.
            let PTerm::App(sel, sargs) = b else {
                continue;
            };
            if sargs.len() != 1 {
                continue;
            }
            let PTerm::Symbol(t2) = &sargs[0] else {
                continue;
            };
            if t2 != t {
                continue;
            }
            // `sel` must be a field selector of a constructor `C` whose tester is
            // asserted on `t` (so `t = C(sel_0 t, …)` and substituting the
            // selector-self-eq gives a depth-1 occurs-check).
            for (cname, csels) in ctor_selectors {
                if csels.iter().any(|s| s == sel) && tester_asserted(cname, t) {
                    return Some(render_dt_occurs_check_lean(
                        1,
                        fnv_hex(&format!("dtoccurs-ite:{asrt:?}:{t}:{sel}")),
                    ));
                }
            }
        }
    }
    None
}

/// Depth (number of constructor layers) at which `t` occurs as a PROPER subterm
/// of `term`, reachable through ONLY datatype constructor applications.
/// `Some(0)` means `term` IS the symbol `t`; `Some(k)` (k ≥ 1) means `t` sits
/// under exactly `k` constructor layers. `None` if `t` is unreachable through a
/// pure-constructor path (blocked by a selector / `ite` / non-constructor
/// application, or simply absent).
fn occurs_ctor_depth(term: &PTerm, t: &str, is_ctor: &impl Fn(&str) -> bool) -> Option<usize> {
    match term {
        PTerm::Symbol(s) if s == t => Some(0),
        PTerm::App(head, args) if is_ctor(head) => {
            let mut best: Option<usize> = None;
            for a in args {
                if let Some(d) = occurs_ctor_depth(a, t, is_ctor) {
                    let cand = d + 1;
                    best = Some(best.map_or(cand, |b: usize| b.min(cand)));
                }
            }
            best
        }
        _ => None,
    }
}

/// Like [`occurs_ctor_depth`] but matches a whole TARGET `PTerm` (e.g. a
/// selector application `(sel x)`) as the recursive occurrence, rather than a
/// bare symbol. Descends ONLY through datatype-constructor applications, so a
/// match at depth `k ≥ 1` witnesses `target = C(… target …)` up to `k` genuine
/// constructor layers — exactly the acyclicity conflict modeled by `k` `wrap`
/// layers. `Some(0)` means `term` IS `target`.
fn occurs_ctor_depth_term(
    term: &PTerm,
    target: &PTerm,
    is_ctor: &impl Fn(&str) -> bool,
) -> Option<usize> {
    if term == target {
        return Some(0);
    }
    match term {
        PTerm::App(head, args) if is_ctor(head) => {
            let mut best: Option<usize> = None;
            for a in args {
                if let Some(d) = occurs_ctor_depth_term(a, target, is_ctor) {
                    let cand = d + 1;
                    best = Some(best.map_or(cand, |b: usize| b.min(cand)));
                }
            }
            best
        }
        _ => None,
    }
}

/// Render the acyclicity / occurs-check refutation Lean, grounded in
/// `AySoundness.Datatype.acyclic_conflict_generic`. `depth` is the number of
/// constructor layers between the variable and its recursive occurrence, modeled
/// as that many `wrap` layers in the context `ctx`.
fn render_dt_occurs_check_lean(depth: usize, hash: String) -> String {
    // ctx z := wrap (wrap … (wrap z))  — `depth` layers (depth ≥ 1).
    let mut ctx_body = String::from("z");
    for _ in 0..depth {
        ctx_body = format!("DtT.wrap ({ctx_body})");
    }
    format!(
        r#"import AySoundness.Firewall
import AySoundness.Datatype
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE ACYCLICITY / OCCURS-CHECK
  conflict grounded in the verified `firewall_combined_unsat`. The assertion
  `t = C(… t …)` (the variable `t` occurring as a PROPER subterm under {depth}
  datatype-constructor layer(s) on the other side) is unsatisfiable in every
  datatype model: the auto-derived structural `sizeOf` strictly increases across
  each constructor layer, so `sizeOf t < sizeOf (ctx t)` and no `t` can equal
  `ctx t`. Discharged through `AySoundness.Datatype.acyclic_conflict_generic`.
  Reconstructed from the frontend parsed ASSERTIONS (ay refutes QF_DT eagerly and
  folds the term structure away before emit). Faithful abstraction: each genuine
  constructor layer is modeled by the single self-recursive `wrap : DtT → DtT`,
  which strictly increases `sizeOf` exactly as any real constructor does; sibling
  fields / specific constructors are dropped (irrelevant to acyclicity, as nullary
  abstraction is to distinctness). Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtOccurs_{hash}
open AySoundness

/-- The datatype abstracted to its recursive spine: one self-recursive
    constructor (`wrap`) modeling each constructor layer, plus a base point. -/
inductive DtT where
  | wrap : DtT → DtT
  | base
deriving DecidableEq

abbrev Val := DtT

/-- The constructor context `ctx z := C(… z …)`, abstracted to {depth} `wrap`
    layer(s) — the occurrence depth of `t` in the asserted equality. -/
def ctx (z : Val) : Val := {ctx_body}

/-- Atom `1 ↦ (m = ctx m)` — the occurs-check equality `t = C(… t …)`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m = ctx m)
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

/-- **Occurs-check lemma validity** — the firewall's premise (b): no datatype
    value equals a strictly-larger constructor context of itself. Grounded in the
    generic `sizeOf`-based acyclicity conflict, with `ctx` instantiated EXPLICITLY
    (no higher-order-unification metavariable) and `sizeOf t < sizeOf (ctx t)`
    closed uniformly by `simp only [ctx, DtT.wrap.sizeOf_spec]; omega`. -/
theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have h : m ≠ ctx m :=
    AySoundness.Datatype.acyclic_conflict_generic (t := m) (ctx := ctx)
      (by simp only [ctx, DtT.wrap.sizeOf_spec]; omega)
  simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil, h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No datatype value satisfies the occurs-check equality — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtOccurs_{hash}
"#,
    )
}

/// Sound, UNCONDITIONAL constant-folds over a parsed datatype term, applied
/// bottom-up. These rewrites hold in EVERY model, so folding preserves the
/// theory (it is reconstruction only — no proof obligation). Used by the
/// case-split emitter to normalize the residual `ite` structure before the
/// bounded `by_cases`.
///
///   * `(ite true a b) → a`, `(ite false a b) → b` (Boolean-constant guard);
///   * `(ite c a a) → a` (reflexive branches — value-independent of `c`);
///   * `((_ is D) (C …)) → true/false` per `C == D` (tester on a constructor
///     application: the head decides the tester), for registered constructors.
///
/// Everything else is returned structurally unchanged (children folded).
fn fold_dt_term(term: &PTerm, is_ctor: &impl Fn(&str) -> bool) -> PTerm {
    match term {
        PTerm::App(op, args) => {
            let fargs: Vec<PTerm> = args.iter().map(|a| fold_dt_term(a, is_ctor)).collect();
            if op == "ite" && fargs.len() == 3 {
                // Boolean-constant guard.
                match &fargs[0] {
                    PTerm::Const(PConst::True) => return fargs[1].clone(),
                    PTerm::Const(PConst::False) => return fargs[2].clone(),
                    _ => {}
                }
                // Reflexive branches.
                if fargs[1] == fargs[2] {
                    return fargs[1].clone();
                }
            }
            PTerm::App(op.clone(), fargs)
        }
        PTerm::IndexedApp(name, idx, args) => {
            let fargs: Vec<PTerm> = args.iter().map(|a| fold_dt_term(a, is_ctor)).collect();
            // Tester on a constructor application: `((_ is D) (C …))`.
            if name == "is" && idx.len() == 1 && fargs.len() == 1 {
                if let Some(d) = idx[0].as_symbol() {
                    if let PTerm::App(head, _) = &fargs[0] {
                        if is_ctor(head) && is_ctor(d) {
                            return PTerm::Const(if head == d {
                                PConst::True
                            } else {
                                PConst::False
                            });
                        }
                    }
                    // Tester on a NULLARY constructor symbol `((_ is D) C)`.
                    if let PTerm::Symbol(head) = &fargs[0] {
                        if is_ctor(head) && is_ctor(d) {
                            return PTerm::Const(if head == d {
                                PConst::True
                            } else {
                                PConst::False
                            });
                        }
                    }
                }
            }
            PTerm::IndexedApp(name.clone(), idx.clone(), fargs)
        }
        other => other.clone(),
    }
}

/// Classification of one `ite` branch against the constructor-application side
/// `K` of a datatype case-split equality `K = ite g B_true B_false`.
enum DtBranch {
    /// The branch is a variable `t` occurring as a proper subterm of `K` under
    /// `depth` pure-constructor layers — the branch equality `K = t` is refuted
    /// by ACYCLICITY (`sizeOf t < sizeOf K`).
    Occurs { depth: usize },
    /// The branch is headed by a DIFFERENT constructor than `K` — the branch
    /// equality `K = D(…)` (`D ≠ head(K)`) is refuted by constructor
    /// DISTINCTNESS.
    Distinct,
}

/// Classify a folded `ite` branch `b` against the constructor-application side
/// `K` (head `k_head`). Returns `None` (fail-closed) when the branch is neither
/// a soundly-refutable occurs-check nor a constructor-distinctness against `K`.
fn classify_dt_branch(
    b: &PTerm,
    k: &PTerm,
    k_head: &str,
    is_ctor: &impl Fn(&str) -> bool,
) -> Option<DtBranch> {
    match b {
        // Occurs-check: `b` is a variable occurring inside `K` (depth ≥ 1).
        PTerm::Symbol(t) if !is_ctor(t) => occurs_ctor_depth(k, t, is_ctor)
            .filter(|d| *d >= 1)
            .map(|depth| DtBranch::Occurs { depth }),
        // Distinctness: `b` headed by a different constructor than `K`.
        PTerm::Symbol(d) if is_ctor(d) && d != k_head => Some(DtBranch::Distinct),
        PTerm::App(d, _) if is_ctor(d) && d != k_head => Some(DtBranch::Distinct),
        _ => None,
    }
}

/// Emit a verified-firewall Lean proof for a DATATYPE CASE-SPLIT refutation over
/// the PARSED (frontend) assertions — the case-split analog of the occurs /
/// distinctness / injectivity datatype emitters, carrying the split as a bounded
/// `by_cases` inside the theory-lemma validity obligation.
///
/// Two shapes are recognized (fail-closed otherwise):
///
///   * **boolean-ite-guard** `K = (ite g B_true B_false)` where `K = C(… t …)` is
///     a constructor application, `g` a Boolean variable, and EACH branch is
///     either an ACYCLICITY occurs-check (branch is `t`, occurring in `K`) or a
///     constructor DISTINCTNESS (branch headed by `D ≠ C`). The single lemma
///     clause `[-1]` (`¬ decide(K = ite g …)`) is validated by `by_cases` on `g`,
///     each branch discharged by `acyclic_conflict_generic` / `DtT.noConfusion`.
///     A sound pre-pass (`fold_dt_term`) normalizes reflexive `ite`s and
///     tautological testers before matching (covers the `dt_residual` shapes).
///
///   * **finite-distinct-disjunction** `((_ is nd) x)` + `(not (distinct A B C))`
///     over a Tree-shaped datatype (a binary constructor `nd` and a nullary `lf`).
///     The 3-way `not distinct` clause `[2,3,4]` resolves against three theory
///     lemmas — `[-2]` (nd ≠ lf, distinctness), `[-3]` (nd(y,x) ≠ x, occurs) and
///     `[-1,-4]` (is-nd(x) ∧ lf=x → False, TESTER mutual-exclusion) — modeled on
///     `AySoundness.Datatype.Tree`/`isNode`/`tester_node_leaf_excl'`.
///
/// EMISSION-ONLY: never changes ay's verdict/clauses; grounded through the
/// verified `AySoundness.firewall_combined_unsat`; axioms ⊆ {propext, Quot.sound}.
pub(crate) fn emit_dt_case_split_firewall_lean_from_parsed(
    parsed: &[PTerm],
    constructors: &[String],
    decls: &[(String, Vec<String>)],
) -> Option<String> {
    let is_ctor = |name: &str| constructors.iter().any(|c| c == name);

    // ---- Shape (A): boolean-ite-guard case split. ----
    for asrt in parsed {
        let PTerm::App(eqop, eqa) = asrt else {
            continue;
        };
        if eqop != "=" || eqa.len() != 2 {
            continue;
        }
        let l = fold_dt_term(&eqa[0], &is_ctor);
        let r = fold_dt_term(&eqa[1], &is_ctor);
        for (k, ite) in [(&l, &r), (&r, &l)] {
            // `K` must be a constructor application …
            let PTerm::App(k_head, _) = k else {
                continue;
            };
            if !is_ctor(k_head) {
                continue;
            }
            // … the other side an `ite` on a Boolean VARIABLE guard.
            let PTerm::App(iop, ia) = ite else {
                continue;
            };
            if iop != "ite" || ia.len() != 3 {
                continue;
            }
            let PTerm::Symbol(g) = &ia[0] else {
                continue;
            };
            if is_ctor(g) {
                continue; // guard must be a genuine Boolean variable
            }
            // Classify both branches; fail-closed unless both are refutable.
            let (Some(bt), Some(bf)) = (
                classify_dt_branch(&ia[1], k, k_head, &is_ctor),
                classify_dt_branch(&ia[2], k, k_head, &is_ctor),
            ) else {
                continue;
            };
            // Occurrence depth for the `ctx` model = the occurs branch's depth
            // (both occurs branches share `K`, hence the same depth); default 1
            // when both branches are distinctness.
            let depth = match (&bt, &bf) {
                (DtBranch::Occurs { depth }, _) | (_, DtBranch::Occurs { depth }) => *depth,
                _ => 1,
            };
            let t_occurs = matches!(bt, DtBranch::Occurs { .. });
            let f_occurs = matches!(bf, DtBranch::Occurs { .. });
            return Some(render_dt_case_split_ite_lean(
                depth,
                t_occurs,
                f_occurs,
                fnv_hex(&format!("dtcasesplit-ite:{asrt:?}:{g}")),
            ));
        }
    }

    // ---- Shape (B): finite-distinct-disjunction case split. ----
    if let Some(lean) = emit_dt_distinct_disjunction(parsed, &is_ctor, decls) {
        return Some(lean);
    }

    None
}

/// Recognize the `((_ is nd) x)` + `(not (distinct nd(y,x) lf x))` distinct-
/// disjunction over a Tree-shaped datatype and render it on
/// `AySoundness.Datatype.Tree`. Fail-closed unless all three disjuncts of the
/// `not distinct` are refuted (distinctness / occurs / tester-exclusion) and the
/// tested constructor is a binary constructor with a nullary sibling.
fn emit_dt_distinct_disjunction(
    parsed: &[PTerm],
    is_ctor: &impl Fn(&str) -> bool,
    decls: &[(String, Vec<String>)],
) -> Option<String> {
    // Is `ctor` a nullary constructor of some datatype?
    let is_nullary_ctor = |name: &str| -> bool {
        decls.iter().any(|(_, cs)| cs.iter().any(|c| c == name)) && is_ctor(name)
    };
    // Datatype of a constructor (to require the nullary sibling be same-datatype).
    let datatype_of = |ctor: &str| -> Option<&str> {
        decls
            .iter()
            .find(|(_, cs)| cs.iter().any(|c| c == ctor))
            .map(|(n, _)| n.as_str())
    };

    // Collect asserted testers `((_ is C) V)`.
    let tester_on = |ctor: &str, v: &str| -> bool {
        parsed.iter().any(|p| {
            let PTerm::IndexedApp(name, idx, targs) = p else {
                return false;
            };
            name == "is"
                && idx.len() == 1
                && idx[0].as_symbol() == Some(ctor)
                && targs.len() == 1
                && matches!(&targs[0], PTerm::Symbol(s) if s == v)
        })
    };

    for asrt in parsed {
        // `(not (distinct A B C))`.
        let PTerm::App(nop, na) = asrt else {
            continue;
        };
        if nop != "not" || na.len() != 1 {
            continue;
        }
        let PTerm::App(dop, da) = &na[0] else {
            continue;
        };
        if dop != "distinct" || da.len() != 3 {
            continue;
        }
        // Try to assign the three roles over all orderings of the 3 disjunct
        // pairs. A disjunct is a pair (P, Q) with the implicit equality P = Q.
        // Roles: (dist) node(y,x)=leaf ; (occ) node(y,x)=x ; (tester) leaf=x.
        // Enumerate which arg is the tested variable `x`.
        for xi in 0..3 {
            let PTerm::Symbol(x) = &da[xi] else {
                continue;
            };
            if is_ctor(x) {
                continue;
            }
            let others: Vec<&PTerm> = (0..3).filter(|i| *i != xi).map(|i| &da[i]).collect();
            // One of `others` is `node(y,x)` (binary ctor app containing x),
            // the other is the nullary `leaf`.
            for (ni, li) in [(0usize, 1usize), (1, 0)] {
                let node_app = others[ni];
                let leaf_t = others[li];
                let PTerm::App(nd, nd_args) = node_app else {
                    continue;
                };
                if !is_ctor(nd) || nd_args.len() != 2 {
                    continue;
                }
                let PTerm::Symbol(leaf) = leaf_t else {
                    continue;
                };
                if !is_nullary_ctor(leaf) || leaf == nd {
                    continue;
                }
                // Same datatype for `nd` and `leaf`.
                if datatype_of(nd) != datatype_of(leaf) {
                    continue;
                }
                // occurs: `x` must occur in `node(y,x)` (depth ≥ 1).
                if occurs_ctor_depth(node_app, x, is_ctor).is_none_or(|depth| depth < 1) {
                    continue;
                }
                // tester: `((_ is nd) x)` asserted (x is node-headed) — the
                // exclusion partner for the `leaf = x` disjunct.
                if !tester_on(nd, x) {
                    continue;
                }
                return Some(render_dt_distinct_disjunction_lean(fnv_hex(&format!(
                    "dtcasesplit-distinct:{asrt:?}:{x}:{nd}:{leaf}"
                ))));
            }
        }
    }
    None
}

/// Render the boolean-ite-guard case-split refutation, grounded in the verified
/// `firewall_combined_unsat`. The single lemma clause `[-1]` is validated by
/// `by_cases` on the Boolean guard, each branch discharged by
/// `AySoundness.Datatype.acyclic_conflict_generic` (occurs) or `DtT.noConfusion`
/// (distinctness). `depth` is the occurrence depth; `t_occurs`/`f_occurs` select,
/// per branch, the occurs-check vs. distinctness discharge.
fn render_dt_case_split_ite_lean(
    depth: usize,
    t_occurs: bool,
    f_occurs: bool,
    hash: String,
) -> String {
    // ctx z := wrap (wrap … (wrap z))  — `depth` layers (depth ≥ 1).
    let mut ctx_body = String::from("z");
    for _ in 0..depth {
        ctx_body = format!("DtT.wrap ({ctx_body})");
    }
    // cond value strings: occurs branch → the variable `m.t`, distinct → base.
    let true_val = if t_occurs { "(m.t)" } else { "(DtT.base)" };
    let false_val = if f_occurs { "(m.t)" } else { "(DtT.base)" };
    // Per-branch proof of `ctx m.t ≠ <val>`.
    let occurs_proof = "      exact Ne.symm (AySoundness.Datatype.acyclic_conflict_generic \
        (t := m.t) (ctx := ctx)\n        (by simp only [ctx, DtT.wrap.sizeOf_spec]; omega))";
    let distinct_proof = "      simp only [ctx]\n      exact fun heq => DtT.noConfusion heq";
    let true_branch = if t_occurs {
        format!("      show ctx m.t ≠ m.t\n{occurs_proof}")
    } else {
        format!("      show ctx m.t ≠ DtT.base\n{distinct_proof}")
    };
    let false_branch = if f_occurs {
        format!("      show ctx m.t ≠ m.t\n{occurs_proof}")
    } else {
        format!("      show ctx m.t ≠ DtT.base\n{distinct_proof}")
    };
    format!(
        r#"import AySoundness.Firewall
import AySoundness.Datatype
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE CASE-SPLIT (boolean-ite-guard)
  conflict grounded in the verified `firewall_combined_unsat`. The residual
  assertion `C(… t …) = ite g B_true B_false` is unsatisfiable: `by_cases` on the
  Boolean guard `g` reduces the `ite` to one branch, each of which is a genuine
  datatype conflict — an ACYCLICITY occurs-check (`C(… t …) ≠ t`, via the
  auto-derived `sizeOf` strictly increasing across the {depth} constructor
  layer(s)) or a constructor DISTINCTNESS (`C(…) ≠ D(…)`, different head). The
  single lemma clause `[-1]` carries the split as a validated `by_cases` inside
  the theory-lemma validity obligation, exactly like the storecomm array emitter.
  Reconstructed from the frontend parsed ASSERTIONS (ay refutes QF_DT eagerly and
  folds the term structure away before emit); reflexive `ite`s and tautological
  testers are const-folded by a sound pre-pass. Faithful abstraction: each
  constructor layer is modeled by the self-recursive `wrap : DtT → DtT` (strictly
  `sizeOf`-increasing as any real constructor), and a distinct constructor by the
  nullary `base` (`wrap _ ≠ base`, as `C(…) ≠ D(…)`). Pure Lean 4 core; axioms ⊆
  {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtCaseSplit_{hash}
open AySoundness

/-- The datatype abstracted to its recursive spine: one self-recursive
    constructor (`wrap`, one per occurrence layer) plus a distinct nullary
    constructor (`base`, the distinctness partner). -/
inductive DtT where
  | wrap : DtT → DtT
  | base
deriving DecidableEq

/-- Theory model: the Boolean guard `g` and the datatype value `t`. -/
structure Val where
  g : Bool
  t : DtT

/-- The occurrence context `ctx z := C(… z …)`, abstracted to {depth} `wrap`
    layer(s). -/
def ctx (z : DtT) : DtT := {ctx_body}

/-- Atom `1 ↦ (ctx t = ite g B_true B_false)` — the residual case-split equality
    `C(… t …) = ite g B_true B_false`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (ctx m.t = (cond m.g {true_val} {false_val}))
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

/-- **Case-split lemma validity** — the firewall's premise (b): the residual
    equality is false in every model. `by_cases` on the guard `g` reduces the
    `ite`; each branch is closed by the matching verified Datatype lemma
    (acyclicity / distinctness). -/
theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have h : ctx m.t ≠ (cond m.g {true_val} {false_val}) := by
    cases hg : m.g
    ·
{false_branch}
    ·
{true_branch}
  simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil, h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No datatype model satisfies the case-split equality — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtCaseSplit_{hash}
"#,
    )
}

/// Render the finite-distinct-disjunction case-split refutation on
/// `AySoundness.Datatype.Tree`, grounded in the verified
/// `firewall_combined_unsat`. The 3-way `not distinct` clause `[2,3,4]` resolves
/// against three theory lemmas (`[-2]` distinctness, `[-3]` occurs, `[-1,-4]`
/// tester-exclusion), each validated by the corresponding named Datatype lemma.
fn render_dt_distinct_disjunction_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
import AySoundness.Datatype
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE CASE-SPLIT (finite distinct-
  disjunction) conflict grounded in the verified `firewall_combined_unsat`. The
  assertions `((_ is nd) x)` and `(not (distinct (nd y x) lf x))` are
  unsatisfiable: `not distinct` is the 3-way disjunction `(nd(y,x)=lf) ∨
  (nd(y,x)=x) ∨ (lf=x)`, and each disjunct is a genuine datatype conflict —
  DISTINCTNESS `nd(y,x) ≠ lf`, ACYCLICITY `nd(y,x) ≠ x` (x is the right child),
  and TESTER mutual-exclusion `is-nd(x) ∧ lf=x → False`. The three theory-lemma
  clauses `[-2]`, `[-3]`, `[-1,-4]` resolve against the disjunction `[2,3,4]` and
  the tester unit `[1]` to the empty clause. Modeled on the concrete
  `AySoundness.Datatype.Tree` (`nd = node`, `lf = leaf`) with `isNode` /
  `node_ne_leaf` / `acyclic_r` / `tester_node_leaf_excl'`. Reconstructed from the
  frontend parsed ASSERTIONS. Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtCaseSplitDisj_{hash}
open AySoundness
open AySoundness.Datatype (Tree isNode)

/-- Theory model: the two datatype values `x, y : Tree` (`nd(y,x) = node y x`,
    `lf = leaf`). -/
structure Val where
  x : Tree
  y : Tree

/-- Atoms: `1 ↦ is-nd(x)`, `2 ↦ nd(y,x)=lf`, `3 ↦ nd(y,x)=x`, `4 ↦ lf=x`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => isNode m.x
  | 2 => decide (Tree.node m.y m.x = Tree.leaf)
  | 3 => decide (Tree.node m.y m.x = m.x)
  | 4 => decide (Tree.leaf = m.x)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2, 3, 4])]
def lemmas   : List (Cid × Clause) := [(3, [-2]), (4, [-3]), (5, [-1, -4])]
def proof    : List (Cid × Clause × List Int) := [(6, [], [1, 3, 4, 5, 2])]

/-- `[-2]` : `nd(y,x) ≠ lf` — constructor DISTINCTNESS. -/
theorem lemma2_valid (m : Val) : clauseSat (atomVal m) [-2] = true := by
  have h : Tree.node m.y m.x ≠ Tree.leaf := Tree.node_ne_leaf
  simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil, h]

/-- `[-3]` : `nd(y,x) ≠ x` — ACYCLICITY (x is the right child). -/
theorem lemma3_valid (m : Val) : clauseSat (atomVal m) [-3] = true := by
  have h : Tree.node m.y m.x ≠ m.x := Ne.symm (Tree.acyclic_r m.x m.y)
  simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil, h]

/-- `[-1,-4]` : `¬is-nd(x) ∨ ¬(lf=x)` — TESTER mutual-exclusion. -/
theorem lemma5_valid (m : Val) : clauseSat (atomVal m) [-1, -4] = true := by
  by_cases h4 : Tree.leaf = m.x
  · have h1 : isNode m.x = false := by rw [← h4]; rfl
    simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil, h1]
  · simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil, h4]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  rcases hcl with h | h | h <;> subst h
  · exact lemma2_valid m
  · exact lemma3_valid m
  · exact lemma5_valid m

/-- `is-nd(x) ∧ ¬distinct(nd(y,x), lf, x)` is unsatisfiable — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtCaseSplitDisj_{hash}
"#,
    )
}

/// Render the `AySoundness.CombinedDtInjective`-shaped Lean for a constructor
/// first-field injectivity refutation. Atoms fixed (`1 ↦ mk a b = mk c d`,
/// `2 ↦ a = c`); the body is a constant template up to the namespace hash.
fn render_dt_injective_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE CONSTRUCTOR INJECTIVITY,
  grounded in the verified `firewall_combined_unsat`. The assertions
  `mk a b = mk c d`, `a ≠ c` are unsatisfiable: a constructor is injective, so
  `mk a b = mk c d` forces `a = c`. Reconstructed from the frontend assertions
  (ay's QF_DT pipeline refutes eagerly and folds the structure away). The
  datatype is modeled as a genuine inductive `Pr` with a binary constructor `mk`
  (extra fields collapsed into the opaque second field — sound for first-field
  injectivity); fully computable, axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtInjective_{hash}
open AySoundness

inductive Pr where
  | mk : Int -> Int -> Pr
  deriving DecidableEq

structure Val where
  a : Int
  b : Int
  c : Int
  d : Int

/-- Atoms: `1 ↦ mk a b = mk c d`, `2 ↦ a = c`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (Pr.mk m.a m.b = Pr.mk m.c m.d)
  | 2 => decide (m.a = m.c)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [-2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, 2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

theorem inj_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2] = true := by
  by_cases h1 : m.a = m.c
  · simp [clauseSat, litSat, atomVal, h1]
  · have hne : Pr.mk m.a m.b ≠ Pr.mk m.c m.d := fun he => h1 (Pr.mk.inj he).1
    simp [clauseSat, litSat, atomVal, hne, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact inj_lemma_valid m

/-- `mk a b = mk c d ∧ a ≠ c` is unsatisfiable — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtInjective_{hash}
"#,
    )
}

/// Flatten a (possibly nested) `(and a b …)` parsed term into its leaf
/// conjuncts. A non-`and` term is its own single conjunct.
fn flatten_dt_and<'a>(t: &'a PTerm, out: &mut Vec<&'a PTerm>) {
    if let PTerm::App(op, args) = t {
        if op == "and" {
            for a in args {
                flatten_dt_and(a, out);
            }
            return;
        }
    }
    out.push(t);
}

/// Recognize a POSITIVE constructor tester `((_ is C) T)` and return `(C, T)`.
fn parsed_positive_tester(t: &PTerm) -> Option<(&str, &PTerm)> {
    let PTerm::IndexedApp(name, idx, args) = t else {
        return None;
    };
    if name != "is" || idx.len() != 1 || args.len() != 1 {
        return None;
    }
    let ctor = idx[0].as_symbol()?;
    Some((ctor, &args[0]))
}

/// Recognize a NEGATIVE constructor tester `(not ((_ is C) T))` → `(C, T)`.
fn parsed_neg_tester(t: &PTerm) -> Option<(&str, &PTerm)> {
    let PTerm::App(op, args) = t else {
        return None;
    };
    if op != "not" || args.len() != 1 {
        return None;
    }
    parsed_positive_tester(&args[0])
}

/// Recognize a disequality against a bare constructor symbol,
/// `(not (= D T))` / `(not (= T D))` with `is_ctor(D)`, and return `(D, T)`.
fn parsed_neg_eq_ctor<'a>(
    t: &'a PTerm,
    is_ctor: &impl Fn(&str) -> bool,
) -> Option<(&'a str, &'a PTerm)> {
    let PTerm::App(op, args) = t else {
        return None;
    };
    if op != "not" || args.len() != 1 {
        return None;
    }
    let PTerm::App(eqop, ea) = &args[0] else {
        return None;
    };
    if eqop != "=" || ea.len() != 2 {
        return None;
    }
    for (ci, ti) in [(0usize, 1usize), (1, 0)] {
        if let PTerm::Symbol(d) = &ea[ci] {
            if is_ctor(d) {
                return Some((d, &ea[ti]));
            }
        }
    }
    None
}

/// Emit a verified-firewall Lean proof for a DATATYPE TESTER MUTUAL-EXCLUSION
/// refutation over the PARSED (frontend) assertions: two DISTINCT constructor
/// testers `((_ is Cᵢ) T)` and `((_ is Cⱼ) T)` (`Cᵢ ≠ Cⱼ`) asserted POSITIVELY
/// on the SAME syntactic term `T`. No value of a datatype is headed by two
/// different constructors, so the pair is unsatisfiable — the generalization of
/// `AySoundness.Datatype.tester_node_leaf_excl` from the concrete node/leaf pair
/// to any two distinct constructors of one datatype, at any arity (`T` need not
/// be a variable — `(f x)` is a single opaque datatype-sorted term; no UF
/// congruence is involved).
///
/// `Cᵢ`, `Cⱼ` must be constructors of the SAME datatype in `decls` (the two
/// testers are only well-typed on that datatype, so `T` is that datatype-sorted;
/// the abstraction is faithful without any sort inference). The datatype is
/// modeled as a genuine `N`-nullary-constructor inductive (fields collapsed —
/// sound for tester head-tag reasoning, as nullary abstraction is to
/// distinctness), the testers as `Bool`-valued matches, and the mutual exclusion
/// discharged by `cases`/`decide` inside the theory-lemma validity obligation.
/// EMISSION-ONLY; grounded through `AySoundness.firewall_combined_unsat`;
/// axioms ⊆ {propext, Quot.sound}. Fail-closed (`None`) on any other shape.
pub(crate) fn emit_dt_tester_exclusion_firewall_lean_from_parsed(
    parsed: &[PTerm],
    decls: &[(String, Vec<String>)],
) -> Option<String> {
    // Collect POSITIVE testers asserted at the top level.
    let testers: Vec<(&str, &PTerm)> = parsed.iter().filter_map(parsed_positive_tester).collect();
    // Datatype (name, ctors) owning a constructor.
    let datatype_of = |ctor: &str| -> Option<&(String, Vec<String>)> {
        let mut owners = decls.iter().filter(|(_, cs)| cs.iter().any(|c| c == ctor));
        let owner = owners.next()?;
        owners.next().is_none().then_some(owner)
    };
    for a in 0..testers.len() {
        for b in (a + 1)..testers.len() {
            let (ci, ti) = testers[a];
            let (cj, tj) = testers[b];
            if ci == cj || ti != tj {
                continue;
            }
            // Both constructors must belong to the SAME datatype.
            let Some((dti, ctors)) = datatype_of(ci) else {
                continue;
            };
            let Some((dtj, _)) = datatype_of(cj) else {
                continue;
            };
            if dti != dtj {
                continue;
            }
            let (Some(i), Some(j)) = (
                ctors.iter().position(|c| c == ci),
                ctors.iter().position(|c| c == cj),
            ) else {
                continue;
            };
            let n = ctors.len();
            if n < 2 || i == j {
                continue;
            }
            return Some(render_dt_tester_exclusion_lean(
                n,
                i,
                j,
                fnv_hex(&format!("dttesterexcl:{dti}:{ci}:{cj}:{ti:?}")),
            ));
        }
    }
    None
}

/// Render the datatype tester mutual-exclusion refutation, grounded in the
/// verified `firewall_combined_unsat`. The datatype is modeled as `n` nullary
/// constructors `k0 … k{n-1}`; the two testers select `ki` / `kj`; the single
/// lemma clause `[-1,-2]` (¬isCᵢ(T) ∨ ¬isCⱼ(T)) is validated by `cases` on the
/// value.
fn render_dt_tester_exclusion_lean(n: usize, i: usize, j: usize, hash: String) -> String {
    let ctors = (0..n)
        .map(|k| format!("k{k}"))
        .collect::<Vec<_>>()
        .join(" | ");
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE TESTER MUTUAL-EXCLUSION
  conflict grounded in the verified `firewall_combined_unsat`. The assertions
  `((_ is Cᵢ) T)` and `((_ is Cⱼ) T)` (Cᵢ ≠ Cⱼ, same datatype, same term T) are
  unsatisfiable: every datatype value is headed by exactly ONE constructor, so no
  `T` is simultaneously `Cᵢ`-headed and `Cⱼ`-headed. This is the generalization of
  `AySoundness.Datatype.tester_node_leaf_excl` from the concrete node/leaf pair to
  ANY two distinct constructors of one datatype; `T` is a single opaque
  datatype-sorted term (`(f x)`, a variable, …) — no UF congruence is involved,
  as both testers apply to the SAME syntactic term. Reconstructed from the
  frontend parsed ASSERTIONS. Faithful abstraction: the datatype is modeled by an
  `{n}`-nullary-constructor inductive (fields collapsed — sound for tester
  head-tag reasoning, as nullary abstraction is to distinctness), the testers as
  `Bool`-valued matches. Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtTesterExcl_{hash}
open AySoundness

/-- The datatype abstracted to its `{n}` constructor head-tags (fields dropped). -/
inductive DtE where
  | {ctors}
  deriving DecidableEq

abbrev Val := DtE

/-- Tester `((_ is Cᵢ) ·)` as ay lowers it: `true` on the i-th head, else `false`. -/
def isC_i (x : DtE) : Bool := match x with | .k{i} => true | _ => false
/-- Tester `((_ is Cⱼ) ·)`: `true` on the j-th head, else `false`. -/
def isC_j (x : DtE) : Bool := match x with | .k{j} => true | _ => false

/-- Atoms: `1 ↦ isCᵢ(T)`, `2 ↦ isCⱼ(T)`. -/
def atomVal (m : Val) : Nat → Bool
  | 1 => isC_i m
  | 2 => isC_j m
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, -2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- **Tester mutual-exclusion validity** — the firewall's premise (b): no value
    is headed by both `Cᵢ` and `Cⱼ`, so `¬isCᵢ(T) ∨ ¬isCⱼ(T)` holds in every
    model. `cases` on the head-tag closes each leaf by `decide`. -/
theorem lemma_valid :
    ∀ c ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) c = true := by
  intro c hc m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  subst hc
  cases m <;> decide

/-- `isCᵢ(T) ∧ isCⱼ(T)` (Cᵢ ≠ Cⱼ) is unsatisfiable — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemma_valid (by decide)

end AySoundness.Emitted.DtTesterExcl_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a DATATYPE EXHAUSTIVENESS (2-ctor
/// case-completeness) refutation over the PARSED (frontend) assertions: a
/// NEGATIVE tester `(not ((_ is C) T))` together with a disequality
/// `(not (= D T))` / `(not (= T D))`, where `C` and `D` are the ONLY TWO
/// constructors of one datatype and `D` is nullary. A value that is neither
/// `C`-headed nor equal to `D` cannot exist (the datatype has exactly those two
/// constructors) — the exhaustiveness dual of the enum-cardinality pigeonhole.
/// The relevant conjuncts are extracted from a flattened top-level `(and …)`
/// (the rest of the conjunction is sat/tautological noise).
///
/// `C`, `D` come from `decls` (the tester and the nullary-constructor equality
/// are only well-typed on that datatype, so `T` is that datatype-sorted; the
/// abstraction is faithful without any sort inference). The datatype is modeled
/// as a genuine 2-nullary-constructor inductive; exhaustiveness (`isC(T) ∨
/// T = D`) is discharged by `cases` inside the theory-lemma validity obligation.
/// EMISSION-ONLY; grounded through `AySoundness.firewall_combined_unsat`;
/// axioms ⊆ {propext, Quot.sound}. Fail-closed (`None`) on any other shape.
pub(crate) fn emit_dt_exhaustiveness_firewall_lean_from_parsed(
    parsed: &[PTerm],
    decls: &[(String, Vec<String>)],
) -> Option<String> {
    let is_ctor = |name: &str| decls.iter().any(|(_, cs)| cs.iter().any(|c| c == name));
    let datatype_of = |ctor: &str| -> Option<&(String, Vec<String>)> {
        let mut owners = decls.iter().filter(|(_, cs)| cs.iter().any(|c| c == ctor));
        let owner = owners.next()?;
        owners.next().is_none().then_some(owner)
    };
    // Flatten every top-level assertion's `and` structure into one conjunct pool.
    let mut conjs: Vec<&PTerm> = Vec::new();
    for a in parsed {
        flatten_dt_and(a, &mut conjs);
    }
    for tc in &conjs {
        let Some((c, tt)) = parsed_neg_tester(tc) else {
            continue;
        };
        for dc in &conjs {
            let Some((d, td)) = parsed_neg_eq_ctor(dc, &is_ctor) else {
                continue;
            };
            // Same term, distinct constructors of a datatype with EXACTLY {C, D}.
            if c == d || tt != td {
                continue;
            }
            let Some((dtc, ctors)) = datatype_of(c) else {
                continue;
            };
            let Some((dtd, _)) = datatype_of(d) else {
                continue;
            };
            if dtc != dtd || ctors.len() != 2 || !ctors.iter().any(|x| x == d) {
                continue;
            }
            return Some(render_dt_exhaustiveness_lean(fnv_hex(&format!(
                "dtexhaust:{dtc}:{c}:{d}:{tt:?}"
            ))));
        }
    }
    None
}

/// Render the 2-constructor exhaustiveness refutation, grounded in the verified
/// `firewall_combined_unsat`. The datatype is modeled as `k0` (the tested
/// constructor `C`) and `k1` (the nullary partner `D`); the single lemma clause
/// `[1,2]` (isC(T) ∨ T = D) is validated by `cases` on the value.
fn render_dt_exhaustiveness_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE EXHAUSTIVENESS (2-constructor
  case-completeness) conflict grounded in the verified `firewall_combined_unsat`.
  The assertions `(not ((_ is C) T))` and `(not (= D T))` are unsatisfiable when
  `C` and `D` are the ONLY two constructors of `T`'s datatype: a value that is
  neither `C`-headed nor `D` cannot exist. This is the exhaustiveness dual of the
  enum-cardinality pigeonhole (`cases <;> …` over a finite constructor set), the
  case-completeness rather than the too-many-distinct direction. Reconstructed
  from the frontend parsed ASSERTIONS (the relevant two conjuncts extracted from a
  flattened top-level `and`; the rest is sat/tautological noise). Faithful
  abstraction: the datatype is modeled by a 2-nullary-constructor inductive
  (`k0 = C`, `k1 = D`; `C`'s fields dropped — sound for head-tag reasoning), the
  tester as a `Bool`-valued match. Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtExhaust_{hash}
open AySoundness

/-- The datatype abstracted to its two constructor head-tags (`k0 = C`, `k1 = D`,
    fields dropped). -/
inductive DtL where
  | k0 | k1
  deriving DecidableEq

abbrev Val := DtL

/-- Tester `((_ is C) ·)` as ay lowers it: `true` on `k0` (= `C`), else `false`. -/
def isC (x : DtL) : Bool := match x with | .k0 => true | _ => false

/-- Atoms: `1 ↦ isC(T)`, `2 ↦ (T = D)` (`D = k1`). -/
def atomVal (m : Val) : Nat → Bool
  | 1 => isC m
  | 2 => decide (m = DtL.k1)
  | _ => false

-- `¬isC(T)` → clause `[-1]`;  `T ≠ D` → clause `[-2]`.
def original : List (Cid × Clause) := [(1, [-1]), (2, [-2])]
-- exhaustiveness: `isC(T) ∨ T = D`.
def lemmas   : List (Cid × Clause) := [(3, [1, 2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- **Exhaustiveness validity** — the firewall's premise (b): every value of a
    two-constructor datatype is `C`-headed or equals `D`, so `isC(T) ∨ T = D`
    holds in every model. `cases` on the value closes each leaf by `decide`. -/
theorem lemma_valid :
    ∀ c ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) c = true := by
  intro c hc m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  subst hc
  cases m <;> decide

/-- `¬isC(T) ∧ T ≠ D` (with `{{C, D}}` the whole datatype) is unsatisfiable — via
    the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemma_valid (by decide)

end AySoundness.Emitted.DtExhaust_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a DATATYPE SELECTOR-OVER-OWN-
/// CONSTRUCTOR refutation over the PARSED (frontend) assertions: an equality
/// `(= X (C a₀ … a_{n-1}))` binding a variable to a constructor application,
/// together with a disequality `(not (= (sᵢ X) v))` where `sᵢ` is `C`'s i-th
/// field selector and `aᵢ` (the constructor's i-th argument) is syntactically
/// `v`. The selector-over-matching-constructor axiom gives `sᵢ X = sᵢ (C …) = aᵢ
/// = v`, contradicting `sᵢ X ≠ v`.
///
/// This is the shape of `benchmarks/smt/datatype_simple.smt2`
/// (`x = Some(0x2a)`, `value(x) ≠ 0x2a`). The proof-step-driven `DtSel`
/// projection emitter does not fire (the executor routes the residual through a
/// BV-constant compare, not a `DtSelector` theory lemma), so reconstruct from the
/// frontend assertions like the selector-congruence / injectivity emitters.
///
/// `C` must have exactly one owner in `decls`, and its selectors come from one
/// unambiguous `ctor_selectors` entry; overloaded surface names therefore
/// decline instead of borrowing another datatype's field positions. The field
/// is abstracted to `Int` (the projection identity `sel (mk a) = a` is
/// field-sort-independent, as in the injectivity emitter). EMISSION-ONLY; grounded through
/// `AySoundness.firewall_combined_unsat`; axioms ⊆ {propext, Quot.sound}.
/// Fail-closed (`None`) on any other shape.
pub(crate) fn emit_dt_selector_over_ctor_firewall_lean_from_parsed(
    parsed: &[PTerm],
    decls: &[(String, Vec<String>)],
    ctor_selectors: &[(String, Vec<String>)],
) -> Option<String> {
    let selectors_of = |ctor: &str| -> Option<&Vec<String>> {
        let mut matches = ctor_selectors.iter().filter(|(c, _)| c == ctor);
        let (_, selectors) = matches.next()?;
        matches.next().is_none().then_some(selectors)
    };
    let has_unique_owner = |ctor: &str| {
        let mut owners = decls.iter().filter(|(_, cs)| cs.iter().any(|c| c == ctor));
        owners.next().is_some() && owners.next().is_none()
    };
    for a in parsed {
        // A: `(= X (C args))` with `X` a variable and `C` a known constructor.
        let PTerm::App(eqop, ea) = a else {
            continue;
        };
        if eqop != "=" || ea.len() != 2 {
            continue;
        }
        for (xi, ci) in [(0usize, 1usize), (1, 0)] {
            let PTerm::Symbol(x) = &ea[xi] else {
                continue;
            };
            let PTerm::App(c, cargs) = &ea[ci] else {
                continue;
            };
            if !has_unique_owner(c) {
                continue;
            }
            let Some(sels) = selectors_of(c) else {
                continue;
            };
            if sels.is_empty() || sels.len() != cargs.len() {
                continue;
            }
            // B: `(not (= (sᵢ X) v))` with `sᵢ` = C's field-i selector, `aᵢ` = v.
            for b in parsed {
                let PTerm::App(nop, nargs) = b else {
                    continue;
                };
                if nop != "not" || nargs.len() != 1 {
                    continue;
                }
                let PTerm::App(beq, ba) = &nargs[0] else {
                    continue;
                };
                if beq != "=" || ba.len() != 2 {
                    continue;
                }
                for (si, vi) in [(0usize, 1usize), (1, 0)] {
                    let PTerm::App(s, sargs) = &ba[si] else {
                        continue;
                    };
                    if sargs.len() != 1 {
                        continue;
                    }
                    let PTerm::Symbol(sx) = &sargs[0] else {
                        continue;
                    };
                    if sx != x {
                        continue;
                    }
                    let mut positions = sels.iter().enumerate().filter(|(_, se)| *se == s);
                    let Some((idx, _)) = positions.next() else {
                        continue;
                    };
                    if positions.next().is_some() {
                        continue;
                    }
                    if cargs[idx] != ba[vi] {
                        continue;
                    }
                    return Some(render_dt_selector_over_ctor_lean(fnv_hex(&format!(
                        "dtselctor:{c}:{s}:{x}:{:?}",
                        cargs[idx]
                    ))));
                }
            }
        }
    }
    None
}

/// Render the datatype selector-over-own-constructor refutation, grounded in the
/// verified `firewall_combined_unsat`. The datatype is modeled as a single-field
/// constructor `mk : Int → D` with projection `sel`; the lemma `[-1,2]`
/// (`X = mk a → sel X = a`) discharges the selector-over-matching-constructor
/// axiom, closed by `by_cases` on the constructor equality.
fn render_dt_selector_over_ctor_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE SELECTOR-OVER-OWN-CONSTRUCTOR
  conflict grounded in the verified `firewall_combined_unsat`. The assertions
  `X = C(… aᵢ …)` and `sᵢ X ≠ aᵢ` are unsatisfiable: the selector of a
  constructor over that same constructor projects its own argument, so
  `sᵢ X = sᵢ (C …) = aᵢ`. Reconstructed from the frontend parsed ASSERTIONS
  (ay routes the residual through a BV/constant compare, so the proof-step `DtSel`
  projection emitter does not fire). Faithful abstraction: the datatype is modeled
  by a single-field constructor `mk : Int → D` with projection `sel` (the
  projected field abstracted to `Int` and the sibling fields dropped — sound for
  single-field projection, as in the injectivity emitter). Pure Lean 4 core;
  axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtSelCtor_{hash}
open AySoundness

/-- The datatype abstracted to the projected field: one single-field constructor
    `mk` carrying the field value (`Int`), sibling fields dropped. -/
inductive D where
  | mk : Int -> D
  deriving DecidableEq

/-- The field-`i` selector as ay lowers it: it projects `mk`'s argument. -/
def sel : D -> Int | .mk a => a

/-- Theory model: the datatype value `X` and the field value `a` (= `aᵢ` = `v`). -/
structure Val where
  x : D
  a : Int

/-- Atoms: `1 ↦ (X = mk a)` (the ctor binding), `2 ↦ (sel X = a)`. -/
def atomVal (m : Val) : Nat -> Bool
  | 1 => decide (m.x = D.mk m.a)
  | 2 => decide (sel m.x = m.a)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [-2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, 2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- **Selector-over-constructor validity** — the firewall's premise (b):
    `X = mk a → sel X = a`. `by_cases` on the constructor equality; the positive
    branch reduces `sel (mk a) = a` by the selector definition. -/
theorem sel_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2] = true := by
  by_cases h : m.x = D.mk m.a
  · simp [clauseSat, litSat, atomVal, sel, h]
  · simp [clauseSat, litSat, atomVal, h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact sel_lemma_valid m

/-- `X = C(… aᵢ …) ∧ sᵢ X ≠ aᵢ` is unsatisfiable — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtSelCtor_{hash}
"#,
    )
}

/// Resolve the (result) sort simple-name of a `distinct` argument, using the
/// declared symbol→sort table. `ite` inherits its branch sort; a function /
/// constructor application takes the head's result sort; a bare symbol is a
/// declared constant/nullary-constructor. `None` (fail-closed) when unresolved.
fn enum_arg_sort(t: &PTerm, sym_sorts: &[(String, String)]) -> Option<String> {
    let lookup = |name: &str| -> Option<String> {
        sym_sorts
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, s)| s.clone())
    };
    match t {
        PTerm::Symbol(s) => lookup(s),
        PTerm::App(op, args) if op == "ite" && args.len() == 3 => {
            enum_arg_sort(&args[1], sym_sorts).or_else(|| enum_arg_sort(&args[2], sym_sorts))
        }
        PTerm::App(head, _) => lookup(head),
        _ => None,
    }
}

/// Emit a verified-firewall Lean proof for a DATATYPE ENUM-CARDINALITY
/// (pigeonhole) refutation over the PARSED (frontend) assertions: a
/// `(distinct T₀ … T_{n-1})` whose `n` arguments all inhabit a FINITE ENUM
/// datatype `D` (every constructor nullary) with only `k < n` constructors. By
/// pigeonhole, `n` values of a `k`-element type cannot be pairwise distinct, so
/// the assertion is unsatisfiable. The `n` derived Enum terms are abstracted to
/// `n` OPAQUE enum variables — any UF application `(f a)`, `ite`, or variable is
/// just an unknown element of `D` — and the pigeonhole is discharged by finite
/// case analysis (`cases … <;> decide`) inside the theory-lemma validity
/// obligation.
///
/// `sym_sorts` maps each declared symbol to its result-sort name (so the common
/// sort of the `distinct` arguments is resolved without a full sort checker;
/// `distinct` is well-typed, so all arguments share one sort — every argument is
/// required to resolve to the SAME `D`, fail-closed otherwise). `enum_datatypes`
/// lists exactly the finite-enum datatypes (all-nullary constructors) with their
/// constructor count `k`, computed by the caller from the datatype registry.
/// EMISSION-ONLY; grounded through `AySoundness.firewall_combined_unsat`; axioms
/// ⊆ {propext, Quot.sound}. Fail-closed (`None`) on any other shape.
pub(crate) fn emit_dt_enum_cardinality_firewall_lean_from_parsed(
    parsed: &[PTerm],
    enum_datatypes: &[(String, usize)],
    sym_sorts: &[(String, String)],
) -> Option<String> {
    // Flatten top-level `and` structure so a `distinct` buried in a conjunction
    // (sat/tautological noise around it) is still found.
    let mut conjs: Vec<&PTerm> = Vec::new();
    for a in parsed {
        flatten_dt_and(a, &mut conjs);
    }
    for c in &conjs {
        let PTerm::App(op, args) = c else {
            continue;
        };
        if op != "distinct" || args.len() < 2 {
            continue;
        }
        let n = args.len();
        // Bound the enumeration (k^n leaves in the pigeonhole `cases`): keep the
        // certificate small and fast to kernel-check. These are diagnostics.
        if n > 6 {
            continue;
        }
        // Every argument must resolve to the SAME datatype sort `D`.
        let mut common: Option<String> = None;
        let mut resolved = true;
        for arg in args {
            match enum_arg_sort(arg, sym_sorts) {
                Some(s) => match &common {
                    Some(prev) if prev != &s => {
                        resolved = false;
                        break;
                    }
                    Some(_) => {}
                    None => common = Some(s),
                },
                None => {
                    resolved = false;
                    break;
                }
            }
        }
        if !resolved {
            continue;
        }
        let Some(d) = common else {
            continue;
        };
        // `D` must be a finite enum (all-nullary constructors) with `k < n`.
        let Some((_, k)) = enum_datatypes.iter().find(|(name, _)| name == &d) else {
            continue;
        };
        let k = *k;
        if k == 0 || n <= k {
            continue;
        }
        return Some(render_enum_cardinality_lean(
            n,
            k,
            fnv_hex(&format!("dtenumcard:{c:?}:{d}:{n}:{k}")),
        ));
    }
    None
}

/// Render the enum-cardinality pigeonhole refutation, grounded in the verified
/// `firewall_combined_unsat`. `n` opaque enum variables over a `k`-nullary-
/// constructor inductive (`k < n`); each of the `P = n·(n-1)/2` atoms is a
/// pairwise equality `xᵢ = xⱼ`; the `distinct` asserts every atom FALSE
/// (`original` = `P` unit clauses `[-a]`), and the single pigeonhole lemma
/// clause `[1 … P]` (some pair is equal) is validated by exhaustive `cases`.
fn render_enum_cardinality_lean(n: usize, k: usize, hash: String) -> String {
    // Constructor list `k0 | k1 | … | k{k-1}`.
    let ctors = (0..k)
        .map(|i| format!("k{i}"))
        .collect::<Vec<_>>()
        .join(" | ");
    // Structure fields `x0 … x{n-1}`.
    let fields = (0..n)
        .map(|i| format!("  x{i} : EnumK"))
        .collect::<Vec<_>>()
        .join("\n");
    // Pair list in atom order (i < j), 1-based atom index.
    let pairs: Vec<(usize, usize)> = (0..n)
        .flat_map(|i| ((i + 1)..n).map(move |j| (i, j)))
        .collect();
    let p = pairs.len();
    // atomVal match arms.
    let arms = pairs
        .iter()
        .enumerate()
        .map(|(a, (i, j))| format!("  | {} => decide (m.x{i} = m.x{j})", a + 1))
        .collect::<Vec<_>>()
        .join("\n");
    // original: P unit clauses [-a].
    let original = (1..=p)
        .map(|a| format!("({a}, [-{a}])"))
        .collect::<Vec<_>>()
        .join(", ");
    // lemma clause [1 … P].
    let lemma_lits = (1..=p)
        .map(|a| a.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    // proof hints: all P original cids + the lemma cid.
    let proof_hints = (1..=(p + 1))
        .map(|a| a.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    // rcases binder `⟨x0, …, x{n-1}⟩` and the `cases … <;>` chain.
    let binder = (0..n)
        .map(|i| format!("x{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let cases_chain = (0..n)
        .map(|i| format!("cases x{i}"))
        .collect::<Vec<_>>()
        .join(" <;> ");
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE ENUM-CARDINALITY (pigeonhole)
  conflict grounded in the verified `firewall_combined_unsat`. The assertion
  `(distinct T₀ … T_{{{nm1}}})` over {n} terms of a FINITE ENUM datatype with only
  {k} (< {n}) constructors is unsatisfiable: by pigeonhole, {n} values of a
  {k}-element type cannot be pairwise distinct. The {n} derived Enum terms — any
  mix of variables, `ite`s and UF applications like `(f a)` — are abstracted to
  {n} OPAQUE enum variables (each is simply an unknown element of the enum; UF is
  projected away, no congruence involved). Faithful abstraction: the datatype is
  modeled by a genuine `{k}`-nullary-constructor inductive (fields collapsed —
  sound for cardinality reasoning, as nullary abstraction is to distinctness), and
  the pigeonhole is discharged by exhaustive finite `cases` (`{kn}` leaves).
  Reconstructed from the frontend parsed ASSERTIONS. Pure Lean 4 core; axioms ⊆
  {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtEnumCard_{hash}
open AySoundness

/-- The finite enum abstracted to its {k} constructor head-tags (fields dropped). -/
inductive EnumK where
  | {ctors}
  deriving DecidableEq

/-- Theory model: the {n} opaque enum values the `distinct` compares. -/
structure Val where
{fields}

/-- Atoms `1 … {p}` — the pairwise equalities `xᵢ = xⱼ` (`i < j`). -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

/-- `distinct` asserts every pairwise equality FALSE: {p} unit clauses `[-a]`. -/
def original : List (Cid × Clause) := [{original}]
/-- Pigeonhole lemma: at least one pair is equal — `[1 … {p}]`. -/
def lemmas   : List (Cid × Clause) := [({lemma_cid}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof_cid}, [], [{proof_hints}])]

/-- **Pigeonhole validity** — the firewall's premise (b): among {n} values of a
    {k}-element enum, some two are equal, so `⋁ᵢ<ⱼ (xᵢ = xⱼ)` holds in every
    model. Exhaustive `cases` over the {n} enum fields; each of the {kn} leaves is
    closed by `decide` (some pair collides). -/
theorem card_lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
  rcases m with ⟨{binder}⟩
  {cases_chain} <;> decide

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact card_lemma_valid m

/-- `(distinct …)` over {n} values of a {k}-element enum is unsatisfiable — via
    the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtEnumCard_{hash}
"#,
        nm1 = n - 1,
        kn = format!("{k}^{n}"),
        lemma_cid = p + 1,
        proof_cid = p + 2,
    )
}

/// Recognize a DISEQUALITY over exactly two operands — either `(distinct A B)`
/// (binary) or `(not (= A B))` — returning `(A, B)`. Used by the F3 emitter to
/// spot the asserted `f v1 ≠ f (f v2)` regardless of which disequality form the
/// frontend produced.
fn parsed_diseq_pair(t: &PTerm) -> Option<(&PTerm, &PTerm)> {
    let PTerm::App(op, args) = t else {
        return None;
    };
    match op.as_str() {
        "distinct" if args.len() == 2 => Some((&args[0], &args[1])),
        "not" if args.len() == 1 => {
            let PTerm::App(eq, ea) = &args[0] else {
                return None;
            };
            (eq == "=" && ea.len() == 2).then(|| (&ea[0], &ea[1]))
        }
        _ => None,
    }
}

/// Emit a verified-firewall Lean proof for the DATATYPE F3 (`f³ = f` on a
/// two-element enum) refutation over the PARSED (frontend) assertions: a
/// two-constructor ENUM datatype (every constructor nullary), a unary
/// uninterpreted function `fEnum : Enum → Enum` over it, and the two assertions
///
///   (= (fEnum v1) v2)                              — `f v1 = v2`
///   (distinct (fEnum v1) (fEnum (fEnum v2)))       — `f v1 ≠ f (f v2)`
///
/// On a two-element type EVERY self-map `f` satisfies `f x = f (f (f x))`, so
/// with `f v1 = v2` we get `f (f v2) = f (f (f v1)) = f v1`, contradicting
/// `f v1 ≠ f (f v2)`. ay's QF_UFDT pipeline refutes eagerly and folds the term
/// structure away (bare `(cl …) :rule trust`), so the shape is reconstructed
/// from the frontend assertions like the other datatype emitters and grounded in
/// the verified `AySoundness.Datatype.F3.f3_conflict` (built on `f3_eq_f`).
///
/// Faithful abstraction: the two-element enum is modeled by the concrete
/// `AySoundness.Datatype.F3.En` (two nullary constructors), and `fEnum` — an
/// UNINTERPRETED function — by an ARBITRARY `f : En → En`. The F3 theorem holds
/// for ALL `f`, so modeling the uninterpreted `fEnum` as an arbitrary function is
/// sound (nothing about `fEnum` beyond its type is used). Emission-only; grounded
/// through `AySoundness.firewall_combined_unsat`; axioms ⊆ {propext, Quot.sound}.
///
/// `enum_datatypes` lists the finite-enum datatypes (all-nullary constructors)
/// with their constructor count, and `sym_sorts` maps each declared symbol to its
/// result-sort name (so `(fEnum v1)` and `v1` are confirmed to inhabit the SAME
/// two-constructor enum, pinning `fEnum : En → En`). DECLINES (`None`) unless the
/// enum is EXACTLY two-constructor and the whole shape matches — fail-closed.
pub(crate) fn emit_dt_f3_firewall_lean_from_parsed(
    parsed: &[PTerm],
    enum_datatypes: &[(String, usize)],
    sym_sorts: &[(String, String)],
) -> Option<String> {
    // Flatten top-level `and` so the two assertions survive being buried in a
    // conjunction (sat/tautological noise around them is tolerated).
    let mut conjs: Vec<&PTerm> = Vec::new();
    for a in parsed {
        flatten_dt_and(a, &mut conjs);
    }
    for c in &conjs {
        // The disequality `f v1 ≠ f (f v2)` (either operand order).
        let Some((x, y)) = parsed_diseq_pair(c) else {
            continue;
        };
        for (fa, ffb) in [(x, y), (y, x)] {
            // fa = (F v1): a unary application of some symbol `F` to a variable.
            let PTerm::App(f1, fa_args) = fa else {
                continue;
            };
            if fa_args.len() != 1 {
                continue;
            }
            let PTerm::Symbol(v1) = &fa_args[0] else {
                continue;
            };
            // ffb = (F (F v2)): the SAME `F` applied twice to a variable.
            let PTerm::App(f2, ffb_args) = ffb else {
                continue;
            };
            if f2 != f1 || ffb_args.len() != 1 {
                continue;
            }
            let PTerm::App(f3, inner_args) = &ffb_args[0] else {
                continue;
            };
            if f3 != f1 || inner_args.len() != 1 {
                continue;
            }
            let PTerm::Symbol(v2) = &inner_args[0] else {
                continue;
            };
            // `(F v1)` must inhabit a two-constructor enum, and `v1` the SAME enum
            // (so `F : En → En` is faithful). DECLINE otherwise — fail-closed.
            let Some(en) = enum_arg_sort(fa, sym_sorts) else {
                continue;
            };
            if !enum_datatypes.iter().any(|(n, k)| n == &en && *k == 2) {
                continue;
            }
            if enum_arg_sort(&fa_args[0], sym_sorts).as_deref() != Some(en.as_str()) {
                continue;
            }
            // The positive equality `(= (F v1) v2)` (either orientation), on the
            // SAME `F`, `v1`, `v2`.
            let has_pos = conjs.iter().any(|p| {
                let PTerm::App(op, a) = p else {
                    return false;
                };
                if op != "=" || a.len() != 2 {
                    return false;
                }
                for (l, r) in [(&a[0], &a[1]), (&a[1], &a[0])] {
                    let PTerm::App(g, ga) = l else {
                        continue;
                    };
                    if g != f1 || ga.len() != 1 {
                        continue;
                    }
                    let PTerm::Symbol(lv1) = &ga[0] else {
                        continue;
                    };
                    if lv1 != v1 {
                        continue;
                    }
                    if matches!(r, PTerm::Symbol(rv2) if rv2 == v2) {
                        return true;
                    }
                }
                false
            });
            if has_pos {
                return Some(render_dt_f3_lean(fnv_hex(&format!(
                    "dtf3:{c:?}:{f1}:{v1}:{v2}"
                ))));
            }
        }
    }
    None
}

/// Render the F3 (`f³ = f` on a 2-element enum) refutation, grounded in the
/// verified `AySoundness.Datatype.F3.f3_conflict` (which is built on `f3_eq_f`)
/// and discharged through `AySoundness.firewall_combined_unsat`. The model is the
/// concrete two-nullary-constructor `En` with an arbitrary `f : En → En`; the two
/// atoms are `f v1 = v2` and `f v1 = f (f v2)`. The body is a constant template
/// up to the namespace hash.
fn render_dt_f3_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
import AySoundness.Datatype
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE F3 (`f³ = f` on a 2-element
  enum) conflict grounded in the verified `firewall_combined_unsat`. Over a
  two-constructor ENUM datatype with an uninterpreted `fEnum : Enum → Enum`, the
  assertions `fEnum v1 = v2` and `fEnum v1 ≠ fEnum (fEnum v2)` are unsatisfiable:
  on a two-element type EVERY self-map `f` satisfies `f x = f (f (f x))`, so with
  `f v1 = v2` we get `f (f v2) = f (f (f v1)) = f v1`, contradicting the
  disequality. Reconstructed from the frontend parsed ASSERTIONS (ay refutes
  QF_UFDT eagerly and folds the term structure away before emit). Faithful
  abstraction: the two-element enum is the concrete two-nullary-constructor
  `AySoundness.Datatype.F3.En`, and the UNINTERPRETED `fEnum` an ARBITRARY
  `f : En → En` — the F3 theorem holds for ALL `f`, so nothing about `fEnum`
  beyond its type is assumed. Discharged through
  `AySoundness.Datatype.F3.f3_conflict` (built on `f3_eq_f`). Pure Lean 4 core;
  axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtF3_{hash}
open AySoundness

/-- Theory model: an ARBITRARY self-map `f` on the concrete two-element enum
    `En`, plus the two enum points `v1`, `v2`. Modeling the uninterpreted
    `fEnum` as an arbitrary `f` is sound — `f3_conflict` holds for every `f`. -/
structure Val where
  f : AySoundness.Datatype.F3.En -> AySoundness.Datatype.F3.En
  v1 : AySoundness.Datatype.F3.En
  v2 : AySoundness.Datatype.F3.En

/-- Atoms: `1 ↦ (f v1 = v2)`, `2 ↦ (f v1 = f (f v2))`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.f m.v1 = m.v2)
  | 2 => decide (m.f m.v1 = m.f (m.f m.v2))
  | _ => false

/-- `fEnum v1 = v2` is `[1]`; the disequality `fEnum v1 ≠ fEnum (fEnum v2)`
    is `[-2]`. -/
def original : List (Cid × Clause) := [(1, [1]), (2, [-2])]
/-- The F3-collapse lemma `f v1 = v2 → f v1 = f (f v2)`, i.e. `[-1, 2]`. -/
def lemmas   : List (Cid × Clause) := [(3, [-1, 2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- **F3-collapse validity** — the firewall's premise (b): if `f v1 = v2` then
    `f v1 = f (f v2)`, so `⟨¬(f v1 = v2)⟩ ∨ ⟨f v1 = f (f v2)⟩` holds in every
    model. The nontrivial branch is closed by the verified
    `AySoundness.Datatype.F3.f3_conflict` (which is built on `f3_eq_f`); the
    case split is over the DECIDABLE equality on `En` (no `Classical`). -/
theorem f3_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2] = true := by
  by_cases h1 : m.f m.v1 = m.v2
  · by_cases h2 : m.f m.v1 = m.f (m.f m.v2)
    · simp [clauseSat, litSat, atomVal, h2]
    · exact (AySoundness.Datatype.F3.f3_conflict m.f m.v1 m.v2 h1 h2).elim
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact f3_lemma_valid m

/-- `fEnum v1 = v2 ∧ fEnum v1 ≠ fEnum (fEnum v2)` is unsatisfiable — via the
    verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtF3_{hash}
"#,
    )
}

/// A sound, UNCONDITIONAL boolean+datatype constant-fold that ALSO substitutes a
/// map of FORCED Boolean units (`env`, derived only from sibling unit
/// assertions) into `ite`/`and`/`or`/`not` guards. Substituting an entailed unit
/// preserves satisfiability of the whole assertion conjunction, so the folded
/// residual is unsat iff the conjunction is. Extends [`fold_dt_term`] with:
///   * a known Boolean variable `v` (in `env`) → its constant;
///   * `(and …)`/`(or …)`/`(not …)` over Boolean constants → the constant;
/// everything else as in `fold_dt_term` (reflexive `ite`, `ite` on constant
/// guard, tester on a constructor application). Applied bottom-up.
fn fold_bool_dt_term(
    term: &PTerm,
    is_ctor: &impl Fn(&str) -> bool,
    env: &std::collections::HashMap<String, bool>,
) -> PTerm {
    match term {
        PTerm::Symbol(s) => {
            if let Some(b) = env.get(s) {
                return PTerm::Const(if *b { PConst::True } else { PConst::False });
            }
            term.clone()
        }
        PTerm::App(op, args) => {
            let fargs: Vec<PTerm> = args
                .iter()
                .map(|a| fold_bool_dt_term(a, is_ctor, env))
                .collect();
            match op.as_str() {
                "not" if fargs.len() == 1 => match &fargs[0] {
                    PTerm::Const(PConst::True) => return PTerm::Const(PConst::False),
                    PTerm::Const(PConst::False) => return PTerm::Const(PConst::True),
                    _ => {}
                },
                "and" => {
                    let mut kept: Vec<PTerm> = Vec::new();
                    for a in &fargs {
                        match a {
                            PTerm::Const(PConst::False) => return PTerm::Const(PConst::False),
                            PTerm::Const(PConst::True) => {}
                            _ => kept.push(a.clone()),
                        }
                    }
                    return match kept.len() {
                        0 => PTerm::Const(PConst::True),
                        1 => kept.pop().unwrap(),
                        _ => PTerm::App("and".to_string(), kept),
                    };
                }
                "or" => {
                    let mut kept: Vec<PTerm> = Vec::new();
                    for a in &fargs {
                        match a {
                            PTerm::Const(PConst::True) => return PTerm::Const(PConst::True),
                            PTerm::Const(PConst::False) => {}
                            _ => kept.push(a.clone()),
                        }
                    }
                    return match kept.len() {
                        0 => PTerm::Const(PConst::False),
                        1 => kept.pop().unwrap(),
                        _ => PTerm::App("or".to_string(), kept),
                    };
                }
                "ite" if fargs.len() == 3 => {
                    match &fargs[0] {
                        PTerm::Const(PConst::True) => return fargs[1].clone(),
                        PTerm::Const(PConst::False) => return fargs[2].clone(),
                        _ => {}
                    }
                    if fargs[1] == fargs[2] {
                        return fargs[1].clone();
                    }
                }
                _ => {}
            }
            PTerm::App(op.clone(), fargs)
        }
        PTerm::IndexedApp(name, idx, args) => {
            let fargs: Vec<PTerm> = args
                .iter()
                .map(|a| fold_bool_dt_term(a, is_ctor, env))
                .collect();
            if name == "is" && idx.len() == 1 && fargs.len() == 1 {
                if let Some(d) = idx[0].as_symbol() {
                    match &fargs[0] {
                        PTerm::App(head, _) if is_ctor(head) && is_ctor(d) => {
                            return PTerm::Const(if head == d {
                                PConst::True
                            } else {
                                PConst::False
                            });
                        }
                        PTerm::Symbol(head) if is_ctor(head) && is_ctor(d) => {
                            return PTerm::Const(if head == d {
                                PConst::True
                            } else {
                                PConst::False
                            });
                        }
                        _ => {}
                    }
                }
            }
            PTerm::IndexedApp(name.clone(), idx.clone(), fargs)
        }
        _ => term.clone(),
    }
}

/// Collect FORCED Boolean units from the top-level assertions: an assertion that
/// (after boolean folding) reduces to a bare Boolean variable `v` forces `v =
/// true`; `(not v)` forces `v = false`. Only genuine unit assertions contribute
/// (a `(not (and v true))` folds to `(not v)`, a unit). Two fixpoint passes let
/// one forced unit unlock another.
fn collect_dt_bool_env(
    parsed: &[PTerm],
    is_ctor: &impl Fn(&str) -> bool,
) -> std::collections::HashMap<String, bool> {
    let mut env: std::collections::HashMap<String, bool> = std::collections::HashMap::new();
    for _ in 0..2 {
        let snapshot = env.clone();
        for a in parsed {
            match &fold_bool_dt_term(a, is_ctor, &snapshot) {
                PTerm::Symbol(s) => {
                    env.insert(s.clone(), true);
                }
                PTerm::App(op, args) if op == "not" && args.len() == 1 => {
                    if let PTerm::Symbol(s) = &args[0] {
                        env.insert(s.clone(), false);
                    }
                }
                _ => {}
            }
        }
    }
    env
}

/// Collect every `ite` subterm of `term` (in pre-order).
fn collect_ite_subterms<'a>(term: &'a PTerm, out: &mut Vec<&'a PTerm>) {
    match term {
        PTerm::App(op, args) => {
            if op == "ite" && args.len() == 3 {
                out.push(term);
            }
            for a in args {
                collect_ite_subterms(a, out);
            }
        }
        PTerm::IndexedApp(_, _, args) => {
            for a in args {
                collect_ite_subterms(a, out);
            }
        }
        _ => {}
    }
}

/// Whether `g` is a constructor tester `((_ is C) v)`.
fn is_tester_term(g: &PTerm) -> bool {
    matches!(g, PTerm::IndexedApp(name, idx, args)
        if name == "is" && idx.len() == 1 && args.len() == 1)
}

/// Structurally replace every occurrence of `target` in `term` with `repl`.
fn replace_dt_subterm(term: &PTerm, target: &PTerm, repl: &PTerm) -> PTerm {
    if term == target {
        return repl.clone();
    }
    match term {
        PTerm::App(op, args) => PTerm::App(
            op.clone(),
            args.iter()
                .map(|a| replace_dt_subterm(a, target, repl))
                .collect(),
        ),
        PTerm::IndexedApp(name, idx, args) => PTerm::IndexedApp(
            name.clone(),
            idx.clone(),
            args.iter()
                .map(|a| replace_dt_subterm(a, target, repl))
                .collect(),
        ),
        _ => term.clone(),
    }
}

/// Emit a verified-firewall Lean proof for a DATATYPE TESTER-GUARDED CASE-SPLIT
/// refutation whose BOTH branches are ACYCLICITY occurs-checks, over the PARSED
/// (frontend) assertions. After (a) substituting any FORCED Boolean unit from a
/// sibling unit-assertion and (b) sound constant-folding, a residual equality
/// `t = C(… ite g A B …)` remains, where `g` is a constructor tester, `t` a bare
/// variable, and BOTH branch-substitutions `C(… A …)` and `C(… B …)` contain `t`
/// as a proper subterm under ≥1 constructor layer. Whatever value the tester
/// takes, `t` equals a strictly-larger context of itself — unsatisfiable by
/// acyclicity in either branch. The split is carried as a `by_cases` on the
/// (opaque) guard inside the theory-lemma validity obligation, each branch
/// discharged by `AySoundness.Datatype.acyclic_conflict_generic` at that branch's
/// occurrence depth.
///
/// This is the tester-guarded, nested-under-a-constructor analog of the boolean-
/// ite-guard case split: there the `ite` is the WHOLE non-constructor side; here
/// it sits under a constructor layer with a bare-variable other side, and the two
/// branches may occur at DIFFERENT depths. EMISSION-ONLY; grounded through
/// `AySoundness.firewall_combined_unsat`; axioms ⊆ {propext, Quot.sound}.
/// Fail-closed (`None`) on any other shape.
pub(crate) fn emit_dt_tester_casesplit_occurs_firewall_lean_from_parsed(
    parsed: &[PTerm],
    constructors: &[String],
) -> Option<String> {
    let is_ctor = |name: &str| constructors.iter().any(|c| c == name);
    let env = collect_dt_bool_env(parsed, &is_ctor);
    for asrt in parsed {
        let folded = fold_bool_dt_term(asrt, &is_ctor, &env);
        let PTerm::App(eqop, eqa) = &folded else {
            continue;
        };
        if eqop != "=" || eqa.len() != 2 {
            continue;
        }
        for (lhs, rhs) in [(&eqa[0], &eqa[1]), (&eqa[1], &eqa[0])] {
            let PTerm::Symbol(t) = lhs else {
                continue;
            };
            if is_ctor(t) {
                continue;
            }
            // `rhs` must be a constructor application …
            let PTerm::App(rhead, _) = rhs else {
                continue;
            };
            if !is_ctor(rhead) {
                continue;
            }
            // … containing EXACTLY one `ite`, tester-guarded with ite-free
            // branches.
            let mut ites: Vec<&PTerm> = Vec::new();
            collect_ite_subterms(rhs, &mut ites);
            if ites.len() != 1 {
                continue;
            }
            let PTerm::App(_, ia) = ites[0] else {
                continue;
            };
            if !is_tester_term(&ia[0]) {
                continue;
            }
            let (a_branch, b_branch) = (&ia[1], &ia[2]);
            // branches must be free of further `ite`s (fully case-split).
            let mut nested: Vec<&PTerm> = Vec::new();
            collect_ite_subterms(a_branch, &mut nested);
            collect_ite_subterms(b_branch, &mut nested);
            if !nested.is_empty() {
                continue;
            }
            let ite_term = ites[0].clone();
            let bt = replace_dt_subterm(rhs, &ite_term, a_branch);
            let bf = replace_dt_subterm(rhs, &ite_term, b_branch);
            let (Some(dt), Some(df)) = (
                occurs_ctor_depth(&bt, t, &is_ctor).filter(|d| *d >= 1),
                occurs_ctor_depth(&bf, t, &is_ctor).filter(|d| *d >= 1),
            ) else {
                continue;
            };
            return Some(render_dt_var_casesplit_occurs_lean(
                dt,
                df,
                fnv_hex(&format!("dttestercs:{asrt:?}:{t}:{dt}:{df}")),
            ));
        }
    }
    None
}

/// Render the tester-guarded both-branches-occurs case split, grounded in the
/// verified `firewall_combined_unsat`. `true_depth`/`false_depth` are the
/// occurrence depths of `t` under the then/else branches; the single lemma clause
/// `[-1]` is validated by `by_cases` on the opaque guard, each branch discharged
/// by `AySoundness.Datatype.acyclic_conflict_generic` at its depth.
fn render_dt_var_casesplit_occurs_lean(
    true_depth: usize,
    false_depth: usize,
    hash: String,
) -> String {
    let wrap_layers = |d: usize| -> String {
        let mut body = String::from("z");
        for _ in 0..d {
            body = format!("DtT.wrap ({body})");
        }
        body
    };
    let ctx_t = wrap_layers(true_depth);
    let ctx_f = wrap_layers(false_depth);
    format!(
        r#"import AySoundness.Firewall
import AySoundness.Datatype
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE TESTER-GUARDED CASE-SPLIT
  (both branches ACYCLICITY occurs-checks) grounded in the verified
  `firewall_combined_unsat`. The residual assertion `t = C(… ite g A B …)` (a
  bare variable `t` equal to a constructor context wrapping a tester-guarded
  `ite`) is unsatisfiable: `by_cases` on the (opaque) tester guard reduces the
  `ite` to one branch, and in EITHER branch `t` occurs as a PROPER subterm under
  ≥1 constructor layer ({true_depth} layer(s) in the then-branch, {false_depth} in
  the else-branch), so `sizeOf t < sizeOf (context t)` and no `t` can equal it.
  Reconstructed from the frontend parsed ASSERTIONS after (a) substituting a
  FORCED Boolean unit from a sibling unit-assertion (entailed by the query, so
  satisfiability-preserving) and (b) sound constant-folding of reflexive `ite`s /
  tautological testers. Faithful abstraction: each constructor layer is modeled by
  the self-recursive `wrap : DtT → DtT` (strictly `sizeOf`-increasing as any real
  constructor), sibling fields dropped (irrelevant to acyclicity), and the tester
  guard abstracted to an arbitrary `Bool` (the conflict holds for BOTH values).
  Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtTesterCaseSplit_{hash}
open AySoundness

/-- The datatype abstracted to its recursive spine: one self-recursive
    constructor (`wrap`, one per occurrence layer) plus a base point. -/
inductive DtT where
  | wrap : DtT → DtT
  | base
deriving DecidableEq

/-- Theory model: the opaque tester guard `g` and the datatype value `t`. -/
structure Val where
  g : Bool
  t : DtT

/-- Then-branch occurrence context `ctxT z := C(… z …)` — {true_depth} `wrap`
    layer(s). -/
def ctxT (z : DtT) : DtT := {ctx_t}
/-- Else-branch occurrence context `ctxF z := C(… z …)` — {false_depth} `wrap`
    layer(s). -/
def ctxF (z : DtT) : DtT := {ctx_f}

/-- Atom `1 ↦ (t = C(… ite g A B …))` — the residual tester-guarded equality,
    with the constructor spine of each branch abstracted to its `wrap` depth and
    the guard to the opaque Boolean `g`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.t = (cond m.g (ctxT m.t) (ctxF m.t)))
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

/-- **Case-split lemma validity** — the firewall's premise (b): the residual
    equality is false in every model. `by_cases` on the guard reduces the `cond`;
    each branch is an acyclicity conflict at its occurrence depth. -/
theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have h : m.t ≠ (cond m.g (ctxT m.t) (ctxF m.t)) := by
    cases hg : m.g
    · show m.t ≠ ctxF m.t
      exact AySoundness.Datatype.acyclic_conflict_generic (t := m.t) (ctx := ctxF)
        (by simp only [ctxF, DtT.wrap.sizeOf_spec]; omega)
    · show m.t ≠ ctxT m.t
      exact AySoundness.Datatype.acyclic_conflict_generic (t := m.t) (ctx := ctxT)
        (by simp only [ctxT, DtT.wrap.sizeOf_spec]; omega)
  simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil, h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No datatype model satisfies the tester-guarded case-split equality — via the
    verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtTesterCaseSplit_{hash}
"#,
    )
}

/// Abstract a datatype term into a Lean expression over the concrete `Tree`
/// datatype of `AySoundness.Datatype` (`leaf | node Tree Tree`), the faithful
/// binary-tree spine every real algebraic datatype maps onto: a constructor with
/// EXACTLY 2 recursive (same-datatype) fields becomes `Tree.node` (its two
/// recursive children mapped, sibling non-recursive fields dropped), a
/// constructor with 0 recursive fields becomes `Tree.leaf` (all fields dropped).
/// A bare datatype VARIABLE becomes a fresh `Val` field `m.t{i}` (registered in
/// `tree_vars`, de-duplicated by name) — unless it is the occurs variable named
/// by `occ_repl`, which is emitted as the literal `z` (for building the
/// acyclicity context `fun z => …`). `None` (fail-closed) on any non-abstractable
/// head — a selector, a UF application, an `ite`, a constructor whose recursive
/// arity is not 0 or 2, or a missing recursive-field record.
fn abstract_tree_term(
    term: &PTerm,
    is_ctor: &impl Fn(&str) -> bool,
    rec_of: &impl Fn(&str) -> Option<Vec<bool>>,
    occ_repl: Option<&str>,
    tree_vars: &mut Vec<String>,
) -> Option<String> {
    const LEAF: &str = "AySoundness.Datatype.Tree.leaf";
    match term {
        PTerm::Symbol(s) => {
            if is_ctor(s) {
                // A nullary constructor abstracts to the recursive base point.
                let rec = rec_of(s)?;
                if rec.iter().filter(|b| **b).count() == 0 {
                    Some(LEAF.to_string())
                } else {
                    None
                }
            } else if occ_repl == Some(s.as_str()) {
                Some("z".to_string())
            } else {
                let idx = match tree_vars.iter().position(|v| v == s) {
                    Some(i) => i,
                    None => {
                        tree_vars.push(s.clone());
                        tree_vars.len() - 1
                    }
                };
                Some(format!("m.t{idx}"))
            }
        }
        PTerm::App(head, args) => {
            if !is_ctor(head) {
                return None;
            }
            let rec = rec_of(head)?;
            if rec.len() != args.len() {
                return None;
            }
            let rec_pos: Vec<usize> = (0..rec.len()).filter(|&i| rec[i]).collect();
            match rec_pos.len() {
                0 => Some(LEAF.to_string()),
                2 => {
                    let c0 = abstract_tree_term(
                        &args[rec_pos[0]],
                        is_ctor,
                        rec_of,
                        occ_repl,
                        tree_vars,
                    )?;
                    let c1 = abstract_tree_term(
                        &args[rec_pos[1]],
                        is_ctor,
                        rec_of,
                        occ_repl,
                        tree_vars,
                    )?;
                    Some(format!("AySoundness.Datatype.Tree.node ({c0}) ({c1})"))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The abstract head-class of a datatype term under the binary-`Tree` spine:
/// `Some("node")` for a constructor application / symbol with exactly 2 recursive
/// fields, `Some("leaf")` for one with 0. `None` for anything else (a variable,
/// a selector, a UF app). Two DISTINCT classes on the same linking variable
/// witness a constructor-DISTINCTNESS conflict (`node ≠ leaf`).
fn tree_head_class(
    term: &PTerm,
    is_ctor: &impl Fn(&str) -> bool,
    rec_of: &impl Fn(&str) -> Option<Vec<bool>>,
) -> Option<&'static str> {
    let head = match term {
        PTerm::Symbol(s) if is_ctor(s) => s,
        PTerm::App(h, _) if is_ctor(h) => h,
        _ => return None,
    };
    match rec_of(head)?.iter().filter(|b| **b).count() {
        0 => Some("leaf"),
        2 => Some("node"),
        _ => None,
    }
}

/// Emit a verified-firewall Lean proof for a DATATYPE TESTER-GUARDED CASE-SPLIT
/// whose two branches are discharged by DIFFERENT verified datatype lemmas — a
/// MIXED conflict — over the PARSED (frontend) assertions. After boolean folding,
/// a residual `(ite g A B) = R` remains, where `g` is a constructor tester, `R` a
/// constructor application, and the two `by_cases` branches on the (opaque) guard
/// discharge as:
///   * else-branch (`g = false`): `B = R` is an ACYCLICITY occurs-check — `B` is
///     a bare variable occurring as a proper subterm of `R`
///     (`AySoundness.Datatype.acyclic_conflict_generic`);
///   * then-branch (`g = true`): `A = R` is a constructor DISTINCTNESS conflict —
///     `A` and `R` are the SAME constructor, and projecting their children (via
///     `AySoundness.Datatype.Tree.node_inj`) forces some variable to equal both a
///     `node`-headed and a `leaf`-headed term, which no value satisfies
///     (`AySoundness.Datatype.Tree.node_ne_leaf`).
///
/// This GENERALIZES the both-branches-occurs
/// [`emit_dt_tester_casesplit_occurs_firewall_lean_from_parsed`]: each `by_cases`
/// branch is discharged by its OWN lemma. The datatype is faithfully abstracted
/// onto the concrete binary `Tree` of `AySoundness.Datatype` (a constructor with
/// 2 recursive fields ↦ `Tree.node`, 0 ↦ `Tree.leaf`, sibling non-recursive
/// fields dropped, the tester guard abstracted to an opaque `Bool`). A real model
/// maps homomorphically onto this abstraction, so no-abstract-model ⟹
/// no-real-model. EMISSION-ONLY; grounded through
/// `AySoundness.firewall_combined_unsat`; axioms ⊆ {propext, Quot.sound}.
/// Fail-closed (`None`) on any other shape. `ctor_rec` is the per-constructor
/// recursive-field mask (`true` at a field of the constructor's OWN datatype).
pub(crate) fn emit_dt_tester_casesplit_mixed_firewall_lean_from_parsed(
    parsed: &[PTerm],
    constructors: &[String],
    ctor_rec: &[(String, Vec<bool>)],
) -> Option<String> {
    let is_ctor = |name: &str| constructors.iter().any(|c| c == name);
    let rec_of = |ctor: &str| -> Option<Vec<bool>> {
        ctor_rec
            .iter()
            .find(|(c, _)| c == ctor)
            .map(|(_, v)| v.clone())
    };
    let env = collect_dt_bool_env(parsed, &is_ctor);
    for asrt in parsed {
        let folded = fold_bool_dt_term(asrt, &is_ctor, &env);
        let PTerm::App(eqop, eqa) = &folded else {
            continue;
        };
        if eqop != "=" || eqa.len() != 2 {
            continue;
        }
        for (lhs, rhs) in [(&eqa[0], &eqa[1]), (&eqa[1], &eqa[0])] {
            // `lhs` must be a top-level tester-guarded `ite` with fully-folded
            // (ite-free) branches; `rhs` a constructor application.
            let PTerm::App(iop, ia) = lhs else {
                continue;
            };
            if iop != "ite" || ia.len() != 3 || !is_tester_term(&ia[0]) {
                continue;
            }
            let (a_branch, b_branch) = (&ia[1], &ia[2]);
            let mut nested: Vec<&PTerm> = Vec::new();
            collect_ite_subterms(a_branch, &mut nested);
            collect_ite_subterms(b_branch, &mut nested);
            collect_ite_subterms(rhs, &mut nested);
            if !nested.is_empty() {
                continue;
            }
            let PTerm::App(rhead, _) = rhs else {
                continue;
            };
            if !is_ctor(rhead) {
                continue;
            }
            // ---- else-branch (g = false): OCCURS-check. `b_branch` a bare
            // variable occurring as a proper subterm of `rhs`.
            let PTerm::Symbol(occ_var) = b_branch else {
                continue;
            };
            if is_ctor(occ_var)
                || occurs_ctor_depth(rhs, occ_var, &is_ctor).is_none_or(|depth| depth < 1)
            {
                continue;
            }
            // ---- then-branch (g = true): DISTINCTNESS. `a_branch` and `rhs`
            // must be the SAME constructor (a 2-recursive-field `node`-like head),
            // and projecting their recursive children pairwise must force some
            // variable to two DISTINCT abstract head-classes (`node` vs `leaf`).
            let (PTerm::App(ahead, aargs), PTerm::App(_, rargs)) = (a_branch, rhs) else {
                continue;
            };
            if ahead != rhead {
                continue;
            }
            let Some(rec) = rec_of(ahead) else { continue };
            if rec.len() != aargs.len() || rec.len() != rargs.len() {
                continue;
            }
            let rec_pos: Vec<usize> = (0..rec.len()).filter(|&i| rec[i]).collect();
            if rec_pos.len() != 2 {
                continue;
            }
            // Accumulate, per linking variable, the abstract head-classes it is
            // directly equated with across the two recursive-child pairs.
            let mut classes: std::collections::HashMap<&str, std::collections::BTreeSet<&str>> =
                std::collections::HashMap::new();
            for &p in &rec_pos {
                for (v_side, c_side) in [(&aargs[p], &rargs[p]), (&rargs[p], &aargs[p])] {
                    if let PTerm::Symbol(w) = v_side {
                        if !is_ctor(w) {
                            if let Some(cls) = tree_head_class(c_side, &is_ctor, &rec_of) {
                                classes.entry(w).or_default().insert(cls);
                            }
                        }
                    }
                }
            }
            if !classes.values().any(|s| s.len() >= 2) {
                continue;
            }
            // Build the abstract `Tree` terms. Field indices are assigned in a
            // deterministic first-seen order across then / else / rhs.
            let mut tree_vars: Vec<String> = Vec::new();
            let (Some(then_abs), Some(else_abs), Some(rhs_abs)) = (
                abstract_tree_term(a_branch, &is_ctor, &rec_of, None, &mut tree_vars),
                abstract_tree_term(b_branch, &is_ctor, &rec_of, None, &mut tree_vars),
                abstract_tree_term(rhs, &is_ctor, &rec_of, None, &mut tree_vars),
            ) else {
                continue;
            };
            // The occurs context `fun z => rhs[occ_var := z]`; `z` must actually
            // appear (occ_var reached through a recursive path) so the acyclicity
            // `sizeOf` hypothesis is discharge-able.
            let Some(rhs_ctx) =
                abstract_tree_term(rhs, &is_ctor, &rec_of, Some(occ_var), &mut tree_vars)
            else {
                continue;
            };
            if !rhs_ctx.contains('z') {
                continue;
            }
            return Some(render_dt_casesplit_mixed_lean(
                tree_vars.len(),
                &then_abs,
                &else_abs,
                &rhs_abs,
                &rhs_ctx,
                fnv_hex(&format!("dtmixed:{asrt:?}:{ahead}:{occ_var}")),
            ));
        }
    }
    None
}

/// Render the MIXED tester-guarded case-split Lean: a `by_cases` on the opaque
/// tester guard whose else-branch is an ACYCLICITY occurs-check
/// (`acyclic_conflict_generic`) and whose then-branch is a constructor
/// DISTINCTNESS conflict (`node_inj` + `node_ne_leaf`, closed by `simp_all`),
/// grounded in the verified `firewall_combined_unsat`. `n_vars` `Tree` fields plus
/// the `Bool` guard model the theory; each `t{i}` is a datatype variable, the
/// abstract terms are the binary-`Tree` images of the residual equality's sides.
fn render_dt_casesplit_mixed_lean(
    n_vars: usize,
    then_abs: &str,
    else_abs: &str,
    rhs_abs: &str,
    rhs_ctx: &str,
    hash: String,
) -> String {
    use std::fmt::Write as _;

    let mut val_fields = String::new();
    for i in 0..n_vars {
        writeln!(&mut val_fields, "  t{i} : AySoundness.Datatype.Tree")
            .expect("writing to a String cannot fail");
    }
    format!(
        r#"import AySoundness.Firewall
import AySoundness.Datatype
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE TESTER-GUARDED CASE-SPLIT with
  a MIXED conflict (a DIFFERENT verified lemma per branch), grounded in the
  verified `firewall_combined_unsat`. The residual assertion `(ite g A B) = R` (a
  tester-guarded `ite` equal to a constructor application `R`) is unsatisfiable:
  `by_cases` on the (opaque) tester guard `g` reduces the `ite` to one branch, and
    * the ELSE branch (`g = false`) gives `B = R` with the bare variable `B`
      occurring as a PROPER subterm of `R` — an ACYCLICITY occurs-check, refuted
      by `AySoundness.Datatype.acyclic_conflict_generic` (`sizeOf B < sizeOf R`);
    * the THEN branch (`g = true`) gives `A = R` with `A` and `R` the SAME
      constructor; projecting their children (`Tree.node_inj`) forces a variable
      to equal both a `node`-headed and a `leaf`-headed term — a constructor
      DISTINCTNESS conflict, refuted by `AySoundness.Datatype.Tree.node_ne_leaf`.
  Reconstructed from the frontend parsed ASSERTIONS after (a) substituting any
  FORCED Boolean unit from a sibling unit-assertion (entailed by the query, so
  satisfiability-preserving) and (b) sound constant-folding of reflexive `ite`s /
  tautological testers. Faithful abstraction: the datatype maps homomorphically
  onto the concrete binary `Tree` of `AySoundness.Datatype` (a constructor with 2
  recursive fields ↦ `Tree.node`, 0 ↦ `Tree.leaf`, sibling non-recursive fields
  dropped, the tester guard abstracted to an arbitrary `Bool`), so no abstract
  model ⟹ no real model. Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtTesterCaseSplitMixed_{hash}
open AySoundness

/-- Theory model: the opaque tester guard `g` and the datatype variables. -/
structure Val where
  g : Bool
{val_fields}
/-- Atom `1 ↦ ((ite g A B) = R)` — the residual tester-guarded equality, each
    side mapped onto the binary-`Tree` spine with the guard abstracted to `g`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (cond m.g ({then_abs}) ({else_abs}) = {rhs_abs})
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

/-- **Case-split lemma validity** — the firewall's premise (b): the residual
    equality is false in every model. `by_cases` on the guard reduces the `cond`;
    the else-branch is an acyclicity occurs-check, the then-branch a constructor
    distinctness conflict (MIXED — a different lemma per branch). -/
theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have h : ¬ (cond m.g ({then_abs}) ({else_abs}) = {rhs_abs}) := by
    cases hg : m.g
    · -- else-branch (g = false): ACYCLICITY occurs-check.
      show ({else_abs}) ≠ {rhs_abs}
      exact AySoundness.Datatype.acyclic_conflict_generic
        (t := {else_abs})
        (ctx := fun z => {rhs_ctx})
        (by simp only [AySoundness.Datatype.Tree.node.sizeOf_spec]; omega)
    · -- then-branch (g = true): constructor DISTINCTNESS (node ≠ leaf).
      show ({then_abs}) ≠ {rhs_abs}
      intro heq
      obtain ⟨hl, hr⟩ := AySoundness.Datatype.Tree.node_inj heq
      simp_all
  simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil, h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No datatype model satisfies the mixed tester-guarded case-split equality — via
    the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtTesterCaseSplitMixed_{hash}
"#,
    )
}

/// Single-level constant-condition `ite` fold: `(ite true a b) ⟶ a`,
/// `(ite false a b) ⟶ b` (recursively on the taken branch). Any other term is
/// returned unchanged. Used to normalize the assert2 `(ite false …)` wrapper of
/// the nested selector-guarded case split before structural matching.
fn strip_const_ite(t: &PTerm) -> &PTerm {
    if let PTerm::App(op, a) = t {
        if op == "ite" && a.len() == 3 {
            match &a[0] {
                PTerm::Const(PConst::True) => return strip_const_ite(&a[1]),
                PTerm::Const(PConst::False) => return strip_const_ite(&a[2]),
                _ => {}
            }
        }
    }
    t
}

/// Emit a verified-firewall Lean proof for a NESTED SELECTOR-GUARDED datatype
/// case split — the shape of
/// `benchmarks/…/soundness_qf_dt_derived_terms/fuzz_ufdt_falsesat_881.smt2`.
///
/// The two residual assertions (over a binary-recursive constructor `nd` — one
/// with EXACTLY two same-datatype fields at positions `p0 < p1`, selectors `selL`
/// at `p0` and `selR` at `p1` — a bare Tree variable `T`, a second Tree variable
/// `Y`, and two Boolean guards `G`, `V18`) are
///
///   assert1: `T = nd(selR(ite G T (nd Y _ T)))  _  (selL(nd Y _ Y))`
///   assert2: `(or (and (not V18) (not G))
///                 (distinct (selR T) (nd (lf …) _ Y) (ite V18 T Y) T))`
///
/// and are jointly unsatisfiable via a NESTED `by_cases`:
///   * `G = false`: assert1's `ite` collapses to `T = nd(T, Y)` — an ACYCLICITY
///     occurs-check (`AySoundness.Datatype.Tree.acyclic_l`);
///   * `G = true`: assert1 forces `T = nd(Y, Y)` (the selector fixpoint
///     `selR T = Y`), so assert2's first disjunct `(… ∧ ¬G)` is FALSE and the
///     `distinct` must hold; an INNER `by_cases` on `V18` makes the 4-element
///     `distinct` list contain a DUPLICATE in each branch (`ite V18 T Y = T = T`
///     when `V18`, or `selR T = Y = ite V18 T Y` when `¬V18`), so it is FALSE by
///     reflexivity (an element `≠` itself). MIXED across the outer split
///     (occurs-check vs distinct-with-duplicate), with an inner split on `V18`.
///
/// The datatype is faithfully abstracted onto the concrete binary `Tree` of
/// `AySoundness.Datatype` (`nd`'s two recursive fields ↦ `Tree.node`, sibling
/// non-recursive fields dropped, `lf` ↦ `Tree.leaf`, the guards to opaque
/// `Bool`s). The selectors `selL`/`selR` are modelled as TOTAL projections whose
/// leaf-case is a DEAD extension: assert1 forces `T` (and the `ite`'s else-branch)
/// to be a `node`, so every selector application in a satisfying assignment lands
/// on a `node` and the leaf-case value is never consulted — hence proving the
/// refutation for the concrete projections establishes it for EVERY selector
/// interpretation. The `distinct`'s falsity comes from GENUINE term duplicates
/// (identical SMT terms), not from the dropped `Rec`/`Enum` fields, so the
/// abstraction cannot conflate distinct SMT terms into a spurious conflict.
/// EMISSION-ONLY, fail-closed; grounded through
/// `AySoundness.firewall_combined_unsat`; axioms ⊆ {propext, Quot.sound}.
pub(crate) fn emit_dt_nested_selector_casesplit_firewall_lean_from_parsed(
    parsed: &[PTerm],
    ctor_rec: &[(String, Vec<bool>)],
    ctor_selectors: &[(String, Vec<String>)],
) -> Option<String> {
    let rec_positions = |ctor: &str| -> Option<Vec<usize>> {
        let mask = &ctor_rec.iter().find(|(c, _)| c == ctor)?.1;
        Some((0..mask.len()).filter(|&i| mask[i]).collect())
    };
    // The selector name projecting field `p` of constructor `ctor`.
    let sel_at = |ctor: &str, p: usize| -> Option<String> {
        ctor_selectors
            .iter()
            .find(|(c, _)| c == ctor)?
            .1
            .get(p)
            .cloned()
    };
    let is_ctor = |name: &str| ctor_rec.iter().any(|(c, _)| c == name);
    let as_sym = |t: &PTerm| -> Option<String> {
        if let PTerm::Symbol(s) = t {
            Some(s.clone())
        } else {
            None
        }
    };

    // Locate the two assertions: an equality (assert1) and an `or` (assert2).
    let mut eq_assert: Option<(&PTerm, &PTerm)> = None;
    let mut or_assert: Option<&Vec<PTerm>> = None;
    for a in parsed {
        if let PTerm::App(op, args) = a {
            if op == "=" && args.len() == 2 && eq_assert.is_none() {
                eq_assert = Some((&args[0], &args[1]));
            } else if op == "or" && args.len() == 2 && or_assert.is_none() {
                or_assert = Some(args);
            }
        }
    }
    let (l, r) = eq_assert?;
    let or_args = or_assert?;

    // ---- assert1: `T = nd(A _ B)` (T a bare Tree variable). Try both sides.
    for (tvar, rhs) in [(l, r), (r, l)] {
        let Some(t_name) = as_sym(tvar) else { continue };
        if is_ctor(&t_name) {
            continue;
        }
        let PTerm::App(nd, rargs) = rhs else { continue };
        if !is_ctor(nd) {
            continue;
        }
        let Some(rp) = rec_positions(nd) else {
            continue;
        };
        if rp.len() != 2 || rargs.len() <= rp[1] {
            continue;
        }
        let (p0, p1) = (rp[0], rp[1]);

        // A := rargs[p0] = `(selR (ite G T (nd Y _ T)))`, selR = nd's p1 selector.
        let PTerm::App(sel_r, aargs) = &rargs[p0] else {
            continue;
        };
        if aargs.len() != 1 || sel_at(nd, p1).as_deref() != Some(sel_r.as_str()) {
            continue;
        }
        let PTerm::App(iop, iargs) = &aargs[0] else {
            continue;
        };
        if iop != "ite" || iargs.len() != 3 {
            continue;
        }
        let Some(g_name) = as_sym(&iargs[0]) else {
            continue;
        };
        if as_sym(&iargs[1]).as_deref() != Some(t_name.as_str()) {
            continue;
        }
        let PTerm::App(indh, inner) = &iargs[2] else {
            continue;
        };
        if indh != nd || inner.len() <= p1 {
            continue;
        }
        let Some(y_name) = as_sym(&inner[p0]) else {
            continue;
        };
        if is_ctor(&y_name) || as_sym(&inner[p1]).as_deref() != Some(t_name.as_str()) {
            continue;
        }

        // B := rargs[p1] = `(selL (nd Y _ Y))`, selL = nd's p0 selector.
        let PTerm::App(sel_l, bargs) = &rargs[p1] else {
            continue;
        };
        if bargs.len() != 1 || sel_at(nd, p0).as_deref() != Some(sel_l.as_str()) {
            continue;
        }
        let PTerm::App(bnh, bnargs) = &bargs[0] else {
            continue;
        };
        if bnh != nd
            || bnargs.len() <= p1
            || as_sym(&bnargs[p0]).as_deref() != Some(y_name.as_str())
            || as_sym(&bnargs[p1]).as_deref() != Some(y_name.as_str())
        {
            continue;
        }

        // ---- assert2: `(or (and (not V18) (not G)) (distinct E1 E2 E3 E4))`.
        for (d1, d2) in [(&or_args[0], &or_args[1]), (&or_args[1], &or_args[0])] {
            let PTerm::App(andop, aa) = d1 else { continue };
            if andop != "and" || aa.len() != 2 {
                continue;
            }
            let not_sym = |t: &PTerm| -> Option<String> {
                let PTerm::App(n, na) = t else { return None };
                if n != "not" || na.len() != 1 {
                    return None;
                }
                as_sym(&na[0])
            };
            let Some(v18_name) = not_sym(&aa[0]) else {
                continue;
            };
            if not_sym(&aa[1]).as_deref() != Some(g_name.as_str()) || is_ctor(&v18_name) {
                continue;
            }

            let PTerm::App(dop, de) = d2 else { continue };
            if dop != "distinct" || de.len() != 4 {
                continue;
            }
            // E1 = (selR T)
            let PTerm::App(e1s, e1a) = &de[0] else {
                continue;
            };
            if e1s != sel_r || e1a.len() != 1 || as_sym(&e1a[0]).as_deref() != Some(t_name.as_str())
            {
                continue;
            }
            // E2 = (nd (lf …) _ Y) after folding a constant-condition `ite`. Its
            // value never affects the `distinct`'s falsity (the duplicates are
            // among E1/E3/E4); pin the shape only to stay fail-closed.
            let PTerm::App(e2h, e2a) = strip_const_ite(&de[1]) else {
                continue;
            };
            if e2h != nd || e2a.len() <= p1 || as_sym(&e2a[p1]).as_deref() != Some(y_name.as_str())
            {
                continue;
            }
            // E3 = (ite V18 T Y)
            let PTerm::App(e3op, e3a) = &de[2] else {
                continue;
            };
            if e3op != "ite"
                || e3a.len() != 3
                || as_sym(&e3a[0]).as_deref() != Some(v18_name.as_str())
                || as_sym(&e3a[1]).as_deref() != Some(t_name.as_str())
                || as_sym(&e3a[2]).as_deref() != Some(y_name.as_str())
            {
                continue;
            }
            // E4 = T
            if as_sym(&de[3]).as_deref() != Some(t_name.as_str()) {
                continue;
            }

            return Some(render_dt_nested_selector_casesplit_lean(fnv_hex(&format!(
                "dtnestedsel:{t_name}:{y_name}:{g_name}:{v18_name}:{nd}"
            ))));
        }
    }
    None
}

/// Render the nested selector-guarded case-split Lean proof (see
/// [`emit_dt_nested_selector_casesplit_firewall_lean_from_parsed`]). The proof is
/// fully generic over the four abstracted variables (`v12`/`v13` : `Tree`,
/// `v17`/`v18` : `Bool`), so only the namespace `hash` varies per instance.
fn render_dt_nested_selector_casesplit_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
import AySoundness.Datatype
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — DATATYPE NESTED SELECTOR-GUARDED
  CASE-SPLIT, grounded in the verified `firewall_combined_unsat`. The two residual
  assertions
    assert1: `v12 = node (right (ite v17 v12 (node v13 v12))) (left (node v13 v13))`
    assert2: `(or (and ¬v18 ¬v17)
                  (distinct (right v12) (node leaf v13) (ite v18 v12 v13) v12))`
  are jointly unsatisfiable via a NESTED `by_cases`:
    * `v17 = false`: assert1 collapses to `v12 = node v12 v13` — an ACYCLICITY
      occurs-check (`AySoundness.Datatype.Tree.acyclic_l`);
    * `v17 = true`: assert1 forces `v12 = node v13 v13` (the selector fixpoint
      `right v12 = v13`), so assert2's first disjunct is FALSE (it needs `¬v17`)
      and the `distinct` must hold; an INNER `by_cases` on `v18` puts a DUPLICATE
      element into the 4-list in either branch (`ite v18 v12 v13 = v12 = v12` when
      `v18`, or `right v12 = v13 = ite v18 v12 v13` when `¬v18`), so `distinct` is
      FALSE by reflexivity.
  Faithful abstraction: the datatype maps homomorphically onto the concrete binary
  `Tree` of `AySoundness.Datatype` (2 recursive fields ↦ `node`, 0 ↦ `leaf`,
  sibling non-recursive fields dropped, guards ↦ opaque `Bool`). The selectors are
  modelled as TOTAL projections whose leaf-case is a DEAD extension — assert1
  forces every selected term to be a `node`, so the leaf value is never consulted
  in any satisfying assignment; and the `distinct`'s falsity rests on GENUINE term
  duplicates, never on the dropped fields — so no abstract model ⟹ no real model.
  Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.DtNestedSelectorCaseSplit_{hash}
open AySoundness
open AySoundness.Datatype (Tree)

/-- Right/left selector projections on the binary `Tree` spine (leaf-case is a
    dead total extension — see the soundness note above). -/
def rightT : Tree → Tree
  | Tree.node _ r => r
  | Tree.leaf => Tree.leaf
def leftT : Tree → Tree
  | Tree.node l _ => l
  | Tree.leaf => Tree.leaf

/-- Theory model: the two opaque Boolean guards and the two datatype variables. -/
structure Val where
  v17 : Bool
  v18 : Bool
  v12 : Tree
  v13 : Tree

/-- `(distinct a b c d)` — pairwise disequality over four `Tree` elements. -/
def distinct4 (a b c d : Tree) : Bool :=
  decide (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)

/-- assert1 (binary-`Tree` image):
    `v12 = node (right (ite v17 v12 (node v13 v12))) (left (node v13 v13))`. -/
abbrev assert1 (m : Val) : Prop :=
  m.v12 = Tree.node
    (rightT (cond m.v17 m.v12 (Tree.node m.v13 m.v12)))
    (leftT (Tree.node m.v13 m.v13))

/-- assert2: `(or (and ¬v18 ¬v17) (distinct (right v12) (node leaf v13)
    (ite v18 v12 v13) v12))`. -/
abbrev assert2 (m : Val) : Prop :=
  (m.v18 = false ∧ m.v17 = false) ∨
    distinct4 (rightT m.v12) (Tree.node Tree.leaf m.v13)
      (cond m.v18 m.v12 m.v13) m.v12 = true

/-- Atom `1 ↦ (assert1 ∧ assert2)` — the full residual conjunction. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (assert1 m ∧ assert2 m)
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

/-- **Case-split lemma validity** — the firewall's premise (b): the residual
    conjunction is false in every model, via the NESTED `by_cases`. -/
theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have h : ¬ (assert1 m ∧ assert2 m) := by
    rintro ⟨h1, h2⟩
    cases hv17 : m.v17
    · -- v17 = false: assert1 collapses to an occurs-check `v12 = node v12 v13`.
      simp only [assert1, hv17, cond_false, rightT, leftT] at h1
      exact absurd h1 (AySoundness.Datatype.Tree.acyclic_l m.v12 m.v13)
    · -- v17 = true: assert1 forces `v12 = node v13 v13`.
      simp only [assert1, hv17, cond_true, leftT] at h1
      have hr : rightT m.v12 = m.v13 := by rw [h1]; rfl
      rw [hr] at h1
      -- disjunct-1 of assert2 needs `¬v17`, so the `distinct` must hold.
      rcases h2 with ⟨_, hv17f⟩ | hd
      · rw [hv17] at hv17f; exact Bool.noConfusion hv17f
      · -- inner case-split on v18: each branch is a distinct-with-duplicate.
        rw [h1] at hd
        cases hv18 : m.v18
        · -- v18 = false: `right v12` and `ite v18 v12 v13` are both `v13`.
          simp [hv18, rightT, distinct4] at hd
        · -- v18 = true: `ite v18 v12 v13` and `v12` are both `node v13 v13`.
          simp [hv18, rightT, distinct4] at hd
  simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil, h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No datatype model satisfies the nested selector-guarded case-split — via the
    verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.DtNestedSelectorCaseSplit_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for an EUF congruence-over-a-transitive-
/// chain refutation found among the PARSED (frontend) assertions: `(= x m)`,
/// `(= m y)`, `(not (= (f x) (f y)))` (a two-link chain `x = m = y` plus the
/// congruence conclusion `f x = f y`).
///
/// ay fuses the transitivity + congruence into one `:rule trust` step, and the
/// executor's split produces `eq_transitive`/`eq_congruent` STEPS (not
/// `TheoryLemma` kinds), so the proof-step-driven firewall dispatch emits no
/// certificate for this shape. The structure survives in the frontend
/// assertions, so reconstruct from there (like the selector / injectivity /
/// string / BV / ROW1 emitters), grounding the single fused lemma
/// `x = m ∧ m = y → f x = f y` through `firewall_combined_unsat`. Runtime
/// counterpart of `AySoundness.CombinedEufCongTrans`; axioms ⊆
/// {propext, Quot.sound} (computable; opaque carrier + arbitrary function).
pub(crate) fn emit_euf_cong_trans_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    for neg_asrt in parsed {
        // (not (= (f x) (f y)))
        let PTerm::App(nop, nargs) = neg_asrt else {
            continue;
        };
        if nop != "not" || nargs.len() != 1 {
            continue;
        }
        let PTerm::App(eqop, eqa) = &nargs[0] else {
            continue;
        };
        if eqop != "=" || eqa.len() != 2 {
            continue;
        }
        let (PTerm::App(f1, fx), PTerm::App(f2, fy)) = (&eqa[0], &eqa[1]) else {
            continue;
        };
        if f1 != f2 || fx.len() != 1 || fy.len() != 1 {
            continue;
        }
        let (x, y) = (&fx[0], &fy[0]);
        if x == y {
            continue;
        }
        // A two-link chain `x = m`, `m = y` for some middle `m`.
        for asrt in parsed {
            let PTerm::App(e, ea) = asrt else { continue };
            if e != "=" || ea.len() != 2 {
                continue;
            }
            let m = if &ea[0] == x {
                &ea[1]
            } else if &ea[1] == x {
                &ea[0]
            } else {
                continue;
            };
            if m == x || m == y {
                continue;
            }
            let has_my = parsed.iter().any(|a| {
                let PTerm::App(e2, ea2) = a else { return false };
                e2 == "="
                    && ea2.len() == 2
                    && ((&ea2[0] == m && &ea2[1] == y) || (&ea2[0] == y && &ea2[1] == m))
            });
            if has_my {
                return Some(render_euf_cong_trans_lean(fnv_hex(&format!(
                    "{neg_asrt:?}"
                ))));
            }
        }
    }
    None
}

/// Render the `AySoundness.CombinedEufCongTrans`-shaped Lean for a two-link
/// congruence-over-transitivity refutation. Atoms fixed (`1 ↦ a = b`,
/// `2 ↦ b = c`, `3 ↦ f a = f c`); constant template up to the namespace hash.
fn render_euf_cong_trans_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — EUF congruence over a transitive chain,
  grounded in the verified `firewall_combined_unsat`. The assertions `a = b`,
  `b = c`, `f a ≠ f c` are unsatisfiable: `a = b ∧ b = c ⟹ a = c` (transitivity),
  then `f a = f c` (congruence). Reconstructed from the frontend assertions (ay
  fuses these into one trust step / split eq_transitive+eq_congruent steps that
  the proof-step dispatch does not emit for). Carrier opaque (`Nat`), function
  arbitrary (`Nat → Int`); computable, axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.EufCongTrans_{hash}
open AySoundness

structure Val where
  a : Nat
  b : Nat
  c : Nat
  f : Nat -> Int

/-- Atoms: `1 ↦ a = b`, `2 ↦ b = c`, `3 ↦ f a = f c`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.a = m.b)
  | 2 => decide (m.b = m.c)
  | 3 => decide (m.f m.a = m.f m.c)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]
def lemmas   : List (Cid × Clause) := [(4, [-1, -2, 3])]
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

theorem cong_trans_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, -2, 3] = true := by
  by_cases h1 : m.a = m.b
  · by_cases h2 : m.b = m.c
    · have hfc : m.f m.a = m.f m.c := by rw [h1.trans h2]
      simp [clauseSat, litSat, atomVal, hfc]
    · simp [clauseSat, litSat, atomVal, h2]
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact cong_trans_lemma_valid m

/-- `a = b ∧ b = c ∧ f a ≠ f c` is unsatisfiable — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.EufCongTrans_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a FLOATING-POINT classification
/// conflict found among the PARSED assertions: a single float `x` asserted to be
/// in two MUTUALLY-EXCLUSIVE IEEE classes (e.g. `(fp.isInfinite x)` and
/// `(fp.isNaN x)`). No bitpattern is in two classes — `AySoundness/FpThy.lean`
/// proves the classifier is a genuine partition — so the conjunction is UNSAT.
///
/// ay reduces FP to bit-vectors (`FpToBv`) and reasons over the classification
/// predicates; its refutation is a bare `(cl) :rule trust`, so the structure is
/// recovered from the frontend AST. Grounds the exclusivity `¬cls₁(x) ∨ ¬cls₂(x)`
/// through `firewall_combined_unsat` over `Val = BitVec FpThy.W`, with lemma
/// validity carried by the verified `FpThy` exclusivity theorem. The emitted file
/// is the runtime counterpart of `AySoundness.CombinedFpClassify`. `None` if no
/// such conflict is present. Top-level `(and …)` assertions are flattened.
pub(crate) fn emit_fp_classification_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    // Collect asserted classification predicates as `(variable, FpThy-predicate)`.
    let mut preds: Vec<(String, &'static str)> = Vec::new();
    let mut stack: Vec<&PTerm> = parsed.iter().collect();
    while let Some(t) = stack.pop() {
        let PTerm::App(op, args) = t else { continue };
        if op == "and" {
            stack.extend(args.iter());
            continue;
        }
        let fpthy = match op.as_str() {
            "fp.isInfinite" => "isInfBits",
            "fp.isNaN" => "isNaNBits",
            "fp.isZero" => "isZeroBits",
            "fp.isSubnormal" => "isSubnormalBits",
            "fp.isNormal" => "isNormalBits",
            _ => continue,
        };
        if let [PTerm::Symbol(v)] = args.as_slice() {
            preds.push((v.clone(), fpthy));
        }
    }
    // Find a mutually-exclusive pair on the SAME variable: ANY two DISTINCT IEEE
    // classes are exclusive (`FpThy` proves the classifier is a partition), so the
    // exclusivity is discharged inline by `decide` over the width-5 carrier.
    for (i, (v1, c1)) in preds.iter().enumerate() {
        for (v2, c2) in preds.iter().skip(i + 1) {
            if v1 == v2 && c1 != c2 {
                // Deterministic orientation (sorted predicate names).
                let (p1, p2) = if c1 <= c2 { (*c1, *c2) } else { (*c2, *c1) };
                return Some(render_fp_classify_lean(p1, p2));
            }
        }
    }
    None
}

/// Render the FP-classification firewall file: a float asserted in two DISTINCT
/// IEEE classes (`p1`, `p2`), refuted because no bitpattern is in two classes —
/// the exclusivity is proved inline by `decide` over the width-5 carrier (32
/// patterns; sound because `FpThy` proves the classifier is a genuine partition).
/// Mirrors `AySoundness/CombinedFpClassify.lean`.
fn render_fp_classify_lean(p1: &str, p2: &str) -> String {
    format!(
        "import AySoundness.Firewall\n\
         import AySoundness.FpThy\n\
         namespace AY.FpClassifyFirewall\n\
         open AySoundness\n\n\
         abbrev Val := BitVec FpThy.W\n\
         def atomVal (x : Val) : Nat → Bool\n  \
           | 1 => @FpThy.{p1} 2 2 x\n  \
           | 2 => @FpThy.{p2} 2 2 x\n  \
           | _ => false\n\n\
         def original : List (Cid × Clause) := [(1, [1]), (2, [2])]\n\
         def lemmas : List (Cid × Clause) := [(3, [-1, -2])]\n\
         def proof : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]\n\n\
         theorem lemma_valid :\n    \
           ∀ c ∈ clauses lemmas, ∀ x : Val, clauseSat (atomVal x) c = true := by\n  \
           intro c hc x\n  \
           simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,\n    \
           List.not_mem_nil, or_false] at hc\n  \
           subst hc\n  \
           simp only [clauseSat, atomVal, AySoundness.litSat, List.any_cons, List.any_nil]\n  \
           have h : ∀ y : Val, ¬ (@FpThy.{p1} 2 2 y = true ∧ @FpThy.{p2} 2 2 y = true) := by decide\n  \
           have hx := h x\n  \
           cases hi : @FpThy.{p1} 2 2 x <;> cases hn : @FpThy.{p2} 2 2 x <;> simp_all\n\n\
         theorem no_model : ∀ x : Val, ¬ Sat (atomVal x) (clauses original) :=\n  \
           firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)\n    \
           atomVal (by decide) (by decide) lemma_valid (by decide)\n\n\
         end AY.FpClassifyFirewall\n"
    )
}

/// Parse a ground SMT-LIB binary bitvector literal (`#b0101…`) into its
/// `(bit_width, value)`. The `#b` prefix is part of the token text. Declines any
/// non-binary constant (a hexadecimal, numeral, symbol, …) — the FP-literal
/// emitters only accept the fully-explicit `(fp #b<sign> #b<exp> #b<mant>)` form.
fn parse_bin_lit(pc: &PConst) -> Option<(usize, u128)> {
    let PConst::Binary(text) = pc else {
        return None;
    };
    let bits = text.strip_prefix("#b")?;
    if bits.is_empty() {
        return None;
    }
    let mut value: u128 = 0;
    for ch in bits.chars() {
        value = value.checked_mul(2)?;
        match ch {
            '0' => {}
            '1' => value += 1,
            _ => return None,
        }
    }
    Some((bits.len(), value))
}

/// Recognize a ground SMT-LIB float literal `(fp #b<sign> #b<exp> #b<mant>)` and
/// return the exact IEEE decode ingredients for `FpUnderflow.decodeFin`:
/// `(src_eb, src_sb, sign, expf, sigf)`. The source format is `eb = |exp|`,
/// `sb = |mant| + 1` (the hidden bit). Declines any non-concrete shape (a symbolic
/// float variable, a non-1-bit sign, a hexadecimal component, …).
fn parse_ground_fp_literal(t: &PTerm) -> Option<(usize, usize, bool, u128, u128)> {
    let PTerm::App(op, args) = t else {
        return None;
    };
    if op != "fp" || args.len() != 3 {
        return None;
    }
    let bit = |x: &PTerm| match x {
        PTerm::Const(pc) => parse_bin_lit(pc),
        _ => None,
    };
    let (sign_w, sign_v) = bit(&args[0])?;
    let (exp_w, exp_v) = bit(&args[1])?;
    let (mant_w, mant_v) = bit(&args[2])?;
    // Sign is exactly one bit; exponent and stored significand must be non-empty.
    if sign_w != 1 || exp_w == 0 || mant_w == 0 {
        return None;
    }
    let sign = sign_v == 1;
    Some((exp_w, mant_w + 1, sign, exp_v, mant_v))
}

/// Emit a verified-firewall Lean proof for a FLOATING-POINT `to_fp` NARROWING
/// UNDERFLOW / OVERFLOW-asymmetry classification conflict found among the PARSED
/// assertions: a single positive class assertion over a CONCRETE, ground
/// conversion —
///
///   `(fp.isInfinite ((_ to_fp EB SB) RTN (fp #b<s> #b<e> #b<m>)))`   or
///   `(fp.isNormal   ((_ to_fp EB SB) RTN (fp #b<s> #b<e> #b<m>)))`
///
/// — whose RTN-narrowed result the faithful, reference-battery-VALIDATED
/// `AySoundness.FpUnderflow` model classifies otherwise (e.g. a tiny source
/// underflows to a subnormal/zero, so it is NOT infinite / NOT normal). ay
/// reduces `to_fp` to bit-vectors and refutes eagerly (bare-trust), so the
/// structure is recovered from the frontend AST and the single-atom claim is
/// grounded through `firewall_combined_unsat`: the source magnitude is decoded
/// exactly by `FpUnderflow.decodeFin`, the RTN class by `FpUnderflow.classifyRTN`,
/// and the atom's closed `Bool` (`isInf` / `isNorm`) is refuted by `decide`
/// (Int-cross-multiplied dyadics — no rounding-fragile arithmetic).
///
/// FAIL-CLOSED / emission-only: recognizes ONLY the concrete ground shape under
/// the `RTN` rounding mode the model covers; returns `None` for any symbolic
/// float, non-`RTN` mode, non-`to_fp` argument, or non-`fp.isInfinite`/`isNormal`
/// predicate. Top-level `(and …)` assertions are flattened. If the model were to
/// disagree with ay's refutation (a modelling bug), the emitted `decide` fails and
/// the file does not build — it never certifies a false verdict.
pub(crate) fn emit_fp_tofp_underflow_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    let mut stack: Vec<&PTerm> = parsed.iter().collect();
    while let Some(t) = stack.pop() {
        let PTerm::App(op, args) = t else { continue };
        if op == "and" {
            stack.extend(args.iter());
            continue;
        }
        // `(fp.isInfinite X)` → `isInf`; `(fp.isNormal X)` → `isNorm`.
        let pred_fn = match op.as_str() {
            "fp.isInfinite" => "isInf",
            "fp.isNormal" => "isNorm",
            _ => continue,
        };
        let [inner] = args.as_slice() else { continue };
        // Inner must be `((_ to_fp EB SB) RM FP-LITERAL)`.
        let PTerm::IndexedApp(name, indices, conv_args) = inner else {
            continue;
        };
        if name != "to_fp" || indices.len() != 2 || conv_args.len() != 2 {
            continue;
        }
        let tgt_eb: usize = indices[0].as_numeral()?.parse().ok()?;
        let tgt_sb: usize = indices[1].as_numeral()?.parse().ok()?;
        // Only the RTN rounding mode is covered by the model (round toward −∞).
        let rm_ok = match &conv_args[0] {
            PTerm::Symbol(rm) => rm == "RTN" || rm == "roundTowardNegative",
            _ => false,
        };
        if !rm_ok {
            continue;
        }
        let Some((src_eb, src_sb, sign, expf, sigf)) = parse_ground_fp_literal(&conv_args[1])
        else {
            continue;
        };
        return Some(render_fp_tofp_underflow_lean(
            pred_fn, src_eb, src_sb, sign, expf, sigf, tgt_eb, tgt_sb,
        ));
    }
    None
}

/// Render the `to_fp` narrowing-classification firewall file: the ground source
/// float is decoded by `FpUnderflow.decodeFin` and its RTN class by
/// `FpUnderflow.classifyRTN`; the single asserted atom (`isInf`/`isNorm` of that
/// class) is a closed `false`, so the assertion has no model — via the verified
/// `firewall_combined_unsat`. `#print axioms no_model` documents the ⊆ {propext,
/// Quot.sound} closure at `lake build`.
#[allow(clippy::too_many_arguments)]
fn render_fp_tofp_underflow_lean(
    pred_fn: &str,
    src_eb: usize,
    src_sb: usize,
    sign: bool,
    expf: u128,
    sigf: u128,
    tgt_eb: usize,
    tgt_sb: usize,
) -> String {
    let sign_lean = if sign { "true" } else { "false" };
    let hash = fnv_hex(&format!(
        "{pred_fn}\u{1}{src_eb}\u{1}{src_sb}\u{1}{sign_lean}\u{1}{expf}\u{1}{sigf}\u{1}{tgt_eb}\u{1}{tgt_sb}"
    ));
    format!(
        r#"import AySoundness.Firewall
import AySoundness.FpUnderflow
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — floating-point `to_fp` NARROWING
  classification conflict (underflow / RTN overflow-asymmetry), grounded in the
  verified, reference-battery-VALIDATED `AySoundness.FpUnderflow` model. The
  assertion `(fp.<pred> ((_ to_fp {tgt_eb} {tgt_sb}) RTN (fp #b<s> #b<e> #b<m>)))`
  claims the RTN-narrowed conversion of a GROUND source bitpattern is
  infinite/normal; the faithful exact-dyadic RTN classifier proves otherwise, so
  the single-atom assertion is refuted through `firewall_combined_unsat`. The
  source magnitude is the EXACT IEEE decode `FpUnderflow.decodeFin` and the class
  is `FpUnderflow.classifyRTN`; both `decide`-reduce (dyadics cross-multiplied in
  `Int`, no rounding-fragile arithmetic). Pure Lean 4 core; axioms ⊆ {{propext,
  Quot.sound}}.
-/
namespace AySoundness.Emitted.FpTofpUnderflow_{hash}
open AySoundness
open AySoundness.FpUnderflow

/-- Exact dyadic value of the ground source float `(fp #b<s> #b<e> #b<m>)` in
    source format `(eb={src_eb}, sb={src_sb})`, via the model's exact IEEE decode. -/
def src : Dy := decodeFin {src_eb} {src_sb} {sign_lean} {expf} {sigf}

/-- The single asserted atom: whether the RTN narrowing of `src` into target
    format `({tgt_eb}, {tgt_sb})` is `{pred_fn}`. The model computes this closed
    `Bool` — and it is `false`. -/
def atomVal (_ : Unit) (n : Nat) : Bool :=
  match n with
  | 1 => {pred_fn} (classifyRTN {tgt_eb} {tgt_sb} src)
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (u : Unit) : clauseSat (atomVal u) [-1] = true := by
  cases u
  decide

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ u : Unit, clauseSat (atomVal u) cl = true := by
  intro cl hcl u
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid u

/-- The concrete `to_fp` classification claim has no model — via the firewall. -/
theorem no_model : ∀ u : Unit, ¬ Sat (atomVal u) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

#print axioms no_model

end AySoundness.Emitted.FpTofpUnderflow_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a FLOATING-POINT `fp.rem`
/// SIGN classification conflict found among the PARSED assertions: a single
/// positive assertion
///
///   `(fp.isNegative (fp.rem (fp #b<s> #b<e> #b<m>) (fp #b<s> #b<e> #b<m>)))`
///
/// over TWO CONCRETE, ground same-format float literals, whose exact IEEE-754
/// remainder the faithful, reference-battery-VALIDATED `AySoundness.FpUnderflow`
/// `fp.rem` model classifies as NOT negative (the exact `remDy` value is
/// non-negative). ay reduces `fp.rem` to bit-vectors and refutes eagerly
/// (bare-trust), so the structure is recovered from the frontend AST and the
/// single-atom claim is grounded through `firewall_combined_unsat`: both operands
/// are decoded exactly by `FpUnderflow.decodeFin`, the round-to-nearest-even
/// remainder by `FpUnderflow.remDy`, and the atom's closed `Bool`
/// (`remIsNegative`) is refuted by `decide` (Int-exact — no rounding-fragile
/// arithmetic on the remainder).
///
/// FAIL-CLOSED / emission-only: recognizes ONLY the concrete ground shape — TWO
/// `(fp #b… #b… #b…)` literals of the SAME `(eb, sb)` format under
/// `fp.isNegative (fp.rem …)`; returns `None` for any symbolic float, mismatched
/// formats, non-`fp.rem` argument, or non-`fp.isNegative` predicate. Top-level
/// `(and …)` assertions are flattened. If the model were to disagree with ay's
/// refutation (a modelling bug), the emitted `decide` fails and the file does not
/// build — it never certifies a false verdict.
pub(crate) fn emit_fp_rem_not_negative_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    let mut stack: Vec<&PTerm> = parsed.iter().collect();
    while let Some(t) = stack.pop() {
        let PTerm::App(op, args) = t else { continue };
        if op == "and" {
            stack.extend(args.iter());
            continue;
        }
        if op != "fp.isNegative" {
            continue;
        }
        let [inner] = args.as_slice() else { continue };
        // Inner must be `(fp.rem FP-LITERAL FP-LITERAL)`.
        let PTerm::App(rem_op, rem_args) = inner else {
            continue;
        };
        if rem_op != "fp.rem" || rem_args.len() != 2 {
            continue;
        }
        let (a_eb, a_sb, a_sign, a_expf, a_sigf) = parse_ground_fp_literal(&rem_args[0])?;
        let (b_eb, b_sb, b_sign, b_expf, b_sigf) = parse_ground_fp_literal(&rem_args[1])?;
        // `fp.rem` is a same-format operation — decline any mismatched pair.
        if a_eb != b_eb || a_sb != b_sb {
            continue;
        }
        return Some(render_fp_rem_not_negative_lean(
            a_eb, a_sb, a_sign, a_expf, a_sigf, b_sign, b_expf, b_sigf,
        ));
    }
    None
}

/// Render the `fp.rem` sign-classification firewall file: both ground operands
/// are decoded by `FpUnderflow.decodeFin`, their round-to-nearest-even remainder
/// by `FpUnderflow.remDy`, and the single asserted atom
/// (`remIsNegative sign_a a b`) is a closed `false`, so the assertion has no model
/// — via the verified `firewall_combined_unsat`. The dividend's sign bit `sign_a`
/// is threaded to resolve the `±0` boundary (`fp.isNegative(−0)=true`).
/// `#print axioms no_model` documents the ⊆ {propext, Quot.sound} closure at
/// `lake build`.
#[allow(clippy::too_many_arguments)]
fn render_fp_rem_not_negative_lean(
    eb: usize,
    sb: usize,
    a_sign: bool,
    a_expf: u128,
    a_sigf: u128,
    b_sign: bool,
    b_expf: u128,
    b_sigf: u128,
) -> String {
    let a_sign_lean = if a_sign { "true" } else { "false" };
    let b_sign_lean = if b_sign { "true" } else { "false" };
    let hash = fnv_hex(&format!(
        "{eb}\u{1}{sb}\u{1}{a_sign_lean}\u{1}{a_expf}\u{1}{a_sigf}\u{1}{b_sign_lean}\u{1}{b_expf}\u{1}{b_sigf}"
    ));
    format!(
        r#"import AySoundness.Firewall
import AySoundness.FpUnderflow
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — floating-point `fp.rem` SIGN conflict,
  grounded in the verified, reference-battery-VALIDATED `AySoundness.FpUnderflow`
  `fp.rem` model. The assertion `(fp.isNegative (fp.rem (fp #b<s> #b<e> #b<m>)
  (fp #b<s> #b<e> #b<m>)))` claims the exact remainder of two GROUND same-format
  bitpatterns is negative; the faithful exact round-to-nearest-even remainder
  proves otherwise (its value is non-negative), so the single-atom assertion is
  refuted through `firewall_combined_unsat`. Both operands are the EXACT IEEE
  decode `FpUnderflow.decodeFin`, the remainder is `FpUnderflow.remDy`, and the
  sign is `FpUnderflow.remIsNegative`; all `decide`-reduce (Int-exact, no
  rounding-fragile arithmetic on the remainder). Pure Lean 4 core; axioms ⊆
  {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.FpRemNotNegative_{hash}
open AySoundness
open AySoundness.FpUnderflow

/-- Exact dyadic value of the dividend `a = (fp #b<s> #b<e> #b<m>)` in format
    `(eb={eb}, sb={sb})`, via the model's exact IEEE decode. -/
def a : Dy := decodeFin {eb} {sb} {a_sign_lean} {a_expf} {a_sigf}

/-- Exact dyadic value of the divisor `b = (fp #b<s> #b<e> #b<m>)` in the same
    format `(eb={eb}, sb={sb})`, via the model's exact IEEE decode. -/
def b : Dy := decodeFin {eb} {sb} {b_sign_lean} {b_expf} {b_sigf}

/-- The single asserted atom: whether the round-to-nearest-even remainder
    `fp.rem a b` is negative. The dividend's sign bit ({a_sign_lean}) resolves the
    `±0` boundary. The model computes this closed `Bool` — and it is `false`. -/
def atomVal (_ : Unit) (n : Nat) : Bool :=
  match n with
  | 1 => remIsNegative {a_sign_lean} a b
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (u : Unit) : clauseSat (atomVal u) [-1] = true := by
  cases u
  decide

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ u : Unit, clauseSat (atomVal u) cl = true := by
  intro cl hcl u
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid u

/-- The concrete `fp.rem` sign claim has no model — via the firewall. -/
theorem no_model : ∀ u : Unit, ¬ Sat (atomVal u) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

#print axioms no_model

end AySoundness.Emitted.FpRemNotNegative_{hash}
"#,
    )
}

// ---------------------------------------------------------------------------
// Floating-point RNE dot-product forward-error firewall authority gate.
// ---------------------------------------------------------------------------

/// The IEEE-754 `binary64` format as `(eb, sb)`: 11 exponent bits, 53
/// significand bits INCLUDING the hidden bit. This is the SMT-LIB `Float64` /
/// `(_ FloatingPoint 11 53)` sort, and the only format the `FpBridge`
/// forward-error theorems are proved for.
const BINARY64_FORMAT: (u32, u32) = (11, 53);

/// The SMT-LIB `RoundingMode` constants, spelled out EXACTLY.
///
/// A rounding mode occupies the first argument slot of the arithmetic
/// `fp.*` operators, where every OTHER argument is floating-point sorted. This
/// table exists so that slot can be skipped by exact name and never by a
/// prefix or shape guess: `RNEx`, `RN`, `rne` and `roundy` are all legal
/// user-declarable symbols, and any of them mistaken for a rounding mode would
/// silently drop a real floating-point operand out of the format check.
const SMTLIB_ROUNDING_MODES: [&str; 10] = [
    "RNE",
    "RNA",
    "RTP",
    "RTN",
    "RTZ",
    "roundNearestTiesToEven",
    "roundNearestTiesToAway",
    "roundTowardPositive",
    "roundTowardNegative",
    "roundTowardZero",
];

/// The SMT-LIB `FloatingPoint` operators whose non-`RoundingMode` arguments are
/// all floating-point sorted, spelled out EXACTLY.
///
/// Deliberately a closed table and not a `starts_with("fp.")` test: `fp.to_ubv`
/// / `fp.to_sbv` are indexed (`(_ fp.to_ubv m)`) and `to_fp` mixes source
/// sorts, so a prefix rule would both over- and under-approximate. An operator
/// missing from this table simply contributes no operands — which can only make
/// the format check MORE conservative if the caller also requires that at least
/// one operand was found.
const FP_SAME_SORT_OPERATORS: [&str; 25] = [
    "fp.abs",
    "fp.neg",
    "fp.add",
    "fp.sub",
    "fp.mul",
    "fp.div",
    "fp.fma",
    "fp.sqrt",
    "fp.rem",
    "fp.roundToIntegral",
    "fp.min",
    "fp.max",
    "fp.leq",
    "fp.lt",
    "fp.geq",
    "fp.gt",
    "fp.eq",
    "fp.isNormal",
    "fp.isSubnormal",
    "fp.isZero",
    "fp.isInfinite",
    "fp.isNaN",
    "fp.isNegative",
    "fp.isPositive",
    "fp.to_real",
];

/// Collect every SYMBOL occurring anywhere in `t`, and reject outright any
/// construct that could introduce a floating-point format this walk cannot
/// account for.
///
/// Returns `false` when the term cannot be analysed, in which case the
/// collected list is meaningless and the caller must decline. That happens for
/// every BINDING form — `let`, `forall`, `exists`, `lambda`, `match` — because
/// a bound occurrence of a name is NOT the declared symbol of that name, so
/// looking the name up in the declaration table would read the wrong sort. It
/// also happens past a depth cap, so a pathological term cannot overflow the
/// stack inside a soundness gate.
///
/// COLLECTION IS UNRESTRICTED BY POSITION. An earlier version pushed a symbol
/// only when it stood in DIRECT operand position of a recognized same-sort
/// `fp.*` application, which let non-`binary64` values reach the formula
/// uncollected and made the caller's `all(...)` pass VACUOUSLY. Four shapes
/// were demonstrated to slip through: a `Float32` symbol reachable only under
/// `=`; `binary32` arithmetic behind `(_ to_fp 8 24)`; `Float32` operands under
/// `ite`; and a `binary32` `(fp #b0 #b00000001 …)` literal operand. A gate that
/// answers "the vocabulary is binary64" must range over the WHOLE term, so
/// every symbol is collected here and the format decision is left to the
/// caller, which checks the entire declared vocabulary rather than a subset.
fn collect_fp_operand_symbols(
    t: &PTerm,
    depth: u32,
    all: &mut Vec<String>,
    operands: &mut Vec<String>,
) -> bool {
    /// Deep enough for any realistic assertion; a term nested deeper than this
    /// is refused rather than recursed into.
    const MAX_DEPTH: u32 = 512;
    if depth >= MAX_DEPTH {
        return false;
    }
    match t {
        PTerm::Const(_) => true,
        PTerm::Symbol(s) => {
            if !SMTLIB_ROUNDING_MODES.contains(&s.as_str()) {
                all.push(s.clone());
            }
            true
        }
        PTerm::App(op, args) => {
            // `(fp <sign> <exp> <sig>)` builds a literal of whatever format its
            // bit-vector widths imply. The surface syntax does not carry the
            // sort, and a `binary32` literal is indistinguishable here from a
            // `binary64` one without re-deriving both widths, so decline.
            if op == "fp" {
                return false;
            }
            if FP_SAME_SORT_OPERATORS.contains(&op.as_str()) {
                for arg in args {
                    if let PTerm::Symbol(s) = arg {
                        if !SMTLIB_ROUNDING_MODES.contains(&s.as_str()) {
                            operands.push(s.clone());
                        }
                    }
                }
            }
            args.iter()
                .all(|arg| collect_fp_operand_symbols(arg, depth + 1, all, operands))
        }
        PTerm::IndexedApp(op, indices, args) => {
            // `((_ to_fp eb sb) …)` and friends NAME their result format in the
            // indices. Any format other than binary64 introduces a value this
            // gate must not vouch for.
            if op.starts_with("to_fp") {
                let names_binary64 = indices.len() == 2
                    && matches!(&indices[0], PIndex::Numeral(n) if n.parse::<u32>() == Ok(BINARY64_FORMAT.0))
                    && matches!(&indices[1], PIndex::Numeral(n) if n.parse::<u32>() == Ok(BINARY64_FORMAT.1));
                if !names_binary64 {
                    return false;
                }
            }
            args.iter()
                .all(|arg| collect_fp_operand_symbols(arg, depth + 1, all, operands))
        }
        PTerm::QualifiedApp(_, _, args) => args
            .iter()
            .all(|arg| collect_fp_operand_symbols(arg, depth + 1, all, operands)),
        PTerm::Annotated(inner, _) => collect_fp_operand_symbols(inner, depth + 1, all, operands),
        // Binding forms: a bound name shadows the declaration table.
        PTerm::Let(..)
        | PTerm::Forall(..)
        | PTerm::Exists(..)
        | PTerm::Lambda(..)
        | PTerm::Match(..) => false,
        // `Term` is `#[non_exhaustive]`: an unrecognized future variant is
        // unanalysable by construction, so decline rather than ignore it.
        _ => false,
    }
}

/// Whether the floating-point vocabulary of this parsed formula is EXACTLY
/// IEEE-754 `binary64`.
///
/// WHY THIS GATE EXISTS. [`Context::assertions_parsed`] hands emitters the
/// original surface syntax, in which `Term::Symbol` carries NO sort. The
/// `guard_claim_guard2.smt2` benchmark and its `Float32` clone
/// (`guard_claim_guard2_float32.smt2`) have BYTE-IDENTICAL parsed assertion
/// terms — yet the `Float64` original is `unsat` (binary64 half-ULP forward
/// error `<= 17/64 < 2`) and the `Float32` clone is SATISFIABLE
/// (`guard_claim_guard2_float32_witness.smt2` pins a model with error
/// `16777214 >= 2`). An error-bound emitter that classifies by term shape alone
/// would emit a `no_model` certificate for a satisfiable formula. Reading the
/// format is therefore a SOUNDNESS prerequisite, not a refinement.
///
/// `fp_formats` is [`Context::nullary_fp_formats`], which lists EVERY nullary
/// symbol with its floating-point format, or `None` when the symbol is not
/// floating-point. The gate is fail-closed in every direction:
///
/// - the term walk refuses binding forms, `fp` bit-pattern literals, a
///   `to_fp` family index pair other than `(11, 53)`, excessive depth, and any
///   unrecognized `Term` variant;
/// - a symbol occurring in the formula but ABSENT from the table (unknown or
///   ambiguous sort) declines;
/// - ANY declared floating-point symbol of a format other than `(11, 53)`
///   declines, whether or not it occurs in this formula;
/// - a formula containing no `binary64` symbol at all declines — there is
///   nothing to certify.
///
/// THE THIRD RULE IS DELIBERATELY WHOLE-VOCABULARY, NOT PER-OCCURRENCE. An
/// earlier version asked only whether the symbols it had collected were
/// binary64, and collected only those in direct operand position of a
/// recognized same-sort `fp.*` application. Non-binary64 values reachable any
/// other way — under `=`, under `ite`, as an `(_ to_fp 8 24)` argument, or as
/// an `(fp …)` literal — were never collected, so the check passed VACUOUSLY on
/// formulas whose vocabulary was NOT binary64. Since the whole point of this
/// gate is that `Term::Symbol` carries no sort and a `Float32` clone of the
/// target benchmark parses IDENTICALLY while being satisfiable, a subset check
/// is worth nothing. Refusing a formula merely because some unrelated
/// non-binary64 symbol is declared elsewhere in the session is the conservative
/// direction, and conservative is the only acceptable direction here.
pub(crate) fn parsed_fp_vocabulary_is_binary64(
    parsed: &[PTerm],
    defined: &[(String, PTerm)],
    fp_formats: &[(String, Option<(u32, u32)>)],
) -> bool {
    // No floating-point symbol of any other format may exist anywhere.
    if fp_formats
        .iter()
        .any(|(_, fmt)| fmt.is_some_and(|f| f != BINARY64_FORMAT))
    {
        return false;
    }

    let mut symbols: Vec<String> = Vec::new();
    let mut operands: Vec<String> = Vec::new();
    for t in parsed {
        if !collect_fp_operand_symbols(t, 0, &mut symbols, &mut operands) {
            return false;
        }
    }
    for (_, body) in defined {
        if !collect_fp_operand_symbols(body, 0, &mut symbols, &mut operands) {
            return false;
        }
    }
    symbols.sort();
    symbols.dedup();
    operands.sort();
    operands.dedup();

    let format_of = |name: &String| fp_formats.iter().find(|(n, _)| n == name).map(|(_, f)| *f);

    // Every symbol the formula mentions must be one this table knows about, or
    // its sort — and hence its format — is simply unknown to us. Non-floating
    // -point symbols are fine here: a `guard_claim` formula legitimately names
    // Bool and Real constants alongside its binary64 values.
    if !symbols.iter().all(|name| format_of(name).is_some()) {
        return false;
    }

    // Anything standing in floating-point OPERAND position must be a declared
    // binary64 value. A symbol used as an `fp.*` operand but declared with a
    // non-floating-point sort is an inconsistency the gate must not paper over.
    if !operands
        .iter()
        .all(|name| format_of(name) == Some(Some(BINARY64_FORMAT)))
    {
        return false;
    }

    // And at least one binary64 value must actually occur.
    operands
        .iter()
        .any(|name| format_of(name) == Some(Some(BINARY64_FORMAT)))
}

/// The two SMT-LIB spellings of round-to-nearest-ties-to-even.
///
/// `FpBridge.NearestF64` is deliberately tie-rule agnostic, so `RNA` would in
/// fact also be sound under it. It is NOT accepted here: the emitter's job is
/// to recognize one certified shape, and every extra accepted spelling is
/// another line a reviewer has to check against the standard for no gain.
const FPDOT_RNE_SPELLINGS: [&str; 2] = ["RNE", "roundNearestTiesToEven"];

/// The asserted position/offset magnitude bound the bridge is proved for:
/// `2^48` (`FpBridge.B48`).
const FPDOT_B48: i128 = 281_474_976_710_656;

/// Largest numerator/denominator the emitter will put into the emitted Lean:
/// `10^30`. Keeps the rendered `Int` literals small enough that the `omega`
/// side conditions stay trivial, and makes every `i128` product below
/// overflow-free by construction (`64 * 10^30` is ~7 orders under `i128::MAX`).
const FPDOT_MAX_RATIONAL: i128 = 1_000_000_000_000_000_000_000_000_000_000;

/// Decimal digits in [`FPDOT_MAX_RATIONAL`] minus one: a longer integer or
/// fractional part cannot survive the range check, so it is refused before a
/// long digit string is built.
const FPDOT_MAX_RATIONAL_DIGITS: usize = 30;

/// Follow nullary `define-fun` macro links to the first non-macro term.
///
/// Returns `None` on a cycle or an over-long chain rather than looping.
fn fpdot_deref<'a>(t: &'a PTerm, defined: &'a [(String, PTerm)]) -> Option<&'a PTerm> {
    let mut cur = t;
    for _ in 0..32 {
        let PTerm::Symbol(s) = cur else {
            return Some(cur);
        };
        match defined.iter().find(|(n, _)| n == s) {
            Some((_, body)) => cur = body,
            None => return Some(cur),
        }
    }
    None
}

/// A LEAF: a bare symbol that is neither a macro nor a rounding mode.
fn fpdot_leaf(t: &PTerm, defined: &[(String, PTerm)]) -> Option<String> {
    match fpdot_deref(t, defined)? {
        PTerm::Symbol(s) if !SMTLIB_ROUNDING_MODES.contains(&s.as_str()) => Some(s.clone()),
        _ => None,
    }
}

/// `(<op> RNE a b)` → `(a, b)`. Any other rounding mode, arity or head declines.
fn fpdot_rne_binop<'a>(
    t: &'a PTerm,
    op: &str,
    defined: &'a [(String, PTerm)],
) -> Option<(&'a PTerm, &'a PTerm)> {
    let PTerm::App(head, args) = fpdot_deref(t, defined)? else {
        return None;
    };
    if head != op || args.len() != 3 {
        return None;
    }
    let PTerm::Symbol(mode) = &args[0] else {
        return None;
    };
    if !FPDOT_RNE_SPELLINGS.contains(&mode.as_str()) {
        return None;
    }
    Some((&args[1], &args[2]))
}

/// `(fp.to_real x)` → `x`.
fn fpdot_to_real<'a>(t: &'a PTerm, defined: &'a [(String, PTerm)]) -> Option<&'a PTerm> {
    let PTerm::App(head, args) = fpdot_deref(t, defined)? else {
        return None;
    };
    if head != "fp.to_real" || args.len() != 1 {
        return None;
    }
    Some(&args[0])
}

/// `(fp.to_real l)` where `l` is a leaf → the leaf name.
fn fpdot_to_real_leaf(t: &PTerm, defined: &[(String, PTerm)]) -> Option<String> {
    fpdot_leaf(fpdot_to_real(t, defined)?, defined)
}

fn fpdot_gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

/// An SMT-LIB numeral or decimal literal → the EXACT rational `(num, den)` in
/// lowest terms with `den > 0`. Declines (never wraps, never rounds) on
/// anything whose numerator or denominator would exceed [`FPDOT_MAX_RATIONAL`].
fn fpdot_parse_decimal(text: &str) -> Option<(i128, i128)> {
    let (negative, body) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let (int_part, frac_part) = body.split_once('.').unwrap_or((body, ""));
    if int_part.is_empty() && frac_part.is_empty() {
        return None;
    }
    if !int_part.bytes().all(|b| b.is_ascii_digit())
        || !frac_part.bytes().all(|b| b.is_ascii_digit())
    {
        return None;
    }
    if frac_part.len() > FPDOT_MAX_RATIONAL_DIGITS || int_part.len() > FPDOT_MAX_RATIONAL_DIGITS {
        return None;
    }
    let mut num: i128 = format!("{int_part}{frac_part}").parse().ok()?;
    let mut den: i128 = 1;
    for _ in 0..frac_part.len() {
        den = den.checked_mul(10)?;
    }
    if negative {
        num = num.checked_neg()?;
    }
    let divisor = i128::try_from(fpdot_gcd(num.unsigned_abs(), den.unsigned_abs())).ok()?;
    if divisor > 0 {
        num /= divisor;
        den /= divisor;
    }
    if num.abs() > FPDOT_MAX_RATIONAL || den > FPDOT_MAX_RATIONAL || den <= 0 {
        return None;
    }
    Some((num, den))
}

/// A numeral/decimal literal, possibly behind nullary `define-fun` macros
/// (`(define-fun B () Real 281474976710656.0)`), as an exact rational.
fn fpdot_rational(t: &PTerm, defined: &[(String, PTerm)]) -> Option<(i128, i128)> {
    let PTerm::Const(c) = fpdot_deref(t, defined)? else {
        return None;
    };
    match c {
        PConst::Numeral(n) => fpdot_parse_decimal(n),
        PConst::Decimal(d) => fpdot_parse_decimal(d),
        _ => None,
    }
}

/// Flatten a (binary or n-ary) `+` tree into its summands.
fn fpdot_flatten_add<'a>(
    t: &'a PTerm,
    defined: &'a [(String, PTerm)],
    depth: u32,
    out: &mut Vec<&'a PTerm>,
) -> bool {
    if depth > 8 || out.len() > 8 {
        return false;
    }
    let Some(term) = fpdot_deref(t, defined) else {
        return false;
    };
    if let PTerm::App(head, args) = term {
        if head == "+" {
            return args
                .iter()
                .all(|a| fpdot_flatten_add(a, defined, depth + 1, out));
        }
    }
    out.push(term);
    true
}

/// `(* (fp.to_real a) (fp.to_real b))` → `(a, b)`.
fn fpdot_real_product(t: &PTerm, defined: &[(String, PTerm)]) -> Option<(String, String)> {
    let PTerm::App(head, args) = fpdot_deref(t, defined)? else {
        return None;
    };
    if head != "*" || args.len() != 2 {
        return None;
    }
    Some((
        fpdot_to_real_leaf(&args[0], defined)?,
        fpdot_to_real_leaf(&args[1], defined)?,
    ))
}

/// `(and (fp.isNormal L) (<= (fp.to_real (fp.abs L)) BOUND))` → `(L, BOUND)`.
///
/// Both conjuncts must name the SAME leaf; the `fp.isNormal` conjunct is what
/// makes `fp.to_real L` a rational at all (SMT-LIB leaves `fp.to_real`
/// unspecified on NaN/±∞), so an assertion missing it is refused even though
/// the Lean atom set drops it.
fn fpdot_magnitude_assertion(
    t: &PTerm,
    defined: &[(String, PTerm)],
) -> Option<(String, (i128, i128))> {
    let PTerm::App(head, args) = fpdot_deref(t, defined)? else {
        return None;
    };
    if head != "and" || args.len() != 2 {
        return None;
    }
    let PTerm::App(normal, normal_args) = fpdot_deref(&args[0], defined)? else {
        return None;
    };
    if normal != "fp.isNormal" || normal_args.len() != 1 {
        return None;
    }
    let leaf = fpdot_leaf(&normal_args[0], defined)?;

    let PTerm::App(le, le_args) = fpdot_deref(&args[1], defined)? else {
        return None;
    };
    if le != "<=" || le_args.len() != 2 {
        return None;
    }
    let PTerm::App(abs, abs_args) = fpdot_deref(fpdot_to_real(&le_args[0], defined)?, defined)?
    else {
        return None;
    };
    if abs != "fp.abs" || abs_args.len() != 1 || fpdot_leaf(&abs_args[0], defined)? != leaf {
        return None;
    }
    Some((leaf, fpdot_rational(&le_args[1], defined)?))
}

/// The recognized `guard_claim` shape: the seven leaves in the order
/// `nx ny nz px py pz d` and the refuted threshold as an exact rational.
struct FpDotShape {
    leaves: [String; 7],
    tnum: i128,
    tden: i128,
}

/// `(>= (- (fp.to_real RF) RREAL) THRESHOLD)`, with `RF` the six-operation RNE
/// evaluation and `RREAL` the exact real dot product over the SAME leaves in
/// the SAME order.
fn fpdot_claim_assertion(t: &PTerm, defined: &[(String, PTerm)]) -> Option<FpDotShape> {
    let PTerm::App(ge, ge_args) = fpdot_deref(t, defined)? else {
        return None;
    };
    if ge != ">=" || ge_args.len() != 2 {
        return None;
    }
    let PTerm::App(minus, minus_args) = fpdot_deref(&ge_args[0], defined)? else {
        return None;
    };
    if minus != "-" || minus_args.len() != 2 {
        return None;
    }

    // The rounded side: rf = fp.add(fp.add(fp.add(n*p, n*p), n*p), d), exactly
    // this association — `close_add`/`close_trans_add` accumulate the certified
    // 17/32 spacing for THIS tree and no other.
    let rounded = fpdot_to_real(&minus_args[0], defined)?;
    let (s2, d_term) = fpdot_rne_binop(rounded, "fp.add", defined)?;
    let (s1, t3) = fpdot_rne_binop(s2, "fp.add", defined)?;
    let (t1, t2) = fpdot_rne_binop(s1, "fp.add", defined)?;
    let (nx, px) = fpdot_rne_binop(t1, "fp.mul", defined)?;
    let (ny, py) = fpdot_rne_binop(t2, "fp.mul", defined)?;
    let (nz, pz) = fpdot_rne_binop(t3, "fp.mul", defined)?;
    let leaves = [
        fpdot_leaf(nx, defined)?,
        fpdot_leaf(ny, defined)?,
        fpdot_leaf(nz, defined)?,
        fpdot_leaf(px, defined)?,
        fpdot_leaf(py, defined)?,
        fpdot_leaf(pz, defined)?,
        fpdot_leaf(d_term, defined)?,
    ];
    // Seven DISTINCT values: the Lean model has thirteen independent `Rat`
    // fields, so an aliased leaf would be modeled as two unrelated values.
    let mut distinct: Vec<&String> = leaves.iter().collect();
    distinct.sort();
    distinct.dedup();
    if distinct.len() != leaves.len() {
        return None;
    }

    // The exact side: the same three products and the same offset, in the same
    // order as the emitted atom `((nx*px + ny*py) + nz*pz) + d`.
    let mut summands: Vec<&PTerm> = Vec::new();
    if !fpdot_flatten_add(&minus_args[1], defined, 0, &mut summands) || summands.len() != 4 {
        return None;
    }
    for (index, summand) in summands.iter().take(3).enumerate() {
        let (n_leaf, p_leaf) = fpdot_real_product(summand, defined)?;
        if n_leaf != leaves[index] || p_leaf != leaves[index + 3] {
            return None;
        }
    }
    if fpdot_to_real_leaf(summands[3], defined)? != leaves[6] {
        return None;
    }

    let (tnum, tden) = fpdot_rational(&ge_args[1], defined)?;
    Some(FpDotShape { leaves, tnum, tden })
}

/// Emit the binary64 RNE dot-product forward-error refutation, grounded in the
/// kernel-checked `AySoundness.FpBridge.guard_claim_no_model`.
///
/// # What the emitted certificate rests on
///
/// The Lean theorem is quantified over the ROUNDING SPECIFICATION, not over a
/// rounding function and not over ay's bit-blaster. `guard_claim_no_model`
/// takes thirteen arbitrary rationals and six hypotheses of the form
/// `NearestF64 r x` — "if `|x|` is under the overflow guard `2^60`, then `r` is
/// at least as close to `x` as any representable value". It is RELATIONAL, so
/// it does not even assume rounding is deterministic, and it is tie-rule
/// agnostic. Nothing in it mentions how ay computes anything: if ay's
/// bit-blaster were wrong, this certificate would be unaffected.
///
/// # The residual identification, stated so a reviewer can disagree with it
///
/// For a model of the SMT formula to contradict the theorem, five readings of
/// the SMT-LIB standard have to be right. They are SPECIFICATION readings, of
/// the same kind as (though longer than) the `Int`↔`Int` readings the other
/// emitters make. None of them is machine-checked here.
///
/// 1. `fp.mul RNE` / `fp.add RNE` denote the exact real product/sum of the
///    operands' values, rounded to the format's nearest representable value
///    (SMT-LIB `FloatingPoint`, which defers to IEEE-754 §4.3.1/§5.1). The
///    emitted atoms say exactly this, weakened to "no farther than any
///    `IsF64` point".
/// 2. `IsF64 ⊆ representable binary64`. This one is NOT a reading — it is
///    `FpBridge.isF64_representable`, proved in the kernel against the
///    independent `FpUnderflow.decodeFin 11 53` bit decode. It is the direction
///    that matters: a non-representable point inside `IsF64` would make the
///    rounding hypothesis STRONGER than the IEEE fact and the certificate
///    unsound.
/// 3. `fp.to_real` on a FINITE float is that float's exact value, and
///    `fp.to_real (fp.abs v)` is `|fp.to_real v|`. `fp.abs` is exact.
/// 4. The thirteen modeled values really are rationals. The seven leaves are
///    finite by the asserted `fp.isNormal` (which is why this emitter refuses a
///    magnitude assertion that omits it, even though the Lean atom set drops
///    it); the six intermediates are finite by
///    `FpBridge.guard_claim_intermediates_finite`, which bounds them by `2^51`
///    — nine binades under the `2^60` guard and 972 under the binary64
///    overflow threshold. That chain also supplies each `NearestF64`
///    hypothesis' antecedent in turn, so the six can be extracted in sequence.
/// 5. The `Real`-sorted claim `(>= (- (fp.to_real rf) rreal) T)` transcribes to
///    `tnum ≤ tden * (rf − dot)`. All the values involved are rational, so no
///    real-closure argument is needed.
///
/// WHAT A REVIEWER SHOULD ATTACK. The weakest link is (1): it is a reading of a
/// natural-language standard, and it is the same proposition ay's bit-blaster
/// is trying to implement. The reason that is acceptable here — and the reason
/// this differs from the earlier "restating the semantics the solver
/// implements" objection that kept this emitter closed — is that the
/// certificate assumes only that the STANDARD says this, never that AY
/// COMPUTES it. Every theory emitter restates a specification; what a firewall
/// must not do is restate an implementation. If you believe (1) misreads
/// SMT-LIB, the certificate is void; if you believe ay's blaster is buggy, the
/// certificate still stands.
///
/// # Gates
///
/// - FORMAT: [`parsed_fp_vocabulary_is_binary64`]. The `Float64` benchmark and
///   its SATISFIABLE `Float32` clone have BYTE-IDENTICAL parsed terms, so this
///   gate — not the term shape — is what stands between the emitter and a
///   `no_model` certificate for a satisfiable formula.
/// - SHAPE: exactly eight assertions — seven
///   `(and (fp.isNormal L) (<= (fp.to_real (fp.abs L)) B))` over seven DISTINCT
///   leaves with `B = 1` for the three direction leaves and `B = 2^48` for the
///   three position leaves and the offset, and one claim assertion in the
///   certified association.
/// - THRESHOLD: strictly above the certified accumulated bound `17/64`
///   (`17·tden < 64·tnum`). `guard_claim_tight_1e7` (`1e-7`) is genuinely SAT
///   and is refused here.
pub(crate) fn emit_fp_dot_error_bound_firewall_lean_from_parsed(
    parsed: &[PTerm],
    defined: &[(String, PTerm)],
    fp_formats: &[(String, Option<(u32, u32)>)],
) -> Option<String> {
    // PREREQUISITE GATE (soundness, see `parsed_fp_vocabulary_is_binary64`).
    // Everything downstream is proved only for binary64.
    if !parsed_fp_vocabulary_is_binary64(parsed, defined, fp_formats) {
        return None;
    }
    if parsed.len() != 8 {
        return None;
    }

    let mut shape: Option<FpDotShape> = None;
    let mut magnitudes: Vec<(String, (i128, i128))> = Vec::new();
    for assertion in parsed {
        if let Some(found) = fpdot_claim_assertion(assertion, defined) {
            if shape.is_some() {
                return None;
            }
            shape = Some(found);
        } else {
            magnitudes.push(fpdot_magnitude_assertion(assertion, defined)?);
        }
    }
    let shape = shape?;
    if magnitudes.len() != 7 {
        return None;
    }

    // `|n| <= 1` on the three direction leaves, `|p|,|d| <= 2^48` on the rest.
    // A LARGER asserted bound would under-approximate the true ulp, so the
    // match is exact in both directions.
    for (index, leaf) in shape.leaves.iter().enumerate() {
        let expected = if index < 3 { (1, 1) } else { (FPDOT_B48, 1) };
        let asserted = magnitudes
            .iter()
            .filter(|(name, _)| name == leaf)
            .map(|(_, bound)| *bound)
            .collect::<Vec<_>>();
        if asserted.len() != 1 || asserted[0] != expected {
            return None;
        }
        // Belt and braces over the vocabulary gate: each leaf is itself a
        // DECLARED binary64 value, not merely a symbol the gate tolerated.
        if fp_formats
            .iter()
            .find(|(name, _)| name == leaf)
            .map(|(_, format)| *format)
            != Some(Some(BINARY64_FORMAT))
        {
            return None;
        }
    }

    // THRESHOLD GATE: strictly above the certified accumulated bound 17/64.
    // `fpdot_parse_decimal` already pinned `0 < tden <= 10^18` and
    // `|tnum| <= 10^18`, so both products are far inside `i128`.
    let (tnum, tden) = (shape.tnum, shape.tden);
    if tden <= 0 || 17 * tden >= 64 * tnum {
        return None;
    }

    Some(render_fp_dot_error_bound_lean(tnum, tden))
}

/// Render the binary64 RNE dot-product forward-error firewall Lean.
///
/// Constant template up to the refuted threshold `tnum/tden` and the namespace
/// hash. The leaf NAMES are deliberately not copied into the artifact (they are
/// untrusted input and carry no proof content): the thirteen `Val` fields are
/// positional, in the same order the recognizer fixed them.
fn render_fp_dot_error_bound_lean(tnum: i128, tden: i128) -> String {
    let hash = fnv_hex(&format!("fpdotrne:{tnum}/{tden}"));
    format!(
        r#"import AySoundness.Firewall
import AySoundness.FpBridge
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — binary64 RNE dot-product FORWARD-ERROR
  refutation, grounded in the verified `firewall_combined_unsat` and in
  `AySoundness.FpBridge.guard_claim_no_model`.

  Seven binary64 leaves with `|n| <= 1` and `|p|,|d| <= 2^48`, the six-operation
  RNE evaluation `rf = ((n*p + n*p) + n*p) + d`, and the refuted claim
  `rf - exact_dot >= {tnum}/{tden}`. The certified accumulated half-ULP forward
  error is `17/64`, and `17*{tden} < 64*{tnum}`, so the claim has no model.

  THE ROUNDING HYPOTHESIS IS A SPECIFICATION, NOT AN IMPLEMENTATION. Atoms 8-13
  are `FpBridge.NearestF64 r x`: "if `|x| <= 2^60` then `r` is at least as close
  to `x` as ANY `IsF64` point". `guard_claim_no_model` is universally quantified
  over all thirteen rationals satisfying that relation, so the certificate is
  independent of how ay computes floating point — a buggy bit-blaster cannot
  make it true and cannot make it false. `FpBridge.isF64_representable` proves
  in the kernel that every `IsF64` point IS a finite binary64 bit pattern (under
  the independent `FpUnderflow.decodeFin 11 53` decode), which is the direction
  that keeps the hypothesis weaker than the IEEE-754 fact.

  The `fp.isNormal` conjunct of each leaf assertion is DROPPED from the atom set
  (refuting a weaker set refutes the original); it is required syntactically by
  the emitter because it is what makes `fp.to_real` of each leaf a rational at
  all. The six intermediates' finiteness is not assumed: it is
  `FpBridge.guard_claim_intermediates_finite` (all `<= 2^51`).

  Model: thirteen `Rat` fields — the `fp.to_real` values of the seven leaves and
  of the six rounded intermediates. Pure Lean 4 core + `FpBridge`.
-/
namespace AySoundness.Emitted.FpDotRne_{hash}
open AySoundness
open AySoundness.FpBridge

attribute [local instance] Classical.propDecidable

structure Val where
  nx : Rat
  ny : Rat
  nz : Rat
  px : Rat
  py : Rat
  pz : Rat
  d : Rat
  t1 : Rat
  t2 : Rat
  t3 : Rat
  s1 : Rat
  s2 : Rat
  rf : Rat

/-- Atoms 1-7: the asserted magnitude bounds. Atoms 8-13: the IEEE-754 RNE
    nearest-value specification of the six recognized operations. Atom 14: the
    refuted claim, scaled to `{tnum} <= {tden} * (rf - dot)`. -/
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (AbsLe m.nx 1)
  | 2 => decide (AbsLe m.ny 1)
  | 3 => decide (AbsLe m.nz 1)
  | 4 => decide (AbsLe m.px B48)
  | 5 => decide (AbsLe m.py B48)
  | 6 => decide (AbsLe m.pz B48)
  | 7 => decide (AbsLe m.d B48)
  | 8 => decide (NearestF64 m.t1 (m.nx * m.px))
  | 9 => decide (NearestF64 m.t2 (m.ny * m.py))
  | 10 => decide (NearestF64 m.t3 (m.nz * m.pz))
  | 11 => decide (NearestF64 m.s1 (m.t1 + m.t2))
  | 12 => decide (NearestF64 m.s2 (m.s1 + m.t3))
  | 13 => decide (NearestF64 m.rf (m.s2 + m.d))
  | 14 => decide (({tnum} : Rat) ≤ ({tden} : Rat) *
            (m.rf - (((m.nx * m.px + m.ny * m.py) + m.nz * m.pz) + m.d)))
  | _ => false

def original : List (Cid × Clause) :=
  [(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]),
   (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14])]

def lemmas : List (Cid × Clause) :=
  [(15, [-1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12, -13, -14])]

def proof : List (Cid × Clause × List Int) :=
  [(16, [], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])]

theorem lemma_valid (m : Val) :
    clauseSat (atomVal m) [-1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12, -13, -14] = true := by
  by_cases h1 : AbsLe m.nx 1
  · by_cases h2 : AbsLe m.ny 1
    · by_cases h3 : AbsLe m.nz 1
      · by_cases h4 : AbsLe m.px B48
        · by_cases h5 : AbsLe m.py B48
          · by_cases h6 : AbsLe m.pz B48
            · by_cases h7 : AbsLe m.d B48
              · by_cases h8 : NearestF64 m.t1 (m.nx * m.px)
                · by_cases h9 : NearestF64 m.t2 (m.ny * m.py)
                  · by_cases h10 : NearestF64 m.t3 (m.nz * m.pz)
                    · by_cases h11 : NearestF64 m.s1 (m.t1 + m.t2)
                      · by_cases h12 : NearestF64 m.s2 (m.s1 + m.t3)
                        · by_cases h13 : NearestF64 m.rf (m.s2 + m.d)
                          · by_cases h14 : ({tnum} : Rat) ≤ ({tden} : Rat) *
                                (m.rf - (((m.nx * m.px + m.ny * m.py) + m.nz * m.pz) + m.d))
                            · exact absurd
                                (guard_claim_no_model m.nx m.ny m.nz m.px m.py m.pz m.d
                                  m.t1 m.t2 m.t3 m.s1 m.s2 m.rf
                                  ((1 : Rat) / ((32 : Int) : Rat))
                                  ((1 : Rat) / ((16 : Int) : Rat))
                                  ((1 : Rat) / ((8 : Int) : Rat))
                                  ((1 : Rat) / ((4 : Int) : Rat))
                                  (Rat.div_mul_cancel (by decide))
                                  (Rat.div_mul_cancel (by decide))
                                  (Rat.div_mul_cancel (by decide))
                                  (Rat.div_mul_cancel (by decide))
                                  h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
                                  {tnum} {tden} (by omega) (by omega) (by simpa using h14))
                                (by simp)
                            -- NOT `simp [.., atomVal, h14]`: with `tden = 1`
                            -- `simp` rewrites `1 * x` to `x` in the goal but
                            -- not in `h14`, and the branch stops closing.
                            -- Discharging the atom first is `tden`-independent.
                            · have h14false : atomVal m 14 = false := by
                                simp only [atomVal, decide_eq_false_iff_not]
                                exact h14
                              simp [clauseSat, litSat, List.any_cons, List.any_nil, h14false]
                          · simp [clauseSat, litSat, atomVal, h13]
                        · simp [clauseSat, litSat, atomVal, h12]
                      · simp [clauseSat, litSat, atomVal, h11]
                    · simp [clauseSat, litSat, atomVal, h10]
                  · simp [clauseSat, litSat, atomVal, h9]
                · simp [clauseSat, litSat, atomVal, h8]
              · simp [clauseSat, litSat, atomVal, h7]
            · simp [clauseSat, litSat, atomVal, h6]
          · simp [clauseSat, litSat, atomVal, h5]
        · simp [clauseSat, litSat, atomVal, h4]
      · simp [clauseSat, litSat, atomVal, h3]
    · simp [clauseSat, litSat, atomVal, h2]
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- The asserted binary64 `guard_claim` set has NO model — via the firewall.
    Reads through the IEEE-754 round-to-nearest SPECIFICATION (`NearestF64`),
    not through any rounding implementation. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.FpDotRne_{hash}
"#,
    )
}

/// `(str.len s)` (parsed) → `s`.
fn parsed_str_len_arg(t: &PTerm) -> Option<String> {
    match t {
        PTerm::App(op, args) if op == "str.len" && args.len() == 1 => match &args[0] {
            PTerm::Symbol(s) => Some(s.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// A non-negative integer numeral (parsed) → its `i64` value.
fn parsed_numeral(t: &PTerm) -> Option<i64> {
    match t {
        PTerm::Const(PConst::Numeral(n)) => n.parse::<i64>().ok(),
        _ => None,
    }
}

/// Escape a string for a Lean string literal.
fn lean_string_lit(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn render_string_length_lean(lit: &str, k: i64) -> String {
    let hash = fnv_hex(&format!("strlen:{lit}\u{1}{k}"));
    let lit_lean = lean_string_lit(lit);
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — string length-vs-literal conflict
  grounded in the verified `firewall_combined_unsat`. `s = L ∧ str.len s = K`
  (with `L.length ≠ K`) is unsatisfiable; the tautology `¬(s = L) ∨ ¬(len s = K)`
  holds because `s = L ⟹ s.length = |L| ≠ K`. Reconstructed from the frontend
  parsed ASSERTIONS (the conflict lemma is surface-rewrite-trivialized before
  emit, at both the lemma and TermId-assertion level). Model: `Val = String`
  (Lean core). Pure Lean 4 core.
-/
namespace AySoundness.Emitted.StrLen_{hash}
open AySoundness

abbrev Val := String

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m = {lit_lean})
  | 2 => decide (m.length = {k})
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, -2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1, -2] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h : m = {lit_lean}
  · subst h; decide
  · simp [h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No string is both equal to the modeled literal and of length {k} — via the
    firewall. The untrusted literal is intentionally not copied into comments. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.StrLen_{hash}
"#,
    )
}

/// Render the sequence length-over-concat firewall Lean for the offset `k`
/// (`k > 0`). Grounds `SeqThy.len_concat` through the verified
/// `firewall_combined_unsat` over `Val = Seq Int × Seq Int`. Constant template up
/// to the numeric offset and namespace hash.
fn render_seq_len_concat_lean(k: i64) -> String {
    let hash = fnv_hex(&format!("seqlenconcat:{k}"));
    format!(
        r#"import AySoundness.Firewall
import AySoundness.SeqThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — SEQUENCE length-over-concat conflict
  grounded in the verified `firewall_combined_unsat`. The assertion
  `seq.len (seq.++ X Y) = seq.len X + seq.len Y + {k}` (with `{k} > 0`) is
  unsatisfiable: the verified axiom `SeqThy.len_concat` gives
  `len (concat X Y) = len X + len Y`, so it demands `n = n + {k}`, impossible.
  Reconstructed from the frontend parsed ASSERTIONS (ay reduces seq.len/seq.++
  eagerly, so the conflict is surface-rewrite-trivialized before emit). Model:
  `Val = Seq Int × Seq Int` (the two concat operands); lengths are `Nat`. The
  certificate quantifies over all independent components, so it also covers the
  diagonal `X = Y`. Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.SeqLenConcat_{hash}
open AySoundness

abbrev Val := SeqThy.Seq Int × SeqThy.Seq Int

/-- Atom `1 ↦ len (X ++ Y) = len X + len Y + {k}`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (SeqThy.len (SeqThy.concat m.1 m.2) = SeqThy.len m.1 + SeqThy.len m.2 + {k})
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have h : SeqThy.len (SeqThy.concat m.1 m.2) = SeqThy.len m.1 + SeqThy.len m.2 :=
    SeqThy.len_concat m.1 m.2
  have ha : atomVal m 1 = false := by
    simp only [atomVal, h, decide_eq_false_iff_not]
    omega
  simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No sequences make `len (X ++ Y)` exceed `len X + len Y` by {k} — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.SeqLenConcat_{hash}
"#,
    )
}

/// Render the string length-over-concat firewall Lean for the offset `k`
/// (`k > 0`). Grounds `StringThy.len_cat` through the verified
/// `firewall_combined_unsat` over `Val = StringThy.Str × StringThy.Str` (the
/// standard `List Nat` sequence model). Constant template up to the numeric
/// offset and namespace hash.
fn render_str_len_concat_lean(k: i64) -> String {
    let hash = fnv_hex(&format!("strlenconcat:{k}"));
    format!(
        r#"import AySoundness.Firewall
import AySoundness.StringThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — STRING length-over-concat conflict
  grounded in the verified `firewall_combined_unsat`. The assertion
  `str.len (str.++ X Y) = str.len X + str.len Y + {k}` (with `{k} > 0`) is
  unsatisfiable: the verified axiom `StringThy.len_cat` gives
  `len (cat X Y) = len X + len Y`, so it demands `n = n + {k}`, impossible.
  Reconstructed from the frontend parsed ASSERTIONS (ay reduces str.len/str.++
  eagerly, so the conflict is surface-rewrite-trivialized before emit). Model:
  `Val = StringThy.Str × StringThy.Str` (the two concat operands; a string is the
  free monoid `List Nat`); lengths are `Nat`. The certificate quantifies over all
  independent components, so it also covers the diagonal `X = Y`. Pure Lean 4
  core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.StrLenConcat_{hash}
open AySoundness

abbrev Val := StringThy.Str × StringThy.Str

/-- Atom `1 ↦ len (X ++ Y) = len X + len Y + {k}`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (StringThy.len (StringThy.cat m.1 m.2) = StringThy.len m.1 + StringThy.len m.2 + {k})
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have h : StringThy.len (StringThy.cat m.1 m.2) = StringThy.len m.1 + StringThy.len m.2 :=
    StringThy.len_cat m.1 m.2
  have ha : atomVal m 1 = false := by
    simp only [atomVal, h, decide_eq_false_iff_not]
    omega
  simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No strings make `len (X ++ Y)` exceed `len X + len Y` by {k} — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.StrLenConcat_{hash}
"#,
    )
}

/// Render the string empty-length conflict firewall Lean for the symbol `s`.
/// Grounds `StringThy.len_zero_iff` (`len s = 0 ↔ s = ε`) through the verified
/// `firewall_combined_unsat` over `Val = StringThy.Str`. The symbol name only
/// distinguishes the namespace; the template is otherwise constant.
fn render_str_len_zero_lean(s: &str) -> String {
    let hash = fnv_hex(&format!("strlenzero:{s}"));
    format!(
        r#"import AySoundness.Firewall
import AySoundness.StringThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — STRING empty-length conflict grounded in
  the verified `firewall_combined_unsat`. The literals `str.len s = 0` and
  `s ≠ ""` are jointly unsatisfiable: the verified axiom `StringThy.len_zero_iff`
  gives `len s = 0 ↔ s = ε`, so `len s = 0` forces `s = ""`, contradicting
  `s ≠ ""`. Reconstructed from the frontend parsed ASSERTIONS (ay reduces str.len
  eagerly, so the conflict is surface-rewrite-trivialized before emit). Model:
  `Val = StringThy.Str` (a string is the free monoid `List Nat`; `ε = []`). Pure
  Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.StrLenZero_{hash}
open AySoundness

abbrev Val := StringThy.Str

/-- Atom `1 ↦ len s = 0`; atom `2 ↦ s = ε`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (StringThy.len m = 0)
  | 2 => decide (m = StringThy.empty)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [-2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, 2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h : StringThy.len m = 0
  · have he : m = StringThy.empty := (StringThy.len_zero_iff m).mp h
    simp [he]
  · simp [h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No string is both length-zero and non-empty — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.StrLenZero_{hash}
"#,
    )
}

// ---------------------------------------------------------------------------
// `str.at` / `seq.at` / `seq.nth` firewall emitters (grounded in the verified
// `AySoundness.StrAt` / `AySoundness.SeqThy` positional-read lemmas).
// ---------------------------------------------------------------------------

/// A GROUND sequence element: an `Int` or a `Bool` literal. Used to reconstruct
/// concrete `seq.unit` / `seq.++` content for the `seq.at` / `seq.nth` firewall
/// emitters so the emitted Lean can close by `decide` over the exact values.
#[derive(Clone, Copy, PartialEq)]
enum SeqElt {
    Int(i64),
    Bool(bool),
}

impl SeqElt {
    /// The Lean element-type name (`Int` / `Bool`).
    fn lean_ty(self) -> &'static str {
        match self {
            SeqElt::Int(_) => "Int",
            SeqElt::Bool(_) => "Bool",
        }
    }

    /// The bare Lean literal (`-2`, `true`) — the surrounding list / `seq.unit`
    /// carries the `: SeqThy.Seq _` / `: _` ascription.
    fn lean_bare(self) -> String {
        match self {
            SeqElt::Int(n) => n.to_string(),
            SeqElt::Bool(b) => {
                if b {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            }
        }
    }
}

/// Parse an `Int`-or-`Bool` value literal (a `seq.unit` operand). Negative
/// integers LEX AS SYMBOLS (`-2`), so a symbol that parses as `i64` is accepted;
/// `(- x)` unary negation is folded too.
fn parse_seq_elt(t: &PTerm) -> Option<SeqElt> {
    match t {
        PTerm::Const(PConst::Numeral(n)) => n.parse::<i64>().ok().map(SeqElt::Int),
        PTerm::Const(PConst::True) => Some(SeqElt::Bool(true)),
        PTerm::Const(PConst::False) => Some(SeqElt::Bool(false)),
        PTerm::Symbol(s) => s.parse::<i64>().ok().map(SeqElt::Int),
        PTerm::App(op, args) if op == "-" && args.len() == 1 => match parse_seq_elt(&args[0]) {
            Some(SeqElt::Int(n)) => Some(SeqElt::Int(-n)),
            _ => None,
        },
        _ => None,
    }
}

/// Reconstruct a fully-GROUND sequence value from a parsed term, resolving symbol
/// references through `binds` (symbol → its bound ground seq). Handles
/// `(seq.unit V)`, n-ary `(seq.++ …)`, `(as seq.empty …)`, and bound symbols.
/// `None` if any part is not ground.
fn parse_ground_seq(t: &PTerm, binds: &[(String, Vec<SeqElt>)]) -> Option<Vec<SeqElt>> {
    match t {
        PTerm::Symbol(s) => binds.iter().find(|(n, _)| n == s).map(|(_, v)| v.clone()),
        // (as seq.empty (Seq _)) — the empty sequence.
        PTerm::QualifiedApp(id, _, args) if args.is_empty() => {
            (id.as_symbol() == Some("seq.empty")).then(Vec::new)
        }
        PTerm::App(op, args) if op == "seq.unit" && args.len() == 1 => {
            parse_seq_elt(&args[0]).map(|e| vec![e])
        }
        PTerm::App(op, args) if op == "seq.++" => {
            let mut out = Vec::new();
            for a in args {
                out.extend(parse_ground_seq(a, binds)?);
            }
            Some(out)
        }
        _ => None,
    }
}

/// The element type shared by a ground seq's elements (`None` if empty / mixed).
fn seq_elt_ty(elts: &[SeqElt]) -> Option<&'static str> {
    let first = elts.first()?.lean_ty();
    elts.iter().all(|e| e.lean_ty() == first).then_some(first)
}

/// Render a ground seq as a bare Lean list literal (`[3, -2, 3]`, `[]`).
fn seq_list_lean(elts: &[SeqElt]) -> String {
    format!(
        "[{}]",
        elts.iter()
            .map(|e| e.lean_bare())
            .collect::<Vec<_>>()
            .join(", ")
    )
}

/// Collect `(= sym numeral)` integer pins from the parsed assertions.
fn collect_int_binds(parsed: &[PTerm]) -> Vec<(String, i64)> {
    let mut v = Vec::new();
    for a in parsed {
        let PTerm::App(op, args) = a else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        for (p, q) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            if let (PTerm::Symbol(s), Some(n)) = (p, parsed_numeral(q)) {
                v.push((s.clone(), n));
            }
        }
    }
    v
}

/// Collect `(= sym ground-seq)` bindings, iterated to a fixpoint so a binding
/// whose RHS references an earlier-bound symbol still resolves.
fn collect_seq_binds(parsed: &[PTerm]) -> Vec<(String, Vec<SeqElt>)> {
    let mut binds: Vec<(String, Vec<SeqElt>)> = Vec::new();
    loop {
        let mut changed = false;
        for a in parsed {
            let PTerm::App(op, args) = a else { continue };
            if op != "=" || args.len() != 2 {
                continue;
            }
            for (p, q) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                if let PTerm::Symbol(s) = p {
                    if binds.iter().any(|(n, _)| n == s) {
                        continue;
                    }
                    if let Some(g) = parse_ground_seq(q, &binds) {
                        binds.push((s.clone(), g));
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    binds
}

/// Resolve an index term to a concrete `i64` (a numeral, a negative-symbol
/// numeral, or an integer-pinned symbol).
fn resolve_index(t: &PTerm, int_binds: &[(String, i64)]) -> Option<i64> {
    match t {
        PTerm::Const(PConst::Numeral(n)) => n.parse::<i64>().ok(),
        PTerm::Symbol(s) => {
            if let Ok(n) = s.parse::<i64>() {
                return Some(n);
            }
            int_binds.iter().find(|(k, _)| k == s).map(|(_, v)| *v)
        }
        _ => None,
    }
}

/// The in-range element read `list[idx]` (`None` when out of range / negative).
fn eval_read(list: &[SeqElt], idx: i64) -> Option<SeqElt> {
    if idx < 0 {
        return None;
    }
    list.get(idx as usize).copied()
}

/// Constant-fold a ground integer arithmetic term (`Numeral`, negative symbol,
/// unary/binary `-`, n-ary `+`/`*`), resolving pinned symbols through `binds`.
fn fold_int(t: &PTerm, binds: &[(String, i64)]) -> Option<i64> {
    match t {
        PTerm::Const(PConst::Numeral(n)) => n.parse::<i64>().ok(),
        PTerm::Symbol(s) => {
            if let Ok(n) = s.parse::<i64>() {
                return Some(n);
            }
            binds.iter().find(|(k, _)| k == s).map(|(_, v)| *v)
        }
        PTerm::App(op, a) if op == "-" && a.len() == 1 => Some(-fold_int(&a[0], binds)?),
        PTerm::App(op, a) if op == "-" && a.len() == 2 => {
            Some(fold_int(&a[0], binds)? - fold_int(&a[1], binds)?)
        }
        PTerm::App(op, a) if op == "+" && !a.is_empty() => {
            let mut s = 0i64;
            for x in a {
                s = s.checked_add(fold_int(x, binds)?)?;
            }
            Some(s)
        }
        PTerm::App(op, a) if op == "*" && !a.is_empty() => {
            let mut s = 1i64;
            for x in a {
                s = s.checked_mul(fold_int(x, binds)?)?;
            }
            Some(s)
        }
        _ => None,
    }
}

/// Flatten nested `(and …)` into a flat list of conjuncts.
fn flatten_and<'a>(t: &'a PTerm, out: &mut Vec<&'a PTerm>) {
    if let PTerm::App(op, args) = t {
        if op == "and" {
            for a in args {
                flatten_and(a, out);
            }
            return;
        }
    }
    out.push(t);
}

/// Emit a verified-firewall Lean proof for a `str.at` LENGTH conflict found among
/// the PARSED assertions: `(= (str.len (str.at T IDX)) N)` (either operand order)
/// with a constant `N ≥ 2`. This is unsatisfiable for ANY string `T` and ANY
/// index: the verified `AySoundness.StrAt.strAt_len_eq_conflict` shows
/// `str.len (str.at s i) ≤ 1`, so it can never equal `N ≥ 2`.
///
/// The bound is index-UNIVERSAL (no case split): the certificate quantifies over
/// all `Str × Nat`, so the concrete symbolic index (`(select a i)` etc.) and any
/// red-herring assertions are irrelevant. Grounded through the verified
/// `firewall_combined_unsat` over `Val = StringThy.Str × Nat`. `None` if no such
/// conflict. Single-conflict, fail-closed.
pub(crate) fn emit_str_at_len_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        for (p, q) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            // p = (str.len (str.at _ _))
            let PTerm::App(lop, largs) = p else { continue };
            if lop != "str.len" || largs.len() != 1 {
                continue;
            }
            let PTerm::App(aop, aargs) = &largs[0] else {
                continue;
            };
            if aop != "str.at" || aargs.len() != 2 {
                continue;
            }
            // q = numeral N ≥ 2
            if let Some(n) = parsed_numeral(q) {
                if n >= 2 {
                    return Some(render_str_at_len_lean(n));
                }
            }
        }
    }
    None
}

/// Render the `str.at` length-conflict firewall Lean for the asserted length `n`
/// (`n ≥ 2`). Grounds `AySoundness.StrAt.strAt_len_eq_conflict` through the
/// verified `firewall_combined_unsat` over `Val = StringThy.Str × Nat` (the
/// abstract string and its abstract read index).
fn render_str_at_len_lean(n: i64) -> String {
    let hash = fnv_hex(&format!("stratlen:{n}"));
    format!(
        r#"import AySoundness.Firewall
import AySoundness.StringThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — `str.at` LENGTH conflict grounded in the
  verified `firewall_combined_unsat`. The assertion `str.len (str.at t i) = {n}`
  (with `{n} ≥ 2`) is unsatisfiable: the verified axiom
  `AySoundness.StrAt.strAt_len_eq_conflict` gives `str.len (str.at s i) ≤ 1` for
  ANY string and ANY index, so it can never equal `{n}`. The bound is
  index-UNIVERSAL — no case split, and the concrete symbolic index (and any
  red-herring assertions) are irrelevant. Reconstructed from the frontend parsed
  ASSERTIONS (ay reduces str.at eagerly, so the conflict is surface-rewrite-
  trivialized before emit). Model: `Val = StringThy.Str × Nat` (abstract string ×
  abstract index). Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.StrAtLen_{hash}
open AySoundness

abbrev Val := StringThy.Str × Nat

/-- Atom `1 ↦ str.len (str.at t i) = {n}`. -/
def atomVal (m : Val) (k : Nat) : Bool :=
  match k with
  | 1 => decide (StringThy.len (StrAt.strAt m.1 m.2) = {n})
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have ha : atomVal m 1 = false := by
    simp only [atomVal, decide_eq_false_iff_not]
    exact StrAt.strAt_len_eq_conflict m.1 m.2 {n} (by decide)
  simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No string's `str.at` read has length {n} — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.StrAtLen_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a fully-GROUND `seq.at` value-mismatch
/// conflict found among the PARSED assertions: `(= (seq.unit V) (seq.at S I))`
/// (either operand order) where `S` resolves to a ground sequence, `I` to a
/// pinned in-range index, and the read element differs from `V`.
///
/// Fully ground — no case split. The read `seq.at S I = seq.unit (S[I])` has
/// length 1, so both sides are length-1 singletons and the conflict is the ELEMENT
/// mismatch `V ≠ S[I]`, closed by `decide` over the verified `SeqThy.seqAt` /
/// `SeqThy.unit` model. Grounded through `firewall_combined_unsat` over the
/// trivial `Val = Unit`. `None` unless the read is in range and the values differ.
pub(crate) fn emit_seq_at_pinned_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    let int_binds = collect_int_binds(parsed);
    let seq_binds = collect_seq_binds(parsed);
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        for (p, q) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            // p = (seq.unit V)
            let PTerm::App(uop, uargs) = p else { continue };
            if uop != "seq.unit" || uargs.len() != 1 {
                continue;
            }
            let Some(vu) = parse_seq_elt(&uargs[0]) else {
                continue;
            };
            // q = (seq.at S I)
            let PTerm::App(aop, aargs) = q else { continue };
            if aop != "seq.at" || aargs.len() != 2 {
                continue;
            }
            let Some(list) = parse_ground_seq(&aargs[0], &seq_binds) else {
                continue;
            };
            let Some(idx) = resolve_index(&aargs[1], &int_binds) else {
                continue;
            };
            let Some(read) = eval_read(&list, idx) else {
                continue;
            };
            // Genuine value mismatch (same element kind, distinct value).
            if read.lean_ty() != vu.lean_ty() || read == vu {
                continue;
            }
            if let Some(ty) = seq_elt_ty(&list) {
                return Some(render_seq_at_pinned_lean(vu, &list, idx, ty));
            }
        }
    }
    None
}

/// Render the ground `seq.at` value-mismatch firewall Lean. Grounds the verified
/// `SeqThy.seqAt` / `SeqThy.unit` model by `decide` over `Val = Unit`.
fn render_seq_at_pinned_lean(vu: SeqElt, list: &[SeqElt], idx: i64, ty: &str) -> String {
    let hash = fnv_hex(&format!(
        "seqatpinned:{}:{}:{idx}",
        vu.lean_bare(),
        seq_list_lean(list)
    ));
    let list_lean = seq_list_lean(list);
    let vu_bare = vu.lean_bare();
    format!(
        r#"import AySoundness.Firewall
import AySoundness.SeqThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — GROUND `seq.at` value-mismatch conflict
  grounded in the verified `firewall_combined_unsat`. The literal
  `seq.unit V = seq.at s i` is unsatisfiable: the read `seq.at s i` wraps the
  in-range element `s[i]` into a length-1 sequence, so the equation forces
  `V = s[i]` — false for the concrete ground values. Discharged by `decide` over
  the verified `SeqThy.seqAt` / `SeqThy.unit` model (mirrors
  `SeqThy.ex_seqat_pinned_conflict`). Reconstructed from the frontend parsed
  ASSERTIONS (ay reduces seq.at eagerly). Model: `Val = Unit` (fully ground). Pure
  Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.SeqAtPinned_{hash}
open AySoundness

abbrev Val := Unit

/-- Atom `1 ↦ seq.unit V = seq.at s i` (the asserted, ground-false equation). -/
def atomVal (_m : Val) (k : Nat) : Bool :=
  match k with
  | 1 => decide (SeqThy.unit ({vu_bare} : {ty}) = SeqThy.seqAt (({list_lean}) : SeqThy.Seq {ty}) {idx})
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have ha : atomVal m 1 = false := by cases m <;> decide
  simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- The pinned `seq.unit` value does not match the `seq.at` read — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.SeqAtPinned_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a `seq.suffixof` LAST-ELEMENT-mismatch
/// conflict found among the PARSED assertions: `(seq.suffixof X Y)` where `X`
/// resolves to a ground NON-EMPTY sequence ending in `a`, `Y` is `(seq.++ … T)`
/// whose LAST operand `T` resolves to a ground NON-EMPTY sequence ending in
/// `b ≠ a` (the prefix operands are arbitrary). A non-empty suffix shares the
/// whole's last element, so `X` (ending in `a`) can be a suffix of `p ++ T`
/// (ending in `b`) for NO prefix `p` — unsatisfiable for the WHOLE assertion.
///
/// Grounded through the verified `SeqThy.suffix_append_last_conflict` (built from
/// the kernel-verified `suffixOf` / `getLast?_of_suffix` / `suffix_last_conflict`):
/// the emitted `no_model` quantifies the prefix `p` universally, so it refutes the
/// suffix relation for every value of the concrete prefix (`v3` etc.). The tail
/// `T` and the alleged suffix `X` are ground concrete lists, so every side
/// condition (`X ≠ []`, `T ≠ []`, the two `getLast?`s, `a ≠ b`) closes by `decide`.
/// `None` (fail-closed) unless the read is a genuine non-empty-suffix last-element
/// mismatch over a shared element type.
pub(crate) fn emit_seq_suffixof_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    let seq_binds = collect_seq_binds(parsed);
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "seq.suffixof" || args.len() != 2 {
            continue;
        }
        // X = the alleged suffix: ground, non-empty, last element `a`.
        let Some(xlist) = parse_ground_seq(&args[0], &seq_binds) else {
            continue;
        };
        let Some(a) = xlist.last().copied() else {
            continue;
        };
        // Y = the whole. Its LAST `seq.++` operand (or Y itself) is the ground,
        // non-empty tail `T`, last element `b`; the prefix operands are arbitrary.
        let tail_term = match &args[1] {
            PTerm::App(yop, yargs) if yop == "seq.++" && !yargs.is_empty() => yargs.last().unwrap(),
            other => other,
        };
        let Some(tlist) = parse_ground_seq(tail_term, &seq_binds) else {
            continue;
        };
        let Some(b) = tlist.last().copied() else {
            continue;
        };
        // Genuine element mismatch over a shared element type.
        if a.lean_ty() != b.lean_ty() || a == b {
            continue;
        }
        let (Some(tyx), Some(tyt)) = (seq_elt_ty(&xlist), seq_elt_ty(&tlist)) else {
            continue;
        };
        if tyx != tyt {
            continue;
        }
        return Some(render_seq_suffixof_lean(&xlist, &tlist, a, b, tyx));
    }
    None
}

/// Render the `seq.suffixof` last-element-mismatch firewall Lean. Grounds the
/// verified `SeqThy.suffix_append_last_conflict` over a universally-quantified
/// prefix `p : List ty`; the suffix `x` and tail `t` are ground concrete lists so
/// all side conditions close by `decide`.
fn render_seq_suffixof_lean(
    xlist: &[SeqElt],
    tlist: &[SeqElt],
    a: SeqElt,
    b: SeqElt,
    ty: &str,
) -> String {
    let x_lean = seq_list_lean(xlist);
    let t_lean = seq_list_lean(tlist);
    let a_bare = a.lean_bare();
    let b_bare = b.lean_bare();
    let hash = fnv_hex(&format!(
        "seqsuffixof:{x_lean}:{t_lean}:{a_bare}:{b_bare}:{ty}"
    ));
    format!(
        r#"import AySoundness.Firewall
import AySoundness.SeqThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — `seq.suffixof` LAST-ELEMENT-mismatch
  conflict grounded in the verified `SeqThy.suffix_append_last_conflict` (itself
  built from the kernel-verified `suffixOf` / `getLast?_of_suffix` /
  `suffix_last_conflict`). The assertion `seq.suffixof x (seq.++ … t)` is
  unsatisfiable: a NON-EMPTY suffix shares the whole's LAST element, but the
  alleged suffix `x = {x_lean}` ends in `{a_bare}` while the whole ends in
  `{b_bare}` (the last `seq.++` operand `t = {t_lean}` is ground and non-empty, so
  `last (p ++ t) = last t = {b_bare}` for EVERY prefix `p`), and `{a_bare} ≠
  {b_bare}`. Reconstructed from the frontend parsed ASSERTIONS (ay reduces
  seq.suffixof / seq.++ eagerly). The prefix `p` is quantified UNIVERSALLY, so the
  certificate refutes the suffix relation for every value of the concrete prefix;
  `x` and `t` are ground concrete lists, so every side condition closes by
  `decide`. Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.SeqSuffixof_{hash}
open AySoundness

/-- No prefix `p` makes `x = {x_lean}` a suffix of `p ++ {t_lean}`: the whole ends
    in `{b_bare}`, the suffix in `{a_bare}`, and `{a_bare} ≠ {b_bare}`. -/
theorem no_model (p : List {ty}) :
    ¬ SeqThy.suffixOf (({x_lean}) : List {ty}) (p ++ (({t_lean}) : List {ty})) :=
  fun h => SeqThy.suffix_append_last_conflict (({x_lean}) : List {ty}) p
    (({t_lean}) : List {ty}) ({a_bare}) ({b_bare}) h
    (by decide) (by decide) (by decide) (by decide) (by decide)

end AySoundness.Emitted.SeqSuffixof_{hash}
"#,
    )
}

/// Parse an `Int`/`Bool` `seq.unit` operand, folding ground integer arithmetic
/// (`(- 0 2)`, pinned symbols) that `parse_seq_elt` alone does not reach.
fn parse_seq_elt_arith(t: &PTerm, int_binds: &[(String, i64)]) -> Option<SeqElt> {
    if let Some(e) = parse_seq_elt(t) {
        return Some(e);
    }
    fold_int(t, int_binds).map(SeqElt::Int)
}

/// Reconstruct a fully-GROUND sequence value like `parse_ground_seq`, but fold
/// ground integer arithmetic inside `seq.unit` operands (`(seq.unit (- 0 2))`).
fn parse_ground_seq_arith(
    t: &PTerm,
    seq_binds: &[(String, Vec<SeqElt>)],
    int_binds: &[(String, i64)],
) -> Option<Vec<SeqElt>> {
    match t {
        PTerm::Symbol(s) => seq_binds
            .iter()
            .find(|(n, _)| n == s)
            .map(|(_, v)| v.clone()),
        PTerm::QualifiedApp(id, _, args) if args.is_empty() => {
            (id.as_symbol() == Some("seq.empty")).then(Vec::new)
        }
        PTerm::App(op, args) if op == "seq.unit" && args.len() == 1 => {
            parse_seq_elt_arith(&args[0], int_binds).map(|e| vec![e])
        }
        PTerm::App(op, args) if op == "seq.++" => {
            let mut out = Vec::new();
            for a in args {
                out.extend(parse_ground_seq_arith(a, seq_binds, int_binds)?);
            }
            Some(out)
        }
        _ => None,
    }
}

/// Emit a verified-firewall Lean certificate for an OUT-OF-BOUNDS `seq.extract`
/// feeding a `seq.replace`'s needle that then conflicts with an asserted whole:
/// `(= (seq.replace HAYSTACK (seq.extract S I N) T) WHOLE)` where the extract
/// offset `I` is a concrete literal `≥ len(S)` (so the needle is EMPTY for every
/// count `N`), `T` is a ground NON-EMPTY sequence with head `a`, and `WHOLE` is a
/// ground NON-EMPTY sequence with head `b ≠ a`.
///
/// SMT `seq.replace` with an EMPTY needle matches at position 0 and PREPENDS the
/// replacement, so the result is `T ++ HAYSTACK`, whose head is pinned by `T`'s
/// head `a` for EVERY haystack (verified `SeqThy.seqReplaceEmpty_head`). Asserting
/// the whole equals `WHOLE` (head `b`) is therefore unsatisfiable for every
/// haystack and every count. The needle's emptiness is grounded through the
/// verified `SeqThy.seqExtract_oob` (offset ≥ length ⇒ empty, for all `N`); the
/// head clash is `SeqThy.seqReplaceEmpty_head`; cf. the hand-checked witnesses
/// `SeqThy.ex_seqExtract_oob_replace_conflict` /
/// `SeqThy.ex_seqExtract_oob_replace_via_principle`. The haystack `s0` and the
/// count `n` are quantified UNIVERSALLY, so the certificate refutes the assertion
/// for every value of the concrete haystack/count.
///
/// `None` (fail-closed) unless the read is a genuine OOB-extract / empty-needle
/// replace with a NON-EMPTY replacement whose head differs from a NON-EMPTY whole
/// over a single shared element type.
pub(crate) fn emit_seq_extract_oob_replace_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    let seq_binds = collect_seq_binds(parsed);
    let int_binds = collect_int_binds(parsed);
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        // One side is the `seq.replace`; the other is the ground WHOLE.
        for (repl_side, whole_side) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            let PTerm::App(rop, rargs) = repl_side else {
                continue;
            };
            if rop != "seq.replace" || rargs.len() != 3 {
                continue;
            }
            // Needle must be an OOB `seq.extract`: `(seq.extract S I N)` with the
            // offset `I` a concrete literal `≥ len(S)` (so the slice is empty).
            let PTerm::App(eop, eargs) = &rargs[1] else {
                continue;
            };
            if eop != "seq.extract" || eargs.len() != 3 {
                continue;
            }
            let Some(inner) = parse_ground_seq_arith(&eargs[0], &seq_binds, &int_binds) else {
                continue;
            };
            let Some(offset) = resolve_index(&eargs[1], &int_binds) else {
                continue;
            };
            // OOB requires a NON-NEGATIVE offset at or past the end.
            if offset < 0 || (offset as usize) < inner.len() {
                continue;
            }
            // Replacement `T`: ground, NON-EMPTY, head `a`.
            let Some(tlist) = parse_ground_seq_arith(&rargs[2], &seq_binds, &int_binds) else {
                continue;
            };
            let Some(a) = tlist.first().copied() else {
                continue;
            };
            // Whole: ground, NON-EMPTY, head `b`.
            let Some(whole) = parse_ground_seq_arith(whole_side, &seq_binds, &int_binds) else {
                continue;
            };
            let Some(b) = whole.first().copied() else {
                continue;
            };
            // Genuine head mismatch over a single shared element type (needle's
            // inner seq, replacement, and whole all agree).
            if a.lean_ty() != b.lean_ty() || a == b {
                continue;
            }
            let (Some(ty_s), Some(ty_t), Some(ty_w)) =
                (seq_elt_ty(&inner), seq_elt_ty(&tlist), seq_elt_ty(&whole))
            else {
                continue;
            };
            if ty_s != ty_t || ty_t != ty_w {
                continue;
            }
            return Some(render_seq_extract_oob_replace_lean(
                &inner, offset, &tlist, &whole, a, b, ty_t,
            ));
        }
    }
    None
}

/// Render the OOB-`seq.extract` / empty-needle `seq.replace` head-conflict Lean.
/// Grounds `SeqThy.seqExtract_oob` (needle empty for every count) and
/// `SeqThy.seqReplaceEmpty_head` (prepended replacement pins the head) over a
/// universally-quantified haystack `s0` and count `n`.
fn render_seq_extract_oob_replace_lean(
    inner: &[SeqElt],
    offset: i64,
    tlist: &[SeqElt],
    whole: &[SeqElt],
    a: SeqElt,
    b: SeqElt,
    ty: &str,
) -> String {
    let s_lean = seq_list_lean(inner);
    let t_lean = seq_list_lean(tlist);
    let whole_lean = seq_list_lean(whole);
    let a_bare = a.lean_bare();
    let b_bare = b.lean_bare();
    let len = inner.len();
    let hash = fnv_hex(&format!(
        "seqextractoobreplace:{s_lean}:{offset}:{t_lean}:{whole_lean}:{a_bare}:{b_bare}:{ty}"
    ));
    format!(
        r#"import AySoundness.Firewall
import AySoundness.SeqThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — OUT-OF-BOUNDS `seq.extract` feeding an
  empty-needle `seq.replace` head conflict, grounded in the verified
  `SeqThy.seqExtract_oob` and `SeqThy.seqReplaceEmpty_head` (cf. the hand-checked
  witnesses `SeqThy.ex_seqExtract_oob_replace_conflict` /
  `SeqThy.ex_seqExtract_oob_replace_via_principle`). The assertion
  `seq.replace HAYSTACK (seq.extract {s_lean} {offset} N) {t_lean} = {whole_lean}`
  is unsatisfiable: the extract offset `{offset} ≥ len {s_lean} = {len}` makes the
  needle EMPTY for every count `N` (`seqExtract_oob`), and an SMT `seq.replace`
  with an empty needle PREPENDS the replacement, so the result is
  `{t_lean} ++ HAYSTACK` whose head is pinned by `{t_lean}`'s head `{a_bare}` for
  EVERY haystack (`seqReplaceEmpty_head`); but the whole `{whole_lean}` has head
  `{b_bare}`, and `{a_bare} ≠ {b_bare}`. Reconstructed from the frontend parsed
  ASSERTIONS (ay reduces seq.extract / seq.replace eagerly). The haystack `s0` and
  count `n` are quantified UNIVERSALLY, so the certificate refutes the assertion
  for every value of the concrete haystack/count; `{s_lean}`, `{t_lean}`,
  `{whole_lean}` are ground concrete lists, so every side condition closes by
  `decide`. Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.SeqExtractOobReplace_{hash}
open AySoundness

/-- The needle `seq.extract {s_lean} {offset} n` is OUT-OF-BOUNDS (offset
    `{offset} ≥ len {s_lean} = {len}`), hence EMPTY for every count `n`. -/
theorem needle_empty (n : Nat) :
    SeqThy.seqExtract (({s_lean}) : SeqThy.Seq {ty}) {offset} n = ([] : SeqThy.Seq {ty}) :=
  SeqThy.seqExtract_oob (({s_lean}) : SeqThy.Seq {ty}) {offset} n (by decide)

/-- No haystack `s0` makes `seq.replace s0 [] {t_lean} = {whole_lean}`: the empty
    needle prepends `{t_lean}` (head `{a_bare}`), but the whole's head is
    `{b_bare} ≠ {a_bare}`. Combined with `needle_empty`, this refutes the assertion
    for every haystack and every count. -/
theorem no_model (s0 : SeqThy.Seq {ty}) :
    ¬ (SeqThy.seqReplaceEmpty s0 (({t_lean}) : SeqThy.Seq {ty})
        = (({whole_lean}) : SeqThy.Seq {ty})) := by
  intro h
  have hhead :=
    SeqThy.seqReplaceEmpty_head s0 (({t_lean}) : SeqThy.Seq {ty}) ({a_bare}) (by decide)
  rw [h] at hhead
  exact absurd hhead (by decide)

end AySoundness.Emitted.SeqExtractOobReplace_{hash}
"#,
    )
}

/// The `(S, I)` operands of a `(seq.nth S I)` read, else `None`.
fn match_seq_nth(t: &PTerm) -> Option<(&PTerm, &PTerm)> {
    match t {
        PTerm::App(op, a) if op == "seq.nth" && a.len() == 2 => Some((&a[0], &a[1])),
        _ => None,
    }
}

/// Emit a verified-firewall Lean proof for a GROUND `seq.nth` + LIA conflict found
/// among the PARSED assertions (possibly inside an `and`): a numeric comparison
/// `(OP … (seq.nth S I) …)` where `S` resolves to a ground sequence, `I` to a
/// pinned in-range index, the other operand constant-folds, and the comparison is
/// FALSE once the read is bound to `S[I]`.
///
/// The total `seq.nth` is modelled by the verified `SeqThy.nthD` bridge; for an
/// in-range read it equals the element, handing a concrete integer to LIA. The
/// whole comparison is ground-false, so it is closed by `decide` over `Val =
/// Unit`. `None` unless a genuinely-false ground comparison over an in-range read
/// is found.
pub(crate) fn emit_seq_nth_ground_lia_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    let int_binds = collect_int_binds(parsed);
    let seq_binds = collect_seq_binds(parsed);
    let mut conjuncts: Vec<&PTerm> = Vec::new();
    for a in parsed {
        flatten_and(a, &mut conjuncts);
    }
    for c in conjuncts {
        let PTerm::App(op, args) = c else { continue };
        let lean_op = match op.as_str() {
            ">=" => "≥",
            "<=" => "≤",
            ">" => ">",
            "<" => "<",
            "=" => "=",
            _ => continue,
        };
        if args.len() != 2 {
            continue;
        }
        // `read_left`: the `seq.nth` read is the FIRST operand.
        for read_left in [true, false] {
            let (read_t, const_t) = if read_left {
                (&args[0], &args[1])
            } else {
                (&args[1], &args[0])
            };
            let Some((s, i)) = match_seq_nth(read_t) else {
                continue;
            };
            let Some(list) = parse_ground_seq(s, &seq_binds) else {
                continue;
            };
            let Some(idx) = resolve_index(i, &int_binds) else {
                continue;
            };
            let Some(SeqElt::Int(rv)) = eval_read(&list, idx) else {
                continue;
            };
            let Some(cv) = fold_int(const_t, &int_binds) else {
                continue;
            };
            let (lv, rhv) = if read_left { (rv, cv) } else { (cv, rv) };
            let holds = match op.as_str() {
                ">=" => lv >= rhv,
                "<=" => lv <= rhv,
                ">" => lv > rhv,
                "<" => lv < rhv,
                "=" => lv == rhv,
                _ => continue,
            };
            // Only a genuine conflict (a FALSE ground comparison) qualifies.
            if holds {
                continue;
            }
            return Some(render_seq_nth_lia_lean(cv, lean_op, read_left, &list, idx));
        }
    }
    None
}

/// Render the ground `seq.nth` + LIA firewall Lean. The total read is
/// `SeqThy.nthD` (verified bridge); the ground-false comparison closes by
/// `decide` over `Val = Unit`.
fn render_seq_nth_lia_lean(
    c: i64,
    lean_op: &str,
    read_left: bool,
    list: &[SeqElt],
    idx: i64,
) -> String {
    let hash = fnv_hex(&format!(
        "seqnthlia:{c}:{lean_op}:{read_left}:{}:{idx}",
        seq_list_lean(list)
    ));
    let list_lean = seq_list_lean(list);
    let nthd = format!("SeqThy.nthD (({list_lean}) : SeqThy.Seq Int) {idx} (0 : Int)");
    let cexpr = format!("({c} : Int)");
    let (lhs, rhs) = if read_left {
        (nthd, cexpr)
    } else {
        (cexpr, nthd)
    };
    format!(
        r#"import AySoundness.Firewall
import AySoundness.SeqThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — GROUND `seq.nth` + LIA conflict grounded
  in the verified `firewall_combined_unsat`. A numeric comparison over the total
  read `seq.nth s i` is unsatisfiable once the in-range read is bound to `s[i]`:
  the verified `SeqThy.nthD` bridge evaluates the total read to the concrete
  element, and the resulting all-constant comparison is FALSE in LIA (mirrors
  `SeqThy.ex_seq_nth_ground_lia_conflict`). Reconstructed from the frontend parsed
  ASSERTIONS (ay refutes eagerly; the irrelevant conjuncts are red herrings).
  Model: `Val = Unit` (fully ground). Pure Lean 4 core; axioms ⊆ {{propext,
  Quot.sound}}.
-/
namespace AySoundness.Emitted.SeqNthLia_{hash}
open AySoundness

abbrev Val := Unit

/-- Atom `1 ↦` the asserted (ground-false) `seq.nth` comparison. -/
def atomVal (_m : Val) (k : Nat) : Bool :=
  match k with
  | 1 => decide ({lhs} {lean_op} {rhs})
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have ha : atomVal m 1 = false := by cases m <;> decide
  simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- The ground `seq.nth` comparison is false — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.SeqNthLia_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a BOUNDED 2-way `seq.at`-vs-`ite`
/// conflict found among the PARSED assertions: `(= (seq.at S I) (ite C TB FB))`
/// (either operand order) where `S` resolves to a ground sequence with an in-range
/// read, and BOTH ground `ite` branches `TB`/`FB` differ from the read.
///
/// The abstract `ite` condition `C` is modelled as a free `Bool` — it is never
/// evaluated (so a red-herring OOB `seq.nth` inside `C` is absorbed). The
/// certificate case-splits on that `Bool`: both branches are ground-false against
/// the verified `SeqThy.seqAt` read (true-branch element/length mismatch,
/// false-branch length mismatch), closed by `cases m <;> decide`. Grounded through
/// `firewall_combined_unsat` over `Val = Bool`. `None` unless both branches are
/// genuine conflicts.
pub(crate) fn emit_seq_at_ite_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    let int_binds = collect_int_binds(parsed);
    let seq_binds = collect_seq_binds(parsed);
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        for (p, q) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            // p = (seq.at S I)
            let PTerm::App(aop, aargs) = p else { continue };
            if aop != "seq.at" || aargs.len() != 2 {
                continue;
            }
            // q = (ite C TB FB)
            let PTerm::App(iop, iargs) = q else { continue };
            if iop != "ite" || iargs.len() != 3 {
                continue;
            }
            let Some(list) = parse_ground_seq(&aargs[0], &seq_binds) else {
                continue;
            };
            let Some(idx) = resolve_index(&aargs[1], &int_binds) else {
                continue;
            };
            let Some(read) = eval_read(&list, idx) else {
                continue;
            };
            let Some(tb) = parse_ground_seq(&iargs[1], &seq_binds) else {
                continue;
            };
            let Some(fb) = parse_ground_seq(&iargs[2], &seq_binds) else {
                continue;
            };
            // The read is the length-1 singleton `[read]`.
            let read_seq = vec![read];
            // Both branches must genuinely conflict with the read.
            if read_seq == tb || read_seq == fb {
                continue;
            }
            let Some(ty) = seq_elt_ty(&list) else {
                continue;
            };
            // Branch element types (where present) must match the read's.
            if !tb.iter().chain(fb.iter()).all(|e| e.lean_ty() == ty) {
                continue;
            }
            return Some(render_seq_at_ite_lean(&list, idx, &tb, &fb, ty));
        }
    }
    None
}

/// Render the bounded 2-way `seq.at`-vs-`ite` firewall Lean. The abstract
/// condition is a free `Bool m`; both branches close by `cases m <;> decide` over
/// the verified `SeqThy.seqAt` read model.
fn render_seq_at_ite_lean(
    list: &[SeqElt],
    idx: i64,
    tb: &[SeqElt],
    fb: &[SeqElt],
    ty: &str,
) -> String {
    let hash = fnv_hex(&format!(
        "seqatite:{}:{idx}:{}:{}",
        seq_list_lean(list),
        seq_list_lean(tb),
        seq_list_lean(fb)
    ));
    let read_lean = seq_list_lean(list);
    let tb_lean = seq_list_lean(tb);
    let fb_lean = seq_list_lean(fb);
    format!(
        r#"import AySoundness.Firewall
import AySoundness.SeqThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — BOUNDED 2-way `seq.at`-vs-`ite` conflict
  grounded in the verified `firewall_combined_unsat`. The literal
  `seq.at s i = ite c TB FB` is unsatisfiable REGARDLESS of the condition `c`: the
  read `seq.at s i` is the fixed length-1 singleton `s[i]`, and BOTH ground
  branches differ from it (true-branch element/length mismatch, false-branch
  length mismatch — cf. `SeqThy.ex_seqat_ite_true_conflict` /
  `ex_seqat_ite_false_conflict`). The abstract condition (a red-herring OOB
  `seq.nth`) is modelled as a free `Bool` and NEVER evaluated; the proof
  case-splits on it (`cases m <;> decide`). Reconstructed from the frontend parsed
  ASSERTIONS (ay reduces seq.at eagerly). Model: `Val = Bool` (the condition).
  Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.SeqAtIte_{hash}
open AySoundness

abbrev Val := Bool

/-- Atom `1 ↦ seq.at s i = (if c then TB else FB)` with `c := m`. -/
def atomVal (m : Val) (k : Nat) : Bool :=
  match k with
  | 1 => decide (SeqThy.seqAt (({read_lean}) : SeqThy.Seq {ty}) {idx} = (bif m then (({tb_lean}) : SeqThy.Seq {ty}) else (({fb_lean}) : SeqThy.Seq {ty})))
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have ha : atomVal m 1 = false := by cases m <;> decide
  simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- Neither `ite` branch matches the `seq.at` read, for any condition — via the
    firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.SeqAtIte_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a binary datatype-distinctness lemma
/// `(not (= c C1)) (not (= c C2))`. Returns `None` if the clause is not that
/// shape or the constructors are not registered distinct constructors of one
/// datatype.
pub(crate) fn emit_datatype_distinct_firewall_lean(
    terms: &TermStore,
    decls: DatatypeDecls<'_>,
    lemma_clause: &[TermId],
) -> Option<String> {
    let literals = flatten_or(terms, lemma_clause);
    if literals.len() != 2 {
        return None;
    }
    let (a1, b1) = negated_equality(terms, literals[0])?;
    let (a2, b2) = negated_equality(terms, literals[1])?;
    // Identify the shared term `c` and the two constructor operands.
    let (c, c1, c2) = shared_and_others(a1, b1, a2, b2)?;
    let _ = c; // the shared term's identity is irrelevant; only the ctors matter
    let ctor1 = constructor_name(terms, c1)?;
    let ctor2 = constructor_name(terms, c2)?;
    if ctor1 == ctor2 {
        return None;
    }
    let (dt1, all1) = datatype_of(decls, &ctor1)?;
    let (dt2, _) = datatype_of(decls, &ctor2)?;
    if dt1 != dt2 {
        return None;
    }
    Some(render_lean(dt1, all1, &ctor1, &ctor2))
}

/// Emit a verified-firewall Lean proof for a linear-arithmetic conflict lemma
/// whose literals are all negated comparisons — `(not (<= x 1)) (not (>= x 2))`
/// (`:rule la_generic`). The minimal firewall instance asserts each comparison
/// and the lemma refutes their conjunction; validity is discharged by `omega`
/// over a `Nat → Int` valuation model. Returns `None` if any literal is not a
/// negated linear comparison this translator handles.
pub(crate) fn emit_lia_firewall_lean(terms: &TermStore, lemma_clause: &[TermId]) -> Option<String> {
    let literals = flatten_or(terms, lemma_clause);
    if literals.len() < 2 {
        return None;
    }
    let mut vars: Vec<(String, u32)> = Vec::new();
    // (rendered comparison, polarity-in-lemma: true = positive). Mixed polarity
    // is supported (e.g. antisymmetry `¬(x≤y) ∨ ¬(y≤x) ∨ (x=y)`), not just
    // all-negated bound conflicts.
    let mut atoms: Vec<(String, bool)> = Vec::new();
    for &lit in &literals {
        let (comp_term, positive) = match terms.get(lit) {
            TermData::Not(inner) => (*inner, false),
            _ => (lit, true),
        };
        atoms.push((render_comparison(terms, comp_term, &mut vars)?, positive));
    }
    // SUBSET-REFUTATION FAITHFULNESS. `original` asserts one unit clause per
    // rendered atom and nothing else, so the artifact refutes a SUBSET of the
    // query's atoms. That is sound only while the rendering is faithful: every
    // `(m i)` must denote one distinct SMT variable and no two distinct
    // variables may share an index. `render_int` keys the map on the term
    // store's unique `(name, id)` variable identity, which makes the map
    // injective by construction; this check witnesses the remaining half — that
    // no atom mentions an index outside the recorded map. Fail closed.
    if !lia_atom_indices_are_in_range(atoms.iter().map(|(a, _)| a.as_str()), vars.len()) {
        return None;
    }
    Some(render_lia_lean(&atoms))
}

/// Witness that every `(m i)` valuation index occurring in the rendered atoms
/// was actually allocated in the emitter's variable map (`i < vars`).
///
/// Together with the map's injectivity this is the faithfulness side-condition
/// of the SUBSET refutation the LIA firewall emits: `original` asserts exactly
/// the rendered atoms, so an index that escaped the map — or two variables
/// sharing one — would let a kernel-checked artifact refute a system that is
/// not a subset of the query's.
fn lia_atom_indices_are_in_range<'a>(
    atoms: impl IntoIterator<Item = &'a str>,
    vars: usize,
) -> bool {
    atoms.into_iter().all(|atom| {
        atom.match_indices("(m ").all(|(at, _)| {
            let rest = &atom[at + 3..];
            let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
            match digits.parse::<usize>() {
                Ok(idx) => idx < vars,
                Err(_) => false,
            }
        })
    })
}

/// Widest clause for which the historical `2ⁿ`-leaf `by_cases … <;> simp <;>
/// omega` product is still attempted FIRST inside the `first` combinator.
///
/// Ordering matters because Lean's heartbeat budget is per-DECLARATION: a
/// sibling alternative that exhausts it aborts the whole declaration, and
/// `first` cannot recover (`Lean.Core`'s `withOptions` refreshes `maxRecDepth`
/// from the options but not `maxHeartbeats`, so a `set_option maxHeartbeats … in`
/// wrapper around one alternative buys it nothing). Measured on the 142
/// LIA/general firewall artifacts emitted across `benchmarks/smt`: the case-split
/// product closes at widths up to 6 and, from width 11 on, burns the entire
/// default budget before failing. Keeping it first at or below this bound
/// preserves every artifact that closes today — including the ones that close
/// CONSTRUCTIVELY, with axioms ⊆ {propext, Quot.sound} — byte for byte; above
/// it the product is unaffordable anyway, so the linear script leads.
const MAX_CASE_SPLIT_FIRST_ATOMS: usize = 8;

/// Linear alternative for a `clauseSat` goal that has already been unfolded by
/// `simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]`.
///
/// It finishes the `Bool`→`Prop` normalisation the unfolding leaves behind
/// (`decide`/`ite`/`Bool.or` scaffolding around the literal indices) and hands
/// ONE linear disjunction to `omega`, in `O(n)` rather than the `2ⁿ` leaves of
/// the case-split product.
///
/// This is what the case-split script cannot do on these inputs, and the reason
/// is tactic HYGIENE rather than any missing theory: `simp [h₁, …, hₙ]` takes an
/// equality hypothesis such as `h₃ : 1 = m 4 + m 1` as a left-to-right rewrite
/// rule and rewrites the literal INDICES `1`, `-1`, `2`, … inside the still-folded
/// `atomVal` match, turning the goal into a shape no arithmetic tactic can close.
const CLAUSE_LINEAR_ALTERNATIVE: &str = "simp only [gt_iff_lt, Int.reduceNeg, Int.reduceLT, Int.reduceGT,\n         Int.reduceToNat, reduceIte, Bool.not_eq_eq_eq_not, Bool.not_true,\n         Bool.or_eq_true, decide_eq_false_iff_not, decide_eq_true_eq,\n         Bool.false_or, Bool.or_false]\n       omega";

/// Combine the historical case-split script with [`CLAUSE_LINEAR_ALTERNATIVE`]
/// under Lean's `first` TACTIC combinator.
///
/// `first` is pure proof SEARCH: whichever alternative succeeds still produces a
/// term the kernel checks in full, so this cannot weaken soundness — it can only
/// turn a previously-unclosable emission into a checked one, or leave it failing
/// (fail-closed). `case_split` stays FIRST while it is affordable, so artifacts
/// that already close keep their exact proof term and axiom basis; see
/// [`MAX_CASE_SPLIT_FIRST_ATOMS`].
fn clause_tactic(case_split: &str, atoms: usize) -> String {
    let linear = CLAUSE_LINEAR_ALTERNATIVE;
    if atoms <= MAX_CASE_SPLIT_FIRST_ATOMS {
        format!("first\n    | ({case_split})\n    | ({linear})")
    } else {
        format!("first\n    | ({linear})\n    | ({case_split})")
    }
}

/// Lean's default `maxRecDepth` (512) is sized for hand-written proofs; a
/// `clauseSat` goal over hundreds of literals unfolds into a term far deeper
/// than that, and the emitted artifact fails for want of stack frames rather
/// than for want of a proof. Scale that guard — and ONLY that guard — with the
/// rendered clause size.
///
/// `maxHeartbeats` is deliberately left at the Lean default. These artifacts are
/// attacker/input-amplifiable through proof size, so the wall-clock guard must
/// stay in force; `maxHeartbeats 0` is never emitted.
fn scaled_max_rec_depth(atoms: usize) -> usize {
    512usize
        .saturating_add(atoms.saturating_mul(256))
        .clamp(4_096, 262_144)
}

fn render_lia_lean(atoms: &[(String, bool)]) -> String {
    let n = atoms.len();
    let hash = fnv_hex(
        &atoms
            .iter()
            .map(|(a, p)| format!("{p}:{a}"))
            .collect::<Vec<_>>()
            .join("\u{1}"),
    );
    let arms = atoms
        .iter()
        .enumerate()
        .map(|(i, (a, _))| format!("  | {} => decide ({a})", i + 1))
        .collect::<Vec<_>>()
        .join("\n");
    // Original asserts the NEGATION of each lemma literal.
    let orig = atoms
        .iter()
        .enumerate()
        .map(|(i, (_, pos))| {
            let lit = if *pos {
                format!("-{}", i + 1)
            } else {
                format!("{}", i + 1)
            };
            format!("({}, [{lit}])", i + 1)
        })
        .collect::<Vec<_>>()
        .join(", ");
    // Lemma clause: signed per polarity (named `neg` for the format template).
    let neg = atoms
        .iter()
        .enumerate()
        .map(|(i, (_, pos))| {
            if *pos {
                format!("{}", i + 1)
            } else {
                format!("-{}", i + 1)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = n + 1;
    let proof_hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let bycases = atoms
        .iter()
        .enumerate()
        .map(|(i, (a, _))| format!("by_cases h{} : {a}", i + 1))
        .collect::<Vec<_>>()
        .join(" <;> ");
    let hs = (1..=n)
        .map(|i| format!("h{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let tactic = clause_tactic(&format!("{bycases} <;> simp [{hs}] <;> omega"), n);
    let rec_depth = scaled_max_rec_depth(n);
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — linear-arithmetic conflict grounded in
  the verified `firewall_combined_unsat`. The asserted comparisons are jointly
  unsatisfiable; premise (a) is the resolution (`lratCheck` by `decide`),
  premise (b) is the `la_generic` lemma holding in every valuation, discharged by
  the `first` combinator: the `2ⁿ`-leaf case-split product where that is
  affordable, else ONE linear `omega` pass. Model: a valuation `Nat → Int`.
  Pure Lean 4 core.
-/
set_option linter.unusedSimpArgs false
set_option maxRecDepth {rec_depth}

namespace AySoundness.Emitted.Lia_{hash}
open AySoundness

abbrev Val := Nat → Int

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{neg}])]
def proof    : List (Cid × Clause × List Int) := [({proof2}, [], [{proof_hints}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{neg}] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  {tactic}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No valuation satisfies all the asserted comparisons — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.Lia_{hash}
"#,
        hash = hash,
        arms = arms,
        orig = orig,
        neg = neg,
        lemma_id = lemma_id,
        proof2 = lemma_id + 1,
        proof_hints = proof_hints,
        tactic = tactic,
        rec_depth = rec_depth,
    )
}

/// Emit a verified-firewall Lean proof for an EUF equality-transitivity conflict
/// lemma `(not (= a b)) (not (= b c)) (= a c)` (`:rule eq_transitive`) — a
/// disjunction of equality literals (mixed polarity) over function-FREE terms
/// (uninterpreted constants/variables). The minimal firewall instance asserts
/// the negation of each lemma literal; validity is discharged by `omega` over a
/// `Nat → Nat` valuation (faithful for equality-only reasoning). Returns `None`
/// if any literal is not a function-free equality.
pub(crate) fn emit_euf_firewall_lean(terms: &TermStore, lemma_clause: &[TermId]) -> Option<String> {
    let literals = flatten_or(terms, lemma_clause);
    if literals.len() < 2 {
        return None;
    }
    let mut consts: Vec<String> = Vec::new();
    // (rendered equality prop, polarity-in-lemma: true = positive)
    let mut atoms: Vec<(String, bool)> = Vec::new();
    for &lit in &literals {
        let (eq_term, positive) = match terms.get(lit) {
            TermData::Not(inner) => (*inner, false),
            _ => (lit, true),
        };
        let (a, b) = equality_sides(terms, eq_term)?;
        let ra = render_const(terms, a, &mut consts)?;
        let rb = render_const(terms, b, &mut consts)?;
        atoms.push((format!("{ra} = {rb}"), positive));
    }
    Some(render_euf_lean(&atoms))
}

fn render_euf_lean(atoms: &[(String, bool)]) -> String {
    let n = atoms.len();
    let hash = fnv_hex(
        &atoms
            .iter()
            .map(|(p, b)| format!("{b}:{p}"))
            .collect::<Vec<_>>()
            .join("\u{1}"),
    );
    let arms = atoms
        .iter()
        .enumerate()
        .map(|(i, (p, _))| format!("  | {} => decide ({p})", i + 1))
        .collect::<Vec<_>>()
        .join("\n");
    // Original asserts the NEGATION of each lemma literal.
    let orig = atoms
        .iter()
        .enumerate()
        .map(|(i, (_, pos))| {
            let lit = if *pos {
                format!("-{}", i + 1)
            } else {
                format!("{}", i + 1)
            };
            format!("({}, [{lit}])", i + 1)
        })
        .collect::<Vec<_>>()
        .join(", ");
    // Lemma clause: signed per polarity.
    let lemma_lits = atoms
        .iter()
        .enumerate()
        .map(|(i, (_, pos))| {
            if *pos {
                format!("{}", i + 1)
            } else {
                format!("-{}", i + 1)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = n + 1;
    let proof_hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let bycases = atoms
        .iter()
        .enumerate()
        .map(|(i, (p, _))| format!("by_cases h{} : {p}", i + 1))
        .collect::<Vec<_>>()
        .join(" <;> ");
    let hs = (1..=n)
        .map(|i| format!("h{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — EUF equality-transitivity conflict
  grounded in the verified `firewall_combined_unsat`. Premise (a): resolution
  (`lratCheck` by `decide`). Premise (b): the `eq_transitive` lemma holds in
  every valuation, discharged by `omega`. Model: a valuation `Nat → Nat`
  (faithful for equality-only EUF). Pure Lean 4 core.
-/
namespace AySoundness.Emitted.Euf_{hash}
open AySoundness

abbrev Val := Nat → Nat

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof2}, [], [{proof_hints}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  {bycases} <;> simp [{hs}] <;> omega

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No valuation satisfies the asserted (dis)equalities — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.Euf_{hash}
"#,
        hash = hash,
        arms = arms,
        orig = orig,
        lemma_lits = lemma_lits,
        lemma_id = lemma_id,
        proof2 = lemma_id + 1,
        proof_hints = proof_hints,
        bycases = bycases,
        hs = hs,
    )
}

/// Emit ONE firewall-grounded Lean file that grounds the ENTIRE proof DAG in the
/// verified `AySoundness.firewall_combined_unsat`, over a single shared integer
/// valuation `Val = Nat → Int`.
///
/// Unlike the single-clause per-kind emitters above (each grounds ONE theory
/// lemma in isolation), this is the GENERAL, whole-DAG emitter: it threads ONE
/// global atom table and ONE shared model through EVERY clause of the proof, so
/// a multi-step refutation — several `Assume` inputs (→ `original`), several
/// arithmetic/equality `TheoryLemma`s (→ `lemmas`), and a resolution DAG to the
/// empty clause (→ the RUP `proof`) — is grounded as a single self-contained
/// certificate. This is the principled "compose the per-theory recipes under one
/// Nelson–Oppen model" shape of `AySoundness.CombinedExample` /
/// `AySoundness.GeneralFirewallPoc`.
///
/// Renderable set (fails closed — returns `None` — otherwise): every theory
/// lemma is an arithmetic comparison / equality lemma (`LraFarkas` /
/// `LiaGeneric` / function-free `EufTransitive`); every atom across the whole
/// proof is a linear comparison or equality renderable over `Nat → Int`; every
/// derived step is resolution-family (`resolution` / `th_resolution` /
/// `contraction`) so the refutation is purely propositional over
/// `original ++ lemmas` and `lratCheck`'s RUP re-derives the empty clause; and a
/// terminal empty clause exists.
///
/// Soundness of the single integer model for BOTH theories: linear-arithmetic
/// variables are genuinely `Int`; modeling uninterpreted constants as integers
/// is sound for equality-only reasoning because any equivalence relation
/// realizable in an uninterpreted sort is realizable over the (infinite)
/// integers — so "UNSAT in every `Nat → Int` valuation" implies UNSAT in the
/// original combined semantics. Each lemma's validity in every integer valuation
/// is premise (b), discharged uniformly by `omega`. A shared symbol that appears
/// in both an arithmetic atom and an equality atom maps to the SAME valuation
/// index in both (the Nelson–Oppen interface), since `render_comparison` keys by
/// SMT name into one `vars` table.
pub(crate) fn emit_general_firewall_lean(
    terms: &TermStore,
    proof: &ay_core::Proof,
) -> Option<String> {
    use ay_core::{AletheRule, ProofStep, TheoryLemmaKind as K};

    // --- Walk the DAG: collect Assume clauses + arithmetic/equality lemma
    //     clauses, require a terminal empty clause, and require every derived
    //     step to be resolution-family (so the refutation is purely
    //     propositional over `original ++ lemmas`). ---
    let mut assume_lits: Vec<TermId> = Vec::new(); // each Assume is one literal
    let mut lemma_clauses: Vec<(Vec<TermId>, K)> = Vec::new();
    let mut has_empty = false;
    for step in &proof.steps {
        match step {
            ProofStep::Assume(t) => assume_lits.push(*t),
            ProofStep::TheoryLemma { kind, clause, .. } => match kind {
                K::LraFarkas
                | K::LiaGeneric
                | K::EufTransitive
                | K::EufCongruent
                | K::EufCongruentPred => {
                    lemma_clauses.push((clause.clone(), *kind));
                }
                // A lemma outside the arithmetic / equality / congruence set is
                // not renderable here.
                _ => return None,
            },
            ProofStep::Resolution { clause, .. } => {
                if clause.is_empty() {
                    has_empty = true;
                }
            }
            ProofStep::Step { rule, clause, .. } => {
                // Only purely-propositional resolution-family steps keep the
                // refutation inside `original ++ lemmas`; a creative rule
                // introducing new atoms could make the RUP certificate fail to
                // close, so decline rather than emit a non-building file.
                if !matches!(
                    rule,
                    AletheRule::Resolution | AletheRule::ThResolution | AletheRule::Contraction
                ) {
                    return None;
                }
                if clause.is_empty() {
                    has_empty = true;
                }
            }
            // Subproofs (nested anchors) are outside this flat-DAG shape.
            ProofStep::Anchor { .. } => return None,
            // `ProofStep` is `#[non_exhaustive]`; an unknown future step kind is
            // not renderable — fail closed.
            _ => return None,
        }
    }
    if !has_empty || assume_lits.is_empty() || lemma_clauses.is_empty() {
        return None;
    }

    // --- Global atom table. Assign Nat ids by first occurrence across the WHOLE
    //     proof: originals first (in Assume order), then lemmas (in lemma order).
    //     `atom_is_fn[i]` records whether atom `i` is a congruence CONCLUSION (a
    //     function- or predicate-application atom) — used to pick the by_cases
    //     set. `atom_is_bool[i]` records whether the atom renders as a raw `Bool`
    //     (a predicate application) vs a `decide`-wrapped `Prop`. Atoms render to
    //     PLACEHOLDER tokens (scalar / function-family / predicate-family); the
    //     `funcs`/`preds` tables are populated on demand and the model layout is
    //     finalised AFTER interning (so a proof with ≥2 functions, ≥2 predicates,
    //     or a function/predicate MIX is supported via Nat-indexed families). ---
    let mut atom_ids: Vec<TermId> = Vec::new();
    let mut atom_render: Vec<String> = Vec::new();
    let mut atom_is_fn: Vec<bool> = Vec::new();
    let mut atom_is_bool: Vec<bool> = Vec::new();
    let mut vars: Vec<String> = Vec::new();
    let mut funcs: Vec<String> = Vec::new(); // uninterpreted function family (m.2 / m.2.1)
    let mut preds: Vec<String> = Vec::new(); // uninterpreted predicate family (m.2 / m.2.2)

    let mut original: Vec<Vec<i64>> = Vec::with_capacity(assume_lits.len());
    for &lit in &assume_lits {
        let signed = general_clause_lits(
            terms,
            &[lit],
            &mut atom_ids,
            &mut atom_render,
            &mut atom_is_fn,
            &mut atom_is_bool,
            &mut vars,
            &mut funcs,
            &mut preds,
        )?;
        if signed.is_empty() {
            return None;
        }
        original.push(signed);
    }
    let mut lemmas: Vec<Vec<i64>> = Vec::with_capacity(lemma_clauses.len());
    for (cl, _k) in &lemma_clauses {
        let signed = general_clause_lits(
            terms,
            cl,
            &mut atom_ids,
            &mut atom_render,
            &mut atom_is_fn,
            &mut atom_is_bool,
            &mut vars,
            &mut funcs,
            &mut preds,
        )?;
        if signed.len() < 2 {
            // A theory lemma should be a genuine disjunction; a unit "lemma" is
            // not the comparison/equality conflict shape this emitter grounds.
            return None;
        }
        lemmas.push(signed);
    }

    // Finalise the model layout now that every atom is interned. A congruence /
    // predicate lemma kind that produced no function/predicate symbol means the
    // atom shape couldn't be represented — fail closed.
    let has_fn = !funcs.is_empty();
    let has_pred = !preds.is_empty();
    if lemma_clauses
        .iter()
        .any(|(_, k)| matches!(k, K::EufCongruent | K::EufCongruentPred))
        && !has_fn
        && !has_pred
    {
        return None;
    }
    // Resolve the placeholder tokens into final model projections.
    let scalar_proj = if has_fn || has_pred { "m.1" } else { "m" };
    let (val_ty, fn_proj, pred_proj) = match (has_fn, has_pred) {
        (false, false) => ("Nat → Int", "", ""),
        (true, false) => ("(Nat → Int) × (Nat → Int → Int)", "m.2", ""),
        (false, true) => ("(Nat → Int) × (Nat → Int → Bool)", "", "m.2"),
        (true, true) => (
            "(Nat → Int) × (Nat → Int → Int) × (Nat → Int → Bool)",
            "m.2.1",
            "m.2.2",
        ),
    };
    let atom_render: Vec<String> = atom_render
        .iter()
        .map(|s| resolve_placeholders(s, scalar_proj, fn_proj, pred_proj))
        .collect();

    // --- Render the Lean file. ---
    let a = original.len();
    let l = lemmas.len();

    let fmt_clause = |lits: &[i64]| {
        lits.iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    };

    // atomVal arms (one per global atom id, contiguous 1..=n). A predicate-
    // application atom is already `Bool`, so it is rendered raw; every other atom
    // is a `Prop` rendered under `decide`.
    let arms = atom_render
        .iter()
        .enumerate()
        .map(|(i, comp)| {
            if atom_is_bool[i] {
                format!("  | {} => {comp}", i + 1)
            } else {
                format!("  | {} => decide ({comp})", i + 1)
            }
        })
        .collect::<Vec<_>>()
        .join("\n");

    let original_src = original
        .iter()
        .enumerate()
        .map(|(i, lits)| format!("({}, [{}])", i + 1, fmt_clause(lits)))
        .collect::<Vec<_>>()
        .join(", ");
    let lemmas_src = lemmas
        .iter()
        .enumerate()
        .map(|(i, lits)| format!("({}, [{}])", a + i + 1, fmt_clause(lits)))
        .collect::<Vec<_>>()
        .join(", ");
    let proof_id = a + l + 1;
    let proof_hints = (1..=a + l)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    // Per-lemma validity theorems + the dispatching membership split. The tactic
    // is chosen per lemma by its atom shape:
    //   - CONGRUENCE shape (has BOTH a congruence-conclusion atom `atom_is_fn`
    //     AND a non-conclusion argument-equality atom): `by_cases` only on the
    //     argument-equality atoms, then `simp` rewrites the family applications
    //     (no `omega` — the rewrite makes the conclusion `rfl`);
    //   - otherwise (pure arithmetic/equality, OR a transitivity lemma whose
    //     atoms are ALL function-application equalities between Int results):
    //     `by_cases` on every atom then `simp <;> omega` (omega treats each
    //     opaque `(m.2 k) …` Int result as a free variable and discharges the
    //     (dis)equality reasoning).
    let mut lemma_thms = String::new();
    let mut dispatch_bullets = String::new();
    let mut max_lemma_atoms = 0usize;
    for (i, lits) in lemmas.iter().enumerate() {
        let cid = a + i + 1;
        let id_of = |x: &i64| x.unsigned_abs() as usize;
        // A PREDICATE-congruence lemma has predicate (raw-`Bool`) conclusion
        // atoms; by_cases on its NON-predicate atom(s) — the argument equality,
        // which may itself be a function-application equality — then `simp`. A
        // FUNCTION-congruence lemma has both a congruence-conclusion atom
        // (`atom_is_fn`) and a non-conclusion argument-equality atom; by_cases on
        // the non-conclusion atoms then `simp`. Everything else (pure arithmetic,
        // or transitivity whose atoms are ALL Int function-result equalities) —
        // by_cases on every atom then `simp <;> omega`.
        let has_pred_atom = lits.iter().any(|x| atom_is_bool[id_of(x) - 1]);
        let has_special = lits.iter().any(|x| atom_is_fn[id_of(x) - 1]);
        let has_nonspecial = lits.iter().any(|x| !atom_is_fn[id_of(x) - 1]);
        let congruence_shape = has_special && has_nonspecial;
        let use_simp_only = has_pred_atom || congruence_shape;
        let mut seen: Vec<usize> = Vec::new();
        for x in lits {
            let id = id_of(x);
            let skip = if has_pred_atom {
                atom_is_bool[id - 1] // skip predicate conclusions
            } else if congruence_shape {
                atom_is_fn[id - 1] // skip function-application conclusions
            } else {
                false
            };
            if skip {
                continue;
            }
            if !seen.contains(&id) {
                seen.push(id);
            }
        }
        if seen.is_empty() {
            return None; // nothing to case-split on — not a groundable shape
        }
        let bycases = seen
            .iter()
            .map(|&id| format!("by_cases h{} : {}", id, atom_render[id - 1]))
            .collect::<Vec<_>>()
            .join(" <;> ");
        let hs = seen
            .iter()
            .map(|&id| format!("h{id}"))
            .collect::<Vec<_>>()
            .join(", ");
        let lits_src = fmt_clause(lits);
        let close = if use_simp_only {
            format!("<;> simp [{hs}]")
        } else {
            format!("<;> simp [{hs}] <;> omega")
        };
        // The case-split product stays the FIRST alternative here (it is the one
        // that closes the congruence shapes, and — measured — every general
        // artifact that closes today does so through it, several with axioms
        // ⊆ {propext, Quot.sound}); the linear script only runs when it fails.
        // Above `MAX_CASE_SPLIT_FIRST_ATOMS` the product cannot finish inside
        // Lean's per-declaration heartbeat budget at all, and exhausting it would
        // abort the declaration before the fallback ever ran, so the order flips.
        let tactic = clause_tactic(&format!("{bycases} {close}"), seen.len());
        max_lemma_atoms = max_lemma_atoms.max(seen.len());
        lemma_thms.push_str(&format!(
            "theorem lemma_{cid}_valid (m : Val) : clauseSat (atomVal m) [{lits_src}] = true := by\n  \
             simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]\n  \
             {tactic}\n\n"
        ));
        dispatch_bullets.push_str(&format!("  · exact lemma_{cid}_valid m\n"));
    }
    // Membership dispatch. With a single lemma, `simp` leaves `hcl` as a plain
    // equality (no disjunction), so `subst hcl` directly; with ≥2, split the
    // right-nested `Or` with `rcases … <;> subst h` and dispatch per branch.
    let dispatch = if l == 1 {
        format!("  subst hcl\n  exact lemma_{}_valid m\n", a + 1)
    } else {
        let rcases_pat = vec!["h"; l].join(" | ");
        format!("  rcases hcl with {rcases_pat} <;> subst h\n{dispatch_bullets}")
    };

    // (`val_ty`, `scalar_proj`, `fn_proj`, `pred_proj` were finalised above.)
    let model_note = match (has_fn, has_pred) {
        (false, false) => {
            "ONE global atom table and ONE shared model `Nat → Int` span every clause —\n  the Nelson–Oppen composition shape, generalised from\n  `AySoundness.CombinedExample`. Modeling uninterpreted constants as integers is\n  sound for equality-only reasoning (any realizable equivalence relation is\n  realizable over the integers)."
        }
        (true, false) => {
            "ONE global atom table and ONE shared model `(Nat → Int) × (Nat → Int → Int)`\n  span every clause (`m.1` = scalar valuation, `m.2` = the uninterpreted-function\n  FAMILY indexed by symbol) — the Nelson–Oppen composition shape, generalised\n  from `AySoundness.CombinedExample` (arithmetic by `omega`, congruence by `simp`)."
        }
        (false, true) => {
            "ONE global atom table and ONE shared model `(Nat → Int) × (Nat → Int → Bool)`\n  span every clause (`m.1` = scalar valuation, `m.2` = the uninterpreted-predicate\n  FAMILY indexed by symbol) — the Nelson–Oppen composition shape, generalised\n  from `AySoundness.CombinedExample` (arithmetic by `omega`, predicate congruence by `simp`)."
        }
        (true, true) => {
            "ONE global atom table and ONE shared model\n  `(Nat → Int) × (Nat → Int → Int) × (Nat → Int → Bool)` span every clause\n  (`m.1` = scalar valuation, `m.2.1` = function family, `m.2.2` = predicate\n  family, both indexed by symbol) — the Nelson–Oppen composition shape,\n  generalised from `AySoundness.CombinedExample`."
        }
    };
    let signature = format!(
        "{has_fn}|{has_pred}|{}|{}|{original_src}|{lemmas_src}|{}",
        funcs.join(","),
        preds.join(","),
        atom_render.join("\u{1}")
    );
    let hash = fnv_hex(&signature);

    let rec_depth = scaled_max_rec_depth(atom_render.len().max(max_lemma_atoms));
    Some(format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — GENERAL whole-DAG refutation grounded
  in the verified `firewall_combined_unsat`. The {a} input clause(s) and {l}
  theory lemma(s) are jointly unsatisfiable; premise (a) is the resolution
  (`lratCheck` by `decide`), premise (b) is each lemma holding in every model.
  {model_note}
  Pure Lean 4 core; axioms ⊆ {{propext, Classical.choice, Quot.sound}}.
-/
set_option linter.unusedSimpArgs false
set_option maxRecDepth {rec_depth}

namespace AySoundness.Emitted.General_{hash}
open AySoundness

abbrev Val := {val_ty}

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{original_src}]
def lemmas   : List (Cid × Clause) := [{lemmas_src}]
def proof    : List (Cid × Clause × List Int) := [({proof_id}, [], [{proof_hints}])]

{lemma_thms}theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
{dispatch}
/-- No model satisfies all the input clauses — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.General_{hash}
"#
    ))
}

/// Render a clause (list of literal `TermId`s) into signed global atom ids,
/// flattening a singleton `(or …)`. Interns each atomic (polarity-stripped)
/// `TermId` via the unified augmented renderer, which emits placeholder tokens
/// (resolved to the final model projections later once the function/predicate
/// family layout is known). Populates the `funcs`/`preds` family tables on
/// demand. `None` if any atom is not renderable.
#[allow(clippy::too_many_arguments)]
fn general_clause_lits(
    terms: &TermStore,
    clause: &[TermId],
    atom_ids: &mut Vec<TermId>,
    atom_render: &mut Vec<String>,
    atom_is_fn: &mut Vec<bool>,
    atom_is_bool: &mut Vec<bool>,
    vars: &mut Vec<String>,
    funcs: &mut Vec<String>,
    preds: &mut Vec<String>,
) -> Option<Vec<i64>> {
    let lits = flatten_or(terms, clause);
    let mut out = Vec::with_capacity(lits.len());
    for &lit in &lits {
        let (atomic, positive) = match terms.get(lit) {
            TermData::Not(inner) => (*inner, false),
            _ => (lit, true),
        };
        let id = intern_general_atom(
            terms,
            atomic,
            atom_ids,
            atom_render,
            atom_is_fn,
            atom_is_bool,
            vars,
            funcs,
            preds,
        )? as i64;
        out.push(if positive { id } else { -id });
    }
    Some(out)
}

/// Get-or-assign the 1-based global Nat id for an atomic term, rendering it on
/// first sight. `None` if the atom is not renderable (BV, non-unary function, …).
#[allow(clippy::too_many_arguments)]
fn intern_general_atom(
    terms: &TermStore,
    atomic: TermId,
    atom_ids: &mut Vec<TermId>,
    atom_render: &mut Vec<String>,
    atom_is_fn: &mut Vec<bool>,
    atom_is_bool: &mut Vec<bool>,
    vars: &mut Vec<String>,
    funcs: &mut Vec<String>,
    preds: &mut Vec<String>,
) -> Option<usize> {
    if let Some(pos) = atom_ids.iter().position(|&a| a == atomic) {
        return Some(pos + 1);
    }
    // `is_special` = congruence conclusion (function/predicate application);
    // `is_bool` = renders as a raw `Bool` (predicate application) vs `decide`-Prop.
    let (rendered, is_special, is_bool) = render_atom_aug(terms, atomic, vars, funcs, preds)?;
    atom_ids.push(atomic);
    atom_render.push(rendered);
    atom_is_fn.push(is_special);
    atom_is_bool.push(is_bool);
    Some(atom_ids.len())
}

/// Render an atom over the augmented EUF congruence model. Returns `(rendered,
/// is_special, is_bool)`:
///   - a binary comparison/equality `(<op> a b)` → `(Prop, sides-have-fn-app,
///     false)`; `is_special` marks a congruence CONCLUSION (a function-
///     application equality, e.g. `f a = g b`);
///   - a unary uninterpreted-PREDICATE application `(P s)` → `(raw-Bool, true,
///     true)`; `s` may itself be a function application (`P(f a)`).
/// Scalars / function applications / predicates are emitted as PLACEHOLDER
/// tokens (`␂S i␂` / `␂F k␂` / `␂P k␂`) and resolved to the final model
/// projections once the (function, predicate) family layout is known (see
/// `resolve_placeholders`). Function symbols index into `funcs`, predicates into
/// `preds`. `None` if not a renderable comparison / equality / unary predicate.
fn render_atom_aug(
    terms: &TermStore,
    atomic: TermId,
    vars: &mut Vec<String>,
    funcs: &mut Vec<String>,
    preds: &mut Vec<String>,
) -> Option<(String, bool, bool)> {
    let TermData::App(sym, args) = terms.get(atomic) else {
        return None;
    };
    match (sym.name(), args.len()) {
        (op @ ("<=" | ">=" | "<" | ">" | "="), 2) => {
            let op = match op {
                "<=" => "≤",
                ">=" => "≥",
                other => other,
            };
            let (l, lf) = render_side_aug(terms, args[0], vars, funcs, preds)?;
            let (r, rf) = render_side_aug(terms, args[1], vars, funcs, preds)?;
            Some((format!("{l} {op} {r}"), lf || rf, false))
        }
        // Unary uninterpreted-predicate application — a congruence conclusion,
        // already `Bool`. Its argument MAY be a function application (`P(f a)`).
        // Require a `Named` symbol (decline `Indexed` operators, which would
        // collapse distinct symbols onto one predicate-family slot).
        (name, 1) if matches!(sym, Symbol::Named(_)) => {
            let k = family_index(preds, name);
            let (arg, _af) = render_side_aug(terms, args[0], vars, funcs, preds)?;
            Some((format!("(\u{2}P{k}\u{2} {arg})"), true, true))
        }
        _ => None,
    }
}

/// Stable 0-based index for a function/predicate symbol name in its family table.
fn family_index(table: &mut Vec<String>, name: &str) -> usize {
    table.iter().position(|n| n == name).unwrap_or_else(|| {
        table.push(name.to_string());
        table.len() - 1
    })
}

/// Resolve the placeholder tokens from `render_side_aug`/`render_atom_aug` into
/// final model projections, once the family layout is known: `␂S i␂` →
/// `(<scalar_proj> i)` (`m` flat, `m.1` augmented); `␂F k␂` → `(<fn_proj> k)`
/// (`m.2` fn-only, `m.2.1` mixed); `␂P k␂` → `(<pred_proj> k)` (`m.2` pred-only,
/// `m.2.2` mixed).
fn resolve_placeholders(s: &str, scalar_proj: &str, fn_proj: &str, pred_proj: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\u{2}' {
            out.push(c);
            continue;
        }
        let kind = chars.next().unwrap_or('S');
        let mut num = String::new();
        while let Some(&d) = chars.peek() {
            if d == '\u{2}' {
                chars.next();
                break;
            }
            num.push(d);
            chars.next();
        }
        let proj = match kind {
            'F' => fn_proj,
            'P' => pred_proj,
            _ => scalar_proj,
        };
        out.push_str(&format!("({proj} {num})"));
    }
    out
}

/// Render one term side over the augmented model. Returns `(rendered,
/// has_fn_app)`. Scalars (Int literal / variable / nullary constant) → an `␂S i␂`
/// placeholder; a UNARY uninterpreted-function application `(f s)` → `(␂F k␂ <s>)`
/// where `f` gets a stable index `k` in the `funcs` family (scalar argument, NO
/// nested function-in-function); linear `+`/`-`/`*` over scalar sides. `None`
/// otherwise.
fn render_side_aug(
    terms: &TermStore,
    t: TermId,
    vars: &mut Vec<String>,
    funcs: &mut Vec<String>,
    preds: &mut Vec<String>,
) -> Option<(String, bool)> {
    match terms.get(t) {
        TermData::Const(ay_core::Constant::Int(v)) => Some((format!("({v} : Int)"), false)),
        TermData::Var(name, _) => Some((format!("\u{2}S{}\u{2}", scalar_index(vars, name)), false)),
        TermData::App(sym, args) if args.is_empty() => Some((
            format!("\u{2}S{}\u{2}", scalar_index(vars, sym.name())),
            false,
        )),
        TermData::App(sym, args) => match (sym.name(), args.len()) {
            ("+", _) if !args.is_empty() => {
                let parts = render_scalar_args(terms, args, vars, funcs, preds)?;
                Some((format!("({})", parts.join(" + ")), false))
            }
            ("-", 2) => {
                let parts = render_scalar_args(terms, args, vars, funcs, preds)?;
                Some((format!("({} - {})", parts[0], parts[1]), false))
            }
            ("-", 1) => {
                let parts = render_scalar_args(terms, args, vars, funcs, preds)?;
                Some((format!("(-{})", parts[0]), false))
            }
            ("*", 2) => {
                let parts = render_scalar_args(terms, args, vars, funcs, preds)?;
                Some((format!("({} * {})", parts[0], parts[1]), false))
            }
            // A unary uninterpreted-function application — a member of the
            // function family, indexed by symbol name. Require a `Named` symbol:
            // an `Indexed` operator (`(_ s i)`) would collapse distinct symbols
            // onto one family slot (`name` drops the indices), so decline it.
            (name, 1) if matches!(sym, Symbol::Named(_)) => {
                let k = family_index(funcs, name);
                let (arg, af) = render_side_aug(terms, args[0], vars, funcs, preds)?;
                if af {
                    return None; // no nested function-in-function applications
                }
                Some((format!("(\u{2}F{k}\u{2} {arg})"), true))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Render each of `args` as a SCALAR side (no function applications allowed —
/// arithmetic must be over scalars for `omega`). `None` if any arg is a function
/// application or otherwise unrenderable.
fn render_scalar_args(
    terms: &TermStore,
    args: &[TermId],
    vars: &mut Vec<String>,
    funcs: &mut Vec<String>,
    preds: &mut Vec<String>,
) -> Option<Vec<String>> {
    let mut out = Vec::with_capacity(args.len());
    for &a in args {
        let (s, f) = render_side_aug(terms, a, vars, funcs, preds)?;
        if f {
            return None;
        }
        out.push(s);
    }
    Some(out)
}

/// Stable 1-of-n index for a scalar symbol name in the valuation table.
fn scalar_index(vars: &mut Vec<String>, name: &str) -> usize {
    vars.iter().position(|v| v == name).unwrap_or_else(|| {
        vars.push(name.to_string());
        vars.len() - 1
    })
}

/// Emit a verified-firewall Lean proof for an EUF congruence conflict lemma
/// `(not (= a b)) (= (f a) (f b))` (`:rule eq_congruent`) with a SINGLE unary
/// uninterpreted function applied to constants. The function is modeled
/// explicitly (`Val = (Nat → Nat) × (Nat → Nat)` = valuation × `f`), since a
/// flat valuation is unfaithful for congruence; validity is `by_cases` on the
/// argument equality + `simp`. Returns `None` for shapes outside this (multiple
/// functions, non-unary, non-constant arguments) — the firewall reconstruction
/// is the function-model PoC `AySoundness.CombinedEufCongruence`.
pub(crate) fn emit_euf_congruence_firewall_lean(
    terms: &TermStore,
    lemma_clause: &[TermId],
) -> Option<String> {
    let lits = flatten_or(terms, lemma_clause);
    if lits.len() < 2 {
        return None;
    }
    let mut consts: Vec<String> = Vec::new();
    let mut func: Option<String> = None;
    let mut arity: Option<usize> = None;
    // (rendered equality prop, polarity-in-lemma, is_argument_equality).
    // Argument equalities (`¬(aᵢ = cᵢ)`, both sides constants) are the ones we
    // `by_cases` on; the single function-application equality conclusion follows
    // by `simp` (congruence by rewriting).
    let mut atoms: Vec<(String, bool, bool)> = Vec::new();
    for &lit in &lits {
        let (inner, positive) = match terms.get(lit) {
            TermData::Not(i) => (*i, false),
            _ => (lit, true),
        };
        let (a, b) = equality_sides(terms, inner)?;
        if is_const(terms, a) && is_const(terms, b) {
            let ra = render_const_m1(terms, a, &mut consts)?;
            let rb = render_const_m1(terms, b, &mut consts)?;
            atoms.push((format!("{ra} = {rb}"), positive, true));
        } else {
            let ra = render_fn_app(terms, a, &mut consts, &mut func, &mut arity)?;
            let rb = render_fn_app(terms, b, &mut consts, &mut func, &mut arity)?;
            atoms.push((format!("{ra} = {rb}"), positive, false));
        }
    }
    let ar = arity?; // at least one function-application equality conclusion
    func.as_ref()?;
    // Need at least one argument equality to `by_cases` on.
    if !atoms.iter().any(|(_, _, is_arg)| *is_arg) {
        return None;
    }
    Some(render_cong_lean(&atoms, ar))
}

/// A constant (uninterpreted): a variable or a nullary application.
fn is_const(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Var(_, _) => true,
        TermData::App(_, args) => args.is_empty(),
        _ => false,
    }
}

/// Emit a verified-firewall Lean proof for an EUF predicate-congruence conflict
/// lemma `(not (= a b)) (not (P a)) (P b)` (`:rule eq_congruent_pred`) with a
/// SINGLE unary uninterpreted predicate applied to constants. Modeled by
/// `Val = (Nat → Nat) × (Nat → Bool)` (valuation × the predicate `P`). Equality
/// atoms render under `decide`; predicate atoms are already `Bool`. Validity is
/// `by_cases` on the argument equality + `simp`. `None` for shapes outside this.
pub(crate) fn emit_euf_pred_congruence_firewall_lean(
    terms: &TermStore,
    lemma_clause: &[TermId],
) -> Option<String> {
    let lits = flatten_or(terms, lemma_clause);
    if lits.len() < 2 {
        return None;
    }
    let mut consts: Vec<String> = Vec::new();
    let mut pred: Option<String> = None;
    // (rendered atom, is_equality, polarity-in-lemma)
    let mut atoms: Vec<(String, bool, bool)> = Vec::new();
    let mut eq_idx: Option<usize> = None;
    for (i, &lit) in lits.iter().enumerate() {
        let (inner, positive) = match terms.get(lit) {
            TermData::Not(inner) => (*inner, false),
            _ => (lit, true),
        };
        if let Some((a, b)) = equality_sides(terms, inner) {
            // Equality atom over constants.
            let ra = render_const_m1(terms, a, &mut consts)?;
            let rb = render_const_m1(terms, b, &mut consts)?;
            atoms.push((format!("{ra} = {rb}"), true, positive));
            if eq_idx.is_some() {
                return None; // more than one equality atom: not this shape
            }
            eq_idx = Some(i);
        } else {
            // Predicate application atom `(P c)`.
            let rp = render_pred_app(terms, inner, &mut consts, &mut pred)?;
            atoms.push((rp, false, positive));
        }
    }
    let eq_idx = eq_idx?;
    if pred.is_none() || consts.len() != 2 {
        return None;
    }
    Some(render_pred_cong_lean(&atoms, eq_idx))
}

/// Render `(P c)` as `(m.2 (m.1 i))` for a single unary predicate `P` over a
/// constant; `None` if not a unary application of a constant or a second
/// distinct predicate symbol appears.
fn render_pred_app(
    terms: &TermStore,
    term: TermId,
    consts: &mut Vec<String>,
    pred: &mut Option<String>,
) -> Option<String> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    match pred {
        Some(p) if p != name => return None,
        Some(_) => {}
        None => *pred = Some(name.clone()),
    }
    let arg = render_const_m1(terms, args[0], consts)?;
    Some(format!("(m.2 {arg})"))
}

fn render_pred_cong_lean(atoms: &[(String, bool, bool)], eq_idx: usize) -> String {
    let n = atoms.len();
    let hash = fnv_hex(
        &atoms
            .iter()
            .map(|(s, e, p)| format!("{e}{p}:{s}"))
            .collect::<Vec<_>>()
            .join("\u{1}"),
    );
    let arms = atoms
        .iter()
        .enumerate()
        .map(|(i, (s, is_eq, _))| {
            if *is_eq {
                format!("  | {} => decide ({s})", i + 1)
            } else {
                format!("  | {} => {s}", i + 1)
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let orig = atoms
        .iter()
        .enumerate()
        .map(|(i, (_, _, pos))| {
            let lit = if *pos {
                format!("-{}", i + 1)
            } else {
                format!("{}", i + 1)
            };
            format!("({}, [{lit}])", i + 1)
        })
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_lits = atoms
        .iter()
        .enumerate()
        .map(|(i, (_, _, pos))| {
            if *pos {
                format!("{}", i + 1)
            } else {
                format!("-{}", i + 1)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = n + 1;
    let proof_hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let eq_prop = &atoms[eq_idx].0;
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — EUF predicate-congruence conflict
  grounded in the verified `firewall_combined_unsat`. Premise (a): resolution
  (`lratCheck` by `decide`). Premise (b): the `eq_congruent_pred` lemma holds in
  every model, by `by_cases` on the argument equality + `simp`. Model:
  `(Nat → Nat) × (Nat → Bool)` = valuation × the uninterpreted predicate. Pure
  Lean 4 core.
-/
namespace AySoundness.Emitted.PredCong_{hash}
open AySoundness

abbrev Val := (Nat → Nat) × (Nat → Bool)

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof2}, [], [{proof_hints}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h1 : {eq_prop} <;> simp [h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No model `(v, P)` satisfies `a = b ∧ P a ∧ ¬P b` — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.PredCong_{hash}
"#,
        hash = hash,
        arms = arms,
        orig = orig,
        lemma_lits = lemma_lits,
        lemma_id = lemma_id,
        proof2 = lemma_id + 1,
        proof_hints = proof_hints,
        eq_prop = eq_prop,
    )
}

/// Render an n-ary EUF congruence conflict. `atoms` are `(prop, polarity,
/// is_argument_equality)`; `arity` is the function's arity. The argument
/// equalities are `by_cases`-split (closing the function-application conclusion
/// by `simp` congruence-rewriting). Model: `(Nat → Nat) × (Nat → … → Nat)` =
/// constant valuation × the uninterpreted `arity`-ary function.
fn render_cong_lean(atoms: &[(String, bool, bool)], arity: usize) -> String {
    let n = atoms.len();
    let hash = fnv_hex(
        &atoms
            .iter()
            .map(|(s, p, a)| format!("{p}{a}:{s}"))
            .collect::<Vec<_>>()
            .join("\u{1}"),
    );
    let arms = atoms
        .iter()
        .enumerate()
        .map(|(i, (s, _, _))| format!("  | {} => decide ({s})", i + 1))
        .collect::<Vec<_>>()
        .join("\n");
    let orig = atoms
        .iter()
        .enumerate()
        .map(|(i, (_, pos, _))| {
            let lit = if *pos {
                format!("-{}", i + 1)
            } else {
                format!("{}", i + 1)
            };
            format!("({}, [{lit}])", i + 1)
        })
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_lits = atoms
        .iter()
        .enumerate()
        .map(|(i, (_, pos, _))| {
            if *pos {
                format!("{}", i + 1)
            } else {
                format!("-{}", i + 1)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = n + 1;
    let proof_hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    // `by_cases` on each argument equality; `simp` closes the conclusion.
    let arg_props: Vec<&String> = atoms
        .iter()
        .filter(|(_, _, is_arg)| *is_arg)
        .map(|(s, _, _)| s)
        .collect();
    let bycases = arg_props
        .iter()
        .enumerate()
        .map(|(i, p)| format!("by_cases h{} : {p}", i + 1))
        .collect::<Vec<_>>()
        .join(" <;> ");
    let hs = (1..=arg_props.len())
        .map(|i| format!("h{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let func_ty = format!("{}Nat", "Nat → ".repeat(arity));
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — EUF congruence conflict ({arity}-ary
  function) grounded in the verified `firewall_combined_unsat`. The `eq_congruent`
  lemma `(⋀ aᵢ = cᵢ) → f a⃗ = f c⃗` holds in every model: `by_cases` on each
  argument equality, then `simp` rewrites and the conclusion is `rfl`. Model:
  `(Nat → Nat) × ({func_ty})` = constant valuation × the uninterpreted function
  (explicit, since a flat valuation is unfaithful for congruence). Pure Lean 4 core.
-/
namespace AySoundness.Emitted.Cong_{hash}
open AySoundness

abbrev Val := (Nat → Nat) × ({func_ty})

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof2}, [], [{proof_hints}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  {bycases} <;> simp [{hs}]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No model satisfies the argument equalities while disagreeing on `f` — via the
    firewall (congruence). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.Cong_{hash}
"#,
        arity = arity,
        func_ty = func_ty,
        hash = hash,
        arms = arms,
        orig = orig,
        lemma_lits = lemma_lits,
        lemma_id = lemma_id,
        proof2 = lemma_id + 1,
        proof_hints = proof_hints,
        bycases = bycases,
        hs = hs,
    )
}

/// Render a function-free constant/variable as `(m.1 i)` (the valuation
/// component of the congruence model).
fn render_const_m1(terms: &TermStore, term: TermId, consts: &mut Vec<String>) -> Option<String> {
    let name = match terms.get(term) {
        TermData::Var(n, _) => n.clone(),
        TermData::App(Symbol::Named(n), args) if args.is_empty() => n.clone(),
        _ => return None,
    };
    let idx = consts.iter().position(|c| c == &name).unwrap_or_else(|| {
        consts.push(name);
        consts.len() - 1
    });
    Some(format!("(m.1 {idx})"))
}

/// Render a function application `(f c1 .. ck)` as `(m.2 (m.1 i1) .. (m.1 ik))`
/// for a SINGLE uninterpreted function `f` (recorded in `func`, arity in
/// `arity`) applied to constants. `None` if a second distinct function symbol or
/// a different arity appears, or an argument is not a constant.
fn render_fn_app(
    terms: &TermStore,
    term: TermId,
    consts: &mut Vec<String>,
    func: &mut Option<String>,
    arity: &mut Option<usize>,
) -> Option<String> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if args.is_empty() {
        return None;
    }
    match func {
        Some(f) if f != name => return None,
        Some(_) => {}
        None => *func = Some(name.clone()),
    }
    match arity {
        Some(k) if *k != args.len() => return None,
        Some(_) => {}
        None => *arity = Some(args.len()),
    }
    let rendered: Option<Vec<String>> = args
        .iter()
        .map(|&a| render_const_m1(terms, a, consts))
        .collect();
    Some(format!("(m.2 {})", rendered?.join(" ")))
}

/// Emit a verified-firewall Lean proof for a self-contained array
/// read-over-write-neg lemma
/// `(i = j) ∨ (= (select (store a i v) j) (select a j))`
/// (`:rule read_over_write_neg`).
///
/// The guard is mandatory: the equality alone is valid only in the contextual
/// `i ≠ j` case and therefore is not a theory lemma.  Requiring the guarded
/// clause keeps proof attribution and firewall recognition aligned with the
/// strict array checker.  The emitter grounds the refutation of
/// `i ≠ j ∧ (the equality fails)` through the verified firewall. Because the
/// McCarthy ROW axiom holds for ALL arrays/indices/values,
/// `a, i, j, v` are modeled as opaque components (`Val = (Nat → Nat) × (Nat →
/// Nat)` = array × scalar valuation with `i = s 0`, `j = s 1`, `v = s 2`); the
/// emitted certificate is the GENERIC ROW2 theorem. Validity is `by_cases` on
/// `i = j` + `simp` (`store`-update reduction). Returns `None` for a guard-less
/// unit or any other non-ROW2 structure.
pub(crate) fn emit_array_row2_firewall_lean(
    terms: &TermStore,
    lemma_clause: &[TermId],
) -> Option<String> {
    // Keep firewall attribution identical to the strict proof boundary,
    // including the complete Array(index, element) signature checks.  This
    // also deliberately excludes weakened three-literal clauses: they must be
    // normalized to an exact ROW2 primitive plus an explicit weakening step.
    if ay_proof::recognize_array_select_store(terms, lemma_clause) != Some(false) {
        return None;
    }
    let lits = flatten_or(terms, lemma_clause);
    if lits.len() != 2 {
        return None;
    }
    for row_position in 0..2 {
        let row_eq = lits[row_position];
        let guard = lits[1 - row_position];
        let Some((lhs, rhs)) = equality_sides(terms, row_eq) else {
            continue;
        };
        // One side is `(select (store a i v) j)`, the other `(select a j)`.
        let Some((a, i, j, v)) =
            parse_row2(terms, lhs, rhs).or_else(|| parse_row2(terms, rhs, lhs))
        else {
            continue;
        };
        if i == j {
            continue;
        }
        let Some((guard_lhs, guard_rhs)) = equality_sides(terms, guard) else {
            continue;
        };
        if !((guard_lhs == i && guard_rhs == j) || (guard_lhs == j && guard_rhs == i)) {
            continue;
        }
        let _ = (a, v); // modeled as opaque components; identity not needed
        return Some(render_array_row2_lean(j.0));
    }
    None
}

/// Parse `lhs = (select (store a i v) j)` and `rhs = (select a' j')` with
/// `a == a'`, `j == j'`. Returns `(a, i, j, v)`.
fn parse_row2(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
) -> Option<(TermId, TermId, TermId, TermId)> {
    let (store_term, j) = select_args(terms, lhs)?;
    let (a, i, v) = store_args(terms, store_term)?;
    let (a2, j2) = select_args(terms, rhs)?;
    if a == a2 && j == j2 {
        Some((a, i, j, v))
    } else {
        None
    }
}

fn select_args(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

fn store_args(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, TermId)> {
    match terms.get(term) {
        TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
            Some((args[0], args[1], args[2]))
        }
        _ => None,
    }
}

fn render_array_row2_lean(seed: u32) -> String {
    let hash = fnv_hex(&format!("row2:{seed}"));
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — array read-over-write-neg, grounded in
  the verified `firewall_combined_unsat`. ay's unit lemma
  `select (store a i v) j = select a j` is valid only under the contextual
  `i ≠ j`; here the self-contained TAUTOLOGY `(i = j) ∨ (that equality)` is used
  (McCarthy ROW: equal indices, or the other-index read is unaffected). The
  refutation of `i ≠ j ∧ (the equality fails)` is discharged through the
  firewall. Model: `(Nat → Nat) × (Nat → Nat)` = array × scalar valuation
  (`i = s 0`, `j = s 1`, `v = s 2`); `store` is an `if`-update. Since the ROW
  axiom holds for all arrays/indices/values, this is the GENERIC ROW2 theorem.
  Validity: `by_cases` on `i = j` + `simp`. Pure Lean 4 core.
-/
namespace AySoundness.Emitted.ArrRow2_{hash}
open AySoundness

abbrev Val := (Nat → Nat) × (Nat → Nat)

-- atom 1 = (i = j); atom 2 = (select (store a i v) j = select a j), where
--   select (store a i v) j = (if j = i then v else a j),  select a j = a j.
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.2 0 = m.2 1)
  | 2 => decide ((if (m.2 1) = (m.2 0) then (m.2 2) else (m.1 (m.2 1))) = (m.1 (m.2 1)))
  | _ => false

def original : List (Cid × Clause) := [(1, [-1]), (2, [-2])]
def lemmas   : List (Cid × Clause) := [(3, [1, 2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [1, 2] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h : m.2 0 = m.2 1 <;> simp [h, eq_comm]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No model satisfies `i ≠ j ∧ select (store a i v) j ≠ select a j` — via the
    firewall (the generic read-over-write-neg theorem). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrRow2_{hash}
"#,
    )
}

fn equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Render a function-free EUF term (constant or variable) as `(m i)` for a
/// stable valuation index; `None` for function applications (need a richer
/// model than a plain valuation).
fn render_const(terms: &TermStore, term: TermId, consts: &mut Vec<String>) -> Option<String> {
    let name = match terms.get(term) {
        TermData::Var(n, _) => n.clone(),
        TermData::App(Symbol::Named(n), args) if args.is_empty() => n.clone(),
        _ => return None,
    };
    let idx = consts.iter().position(|c| c == &name).unwrap_or_else(|| {
        consts.push(name);
        consts.len() - 1
    });
    Some(format!("(m {idx})"))
}

/// Deterministic FNV-1a hash, lowercase hex — for collision-free namespaces.
fn fnv_hex(s: &str) -> String {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in s.bytes() {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    format!("{h:016x}")
}

/// Render a comparison `(<op> a b)` as a Lean `Prop`, collecting variables into
/// `vars` (a stable valuation index per distinct variable IDENTITY).
fn render_comparison(
    terms: &TermStore,
    term: TermId,
    vars: &mut Vec<(String, u32)>,
) -> Option<String> {
    let TermData::App(sym, args) = terms.get(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let op = match sym.name() {
        "<=" => "≤",
        ">=" => "≥",
        "<" => "<",
        ">" => ">",
        "=" => "=",
        _ => return None,
    };
    let lhs = render_int(terms, args[0], vars)?;
    let rhs = render_int(terms, args[1], vars)?;
    Some(format!("{lhs} {op} {rhs}"))
}

/// Render a linear integer term as Lean. Variables become `(m i)` for a stable
/// valuation index `i`; only `+`, `-`, `*` and integer constants are handled.
///
/// The index is keyed on the term store's UNIQUE variable identity — the
/// `(name, id)` pair, not the printed name alone. Two distinct variables that
/// happen to print the same would otherwise collapse onto one `(m i)`, and the
/// emitted `original` would no longer be a faithful subset of the query's
/// atoms.
fn render_int(terms: &TermStore, term: TermId, vars: &mut Vec<(String, u32)>) -> Option<String> {
    match terms.get(term) {
        TermData::Const(ay_core::Constant::Int(v)) => Some(format!("({v} : Int)")),
        TermData::Var(name, id) => {
            let key = (name.clone(), *id);
            let idx = vars.iter().position(|v| *v == key).unwrap_or_else(|| {
                vars.push(key);
                vars.len() - 1
            });
            Some(format!("(m {idx})"))
        }
        TermData::App(sym, args) => {
            let parts: Option<Vec<String>> =
                args.iter().map(|&a| render_int(terms, a, vars)).collect();
            let parts = parts?;
            match (sym.name(), parts.len()) {
                ("+", _) if !parts.is_empty() => Some(format!("({})", parts.join(" + "))),
                ("-", 2) => Some(format!("({} - {})", parts[0], parts[1])),
                ("-", 1) => Some(format!("(-{})", parts[0])),
                ("*", 2) => Some(format!("({} * {})", parts[0], parts[1])),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Render the Lean source. `dt` is the datatype name, `ctors` all its
/// constructors (emitted nullary), `c1`/`c2` the two the lemma distinguishes.
fn render_lean(dt: &str, ctors: &[String], c1: &str, c2: &str) -> String {
    let ns = sanitize(dt);
    let ind = ctors
        .iter()
        .map(|c| format!("  | {}", sanitize(c)))
        .collect::<Vec<_>>()
        .join("\n");
    let s1 = sanitize(c1);
    let s2 = sanitize(c2);
    format!(
        r#"import AySoundness.Firewall
import AySoundness.Datatype
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — datatype constructor-distinctness
  conflict over encoded datatype `{ns}`, grounded in the verified
  `firewall_combined_unsat`.
  `c = {s1}` ∧ `c = {s2}` is unsatisfiable because `{s1}` and `{s2}` are distinct
  constructors. Premise (a): resolution closes (`lratCheck` by `decide`).
  Premise (b): the `dt_distinct` lemma `¬(c={s1}) ∨ ¬(c={s2})` holds in every
  model. Constructors are emitted nullary — a faithful abstraction for
  distinctness (the fact used is `{s1} ≠ {s2}`). Pure Lean 4 core. Original SMT
  names are never copied into Lean comments or identifiers.
-/
namespace AySoundness.Emitted.{ns}
open AySoundness

/-- The encoded datatype `{ns}` (constructors emitted nullary; see module note). -/
inductive T where
{ind}
deriving DecidableEq

/-- Atom interpretation under a model (the value of `c`):
    `1 ↦ c = {s1}`, `2 ↦ c = {s2}`. -/
def atomVal (c : T) (n : Nat) : Bool :=
  match n with
  | 1 => decide (c = T.{s1})
  | 2 => decide (c = T.{s2})
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, -2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- The `dt_distinct` lemma `¬(c={s1}) ∨ ¬(c={s2})` is valid in every model:
    no `c` is both `{s1}` and `{s2}` (distinct constructors). -/
theorem dt_distinct_lemma_valid (c : T) : clauseSat (atomVal c) [-1, -2] = true := by
  cases c <;>
    simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ c : T, clauseSat (atomVal c) cl = true := by
  intro cl hcl c
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact dt_distinct_lemma_valid c

/-- No model assigns `c` both `{s1}` and `{s2}` — through the verified firewall. -/
theorem no_model : ∀ c : T, ¬ Sat (atomVal c) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.{ns}
"#,
    )
}

/// Encode every byte of an untrusted SMT identifier into one injective Lean
/// identifier component. Encoding even apparently plain names avoids Lean
/// keyword collisions and avoids collisions between a plain name and an escape
/// spelling. No user byte reaches generated code or comments verbatim.
fn sanitize(name: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::from("s_");
    for byte in name.bytes() {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn flatten_or(terms: &TermStore, clause: &[TermId]) -> Vec<TermId> {
    if clause.len() == 1 {
        if let TermData::App(sym, args) = terms.get(clause[0]) {
            if sym.name() == "or" {
                return args.clone();
            }
        }
    }
    clause.to_vec()
}

fn negated_equality(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::Not(inner) = terms.get(term) else {
        return None;
    };
    match terms.get(*inner) {
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

fn shared_and_others(
    a1: TermId,
    b1: TermId,
    a2: TermId,
    b2: TermId,
) -> Option<(TermId, TermId, TermId)> {
    if a1 == a2 {
        Some((a1, b1, b2))
    } else if a1 == b2 {
        Some((a1, b1, a2))
    } else if b1 == a2 {
        Some((b1, a1, b2))
    } else if b1 == b2 {
        Some((b1, a1, a2))
    } else {
        None
    }
}

fn constructor_name(terms: &TermStore, term: TermId) -> Option<String> {
    match terms.get(term) {
        TermData::App(Symbol::Named(n), _) => Some(n.clone()),
        TermData::Var(n, _) => Some(n.clone()),
        _ => None,
    }
}

fn datatype_of<'a>(decls: DatatypeDecls<'a>, ctor: &str) -> Option<(&'a str, &'a [String])> {
    decls.iter().find_map(|(dt, ctors)| {
        ctors
            .iter()
            .any(|c| c == ctor)
            .then_some((dt.as_str(), ctors.as_slice()))
    })
}

// ==== APPENDED BUCKET: b_wordeq.rs ====
/// Length-polynomial of a parsed string-valued term over `str.++` (any arity),
/// symbols, and string literals: returns `(variable → occurrence coefficient,
/// literal-length constant)`, or `None` if the term contains ANY other shape
/// (`str.at`, `str.replace`, `str.substr`, …) — fail-closed decline.
///
/// This is the Parikh-on-lengths projection: `len` of the term equals
/// `Σ coeff_v · len v + constant`, a fact justified entirely by `StringThy.len_cat`
/// (length is a monoid homomorphism). Occurrence coefficients count how many times
/// each variable appears in the concatenation.
fn parsed_str_len_poly(t: &PTerm) -> Option<(Vec<(String, i64)>, i64)> {
    fn go(t: &PTerm, coeffs: &mut Vec<(String, i64)>, constant: &mut i64) -> Option<()> {
        match t {
            PTerm::Symbol(s) => {
                if let Some(e) = coeffs.iter_mut().find(|(n, _)| n == s) {
                    e.1 += 1;
                } else {
                    coeffs.push((s.clone(), 1));
                }
                Some(())
            }
            PTerm::Const(PConst::String(l)) => {
                *constant += l.chars().count() as i64;
                Some(())
            }
            PTerm::App(op, args) if op == "str.++" && !args.is_empty() => {
                for a in args {
                    go(a, coeffs, constant)?;
                }
                Some(())
            }
            _ => None,
        }
    }
    let mut coeffs: Vec<(String, i64)> = Vec::new();
    let mut constant: i64 = 0;
    go(t, &mut coeffs, &mut constant)?;
    Some((coeffs, constant))
}

/// Collect the DISTINCT string literals (by content) appearing under `str.++` in
/// a parsed string-valued term, in first-appearance order.
fn collect_str_literals(t: &PTerm, out: &mut Vec<String>) {
    match t {
        PTerm::Const(PConst::String(l)) => {
            if !out.iter().any(|x| x == l) {
                out.push(l.clone());
            }
        }
        PTerm::App(op, args) if op == "str.++" => {
            for a in args {
                collect_str_literals(a, out);
            }
        }
        _ => {}
    }
}

/// Lean model projection for the variable `s` given the ordered variable list.
/// One variable ⟹ the whole model `m`; two ⟹ `m.1` / `m.2`.
fn word_eq_proj(vars: &[String], s: &str) -> String {
    let idx = vars.iter().position(|v| v == s).unwrap_or(0);
    if vars.len() <= 1 {
        "m".to_string()
    } else if idx == 0 {
        "m.1".to_string()
    } else {
        "m.2".to_string()
    }
}

/// Render a string literal as a concrete `StringThy.Str` (`List Nat` of Unicode
/// codepoints) with a type ascription, e.g. `"ab"` ⟹ `([97, 98] : StringThy.Str)`.
fn word_eq_lean_str_list(l: &str) -> String {
    let codes: Vec<String> = l.chars().map(|c| (c as u32).to_string()).collect();
    format!("([{}] : StringThy.Str)", codes.join(", "))
}

/// Render a parsed string-valued concat-tree to a Lean `StringThy` expression over
/// the model: symbols ⟹ `m` / `m.1` / `m.2`, literals ⟹ concrete `List Nat`,
/// `str.++` ⟹ right-associated `StringThy.cat`. Assumes the term already passed
/// [`parsed_str_len_poly`] (so only these three shapes occur).
fn word_eq_render_str_expr(t: &PTerm, vars: &[String]) -> String {
    match t {
        PTerm::Symbol(s) => word_eq_proj(vars, s),
        PTerm::Const(PConst::String(l)) => word_eq_lean_str_list(l),
        PTerm::App(op, args) if op == "str.++" && !args.is_empty() => {
            let parts: Vec<String> = args
                .iter()
                .map(|a| word_eq_render_str_expr(a, vars))
                .collect();
            let mut acc = parts.last().unwrap().clone();
            for p in parts.iter().rev().skip(1) {
                acc = format!("(StringThy.cat {p} {acc})");
            }
            acc
        }
        // Unreachable: guarded by `parsed_str_len_poly`; fail-closed to a harmless
        // placeholder rather than panicking.
        _ => "(StringThy.empty)".to_string(),
    }
}

/// Emit a verified-firewall Lean proof for a WORD-EQUATION length conflict found
/// among the PARSED (frontend) assertions: a string equation `(= A B)` whose two
/// sides are `str.++`/literal/variable concat-trees, together with zero or more
/// `(= (str.len v) c)` length pins, whose induced LENGTH system is unsatisfiable
/// over `ℕ`.
///
/// Taking `len` of both sides of `A = B` and expanding every `str.++` through the
/// verified axiom `StringThy.len_cat` (`len (cat X Y) = len X + len Y`) yields a
/// linear equation `Σ (a_v − b_v) · len v = |lits B| − |lits A|`; substituting the
/// pinned `len v = c` leaves a residual that has NO ℕ solution (e.g. `2·len x = 3`
/// for `x·x = "aba"`, `3·len x = 2` for `x·x·x = "ab"`, or the pinned collapse
/// `1 + 2 = 1 + 1` for `x·"ab" = "a"·y ∧ |x| = |y| = 1`). The conflict is recovered
/// from the frontend parsed assertions (ay reduces str.len/str.++ eagerly, so the
/// TermId-level conflict is surface-rewrite-trivialized before emit), grounded
/// through the verified `firewall_combined_unsat` over `Val = StringThy.Str`
/// (one variable) or `StringThy.Str × StringThy.Str` (two); kernel-checks with
/// axioms ⊆ {propext, Quot.sound}.
///
/// Fail-closed: declines (returns `None`) unless it identifies a string equation
/// with 1–2 variables whose length projection — after substituting the pins — is
/// provably ℕ-infeasible with AT MOST ONE remaining free variable length (so the
/// emitted `omega` is guaranteed to discharge it). Anything else — regex/contains/
/// suffix predicates, ≥3 variables, ≥2 free lengths, or a satisfiable length
/// system — is left uncertified (still sound: emission is verification-only).
pub(crate) fn emit_str_word_eq_len_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    // Collect asserted variable lengths: `(= (str.len v) c)` / `(= c (str.len v))`.
    let mut known_len: Vec<(String, i64)> = Vec::new();
    for asrt in parsed {
        if let PTerm::App(op, args) = asrt {
            if op == "=" && args.len() == 2 {
                for (a, b) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    if let (Some(v), Some(k)) = (parsed_str_len_arg(a), parsed_numeral(b)) {
                        if k >= 0 && !known_len.iter().any(|(n, _)| *n == v) {
                            known_len.push((v, k));
                        }
                    }
                }
            }
        }
    }
    // Find a string equation whose length projection is ℕ-infeasible.
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        let (Some((amap, aconst)), Some((bmap, bconst))) =
            (parsed_str_len_poly(&args[0]), parsed_str_len_poly(&args[1]))
        else {
            continue;
        };
        // Variables in first-appearance order across both sides.
        let mut vars: Vec<String> = Vec::new();
        for (v, _) in amap.iter().chain(bmap.iter()) {
            if !vars.contains(v) {
                vars.push(v.clone());
            }
        }
        if vars.is_empty() || vars.len() > 2 {
            continue;
        }
        let coeff = |m: &[(String, i64)], v: &str| -> i64 {
            m.iter().find(|(n, _)| n == v).map(|(_, c)| *c).unwrap_or(0)
        };
        // Net coefficient per variable and constant R: `Σ net_v · len v = R`.
        let net: Vec<(String, i64)> = vars
            .iter()
            .map(|v| (v.clone(), coeff(&amap, v) - coeff(&bmap, v)))
            .collect();
        let mut r: i64 = bconst - aconst;
        // Length pins restricted to variables appearing in this equation.
        let len_atoms: Vec<(String, i64)> = vars
            .iter()
            .filter_map(|v| {
                known_len
                    .iter()
                    .find(|(n, _)| n == v)
                    .map(|(_, k)| (v.clone(), *k))
            })
            .collect();
        for (v, k) in &len_atoms {
            let d = net
                .iter()
                .find(|(n, _)| n == v)
                .map(|(_, c)| *c)
                .unwrap_or(0);
            r -= d * k;
        }
        // Free variables: net-nonzero and NOT pinned.
        let free: Vec<(String, i64)> = net
            .iter()
            .filter(|(v, c)| *c != 0 && !len_atoms.iter().any(|(p, _)| p == v))
            .cloned()
            .collect();
        let infeasible = match free.len() {
            0 => r != 0,
            1 => {
                let d = free[0].1;
                // `d · L = r` has an ℕ solution iff `d | r` and `r / d ≥ 0`.
                !(r % d == 0 && r / d >= 0)
            }
            _ => false, // ≥2 free lengths: conservatively decline.
        };
        if !infeasible {
            continue;
        }
        return Some(render_str_word_eq_len_lean(
            &vars, &len_atoms, &args[0], &args[1],
        ));
    }
    None
}

/// Render the word-equation length-conflict firewall Lean. `lhs`/`rhs` are the two
/// sides of the string equation `(= lhs rhs)`; `len_atoms` are the pinned variable
/// lengths (`len v = c`) for variables occurring in the equation. Grounds
/// `StringThy.len_cat` through the verified `firewall_combined_unsat` over
/// `Val = StringThy.Str` (`vars.len() == 1`) or `StringThy.Str × StringThy.Str`.
///
/// Model layout: atoms `1..=p` are the `p = len_atoms.len()` length pins, atom
/// `p+1` is the string equation. The single theory-lemma clause `[-1, …, -(p+1)]`
/// asserts the atoms cannot all hold; its validity is discharged by case-splitting
/// the pins and refuting the string-equation atom via `congrArg StringThy.len`,
/// `StringThy.len_cat`, and `omega` on the residual ℕ-linear contradiction.
fn render_str_word_eq_len_lean(
    vars: &[String],
    len_atoms: &[(String, i64)],
    lhs: &PTerm,
    rhs: &PTerm,
) -> String {
    let val_ty = if vars.len() <= 1 {
        "StringThy.Str".to_string()
    } else {
        "StringThy.Str × StringThy.Str".to_string()
    };
    let seq = format!(
        "{} = {}",
        word_eq_render_str_expr(lhs, vars),
        word_eq_render_str_expr(rhs, vars)
    );
    // Distinct literals across both sides (for their `len = n` facts).
    let mut literals: Vec<String> = Vec::new();
    collect_str_literals(lhs, &mut literals);
    collect_str_literals(rhs, &mut literals);

    let p = len_atoms.len();
    let str_atom_id = p + 1;
    // atomVal arms.
    let mut arms: Vec<String> = Vec::new();
    for (i, (v, c)) in len_atoms.iter().enumerate() {
        arms.push(format!(
            "  | {} => decide (StringThy.len {} = {})",
            i + 1,
            word_eq_proj(vars, v),
            c
        ));
    }
    arms.push(format!("  | {str_atom_id} => decide ({seq})"));
    let arms = arms.join("\n");

    let orig = (1..=str_atom_id)
        .map(|i| format!("({i}, [{i}])"))
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_lits = (1..=str_atom_id)
        .map(|i| format!("-{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = str_atom_id + 1;
    let proof_id = str_atom_id + 2;
    let proof_hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    // Innermost block: refute the string-equation atom via len_cat + omega.
    let mut inner: Vec<String> = Vec::new();
    inner.push(format!("have hs : ¬ ({seq}) := by"));
    inner.push("  intro heq".to_string());
    inner.push("  have hl := congrArg StringThy.len heq".to_string());
    inner.push("  simp only [StringThy.len_cat] at hl".to_string());
    for (i, l) in literals.iter().enumerate() {
        inner.push(format!(
            "  have hlit{i} : StringThy.len {} = {} := by decide",
            word_eq_lean_str_list(l),
            l.chars().count()
        ));
    }
    inner.push("  omega".to_string());
    inner.push("simp [hs]".to_string());

    // Wrap with a `by_cases` per length pin (atom 0 outermost).
    let mut body = inner;
    for j in (0..p).rev() {
        let (v, c) = &len_atoms[j];
        let hyp = format!("h{j}");
        let cond = format!("StringThy.len {} = {}", word_eq_proj(vars, v), c);
        let mut wrapped: Vec<String> = Vec::new();
        wrapped.push(format!("by_cases {hyp} : {cond}"));
        for (k, line) in body.iter().enumerate() {
            if k == 0 {
                wrapped.push(format!("· {line}"));
            } else {
                wrapped.push(format!("  {line}"));
            }
        }
        wrapped.push(format!("· simp [{hyp}]"));
        body = wrapped;
    }
    let proof_body = body
        .iter()
        .map(|l| format!("  {l}"))
        .collect::<Vec<_>>()
        .join("\n");

    let hash = fnv_hex(&format!("wordeqlen:{seq}\u{1}{p}"));
    format!(
        r#"import AySoundness.Firewall
import AySoundness.StringThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — WORD-EQUATION length conflict grounded in
  the verified `firewall_combined_unsat`. A string equation `A = B` over `str.++`,
  variables and literals (optionally with `str.len v = c` pins) is unsatisfiable
  because its LENGTH projection has no `ℕ` solution: taking `len` of both sides and
  expanding every `str.++` through the verified axiom `StringThy.len_cat`
  (`len (cat X Y) = len X + len Y`) yields a linear ℕ equation refuted by `omega`
  (e.g. `2·len x = 3` for `x·x = "aba"`). Reconstructed from the frontend parsed
  ASSERTIONS (ay reduces str.len/str.++ eagerly, so the conflict is
  surface-rewrite-trivialized before emit). Model: `Val = {val_ty}` (a string is
  the free monoid `List Nat` of codepoints; literals are their concrete codepoint
  lists). Pure Lean 4 core; axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.WordEqLen_{hash}
open AySoundness

abbrev Val := {val_ty}

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof_id}, [], [{proof_hints}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
{proof_body}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No assignment of the string variables satisfies the asserted word equation and
    its length pins — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.WordEqLen_{hash}
"#,
    )
}

// ---------------------------------------------------------------------------
// `str.indexof` ABSENT-needle firewall emitters (grounded in the verified,
// CLASSICAL-FREE `AySoundness.IndexOfThy.indexOf_absent_all_start`).
// ---------------------------------------------------------------------------

const MAX_INDEXOF_ALIAS_ASSERTIONS: usize = 10_000;
const MAX_INDEXOF_ALIAS_BYTES: usize = 8 * 1024 * 1024;
const MAX_INDEXOF_LITERAL_BYTES: usize = 1024 * 1024;
const MAX_INDEXOF_FIREWALL_SOURCE_BYTES: usize = 8 * 1024 * 1024;
const INDEXOF_RENDER_FIXED_RESERVE: usize = 64 * 1024;
const INDEXOF_RENDER_REFERENCE_FACTOR: usize = 16;

/// Resolve a parsed term to a ground STRING literal (its raw content). A string
/// literal resolves to itself; a symbol resolves through the `(= sym literal)` /
/// transitive `(= sym sym')` aliases in `str_binds`. The returned string borrows
/// the parsed AST: a long literal is never copied once per alias. `None` if the
/// term is not ground.
fn resolve_str_literal<'a>(
    t: &'a PTerm,
    str_binds: &std::collections::BTreeMap<&'a str, &'a str>,
) -> Option<&'a str> {
    match t {
        PTerm::Const(PConst::String(l)) => Some(l.as_str()),
        PTerm::Symbol(s) => str_binds.get(s.as_str()).copied(),
        _ => None,
    }
}

/// Collect `(= sym str-literal)` bindings AND transitive `(= sym sym')` string
/// aliases. A single graph build followed by a worklist traversal is
/// `O((V + E) log V)`; the former repeated full scan plus linear binding lookup
/// was cubic on a reverse-ordered alias chain. All names and literal values
/// borrow the parsed AST, preventing alias-count × literal-size amplification.
///
/// The assertion and referenced-byte caps mirror the diagnostic preflight's
/// resource envelope, but are repeated here because explicit
/// `--emit-firewall-lean` calls this emitter without that preflight. Crossing
/// either cap declines the entire lane (fail closed).
fn collect_str_binds(parsed: &[PTerm]) -> Option<std::collections::BTreeMap<&str, &str>> {
    use std::collections::{BTreeMap, VecDeque};

    if parsed.len() > MAX_INDEXOF_ALIAS_ASSERTIONS {
        return None;
    }

    let mut edges: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    let mut seeds: Vec<(&str, &str)> = Vec::new();
    let mut alias_bytes = 0usize;
    for assertion in parsed {
        let PTerm::App(op, args) = assertion else {
            continue;
        };
        if op != "=" || args.len() != 2 {
            continue;
        }
        match (&args[0], &args[1]) {
            (PTerm::Symbol(symbol), PTerm::Const(PConst::String(literal)))
            | (PTerm::Const(PConst::String(literal)), PTerm::Symbol(symbol)) => {
                alias_bytes = alias_bytes
                    .checked_add(symbol.len())?
                    .checked_add(literal.len())?;
                if alias_bytes > MAX_INDEXOF_ALIAS_BYTES {
                    return None;
                }
                seeds.push((symbol.as_str(), literal.as_str()));
            }
            (PTerm::Symbol(left), PTerm::Symbol(right)) if left != right => {
                alias_bytes = alias_bytes
                    .checked_add(left.len())?
                    .checked_add(right.len())?;
                if alias_bytes > MAX_INDEXOF_ALIAS_BYTES {
                    return None;
                }
                edges.entry(left.as_str()).or_default().push(right.as_str());
                edges.entry(right.as_str()).or_default().push(left.as_str());
            }
            _ => {}
        }
    }

    let mut binds = BTreeMap::new();
    let mut work = VecDeque::new();
    // Complete one component before considering the next literal seed. If an
    // asserted-equality component contains conflicting literal seeds then the
    // query is already inconsistent; choosing its first asserted seed remains
    // deterministic and every propagated equality is still an asserted fact.
    for (root, literal) in seeds {
        if binds.contains_key(root) {
            continue;
        }
        work.push_back(root);
        while let Some(symbol) = work.pop_front() {
            if binds.contains_key(symbol) {
                continue;
            }
            binds.insert(symbol, literal);
            if let Some(neighbors) = edges.get(symbol) {
                for &neighbor in neighbors {
                    if !binds.contains_key(neighbor) {
                        work.push_back(neighbor);
                    }
                }
            }
        }
    }
    Some(binds)
}

/// Render a string's Unicode codepoints as a bare Lean `List Nat` literal
/// (`"cba"` ⟹ `[99, 98, 97]`); the surrounding `IndexOfThy.indexOf : Str → …`
/// fixes the element type, so no ascription is needed. Mirrors the codepoint
/// mapping of [`word_eq_lean_str_list`] (which additionally ascribes).
fn indexof_codelist_len(s: &str) -> Option<usize> {
    let mut len = 2usize; // `[` + `]`
    let mut first = true;
    for codepoint in s.chars().map(|c| c as u32) {
        if !first {
            len = len.checked_add(2)?; // `, `
        }
        first = false;
        let digits = if codepoint == 0 {
            1
        } else {
            codepoint.ilog10() as usize + 1
        };
        len = len.checked_add(digits)?;
    }
    Some(len)
}

fn indexof_codelist(s: &str, exact_len: usize) -> String {
    use std::fmt::Write as _;

    let mut out = String::with_capacity(exact_len);
    out.push('[');
    for (index, codepoint) in s.chars().map(|c| c as u32).enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        write!(&mut out, "{codepoint}").expect("writing to String cannot fail");
    }
    out.push(']');
    debug_assert_eq!(out.len(), exact_len);
    out
}

/// Is `needle` ABSENT from `hay` — i.e. does the SMT `str.indexof hay needle _`
/// return `-1` for every start? Mirrors the verified `IndexOfThy.matchAt` /
/// `indexOf` model EXACTLY: `matchAt` at position `i` compares
/// `(hay.drop i).take needle.len` to `needle`, and `indexOf` scans `i ∈
/// 0..=hay.len`. Absence (⇒ the `by decide` `List.all` premise of
/// `indexOf_absent_all_start` holds) means no such `i` matches. An EMPTY needle
/// matches everywhere, so it is NOT absent (the emitters then decline). UTF-8
/// is self-synchronizing, so byte-substring containment of valid Rust strings is
/// equivalent to codepoint-list containment. `str::contains` uses a bounded,
/// allocation-free substring search; the checked byte cap also fences the work.
fn needle_absent(hay: &str, needle: &str) -> Option<bool> {
    let input_bytes = hay.len().checked_add(needle.len())?;
    if input_bytes > MAX_INDEXOF_LITERAL_BYTES {
        return None;
    }
    Some(!needle.is_empty() && !hay.contains(needle))
}

/// Materialize the two codepoint lists only after proving a conservative upper
/// bound for every repeated interpolation in the final source. This prevents a
/// large literal from allocating codepoint strings (and then a much larger
/// formatted artifact) before `BoundedFirewallArtifacts` can reject it.
fn bounded_indexof_codelists(
    hay: &str,
    needle: &str,
    max_source_bytes: usize,
) -> Option<(String, String)> {
    let source_cap = max_source_bytes.min(MAX_INDEXOF_FIREWALL_SOURCE_BYTES);
    let hay_len = indexof_codelist_len(hay)?;
    let needle_len = indexof_codelist_len(needle)?;
    let repeated_lists = hay_len
        .checked_add(needle_len)?
        .checked_mul(INDEXOF_RENDER_REFERENCE_FACTOR)?;
    let estimated_source = repeated_lists.checked_add(INDEXOF_RENDER_FIXED_RESERVE)?;
    if estimated_source > source_cap {
        return None;
    }
    Some((
        indexof_codelist(hay, hay_len),
        indexof_codelist(needle, needle_len),
    ))
}

/// Emit a verified-firewall Lean certificate for a `str.indexof`-ABSENT `≥ 0`
/// conflict among the PARSED assertions: `(>= (str.indexof H N s) 0)` where the
/// haystack `H` and needle `N` resolve to ground string LITERALS (through
/// `(= sym literal)` aliases) and `N` is genuinely ABSENT from `H` (so
/// `str.indexof = -1` for EVERY start). Asserting `-1 ≥ 0` is unsatisfiable.
///
/// Grounded in the verified, CLASSICAL-FREE `IndexOfThy.indexOf_absent_all_start`
/// (`∀ m, indexOf H N m = -1`, discharged from the decidable `List.all` witness by
/// `by decide` — NOT `simp`, which would leak `Classical.choice`); cf. the
/// hand-checked witness `IndexOfThy.xt_indexof_not_ge_zero`. The symbolic start `m`
/// is quantified UNIVERSALLY (`Val = Nat`), so the certificate refutes the
/// assertion for every non-negative start. `Ok(None)` unless `H`/`N` are ground
/// literals and `N` is genuinely absent from `H`; `Err(())` reports a resource
/// fence so the caller rejects the entire artifact batch rather than silently
/// publishing an incomplete set.
pub(crate) fn emit_str_indexof_absent_ge_firewall_lean_from_parsed(
    parsed: &[PTerm],
    max_source_bytes: usize,
) -> Result<Option<String>, ()> {
    let str_binds = collect_str_binds(parsed).ok_or(())?;
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        // `(>= (str.indexof H N s) 0)` — the absent-index-is-non-negative claim.
        if op != ">=" || args.len() != 2 {
            continue;
        }
        if parsed_numeral(&args[1]) != Some(0) {
            continue;
        }
        let PTerm::App(iop, iargs) = &args[0] else {
            continue;
        };
        if iop != "str.indexof" || iargs.len() != 3 {
            continue;
        }
        let (Some(hay), Some(needle)) = (
            resolve_str_literal(&iargs[0], &str_binds),
            resolve_str_literal(&iargs[1], &str_binds),
        ) else {
            continue;
        };
        // Fail-closed: emit ONLY when the needle is genuinely absent (so the
        // `by decide` `List.all` premise of `indexOf_absent_all_start` holds).
        if !needle_absent(hay, needle).ok_or(())? {
            continue;
        }
        let (hay_l, needle_l) =
            bounded_indexof_codelists(hay, needle, max_source_bytes).ok_or(())?;
        let rendered =
            render_str_indexof_absent_ge_lean(&hay_l, &needle_l, max_source_bytes).ok_or(())?;
        return Ok(Some(rendered));
    }
    Ok(None)
}

/// Render the `str.indexof`-ABSENT `≥ 0` firewall Lean. Grounds
/// `IndexOfThy.indexOf_absent_all_start` (CLASSICAL-FREE) through the verified
/// `firewall_combined_unsat` over `Val = Nat` (the universally-quantified symbolic
/// start `m`). The atom `str.indexof H N m ≥ 0` is refuted by rewriting the index
/// to `-1` (via the absence lemma) and closing the ground `¬(-1 ≥ 0)` by `decide`.
fn render_str_indexof_absent_ge_lean(
    hay_l: &str,
    needle_l: &str,
    max_source_bytes: usize,
) -> Option<String> {
    let hash = fnv_hex(&format!("indexofabsentge:{hay_l}:{needle_l}"));
    let rendered = format!(
        r#"import AySoundness.Firewall
import AySoundness.StringThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — `str.indexof`-ABSENT `≥ 0` conflict,
  grounded in the verified, CLASSICAL-FREE `IndexOfThy.indexOf_absent_all_start`
  (cf. the hand-checked witness `IndexOfThy.xt_indexof_not_ge_zero`). The assertion
  `str.indexof {hay_l} {needle_l} s ≥ 0` is unsatisfiable: the needle {needle_l} is
  ABSENT from the haystack {hay_l} (its concrete `matchAt` fails at every position,
  closed by `decide` on the `List.all` witness), so `str.indexof = -1` for EVERY
  start `m` (`indexOf_absent_all_start`, proved via the constructive
  `filter_all_false` — NO `Classical.choice`), and `-1 ≥ 0` is false. Reconstructed
  from the frontend parsed ASSERTIONS (ay reduces str.indexof eagerly). The symbolic
  start `m` is quantified UNIVERSALLY (`Val = Nat`), so the certificate refutes the
  assertion for every non-negative start; the `indexOf … m = -1` step is closed by
  the absence lemma / `decide`, never `simp`. Pure Lean 4 core; axioms ⊆
  {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.StrIndexofAbsentGe_{hash}
open AySoundness

abbrev Val := Nat

/-- Atom `1 ↦ str.indexof {hay_l} {needle_l} m ≥ 0` (`m` = the symbolic start). -/
def atomVal (m : Val) (k : Nat) : Bool :=
  match k with
  | 1 => decide (IndexOfThy.indexOf {hay_l} {needle_l} m ≥ 0)
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  -- Close `indexOf … m = -1` via the CLASSICAL-FREE absence lemma (NOT `simp`).
  have h1 : IndexOfThy.indexOf {hay_l} {needle_l} m = -1 :=
    IndexOfThy.indexOf_absent_all_start {hay_l} {needle_l} (by decide) m
  have ha : atomVal m 1 = false := by
    simp only [atomVal, h1]
    decide
  simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No start makes the absent needle's `str.indexof` non-negative — via the
    firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

-- verify: axioms ⊆ {{propext, Quot.sound}} (NO Classical.choice)
#print axioms no_model

end AySoundness.Emitted.StrIndexofAbsentGe_{hash}
"#,
    );
    (rendered.len() <= max_source_bytes.min(MAX_INDEXOF_FIREWALL_SOURCE_BYTES)).then_some(rendered)
}

/// Emit a verified-firewall Lean certificate for a `str.indexof`-ABSENT
/// `str.is_digit ∘ str.from_int` conflict among the PARSED assertions:
/// `(str.is_digit (str.from_int (str.indexof T W k)))` where the haystack `T` and
/// needle `W` resolve to ground string LITERALS (through transitive `(= sym
/// literal)` / `(= sym sym')` aliases — e.g. `v = "cba"`, `v = t`) and `W` is
/// genuinely ABSENT from `T`. Asserting the predicate TRUE is unsatisfiable: the
/// index is `-1`, `str.from_int (-1) = ""`, and `str.is_digit "" = false`.
///
/// Grounded in the verified, CLASSICAL-FREE `IndexOfThy.indexOf_absent_all_start`
/// (`∀ m, indexOf T W m = -1`, via `by decide` — NOT `simp`); the residual
/// `str.is_digit (str.from_int (-1)) = false` is a ground `decide`. Cf. the
/// hand-checked witness `IndexOfThy.str_indexof_is_digit_false`. The symbolic start
/// `m` is quantified UNIVERSALLY (`Val = Nat`). `Ok(None)` unless `T`/`W` are
/// ground literals and `W` is genuinely absent from `T`; `Err(())` reports a
/// resource fence to the bounded batch collector.
pub(crate) fn emit_str_indexof_is_digit_firewall_lean_from_parsed(
    parsed: &[PTerm],
    max_source_bytes: usize,
) -> Result<Option<String>, ()> {
    let str_binds = collect_str_binds(parsed).ok_or(())?;
    for asrt in parsed {
        // `(str.is_digit (str.from_int (str.indexof T W k)))`.
        let PTerm::App(dop, dargs) = asrt else {
            continue;
        };
        if dop != "str.is_digit" || dargs.len() != 1 {
            continue;
        }
        let PTerm::App(fop, fargs) = &dargs[0] else {
            continue;
        };
        if fop != "str.from_int" || fargs.len() != 1 {
            continue;
        }
        let PTerm::App(iop, iargs) = &fargs[0] else {
            continue;
        };
        if iop != "str.indexof" || iargs.len() != 3 {
            continue;
        }
        let (Some(hay), Some(needle)) = (
            resolve_str_literal(&iargs[0], &str_binds),
            resolve_str_literal(&iargs[1], &str_binds),
        ) else {
            continue;
        };
        if !needle_absent(hay, needle).ok_or(())? {
            continue;
        }
        let (hay_l, needle_l) =
            bounded_indexof_codelists(hay, needle, max_source_bytes).ok_or(())?;
        let rendered =
            render_str_indexof_is_digit_lean(&hay_l, &needle_l, max_source_bytes).ok_or(())?;
        return Ok(Some(rendered));
    }
    Ok(None)
}

/// Render the `str.indexof`-ABSENT `str.is_digit ∘ str.from_int` firewall Lean.
/// Grounds `IndexOfThy.indexOf_absent_all_start` (CLASSICAL-FREE) through the
/// verified `firewall_combined_unsat` over `Val = Nat`; the residual
/// `str.is_digit (str.from_int (-1)) = false` closes by ground `decide`.
fn render_str_indexof_is_digit_lean(
    hay_l: &str,
    needle_l: &str,
    max_source_bytes: usize,
) -> Option<String> {
    let hash = fnv_hex(&format!("indexofisdigit:{hay_l}:{needle_l}"));
    let rendered = format!(
        r#"import AySoundness.Firewall
import AySoundness.StringThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — `str.indexof`-ABSENT
  `str.is_digit ∘ str.from_int` conflict, grounded in the verified, CLASSICAL-FREE
  `IndexOfThy.indexOf_absent_all_start` (cf. the hand-checked witness
  `IndexOfThy.str_indexof_is_digit_false`). The assertion
  `str.is_digit (str.from_int (str.indexof {hay_l} {needle_l} k))` is unsatisfiable:
  the needle {needle_l} is ABSENT from the haystack {hay_l} (its concrete `matchAt`
  fails everywhere, closed by `decide`), so `str.indexof = -1` for EVERY start `m`
  (`indexOf_absent_all_start`, via the constructive `filter_all_false` — NO
  `Classical.choice`), `str.from_int (-1) = ""`, and `str.is_digit "" = false`.
  Reconstructed from the frontend parsed ASSERTIONS, resolving the string aliases
  transitively (ay reduces str.indexof / str.from_int / str.is_digit eagerly). The
  symbolic start `m` is quantified UNIVERSALLY (`Val = Nat`); the `indexOf … m = -1`
  step is closed by the absence lemma, never `simp`. Pure Lean 4 core; axioms ⊆
  {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.StrIndexofIsDigit_{hash}
open AySoundness

abbrev Val := Nat

/-- Atom `1 ↦ str.is_digit (str.from_int (str.indexof {hay_l} {needle_l} m))`. -/
def atomVal (m : Val) (k : Nat) : Bool :=
  match k with
  | 1 => IndexOfThy.isDigit (IndexOfThy.fromInt (IndexOfThy.indexOf {hay_l} {needle_l} m))
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  -- Close `indexOf … m = -1` via the CLASSICAL-FREE absence lemma (NOT `simp`).
  have h1 : IndexOfThy.indexOf {hay_l} {needle_l} m = -1 :=
    IndexOfThy.indexOf_absent_all_start {hay_l} {needle_l} (by decide) m
  have ha : atomVal m 1 = false := by
    simp only [atomVal, h1]
    decide
  simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No start makes the absent needle's `str.indexof` a digit through
    `str.from_int` — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

-- verify: axioms ⊆ {{propext, Quot.sound}} (NO Classical.choice)
#print axioms no_model

end AySoundness.Emitted.StrIndexofIsDigit_{hash}
"#,
    );
    (rendered.len() <= max_source_bytes.min(MAX_INDEXOF_FIREWALL_SOURCE_BYTES)).then_some(rendered)
}

// ==== APPENDED BUCKET: b_sets.rs ====
// STRUCTURAL ground-set (QF_SETLIA) firewall emitters + shared helpers.

/// A ground integer literal (`n` or `(- n)`) -> its `i64` value. `None` on any
/// non-literal / non-ground operand (fail-closed).
fn parsed_set_int_lit(t: &PTerm) -> Option<i64> {
    match t {
        PTerm::Const(PConst::Numeral(n)) => n.parse::<i64>().ok(),
        PTerm::App(op, args) if op == "-" && args.len() == 1 => {
            parsed_set_int_lit(&args[0]).map(|v| -v)
        }
        _ => None,
    }
}

/// Structurally evaluate a GROUND QF_SETLIA set term -- `set.singleton n`->`{n}`,
/// `set.insert n s`->`{n} u eval(s)`, `set.empty` / `(as set.empty ...)`->`{}`
/// over integer literals -- into its finite element set. Returns `None` on any
/// non-ground / variable / unsupported operand (fail-closed: the emitter then
/// DECLINES and the core still refuses the unverified proof, preserving
/// soundness). Used both to VERIFY the conflict really holds before emitting and
/// to pick the disequality witness.
fn eval_set_pterm(t: &PTerm) -> Option<std::collections::BTreeSet<i64>> {
    use std::collections::BTreeSet;
    match t {
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("set.singleton", 1) => {
                let n = parsed_set_int_lit(&args[0])?;
                Some(BTreeSet::from([n]))
            }
            ("set.insert", 2) => {
                let n = parsed_set_int_lit(&args[0])?;
                let mut s = eval_set_pterm(&args[1])?;
                s.insert(n);
                Some(s)
            }
            ("set.empty", 0) => Some(BTreeSet::new()),
            ("as", 2) => match &args[0] {
                PTerm::Symbol(s) if s == "set.empty" => Some(BTreeSet::new()),
                _ => None,
            },
            _ => None,
        },
        PTerm::Symbol(s) if s == "set.empty" => Some(BTreeSet::new()),
        _ => None,
    }
}

/// Render a GROUND QF_SETLIA set term as its `AySoundness.SetThy` tower
/// (`SetThy.singleton`/`SetThy.insert`/`SetThy.emptyS`). `None` on any
/// non-structural operand (kept in lockstep with [`eval_set_pterm`]).
fn render_set_term_lean(t: &PTerm) -> Option<String> {
    fn lit(n: i64) -> String {
        if n < 0 {
            format!("({n})")
        } else {
            n.to_string()
        }
    }
    match t {
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("set.singleton", 1) => {
                let n = parsed_set_int_lit(&args[0])?;
                Some(format!("(SetThy.singleton {})", lit(n)))
            }
            ("set.insert", 2) => {
                let n = parsed_set_int_lit(&args[0])?;
                let s = render_set_term_lean(&args[1])?;
                Some(format!("(SetThy.insert {} {})", lit(n), s))
            }
            ("set.empty", 0) => Some("SetThy.emptyS".to_string()),
            ("as", 2) => match &args[0] {
                PTerm::Symbol(s) if s == "set.empty" => Some("SetThy.emptyS".to_string()),
                _ => None,
            },
            _ => None,
        },
        PTerm::Symbol(s) if s == "set.empty" => Some("SetThy.emptyS".to_string()),
        _ => None,
    }
}

/// A Lean integer literal for a witness element (parenthesise negatives).
fn set_witness_lean(n: i64) -> String {
    if n < 0 {
        format!("({n})")
    } else {
        n.to_string()
    }
}

/// (1) `(not (set.subset S T))` with eval(S) subseteq eval(T): a VALID subset
/// asserted NEGATED, hence UNSAT. Grounds `SetThy.subset` (gap-1 == sub_1_01).
pub(crate) fn emit_set_subset_structural_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    for asrt in parsed {
        let PTerm::App(nop, nargs) = asrt else {
            continue;
        };
        if nop != "not" || nargs.len() != 1 {
            continue;
        }
        let PTerm::App(sop, sargs) = &nargs[0] else {
            continue;
        };
        if sop != "set.subset" || sargs.len() != 2 {
            continue;
        }
        let (s, t) = (&sargs[0], &sargs[1]);
        let (Some(es), Some(et)) = (eval_set_pterm(s), eval_set_pterm(t)) else {
            continue;
        };
        if !es.is_subset(&et) {
            continue;
        }
        let (Some(sl), Some(tl)) = (render_set_term_lean(s), render_set_term_lean(t)) else {
            continue;
        };
        return Some(render_set_subset_structural_lean(
            &sl,
            &tl,
            fnv_hex(&format!("setsubstruct:{asrt:?}")),
        ));
    }
    None
}

/// (2) `(= S T)` with eval(S) != eval(T): a FALSE set-equality, hence UNSAT.
/// Grounds `SetThy.seteq` at a symmetric-difference witness (gap-2 == sing_0_ne_1).
pub(crate) fn emit_set_eq_structural_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        let (s, t) = (&args[0], &args[1]);
        let (Some(es), Some(et)) = (eval_set_pterm(s), eval_set_pterm(t)) else {
            continue;
        };
        if es == et {
            continue;
        }
        let Some(&w) = es.symmetric_difference(&et).next() else {
            continue;
        };
        let (Some(sl), Some(tl)) = (render_set_term_lean(s), render_set_term_lean(t)) else {
            continue;
        };
        return Some(render_set_eq_structural_lean(
            &sl,
            &tl,
            w,
            fnv_hex(&format!("seteqstruct:{asrt:?}")),
        ));
    }
    None
}

/// (3) positive `(set.subset S T)` with eval(S) not-subseteq eval(T): a FALSE
/// subset asserted POSITIVELY, hence UNSAT. Grounds `SetThy.subset` at a witness
/// w in S\T (gap-3 == not_sub_0_1).
pub(crate) fn emit_set_subset_structural_false_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "set.subset" || args.len() != 2 {
            continue;
        }
        let (s, t) = (&args[0], &args[1]);
        let (Some(es), Some(et)) = (eval_set_pterm(s), eval_set_pterm(t)) else {
            continue;
        };
        if es.is_subset(&et) {
            continue;
        }
        let Some(&w) = es.difference(&et).next() else {
            continue;
        };
        let (Some(sl), Some(tl)) = (render_set_term_lean(s), render_set_term_lean(t)) else {
            continue;
        };
        return Some(render_set_subset_structural_false_lean(
            &sl,
            &tl,
            w,
            fnv_hex(&format!("setsubstructfalse:{asrt:?}")),
        ));
    }
    None
}

fn render_set_subset_structural_lean(sl: &str, tl: &str, hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
import AySoundness.SetThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) -- STRUCTURAL set-subset conflict grounded
  in the verified `firewall_combined_unsat`. `not (S subseteq T)` over the concrete
  finite sets `S = {sl}`, `T = {tl}` is unsatisfiable: `SetThy.subset S T` genuinely
  holds, so its negation has no model. Reconstructed from the frontend parsed
  ASSERTIONS. Sets are the characteristic-function model `Int -> Bool`; `subset` is
  the forall-implication (atom noncomputable via `Classical.propDecidable`). Pure
  Lean 4 core; axioms subseteq {{propext, Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.SetSubStruct_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

abbrev Val := Unit

/-- Atom `1 ↦ subset S T`. -/
noncomputable def atomVal (_m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (SetThy.subset {sl} {tl})
  | _ => false

def original : List (Cid × Clause) := [(1, [-1])]
def lemmas   : List (Cid × Clause) := [(2, [1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [1] = true := by
  have h : SetThy.subset {sl} {tl} := by
    intro x hx
    simp only [SetThy.mem, SetThy.singleton, SetThy.insert, SetThy.emptyS,
      decide_eq_true_eq, Bool.or_eq_true, Bool.false_eq_true, or_false] at *
    omega
  simp [clauseSat, litSat, atomVal, h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.SetSubStruct_{hash}
"#,
    )
}

fn render_set_eq_structural_lean(sl: &str, tl: &str, w: i64, hash: String) -> String {
    let wl = set_witness_lean(w);
    format!(
        r#"import AySoundness.Firewall
import AySoundness.SetThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) -- STRUCTURAL set-equality conflict grounded
  in the verified `firewall_combined_unsat`. `S = T` over the concrete finite sets
  `S = {sl}`, `T = {tl}` is unsatisfiable: they differ at `{wl}` (mem {wl} S != mem
  {wl} T), so `SetThy.seteq S T` fails and by `seteq_iff` the equality cannot hold.
  Sets are `Int -> Bool`; axioms subseteq {{propext, Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.SetEqStruct_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

abbrev Val := Unit

/-- Atom `1 ↦ seteq S T`. -/
noncomputable def atomVal (_m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (SetThy.seteq {sl} {tl})
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have h : ¬ SetThy.seteq {sl} {tl} := by
    intro hs
    exact absurd (hs {wl}) (by decide)
  simp [clauseSat, litSat, atomVal, h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.SetEqStruct_{hash}
"#,
    )
}

fn render_set_subset_structural_false_lean(sl: &str, tl: &str, w: i64, hash: String) -> String {
    let wl = set_witness_lean(w);
    format!(
        r#"import AySoundness.Firewall
import AySoundness.SetThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) -- STRUCTURAL false-subset conflict grounded
  in the verified `firewall_combined_unsat`. `S subseteq T` over the concrete finite
  sets `S = {sl}`, `T = {tl}` is unsatisfiable: `{wl}` is in S but not in T
  (mem {wl} S = true, mem {wl} T = false), so `SetThy.subset S T` fails. Sets are
  `Int -> Bool`; axioms subseteq {{propext, Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.SetSubStructFalse_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

abbrev Val := Unit

/-- Atom `1 ↦ subset S T`. -/
noncomputable def atomVal (_m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (SetThy.subset {sl} {tl})
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  have h : ¬ SetThy.subset {sl} {tl} := by
    intro hs
    exact absurd (hs {wl} (by decide)) (by decide)
  simp [clauseSat, litSat, atomVal, h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.SetSubStructFalse_{hash}
"#,
    )
}

// ==== APPENDED BUCKET: b_arrays.rs ====
/// Scalar-leaf name for array-index normalization: a bare `Symbol`, a nullary
/// application, or a literal `Const`. This is the String-returning leaf extractor
/// the arith-normalizer below bottoms out at. (Origin refactored the executor's
/// own `nested_scalar_name` into the richer `nested_scalar_key -> NestedScalarKey`;
/// this batch's array emitter only needs the plain-name form, kept local here.)
fn nested_scalar_name(t: &PTerm) -> Option<String> {
    match t {
        PTerm::Symbol(s) => Some(s.clone()),
        PTerm::App(f, args) if args.is_empty() => Some(f.clone()),
        PTerm::Const(c) => Some(format!("{c:?}")),
        _ => None,
    }
}

/// Arith-normalize an array INDEX term to a canonical scalar name, stripping
/// the identity offsets `(+ x 0)` / `(+ 0 x)` / `(- x 0)` that a frontend may
/// leave on a read index (e.g. `(select (store a i v) (+ i 0))`, where `i+0 ≡ i`
/// so the read still lands on the stored slot). Bottoms out at
/// `nested_scalar_name` (Symbol / nullary app / literal). `None` for any other
/// compound index — fail closed, the emitter then declines.
fn arith_normalize_scalar_name(t: &PTerm) -> Option<String> {
    match t {
        PTerm::App(op, args) if op == "+" && args.len() == 2 => {
            match (parsed_numeral(&args[0]), parsed_numeral(&args[1])) {
                (Some(0), _) => arith_normalize_scalar_name(&args[1]),
                (_, Some(0)) => arith_normalize_scalar_name(&args[0]),
                _ => None,
            }
        }
        PTerm::App(op, args) if op == "-" && args.len() == 2 => match parsed_numeral(&args[1]) {
            Some(0) => arith_normalize_scalar_name(&args[0]),
            _ => None,
        },
        _ => nested_scalar_name(t),
    }
}

/// Emit a verified-firewall Lean proof for a POSITIVE-literal read-over-write-SAME
/// MISMATCH found among the PARSED assertions: `(= (select (store a i v) ridx) w)`
/// where `ridx` arith-normalizes to the store index `i` and `v`, `w` are DISTINCT
/// non-negative integer literals. By the McCarthy ROW-same axiom
/// `select (store a i v) i = v`, the read yields `v`; asserting it equals a
/// different literal `w` is unsatisfiable (`v ≠ w`). ay refutes arrays eagerly
/// (bare-trust), so the structure is recovered from the frontend assertions.
///
/// This is the positive-polarity dual of `emit_array_row1_firewall_lean_from_parsed`
/// (which handles the NEGATED shape `select … i ≠ v`): here the conflict comes not
/// from the polarity but from the two distinct concrete values, so the stored value
/// and the read target are rendered as literal `Nat`s (making `v = w` decidably
/// false) rather than opaque scalars. Grounded through the same verified
/// `firewall_combined_unsat` over the functional array model `(Nat → Nat) × (Nat →
/// Nat)` with `store` inlined as an `if`-update; the same ArrayThy `sel_upd_same`
/// fact the ROW1/nested emitters use. Pure Lean 4 core.
///
/// Fail-closed: declines (`None`) unless a single-store `select` whose read index
/// arith-normalizes to the store index carries two DISTINCT non-negative integer
/// literals. Matching values (`v = w`) is SAT — declined. No verdict/clause change.
pub(crate) fn emit_array_row_mismatch_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    for asrt in parsed {
        // Positive top-level equality `(= SEL LIT)` — NOT wrapped in `not`.
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        for (sel, lit) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            // Read-target `w`: a non-negative integer literal.
            let Some(w) = parsed_numeral(lit) else {
                continue;
            };
            if w < 0 {
                continue;
            }
            // SEL = (select (store a i v) ridx).
            let PTerm::App(s1, sargs) = sel else { continue };
            if s1 != "select" || sargs.len() != 2 {
                continue;
            }
            let (store_t, ridx) = (&sargs[0], &sargs[1]);
            let PTerm::App(s2, stargs) = store_t else {
                continue;
            };
            if s2 != "store" || stargs.len() != 3 {
                continue;
            }
            let (_a, sidx, sval) = (&stargs[0], &stargs[1], &stargs[2]);
            // Read index must arith-normalize to the SAME scalar as the store
            // index (ROW-same); else this is a ROW-OTHER shape, not this emitter's.
            let (Some(rname), Some(sname)) = (
                arith_normalize_scalar_name(ridx),
                arith_normalize_scalar_name(sidx),
            ) else {
                continue;
            };
            if rname != sname {
                continue;
            }
            // Stored value `v`: a non-negative integer literal, DISTINCT from `w`.
            let Some(v) = parsed_numeral(sval) else {
                continue;
            };
            if v < 0 || v == w {
                continue;
            }
            return Some(render_array_row_mismatch_lean(
                v as u64,
                w as u64,
                fnv_hex(&format!("rowmismatch:{asrt:?}")),
            ));
        }
    }
    None
}

/// Recursively substitute a parsed term under an array-variable definition map.
fn subst_array_def_pterm(t: &PTerm, defs: &[(String, PTerm)]) -> PTerm {
    match t {
        PTerm::Symbol(s) => defs
            .iter()
            .find(|(n, _)| n == s)
            .map(|(_, rep)| rep.clone())
            .unwrap_or_else(|| t.clone()),
        PTerm::App(op, args) => PTerm::App(
            op.clone(),
            args.iter()
                .map(|a| subst_array_def_pterm(a, defs))
                .collect(),
        ),
        other => other.clone(),
    }
}

/// Inline array-variable definitions of the form `(= v (store …))` /
/// `(= (store …) v)` (v a Symbol bound to a `store`-chain) throughout the OTHER
/// assertions, dropping the defining equality. Substituting an asserted equality
/// preserves (un)satisfiability, so this is a SOUND rewrite; it exposes the
/// `select (store …)` structure otherwise hidden behind an array-let (e.g. a swap
/// `b = store (store a i (select a j)) j (select a i)`, then `select b i`). Returns
/// the assertions unchanged when no such definition is present.
fn inline_array_store_defs(parsed: &[PTerm]) -> Vec<PTerm> {
    let mut defs: Vec<(String, PTerm)> = Vec::new();
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        for (a, b) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            if let PTerm::Symbol(s) = a {
                if matches!(b, PTerm::App(o, ba) if o == "store" && ba.len() == 3)
                    && !defs.iter().any(|(n, _)| n == s)
                {
                    defs.push((s.clone(), b.clone()));
                }
            }
        }
    }
    if defs.is_empty() {
        return parsed.to_vec();
    }
    let is_def = |asrt: &PTerm| -> bool {
        matches!(asrt, PTerm::App(op, args) if op == "=" && args.len() == 2
        && defs.iter().any(|(n, _)| {
            matches!(&args[0], PTerm::Symbol(s) if s == n)
                || matches!(&args[1], PTerm::Symbol(s) if s == n)
        }))
    };
    parsed
        .iter()
        .filter(|a| !is_def(a))
        .map(|a| subst_array_def_pterm(a, &defs))
        .collect()
}

/// Emit a verified-firewall Lean proof for a nested / multi-`store` array
/// read-over-write conflict whose `select` targets are hidden behind an ARRAY-LET
/// binding `(= b (store …))` — e.g. an element swap
/// `b = store (store a i (select a j)) j (select a i)` with `i ≠ j` and
/// `select b i ≠ select a j`. Inlines the array-let (a sound equality
/// substitution) and delegates to
/// `emit_array_nested_store_row_firewall_lean_from_parsed`, which grounds the
/// composed McCarthy `sel_upd_same`/`sel_upd_other` conflict in the same verified
/// `firewall_combined_unsat`. `None` when no array-let is present (the plain
/// nested emitter already covers that) or the inlined form does not reduce to a
/// backed nested read-over-write conflict — fail closed.
pub(crate) fn emit_array_inlined_nested_store_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    let inlined = inline_array_store_defs(parsed);
    if inlined.as_slice() == parsed {
        // No array-let inlined; nothing this wrapper adds over the plain emitter.
        return None;
    }
    // After substituting the array-let, the `select (store …)` structure is
    // exposed: try the nested emitter first (guarded or unconditional), then the
    // reflexive single-store ROW1 / ROW1-MISMATCH shapes it does not model (a bare
    // `select (store a i e) i = e` collapses to a plain ROW1 with an empty guard,
    // and a positive `select (store a i v) i = w` with `v ≠ w` is a ROW1 mismatch).
    // Each delegate independently grounds the same verified firewall; the first
    // Some wins. Fail closed when none fires.
    emit_array_nested_store_row_firewall_lean_from_parsed(&inlined)
        .or_else(|| emit_array_row1_firewall_lean_from_parsed(&inlined))
        .or_else(|| emit_array_row_mismatch_firewall_lean_from_parsed(&inlined))
}

/// Recursively substitute nullary `define-fun` macro bodies (`name → body`) into
/// a parsed term to a fixpoint. `assertions_parsed()` retains macros UNEXPANDED
/// (`(select fwd i0)` with `fwd` a `define-fun`), so this exposes the underlying
/// `store`-chain for the array recognizers. Macro bodies may reference other
/// macros (`(define-fun f1 () _ (store f0 …))`), hence the bounded fixpoint;
/// substituting a definitionally-equal body is a SOUND rewrite. The iteration cap
/// guards against pathological chains (plain `define-fun` is non-recursive, so a
/// well-formed input always converges well within it).
fn expand_nullary_defs(t: &PTerm, defs: &[(String, PTerm)]) -> PTerm {
    fn subst_once(t: &PTerm, defs: &[(String, PTerm)]) -> PTerm {
        match t {
            PTerm::Symbol(s) => defs
                .iter()
                .find(|(n, _)| n == s)
                .map(|(_, body)| body.clone())
                .unwrap_or_else(|| t.clone()),
            // A macro used as a nullary application `(fwd)` — substitute the body.
            PTerm::App(op, args) if args.is_empty() => defs
                .iter()
                .find(|(n, _)| n == op)
                .map(|(_, body)| body.clone())
                .unwrap_or_else(|| t.clone()),
            PTerm::App(op, args) => PTerm::App(
                op.clone(),
                args.iter().map(|a| subst_once(a, defs)).collect(),
            ),
            other => other.clone(),
        }
    }
    let mut cur = t.clone();
    for _ in 0..64 {
        let next = subst_once(&cur, defs);
        if next == cur {
            return cur;
        }
        cur = next;
    }
    cur
}

/// Emit a verified-firewall Lean proof for an array read-over-write conflict whose
/// `select`/`store` structure is hidden behind nullary `define-fun` MACROS — the
/// QF_AX store-commute shape `(define-fun fwd () _ (store … i0 e0 …))`,
/// `(define-fun rev () _ (store … in-reverse …))`,
/// `(not (= (select fwd i0) (select rev i0)))` with `(distinct i0 …)`. The frontend
/// retains such macros unexpanded in `assertions_parsed()`, so substitute their
/// (definitionally-equal) bodies, then delegate to the nested / ROW1 / ROW-mismatch
/// emitters, which ground the composed McCarthy conflict in the same verified
/// `firewall_combined_unsat`. `None` when no macro actually expands (the plain
/// emitters already cover that) or the expanded form does not reduce to a
/// groundable conflict — fail closed.
pub(crate) fn emit_array_defexpanded_firewall_lean_from_parsed(
    parsed: &[PTerm],
    defs: &[(String, PTerm)],
) -> Option<String> {
    if defs.is_empty() {
        return None;
    }
    let expanded: Vec<PTerm> = parsed
        .iter()
        .map(|a| expand_nullary_defs(a, defs))
        .collect();
    if expanded.as_slice() == parsed {
        // No macro expanded; nothing this wrapper adds over the plain emitters.
        return None;
    }
    emit_array_nested_store_row_firewall_lean_from_parsed(&expanded)
        .or_else(|| emit_array_store_commute_firewall_lean_from_parsed(&expanded))
        .or_else(|| emit_array_inlined_nested_store_firewall_lean_from_parsed(&expanded))
        .or_else(|| emit_array_row1_firewall_lean_from_parsed(&expanded))
        .or_else(|| emit_array_row_mismatch_firewall_lean_from_parsed(&expanded))
}

fn render_array_row_mismatch_lean(v: u64, w: u64, hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — array read-over-write-SAME MISMATCH,
  grounded in the verified `firewall_combined_unsat`. The assertion
  `select (store a i v) i = w` (with `v ≠ w`) contradicts the McCarthy ROW-same
  axiom `select (store a i v) i = v` (holds for ALL a, i, v): the read yields `v`,
  not `w`. Reconstructed from the frontend assertions (ay refutes arrays eagerly as
  bare-trust); the read index is arith-normalized (`i + 0 ≡ i`). Model:
  `(Nat → Nat) × (Nat → Nat)` = array × scalar valuation (`i = m.2 0`); `store` is
  an `if`-update; `select (store …) i` reduces to `v` since `i = i`, and the two
  distinct literals `v = {v}`, `w = {w}` make the equality decidably false. Pure
  Lean 4 core.
-/
namespace AySoundness.Emitted.ArrRowMismatch_{hash}
open AySoundness

abbrev Val := (Nat → Nat) × (Nat → Nat)

-- atom 1 = (select (store a i {v}) i = {w}) = (if i = i then {v} else a i) = {w}.
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((if (m.2 0) = (m.2 0) then ({v} : Nat) else (m.1 (m.2 0))) = ({w} : Nat))
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- `select (store a i {v}) i = {w}` (with `{v} ≠ {w}`) is unsatisfiable — via the
    firewall (ROW-same). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrRowMismatch_{hash}
"#,
    )
}

/// View a term as a `(store base idx val)` application.
fn as_store_app(t: &PTerm) -> Option<(&PTerm, &PTerm, &PTerm)> {
    match t {
        PTerm::App(op, args) if op == "store" && args.len() == 3 => {
            Some((&args[0], &args[1], &args[2]))
        }
        _ => None,
    }
}

/// View a term as a `(select base idx)` application.
fn as_select_app(t: &PTerm) -> Option<(&PTerm, &PTerm)> {
    match t {
        PTerm::App(op, args) if op == "select" && args.len() == 2 => Some((&args[0], &args[1])),
        _ => None,
    }
}

/// Recognize a WRITE-BACK IDENTITY store-chain over a single named base array
/// `a`: `store (store … (store a k₁ (select a k₁)) …) kₙ (select a kₙ)`. Every
/// store level writes back the base array's OWN value at that index
/// (`(select a kᵢ)` with the select base = the chain's base and the select index
/// = the store index), so the whole chain equals `a` pointwise. Returns
/// `(base_name, index_names)` with the index names OUTER-first, or `None` if the
/// term is not a pure write-back chain over one base with distinct index names.
fn array_writeback_chain(t: &PTerm) -> Option<(String, Vec<String>)> {
    match t {
        PTerm::Symbol(s) => Some((s.clone(), Vec::new())),
        PTerm::App(f, args) if args.is_empty() => Some((f.clone(), Vec::new())),
        _ => {
            let (inner, idx, val) = as_store_app(t)?;
            let idx_name = nested_scalar_name(idx)?;
            // val must be `(select <sb> <sidx>)` with sidx == this store index.
            let (sb, sidx) = as_select_app(val)?;
            if nested_scalar_name(sidx)? != idx_name {
                return None;
            }
            let sb_name = nested_scalar_name(sb)?;
            let (base, mut inner_idxs) = array_writeback_chain(inner)?;
            // The written-back value must reference the CHAIN BASE, not an
            // intermediate array — that is exactly the write-back identity.
            if sb_name != base {
                return None;
            }
            let mut idxs = vec![idx_name];
            idxs.append(&mut inner_idxs);
            Some((base, idxs))
        }
    }
}

/// Emit a verified-firewall Lean proof for an array WRITE-BACK IDENTITY CHAIN
/// conflict: `(not (= CHAIN a))` where `CHAIN` is `store (store … (store a k₁
/// (select a k₁)) …) kₙ (select a kₙ)` — every level writes the base array's own
/// value back at its index, so `CHAIN = a` in EVERY model, contradicting the
/// asserted `CHAIN ≠ a`. This is the store-forwarding chain that ay's frontend
/// hides behind nullary `define-fun` macros (`storeinv_sf_chain`): expanding the
/// macros exposes the chain, which ay refutes eagerly (bare trust) with no array
/// theory-lemma clause to ground.
///
/// Grounding: the standard functional array model `(Nat → Nat) × (Nat → Nat)`
/// (base array × scalar valuation); `store` inlines to nested `if`-updates and
/// the write-back identity `store a k (select a k) = a` is discharged by
/// `funext` + `by_cases` on each index (the same content as
/// `AySoundness.ArrayThy.ext_nonvacuous`), composed through the verified
/// `firewall_combined_unsat`. The array-equality atom uses
/// `Classical.propDecidable` (so `atomVal` is `noncomputable`); axioms of the
/// emitted `no_model` are ⊆ {propext, Classical.choice, Quot.sound}.
///
/// Fail-closed: declines unless some assertion is `(not (= CHAIN a))` /
/// `(not (= a CHAIN))` with `CHAIN` a non-empty write-back chain over the base
/// symbol `a` and DISTINCT store-index names. No verdict/clause change on decline.
pub(crate) fn emit_array_writeback_chain_firewall_lean_from_parsed(
    parsed: &[PTerm],
    defs: &[(String, PTerm)],
) -> Option<String> {
    let expanded: Vec<PTerm> = parsed
        .iter()
        .map(|a| expand_nullary_defs(a, defs))
        .collect();
    let inlined = inline_array_store_defs(&expanded);
    for asrt in &inlined {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "not" || args.len() != 1 {
            continue;
        }
        let PTerm::App(eq, ea) = &args[0] else {
            continue;
        };
        if eq != "=" || ea.len() != 2 {
            continue;
        }
        for (chain_t, base_t) in [(&ea[0], &ea[1]), (&ea[1], &ea[0])] {
            let Some((base, idxs)) = array_writeback_chain(chain_t) else {
                continue;
            };
            if idxs.is_empty() {
                continue; // `(not (= a a))` — not a write-back chain.
            }
            // The other side must be exactly the base array symbol.
            if nested_scalar_name(base_t).as_deref() != Some(base.as_str()) {
                continue;
            }
            // Distinct store-index names keep the per-level `by_cases` guards
            // syntactically independent.
            let mut seen = std::collections::HashSet::new();
            if !idxs.iter().all(|n| seen.insert(n.clone())) {
                continue;
            }
            return Some(render_array_writeback_chain_lean(
                idxs.len(),
                fnv_hex(&format!("writeback:{asrt:?}")),
            ));
        }
    }
    None
}

/// Render the write-back-identity-chain firewall Lean for `n` store levels
/// (valuation indices `0..n-1`, OUTER→INNER). The nested `if`-update tree and its
/// `funext`+`by_cases` discharge are generated from `n`; the model components are
/// opaque, so only `n` and the namespace hash vary.
fn render_array_writeback_chain_lean(n: usize, hash: String) -> String {
    // Nested `if`-update tree: outermost level 0 first, bottoming at `m.1 x`.
    fn nested_if(k: usize, n: usize) -> String {
        if k == n {
            "m.1 x".to_string()
        } else {
            format!(
                "(if x = (m.2 {k}) then m.1 (m.2 {k}) else {})",
                nested_if(k + 1, n)
            )
        }
    }
    // `by_cases` cascade; the returned first line carries NO leading indent (the
    // caller / parent bullet supplies it), subsequent lines use `indent`.
    fn cases(k: usize, n: usize, indent: usize) -> String {
        let sp = " ".repeat(indent);
        let li = k - 1;
        let then_hint = if k == 1 {
            String::new()
        } else {
            let hs: Vec<String> = (1..k).map(|i| format!("h{i}")).collect();
            format!(" [{}]", hs.join(", "))
        };
        let then_line = format!("{sp}· subst h{k}; simp{then_hint}");
        let else_line = if k == n {
            let hs: Vec<String> = (1..=n).map(|i| format!("h{i}")).collect();
            format!("{sp}· simp [{}]", hs.join(", "))
        } else {
            format!("{sp}· {}", cases(k + 1, n, indent + 2))
        };
        format!("by_cases h{k} : x = (m.2 {li})\n{then_line}\n{else_line}")
    }
    let bigif = nested_if(0, n);
    let proof_tree = format!("    {}", cases(1, n, 4));
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — array WRITE-BACK IDENTITY CHAIN,
  grounded in the verified `firewall_combined_unsat`. The assertion
  `store (store … (store a k1 (select a k1)) …) kn (select a kn) ≠ a` is
  unsatisfiable: writing back the base array's own value at each index leaves the
  array unchanged, so the chain equals `a` in every model (McCarthy read-over-
  write; the same content as `AySoundness.ArrayThy.ext_nonvacuous`). ay hides the
  chain behind nullary `define-fun` macros and refutes arrays eagerly (bare
  trust), so it is reconstructed from the (macro-expanded) frontend assertions.
  Model: `(Nat -> Nat) x (Nat -> Nat)` = base array x scalar valuation; `store`
  is an `if`-update; the pointwise identity is closed by `funext` + `by_cases`.
  The array-equality atom uses `Classical.propDecidable` (so `atomVal` is
  `noncomputable`); axioms of `no_model` are propext / Classical.choice /
  Quot.sound.
-/
namespace AySoundness.Emitted.ArrWriteBack_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

abbrev Val := (Nat -> Nat) × (Nat -> Nat)

-- atom 1 = (write-back chain = a); each level `store _ k (select a k)` is an
-- `if x = k then a k else …` update, so the whole tree collapses to `a x`.
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((fun x => {bigif}) = m.1)
  | _ => false

def original : List (Cid × Clause) := [(1, [-1])]
def lemmas   : List (Cid × Clause) := [(2, [1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem writeback_lemma_valid (m : Val) : clauseSat (atomVal m) [1] = true := by
  have heq : (fun x => {bigif}) = m.1 := by
    funext x
{proof_tree}
  simp [clauseSat, litSat, atomVal, heq]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact writeback_lemma_valid m

/-- The write-back chain differs from `a` in NO model — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrWriteBack_{hash}
"#,
    )
}

/// Emit a verified-firewall Lean proof for a single-index array STORE-INVERSE
/// (cross-swap) conflict: `(= (store P i (select Q i)) (store Q i (select P i)))`
/// together with `(not (= P Q))`. Equating the two swapped stores forces `P = Q`
/// pointwise — at `i`, `P i = Q i` (the swapped values), and off `i`, `Q j = P j`
/// (the swapped bases) — contradicting `P ≠ Q`. This is `storeinv_cross_1idx`;
/// ay refutes it eagerly with no array theory-lemma clause to ground.
///
/// Grounding: the standard functional model (arrays `Nat → Nat`); `store` inlines
/// to `if`-updates and the disjunctive theory-lemma clause `¬(v0 = v1) ∨ (P = Q)`
/// is discharged by `by_cases` on `P = Q` — the false branch derives `P = Q` from
/// `v0 = v1` by `funext` + `by_cases` on `j = i` (the array `ext` axiom), a
/// contradiction. Composed through the verified `firewall_combined_unsat`; both
/// array-equality atoms use `Classical.propDecidable` (so `atomVal` is
/// `noncomputable`); axioms of `no_model` ⊆ {propext, Classical.choice,
/// Quot.sound}.
///
/// Fail-closed: declines unless some assertion equates a genuine `i`-swap of two
/// DISTINCT base arrays `P`, `Q` and a matching `(not (= P Q))` is present. No
/// verdict/clause change on decline.
pub(crate) fn emit_array_storeinv_swap_firewall_lean_from_parsed(
    parsed: &[PTerm],
    defs: &[(String, PTerm)],
) -> Option<String> {
    // Substitutable array bindings: nullary `define-fun` macros (`defs`) PLUS
    // asserted array-lets `(= v (store …))`. Unlike `inline_array_store_defs`,
    // this keeps a `(= v0 v1)` CONSTRAINT between two let-vars (it is not a
    // binding) and expands BOTH sides — exactly the store-inverse swap equality.
    let mut binds: Vec<(String, PTerm)> = defs.to_vec();
    for asrt in parsed {
        if let PTerm::App(op, args) = asrt {
            if op == "=" && args.len() == 2 {
                for (a, b) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    if let PTerm::Symbol(s) = a {
                        if matches!(b, PTerm::App(o, ba) if o == "store" && ba.len() == 3)
                            && !binds.iter().any(|(n, _)| n == s)
                        {
                            binds.push((s.clone(), b.clone()));
                        }
                    }
                }
            }
        }
    }
    // A pure binding assertion `(= v STORE)` / `(= STORE v)` is dropped; every
    // other assertion is macro/let-expanded to a fixpoint.
    let is_binding = |asrt: &PTerm| -> bool {
        matches!(asrt, PTerm::App(op, args) if op == "=" && args.len() == 2
            && [(&args[0], &args[1]), (&args[1], &args[0])].iter().any(|(a, b)|
                matches!(a, PTerm::Symbol(s) if binds.iter().any(|(n, _)| n == s))
                    && matches!(b, PTerm::App(o, ba) if o == "store" && ba.len() == 3)))
    };
    let inlined: Vec<PTerm> = parsed
        .iter()
        .filter(|a| !is_binding(a))
        .map(|a| expand_nullary_defs(a, &binds))
        .collect();
    // Collect asserted array disequalities `(not (= X Y))` as unordered name pairs.
    let diseqs: Vec<(String, String)> = inlined
        .iter()
        .filter_map(|asrt| {
            let PTerm::App(op, args) = asrt else {
                return None;
            };
            if op != "not" || args.len() != 1 {
                return None;
            }
            let PTerm::App(eq, ea) = &args[0] else {
                return None;
            };
            if eq != "=" || ea.len() != 2 {
                return None;
            }
            Some((nested_scalar_name(&ea[0])?, nested_scalar_name(&ea[1])?))
        })
        .collect();
    let backed = |p: &str, q: &str| {
        diseqs
            .iter()
            .any(|(x, y)| (x == p && y == q) || (x == q && y == p))
    };
    for asrt in &inlined {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "=" || args.len() != 2 {
            continue;
        }
        // args[0] = store(P, i, (select Q i)); args[1] = store(Q, i, (select P i)).
        let (Some((b0, i0, v0)), Some((b1, i1, v1))) =
            (as_store_app(&args[0]), as_store_app(&args[1]))
        else {
            continue;
        };
        let (Some(i0n), Some(i1n)) = (nested_scalar_name(i0), nested_scalar_name(i1)) else {
            continue;
        };
        if i0n != i1n {
            continue; // both stores must write the SAME index.
        }
        let (Some((sb0, si0)), Some((sb1, si1))) = (as_select_app(v0), as_select_app(v1)) else {
            continue;
        };
        // Each written value reads the OTHER base at the same index `i`.
        if nested_scalar_name(si0).as_deref() != Some(i0n.as_str())
            || nested_scalar_name(si1).as_deref() != Some(i0n.as_str())
        {
            continue;
        }
        let (Some(p), Some(q)) = (nested_scalar_name(b0), nested_scalar_name(b1)) else {
            continue;
        };
        let (Some(vp), Some(vq)) = (nested_scalar_name(sb0), nested_scalar_name(sb1)) else {
            continue;
        };
        // Bases swapped: store P writes Q's value, store Q writes P's value.
        if p == q || vp != q || vq != p {
            continue;
        }
        if !backed(&p, &q) {
            continue; // the `P ≠ Q` premise must be asserted.
        }
        return Some(render_array_storeinv_swap_lean(fnv_hex(&format!(
            "storeinv1:{asrt:?}"
        ))));
    }
    None
}

/// Render the single-index store-inverse (cross-swap) firewall Lean. The model
/// (`a1`, `a2`, `i`) is fully opaque, so the body is a constant template up to the
/// namespace hash.
fn render_array_storeinv_swap_lean(hash: String) -> String {
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — single-index array STORE-INVERSE
  (cross-swap), grounded in the verified `firewall_combined_unsat`. The
  assertions `store a2 i (select a1 i) = store a1 i (select a2 i)` and `a1 ≠ a2`
  are unsatisfiable: equating the two index-`i` swaps forces `a1 = a2` pointwise
  (at `i`: `a1 i = a2 i`; off `i`: `a1 j = a2 j`) by the array extensionality
  axiom, contradicting `a1 ≠ a2`. ay refutes arrays eagerly (bare trust), so the
  conflict is reconstructed from the frontend assertions. Model: arrays as
  `Nat -> Nat`; `store` is an `if`-update; the disjunctive theory lemma
  `¬(v0 = v1) ∨ (a1 = a2)` is discharged by `by_cases` + `funext`. Equality atoms
  use `Classical.propDecidable` (so `atomVal` is `noncomputable`); axioms of
  `no_model` are propext / Classical.choice / Quot.sound.
-/
namespace AySoundness.Emitted.ArrStoreInv1_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
  a1 : Nat -> Nat
  a2 : Nat -> Nat
  i : Nat

-- atom 1 = (store a2 i (select a1 i) = store a1 i (select a2 i)); atom 2 = (a1 = a2).
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((fun x => if x = m.i then m.a1 m.i else m.a2 x)
                   = (fun x => if x = m.i then m.a2 m.i else m.a1 x))
  | 2 => decide (m.a1 = m.a2)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [-2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, 2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

theorem storeinv_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2] = true := by
  by_cases h : m.a1 = m.a2
  · simp [clauseSat, litSat, atomVal, h]
  · have hne : ¬ ((fun x => if x = m.i then m.a1 m.i else m.a2 x)
                    = (fun x => if x = m.i then m.a2 m.i else m.a1 x)) := by
      intro heq
      apply h
      funext x
      have hx := congrFun heq x
      by_cases hxi : x = m.i
      · subst hxi; simpa using hx
      · simp [hxi] at hx; exact hx.symm
    simp [clauseSat, litSat, atomVal, hne]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact storeinv_lemma_valid m

/-- The single-index store-inverse with `a1 ≠ a2` has NO model — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrStoreInv1_{hash}
"#,
    )
}

/// Names of nullary `define-fun` macros whose body is a `store` (array-valued),
/// used to gate the LINEAR-INTEGER firewall OFF array-typed macros: a
/// disequality between such array macros (e.g. `storeinv_sf_chain`'s
/// `(not (= a2 a))`) is NOT an integer atom and must not be reconstructed as one.
fn array_valued_def_names(defs: &[(String, PTerm)]) -> std::collections::HashSet<String> {
    defs.iter()
        .filter(|(_, body)| matches!(body, PTerm::App(op, a) if op == "store" && a.len() == 3))
        .map(|(name, _)| name.clone())
        .collect()
}

/// Whether a parsed term mentions any name in `syms` (as a symbol leaf or a
/// nullary/compound application head).
fn term_mentions_name(t: &PTerm, syms: &std::collections::HashSet<String>) -> bool {
    match t {
        PTerm::Symbol(s) => syms.contains(s),
        PTerm::App(f, args) => syms.contains(f) || args.iter().any(|a| term_mentions_name(a, syms)),
        _ => false,
    }
}

// ==== APPENDED BUCKET: b_lia.rs ====
/// Render a parsed LINEAR integer term to a Lean `Int` expression over the model
/// `Val := Nat → Int`, assigning each distinct variable a stable index `(m i)`.
/// Handles `+` (n-ary), binary/unary `-`, `*` with at least one constant operand
/// (linearity — a `var*var` product returns `None`), and Euclidean `mod`/`div` by
/// a constant divisor (rendered `Int.emod`/`Int.ediv`, which `omega` supports).
/// Returns `(expr, references_var)`; `None` on any non-linear or unsupported shape.
fn render_int_lia_parsed(
    t: &PTerm,
    vars: &mut Vec<String>,
    context: &ay_frontend::Context,
) -> Option<(String, bool)> {
    match t {
        PTerm::Symbol(v) => {
            if cbr_is_int_constant(context, v) {
                let idx = vars.iter().position(|x| x == v).unwrap_or_else(|| {
                    vars.push(v.clone());
                    vars.len() - 1
                });
                return Some((format!("(m {idx})"), true));
            }
            // SMT-LIB numerals are non-negative, so a negative literal such as
            // `-1` in `(* -1 v0)` reaches the parser as a SYMBOL. Treat any
            // undeclared symbol whose text is an integer as a constant (matches
            // ay's own lenient elaboration). A declaration wins first: `|-1|`
            // may legally name an Int/Real constant or a function.
            if let Some(val) = firewall_undeclared_i64_symbol_literal(context, v) {
                return Some((format!("({val} : Int)"), false));
            }
            None
        }
        PTerm::Const(PConst::Numeral(n)) => {
            let val: i64 = n.parse().ok()?;
            Some((format!("({val} : Int)"), false))
        }
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("+", k) if k >= 1 => {
                let mut parts = Vec::with_capacity(k);
                let mut refs = false;
                for a in args {
                    let (e, r) = render_int_lia_parsed(a, vars, context)?;
                    parts.push(e);
                    refs |= r;
                }
                Some((format!("({})", parts.join(" + ")), refs))
            }
            ("-", 2) => {
                let (a, ar) = render_int_lia_parsed(&args[0], vars, context)?;
                let (b, br) = render_int_lia_parsed(&args[1], vars, context)?;
                Some((format!("({a} - {b})"), ar || br))
            }
            ("-", 1) => {
                let (a, ar) = render_int_lia_parsed(&args[0], vars, context)?;
                Some((format!("(- {a})"), ar))
            }
            ("*", 2) => {
                let (a, ar) = render_int_lia_parsed(&args[0], vars, context)?;
                let (b, br) = render_int_lia_parsed(&args[1], vars, context)?;
                if ar && br {
                    return None; // nonlinear var*var — omega cannot discharge
                }
                Some((format!("({a} * {b})"), ar || br))
            }
            ("mod", 2) => {
                let (a, ar) = render_int_lia_parsed(&args[0], vars, context)?;
                let (b, br) = render_int_lia_parsed(&args[1], vars, context)?;
                if br {
                    return None; // non-constant modulus — omega supports literals only
                }
                Some((format!("(Int.emod {a} {b})"), ar))
            }
            ("div", 2) => {
                let (a, ar) = render_int_lia_parsed(&args[0], vars, context)?;
                let (b, br) = render_int_lia_parsed(&args[1], vars, context)?;
                if br {
                    return None; // non-constant divisor — omega supports literals only
                }
                Some((format!("(Int.ediv {a} {b})"), ar))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Render a parsed arithmetic comparison `(op lhs rhs)` — `op ∈ {<=,>=,<,>,=}` —
/// to a Lean `Prop` over the `Val := Nat → Int` model. Returns `None` for any
/// non-comparison head, wrong arity, or non-linear side.
fn lia_comparison_atom(
    t: &PTerm,
    vars: &mut Vec<String>,
    context: &ay_frontend::Context,
) -> Option<String> {
    let PTerm::App(op, args) = t else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let lean_op = match op.as_str() {
        "<=" => "≤",
        ">=" => "≥",
        "<" => "<",
        ">" => ">",
        "=" => "=",
        _ => return None,
    };
    let (l, _) = render_int_lia_parsed(&args[0], vars, context)?;
    let (r, _) = render_int_lia_parsed(&args[1], vars, context)?;
    Some(format!("{l} {lean_op} {r}"))
}

/// Emit a verified-firewall Lean proof for a LINEAR-INTEGER conflict
/// reconstructed from the PARSED frontend assertions. ay refutes a jointly
/// integer-UNSAT conjunction of linear (in)equalities with a bare `:rule trust`
/// integer step (ILP/divisibility/tightening) — there is NO `la_generic`
/// theory-lemma clause for the per-step emitter to ground — so the conflict is
/// rebuilt here from `ctx.assertions_parsed()`.
///
/// Recognizer (fail-closed): each assertion must be a linear comparison
/// (`<=,>=,<,>,=` over `+`, binary/unary `-`, `const*var`, `mod`/`div` by a
/// constant), a negated such comparison, or a `distinct` (expanded to pairwise
/// `≠`). Every surface variable must resolve uniquely in `context` as a nullary
/// Int declaration. Any Real/ambiguous/missing variable, `var*var` product,
/// non-arithmetic atom, or `or`/`ite`/`and` propositional structure returns
/// `None`.
///
/// Render: each atom is asserted POSITIVELY (`original`); the single all-negated
/// blocking clause is the `lemmas`; the RUP `proof` resolves to empty. The
/// blocking clause `¬S₁ ∨ … ∨ ¬Sₙ` is discharged by a CONSTRUCTIVE linear case
/// cascade closed by `omega` (a Lean-CORE tactic) — not the exponential
/// `by_cases <;> … <;> omega` of `render_lia_lean`, which explodes on the
/// ~30-atom ring files. Runtime counterpart of the worked instance
/// `FirewallExample.no_x_gt5_lt3`; axioms ⊆ {propext, Quot.sound}.
///
/// `defs` are the nullary `define-fun` bodies: any assertion mentioning an
/// ARRAY-valued (`store`-bodied) macro is NOT a linear-integer atom, so the whole
/// reconstruction declines — otherwise an array disequality like
/// `storeinv_sf_chain`'s `(not (= a2 a))` is mis-modeled as two fresh integer
/// vars and yields an `omega`-unclosable (fail-lake) artifact.
pub(crate) fn emit_lia_firewall_lean_from_parsed(
    parsed: &[PTerm],
    defs: &[(String, PTerm)],
    context: &ay_frontend::Context,
) -> Option<String> {
    // Gate OFF array-typed `define-fun` macros: their (dis)equalities are array,
    // not integer, atoms — reconstructing them as LIA is unsound-looking and
    // fails the kernel check. The array firewalls handle these shapes instead.
    let array_defs = array_valued_def_names(defs);
    if !array_defs.is_empty() && parsed.iter().any(|a| term_mentions_name(a, &array_defs)) {
        return None;
    }
    let mut vars: Vec<String> = Vec::new();
    let mut atoms: Vec<String> = Vec::new();
    for asrt in parsed {
        match asrt {
            // (not <comparison>) → the negated comparison as a single atom.
            PTerm::App(op, args) if op == "not" && args.len() == 1 => {
                let inner = lia_comparison_atom(&args[0], &mut vars, context)?;
                atoms.push(format!("¬ ({inner})"));
            }
            // (distinct t1 t2 …) → pairwise `ti ≠ tj`, each a positive atom.
            PTerm::App(op, args) if op == "distinct" && args.len() >= 2 => {
                let rendered: Vec<String> = args
                    .iter()
                    .map(|a| render_int_lia_parsed(a, &mut vars, context).map(|(expr, _)| expr))
                    .collect::<Option<Vec<_>>>()?;
                for i in 0..rendered.len() {
                    for j in (i + 1)..rendered.len() {
                        atoms.push(format!("{} ≠ {}", rendered[i], rendered[j]));
                    }
                }
            }
            // Any other assertion must be a bare linear comparison.
            other => {
                atoms.push(lia_comparison_atom(other, &mut vars, context)?);
            }
        }
    }
    if atoms.is_empty() {
        return None;
    }
    Some(render_lia_lean_from_parsed(&atoms))
}

/// Build the CONSTRUCTIVE linear case-cascade term proving the all-negated
/// blocking clause `¬S₁ ∨ … ∨ ¬Sₙ` (right-associated). At atom `k`, if `Sₖ` is
/// FALSE we immediately select that disjunct; only the all-true spine recurses to
/// the bottom, where the collected hypotheses are contradictory and `omega`
/// closes `False`. Linear in `n` (no 2ⁿ split). Deriving `False` from the
/// hypotheses keeps the proof axiom-clean — `omega` on a *disjunction* goal would
/// otherwise pull in `Classical.choice`.
fn lia_cascade_term(atoms: &[String]) -> String {
    cascade_term_with_closer(atoms, "omega")
}

/// `lia_cascade_term` with the bottom-of-cascade tactic script made explicit.
/// The NIA-product emitter reuses the identical cascade but first introduces the
/// verified McCormick bridge facts (`closer` = `have … ; have … ; omega`), which
/// is what lets `omega` see a LINEAR relation between the atomised product term
/// and its two factors. `closer` must be a single-line tactic script: it is
/// spliced inside `(show False by …)` on one line, so no indentation-sensitive
/// multi-line block can be introduced here.
fn cascade_term_with_closer(atoms: &[String], closer: &str) -> String {
    let n = atoms.len();
    fn disjunct(i: usize, n: usize) -> String {
        let inner = if i < n {
            format!("Or.inl h{i}")
        } else {
            format!("h{i}")
        };
        let mut s = String::new();
        for _ in 0..(i - 1) {
            s.push_str("Or.inr (");
        }
        s.push_str(&inner);
        for _ in 0..(i - 1) {
            s.push(')');
        }
        s
    }
    fn build(k: usize, n: usize, atoms: &[String], closer: &str) -> String {
        if k == n {
            format!(
                "if h{k} : {a} then (show False by {closer}).elim else {d}",
                a = atoms[k - 1],
                d = disjunct(k, n)
            )
        } else {
            format!(
                "if h{k} : {a} then\n  {rest}\nelse {d}",
                a = atoms[k - 1],
                rest = build(k + 1, n, atoms, closer),
                d = disjunct(k, n)
            )
        }
    }
    build(1, n, atoms, closer)
}

/// Render the `firewall_combined_unsat`-grounded Lean for a linear-integer
/// conflict over the parsed atoms `S₁ … Sₙ` (each a Lean `Prop`). Model:
/// `Val := Nat → Int`. See `emit_lia_firewall_lean_from_parsed`.
fn render_lia_lean_from_parsed(atoms: &[String]) -> String {
    let n = atoms.len();
    let hash = fnv_hex(&atoms.join("\u{1}"));
    let arms = atoms
        .iter()
        .enumerate()
        .map(|(i, a)| format!("  | {} => decide ({a})", i + 1))
        .collect::<Vec<_>>()
        .join("\n");
    let orig = (1..=n)
        .map(|i| format!("({i}, [{i}])"))
        .collect::<Vec<_>>()
        .join(", ");
    let neg = (1..=n)
        .map(|i| format!("-{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = n + 1;
    let proof_id = n + 2;
    let hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let cascade = lia_cascade_term(atoms);
    // Stack-depth guard only: the cascade term nests one `if … then … else` per
    // atom, so a several-hundred-atom reconstruction outruns Lean's 512-frame
    // default long before it outruns the (deliberately unchanged) heartbeat
    // budget. Raising it keeps the CONSTRUCTIVE cascade — axioms ⊆ {propext,
    // Quot.sound} — rather than falling back to a classical tactic.
    let rec_depth = scaled_max_rec_depth(n);
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — LINEAR-INTEGER conflict reconstructed
  from the parsed frontend assertions, grounded in the verified
  `firewall_combined_unsat`. ay refutes the jointly integer-UNSAT (in)equality
  system with a bare `:rule trust` integer step (no `la_generic` lemma clause to
  ground per-step), so the conflict is rebuilt here: every assertion is asserted
  POSITIVELY and the single all-negated blocking clause `¬S₁ ∨ … ∨ ¬Sₙ` is
  discharged by a constructive linear case cascade closed by `omega` (a
  Lean-CORE tactic — no Mathlib). Model: a valuation `Nat → Int`.
  axioms ⊆ {{propext, Quot.sound}}.
-/
set_option linter.unusedSimpArgs false
set_option maxRecDepth {rec_depth}

namespace AySoundness.Emitted.Lia_{hash}
open AySoundness

abbrev Val := Nat → Int

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{neg}])]
def proof    : List (Cid × Clause × List Int) := [({proof_id}, [], [{hints}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{neg}] = true := by
  simp only [clauseSat, litSat, atomVal, List.any_cons, List.any_nil,
    Int.reduceGT, Int.reduceNeg, Int.reduceToNat, reduceIte, Bool.or_false,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  exact
    {cascade}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No integer valuation satisfies all the asserted linear (in)equalities —
    through the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.Lia_{hash}
"#
    )
}

// ==== APPENDED BUCKET: b_euf.rs ====
// ===========================================================================
// EUF + LINEAR-INTEGER fused congruence-value firewall (bucket "euf_uflia").
// ===========================================================================

/// A linear-integer normal form: `Σ coeffs·var + konst`.
#[derive(Clone)]
struct EufLiaLin {
    coeffs: std::collections::BTreeMap<String, i64>,
    konst: i64,
}

/// Parse the frontend's two integer-literal representations.
///
/// Ordinary SMT-LIB numerals arrive as `Numeral`; ay's lenient elaboration can
/// also preserve an *undeclared* signed literal such as `-1` as a numeric-text
/// `Symbol`. A declared numeric-looking surface name is not a literal: quoted
/// `|-1|` is a legal constant/function name and declaration resolution precedes
/// ay's lenient signed-literal fallback.
fn euf_lia_i64_literal(t: &PTerm, context: &ay_frontend::Context) -> Option<i64> {
    match t {
        PTerm::Const(PConst::Numeral(n)) => n.parse::<i64>().ok(),
        PTerm::Symbol(n) => firewall_undeclared_i64_symbol_literal(context, n),
        _ => None,
    }
}

/// Parse a frontend term into a linear-integer normal form, or `None` on any
/// non-linear / non-Int shape (a Real `Decimal` numeral, a nonlinear product, or
/// an uninterpreted application — the latter forces UF-value classification /
/// decline). This is the linearity + Int gate: `omega` (Lean core) discharges
/// only Int, so declining here keeps QF_UFLRA / nonlinear fail-closed.
fn euf_lia_lin_of(t: &PTerm, context: &ay_frontend::Context) -> Option<EufLiaLin> {
    use std::collections::BTreeMap;
    match t {
        PTerm::Symbol(v) if cbr_is_int_constant(context, v) => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(v.clone(), 1i64);
            Some(EufLiaLin { coeffs, konst: 0 })
        }
        PTerm::Symbol(v) => Some(EufLiaLin {
            coeffs: BTreeMap::new(),
            konst: firewall_undeclared_i64_symbol_literal(context, v)?,
        }),
        PTerm::Const(PConst::Numeral(n)) => Some(EufLiaLin {
            coeffs: BTreeMap::new(),
            konst: n.parse::<i64>().ok()?,
        }),
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("+", _) if !args.is_empty() => {
                let mut acc = EufLiaLin {
                    coeffs: BTreeMap::new(),
                    konst: 0,
                };
                for a in args {
                    acc = firewall_lin_add_checked(&acc, &euf_lia_lin_of(a, context)?, 1)?;
                }
                Some(acc)
            }
            ("-", 1) => firewall_lin_scale_checked(&euf_lia_lin_of(&args[0], context)?, -1),
            ("-", n) if n >= 2 => {
                let mut acc = euf_lia_lin_of(&args[0], context)?;
                for a in &args[1..] {
                    acc = firewall_lin_add_checked(&acc, &euf_lia_lin_of(a, context)?, -1)?;
                }
                Some(acc)
            }
            ("*", _) if !args.is_empty() => {
                let mut acc = EufLiaLin {
                    coeffs: BTreeMap::new(),
                    konst: 1,
                };
                for a in args {
                    let l = euf_lia_lin_of(a, context)?;
                    if acc.coeffs.is_empty() {
                        acc = firewall_lin_scale_checked(&l, acc.konst)?;
                    } else if l.coeffs.is_empty() {
                        acc = firewall_lin_scale_checked(&acc, l.konst)?;
                    } else {
                        return None; // nonlinear product of two variable terms
                    }
                }
                Some(acc)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Sanitize an SMT symbol to a Lean-identifier tail (alnum kept, everything else
/// `_`). Combined with an `x_` / `f_` field prefix this guarantees a valid,
/// keyword-free field name AND keeps the Int-variable and UF-function namespaces
/// disjoint.
fn euf_lia_san(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

/// Render a linear-integer frontend term to a Lean `Int` expression over the
/// `Val` model (`m.x_<san>` per variable, `(n : Int)` per numeral). Mirrors
/// `euf_lia_lin_of`'s accepted shapes; `None` otherwise.
fn euf_lia_render_int(t: &PTerm, context: &ay_frontend::Context) -> Option<String> {
    match t {
        PTerm::Symbol(v) if cbr_is_int_constant(context, v) => {
            Some(format!("m.x_{}", euf_lia_san(v)))
        }
        PTerm::Symbol(v) => Some(format!(
            "({} : Int)",
            firewall_undeclared_i64_symbol_literal(context, v)?
        )),
        PTerm::Const(PConst::Numeral(n)) => {
            n.parse::<i64>().ok()?;
            Some(format!("({n} : Int)"))
        }
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("+", _) if !args.is_empty() => {
                let parts: Option<Vec<String>> = args
                    .iter()
                    .map(|arg| euf_lia_render_int(arg, context))
                    .collect();
                Some(format!("({})", parts?.join(" + ")))
            }
            ("-", 1) => Some(format!("(- {})", euf_lia_render_int(&args[0], context)?)),
            ("-", n) if n >= 2 => {
                let parts: Option<Vec<String>> = args
                    .iter()
                    .map(|arg| euf_lia_render_int(arg, context))
                    .collect();
                Some(format!("({})", parts?.join(" - ")))
            }
            ("*", _) if !args.is_empty() => {
                let parts: Option<Vec<String>> = args
                    .iter()
                    .map(|arg| euf_lia_render_int(arg, context))
                    .collect();
                Some(format!("({})", parts?.join(" * ")))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Match an uninterpreted single-application value atom `(g (symbol arg))` on
/// `head` against an Int numeral on `tail` → `(g, arg, value)`. `g` must not be
/// an arithmetic operator (those are LIA, not UF). The argument must be a bare
/// symbol (single application; congruence over compound args is out of scope).
fn euf_lia_match_uf_value(
    head: &PTerm,
    tail: &PTerm,
    context: &ay_frontend::Context,
) -> Option<(String, String, i64)> {
    let PTerm::App(g, gargs) = head else {
        return None;
    };
    if matches!(
        g.as_str(),
        "+" | "-" | "*" | "=" | ">=" | "<=" | ">" | "<" | "not"
    ) {
        return None;
    }
    if gargs.len() != 1 {
        return None;
    }
    let PTerm::Symbol(arg) = &gargs[0] else {
        return None;
    };
    if !cbr_is_int_constant(context, arg) || !cbr_is_int_unary_function(context, g) {
        return None;
    }
    let val = euf_lia_i64_literal(tail, context)?;
    Some((g.clone(), arg.clone(), val))
}

/// Union-find root with path compression over a `parent` map.
fn euf_lia_find(parent: &mut std::collections::HashMap<String, String>, x: &str) -> String {
    let mut root = x.to_string();
    while let Some(p) = parent.get(&root) {
        if p == &root {
            break;
        }
        root = p.clone();
    }
    let mut cur = x.to_string();
    while let Some(p) = parent.get(&cur).cloned() {
        if p == cur {
            break;
        }
        parent.insert(cur.clone(), root.clone());
        cur = p;
    }
    root
}

/// One asserted atom: its rendered Lean `Prop` and its asserted polarity
/// (`cv = true` ⟺ asserted positively).
struct EufLiaAtom {
    prop: String,
    cv: bool,
}

/// Emit a verified-firewall Lean proof for an EUF + LINEAR-INTEGER fused
/// congruence-value conflict found among the PARSED (frontend) assertions —
/// bucket "euf_uflia". See the section header above for the recognized shape.
///
/// Fail-closed: an unrecognized atom, a non-linear/non-Int (Real) shape, a
/// non-symbol UF argument, or the absence of a genuine congruence-closing
/// conflict all return `None`. Every surface variable/function must resolve
/// uniquely in `context` as Int / Int → Int. axioms ⊆ {propext, Quot.sound}; NO
/// Mathlib, no new AySoundness lemma, no `sorry`.
pub(crate) fn emit_euf_lia_congruence_firewall_lean_from_parsed(
    parsed: &[PTerm],
    context: &ay_frontend::Context,
) -> Option<String> {
    use std::collections::{BTreeSet, HashMap};

    let mut atoms: Vec<EufLiaAtom> = Vec::new();
    let mut int_vars: BTreeSet<String> = BTreeSet::new();
    let mut uf_funcs: BTreeSet<String> = BTreeSet::new();
    // (func, arg-var, value, asserted-positive) for congruence-conflict detection.
    let mut uf_values: Vec<(String, String, i64, bool)> = Vec::new();
    // Positive LIA `=` differences (L - R) for implied-equality analysis.
    let mut eq_diffs: Vec<EufLiaLin> = Vec::new();
    // Positive LIA bounds: (op, (L - R)) for constant-pin analysis.
    let mut bound_atoms: Vec<(String, EufLiaLin)> = Vec::new();

    if parsed.is_empty() {
        return None;
    }

    for asrt in parsed {
        let (inner, positive) = match asrt {
            PTerm::App(op, a) if op == "not" && a.len() == 1 => (&a[0], false),
            other => (other, true),
        };
        let PTerm::App(op, args) = inner else {
            return None;
        };
        // UF value atom: `(= (f x) c)` / `(= c (f x))`.
        if op == "=" && args.len() == 2 {
            if let Some((g, arg, val)) = euf_lia_match_uf_value(&args[0], &args[1], context)
                .or_else(|| euf_lia_match_uf_value(&args[1], &args[0], context))
            {
                let prop = format!(
                    "m.f_{} (m.x_{}) = ({} : Int)",
                    euf_lia_san(&g),
                    euf_lia_san(&arg),
                    val
                );
                uf_funcs.insert(g.clone());
                int_vars.insert(arg.clone());
                uf_values.push((g, arg, val, positive));
                atoms.push(EufLiaAtom { prop, cv: positive });
                continue;
            }
        }
        // LIA relational atom.
        let lean_op = match op.as_str() {
            "=" => "=",
            ">=" => ">=",
            "<=" => "<=",
            ">" => ">",
            "<" => "<",
            _ => return None,
        };
        if args.len() != 2 {
            return None;
        }
        let (la, lb) = (
            euf_lia_lin_of(&args[0], context),
            euf_lia_lin_of(&args[1], context),
        );
        let (Some(la), Some(lb)) = (la, lb) else {
            return None;
        };
        let sa = euf_lia_render_int(&args[0], context)?;
        let sb = euf_lia_render_int(&args[1], context)?;
        for v in la.coeffs.keys().chain(lb.coeffs.keys()) {
            int_vars.insert(v.clone());
        }
        atoms.push(EufLiaAtom {
            prop: format!("{sa} {lean_op} {sb}"),
            cv: positive,
        });
        if positive {
            let diff = firewall_lin_add_checked(&la, &lb, -1)?;
            if op == "=" {
                eq_diffs.push(diff);
            } else {
                bound_atoms.push((op.clone(), diff));
            }
        }
    }

    if uf_values.is_empty() {
        return None;
    }
    // Every field name must be a simple identifier tail with NO collision after
    // sanitization (fail-closed determinism guard).
    {
        let mut seen: HashMap<String, String> = HashMap::new();
        for v in &int_vars {
            if let Some(prev) = seen.insert(euf_lia_san(v), v.clone()) {
                if &prev != v {
                    return None; // two distinct vars sanitize to one field
                }
            }
        }
        let mut seenf: HashMap<String, String> = HashMap::new();
        for g in &uf_funcs {
            if let Some(prev) = seenf.insert(euf_lia_san(g), g.clone()) {
                if &prev != g {
                    return None;
                }
            }
        }
    }

    // --- LIA implied-equality analysis (SOUND: only conclude x=y when truly
    // LIA-implied, so the emitted bridge's inner `by omega` always succeeds). ---
    // Constant pins from bound pairs (v>=k & v<=k) over single ±1-coefficient vars.
    let mut lb: HashMap<String, i64> = HashMap::new();
    let mut ub: HashMap<String, i64> = HashMap::new();
    for (op, diff) in &bound_atoms {
        if diff.coeffs.len() != 1 {
            continue;
        }
        let (v, &c) = diff.coeffs.iter().next().unwrap();
        let d = diff.konst;
        // c*v + d  (op)  0
        let (lo, hi) = cbr_bound_lo_hi(op, c, d)?;
        if let Some(l) = lo {
            let e = lb.entry(v.clone()).or_insert(l);
            if l > *e {
                *e = l;
            }
        }
        if let Some(h) = hi {
            let e = ub.entry(v.clone()).or_insert(h);
            if h < *e {
                *e = h;
            }
        }
    }
    let mut pins: HashMap<String, i64> = HashMap::new();
    for v in &int_vars {
        if let (Some(&l), Some(&h)) = (lb.get(v), ub.get(v)) {
            if l == h {
                pins.insert(v.clone(), l);
            }
        }
    }
    // Fixpoint over equalities: substitute known pins, deriving new pins (1 var
    // remaining) or variable unions (2 opposite-coefficient vars, zero offset).
    let mut parent: HashMap<String, String> = HashMap::new();
    for v in &int_vars {
        parent.insert(v.clone(), v.clone());
    }
    loop {
        let mut changed = false;
        for diff in &eq_diffs {
            let mut coeffs = diff.coeffs.clone();
            let mut konst = diff.konst;
            let pinned: Vec<String> = coeffs
                .keys()
                .filter(|v| pins.contains_key(*v))
                .cloned()
                .collect();
            for v in pinned {
                let c = coeffs.remove(&v).unwrap();
                konst = konst.checked_add(c.checked_mul(pins[&v])?)?;
            }
            coeffs.retain(|_, &mut c| c != 0);
            match coeffs.len() {
                1 => {
                    let (v, &c) = coeffs.iter().next().unwrap();
                    if let Some(val) = cbr_single_key_pin(c, konst)? {
                        if pins.get(v) != Some(&val) {
                            pins.insert(v.clone(), val);
                            changed = true;
                        }
                    }
                }
                2 => {
                    let mut it = coeffs.iter();
                    let (v1, &c1) = it.next().unwrap();
                    let (v2, &c2) = it.next().unwrap();
                    if c1 != 0 && c1.checked_neg() == Some(c2) && konst == 0 {
                        let r1 = euf_lia_find(&mut parent, v1);
                        let r2 = euf_lia_find(&mut parent, v2);
                        if r1 != r2 {
                            parent.insert(r1, r2);
                            changed = true;
                        }
                    }
                }
                _ => {}
            }
        }
        if !changed {
            break;
        }
    }
    // Constant value per union class (for pinned-equal detection across classes).
    let mut class_pin: HashMap<String, i64> = HashMap::new();
    for (v, &p) in &pins {
        let r = euf_lia_find(&mut parent, v);
        class_pin.entry(r).or_insert(p);
    }
    let mut implies_eq = |x: &str, y: &str| -> bool {
        let rx = euf_lia_find(&mut parent, x);
        let ry = euf_lia_find(&mut parent, y);
        if rx == ry {
            return true;
        }
        match (class_pin.get(&rx), class_pin.get(&ry)) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    };

    // --- Congruence-conflict detection: a same-function value-atom pair whose
    // args are LIA-implied equal but whose asserted values contradict. ---
    let mut bridges: BTreeSet<(String, String, String)> = BTreeSet::new();
    let mut has_conflict = false;
    for i in 0..uf_values.len() {
        for j in (i + 1)..uf_values.len() {
            let (gi, ai, vi, pi) = &uf_values[i];
            let (gj, aj, vj, pj) = &uf_values[j];
            if gi != gj {
                continue;
            }
            if !implies_eq(ai, aj) {
                continue;
            }
            let conflict = match (pi, pj) {
                (true, true) => vi != vj,
                (true, false) | (false, true) => vi == vj,
                (false, false) => false,
            };
            if conflict {
                has_conflict = true;
                if ai != aj {
                    // Deterministic bridge orientation (sorted arg names).
                    let (lo, hi) = if ai <= aj { (ai, aj) } else { (aj, ai) };
                    bridges.insert((gi.clone(), lo.clone(), hi.clone()));
                }
            }
        }
    }
    if !has_conflict {
        return None;
    }
    if atoms.iter().any(|a| atom_prop_defeats_closure(&a.prop)) {
        return None;
    }

    Some(render_euf_lia_congruence_lean(
        &atoms,
        &int_vars,
        &uf_funcs,
        &bridges.into_iter().collect::<Vec<_>>(),
    ))
}

/// Whether an atom's rendered `Prop` defeats the nested-`by_cases` closing
/// tactic `simp [clauseSat, litSat, atomVal, hᵢ]`, so the emitter must DECLINE
/// rather than write an artifact that will not compile.
///
/// Two shapes do, both found by fuzzing the emitters and both producing a file
/// that fails `lake env lean` and reports `sorryAx` — worse than declining, and
/// a regression against the previous behaviour of declining these inputs
/// outright:
///
/// 1. A SYNTACTICALLY REFLEXIVE equality, `t = t`, from e.g. `(assert (= z z))`,
///    `(assert (= 5.0 5.0))`, `(assert (= (f x) (f x)))`, or `(assert (= 5 5.0))`
///    where both sides render alike. `simp`'s `eq_self` rewrites the atom to
///    `True` before the branch hypothesis `hᵢ : ¬(t = t)` can be used — Lean's
///    own linter flags the argument as unused — so the goal survives. Adding
///    `(assert (= x x))` to an otherwise-clean benchmark was enough to turn a
///    checking artifact into a `sorryAx` one.
/// 2. A disequality whose sides stand in an OCCURS relation, e.g.
///    `(assert (not (= y (g y))))`. The closing branch hands `h : y = g y` to
///    `simp` as a rewrite rule, which loops until "maximum recursion depth".
///
/// Declining is the conservative direction and matches what these emitters did
/// before the shapes were reachable. Widening coverage means FIXING the closing
/// tactic (a reflexive branch is vacuous and closes by `absurd rfl hᵢ`), not
/// relaxing this gate.
fn atom_prop_defeats_closure(prop: &str) -> bool {
    let Some((lhs, rhs)) = prop.split_once(" = ") else {
        return false;
    };
    let (lhs, rhs) = (lhs.trim(), rhs.trim());
    if lhs == rhs {
        return true; // reflexive: `simp` rewrites it away before hᵢ applies
    }
    // Occurs relation. For a single-token side, require a whole-token match so
    // `m.x_a` does not spuriously "occur in" `m.x_ab`.
    let occurs = |small: &str, big: &str| -> bool {
        if small.contains(' ') {
            big.contains(small)
        } else {
            big.split(|c: char| c.is_whitespace() || c == '(' || c == ')')
                .any(|tok| tok == small)
        }
    };
    occurs(lhs, rhs) || occurs(rhs, lhs)
}

/// Render the fused EUF+LIA congruence-value firewall file. The lemma clause is
/// the all-negated disjunction of every asserted atom; its validity is proved
/// inline by nested `by_cases` (each deviating branch closed by `simp`) with the
/// all-consistent leaf closed by `omega` after the congruence bridges
/// `f x = f y` (each from the `omega`-provable `x = y`) are introduced by `rw`.
fn render_euf_lia_congruence_lean(
    atoms: &[EufLiaAtom],
    int_vars: &std::collections::BTreeSet<String>,
    uf_funcs: &std::collections::BTreeSet<String>,
    bridges: &[(String, String, String)],
) -> String {
    let n = atoms.len();
    let lemma_id = n + 1;
    let proof_id = n + 2;

    let fields = {
        let mut f: Vec<String> = int_vars
            .iter()
            .map(|v| format!("  x_{} : Int", euf_lia_san(v)))
            .collect();
        f.extend(
            uf_funcs
                .iter()
                .map(|g| format!("  f_{} : Int -> Int", euf_lia_san(g))),
        );
        f.join("\n")
    };
    let arms = atoms
        .iter()
        .enumerate()
        .map(|(i, a)| format!("  | {} => decide ({})", i + 1, a.prop))
        .collect::<Vec<_>>()
        .join("\n");
    let orig = atoms
        .iter()
        .enumerate()
        .map(|(i, a)| {
            let lit = if a.cv {
                format!("{}", i + 1)
            } else {
                format!("-{}", i + 1)
            };
            format!("({}, [{lit}])", i + 1)
        })
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_lits = atoms
        .iter()
        .enumerate()
        .map(|(i, a)| {
            if a.cv {
                format!("-{}", i + 1)
            } else {
                format!("{}", i + 1)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let proof_hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    // Bridge tactic lines (relative indentation; leaf prefixes the base indent).
    let bridge_rel: Vec<Vec<String>> = bridges
        .iter()
        .enumerate()
        .map(|(k, (g, ai, aj))| {
            let gs = euf_lia_san(g);
            let (xi, xj) = (euf_lia_san(ai), euf_lia_san(aj));
            vec![
                format!("have hbr{k} : m.f_{gs} (m.x_{xi}) = m.f_{gs} (m.x_{xj}) := by"),
                format!("  have he{k} : (m.x_{xi} : Int) = (m.x_{xj} : Int) := by omega"),
                format!("  rw [he{k}]"),
            ]
        })
        .collect();

    let proof_body = euf_lia_emit_block(atoms, 0, "  ", &bridge_rel).join("\n");

    let hash = fnv_hex(
        &atoms
            .iter()
            .map(|a| format!("{}:{}", a.cv, a.prop))
            .collect::<Vec<_>>()
            .join("\u{1}"),
    );

    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — EUF + LINEAR-INTEGER fused
  congruence-value conflict, grounded in the verified `firewall_combined_unsat`.
  A set of LIA atoms forces some Int variables to a common value; single-
  application UF value atoms `f x = c1`, `f y = c2` (or one negated) then
  contradict via the congruence conclusion `f x = f y` (from `x = y`). ay fuses
  the whole refutation into one `:rule trust` clause, so the structure is
  reconstructed from the frontend assertions. The single fused conflict clause is
  discharged INLINE: nested `by_cases` on every atom (deviating branches closed by
  `simp`), the all-consistent leaf closed by `omega` after the congruence bridge
  `f x = f y` is introduced by `rw` (from the `omega`-provable `x = y`). All
  tactics are Lean 4 core (no Mathlib). axioms ⊆ {{propext, Quot.sound}}.
-/
namespace AySoundness.Emitted.EufLiaCong_{hash}
open AySoundness

structure Val where
{fields}

/-- Atoms (one per asserted frontend atom, in assertion order). -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof_id}, [], [{proof_hints}])]

/-- The fused conflict clause is valid in EVERY model: any deviation from the
    asserted polarities satisfies the clause; the all-consistent case is refuted
    by `omega` through the congruence bridge. -/
theorem euf_lia_lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
{proof_body}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact euf_lia_lemma_valid m

/-- No model satisfies the fused EUF+LIA congruence-value conflict — via the
    verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.EufLiaCong_{hash}
"#,
    )
}

/// Recursively emit the nested `by_cases` proof block for the fused conflict
/// clause, one atom per level. Each level splits on the atom's `Prop`; the
/// branch deviating from the asserted polarity closes the clause by `simp`, the
/// consistent branch recurses. The innermost (all-consistent) leaf emits
/// `exfalso`, the congruence bridges, then `omega`. Lines are prefixed with
/// `indent`; bullet sub-blocks are indented two further.
fn euf_lia_emit_block(
    atoms: &[EufLiaAtom],
    idx: usize,
    indent: &str,
    bridges: &[Vec<String>],
) -> Vec<String> {
    if idx == atoms.len() {
        let mut lines = vec![format!("{indent}exfalso")];
        for b in bridges {
            for line in b {
                lines.push(format!("{indent}{line}"));
            }
        }
        lines.push(format!("{indent}omega"));
        return lines;
    }
    let a = &atoms[idx];
    let hi = format!("h{}", idx + 1);
    let child = format!("{indent}  ");
    let cont = euf_lia_emit_block(atoms, idx + 1, &child, bridges);
    let close = vec![format!("{child}simp [clauseSat, litSat, atomVal, {hi}]")];
    let bulletize = |sub: &[String]| -> Vec<String> {
        sub.iter()
            .enumerate()
            .map(|(k, line)| {
                if k == 0 {
                    let content = line
                        .strip_prefix(child.as_str())
                        .unwrap_or(line.trim_start());
                    format!("{indent}· {content}")
                } else {
                    line.clone()
                }
            })
            .collect()
    };
    let mut lines = vec![format!("{indent}by_cases {hi} : ({})", a.prop)];
    // Lean `by_cases h : P` yields the `P` (true) branch first, then `¬P`.
    if a.cv {
        // asserted positive: true branch is consistent (recurse); false closes.
        lines.extend(bulletize(&cont));
        lines.extend(bulletize(&close));
    } else {
        // asserted negative: true branch deviates (closes); false is consistent.
        lines.extend(bulletize(&close));
        lines.extend(bulletize(&cont));
    }
    lines
}

// ===========================================================================
// EUF + ORDERED-FIELD (SMT-LIB `Real`) fused congruence-value firewall
// (bucket "euf_uflra").
// ===========================================================================
//
// FAITHFULNESS. Lean core has no ℝ, so a `no_model` over `Int`/`Rat` would
// certify something STRICTLY WEAKER than a Real-sorted `unsat`. This emitter
// instead parameterises the model by an ARBITRARY linearly ordered field
// `F : AySoundness.OrdField`, so the theorem reads "no model in ANY linearly
// ordered field", which DOES entail "no real model". See
// `verification/lean/AySoundness/OrdField.lean`.
//
// SEPARATION FROM THE Int PATH (a §0 obligation, not a style choice). Nothing
// here calls `cbr_lin_of`, `euf_lia_lin_of`, `cbr_is_int_constant` or
// `cbr_is_int_unary_function`, and none of those is modified: the Int emitters
// keep their `Sort::Int` gates verbatim, so a Real file can never reach an
// `omega`/Int render, and this emitter's `Sort::Real` gates mean an Int file can
// never reach the ordered-field render. The distinction is load-bearing because
// INTEGER reasoning is UNSOUND over ℝ: `x > 5 ∧ x < 7` pins `x = 6` over `Int`
// but leaves `x` free over ℝ. Accordingly the pin analysis below accepts ONLY
// non-strict bounds with a coincident low and high, which is exactly
// `OrdField.le_antisymm` and holds in every ordered field.
//
// ARITHMETIC IS DELIBERATELY OUT OF SCOPE. Atoms are rendered DIRECTLY (a
// variable, a numeral, or a single UF application); no linear normal form is
// ever built, so the "a normalized negative coefficient has no `F.ofNat`
// representation" hazard cannot arise. Any `+`/`-`/`*`/`/` inside an atom
// declines.

/// One side of a recognized Real atom.
#[derive(Clone, PartialEq, Eq)]
enum OrdFieldTerm {
    /// A declared 0-ary `Real` constant.
    Var(String),
    /// A non-negative integer-valued Real literal, rendered `F.ofNat k`.
    Num(u64),
    /// A single application `(g x)` of a declared `Real -> Real` function to a
    /// declared 0-ary `Real` constant.
    UfApp(String, String),
}

/// The largest numeral this emitter will render. `F.ofNat` is a successor-style
/// recursive definition; the emitted proofs never unfold it, but an unbounded
/// literal still has no place in a diagnostic artifact, and the bound keeps the
/// `by decide` on `m ≠ n` cheap.
const ORDFIELD_MAX_NUMERAL: u64 = 1_000_000;

fn ordfield_is_real_constant(context: &ay_frontend::Context, name: &str) -> bool {
    firewall_unique_symbol_info(context, name)
        .is_some_and(|info| info.arg_sorts.is_empty() && info.sort == Sort::Real)
}

fn ordfield_is_real_unary_function(context: &ay_frontend::Context, name: &str) -> bool {
    firewall_unique_symbol_info(context, name).is_some_and(|info| {
        matches!(info.arg_sorts.as_slice(), [Sort::Real]) && info.sort == Sort::Real
    })
}

/// A non-negative integer-valued Real literal, as a `Nat`.
///
/// Accepts `5` (`Numeral`) and `5.0` / `5.000` (`Decimal` with an all-zero
/// fractional part). Declines a genuinely fractional decimal (`2.5`), a negative
/// value, anything above `ORDFIELD_MAX_NUMERAL`, and — unlike the Int
/// recognizers — ANY `Symbol`: there is no lenient signed-literal fallback here,
/// so a declared symbol whose surface text merely looks numeric can never be
/// reinterpreted as a constant.
fn ordfield_nat_literal(t: &PTerm) -> Option<u64> {
    let text = match t {
        PTerm::Const(PConst::Numeral(n)) => n.as_str(),
        PTerm::Const(PConst::Decimal(d)) => d.as_str(),
        _ => return None,
    };
    let (int_part, frac_part) = text.split_once('.').unwrap_or((text, ""));
    if !frac_part.chars().all(|c| c == '0') {
        return None;
    }
    if int_part.is_empty() || !int_part.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let value = int_part.parse::<u64>().ok()?;
    (value <= ORDFIELD_MAX_NUMERAL).then_some(value)
}

/// Classify one side of an atom, declining every shape outside the scope above.
fn ordfield_term_of(t: &PTerm, context: &ay_frontend::Context) -> Option<OrdFieldTerm> {
    if let Some(k) = ordfield_nat_literal(t) {
        return Some(OrdFieldTerm::Num(k));
    }
    match t {
        PTerm::Symbol(v) if ordfield_is_real_constant(context, v) => {
            Some(OrdFieldTerm::Var(v.clone()))
        }
        PTerm::App(g, args) if args.len() == 1 && !cbr_is_builtin_op(g) => {
            let PTerm::Symbol(arg) = &args[0] else {
                return None;
            };
            (ordfield_is_real_unary_function(context, g) && ordfield_is_real_constant(context, arg))
                .then(|| OrdFieldTerm::UfApp(g.clone(), arg.clone()))
        }
        _ => None,
    }
}

/// Render a classified term as a Lean expression over the `Val F` model.
fn ordfield_render(t: &OrdFieldTerm) -> String {
    match t {
        OrdFieldTerm::Var(v) => format!("m.x_{}", euf_lia_san(v)),
        OrdFieldTerm::Num(k) => format!("F.ofNat {k}"),
        OrdFieldTerm::UfApp(g, a) => format!("m.f_{} (m.x_{})", euf_lia_san(g), euf_lia_san(a)),
    }
}

/// One asserted Real atom: its rendered Lean `Prop` and its asserted polarity.
struct OrdFieldAtom {
    prop: String,
    cv: bool,
}

/// Equality-proof-graph node for a Real variable. Numerals are nodes too
/// (`ordfield_num_node`), because a pinned variable is proved equal to
/// `F.ofNat k` and two variables pinned to the SAME numeral are thereby equal.
/// U+0001 cannot occur in an SMT symbol, so the two namespaces never collide.
fn ordfield_var_node(v: &str) -> String {
    format!("v\u{1}{v}")
}

fn ordfield_num_node(k: u64) -> String {
    format!("n\u{1}{k}")
}

type OrdFieldEdges = std::collections::BTreeMap<String, Vec<(String, String)>>;

/// Record `a = b` with `proof : a = b` and `proof_sym : b = a`.
fn ordfield_add_edge(edges: &mut OrdFieldEdges, a: &str, b: &str, proof: String, sym: String) {
    edges
        .entry(a.to_string())
        .or_default()
        .push((b.to_string(), proof));
    edges
        .entry(b.to_string())
        .or_default()
        .push((a.to_string(), sym));
}

/// Shortest equality-proof path `a = b` over the graph, as a Lean term, or
/// `None` when the two variables are not provably equal from the recorded
/// hypotheses (in which case the caller declines rather than guessing).
fn ordfield_eq_proof(edges: &OrdFieldEdges, a: &str, b: &str) -> Option<String> {
    use std::collections::{BTreeSet, HashMap, VecDeque};
    let (start, goal) = (ordfield_var_node(a), ordfield_var_node(b));
    if start == goal {
        return Some("rfl".to_string());
    }
    let mut prev: HashMap<String, (String, String)> = HashMap::new();
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut queue: VecDeque<String> = VecDeque::new();
    seen.insert(start.clone());
    queue.push_back(start.clone());
    while let Some(cur) = queue.pop_front() {
        if cur == goal {
            break;
        }
        for (next, proof) in edges.get(&cur).into_iter().flatten() {
            if seen.insert(next.clone()) {
                prev.insert(next.clone(), (cur.clone(), proof.clone()));
                queue.push_back(next.clone());
            }
        }
    }
    if !seen.contains(&goal) {
        return None;
    }
    let mut steps: Vec<String> = Vec::new();
    let mut cur = goal;
    while cur != start {
        let (p, proof) = prev.get(&cur)?.clone();
        steps.push(proof);
        cur = p;
    }
    steps.reverse();
    let mut acc = steps.first()?.clone();
    for step in &steps[1..] {
        acc = format!("({acc}.trans {step})");
    }
    Some(acc)
}

/// Emit a verified-firewall Lean proof for an EUF + ORDERED-FIELD fused
/// congruence-value conflict among the PARSED (frontend) assertions — bucket
/// "euf_uflra".
///
/// Recognized shape: every assertion is a (possibly `not`-wrapped) binary
/// `=`/`>=`/`<=`/`>`/`<` whose sides are a declared `Real` constant, a
/// non-negative integer-valued Real literal, or a single application of a
/// declared `Real -> Real` function to a declared `Real` constant; and some pair
/// of same-function UF value atoms has ordered-field-implied-equal arguments but
/// contradictory asserted values.
///
/// Fail-closed on everything else: any arithmetic operator, any non-Real sort,
/// any fractional or negative literal, any symbol collision after sanitization,
/// any missing equality-proof path.
pub(crate) fn emit_euf_ordfield_congruence_firewall_lean_from_parsed(
    parsed: &[PTerm],
    context: &ay_frontend::Context,
) -> Option<String> {
    use std::collections::{BTreeSet, HashMap};

    if parsed.is_empty() {
        return None;
    }

    let mut atoms: Vec<OrdFieldAtom> = Vec::new();
    let mut real_vars: BTreeSet<String> = BTreeSet::new();
    let mut uf_funcs: BTreeSet<String> = BTreeSet::new();
    // (func, arg, value, asserted-positive, 0-based atom index)
    let mut uf_values: Vec<(String, String, u64, bool, usize)> = Vec::new();
    // Non-strict bounds per variable: (bound, index of the atom proving it).
    // Deliberately separate from `bound_*` below so a STRICT bound can never
    // leak into the pin analysis, where it would be unsound over ℝ.
    let mut lower: HashMap<String, (u64, usize)> = HashMap::new();
    let mut upper: HashMap<String, (u64, usize)> = HashMap::new();
    // Strongest bound of EITHER kind per variable, for the one-variable
    // bound-contradiction refutation: (bound, atom index, strict?).
    let mut bound_lo: HashMap<String, (u64, usize, bool)> = HashMap::new();
    let mut bound_hi: HashMap<String, (u64, usize, bool)> = HashMap::new();
    let mut edges: OrdFieldEdges = OrdFieldEdges::new();

    for asrt in parsed {
        let (inner, positive) = match asrt {
            PTerm::App(op, a) if op == "not" && a.len() == 1 => (&a[0], false),
            other => (other, true),
        };
        let PTerm::App(op, args) = inner else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let lhs = ordfield_term_of(&args[0], context)?;
        let rhs = ordfield_term_of(&args[1], context)?;
        for side in [&lhs, &rhs] {
            match side {
                OrdFieldTerm::Var(v) => {
                    real_vars.insert(v.clone());
                }
                OrdFieldTerm::UfApp(g, a) => {
                    uf_funcs.insert(g.clone());
                    real_vars.insert(a.clone());
                }
                OrdFieldTerm::Num(_) => {}
            }
        }
        let idx = atoms.len();

        match op.as_str() {
            "=" => {
                let hyp = format!("h{}", idx + 1);
                // A UF value atom, normalized to `f x = numeral` (equality is
                // symmetric, so the flipped source orientation renders the same).
                let uf_value = match (&lhs, &rhs) {
                    (OrdFieldTerm::UfApp(g, a), OrdFieldTerm::Num(k))
                    | (OrdFieldTerm::Num(k), OrdFieldTerm::UfApp(g, a)) => {
                        Some((g.clone(), a.clone(), *k))
                    }
                    _ => None,
                };
                if let Some((g, a, k)) = uf_value {
                    atoms.push(OrdFieldAtom {
                        prop: format!(
                            "m.f_{} (m.x_{}) = F.ofNat {k}",
                            euf_lia_san(&g),
                            euf_lia_san(&a)
                        ),
                        cv: positive,
                    });
                    uf_values.push((g, a, k, positive, idx));
                    continue;
                }
                atoms.push(OrdFieldAtom {
                    prop: format!("{} = {}", ordfield_render(&lhs), ordfield_render(&rhs)),
                    cv: positive,
                });
                if positive {
                    let node = |t: &OrdFieldTerm| match t {
                        OrdFieldTerm::Var(v) => Some(ordfield_var_node(v)),
                        OrdFieldTerm::Num(k) => Some(ordfield_num_node(*k)),
                        OrdFieldTerm::UfApp(_, _) => None,
                    };
                    if let (Some(na), Some(nb)) = (node(&lhs), node(&rhs)) {
                        ordfield_add_edge(&mut edges, &na, &nb, hyp.clone(), format!("{hyp}.symm"));
                    }
                }
            }
            ">=" | "<=" | ">" | "<" => {
                // `a >= b` renders `F.le b a`; `a > b` renders `F.lt b a`.
                let (low, high) = if matches!(op.as_str(), ">=" | ">") {
                    (&rhs, &lhs)
                } else {
                    (&lhs, &rhs)
                };
                let strict = matches!(op.as_str(), ">" | "<");
                let rel = if strict { "F.lt" } else { "F.le" };
                atoms.push(OrdFieldAtom {
                    prop: format!(
                        "{rel} ({}) ({})",
                        ordfield_render(low),
                        ordfield_render(high)
                    ),
                    cv: positive,
                });
                // ONLY non-strict, positively asserted bounds pin. A strict bound
                // pins nothing in an ordered field, unlike over `Int`.
                if positive {
                    match (low, high) {
                        (OrdFieldTerm::Num(k), OrdFieldTerm::Var(v)) => {
                            if !strict {
                                let e = lower.entry(v.clone()).or_insert((*k, idx));
                                if *k >= e.0 {
                                    *e = (*k, idx);
                                }
                            }
                            let e = bound_lo.entry(v.clone()).or_insert((*k, idx, strict));
                            if (*k, strict) >= (e.0, e.2) {
                                *e = (*k, idx, strict);
                            }
                        }
                        (OrdFieldTerm::Var(v), OrdFieldTerm::Num(k)) => {
                            if !strict {
                                let e = upper.entry(v.clone()).or_insert((*k, idx));
                                if *k <= e.0 {
                                    *e = (*k, idx);
                                }
                            }
                            let e = bound_hi.entry(v.clone()).or_insert((*k, idx, strict));
                            if (*k, !strict) <= (e.0, !e.2) {
                                *e = (*k, idx, strict);
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => return None,
        }
    }

    // A `Val` structure with no fields is not valid Lean, and an assertion set
    // with no Real variable carries no refutable content here anyway.
    if real_vars.is_empty() {
        return None;
    }

    // O3 — symbol-mangling injectivity. Two distinct SMT symbols collapsing onto
    // one `Val` field would silently FORCE an equality, so the theorem would
    // prove a MORE-CONSTRAINED formula, which does NOT entail unsat of the
    // original. Decline instead.
    {
        let mut seen: HashMap<String, String> = HashMap::new();
        for v in &real_vars {
            if let Some(prev) = seen.insert(euf_lia_san(v), v.clone()) {
                if &prev != v {
                    return None;
                }
            }
        }
        let mut seen_f: HashMap<String, String> = HashMap::new();
        for g in &uf_funcs {
            if let Some(prev) = seen_f.insert(euf_lia_san(g), g.clone()) {
                if &prev != g {
                    return None;
                }
            }
        }
    }

    // Pins from coincident non-strict bounds: `ofNat k <= v` and `v <= ofNat k`
    // give `v = ofNat k` by `OrdField.le_antisymm`.
    let mut pin_lines: Vec<String> = Vec::new();
    for v in &real_vars {
        let (Some(&(l, li)), Some(&(u, ui))) = (lower.get(v), upper.get(v)) else {
            continue;
        };
        if l != u {
            continue;
        }
        let sv = euf_lia_san(v);
        let name = format!("hpin_{sv}");
        pin_lines.push(format!(
            "have {name} : m.x_{sv} = F.ofNat {l} := F.le_antisymm _ _ h{} h{}",
            ui + 1,
            li + 1
        ));
        ordfield_add_edge(
            &mut edges,
            &ordfield_var_node(v),
            &ordfield_num_node(l),
            name.clone(),
            format!("{name}.symm"),
        );
    }

    // Congruence conflict: same function, ordered-field-implied-equal arguments,
    // contradictory asserted values.
    let mut conflict_lines: Option<Vec<String>> = None;
    'outer: for i in 0..uf_values.len() {
        for j in (i + 1)..uf_values.len() {
            let (gi, ai, vi, pi, hi_at) = &uf_values[i];
            let (gj, aj, vj, pj, hj_at) = &uf_values[j];
            if gi != gj {
                continue;
            }
            let contradictory = match (pi, pj) {
                (true, true) => vi != vj,
                (true, false) | (false, true) => vi == vj,
                (false, false) => false,
            };
            if !contradictory {
                continue;
            }
            let Some(arg_eq) = ordfield_eq_proof(&edges, ai, aj) else {
                continue;
            };
            let gs = euf_lia_san(gi);
            let (si, sj) = (euf_lia_san(ai), euf_lia_san(aj));
            let mut lines: Vec<String> = Vec::new();
            if ai == aj {
                lines.push(format!(
                    "have hbr : m.f_{gs} (m.x_{si}) = m.f_{gs} (m.x_{sj}) := rfl"
                ));
            } else {
                lines.push(format!("have harg : m.x_{si} = m.x_{sj} := {arg_eq}"));
                lines.push(format!(
                    "have hbr : m.f_{gs} (m.x_{si}) = m.f_{gs} (m.x_{sj}) := by rw [harg]"
                ));
            }
            let (hi_name, hj_name) = (format!("h{}", hi_at + 1), format!("h{}", hj_at + 1));
            match (pi, pj) {
                (true, true) => {
                    lines.push(format!(
                        "have hnum : (F.ofNat {vi} : F.carrier) = F.ofNat {vj} := \
                         (({hi_name}.symm).trans hbr).trans {hj_name}"
                    ));
                    lines.push("exact F.ofNat_ne (by decide) hnum".to_string());
                }
                (true, false) => {
                    lines.push(format!("exact {hj_name} ((hbr.symm).trans {hi_name})"))
                }
                (false, true) => {
                    lines.push(format!("exact {hi_name} (hbr.trans ({hj_name}.symm))"))
                }
                (false, false) => continue,
            }
            conflict_lines = Some(lines);
            break 'outer;
        }
    }
    // Fallback: a ONE-VARIABLE bound contradiction, e.g. `x >= 10 && x <= 5`,
    // `x > 5 && x < 5`, `x > 1 && x < 1`. Both bounds are collapsed onto the
    // numerals by `le_trans` and closed by `OrdField.lt_le_absurd`. This is a
    // pure ordered-field argument: it never divides, never counts integers, and
    // never treats a strict bound as if it pinned a value.
    let bound_conflict = || -> Option<Vec<String>> {
        for v in &real_vars {
            let (Some(&(l, li, l_strict)), Some(&(u, ui, u_strict))) =
                (bound_lo.get(v), bound_hi.get(v))
            else {
                continue;
            };
            if l < u || (l == u && !l_strict && !u_strict) {
                continue; // the interval is non-empty in an ordered field
            }
            let sv = euf_lia_san(v);
            let (hl, hu) = (format!("h{}", li + 1), format!("h{}", ui + 1));
            // A strict bound `a < b` yields the weak `a ≤ b` as its first
            // conjunct, so both kinds reduce to `F.le` here.
            let weak_lo = if l_strict {
                format!("{hl}.1")
            } else {
                hl.clone()
            };
            let weak_up = if u_strict {
                format!("{hu}.1")
            } else {
                hu.clone()
            };
            let lines = if l > u {
                vec![
                    format!("have hlo : F.le (F.ofNat {l}) (m.x_{sv}) := {weak_lo}"),
                    format!("have hup : F.le (m.x_{sv}) (F.ofNat {u}) := {weak_up}"),
                    format!(
                        "have hcross : F.le (F.ofNat {l}) (F.ofNat {u}) := F.le_trans _ _ _ hlo hup"
                    ),
                    format!(
                        "have hlt : F.lt (F.ofNat {u}) (F.ofNat {l}) := F.ofNat_lt_of_lt (by decide)"
                    ),
                    "exact F.lt_le_absurd hlt hcross".to_string(),
                ]
            } else if l_strict {
                // `ofNat l < x` together with `x ≤ ofNat l`.
                vec![
                    format!("have hup : F.le (m.x_{sv}) (F.ofNat {u}) := {weak_up}"),
                    format!("exact F.lt_le_absurd {hl} hup"),
                ]
            } else {
                // `x < ofNat u` together with `ofNat u ≤ x`.
                vec![
                    format!("have hlo : F.le (F.ofNat {l}) (m.x_{sv}) := {weak_lo}"),
                    format!("exact F.lt_le_absurd {hu} hlo"),
                ]
            };
            return Some(lines);
        }
        None
    };

    // The pins are premises of the congruence bridge only; the bound refutation
    // does not use them, so it does not carry them.
    let mut leaf: Vec<String> = vec!["exfalso".to_string()];
    if let Some(lines) = conflict_lines {
        leaf.extend(pin_lines);
        leaf.extend(lines);
    } else {
        leaf.extend(bound_conflict()?);
    }

    if atoms.iter().any(|a| atom_prop_defeats_closure(&a.prop)) {
        return None;
    }

    Some(render_euf_ordfield_congruence_lean(
        &atoms, &real_vars, &uf_funcs, &leaf,
    ))
}

/// Recursively emit the nested `by_cases` block for the fused conflict clause.
/// Mirrors `euf_lia_emit_block`, except the leaf is supplied by the caller (the
/// ordered-field refutation) instead of being a fixed `omega`.
fn ordfield_emit_block(
    atoms: &[OrdFieldAtom],
    idx: usize,
    indent: &str,
    leaf: &[String],
) -> Vec<String> {
    if idx == atoms.len() {
        return leaf.iter().map(|l| format!("{indent}{l}")).collect();
    }
    let a = &atoms[idx];
    let hyp = format!("h{}", idx + 1);
    let child = format!("{indent}  ");
    let cont = ordfield_emit_block(atoms, idx + 1, &child, leaf);
    let close = vec![format!("{child}simp [clauseSat, litSat, atomVal, {hyp}]")];
    let bulletize = |sub: &[String]| -> Vec<String> {
        sub.iter()
            .enumerate()
            .map(|(k, line)| {
                if k == 0 {
                    let content = line
                        .strip_prefix(child.as_str())
                        .unwrap_or(line.trim_start());
                    format!("{indent}· {content}")
                } else {
                    line.clone()
                }
            })
            .collect()
    };
    let mut lines = vec![format!("{indent}by_cases {hyp} : ({})", a.prop)];
    // Lean `by_cases h : P` yields the `P` (true) branch first, then `¬P`.
    if a.cv {
        lines.extend(bulletize(&cont));
        lines.extend(bulletize(&close));
    } else {
        lines.extend(bulletize(&close));
        lines.extend(bulletize(&cont));
    }
    lines
}

/// Render the fused EUF + ordered-field congruence firewall file.
fn render_euf_ordfield_congruence_lean(
    atoms: &[OrdFieldAtom],
    real_vars: &std::collections::BTreeSet<String>,
    uf_funcs: &std::collections::BTreeSet<String>,
    leaf: &[String],
) -> String {
    let n = atoms.len();
    let lemma_id = n + 1;
    let proof_id = n + 2;

    let fields = {
        let mut f: Vec<String> = real_vars
            .iter()
            .map(|v| format!("  x_{} : F.carrier", euf_lia_san(v)))
            .collect();
        f.extend(
            uf_funcs
                .iter()
                .map(|g| format!("  f_{} : F.carrier -> F.carrier", euf_lia_san(g))),
        );
        f.join("\n")
    };
    let arms = atoms
        .iter()
        .enumerate()
        .map(|(i, a)| format!("  | {} => decide ({})", i + 1, a.prop))
        .collect::<Vec<_>>()
        .join("\n");
    let orig = atoms
        .iter()
        .enumerate()
        .map(|(i, a)| {
            let lit = if a.cv {
                format!("{}", i + 1)
            } else {
                format!("-{}", i + 1)
            };
            format!("({}, [{lit}])", i + 1)
        })
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_lits = atoms
        .iter()
        .enumerate()
        .map(|(i, a)| {
            if a.cv {
                format!("-{}", i + 1)
            } else {
                format!("{}", i + 1)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let proof_hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    let proof_body = ordfield_emit_block(atoms, 0, "  ", leaf).join("\n");

    let hash = fnv_hex(
        &atoms
            .iter()
            .map(|a| format!("{}:{}", a.cv, a.prop))
            .collect::<Vec<_>>()
            .join("\u{1}"),
    );

    format!(
        r#"import AySoundness.Firewall
import AySoundness.OrdField
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — REAL-SORTED EUF + LINEARLY-ORDERED-
  FIELD fused congruence-value conflict, grounded in the verified
  `firewall_combined_unsat`.

  FAITHFULNESS. The sort is `Real`. Lean core has no ℝ, and a `no_model` over
  `Int`/`Rat` would certify "no INTEGER/RATIONAL model" — strictly weaker than
  the CLI's `unsat` over ℝ. Instead the model type is parameterised by an
  ARBITRARY linearly ordered field `F : AySoundness.OrdField`, so the theorem
  below reads "no model in ANY linearly ordered field", which DOES entail "no
  real model" (ℝ is a linearly ordered field). `AySoundness.ordField_nonvacuous`
  exhibits `Rat` as an instance, so the quantification is not vacuous.

  The refutation is purely EQUATIONAL + CONGRUENCE, so no field-specific decision
  procedure is needed: the Int emitter's `omega` steps are replaced by
    * bound pinning      `x >= k` and `x <= k` give `x = k`  — `le_antisymm`
    * numeral conflict   `c1 != c2`                          — `OrdField.ofNat_ne`
  and the congruence bridge `f x = f y` stays a plain `rw`. NO integer reasoning
  appears anywhere: strict bounds pin nothing, because `x > 5 && x < 7` leaves
  `x` free in an ordered field. Atoms are Props over an abstract carrier, so they
  are decided classically (`Classical.propDecidable`, hence a `noncomputable`
  `atomVal`), exactly as the existing array emitters already do. All tactics are
  Lean 4 core (no Mathlib). axioms ⊆ {{propext, Classical.choice, Quot.sound}}.
-/
namespace AySoundness.Emitted.EufOrdFieldCong_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

/-- Model: an arbitrary linearly ordered field `F`, a valuation of the Real
    constants, and the uninterpreted `Real -> Real` functions. -/
structure Val (F : OrdField) where
{fields}

/-- Atoms (one per asserted frontend atom, in assertion order). -/
noncomputable def atomVal (F : OrdField) (m : Val F) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof_id}, [], [{proof_hints}])]

/-- The fused conflict clause is valid in EVERY ordered-field model: any
    deviation from the asserted polarities satisfies the clause; the
    all-consistent case is refuted through the congruence bridge. -/
theorem euf_ordfield_lemma_valid (F : OrdField) (m : Val F) :
    clauseSat (atomVal F m) [{lemma_lits}] = true := by
{proof_body}

theorem lemmas_valid (F : OrdField) :
    ∀ cl ∈ clauses lemmas, ∀ m : Val F, clauseSat (atomVal F m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact euf_ordfield_lemma_valid F m

/-- **No model in ANY linearly ordered field** — in particular none over ℝ —
    satisfies the asserted conjunction. Via the verified firewall. -/
theorem no_model (F : OrdField) : ∀ m : Val F, ¬ Sat (atomVal F m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    (atomVal F) (by decide) (by decide) (lemmas_valid F) (by decide)

end AySoundness.Emitted.EufOrdFieldCong_{hash}
"#,
    )
}

/// Reserved separator: an SMT symbol cannot contain U+0001, so a UF-application
/// linear-form key `"<g>\u{1}<arg>"` never collides with a bare int-variable key.
fn cbr_uf_key(g: &str, arg: &str) -> String {
    format!("{g}\u{1}{arg}")
}

/// `true` iff `op` is a builtin (arithmetic / relational / logical / array /
/// datatype) operator rather than an uninterpreted function symbol.
fn cbr_is_builtin_op(op: &str) -> bool {
    matches!(
        op,
        "+" | "-"
            | "*"
            | "/"
            | "div"
            | "mod"
            | "abs"
            | "="
            | ">="
            | "<="
            | ">"
            | "<"
            | "not"
            | "and"
            | "or"
            | "=>"
            | "xor"
            | "ite"
            | "select"
            | "store"
            | "distinct"
            | "to_int"
            | "to_real"
    )
}

/// Resolve one surface symbol only when it has exactly one active declaration.
///
/// Parsed assertions retain the surface name, not an overload identity. Any
/// overloaded name is therefore ambiguous at this diagnostic boundary and must
/// be declined rather than guessed.
fn firewall_unique_symbol_info<'a>(
    context: &'a ay_frontend::Context,
    name: &str,
) -> Option<&'a ay_frontend::SymbolInfo> {
    let mut matches = context
        .symbols_iter()
        .filter_map(|(surface, info)| (surface == name).then_some(info));
    let info = matches.next()?;
    if matches.next().is_some() {
        return None;
    }
    Some(info)
}

/// Parse `name` as ay's lenient signed-Int literal only when no declaration has
/// that exact surface name. SMT-LIB quoted symbols lose their quoting in
/// `ParsedTerm`, so a declared `|-1|` and the numeric-looking text `-1` are
/// distinguishable here only through `Context`. One wrong-signature declaration
/// or multiple overloaded declarations must therefore decline, not fall back to
/// a literal.
fn firewall_undeclared_i64_symbol_literal(
    context: &ay_frontend::Context,
    name: &str,
) -> Option<i64> {
    if context.symbols_iter().any(|(surface, _)| surface == name) {
        return None;
    }
    name.parse::<i64>().ok()
}

fn cbr_is_int_constant(context: &ay_frontend::Context, name: &str) -> bool {
    firewall_unique_symbol_info(context, name)
        .is_some_and(|info| info.arg_sorts.is_empty() && info.sort == Sort::Int)
}

fn cbr_is_int_unary_function(context: &ay_frontend::Context, name: &str) -> bool {
    firewall_unique_symbol_info(context, name).is_some_and(|info| {
        matches!(info.arg_sorts.as_slice(), [Sort::Int]) && info.sort == Sort::Int
    })
}

/// Checked linear-form addition shared by the parsed-assertion emitters. A
/// source-level integer expression is unbounded, while these recognizers use
/// `i64` as a deliberately small analysis domain; any coefficient/constant
/// that leaves that domain must decline instead of panicking or wrapping.
fn firewall_lin_add_checked(a: &EufLiaLin, b: &EufLiaLin, sign: i64) -> Option<EufLiaLin> {
    let mut coeffs = a.coeffs.clone();
    for (v, &c) in &b.coeffs {
        let scaled = sign.checked_mul(c)?;
        let current = coeffs.get(v).copied().unwrap_or_default();
        let next = current.checked_add(scaled)?;
        if next == 0 {
            coeffs.remove(v);
        } else {
            coeffs.insert(v.clone(), next);
        }
    }
    Some(EufLiaLin {
        coeffs,
        konst: a.konst.checked_add(sign.checked_mul(b.konst)?)?,
    })
}

/// Checked linear-form scaling shared by the parsed-assertion emitters.
fn firewall_lin_scale_checked(a: &EufLiaLin, scale: i64) -> Option<EufLiaLin> {
    let mut coeffs = a.coeffs.clone();
    for coeff in coeffs.values_mut() {
        *coeff = coeff.checked_mul(scale)?;
    }
    coeffs.retain(|_, &mut coeff| coeff != 0);
    Some(EufLiaLin {
        coeffs,
        konst: a.konst.checked_mul(scale)?,
    })
}

/// Convert a single-key comparison `c*x + d op 0` into inclusive integer
/// bounds. Intermediate arithmetic uses `i128`; conversion back to the
/// recognizer's `i64` domain is checked and an out-of-range boundary declines.
fn cbr_bound_lo_hi(
    op: &str,
    coefficient: i64,
    constant: i64,
) -> Option<(Option<i64>, Option<i64>)> {
    let d = i128::from(constant);
    let checked = |value: i128| i64::try_from(value).ok();
    match (op, coefficient) {
        (">=", 1) => Some((Some(checked(-d)?), None)),
        (">=", -1) => Some((None, Some(constant))),
        (">", 1) => Some((Some(checked(-d + 1)?), None)),
        (">", -1) => Some((None, Some(checked(d - 1)?))),
        ("<=", 1) => Some((None, Some(checked(-d)?))),
        ("<=", -1) => Some((Some(constant), None)),
        ("<", 1) => Some((None, Some(checked(-d - 1)?))),
        ("<", -1) => Some((Some(checked(d + 1)?), None)),
        _ => Some((None, None)),
    }
}

/// Solve `coefficient*x + constant = 0` inside the recognizer's `i64`
/// analysis domain without `MIN / -1` or negation overflow.
fn cbr_single_key_pin(coefficient: i64, constant: i64) -> Option<Option<i64>> {
    if coefficient == 0 {
        return Some(None);
    }
    let numerator = -i128::from(constant);
    let denominator = i128::from(coefficient);
    if numerator % denominator != 0 {
        return Some(None);
    }
    Some(Some(i64::try_from(numerator / denominator).ok()?))
}

/// Like `euf_lia_lin_of`, but a single-application UF term `(g x)` (g NOT a
/// builtin operator, x a bare symbol) is admitted as an OPAQUE integer atom,
/// keyed `cbr_uf_key(g, x)` and recorded in `uf_apps`. This lets a congruence
/// bridge `f s = f t` be closed by `omega` over these atoms. Any other
/// non-linear / non-Int shape (a Real `Decimal`, a nested/compound UF argument,
/// a nonlinear product) returns `None` (fail-closed).
fn cbr_lin_of(
    t: &PTerm,
    uf_apps: &mut std::collections::BTreeMap<String, (String, String)>,
    context: &ay_frontend::Context,
) -> Option<EufLiaLin> {
    use std::collections::BTreeMap;
    match t {
        PTerm::Symbol(v) if cbr_is_int_constant(context, v) => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(v.clone(), 1i64);
            Some(EufLiaLin { coeffs, konst: 0 })
        }
        PTerm::Const(PConst::Numeral(n)) => Some(EufLiaLin {
            coeffs: BTreeMap::new(),
            konst: n.parse::<i64>().ok()?,
        }),
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("+", _) if !args.is_empty() => {
                let mut acc = EufLiaLin {
                    coeffs: BTreeMap::new(),
                    konst: 0,
                };
                for a in args {
                    acc = firewall_lin_add_checked(&acc, &cbr_lin_of(a, uf_apps, context)?, 1)?;
                }
                Some(acc)
            }
            ("-", 1) => firewall_lin_scale_checked(&cbr_lin_of(&args[0], uf_apps, context)?, -1),
            ("-", n) if n >= 2 => {
                let mut acc = cbr_lin_of(&args[0], uf_apps, context)?;
                for a in &args[1..] {
                    acc = firewall_lin_add_checked(&acc, &cbr_lin_of(a, uf_apps, context)?, -1)?;
                }
                Some(acc)
            }
            ("*", _) if !args.is_empty() => {
                let mut acc = EufLiaLin {
                    coeffs: BTreeMap::new(),
                    konst: 1,
                };
                for a in args {
                    let l = cbr_lin_of(a, uf_apps, context)?;
                    if acc.coeffs.is_empty() {
                        acc = firewall_lin_scale_checked(&l, acc.konst)?;
                    } else if l.coeffs.is_empty() {
                        acc = firewall_lin_scale_checked(&acc, l.konst)?;
                    } else {
                        return None; // nonlinear product of two variable terms
                    }
                }
                Some(acc)
            }
            // Single-application UF atom `(g x)` — an opaque integer atom.
            (g, 1) if !cbr_is_builtin_op(g) => {
                let PTerm::Symbol(arg) = &args[0] else {
                    return None;
                };
                if !cbr_is_int_constant(context, arg) || !cbr_is_int_unary_function(context, g) {
                    return None;
                }
                let key = cbr_uf_key(g, arg);
                uf_apps.insert(key.clone(), (g.to_string(), arg.clone()));
                let mut coeffs = BTreeMap::new();
                coeffs.insert(key, 1i64);
                Some(EufLiaLin { coeffs, konst: 0 })
            }
            _ => None,
        },
        _ => None,
    }
}

/// Render a linear-integer term (admitting single-application UF terms) to a Lean
/// `Int` expression over the `Val` model: `m.x_<v>` per int variable, `(n : Int)`
/// per numeral, `m.f_<g> (m.x_<arg>)` per UF application. Mirrors `cbr_lin_of`.
fn cbr_render_int(t: &PTerm, context: &ay_frontend::Context) -> Option<String> {
    match t {
        PTerm::Symbol(v) if cbr_is_int_constant(context, v) => {
            Some(format!("m.x_{}", euf_lia_san(v)))
        }
        PTerm::Const(PConst::Numeral(n)) => {
            n.parse::<i64>().ok()?;
            Some(format!("({n} : Int)"))
        }
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("+", _) if !args.is_empty() => {
                let parts: Option<Vec<String>> = args
                    .iter()
                    .map(|arg| cbr_render_int(arg, context))
                    .collect();
                Some(format!("({})", parts?.join(" + ")))
            }
            ("-", 1) => Some(format!("(- {})", cbr_render_int(&args[0], context)?)),
            ("-", n) if n >= 2 => {
                let parts: Option<Vec<String>> = args
                    .iter()
                    .map(|arg| cbr_render_int(arg, context))
                    .collect();
                Some(format!("({})", parts?.join(" - ")))
            }
            ("*", _) if !args.is_empty() => {
                let parts: Option<Vec<String>> = args
                    .iter()
                    .map(|arg| cbr_render_int(arg, context))
                    .collect();
                Some(format!("({})", parts?.join(" * ")))
            }
            (g, 1) if !cbr_is_builtin_op(g) => {
                let PTerm::Symbol(arg) = &args[0] else {
                    return None;
                };
                if !cbr_is_int_constant(context, arg) || !cbr_is_int_unary_function(context, g) {
                    return None;
                }
                Some(format!("m.f_{} (m.x_{})", euf_lia_san(g), euf_lia_san(arg)))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Emit a verified-firewall Lean proof for an EUF CONGRUENCE conflict that closes
/// a LINEAR-INTEGER (bound / equality / disequality) system once the
/// congruence-derived equality `f s = f t` (from an LIA-implied `s = t`) is
/// injected — bucket "euf_cong_bridge".
///
/// This is the sibling of `emit_euf_lia_congruence_firewall_lean_from_parsed`:
/// that one closes a VALUE-atom pair (`f x = c1`, `f y = c2`); this one closes the
/// cases where the UF applications appear inside INEQUALITY bounds
/// (`f a < 0 ∧ f b ≥ 0` with `a = b`) or a DIRECT disequality
/// (`f x ≠ f y` with `x + 1 = y + 1`). Assertions that are not linear-integer /
/// UF atoms (e.g. an inert array `store`-equality) are DROPPED from the emitted
/// core — sound because a refutation of a SUBSET of the assertions refutes the
/// whole (the kernel-checked `no_model` is over exactly the retained atoms).
///
/// Fail-closed: fires ONLY when a genuine congruence-mediated conflict is
/// detected (a single-variable bound infeasibility over a merged UF-application
/// class, or a disequality between two congruent applications) AND at least one
/// congruence bridge is generated — so pure-LIA conflicts (no UF) are left to the
/// LIA emitter. Every retained surface symbol must also resolve unambiguously in
/// `context` as an Int constant or Int → Int function; Real, missing, or
/// overloaded declarations decline. axioms ⊆ {propext, Quot.sound}; NO Mathlib,
/// no new AySoundness lemma, no `sorry`.
pub(crate) fn emit_euf_congruence_bridge_firewall_lean_from_parsed(
    parsed: &[PTerm],
    context: &ay_frontend::Context,
) -> Option<String> {
    use std::collections::{BTreeMap, BTreeSet, HashMap};

    const MAX_CBR_ATOMS: usize = 64;
    const MAX_CBR_BRIDGES: usize = 64;

    if parsed.is_empty() {
        return None;
    }

    let mut atoms: Vec<EufLiaAtom> = Vec::new();
    let mut int_vars: BTreeSet<String> = BTreeSet::new();
    let mut uf_funcs: BTreeSet<String> = BTreeSet::new();
    let mut uf_apps: BTreeMap<String, (String, String)> = BTreeMap::new();
    // Positive `=` diffs with ONLY int-variable keys (drive arg equivalence).
    let mut iv_eq_diffs: Vec<EufLiaLin> = Vec::new();
    // Positive bounds with ONLY int-variable keys (drive int-variable pins).
    let mut iv_bound_atoms: Vec<(String, EufLiaLin)> = Vec::new();
    // Every positive single-key bound (int-variable OR UF-application key).
    let mut all_bounds: Vec<(String, EufLiaLin)> = Vec::new();
    // Positive single-key equalities (pins) over any key.
    let mut all_eq_diffs: Vec<EufLiaLin> = Vec::new();
    // Negative `=` atom diffs — candidate disequality conflicts.
    let mut neg_eq_diffs: Vec<EufLiaLin> = Vec::new();

    for asrt in parsed {
        let (inner, positive) = match asrt {
            PTerm::App(op, a) if op == "not" && a.len() == 1 => (&a[0], false),
            other => (other, true),
        };
        let PTerm::App(op, args) = inner else {
            // A non-application assertion (bare symbol/const): drop it.
            continue;
        };
        let lean_op = match op.as_str() {
            "=" => "=",
            ">=" => ">=",
            "<=" => "<=",
            ">" => ">",
            "<" => "<",
            // Any other head (store-equality already handled via `=`; disjunctions,
            // array atoms, …) is inert to this conflict shape — drop from the core.
            _ => continue,
        };
        if args.len() != 2 {
            continue;
        }
        let mut local_apps: BTreeMap<String, (String, String)> = BTreeMap::new();
        let (la, lb) = (
            cbr_lin_of(&args[0], &mut local_apps, context),
            cbr_lin_of(&args[1], &mut local_apps, context),
        );
        let (Some(la), Some(lb)) = (la, lb) else {
            // Un-modellable operand (array store, compound UF arg, Real, …): drop.
            continue;
        };
        let (Some(sa), Some(sb)) = (
            cbr_render_int(&args[0], context),
            cbr_render_int(&args[1], context),
        ) else {
            continue;
        };
        if atoms.len() >= MAX_CBR_ATOMS {
            return None;
        }
        // Commit this atom's symbols.
        for (k, (g, arg)) in &local_apps {
            uf_apps.insert(k.clone(), (g.clone(), arg.clone()));
            uf_funcs.insert(g.clone());
            int_vars.insert(arg.clone());
        }
        for k in la.coeffs.keys().chain(lb.coeffs.keys()) {
            if !k.contains('\u{1}') {
                int_vars.insert(k.clone());
            }
        }
        atoms.push(EufLiaAtom {
            prop: format!("{sa} {lean_op} {sb}"),
            cv: positive,
        });
        let diff = firewall_lin_add_checked(&la, &lb, -1)?;
        let has_uf_key = diff.coeffs.keys().any(|k| k.contains('\u{1}'));
        if op == "=" {
            if positive {
                all_eq_diffs.push(diff.clone());
                if !has_uf_key {
                    iv_eq_diffs.push(diff);
                }
            } else {
                neg_eq_diffs.push(diff);
            }
        } else if positive {
            all_bounds.push((op.clone(), diff.clone()));
            if !has_uf_key {
                iv_bound_atoms.push((op.clone(), diff));
            }
        }
    }

    if atoms.is_empty() || uf_apps.is_empty() {
        return None;
    }
    // Determinism / collision guard (mirrors the value-atom emitter).
    {
        let mut seen: HashMap<String, String> = HashMap::new();
        for v in &int_vars {
            if let Some(prev) = seen.insert(euf_lia_san(v), v.clone()) {
                if &prev != v {
                    return None;
                }
            }
        }
        let mut seenf: HashMap<String, String> = HashMap::new();
        for g in &uf_funcs {
            if let Some(prev) = seenf.insert(euf_lia_san(g), g.clone()) {
                if &prev != g {
                    return None;
                }
            }
        }
    }

    // --- Int-variable pin / union-find analysis (over int-variable keys only, so
    // an implied `s = t` is genuinely LIA-derivable — the bridge's inner `by
    // omega` then always succeeds). ---
    let mut lbnd: HashMap<String, i64> = HashMap::new();
    let mut ubnd: HashMap<String, i64> = HashMap::new();
    for (op, diff) in &iv_bound_atoms {
        if diff.coeffs.len() != 1 {
            continue;
        }
        let Some((v, &c)) = diff.coeffs.iter().next() else {
            continue;
        };
        let (lo, hi) = cbr_bound_lo_hi(op, c, diff.konst)?;
        if let Some(l) = lo {
            let e = lbnd.entry(v.clone()).or_insert(l);
            if l > *e {
                *e = l;
            }
        }
        if let Some(h) = hi {
            let e = ubnd.entry(v.clone()).or_insert(h);
            if h < *e {
                *e = h;
            }
        }
    }
    let mut pins: HashMap<String, i64> = HashMap::new();
    for v in &int_vars {
        if let (Some(&l), Some(&h)) = (lbnd.get(v), ubnd.get(v)) {
            if l == h {
                pins.insert(v.clone(), l);
            }
        }
    }
    let mut parent: HashMap<String, String> = HashMap::new();
    for v in &int_vars {
        parent.insert(v.clone(), v.clone());
    }
    loop {
        let mut changed = false;
        for diff in &iv_eq_diffs {
            let mut coeffs = diff.coeffs.clone();
            let mut konst = diff.konst;
            let pinned: Vec<String> = coeffs
                .keys()
                .filter(|v| pins.contains_key(*v))
                .cloned()
                .collect();
            for v in pinned {
                let c = coeffs.remove(&v)?;
                let pin = *pins.get(&v)?;
                konst = konst.checked_add(c.checked_mul(pin)?)?;
            }
            coeffs.retain(|_, &mut c| c != 0);
            match coeffs.len() {
                1 => {
                    let Some((v, &c)) = coeffs.iter().next() else {
                        continue;
                    };
                    if let Some(val) = cbr_single_key_pin(c, konst)? {
                        if pins.get(v) != Some(&val) {
                            pins.insert(v.clone(), val);
                            changed = true;
                        }
                    }
                }
                2 => {
                    let mut it = coeffs.iter();
                    let (Some((v1, &c1)), Some((v2, &c2)), None) =
                        (it.next(), it.next(), it.next())
                    else {
                        continue;
                    };
                    if i128::from(c1) == -i128::from(c2) && c1 != 0 && konst == 0 {
                        let r1 = euf_lia_find(&mut parent, v1);
                        let r2 = euf_lia_find(&mut parent, v2);
                        if r1 != r2 {
                            parent.insert(r1, r2);
                            changed = true;
                        }
                    }
                }
                _ => {}
            }
        }
        if !changed {
            break;
        }
    }
    let mut class_pin: HashMap<String, i64> = HashMap::new();
    for (v, &p) in &pins {
        let r = euf_lia_find(&mut parent, v);
        class_pin.entry(r).or_insert(p);
    }
    // Canonical arg class: two int variables collapse iff LIA-implied equal
    // (same union root, or pinned to the same constant).
    let mut arg_class = |v: &str| -> String {
        let r = euf_lia_find(&mut parent, v);
        match class_pin.get(&r) {
            Some(p) => format!("\u{2}pin\u{2}{p}"),
            None => r,
        }
    };
    // Canonical class of any linear-form key (int variable or UF application).
    let mut key_class = |k: &str| -> String {
        if let Some((g, arg)) = uf_apps.get(k) {
            format!("{g}\u{1}{}", arg_class(arg))
        } else {
            arg_class(k)
        }
    };

    // --- Conflict detection (SOUND under-approximation of infeasibility). ---
    // (A) single-key bound infeasibility over merged classes: a lower bound above
    //     an upper bound (candidate `f a < 0 ∧ f b ≥ 0`, a = b).
    let mut clb: HashMap<String, i64> = HashMap::new();
    let mut cub: HashMap<String, i64> = HashMap::new();
    for (op, diff) in &all_bounds {
        if diff.coeffs.len() != 1 {
            continue;
        }
        let Some((k, &c)) = diff.coeffs.iter().next() else {
            continue;
        };
        let (lo, hi) = cbr_bound_lo_hi(op, c, diff.konst)?;
        let cls = key_class(k);
        if let Some(l) = lo {
            let e = clb.entry(cls.clone()).or_insert(l);
            if l > *e {
                *e = l;
            }
        }
        if let Some(h) = hi {
            let e = cub.entry(cls).or_insert(h);
            if h < *e {
                *e = h;
            }
        }
    }
    for diff in &all_eq_diffs {
        // A single-key equality `k + d = 0` pins class(k) to -d.
        if diff.coeffs.len() == 1 {
            let Some((k, &c)) = diff.coeffs.iter().next() else {
                continue;
            };
            if let Some(val) = cbr_single_key_pin(c, diff.konst)? {
                let cls = key_class(k);
                let el = clb.entry(cls.clone()).or_insert(val);
                if val > *el {
                    *el = val;
                }
                let eu = cub.entry(cls).or_insert(val);
                if val < *eu {
                    *eu = val;
                }
            }
        }
    }
    let mut has_conflict = false;
    for (cls, &l) in &clb {
        if let Some(&h) = cub.get(cls) {
            if l > h {
                has_conflict = true;
            }
        }
    }
    // (B) disequality between two congruent terms (candidate `f x ≠ f y`, x = y).
    for diff in &neg_eq_diffs {
        if diff.coeffs.len() == 2 && diff.konst == 0 {
            let mut it = diff.coeffs.iter();
            let (Some((k1, &c1)), Some((k2, &c2)), None) = (it.next(), it.next(), it.next()) else {
                continue;
            };
            if i128::from(c1) == -i128::from(c2) && c1 != 0 && key_class(k1) == key_class(k2) {
                has_conflict = true;
            }
        }
    }

    // --- Congruence bridges: every pair of DISTINCT UF applications sharing a
    // function whose arguments are LIA-implied equal. ---
    let mut bridges: BTreeSet<(String, String, String)> = BTreeSet::new();
    let app_list: Vec<(String, String)> = uf_apps.values().cloned().collect();
    for i in 0..app_list.len() {
        for j in (i + 1)..app_list.len() {
            let (gi, ai) = &app_list[i];
            let (gj, aj) = &app_list[j];
            if gi != gj || ai == aj {
                continue;
            }
            if arg_class(ai) == arg_class(aj) {
                let (lo, hi) = if ai <= aj { (ai, aj) } else { (aj, ai) };
                bridges.insert((gi.clone(), lo.clone(), hi.clone()));
            }
        }
    }

    if !has_conflict || bridges.is_empty() || bridges.len() > MAX_CBR_BRIDGES {
        return None;
    }

    Some(render_euf_lia_congruence_lean(
        &atoms,
        &int_vars,
        &uf_funcs,
        &bridges.into_iter().collect::<Vec<_>>(),
    ))
}

/// One `(= ARR (store BASE IDX VAL))` array-defining equality (IDX/VAL Int
/// numerals; ARR/BASE array symbols). BASE may equal ARR (a self-store fixpoint).
struct C4Store {
    arr: String,
    base: String,
    idx: i64,
    val: i64,
}

fn c4_is_int_array_constant(context: &ay_frontend::Context, name: &str) -> bool {
    firewall_unique_symbol_info(context, name).is_some_and(|info| {
        if !info.arg_sorts.is_empty() {
            return false;
        }
        matches!(
            &info.sort,
            Sort::Array(array)
                if array.index_sort.is_int() && array.element_sort.is_int()
        )
    })
}

/// Match `(select ARR IDX)` with ARR a symbol and IDX an Int numeral.
fn c4_match_select(t: &PTerm, context: &ay_frontend::Context) -> Option<(String, i64)> {
    let PTerm::App(op, args) = t else {
        return None;
    };
    if op != "select" || args.len() != 2 {
        return None;
    }
    let PTerm::Symbol(arr) = &args[0] else {
        return None;
    };
    if !c4_is_int_array_constant(context, arr) {
        return None;
    }
    let PTerm::Const(PConst::Numeral(n)) = &args[1] else {
        return None;
    };
    Some((arr.clone(), n.parse::<i64>().ok()?))
}

/// Match `(store BASE IDX VAL)` with BASE a symbol and IDX/VAL Int numerals.
fn c4_match_store(t: &PTerm, context: &ay_frontend::Context) -> Option<(String, i64, i64)> {
    let PTerm::App(op, args) = t else {
        return None;
    };
    if op != "store" || args.len() != 3 {
        return None;
    }
    let PTerm::Symbol(base) = &args[0] else {
        return None;
    };
    if !c4_is_int_array_constant(context, base) {
        return None;
    }
    let PTerm::Const(PConst::Numeral(i)) = &args[1] else {
        return None;
    };
    let PTerm::Const(PConst::Numeral(v)) = &args[2] else {
        return None;
    };
    Some((base.clone(), i.parse::<i64>().ok()?, v.parse::<i64>().ok()?))
}

/// Linear-integer form over `select`-atoms: `(select ARR IDX)` (IDX a numeral) is
/// an opaque integer atom keyed `"select\u{1}<arr>\u{1}<idx>"`; numerals /
/// `+`/`-`/`*` compose linearly. Any other shape (a bare symbol, a symbolic
/// index, …) returns `None` (fail-closed — keeps the emitter to the fully-ground
/// select→arithmetic case it can prove).
fn c4_lin_of(
    t: &PTerm,
    selects: &mut std::collections::BTreeMap<String, (String, i64)>,
    context: &ay_frontend::Context,
) -> Option<EufLiaLin> {
    use std::collections::BTreeMap;
    if let Some((arr, idx)) = c4_match_select(t, context) {
        let key = format!("select\u{1}{arr}\u{1}{idx}");
        selects.insert(key.clone(), (arr, idx));
        let mut coeffs = BTreeMap::new();
        coeffs.insert(key, 1i64);
        return Some(EufLiaLin { coeffs, konst: 0 });
    }
    match t {
        PTerm::Const(PConst::Numeral(n)) => Some(EufLiaLin {
            coeffs: BTreeMap::new(),
            konst: n.parse::<i64>().ok()?,
        }),
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("+", _) if !args.is_empty() => {
                let mut acc = EufLiaLin {
                    coeffs: BTreeMap::new(),
                    konst: 0,
                };
                for a in args {
                    acc = firewall_lin_add_checked(&acc, &c4_lin_of(a, selects, context)?, 1)?;
                }
                Some(acc)
            }
            ("-", 1) => firewall_lin_scale_checked(&c4_lin_of(&args[0], selects, context)?, -1),
            ("-", n) if n >= 2 => {
                let mut acc = c4_lin_of(&args[0], selects, context)?;
                for a in &args[1..] {
                    acc = firewall_lin_add_checked(&acc, &c4_lin_of(a, selects, context)?, -1)?;
                }
                Some(acc)
            }
            ("*", _) if !args.is_empty() => {
                let mut acc = EufLiaLin {
                    coeffs: BTreeMap::new(),
                    konst: 1,
                };
                for a in args {
                    let l = c4_lin_of(a, selects, context)?;
                    if acc.coeffs.is_empty() {
                        acc = firewall_lin_scale_checked(&l, acc.konst)?;
                    } else if l.coeffs.is_empty() {
                        acc = firewall_lin_scale_checked(&acc, l.konst)?;
                    } else {
                        return None;
                    }
                }
                Some(acc)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Render a `select`-bearing linear term to a Lean `Int` expression over the array
/// model: `(select ARR IDX)` → `m.<arr> (<idx> : Int)`; numeral → `(n : Int)`.
fn c4_render_lia(t: &PTerm, context: &ay_frontend::Context) -> Option<String> {
    if let Some((arr, idx)) = c4_match_select(t, context) {
        return Some(format!("m.{} ({idx} : Int)", euf_lia_san(&arr)));
    }
    match t {
        PTerm::Const(PConst::Numeral(n)) => {
            n.parse::<i64>().ok()?;
            Some(format!("({n} : Int)"))
        }
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("+", _) if !args.is_empty() => {
                let parts: Option<Vec<String>> =
                    args.iter().map(|arg| c4_render_lia(arg, context)).collect();
                Some(format!("({})", parts?.join(" + ")))
            }
            ("-", 1) => Some(format!("(- {})", c4_render_lia(&args[0], context)?)),
            ("-", n) if n >= 2 => {
                let parts: Option<Vec<String>> =
                    args.iter().map(|arg| c4_render_lia(arg, context)).collect();
                Some(format!("({})", parts?.join(" - ")))
            }
            ("*", _) if !args.is_empty() => {
                let parts: Option<Vec<String>> =
                    args.iter().map(|arg| c4_render_lia(arg, context)).collect();
                Some(format!("({})", parts?.join(" * ")))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Emit a verified-firewall Lean proof for a FUSED array-ROW + LINEAR-INTEGER
/// conflict (bucket "array_sum_bound"): array-defining equalities
/// `arr = store(base, i, v)` PIN the reads `select arr i = v` (McCarthy RoW-1,
/// the verified `AySoundness.ArrayThy.sel_upd_same`), and those pinned values make
/// an integer (in)equality over the reads infeasible — the residual conflict is
/// closed by `omega`. Example: `b = store(a,0,10) ∧ b = store(b,1,20) ∧
/// (select b 0) + (select b 1) > 31` — `b[0]=10, b[1]=20`, so `30 > 31` is false.
///
/// Model: arrays are `Int → Int` functions, `store` is an `if`-update; each read
/// `select arr i` is grounded to its written value at the leaf by `congrFun` on
/// the store-equality hypothesis + `simp` (RoW-1), then the fully-ground integer
/// conflict is discharged by `omega`. Composed through `firewall_combined_unsat`;
/// the array-equality atoms use `Classical.propDecidable` (so `atomVal` is
/// `noncomputable`); axioms of `no_model` ⊆ {propext, Classical.choice, Quot.sound}.
///
/// Fail-closed: fires ONLY when every array surface symbol resolves uniquely in
/// `context` as a nullary `(Array Int Int)`, every `select` in the integer atoms
/// is grounded by a matching store-equality, and the ground integer system is
/// genuinely infeasible; declines otherwise.
pub(crate) fn emit_array_sum_bound_firewall_lean_from_parsed(
    parsed: &[PTerm],
    context: &ay_frontend::Context,
) -> Option<String> {
    use std::collections::{BTreeMap, BTreeSet};

    const MAX_C4_ATOMS: usize = 64;

    if parsed.is_empty() {
        return None;
    }

    // atoms[i] is EITHER a store-defining equality (recorded in `store_at[i]`) or
    // an integer atom (recorded in `lia_at[i]`), preserving assertion order so the
    // `by_cases` hypothesis `h{i+1}` lines up with the atom index.
    let mut atoms: Vec<EufLiaAtom> = Vec::new();
    let mut store_at: BTreeMap<usize, C4Store> = BTreeMap::new();
    let mut lia_at: BTreeMap<usize, EufLiaLin> = BTreeMap::new();
    let mut lia_ops: BTreeMap<usize, String> = BTreeMap::new();
    let mut arrays: BTreeSet<String> = BTreeSet::new();
    let mut selects: BTreeMap<String, (String, i64)> = BTreeMap::new();

    for asrt in parsed {
        // Only positively-asserted atoms participate in this ground conflict.
        let PTerm::App(op, args) = asrt else {
            continue;
        };
        if atoms.len() >= MAX_C4_ATOMS {
            return None;
        }
        // Array-defining equality `(= ARR (store BASE IDX VAL))` (either side).
        if op == "=" && args.len() == 2 {
            let stored = [(&args[0], &args[1]), (&args[1], &args[0])]
                .into_iter()
                .find_map(|(lhs, rhs)| {
                    let PTerm::Symbol(arr) = lhs else { return None };
                    if !c4_is_int_array_constant(context, arr) {
                        return None;
                    }
                    let (base, idx, val) = c4_match_store(rhs, context)?;
                    Some(C4Store {
                        arr: arr.clone(),
                        base,
                        idx,
                        val,
                    })
                });
            if let Some(st) = stored {
                arrays.insert(st.arr.clone());
                arrays.insert(st.base.clone());
                atoms.push(EufLiaAtom {
                    prop: format!(
                        "m.{} = (fun x => if x = ({} : Int) then ({} : Int) else m.{} x)",
                        euf_lia_san(&st.arr),
                        st.idx,
                        st.val,
                        euf_lia_san(&st.base),
                    ),
                    cv: true,
                });
                store_at.insert(atoms.len() - 1, st);
                continue;
            }
        }
        // Integer relational atom over `select` reads.
        let lean_op = match op.as_str() {
            "=" => "=",
            ">=" => ">=",
            "<=" => "<=",
            ">" => ">",
            "<" => "<",
            _ => continue,
        };
        if args.len() != 2 {
            continue;
        }
        let mut local_selects = BTreeMap::new();
        let (la, lb) = (
            c4_lin_of(&args[0], &mut local_selects, context),
            c4_lin_of(&args[1], &mut local_selects, context),
        );
        let (Some(la), Some(lb)) = (la, lb) else {
            continue;
        };
        let (Some(sa), Some(sb)) = (
            c4_render_lia(&args[0], context),
            c4_render_lia(&args[1], context),
        ) else {
            continue;
        };
        selects.extend(local_selects);
        atoms.push(EufLiaAtom {
            prop: format!("{sa} {lean_op} {sb}"),
            cv: true,
        });
        let idx = atoms.len() - 1;
        lia_at.insert(idx, firewall_lin_add_checked(&la, &lb, -1)?);
        lia_ops.insert(idx, op.clone());
    }

    if store_at.is_empty() || lia_at.is_empty() || selects.is_empty() {
        return None;
    }
    // Field-name collision guard.
    {
        let mut seen: std::collections::HashMap<String, String> = std::collections::HashMap::new();
        for a in &arrays {
            if let Some(prev) = seen.insert(euf_lia_san(a), a.clone()) {
                if &prev != a {
                    return None;
                }
            }
        }
    }

    // Ground each read `select arr i` to a written value via the FIRST matching
    // store-equality (arr matches, store index == read index → RoW-1 value).
    let mut ground_val: BTreeMap<String, i64> = BTreeMap::new();
    let mut groundings: Vec<Vec<String>> = Vec::new();
    for (key, (arr, idx)) in &selects {
        let mut found = None;
        for (pos, st) in &store_at {
            if &st.arr == arr && st.idx == *idx {
                found = Some((*pos, st.val));
                break;
            }
        }
        let Some((pos, val)) = found else {
            return None; // ungroundable read — decline
        };
        ground_val.insert(key.clone(), val);
        let hyp = pos + 1;
        let asan = euf_lia_san(arr);
        groundings.push(vec![format!(
            "have e_{asan}_{idx} : m.{asan} ({idx} : Int) = ({val} : Int) := by \
have t := congrFun h{hyp} ({idx} : Int); simpa using t"
        )]);
    }

    // Ground infeasibility check: every read is a concrete value, so each integer
    // atom is a concrete comparison; fire only if at least one is FALSE.
    let mut infeasible = false;
    for (idx, diff) in &lia_at {
        // diff = (L - R); the atom is `L op R`, i.e. `diff op 0` in the reads.
        let mut konst = diff.konst;
        let mut all_ground = true;
        for (k, &c) in &diff.coeffs {
            match ground_val.get(k) {
                Some(&v) => konst = konst.checked_add(c.checked_mul(v)?)?,
                None => {
                    all_ground = false;
                    break;
                }
            }
        }
        if !all_ground {
            return None; // a read escaped grounding — decline
        }
        // konst `op` 0 must be FALSE for a conflict.
        let holds = match lia_ops.get(idx)?.as_str() {
            "=" => konst == 0,
            ">=" => konst >= 0,
            "<=" => konst <= 0,
            ">" => konst > 0,
            "<" => konst < 0,
            _ => return None,
        };
        if !holds {
            infeasible = true;
        }
    }
    if !infeasible {
        return None;
    }

    let hash = fnv_hex(
        &atoms
            .iter()
            .map(|a| format!("{}:{}", a.cv, a.prop))
            .collect::<Vec<_>>()
            .join("\u{1}"),
    );
    Some(render_array_sum_bound_lean(
        &atoms,
        &arrays,
        &groundings,
        &hash,
    ))
}

/// Render the fused array-ROW + LIA firewall file. The nested `by_cases` proof
/// tree (each deviating branch closed by `simp`, the all-consistent leaf grounding
/// every read then closing by `omega`) is generated by `euf_lia_emit_block`, the
/// same spine the EUF+LIA congruence emitter uses.
fn render_array_sum_bound_lean(
    atoms: &[EufLiaAtom],
    arrays: &std::collections::BTreeSet<String>,
    groundings: &[Vec<String>],
    hash: &str,
) -> String {
    let n = atoms.len();
    let lemma_id = n + 1;
    let proof_id = n + 2;

    let fields = arrays
        .iter()
        .map(|a| format!("  {} : Int -> Int", euf_lia_san(a)))
        .collect::<Vec<_>>()
        .join("\n");
    let arms = atoms
        .iter()
        .enumerate()
        .map(|(i, a)| format!("  | {} => decide ({})", i + 1, a.prop))
        .collect::<Vec<_>>()
        .join("\n");
    let orig = atoms
        .iter()
        .enumerate()
        .map(|(i, _)| format!("({}, [{}])", i + 1, i + 1))
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_lits = (1..=n)
        .map(|i| format!("-{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let proof_hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let proof_body = euf_lia_emit_block(atoms, 0, "  ", groundings).join("\n");

    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — FUSED array-ROW + LINEAR-INTEGER
  conflict, grounded in the verified `firewall_combined_unsat`. Array-defining
  equalities `arr = store(base, i, v)` PIN the reads `select arr i = v` (McCarthy
  read-over-write RoW-1, the content of `AySoundness.ArrayThy.sel_upd_same`); the
  pinned values then make an integer (in)equality over the reads infeasible, and
  the residual ground conflict is closed by `omega`. Reconstructed from the
  frontend assertions. Arrays are modelled as `Int → Int` functions and `store`
  as an `if`-update; each read is grounded at the leaf by `congrFun` on the
  store-equality hypothesis + `simp`. The array-equality atoms use
  `Classical.propDecidable` (so `atomVal` is `noncomputable`); axioms of
  `no_model` ⊆ {{propext, Classical.choice, Quot.sound}}. Pure Lean 4 core.
-/
namespace AySoundness.Emitted.ArrSumBound_{hash}
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
{fields}

/-- Atoms (one per asserted frontend atom, in assertion order). -/
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof_id}, [], [{proof_hints}])]

/-- The fused conflict clause is valid in EVERY model: any deviation from the
    asserted polarities satisfies the clause; the all-consistent leaf grounds
    every read (RoW-1) and closes the residual integer conflict by `omega`. -/
theorem array_sum_lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
{proof_body}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact array_sum_lemma_valid m

/-- No model satisfies the fused array-ROW + LIA conflict — via the verified
    firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrSumBound_{hash}
"#,
    )
}

// ==== APPENDED BUCKET: b_nia_product.rs ====
// ===========================================================================
// NONLINEAR-INTEGER *product* firewall (bucket "nia_product").
//
// `omega` is a LINEAR decision procedure: it atomises a bilinear term `x * y`
// into an opaque unknown with no residual link to `x` or `y`. The verified
// module `AySoundness.NiaProduct` supplies that link as four LINEAR McCormick
// corner facts, each an `Int.mul_nonneg` instance. This bucket reconstructs the
// conflict from the frontend assertions, proves INFEASIBILITY IN RUST over
// exactly the system `omega` will see after atomisation, and only then emits.
//
// Soundness posture (`--emit-firewall-lean` is verdict-publication-gating: an
// emission turns an exit-1 "no supported obligation" decline into a published
// `unsat`, and that path never kernel-checks the file). Therefore every gate
// below is an UNDER-approximation of what `omega` can prove:
//
//   * the Rust gate reasons over the SAME atom set `omega` sees — the product
//     is ONE slot, exactly as `omega` atomises it, and the emitted Lean text is
//     rendered FROM that normal form, so the two cannot drift apart;
//   * the gate refutes with rational Fourier–Motzkin plus per-row integer
//     tightening. Every derived row is an integer consequence of the asserted
//     rows, so a derived `k ≤ 0` with `k > 0` means the system really is
//     integer-infeasible — and `omega`, being COMPLETE for linear integer
//     arithmetic, then closes the same goal;
//   * atoms the gate cannot linearise (disequalities) are DROPPED from the gate
//     system while still being rendered and hypothesised in Lean. Dropping only
//     weakens the gate, so it can never manufacture a false infeasibility;
//   * every bound fed to a McCormick corner comes from a SINGLE asserted unit
//     row, so the corner's `(by omega)` side goals are discharged from the very
//     hypotheses the cascade has in scope;
//   * any unsupported shape, unresolved symbol, second distinct product,
//     coefficient overflow or elimination blow-up returns `None` (decline).
// ===========================================================================

/// Maximum assertions / rendered atoms / distinct Int variables the recognizer
/// will consider. The cascade is linear in the atom count and Fourier–Motzkin is
/// exponential in the variable count, so both are capped well below the
/// diagnostic source-size ceiling.
const NIA_MAX_ASSERTIONS: usize = 64;
const NIA_MAX_ATOMS: usize = 64;
const NIA_MAX_VARS: usize = 8;
/// Fourier–Motzkin working-set ceiling and coefficient magnitude ceiling.
const NIA_FM_MAX_ROWS: usize = 512;
const NIA_FM_MAX_MAGNITUDE: i128 = 1 << 40;

/// A slot in the linear normal form: either a declared nullary Int variable
/// (rendered `(m i)`) or THE single bilinear product atom of the query
/// (rendered `((m i) * (m j))` with `i ≤ j`).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum NiaSlot {
    Var(usize),
    Product,
}

/// `Σ coeffs[slot]·slot + konst` over `Int`.
#[derive(Clone, Default, PartialEq, Eq)]
struct NiaLin {
    coeffs: std::collections::BTreeMap<NiaSlot, i64>,
    konst: i64,
}

impl NiaLin {
    fn constant(k: i64) -> Self {
        Self {
            coeffs: std::collections::BTreeMap::new(),
            konst: k,
        }
    }

    fn slot(s: NiaSlot) -> Self {
        let mut coeffs = std::collections::BTreeMap::new();
        coeffs.insert(s, 1i64);
        Self { coeffs, konst: 0 }
    }

    fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// `Some((index, coeff))` when this form is exactly `coeff · varᵢ` — the only
    /// shape allowed as a factor of the bilinear product.
    fn single_var(&self) -> Option<(usize, i64)> {
        if self.konst != 0 || self.coeffs.len() != 1 {
            return None;
        }
        match self.coeffs.iter().next()? {
            (NiaSlot::Var(i), c) => Some((*i, *c)),
            (NiaSlot::Product, _) => None,
        }
    }

    /// `self + sign·other`, declining on `i64` overflow.
    fn add(&self, other: &Self, sign: i64) -> Option<Self> {
        let mut coeffs = self.coeffs.clone();
        for (slot, &c) in &other.coeffs {
            let scaled = sign.checked_mul(c)?;
            let next = coeffs
                .get(slot)
                .copied()
                .unwrap_or_default()
                .checked_add(scaled)?;
            if next == 0 {
                coeffs.remove(slot);
            } else {
                coeffs.insert(*slot, next);
            }
        }
        let konst = self.konst.checked_add(sign.checked_mul(other.konst)?)?;
        Some(Self { coeffs, konst })
    }

    fn scale(&self, factor: i64) -> Option<Self> {
        if factor == 0 {
            return Some(Self::constant(0));
        }
        let mut coeffs = std::collections::BTreeMap::new();
        for (slot, &c) in &self.coeffs {
            coeffs.insert(*slot, c.checked_mul(factor)?);
        }
        Some(Self {
            coeffs,
            konst: self.konst.checked_mul(factor)?,
        })
    }
}

/// A rendered assertion atom, kept STRUCTURAL until the canonical product key is
/// known (it is only fixed once every assertion has been walked).
struct NiaAtom {
    lhs: NiaLin,
    rhs: NiaLin,
    /// Lean comparison operator text.
    op: &'static str,
    negated: bool,
}

/// Multiply two normal forms. Linear·constant scales; variable·variable becomes
/// THE product slot (registering / checking the canonical key). Every other
/// combination — in particular a product appearing inside a further product, and
/// a second, DIFFERENT bilinear pair — declines.
fn nia_lin_mul(a: &NiaLin, b: &NiaLin, prod: &mut Option<(usize, usize)>) -> Option<NiaLin> {
    if a.is_constant() {
        return b.scale(a.konst);
    }
    if b.is_constant() {
        return a.scale(b.konst);
    }
    let (i, ci) = a.single_var()?;
    let (j, cj) = b.single_var()?;
    // O1 CANONICALIZATION. `x * y` and `y * x` are the SAME product, but `omega`
    // atomises them as two INDEPENDENT unknowns. Ordering the factor indices
    // here — and rendering the slot from that order everywhere — makes every
    // occurrence syntactically identical in the emitted Lean, so `omega` and the
    // Rust gate agree on how many unknowns there are.
    let key = if i <= j { (i, j) } else { (j, i) };
    match prod {
        Some(existing) if *existing != key => return None,
        Some(_) => {}
        None => *prod = Some(key),
    }
    NiaLin::slot(NiaSlot::Product).scale(ci.checked_mul(cj)?)
}

/// Parse a frontend integer term into the NIA normal form, allocating a stable
/// `(m i)` index per distinct declared Int variable. Declines on any Real /
/// undeclared / non-Int symbol, on `mod`/`div` (outside the Fourier–Motzkin
/// domain), and on any product shape richer than `linear · linear`.
fn nia_lin_of(
    t: &PTerm,
    vars: &mut Vec<String>,
    prod: &mut Option<(usize, usize)>,
    context: &ay_frontend::Context,
) -> Option<NiaLin> {
    match t {
        PTerm::Symbol(v) => {
            if cbr_is_int_constant(context, v) {
                let idx = vars.iter().position(|x| x == v).unwrap_or_else(|| {
                    vars.push(v.clone());
                    vars.len() - 1
                });
                if vars.len() > NIA_MAX_VARS {
                    return None;
                }
                return Some(NiaLin::slot(NiaSlot::Var(idx)));
            }
            // ay's lenient elaboration keeps an undeclared signed literal such as
            // `-1` as a Symbol; a DECLARED numeric-looking name is not a literal.
            Some(NiaLin::constant(firewall_undeclared_i64_symbol_literal(
                context, v,
            )?))
        }
        PTerm::Const(PConst::Numeral(n)) => Some(NiaLin::constant(n.parse::<i64>().ok()?)),
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("+", k) if k >= 1 => {
                let mut acc = NiaLin::constant(0);
                for a in args {
                    acc = acc.add(&nia_lin_of(a, vars, prod, context)?, 1)?;
                }
                Some(acc)
            }
            ("-", 1) => nia_lin_of(&args[0], vars, prod, context)?.scale(-1),
            ("-", k) if k >= 2 => {
                let mut acc = nia_lin_of(&args[0], vars, prod, context)?;
                for a in &args[1..] {
                    acc = acc.add(&nia_lin_of(a, vars, prod, context)?, -1)?;
                }
                Some(acc)
            }
            ("*", k) if k >= 1 => {
                let mut acc = nia_lin_of(&args[0], vars, prod, context)?;
                for a in &args[1..] {
                    let next = nia_lin_of(a, vars, prod, context)?;
                    acc = nia_lin_mul(&acc, &next, prod)?;
                }
                Some(acc)
            }
            _ => None,
        },
        _ => None,
    }
}

/// The integer-tightened rows `Σ c·slot + k ≤ 0` implied by `lhs op rhs` under
/// `negated`. A disequality has no such rows and yields an EMPTY list: the atom
/// is still rendered and hypothesised in Lean, it merely does not strengthen the
/// Rust gate.
fn nia_comparison_rows(lhs: &NiaLin, rhs: &NiaLin, op: &str, negated: bool) -> Option<Vec<NiaLin>> {
    let le = |a: &NiaLin, b: &NiaLin| a.add(b, -1); // a - b ≤ 0
    let lt = |a: &NiaLin, b: &NiaLin| a.add(b, -1)?.add(&NiaLin::constant(1), 1); // a - b + 1 ≤ 0
    Some(match (op, negated) {
        ("<=", false) | (">", true) => vec![le(lhs, rhs)?],
        ("<", false) | (">=", true) => vec![lt(lhs, rhs)?],
        (">=", false) | ("<", true) => vec![le(rhs, lhs)?],
        (">", false) | ("<=", true) => vec![lt(rhs, lhs)?],
        ("=", false) => vec![le(lhs, rhs)?, le(rhs, lhs)?],
        ("=", true) => Vec::new(),
        _ => return None,
    })
}

/// Recognize one frontend assertion as a list of `(atom, gate rows)`. Accepts a
/// comparison, a negated comparison, and `distinct` (expanded to pairwise `≠`).
/// Anything else — `or`/`and`/`ite`, a Bool variable, a non-Int atom — declines.
fn nia_assertion_atoms(
    t: &PTerm,
    vars: &mut Vec<String>,
    prod: &mut Option<(usize, usize)>,
    context: &ay_frontend::Context,
) -> Option<Vec<(NiaAtom, Vec<NiaLin>)>> {
    let comparison = |t: &PTerm,
                      negated: bool,
                      vars: &mut Vec<String>,
                      prod: &mut Option<(usize, usize)>|
     -> Option<(NiaAtom, Vec<NiaLin>)> {
        let PTerm::App(op, args) = t else { return None };
        if args.len() != 2 {
            return None;
        }
        let lean_op = match op.as_str() {
            "<=" => "≤",
            ">=" => "≥",
            "<" => "<",
            ">" => ">",
            "=" => "=",
            _ => return None,
        };
        let lhs = nia_lin_of(&args[0], vars, prod, context)?;
        let rhs = nia_lin_of(&args[1], vars, prod, context)?;
        let rows = nia_comparison_rows(&lhs, &rhs, op, negated)?;
        Some((
            NiaAtom {
                lhs,
                rhs,
                op: lean_op,
                negated,
            },
            rows,
        ))
    };
    match t {
        PTerm::App(op, args) if op == "not" && args.len() == 1 => {
            Some(vec![comparison(&args[0], true, vars, prod)?])
        }
        PTerm::App(op, args) if op == "distinct" && args.len() >= 2 => {
            let rendered: Vec<NiaLin> = args
                .iter()
                .map(|a| nia_lin_of(a, vars, prod, context))
                .collect::<Option<Vec<_>>>()?;
            let mut out = Vec::new();
            for i in 0..rendered.len() {
                for j in (i + 1)..rendered.len() {
                    out.push((
                        NiaAtom {
                            lhs: rendered[i].clone(),
                            rhs: rendered[j].clone(),
                            op: "≠",
                            negated: false,
                        },
                        Vec::new(),
                    ));
                }
            }
            Some(out)
        }
        other => Some(vec![comparison(other, false, vars, prod)?]),
    }
}

/// Render one slot. The product renders with the CANONICAL factor order at every
/// occurrence — the O1 requirement that makes it a single `omega` atom.
fn render_nia_slot(slot: NiaSlot, prod: (usize, usize)) -> String {
    match slot {
        NiaSlot::Var(i) => format!("(m {i})"),
        NiaSlot::Product => format!("((m {}) * (m {}))", prod.0, prod.1),
    }
}

/// Render a normal form as a Lean `Int` expression. Rendering FROM the normal
/// form (rather than from the surface term) is what makes the emitted goal and
/// the Rust gate the same system by construction.
fn render_nia_lin(lin: &NiaLin, prod: (usize, usize)) -> String {
    let mut parts: Vec<String> = Vec::new();
    for (slot, &c) in &lin.coeffs {
        let expr = render_nia_slot(*slot, prod);
        parts.push(match c {
            1 => expr,
            -1 => format!("(- {expr})"),
            _ => format!("(({c} : Int) * {expr})"),
        });
    }
    if parts.is_empty() || lin.konst != 0 {
        parts.push(format!("({} : Int)", lin.konst));
    }
    if parts.len() == 1 {
        parts.swap_remove(0)
    } else {
        format!("({})", parts.join(" + "))
    }
}

fn render_nia_atom(atom: &NiaAtom, prod: (usize, usize)) -> String {
    let body = format!(
        "{} {} {}",
        render_nia_lin(&atom.lhs, prod),
        atom.op,
        render_nia_lin(&atom.rhs, prod)
    );
    if atom.negated {
        format!("¬ ({body})")
    } else {
        body
    }
}

/// Tightest integer bounds on `var` derivable from the SINGLE-variable gate rows
/// — never from a combination, so the matching Lean `(by omega)` side goal is
/// discharged directly from one hypothesis already in the cascade's scope.
fn nia_unit_bounds(rows: &[NiaLin], var: usize) -> (Option<i64>, Option<i64>) {
    let (mut lo, mut hi) = (None::<i64>, None::<i64>);
    for row in rows {
        if row.coeffs.len() != 1 {
            continue;
        }
        let Some((NiaSlot::Var(i), &coeff)) = row.coeffs.iter().next() else {
            continue;
        };
        if *i != var {
            continue;
        }
        // coeff·v + k ≤ 0.
        if coeff > 0 {
            // v ≤ -k/coeff, floored (v is an integer).
            let Some(neg_k) = row.konst.checked_neg() else {
                continue;
            };
            let Some(b) = nia_floor_div(neg_k, coeff) else {
                continue;
            };
            hi = Some(hi.map_or(b, |h| h.min(b)));
        } else if coeff < 0 {
            // v ≥ k/(-coeff), ceiled.
            let Some(den) = coeff.checked_neg() else {
                continue;
            };
            let Some(b) = nia_ceil_div(row.konst, den) else {
                continue;
            };
            lo = Some(lo.map_or(b, |l| l.max(b)));
        }
    }
    (lo, hi)
}

/// Floor of `a / b` for `b > 0`.
fn nia_floor_div(a: i64, b: i64) -> Option<i64> {
    let q = a.checked_div(b)?;
    let r = a.checked_rem(b)?;
    if r < 0 {
        q.checked_sub(1)
    } else {
        Some(q)
    }
}

/// Ceiling of `a / b` for `b > 0`.
fn nia_ceil_div(a: i64, b: i64) -> Option<i64> {
    let q = a.checked_div(b)?;
    let r = a.checked_rem(b)?;
    if r > 0 {
        q.checked_add(1)
    } else {
        Some(q)
    }
}

/// One McCormick corner: the Lean `have` that introduces it and the LINEAR row
/// it contributes to the Rust gate. Both are built from the same `(i, j, p, q)`
/// data, so the gate cannot assume a bound the emitted proof does not derive.
struct NiaCorner {
    have_line: String,
    row: NiaLin,
}

/// Which corner of the McCormick envelope: the `AySoundness.NiaProduct` lemma
/// name, its two bound binder names, and whether it bounds `x · y` from BELOW
/// (`sign = 1`) or from ABOVE (`sign = -1`). In every corner the first bound `p`
/// constrains `x = varᵢ` and the second bound `q` constrains `y = varⱼ`, and the
/// conclusion is `p·y + q·x - p·q ≤ x·y` (below) or `x·y ≤ p·y + q·x - p·q`
/// (above).
struct NiaCornerKind {
    lemma: &'static str,
    x_binder: &'static str,
    y_binder: &'static str,
    sign: i64,
}

/// `a ≤ x`, `c ≤ y` ⟹ `a·y + c·x - a·c ≤ x·y`.
const NIA_CORNER_LB_LL: NiaCornerKind = NiaCornerKind {
    lemma: "mul_lb_ll",
    x_binder: "a",
    y_binder: "c",
    sign: 1,
};
/// `x ≤ b`, `y ≤ d` ⟹ `b·y + d·x - b·d ≤ x·y`.
const NIA_CORNER_LB_UU: NiaCornerKind = NiaCornerKind {
    lemma: "mul_lb_uu",
    x_binder: "b",
    y_binder: "d",
    sign: 1,
};
/// `x ≤ b`, `c ≤ y` ⟹ `x·y ≤ b·y + c·x - b·c`.
const NIA_CORNER_UB_UL: NiaCornerKind = NiaCornerKind {
    lemma: "mul_ub_ul",
    x_binder: "b",
    y_binder: "c",
    sign: -1,
};
/// `a ≤ x`, `y ≤ d` ⟹ `x·y ≤ a·y + d·x - a·d`.
const NIA_CORNER_UB_LU: NiaCornerKind = NiaCornerKind {
    lemma: "mul_ub_lu",
    x_binder: "a",
    y_binder: "d",
    sign: -1,
};

/// Build corner `kind` (named `hb{index}` in the emitted proof) under factor
/// indices `(i, j)` and the two bounds `p` (on `x = varᵢ`) and `q` (on
/// `y = varⱼ`). Squares (`i == j`) need no special case: both coefficient
/// contributions land on the same slot.
fn nia_corner(
    kind: &NiaCornerKind,
    index: usize,
    i: usize,
    j: usize,
    p: i64,
    q: i64,
) -> Option<NiaCorner> {
    let sign = kind.sign;
    let mut row = NiaLin::constant(p.checked_mul(q)?.checked_neg()?.checked_mul(sign)?);
    for (slot, coeff) in [(NiaSlot::Var(j), p), (NiaSlot::Var(i), q)] {
        let scaled = coeff.checked_mul(sign)?;
        let next = row
            .coeffs
            .get(&slot)
            .copied()
            .unwrap_or_default()
            .checked_add(scaled)?;
        if next == 0 {
            row.coeffs.remove(&slot);
        } else {
            row.coeffs.insert(slot, next);
        }
    }
    // `sign = +1` ⟹ subtract the product slot; `sign = -1` ⟹ add it.
    let product = row
        .coeffs
        .get(&NiaSlot::Product)
        .copied()
        .unwrap_or_default()
        .checked_sub(sign)?;
    if product == 0 {
        row.coeffs.remove(&NiaSlot::Product);
    } else {
        row.coeffs.insert(NiaSlot::Product, product);
    }
    Some(NiaCorner {
        have_line: format!(
            "have hb{index} := AySoundness.NiaProduct.{lemma} (x := (m {i})) (y := (m {j})) \
             ({x_binder} := ({p} : Int)) ({y_binder} := ({q} : Int)) (by omega) (by omega)",
            lemma = kind.lemma,
            x_binder = kind.x_binder,
            y_binder = kind.y_binder,
        ),
        row,
    })
}

/// A Fourier–Motzkin working row `Σ c·slot + k ≤ 0` over `i128`.
#[derive(Clone)]
struct NiaFmRow {
    coeffs: std::collections::BTreeMap<NiaSlot, i128>,
    konst: i128,
}

fn nia_gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Ceiling of `a / b` for `b > 0`, over `i128`.
fn nia_i128_ceil_div(a: i128, b: i128) -> i128 {
    let q = a / b;
    if a % b > 0 {
        q + 1
    } else {
        q
    }
}

/// Drop zero coefficients, divide through by the coefficient gcd and TIGHTEN the
/// constant: `Σ c·s ≤ -k` with `g | c` for all `c` means the (integral) left side
/// is a multiple of `g`, so `Σ (c/g)·s ≤ ⌊-k/g⌋`. Every row produced this way is
/// an INTEGER consequence of its input, which is exactly what lets a derived
/// contradiction transfer to `omega`. `None` on a magnitude blow-up.
fn nia_fm_normalise(mut row: NiaFmRow) -> Option<NiaFmRow> {
    row.coeffs.retain(|_, c| *c != 0);
    let mut g: i128 = 0;
    for c in row.coeffs.values() {
        g = nia_gcd(g, *c);
    }
    if g > 1 {
        for c in row.coeffs.values_mut() {
            *c /= g;
        }
        row.konst = nia_i128_ceil_div(row.konst, g);
    }
    if row.konst.abs() > NIA_FM_MAX_MAGNITUDE
        || row.coeffs.values().any(|c| c.abs() > NIA_FM_MAX_MAGNITUDE)
    {
        return None;
    }
    Some(row)
}

/// Eliminate `slot` from `pos` (coefficient > 0) and `neg` (coefficient < 0) by
/// the positive combination `(-cn)·pos + cp·neg`.
fn nia_fm_combine(pos: &NiaFmRow, neg: &NiaFmRow, slot: NiaSlot) -> Option<NiaFmRow> {
    let cp = *pos.coeffs.get(&slot)?;
    let cn = *neg.coeffs.get(&slot)?;
    let (m_pos, m_neg) = (cn.checked_neg()?, cp);
    let mut coeffs: std::collections::BTreeMap<NiaSlot, i128> = std::collections::BTreeMap::new();
    for (s, &c) in &pos.coeffs {
        coeffs.insert(*s, c.checked_mul(m_pos)?);
    }
    for (s, &c) in &neg.coeffs {
        let add = c.checked_mul(m_neg)?;
        let next = coeffs
            .get(s)
            .copied()
            .unwrap_or_default()
            .checked_add(add)?;
        coeffs.insert(*s, next);
    }
    coeffs.remove(&slot);
    let konst = pos
        .konst
        .checked_mul(m_pos)?
        .checked_add(neg.konst.checked_mul(m_neg)?)?;
    nia_fm_normalise(NiaFmRow { coeffs, konst })
}

/// Decide whether `rows` (each `Σ c·slot + k ≤ 0`) is INFEASIBLE over the
/// integers, by Fourier–Motzkin elimination with per-row integer tightening.
///
/// This is deliberately an UNDER-approximation: `true` is a proof of
/// infeasibility (every derived row is an integer consequence of the input), and
/// `false` merely means "not established here" — including every resource-limit
/// and overflow bail-out. `omega` is complete for linear integer arithmetic, so
/// `true` guarantees `omega` closes the corresponding Lean goal.
fn nia_rows_infeasible(rows: &[NiaLin]) -> bool {
    let Some(mut work) = rows
        .iter()
        .map(|r| {
            nia_fm_normalise(NiaFmRow {
                coeffs: r.coeffs.iter().map(|(s, &c)| (*s, i128::from(c))).collect(),
                konst: i128::from(r.konst),
            })
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    // At most one elimination round per slot (NIA_MAX_VARS variables + product).
    for _ in 0..=NIA_MAX_VARS {
        if work.len() > NIA_FM_MAX_ROWS {
            return false;
        }
        if work.iter().any(|r| r.coeffs.is_empty() && r.konst > 0) {
            return true;
        }
        work.retain(|r| !r.coeffs.is_empty());
        // Eliminate the slot with the smallest pos×neg product.
        let mut slots: Vec<NiaSlot> = work.iter().flat_map(|r| r.coeffs.keys().copied()).collect();
        slots.sort_unstable();
        slots.dedup();
        let Some(slot) = slots.into_iter().min_by_key(|s| {
            let pos = work
                .iter()
                .filter(|r| r.coeffs.get(s).is_some_and(|c| *c > 0))
                .count();
            let neg = work
                .iter()
                .filter(|r| r.coeffs.get(s).is_some_and(|c| *c < 0))
                .count();
            pos * neg
        }) else {
            return false; // no slots left and no contradiction found
        };
        let pos: Vec<&NiaFmRow> = work
            .iter()
            .filter(|r| r.coeffs.get(&slot).is_some_and(|c| *c > 0))
            .collect();
        let neg: Vec<&NiaFmRow> = work
            .iter()
            .filter(|r| r.coeffs.get(&slot).is_some_and(|c| *c < 0))
            .collect();
        if pos.len().saturating_mul(neg.len()) > NIA_FM_MAX_ROWS {
            return false;
        }
        let mut next: Vec<NiaFmRow> = Vec::new();
        for p in &pos {
            for n in &neg {
                let Some(row) = nia_fm_combine(p, n, slot) else {
                    return false;
                };
                next.push(row);
            }
        }
        next.extend(
            work.iter()
                .filter(|r| !r.coeffs.contains_key(&slot))
                .cloned(),
        );
        work = next;
    }
    false
}

/// Emit a verified-firewall Lean proof for a NONLINEAR-INTEGER conflict carried
/// by ONE bilinear product term, reconstructed from the PARSED frontend
/// assertions.
///
/// ay refutes QF_NIA eagerly (bounded enumeration / bare `:rule trust`), so there
/// is no theory-lemma clause to ground per step; and the LIA emitter DECLINES the
/// moment it meets a `var·var` product, because `omega` atomises the product and
/// then cannot close the goal. This bucket supplies the missing link: the
/// verified `AySoundness.NiaProduct` McCormick corners relate the atomised
/// product to its two factors LINEARLY, and the cascade's bottom `omega` finishes.
///
/// Recognizer (fail-closed at every step):
///  * `defs` gates OFF array-valued (`store`-bodied) `define-fun` macros exactly
///    as the LIA emitter does — an array disequality is NOT an Int atom, and
///    modelling one as two fresh integers would be an unsound abstraction;
///  * every surface variable must resolve in `context` as a nullary **Int**
///    declaration (`cbr_is_int_constant`), so Real/Bool/array/UF atoms decline;
///  * every assertion must be a comparison, a negated comparison, or `distinct`;
///  * EXACTLY ONE canonical bilinear product `varᵢ · varⱼ` (`i ≤ j`, squares
///    allowed) may occur; a second distinct pair, a degree-3 term, or a product
///    of compound terms declines;
///  * the reconstructed system — the atom rows PLUS the injected corner rows —
///    must be proved integer-infeasible by `nia_rows_infeasible` BEFORE anything
///    is emitted. Without a product there is nothing for this bucket to add over
///    the LIA emitter, so it declines then too.
pub(crate) fn emit_nia_product_firewall_lean_from_parsed(
    parsed: &[PTerm],
    defs: &[(String, PTerm)],
    context: &ay_frontend::Context,
) -> Option<String> {
    // O2: an assertion mentioning an ARRAY-valued macro is not an integer atom.
    let array_defs = array_valued_def_names(defs);
    if !array_defs.is_empty() && parsed.iter().any(|a| term_mentions_name(a, &array_defs)) {
        return None;
    }
    if parsed.is_empty() || parsed.len() > NIA_MAX_ASSERTIONS {
        return None;
    }
    let mut vars: Vec<String> = Vec::new();
    let mut prod: Option<(usize, usize)> = None;
    let mut atoms: Vec<NiaAtom> = Vec::new();
    let mut rows: Vec<NiaLin> = Vec::new();
    for asrt in parsed {
        for (atom, atom_rows) in nia_assertion_atoms(asrt, &mut vars, &mut prod, context)? {
            atoms.push(atom);
            rows.extend(atom_rows);
        }
        if atoms.len() > NIA_MAX_ATOMS {
            return None;
        }
    }
    // No bilinear product ⟹ nothing this bucket can add; the LIA emitter owns it.
    let (pi, pj) = prod?;
    if atoms.is_empty() {
        return None;
    }
    // McCormick corners for whichever of the four bound pairs the assertions
    // actually establish. `sign_consistency` has LOWER bounds only.
    let (lo_i, hi_i) = nia_unit_bounds(&rows, pi);
    let (lo_j, hi_j) = nia_unit_bounds(&rows, pj);
    let mut corners: Vec<NiaCorner> = Vec::new();
    for (kind, p, q) in [
        (&NIA_CORNER_LB_LL, lo_i, lo_j),
        (&NIA_CORNER_LB_UU, hi_i, hi_j),
        (&NIA_CORNER_UB_UL, hi_i, lo_j),
        (&NIA_CORNER_UB_LU, lo_i, hi_j),
    ] {
        if let (Some(p), Some(q)) = (p, q) {
            corners.push(nia_corner(kind, corners.len(), pi, pj, p, q)?);
        }
    }

    // O5: gate on EXACTLY the system `omega` will see — same slots (one product
    // atom), same polarities, same corner rows as the emitted `have`s.
    let mut gate = rows.clone();
    gate.extend(corners.iter().map(|c| c.row.clone()));
    if !nia_rows_infeasible(&gate) {
        return None;
    }

    let rendered: Vec<String> = atoms.iter().map(|a| render_nia_atom(a, (pi, pj))).collect();
    let mut closer = String::new();
    for corner in &corners {
        closer.push_str(&corner.have_line);
        closer.push_str("; ");
    }
    closer.push_str("omega");
    Some(render_nia_product_lean(&rendered, &closer))
}

/// Render the `firewall_combined_unsat`-grounded Lean for a bilinear-product
/// conflict over the rendered atoms `S₁ … Sₙ`. Identical in shape to
/// `render_lia_lean_from_parsed`, except that the cascade's bottom introduces the
/// verified McCormick corner facts before calling `omega`.
fn render_nia_product_lean(atoms: &[String], closer: &str) -> String {
    let n = atoms.len();
    let hash = fnv_hex(&format!("{}\u{1}{closer}", atoms.join("\u{1}")));
    let arms = atoms
        .iter()
        .enumerate()
        .map(|(i, a)| format!("  | {} => decide ({a})", i + 1))
        .collect::<Vec<_>>()
        .join("\n");
    let orig = (1..=n)
        .map(|i| format!("({i}, [{i}])"))
        .collect::<Vec<_>>()
        .join(", ");
    let neg = (1..=n)
        .map(|i| format!("-{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = n + 1;
    let proof_id = n + 2;
    let hints = (1..=lemma_id)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let cascade = cascade_term_with_closer(atoms, closer);
    format!(
        r#"import AySoundness.Firewall
import AySoundness.NiaProduct
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — NONLINEAR-INTEGER conflict carried by a
  single BILINEAR PRODUCT, reconstructed from the parsed frontend assertions and
  grounded in the verified `firewall_combined_unsat`.

  `omega` decides LINEAR integer arithmetic: it atomises `x * y` into an opaque
  unknown, so the conflict is not linear-closable on its own. The verified
  McCormick corner lemmas of `AySoundness.NiaProduct` (each an `Int.mul_nonneg`
  instance — Lean CORE, no Mathlib) reintroduce the product as LINEAR bounds in
  the two factors, and the cascade's bottom `omega` then closes `False`.

  Every assertion is asserted POSITIVELY and the single all-negated blocking
  clause `¬S₁ ∨ … ∨ ¬Sₙ` is discharged by a constructive linear case cascade.
  Every occurrence of the product uses ONE canonical factor order, so `omega`
  sees exactly ONE product atom. Model: a valuation `Nat → Int`.
  axioms ⊆ {{propext, Quot.sound}}.
-/
set_option linter.unusedSimpArgs false

namespace AySoundness.Emitted.NiaProd_{hash}
open AySoundness

abbrev Val := Nat → Int

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
{arms}
  | _ => false

def original : List (Cid × Clause) := [{orig}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{neg}])]
def proof    : List (Cid × Clause × List Int) := [({proof_id}, [], [{hints}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{neg}] = true := by
  simp only [clauseSat, litSat, atomVal, List.any_cons, List.any_nil,
    Int.reduceGT, Int.reduceNeg, Int.reduceToNat, reduceIte, Bool.or_false,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  exact
    {cascade}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No integer valuation satisfies all the asserted (non)linear constraints —
    through the verified firewall and the verified McCormick product bridge. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.NiaProd_{hash}
"#
    )
}

include!("lean_firewall/regex_len_model.rs");

include!("lean_firewall/regex_len_recognizer.rs");

/// Render the `str.in_re` length-invariant firewall Lean artifact.
fn render_str_in_re_len_lean(sym: &str, re: &ReAst, pin: LenPin, tier: RegexLenTier) -> String {
    let mut re_lean = String::new();
    re.render(&mut re_lean);
    let hash = fnv_hex(&format!("strinrelen:{sym}:{re_lean}:{pin:?}:{tier:?}"));
    // One `Re` constructor per code point, so elaboration depth tracks the
    // rendered term's size. Reuses the shared scaler (clamped, never disabled).
    let rec_depth = scaled_max_rec_depth(re_lean.len());
    let (pin_prop, pin_smt) = len_pin_lean(pin);
    let conflict = regex_len_conflict_term(tier);
    let note = regex_len_tier_note(tier);
    let sym_note = lean_comment_safe(sym);
    let approx = if re_lean.contains("anyChar") {
        "\n  ONE-SIDED RENDERING: `re.range` / `re.allchar` are rendered as `anyChar`, an\n  \
         OVER-approximation of the asserted language. The source assertion IMPLIES the\n  \
         rendered atom, so refuting the rendered set refutes the source set; the atom is\n  \
         not a byte-mirror of the source text."
    } else {
        ""
    };
    format!(
        r#"import AySoundness.Firewall
import AySoundness.StringThy
import AySoundness.RegexThy
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — SYMBOLIC `str.in_re` LENGTH-INVARIANT
  conflict, grounded in the verified `firewall_combined_unsat` and the verified
  regex length invariants of `AySoundness.RegexThy`.

  Reconstructed from the frontend parsed ASSERTIONS for the String symbol
  `{sym_note}`:

    (assert (str.in_re X R))
    (assert {pin_smt})

  {note}

  Model: `Val = StringThy.Str` — a string is the free monoid `List Nat` of code
  points, `str.len` is `List.length`. The certificate quantifies over ALL
  strings, so it holds for whatever `{sym_note}` denotes.{approx}

  The artifact certifies exactly this two-assertion subset of the query. A
  subset with no model makes the whole query unsatisfiable; it does not by
  itself replay ay's refutation. Pure Lean 4 core; axioms ⊆ {{propext,
  Classical.choice, Quot.sound}} (`Classical.choice` enters only through the
  opaque `Decidable (Mem r s)` instance the `Bool`-valued atom needs).
-/
-- Lean's default `maxRecDepth` (512) is sized for hand-written proofs. The
-- rendered `Re` is one constructor per code point, so `decide`/`simp` recurse
-- once per character and a literal past ~120 code points overflowed the stack:
-- the artifact then failed to compile and reported `sorryAx`, which is worse
-- than declining. Scaled with the rendered term, never disabled — proof size is
-- attacker-amplifiable, so the guard moves with the input rather than off.
set_option maxRecDepth {rec_depth}
namespace AySoundness.Emitted.StrInReLen_{hash}
open AySoundness

abbrev Val := StringThy.Str

/-- The asserted regular expression, rendered constructor-for-constructor. -/
def re1 : RegexThy.Re :=
  {re_lean}

/-- Atom `1 ↦ X ∈ L(re1)`; atom `2 ↦ the asserted length pin`. -/
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (RegexThy.Mem re1 m)
  | 2 => decide ({pin_prop})
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, -2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1, -2] = true := by
  by_cases hm : RegexThy.Mem re1 m
  · have hpin : ¬ ({pin_prop}) := fun h =>
      {conflict}
    have ha : atomVal m 2 = false := by
      simp only [atomVal, decide_eq_false_iff_not]
      exact hpin
    simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]
  · have ha : atomVal m 1 = false := by
      simp only [atomVal, decide_eq_false_iff_not]
      exact hm
    simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- No string is both a member of the asserted regex and of the pinned length —
    via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.StrInReLen_{hash}
"#,
    )
}

#[cfg(test)]
#[path = "lean_firewall_tests.rs"]
mod tests;
