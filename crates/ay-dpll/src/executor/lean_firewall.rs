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
                if occurs_ctor_depth(node_app, x, is_ctor)
                    .filter(|d| *d >= 1)
                    .is_none()
                {
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
    let mut vars: Vec<String> = Vec::new();
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
    Some(render_lia_lean(&atoms))
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
    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — linear-arithmetic conflict grounded in
  the verified `firewall_combined_unsat`. The asserted comparisons are jointly
  unsatisfiable; premise (a) is the resolution (`lratCheck` by `decide`),
  premise (b) is the `la_generic` lemma holding in every valuation, discharged by
  `omega`. Model: a valuation `Nat → Int`. Pure Lean 4 core.
-/
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
  {bycases} <;> simp [{hs}] <;> omega

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
        bycases = bycases,
        hs = hs,
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
        lemma_thms.push_str(&format!(
            "theorem lemma_{cid}_valid (m : Val) : clauseSat (atomVal m) [{lits_src}] = true := by\n  \
             simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]\n  \
             {bycases} {close}\n\n"
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
/// `vars` (a stable valuation index per distinct variable name).
fn render_comparison(terms: &TermStore, term: TermId, vars: &mut Vec<String>) -> Option<String> {
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
fn render_int(terms: &TermStore, term: TermId, vars: &mut Vec<String>) -> Option<String> {
    match terms.get(term) {
        TermData::Const(ay_core::Constant::Int(v)) => Some(format!("({v} : Int)")),
        TermData::Var(name, _) => {
            let idx = vars.iter().position(|v| v == name).unwrap_or_else(|| {
                vars.push(name.clone());
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

// ==== APPENDED BUCKET: b_lia.rs ====
/// Render a parsed LINEAR integer term to a Lean `Int` expression over the model
/// `Val := Nat → Int`, assigning each distinct variable a stable index `(m i)`.
/// Handles `+` (n-ary), binary/unary `-`, `*` with at least one constant operand
/// (linearity — a `var*var` product returns `None`), and Euclidean `mod`/`div` by
/// a constant divisor (rendered `Int.emod`/`Int.ediv`, which `omega` supports).
/// Returns `(expr, references_var)`; `None` on any non-linear or unsupported shape.
fn render_int_lia_parsed(t: &PTerm, vars: &mut Vec<String>) -> Option<(String, bool)> {
    match t {
        PTerm::Symbol(v) => {
            // SMT-LIB numerals are non-negative, so a negative literal such as
            // `-1` in `(* -1 v0)` reaches the parser as a SYMBOL. Treat any
            // symbol whose text is an integer as a constant (matches ay's own
            // lenient elaboration), never a free variable.
            if let Ok(val) = v.parse::<i64>() {
                return Some((format!("({val} : Int)"), false));
            }
            let idx = vars.iter().position(|x| x == v).unwrap_or_else(|| {
                vars.push(v.clone());
                vars.len() - 1
            });
            Some((format!("(m {idx})"), true))
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
                    let (e, r) = render_int_lia_parsed(a, vars)?;
                    parts.push(e);
                    refs |= r;
                }
                Some((format!("({})", parts.join(" + ")), refs))
            }
            ("-", 2) => {
                let (a, ar) = render_int_lia_parsed(&args[0], vars)?;
                let (b, br) = render_int_lia_parsed(&args[1], vars)?;
                Some((format!("({a} - {b})"), ar || br))
            }
            ("-", 1) => {
                let (a, ar) = render_int_lia_parsed(&args[0], vars)?;
                Some((format!("(- {a})"), ar))
            }
            ("*", 2) => {
                let (a, ar) = render_int_lia_parsed(&args[0], vars)?;
                let (b, br) = render_int_lia_parsed(&args[1], vars)?;
                if ar && br {
                    return None; // nonlinear var*var — omega cannot discharge
                }
                Some((format!("({a} * {b})"), ar || br))
            }
            ("mod", 2) => {
                let (a, ar) = render_int_lia_parsed(&args[0], vars)?;
                let (b, br) = render_int_lia_parsed(&args[1], vars)?;
                if br {
                    return None; // non-constant modulus — omega supports literals only
                }
                Some((format!("(Int.emod {a} {b})"), ar))
            }
            ("div", 2) => {
                let (a, ar) = render_int_lia_parsed(&args[0], vars)?;
                let (b, br) = render_int_lia_parsed(&args[1], vars)?;
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
fn lia_comparison_atom(t: &PTerm, vars: &mut Vec<String>) -> Option<String> {
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
    let (l, _) = render_int_lia_parsed(&args[0], vars)?;
    let (r, _) = render_int_lia_parsed(&args[1], vars)?;
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
/// `≠`). Any `var*var` product, non-arithmetic atom, or `or`/`ite`/`and`
/// propositional structure returns `None`.
///
/// Render: each atom is asserted POSITIVELY (`original`); the single all-negated
/// blocking clause is the `lemmas`; the RUP `proof` resolves to empty. The
/// blocking clause `¬S₁ ∨ … ∨ ¬Sₙ` is discharged by a CONSTRUCTIVE linear case
/// cascade closed by `omega` (a Lean-CORE tactic) — not the exponential
/// `by_cases <;> … <;> omega` of `render_lia_lean`, which explodes on the
/// ~30-atom ring files. Runtime counterpart of the worked instance
/// `FirewallExample.no_x_gt5_lt3`; axioms ⊆ {propext, Quot.sound}.
pub(crate) fn emit_lia_firewall_lean_from_parsed(parsed: &[PTerm]) -> Option<String> {
    let mut vars: Vec<String> = Vec::new();
    let mut atoms: Vec<String> = Vec::new();
    for asrt in parsed {
        match asrt {
            // (not <comparison>) → the negated comparison as a single atom.
            PTerm::App(op, args) if op == "not" && args.len() == 1 => {
                let inner = lia_comparison_atom(&args[0], &mut vars)?;
                atoms.push(format!("¬ ({inner})"));
            }
            // (distinct t1 t2 …) → pairwise `ti ≠ tj`, each a positive atom.
            PTerm::App(op, args) if op == "distinct" && args.len() >= 2 => {
                let rendered: Vec<String> = args
                    .iter()
                    .map(|a| render_int_lia_parsed(a, &mut vars).map(|(e, _)| e))
                    .collect::<Option<Vec<_>>>()?;
                for i in 0..rendered.len() {
                    for j in (i + 1)..rendered.len() {
                        atoms.push(format!("{} ≠ {}", rendered[i], rendered[j]));
                    }
                }
            }
            // Any other assertion must be a bare linear comparison.
            other => {
                atoms.push(lia_comparison_atom(other, &mut vars)?);
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
    fn build(k: usize, n: usize, atoms: &[String]) -> String {
        if k == n {
            format!(
                "if h{k} : {a} then (show False by omega).elim else {d}",
                a = atoms[k - 1],
                d = disjunct(k, n)
            )
        } else {
            format!(
                "if h{k} : {a} then\n  {rest}\nelse {d}",
                a = atoms[k - 1],
                rest = build(k + 1, n, atoms),
                d = disjunct(k, n)
            )
        }
    }
    build(1, n, atoms)
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

/// `a + sign*b` (coefficient-wise), preserving determinism (sorted keys).
fn euf_lia_lin_add(a: &EufLiaLin, b: &EufLiaLin, sign: i64) -> EufLiaLin {
    let mut coeffs = a.coeffs.clone();
    for (v, &c) in &b.coeffs {
        let e = coeffs.entry(v.clone()).or_insert(0);
        *e += sign * c;
    }
    coeffs.retain(|_, &mut c| c != 0);
    EufLiaLin {
        coeffs,
        konst: a.konst + sign * b.konst,
    }
}

/// `s*a` (coefficient-wise).
fn euf_lia_lin_scale(a: &EufLiaLin, s: i64) -> EufLiaLin {
    let mut coeffs = a.coeffs.clone();
    for c in coeffs.values_mut() {
        *c *= s;
    }
    coeffs.retain(|_, &mut c| c != 0);
    EufLiaLin {
        coeffs,
        konst: a.konst * s,
    }
}

/// Parse a frontend term into a linear-integer normal form, or `None` on any
/// non-linear / non-Int shape (a Real `Decimal` numeral, a nonlinear product, or
/// an uninterpreted application — the latter forces UF-value classification /
/// decline). This is the linearity + Int gate: `omega` (Lean core) discharges
/// only Int, so declining here keeps QF_UFLRA / nonlinear fail-closed.
fn euf_lia_lin_of(t: &PTerm) -> Option<EufLiaLin> {
    use std::collections::BTreeMap;
    match t {
        PTerm::Symbol(v) => {
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
                    acc = euf_lia_lin_add(&acc, &euf_lia_lin_of(a)?, 1);
                }
                Some(acc)
            }
            ("-", 1) => Some(euf_lia_lin_scale(&euf_lia_lin_of(&args[0])?, -1)),
            ("-", n) if n >= 2 => {
                let mut acc = euf_lia_lin_of(&args[0])?;
                for a in &args[1..] {
                    acc = euf_lia_lin_add(&acc, &euf_lia_lin_of(a)?, -1);
                }
                Some(acc)
            }
            ("*", _) if !args.is_empty() => {
                let mut acc = EufLiaLin {
                    coeffs: BTreeMap::new(),
                    konst: 1,
                };
                for a in args {
                    let l = euf_lia_lin_of(a)?;
                    if acc.coeffs.is_empty() {
                        acc = euf_lia_lin_scale(&l, acc.konst);
                    } else if l.coeffs.is_empty() {
                        acc = euf_lia_lin_scale(&acc, l.konst);
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
fn euf_lia_render_int(t: &PTerm) -> Option<String> {
    match t {
        PTerm::Symbol(v) => Some(format!("m.x_{}", euf_lia_san(v))),
        PTerm::Const(PConst::Numeral(n)) => {
            n.parse::<i64>().ok()?;
            Some(format!("({n} : Int)"))
        }
        PTerm::App(op, args) => match (op.as_str(), args.len()) {
            ("+", _) if !args.is_empty() => {
                let parts: Option<Vec<String>> = args.iter().map(euf_lia_render_int).collect();
                Some(format!("({})", parts?.join(" + ")))
            }
            ("-", 1) => Some(format!("(- {})", euf_lia_render_int(&args[0])?)),
            ("-", n) if n >= 2 => {
                let parts: Option<Vec<String>> = args.iter().map(euf_lia_render_int).collect();
                Some(format!("({})", parts?.join(" - ")))
            }
            ("*", _) if !args.is_empty() => {
                let parts: Option<Vec<String>> = args.iter().map(euf_lia_render_int).collect();
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
fn euf_lia_match_uf_value(head: &PTerm, tail: &PTerm) -> Option<(String, String, i64)> {
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
    let PTerm::Const(PConst::Numeral(n)) = tail else {
        return None;
    };
    let val = n.parse::<i64>().ok()?;
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
/// conflict all return `None`. axioms ⊆ {propext, Quot.sound}; NO Mathlib, no new
/// AySoundness lemma, no `sorry`.
pub(crate) fn emit_euf_lia_congruence_firewall_lean_from_parsed(
    parsed: &[PTerm],
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
            if let Some((g, arg, val)) = euf_lia_match_uf_value(&args[0], &args[1])
                .or_else(|| euf_lia_match_uf_value(&args[1], &args[0]))
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
        let (la, lb) = (euf_lia_lin_of(&args[0]), euf_lia_lin_of(&args[1]));
        let (Some(la), Some(lb)) = (la, lb) else {
            return None;
        };
        let sa = euf_lia_render_int(&args[0])?;
        let sb = euf_lia_render_int(&args[1])?;
        for v in la.coeffs.keys().chain(lb.coeffs.keys()) {
            int_vars.insert(v.clone());
        }
        atoms.push(EufLiaAtom {
            prop: format!("{sa} {lean_op} {sb}"),
            cv: positive,
        });
        if positive {
            let diff = euf_lia_lin_add(&la, &lb, -1);
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
        let (lo, hi): (Option<i64>, Option<i64>) = match (op.as_str(), c) {
            (">=", 1) => (Some(-d), None),
            (">=", -1) => (None, Some(d)),
            (">", 1) => (Some(-d + 1), None),
            (">", -1) => (None, Some(d - 1)),
            ("<=", 1) => (None, Some(-d)),
            ("<=", -1) => (Some(d), None),
            ("<", 1) => (None, Some(-d - 1)),
            ("<", -1) => (Some(d + 1), None),
            _ => (None, None),
        };
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
                konst += c * pins[&v];
            }
            coeffs.retain(|_, &mut c| c != 0);
            match coeffs.len() {
                1 => {
                    let (v, &c) = coeffs.iter().next().unwrap();
                    if c != 0 && konst % c == 0 {
                        let val = -konst / c;
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
                    if c1 == -c2 && c1 != 0 && konst == 0 {
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

    Some(render_euf_lia_congruence_lean(
        &atoms,
        &int_vars,
        &uf_funcs,
        &bridges.into_iter().collect::<Vec<_>>(),
    ))
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

#[cfg(test)]
#[path = "lean_firewall_tests.rs"]
mod tests;
