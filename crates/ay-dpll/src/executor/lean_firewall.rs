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
//! Faithful abstraction: the datatype's constructors are emitted as a Lean
//! `inductive` of NULLARY constructors. Distinctness depends only on the
//! constructors being pairwise distinct — which the kernel guarantees for any
//! `inductive` — so dropping constructor arguments does not weaken the
//! certificate (it is exactly the fact `C1 ≠ C2`).

use ay_core::{Sort, Symbol, TermData, TermId, TermStore};
use ay_frontend::command::{Constant as PConst, Term as PTerm};

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

/-- No string is both `= {lit}` and of length {k} — via the firewall. -/
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
  conflict over `{dt}`, grounded in the verified `firewall_combined_unsat`.
  `c = {c1}` ∧ `c = {c2}` is unsatisfiable because `{c1}` and `{c2}` are distinct
  constructors. Premise (a): resolution closes (`lratCheck` by `decide`).
  Premise (b): the `dt_distinct` lemma `¬(c={c1}) ∨ ¬(c={c2})` holds in every
  model. Constructors are emitted nullary — a faithful abstraction for
  distinctness (the fact used is `{c1} ≠ {c2}`). Pure Lean 4 core.
-/
namespace AySoundness.Emitted.{ns}
open AySoundness

/-- The datatype `{dt}` (constructors emitted nullary; see module note). -/
inductive T where
{ind}
deriving DecidableEq

/-- Atom interpretation under a model (the value of `c`):
    `1 ↦ c = {c1}`, `2 ↦ c = {c2}`. -/
def atomVal (c : T) (n : Nat) : Bool :=
  match n with
  | 1 => decide (c = T.{s1})
  | 2 => decide (c = T.{s2})
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, -2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- The `dt_distinct` lemma `¬(c={c1}) ∨ ¬(c={c2})` is valid in every model:
    no `c` is both `{c1}` and `{c2}` (distinct constructors). -/
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

/-- No model assigns `c` both `{c1}` and `{c2}` — through the verified firewall. -/
theorem no_model : ∀ c : T, ¬ Sat (atomVal c) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.{ns}
"#,
    )
}

/// Make an SMT identifier safe as a Lean identifier component: keep it as-is if
/// it is a plain alphanumeric/underscore identifier, else map to a stable hash.
fn sanitize(name: &str) -> String {
    if !name.is_empty()
        && name
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        name.to_string()
    } else {
        // Deterministic, identifier-safe fallback.
        let mut s = String::from("c_");
        for b in name.bytes() {
            s.push_str(&format!("{b:02x}"));
        }
        s
    }
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

#[cfg(test)]
#[path = "lean_firewall_tests.rs"]
mod tests;
