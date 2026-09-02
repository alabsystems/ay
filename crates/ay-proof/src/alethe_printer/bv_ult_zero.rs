// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked Alethe lowering for the bit-vector unsigned-less-than-one zero test.

use super::AlethePrinter;
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId};
use std::fmt::Write as _;

/// The wire spelling of an idempotent gate collapse on the zero-test side.
///
/// Both rule names are taken verbatim from `decode_idempotent_bv_gate`, the
/// single production table that maps a bit-wise operator onto the Carcara
/// rules that discharge it. Carrying COMPLETE rule names — rather than
/// re-deriving `bitblast_{conn}` / `{conn}_simplify` by concatenation at the
/// print site — is what keeps this producer inside the wire-rule inventory:
/// the coverage gate probes rule names it can read, and a name spliced out of
/// a fragment is not one.
#[derive(Clone, Copy)]
struct ZeroTestGate {
    operator: &'static str,
    connective: &'static str,
    blast_rule: &'static str,
    simplify_rule: &'static str,
}

#[derive(Clone, Copy)]
struct ZeroTestPair {
    one: TermId,
    v: TermId,
    z: TermId,
    zero: TermId,
    width: u32,
    gate: Option<ZeroTestGate>,
}

#[derive(Clone, Copy)]
struct ZeroTestShape {
    equality: TermId,
    ult: TermId,
    eqz: TermId,
    pair: ZeroTestPair,
    reversed: bool,
}

struct ZeroTestText {
    ult: String,
    eqz: String,
    oriented_equality: String,
    v: String,
    z: String,
    one: String,
    zero: String,
    pure_eq: String,
    eqz_reversed: bool,
}

impl AlethePrinter<'_> {
    /// Lower the ZERO-TEST duality `(bvult v 1) = (= z 0)` — where `z` is `v`
    /// itself or its idempotent gate collapse `(bvand v v)` / `(bvor v v)` —
    /// to Carcara's pseudo-Boolean blasting plus checked linear arithmetic,
    /// composed with the existing bit-blast idempotency derivation for the
    /// gate side.
    ///
    /// This is the DivZero/NullIfZero guard-carrier shape (x86 condition code
    /// `E` = "is zero") after a verified code generator re-phrased its guards
    /// uniformly over `bvult`: the intended trap set is `(bvult lhs 1)` while
    /// the emitted test is `(= (bvand lhs lhs) 0)`. It mirrors `ay_dpll`'s
    /// `is_ult_one_eq_zero_of` and must stay in lock-step with it.
    ///
    /// The derivation rewrites both words and constants to `@pbbterm`, blasts
    /// the comparisons, derives bit non-negativity with weighted `cp_literal`
    /// steps, and closes both arithmetic directions with `la_generic`.
    /// `equiv_neg*`, resolution, and transitivity reconstruct the word-level
    /// equality. An idempotent gate is bridged by its existing per-bit
    /// `bitblast_*` derivation.
    ///
    /// Non-1/non-0 constants, width or subject mismatches, foreign gate
    /// operands, over-cap widths, and surface overrides that change printed
    /// operand identity all return `None` and retain the honest `hole`.
    pub(super) fn format_bv_ult_one_zero_equiv(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let [equality] = clause else {
            return None;
        };
        let shape = self.decode_zero_test_shape(*equality)?;
        if shape.pair.width == 0 || shape.pair.width > Self::MAX_BITBLAST_LOWERING_WIDTH {
            return None;
        }
        let text = self.zero_test_text(shape)?;
        let mut out = self.format_pb_core(id, shape, &text);
        let forward = Self::append_zero_test_gate_bridge(id, shape, &text, &mut out);
        if shape.reversed {
            let _ = write!(
                out,
                "\n(step {id} (cl {}) :rule symm :premises ({forward}))",
                text.oriented_equality
            );
        }
        Some(out)
    }

    fn decode_zero_test_shape(&self, equality: TermId) -> Option<ZeroTestShape> {
        let TermData::App(Symbol::Named(eq), args) = self.terms.get(equality) else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        if eq != "=" {
            return None;
        }
        let (ult, eqz, pair, reversed) = match self.decode_zero_test_pair(*left, *right) {
            Some(pair) => (*left, *right, pair, false),
            None => (
                *right,
                *left,
                self.decode_zero_test_pair(*right, *left)?,
                true,
            ),
        };
        Some(ZeroTestShape {
            equality,
            ult,
            eqz,
            pair,
            reversed,
        })
    }

    fn decode_zero_test_pair(&self, ult: TermId, eqz: TermId) -> Option<ZeroTestPair> {
        let TermData::App(Symbol::Named(op), args) = self.terms.get(ult) else {
            return None;
        };
        let [v, one] = args.as_slice() else {
            return None;
        };
        if op != "bvult" {
            return None;
        }
        let (v, one) = (*v, *one);
        let Sort::BitVec(bits) = self.terms.sort(v) else {
            return None;
        };
        let width = bits.width;
        let TermData::Const(Constant::BitVec { value, width: cw }) = self.terms.get(one) else {
            return None;
        };
        if *cw != width || *value != 1u32.into() {
            return None;
        }

        let TermData::App(Symbol::Named(eq), args) = self.terms.get(eqz) else {
            return None;
        };
        let [first, second] = args.as_slice() else {
            return None;
        };
        if eq != "=" {
            return None;
        }
        let is_zero = |term| {
            matches!(
                self.terms.get(term),
                TermData::Const(Constant::BitVec { value, width: zw })
                    if *zw == width && *value == 0u32.into()
            )
        };
        // Equality is interned canonically by TermId, so the zero constant can
        // occupy either operand even when the authored source wrote `(= z 0)`.
        // Recover the semantic roles first; the rendered orientation is
        // checked separately and bridged with `eq_symmetric` when necessary.
        let (z, zero) = if is_zero(*second) {
            (*first, *second)
        } else if is_zero(*first) {
            (*second, *first)
        } else {
            return None;
        };

        let gate = if z == v {
            None
        } else {
            // Reuse the printer's idempotent-gate table instead of a second
            // operator match: it already pairs `bvand`/`bvor` with the exact
            // Carcara rules used below, and it is the table the wire-rule
            // coverage gate reads.
            let (operator, blast_rule, connective, simplify_rule, operand) =
                Self::decode_idempotent_bv_gate(self.terms, z)?;
            if operand != v {
                return None;
            }
            Some(ZeroTestGate {
                operator,
                connective,
                blast_rule,
                simplify_rule,
            })
        };
        Some(ZeroTestPair {
            one,
            v,
            z,
            zero,
            width,
            gate,
        })
    }

    fn zero_test_text(&self, shape: ZeroTestShape) -> Option<ZeroTestText> {
        let v = self.format_term(shape.pair.v);
        let z = self.format_term(shape.pair.z);
        let one = self.format_term(shape.pair.one);
        let zero = self.format_term(shape.pair.zero);
        let (one_value, one_width) = super::parse_printed_bitvec_literal(&one)?;
        let (zero_value, zero_width) = super::parse_printed_bitvec_literal(&zero)?;
        if one_width != shape.pair.width
            || one_value != 1_u8.into()
            || zero_width != shape.pair.width
            || zero_value != 0_u8.into()
        {
            return None;
        }
        if let Some(gate) = shape.pair.gate {
            let [first, second] =
                <[String; 2]>::try_from(super::split_application(&z, gate.operator)?).ok()?;
            if first != v || second != v {
                return None;
            }
        } else if z != v {
            return None;
        }
        let ult = self.format_term(shape.ult);
        let eqz = self.format_term(shape.eqz);
        if !super::surface_literal::equal_modulo_bitvec_literal_spelling(
            &ult,
            &format!("(bvult {v} {one})"),
        ) {
            return None;
        }
        let direct_eqz = format!("(= {z} {zero})");
        let reversed_eqz = format!("(= {zero} {z})");
        let eqz_reversed =
            if super::surface_literal::equal_modulo_bitvec_literal_spelling(&eqz, &direct_eqz) {
                false
            } else if super::surface_literal::equal_modulo_bitvec_literal_spelling(
                &eqz,
                &reversed_eqz,
            ) {
                true
            } else {
                return None;
            };
        let oriented_equality = if shape.reversed {
            format!("(= {eqz} {ult})")
        } else {
            format!("(= {ult} {eqz})")
        };
        // A source row may retain SMT-LIB's indexed numeral spelling while
        // its interned constant children print canonically as `#b...`.
        // Those spellings parse to the same bit-vector term; the bounded
        // positional comparison still rejects every changed operator,
        // operand, value, or width.
        if !super::surface_literal::equal_modulo_bitvec_literal_spelling(
            &self.format_term(shape.equality),
            &oriented_equality,
        ) {
            return None;
        }
        let pure_eq = format!("(= {v} {zero})");
        Some(ZeroTestText {
            ult,
            eqz,
            oriented_equality,
            one,
            zero,
            pure_eq,
            eqz_reversed,
            v,
            z,
        })
    }

    fn format_pb_core(&self, id: ProofId, shape: ZeroTestShape, text: &ZeroTestText) -> String {
        let width = shape.pair.width;
        let proj = |i: u32| format!("((_ @int_of {i}) {})", text.v);
        let pbx = format!(
            "(@pbbterm {})",
            (0..width).map(proj).collect::<Vec<_>>().join(" ")
        );
        let pb_const = |bit0: u32| {
            let mut items = vec![bit0.to_string()];
            items.extend((1..width).map(|_| "0".to_string()));
            format!("(@pbbterm {})", items.join(" "))
        };
        let (pb1, pb0) = (pb_const(1), pb_const(0));
        let sum_x = Self::pbblast_value_sum(&text.v, width);
        let literal_sum = |bit0: u32| {
            let summands: Vec<String> = (0..width)
                .map(|i| match i {
                    0 => bit0.to_string(),
                    _ => format!("(* {} 0)", 1_u128 << i),
                })
                .collect();
            match summands.as_slice() {
                [only] => only.clone(),
                _ => format!("(+ {})", summands.join(" ")),
            }
        };
        let (s1, s0) = (literal_sum(1), literal_sum(0));
        let up = format!("(bvult {pbx} {pb1})");
        let ep = format!("(= {pbx} {pb0})");
        let a = format!("(>= (- {s1} {sum_x}) 1)");
        let t = format!("(- {sum_x} {s0})");
        let b = format!("(= {t} 0)");
        let ab = format!("(= {a} {b})");
        let mut out = format!(
            "(step {id}.vx (cl (= {v} {pbx})) :rule pbblast_pbbvar)\n\
             (step {id}.c1 (cl (= {one} {pb1})) :rule pbblast_pbbconst)\n\
             (step {id}.c0 (cl (= {zero} {pb0})) :rule pbblast_pbbconst)\n\
             (step {id}.u1 (cl (= {ult} {up})) :rule cong :premises ({id}.vx {id}.c1))\n\
             (step {id}.e0 (cl (= {pure_eq} {ep})) :rule cong :premises ({id}.vx {id}.c0))\n\
             (step {id}.pu (cl (= {up} {a})) :rule pbblast_bvult)\n\
             (step {id}.pe (cl (= {ep} {b})) :rule pbblast_bveq)",
            v = text.v,
            one = text.one,
            zero = text.zero,
            ult = text.ult,
            pure_eq = text.pure_eq,
        );
        for i in 0..width {
            let p = proj(i);
            let _ = write!(
                out,
                "\n(step {id}.b{i} (cl (>= {p} 0)) :rule cp_literal :args ({p}))"
            );
        }
        let lits = (0..width)
            .map(|i| format!("(not (>= {} 0))", proj(i)))
            .collect::<Vec<_>>()
            .join(" ");
        let args = (0..width)
            .map(|i| (1_u128 << i).to_string())
            .collect::<Vec<_>>()
            .join(" ");
        let bres = (0..width)
            .map(|i| format!("{id}.b{i}"))
            .collect::<Vec<_>>()
            .join(" ");
        let core_id = if shape.pair.gate.is_none() && !shape.reversed && !text.eqz_reversed {
            id.to_string()
        } else {
            format!("{id}.a")
        };
        let _ = write!(
            out,
            "\n(step {id}.ld (cl (or {b} (not (<= {t} 0)) (not (<= 0 {t})))) :rule la_disequality)\n\
             (step {id}.ldc (cl {b} (not (<= {t} 0)) (not (<= 0 {t}))) :rule or :premises ({id}.ld))\n\
             (step {id}.lb (cl {lits} (<= 0 {t})) :rule la_generic :args ({args} 1))\n\
             (step {id}.lbr (cl (<= 0 {t})) :rule resolution :premises ({id}.lb {bres}))\n\
             (step {id}.ub (cl (not {a}) (<= {t} 0)) :rule la_generic :args (1 1))\n\
             (step {id}.fb (cl {b} (not {a})) :rule resolution :premises ({id}.ldc {id}.ub {id}.lbr))\n\
             (step {id}.f2 (cl {a} (not {b})) :rule la_generic :args (1 -1))\n\
             (step {id}.n1 (cl {ab} (not {a}) (not {b})) :rule equiv_neg1)\n\
             (step {id}.n2 (cl {ab} {a} {b}) :rule equiv_neg2)\n\
             (step {id}.ra (cl {ab} (not {a}) (not {a})) :rule resolution :premises ({id}.n1 {id}.fb))\n\
             (step {id}.rac (cl {ab} (not {a})) :rule contraction :premises ({id}.ra))\n\
             (step {id}.rb (cl {ab} {a} {a}) :rule resolution :premises ({id}.n2 {id}.f2))\n\
             (step {id}.rbc (cl {ab} {a}) :rule contraction :premises ({id}.rb))\n\
             (step {id}.rc (cl {ab} {ab}) :rule resolution :premises ({id}.rac {id}.rbc))\n\
             (step {id}.eq (cl {ab}) :rule contraction :premises ({id}.rc))\n\
             (step {id}.tu (cl (= {ult} {a})) :rule trans :premises ({id}.u1 {id}.pu))\n\
             (step {id}.te (cl (= {pure_eq} {b})) :rule trans :premises ({id}.e0 {id}.pe))\n\
             (step {id}.tes (cl (= {b} {pure_eq})) :rule symm :premises ({id}.te))\n\
             (step {core_id} (cl (= {ult} {pure_eq})) :rule trans :premises ({id}.tu {id}.eq {id}.tes))",
            ult = text.ult,
            pure_eq = text.pure_eq,
        );
        out
    }

    fn append_zero_test_gate_bridge(
        id: ProofId,
        shape: ZeroTestShape,
        text: &ZeroTestText,
        out: &mut String,
    ) -> String {
        let direct_eqz = format!("(= {} {})", text.z, text.zero);
        let mut eqz_bridge = None;
        if let Some(ZeroTestGate {
            operator: _,
            connective: conn,
            blast_rule,
            simplify_rule,
        }) = shape.pair.gate
        {
            let width = shape.pair.width;
            let bit = |i: u32| format!("((_ @bit_of {i}) {})", text.v);
            let gated = (0..width)
                .map(|i| format!("({conn} {b} {b})", b = bit(i)))
                .collect::<Vec<_>>();
            let bits = (0..width).map(bit).collect::<Vec<_>>();
            let bb_gated = format!("(@bbterm {})", gated.join(" "));
            let bb_bits = format!("(@bbterm {})", bits.join(" "));
            let _ = write!(
                out,
                "\n(step {id}.gb (cl (= {z} {bb_gated})) :rule {blast_rule})\n\
                 (step {id}.gv (cl (= {v} {bb_bits})) :rule bitblast_var)",
                z = text.z,
                v = text.v,
            );
            for i in 0..width {
                let bi = bit(i);
                let _ = write!(
                    out,
                    "\n(step {id}.j{i} (cl (= ({conn} {bi} {bi}) {bi})) :rule {simplify_rule})"
                );
            }
            let jres = (0..width)
                .map(|i| format!("{id}.j{i}"))
                .collect::<Vec<_>>()
                .join(" ");
            let _ = write!(
                out,
                "\n(step {id}.gc (cl (= {bb_gated} {bb_bits})) :rule cong :premises ({jres}))\n\
                 (step {id}.gl (cl (= {z} {bb_bits})) :rule trans :premises ({id}.gb {id}.gc))\n\
                 (step {id}.gr (cl (= {bb_bits} {v})) :rule symm :premises ({id}.gv))\n\
                 (step {id}.gf (cl (= {z} {v})) :rule trans :premises ({id}.gl {id}.gr))\n\
                 (step {id}.gi (cl (= {v} {z})) :rule symm :premises ({id}.gf))\n\
                 (step {id}.ge (cl (= {pure_eq} {direct_eqz})) :rule cong :premises ({id}.gi))",
                z = text.z,
                v = text.v,
                pure_eq = text.pure_eq,
            );
            eqz_bridge = Some(format!("{id}.ge"));
        }

        if text.eqz_reversed {
            let _ = write!(
                out,
                "\n(step {id}.es (cl (= {direct_eqz} {eqz})) :rule eq_symmetric)",
                eqz = text.eqz,
            );
            if let Some(prior) = eqz_bridge.as_deref() {
                let _ = write!(
                    out,
                    "\n(step {id}.et (cl (= {pure_eq} {eqz})) :rule trans :premises ({prior} {id}.es))",
                    pure_eq = text.pure_eq,
                    eqz = text.eqz,
                );
                eqz_bridge = Some(format!("{id}.et"));
            } else {
                // Without a gate `z` is `v`, so `direct_eqz` is exactly the
                // `pure_eq` endpoint produced by the pseudo-Boolean core.
                eqz_bridge = Some(format!("{id}.es"));
            }
        }

        let Some(eqz_bridge) = eqz_bridge else {
            // No gate and no inner equality reversal: the core already ends
            // at the target endpoint. It used `.a` only when the OUTER
            // equality is reversed and the caller must append one `symm`.
            return if shape.reversed {
                format!("{id}.a")
            } else {
                id.to_string()
            };
        };
        let forward_id = if shape.reversed {
            format!("{id}.fwd")
        } else {
            id.to_string()
        };
        let _ = write!(
            out,
            "\n(step {forward_id} (cl (= {ult} {eqz})) :rule trans :premises ({id}.a {eqz_bridge}))",
            ult = text.ult,
            eqz = text.eqz,
        );
        forward_id
    }
}
