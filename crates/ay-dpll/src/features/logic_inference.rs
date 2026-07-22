// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Logic string inference from static formula features.
//!
//! Extracted from `mod.rs` for code health. Maps collected `StaticFeatures`
//! to the appropriate SMT-LIB logic string (e.g., "QF_LIA", "QF_AUFBV").

use super::StaticFeatures;

impl StaticFeatures {
    /// Infer the best logic string from collected features.
    ///
    /// Follows Z3's auto-detection logic from `smt_setup.cpp:831-935`.
    /// Extended to detect non-linear arithmetic (#1551).
    pub(crate) fn infer_logic(&self) -> &'static str {
        // Quantified logics
        if self.has_quantifiers {
            // BV with quantifiers - AY doesn't support this yet, but route to QF_BV
            // which will report "unknown" for quantified formulas
            if self.has_bv {
                if self.has_arrays && self.has_uf {
                    return "QF_AUFBV";
                }
                if self.has_arrays {
                    return "QF_ABV";
                }
                return "QF_BV";
            }
            if self.has_arrays && self.has_uf {
                if self.has_int && self.has_real {
                    return "AUFLIRA";
                }
                if self.has_real {
                    return "AUFLRA";
                }
                if self.has_int {
                    return "AUFLIA";
                }
            }
            // Mixed integer/real arithmetic (#5888)
            if self.has_int && self.has_real {
                if self.has_nonlinear_int || self.has_nonlinear_real {
                    // Preserve UF information for non-linear logics (#5984)
                    return if self.has_uf { "UFNIRA" } else { "NIRA" };
                }
                return "LIRA";
            }
            // Non-linear quantified arithmetic
            if self.has_real {
                if self.has_nonlinear_real {
                    return if self.has_uf { "UFNRA" } else { "NRA" };
                }
                return "LRA";
            }
            if self.has_int {
                if self.has_nonlinear_int {
                    return if self.has_uf { "UFNIA" } else { "NIA" };
                }
                return "LIA";
            }
            return "UF";
        }

        // QF: Native finite-set theory. `set.card`/`set.subset` (and the
        // fail-closed combinators) MUST route to the set solver so the ground
        // cardinality axioms (`card >= 0`, `card(empty)=0`) are injected;
        // otherwise `set.card` is an unconstrained opaque UF (unsound).
        //
        // This is checked FIRST among the quantifier-free theory branches —
        // ahead of single-theory, BV, and arithmetic routing — because the set
        // carrier `Set(T) = Array(T → Bool)` always makes `has_arrays` true and,
        // when `T` is a bitvector sort, also makes `has_bv` true. Without this
        // precedence a `set.card`/`set.subset` query over `Set(BV n)` would fall
        // into the BV/array branch (QF_ABV/QF_AUFBV) and the card/subset symbols
        // would degrade to opaque UF (unsound). The `UfSetLiaSolver` combination
        // embeds EUF + Arrays + Set + LIA, so the BV-sorted membership carrier is
        // still decided soundly: membership is `select` over `Array(BV → Bool)`
        // (handled by the array solver), and the card/subset saturation rules are
        // sort-agnostic over the element sort. Always use QF_SETLIA (it subsumes
        // QF_SET with the LIA card bridge).
        if self.has_set_ops {
            return "QF_SETLIA";
        }

        // QF: Native multiset theory. `multiset.count`/`multiset.subset` (and the
        // fail-closed combinators) MUST route to the multiset solver so the
        // ground count axioms (`count >= 0`, subset↔count) are injected;
        // otherwise `multiset.subset` is an unconstrained opaque UF (unsound).
        //
        // Checked here — ahead of single-theory, BV, and arithmetic routing —
        // for exactly the same reason as the set branch above: the count carrier
        // `Multiset(T) = Array(T → Int)` always makes `has_arrays` (and
        // `has_int`) true and, when `T` is a bitvector sort, also `has_bv`.
        // Without this precedence a `multiset.count`/`multiset.subset` query over
        // `Multiset(BV n)` would fall into the BV/array branch (QF_ABV/QF_AUFBV)
        // and the count/subset symbols would degrade to opaque UF (unsound). The
        // `UfMultisetLiaSolver` combination embeds EUF + Arrays + Multiset + LIA,
        // so the BV-sorted count carrier is still decided soundly: the count
        // carrier is `select` over `Array(BV → Int)` (handled by the array
        // solver), and the subset reflexivity rule is sort-agnostic over the
        // element sort. Always use QF_MSLIA (it subsumes QF_MULTISET with the LIA
        // count bridge).
        if self.has_multiset_ops {
            return "QF_MSLIA";
        }

        // QF: Native finite-map theory. The surviving `map.*` symbols
        // (`map.insert`/`map.remove`/`map.dom`/`map.subset` and the fail-closed
        // image ops) MUST route to the map solver so the ground subset↔key
        // obligations are injected and out-of-fragment ops fail closed;
        // otherwise `map.subset` is an unconstrained opaque UF (unsound).
        //
        // Checked here — ahead of single-theory, BV, and arithmetic routing —
        // for exactly the same reason as the set/multiset branches above: the
        // value carrier `Map(K, V) = Array(K → V)` always makes `has_arrays`
        // true and, when `K` (or `V`) is a bitvector sort, also makes `has_bv`
        // true. Without this precedence a `map.subset`/`map.dom` query over
        // `Map(BV n, _)` would fall into the BV/array branch (QF_ABV/QF_AUFBV)
        // and the map symbols would degrade to opaque UF (unsound). The
        // `UfMapLiaSolver` combination embeds EUF + Arrays + Map + LIA, so the
        // BV-sorted key carrier is still decided soundly: get/dom are `select`
        // over the value/domain `Array(BV → _)` (handled by the array solver),
        // and the subset reflexivity rule is sort-agnostic over the key sort.
        // Always use QF_MAPLIA (it subsumes QF_MAP with the LIA bridge for any
        // numeric key/value relations, e.g. a map size).
        if self.has_map_ops {
            return "QF_MAPLIA";
        }

        // QF: Pure theories (no non-UF theories)
        if self.num_theories == 0 {
            return "QF_UF"; // Pure UF or propositional
        }

        // QF: Single theory (without UF - UF combinations handled below)
        if self.num_theories == 1 && !self.has_uf {
            if self.has_bv {
                return "QF_BV";
            }
            if self.has_int {
                if self.has_nonlinear_int {
                    return "QF_NIA";
                }
                return "QF_LIA";
            }
            if self.has_real {
                if self.has_nonlinear_real {
                    return "QF_NRA";
                }
                return "QF_LRA";
            }
            if self.has_arrays {
                return "QF_AX";
            }
            if self.has_strings {
                return "QF_S";
            }
            if self.has_seq_ops {
                return "QF_SEQ";
            }
            if self.has_fpa {
                if self.has_bv {
                    return "QF_BVFP";
                }
                return "QF_FP";
            }
        }

        // QF: BV combinations (common for Kani/verification)
        if self.has_bv {
            // String + BV appears in format-string and binary-analysis queries.
            // No combined solver exists yet; routing to QF_BV drops string
            // constraints and can produce spurious SAT (#8333).
            if self.has_strings {
                return "_STRING_BV";
            }
            if self.has_arrays && self.has_fpa {
                return "QF_ABVFP";
            }
            // BV + FP: route to combined solver so FP constraints are not lost.
            // Without this, BV+FP formulas (e.g., fp-to-bv conversions under
            // auto-detection) silently drop FP semantics and route to QF_BV.
            if self.has_fpa {
                return "QF_BVFP";
            }
            // BV + Int/Real: check if cross-theory conversion functions are used.
            if self.has_int || self.has_real {
                if self.has_bv_int_conversion {
                    // Actual cross-theory interaction via bv2nat/int2bv (#5503).
                    // No combined BV+LIA solver exists yet — route to explicit
                    // category so the executor returns Unknown with a clear reason.
                    return "_BV_LIA";
                }
                // BV and Int/Real coexist but without conversion functions (#5356).
                // Route to AUFLIA which treats BV terms as uninterpreted. Sound
                // for SAT (UF handles BV equalities), incomplete for UNSAT.
                return "_BV_LIA_INDEP";
            }
            if self.has_arrays && self.has_uf {
                return "QF_AUFBV";
            }
            if self.has_arrays {
                return "QF_ABV";
            }
            if self.has_uf {
                return "QF_UFBV";
            }
            return "QF_BV";
        }

        // QF: FP combinations with non-BV theories.
        // FP + Int/Real or FP + Strings: no combined solver exists. Route to
        // QF_FP so the FP solver's arithmetic guard can return Unknown (sound)
        // rather than silently ignoring FP constraints.
        if self.has_fpa {
            return "QF_FP";
        }

        // QF: Native Seq + Integer arithmetic combinations (seq.len produces Int).
        // Seq-sorted UF proxies without `seq.*` operators are routed as EUF/LIA.
        if self.has_seq_ops && self.has_int {
            return "QF_SEQLIA";
        }
        if self.has_seq_ops {
            return "QF_SEQ";
        }

        // QF: Strings + Integer arithmetic combinations.
        // When arrays are also present, skip this block and fall through to the
        // arithmetic+arrays block which routes to AUFLIA/AUFLRA. The array solver
        // handles array axioms (ROW1/ROW2) correctly while string constraints
        // degrade to uninterpreted — incomplete but sound. Without this guard,
        // QF_SLIA silently drops array semantics causing unsound SAT (#6724).
        if self.has_strings && self.has_int && !self.has_arrays {
            if self.has_nonlinear_int {
                return "QF_SNIA";
            }
            return "QF_SLIA";
        }

        // QF: Arithmetic combinations
        if self.has_int || self.has_real {
            let has_both = self.has_int && self.has_real;
            let has_nonlinear = self.has_nonlinear_int || self.has_nonlinear_real;

            // Arrays + arithmetic: route to array-aware logics (AUFLIA/AUFLRA).
            // The "UF" in "AUFLIA" is part of the standard logic name; we route
            // here regardless of whether uninterpreted functions are present.
            if self.has_arrays {
                if has_both {
                    if has_nonlinear {
                        // Arrays+UF+nonlinear: preserve UF info (#5984)
                        return "QF_AUFNIA";
                    }
                    return "QF_AUFLIRA";
                }
                if self.has_real {
                    if self.has_nonlinear_real {
                        return "QF_AUFNRA";
                    }
                    return "QF_AUFLRA";
                }
                if self.has_nonlinear_int {
                    return "QF_AUFNIA";
                }
                return "QF_AUFLIA";
            }
            if self.has_uf {
                // Check mixed Int/Real FIRST to avoid dropping integer constraints.
                // AUFLIRA subsumes UFLIRA (array solver is a no-op without arrays).
                if has_both {
                    if has_nonlinear {
                        // UF + nonlinear mixed: no combined solver (#5984)
                        return "QF_UFNIRA";
                    }
                    return "QF_AUFLIRA";
                }
                if self.has_real {
                    if self.has_nonlinear_real {
                        // Preserve UF information for non-linear logics (#5984)
                        return "QF_UFNRA";
                    }
                    return "QF_UFLRA";
                }
                if self.has_nonlinear_int {
                    return "QF_UFNIA";
                }
                return "QF_UFLIA";
            }
            if has_both {
                if has_nonlinear {
                    // Route to NIRA so the dispatcher can detect Real terms and
                    // return Unknown instead of silently solving as pure NIA.
                    return "QF_NIRA";
                }
                return "QF_LIRA";
            }
            if self.has_real {
                if self.has_nonlinear_real {
                    return "QF_NRA";
                }
                return "QF_LRA";
            }
            // Int only
            if self.has_nonlinear_int {
                return "QF_NIA";
            }
            return "QF_LIA";
        }

        // QF: Arrays only
        if self.has_arrays {
            if self.has_uf {
                return "QF_AUFLIA"; // Arrays need index theory
            }
            return "QF_AX";
        }

        // Fallback
        "QF_UF"
    }
}
