// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared logic-category detection for executor solve entry points.

use ay_core::term::TermData;
use ay_core::{Constant, Sort, TermId};

use super::Executor;
use crate::features::StaticFeatures;
use crate::logic_detection::{declared_logic_routes_as_all, LogicCategory};

impl Executor {
    pub(in crate::executor) fn detect_logic_category(
        &self,
        assertions: &[TermId],
    ) -> (LogicCategory, StaticFeatures) {
        // Theory-usage routing (LOGIC-AGNOSTIC). A formula that uses set/multiset
        // operators must reach the dedicated solver that enforces its invariants
        // even under a MISMATCHED declared logic (e.g. `(set-logic QF_SLIA)` with
        // `multiset.count` or `set.card`). The `(Set T)`/`(Multiset T)` carrier is
        // erased to an array at elaboration, so generic array routing would miss
        // `card >= 0` / `count >= 0` / subset semantics and admit a wrong SAT
        // (#set-routing / #multiset-routing). We only skip the override when the
        // declared logic already routes the theory natively. Multiset takes
        // precedence over set (a formula using multiset.* needs the count carrier).
        let logic_name = self.ctx.logic();
        if self.ctx.uses_multiset()
            && !matches!(
                logic_name,
                Some("QF_MSLIA") | Some("QF_MULTISETLIA") | Some("QF_MULTISET") | Some("QF_MS")
            )
        {
            let features = StaticFeatures::collect(&self.ctx.terms, assertions);
            return (LogicCategory::QfMslia, features);
        }
        if self.ctx.uses_set() && !matches!(logic_name, Some("QF_SET") | Some("QF_SETLIA")) {
            let features = StaticFeatures::collect(&self.ctx.terms, assertions);
            return (LogicCategory::QfSetlia, features);
        }

        let logic = match self.ctx.logic() {
            // A MAPPED, explicit (non-`ALL`) declared logic keeps its own
            // routing (incl. the QF_S → QF_SEQ/QF_SLIA refinement below).
            Some(logic) if logic != "ALL" && !declared_logic_routes_as_all(logic) => {
                if logic == "QF_S" || logic == "QF_SLIA" {
                    let features = StaticFeatures::collect(&self.ctx.terms, assertions);
                    if features.has_seq_ops && features.has_int {
                        "QF_SEQLIA"
                    } else if features.has_seq_ops {
                        "QF_SEQ"
                    } else if logic == "QF_S" && features.has_int {
                        "QF_SLIA"
                    } else {
                        logic
                    }
                } else {
                    logic
                }
            }
            // `None`, explicit `ALL`, and any accepted-but-unmapped declared
            // logic (a z3-recognized token AY does not map to a category, e.g.
            // QF_UFLIRA / AUFBVDTLIA) route through the SAME content detection.
            // For a stored unmapped token this makes the verdict byte-identical
            // to the pre-leniency post-rejection path (which also left the logic
            // unset → content detection). The fail-closed combined logics are
            // NOT `declared_logic_routes_as_all` (excluded there), so they stay
            // in the mapped arm above → `LogicCategory::Other` dispatch → sound
            // `unknown`.
            _ => {
                let features = StaticFeatures::collect(&self.ctx.terms, assertions);
                let has_datatypes = self.ctx.datatype_iter().next().is_some()
                    && self.terms_contain_datatype_terms(assertions);

                if has_datatypes {
                    if features.has_fpa {
                        // DT + FP has no sound combined solver yet (#8728).
                        // Routing to QF_DT drops the FP theory entirely, which
                        // lets the DT solver satisfy `distinct(Flt NaN, Flt x)`
                        // + `fp.isNaN(getFlt_1 x)` by treating FP constants as
                        // opaque terms and returning spurious `sat`.
                        // Route to QF_BVFP/QF_FP so `with_datatypes()` maps
                        // to `Other` and the dispatch returns an
                        // `UnsupportedLogic` error (sound).
                        if features.has_bv {
                            "QF_BVFP"
                        } else {
                            "QF_FP"
                        }
                    } else if features.has_int || features.has_real {
                        if features.has_int && features.has_real {
                            "_DT_AUFLIRA"
                        } else if features.has_real {
                            "_DT_AUFLRA"
                        } else {
                            "_DT_AUFLIA"
                        }
                    } else if features.has_bv || features.has_arrays {
                        if features.has_bv && features.has_arrays {
                            "_DT_AUFBV"
                        } else if features.has_bv {
                            "_DT_UFBV"
                        } else {
                            "_DT_AX"
                        }
                    } else {
                        "QF_DT"
                    }
                } else {
                    features.infer_logic()
                }
            }
        };
        let mut category = LogicCategory::from_logic(logic);

        let assertion_has_datatypes = self.terms_contain_datatype_terms(assertions);

        if self.ctx.datatype_iter().next().is_some() && assertion_has_datatypes {
            category = category.with_datatypes();
        }

        let assertion_features = StaticFeatures::collect(&self.ctx.terms, assertions);

        // Datatype + non-DT-content routing must be LOGIC-AGNOSTIC. A datatype
        // problem whose selectors return Int/Real/BitVec (e.g. `(hd (tl (tl x)))`
        // or `(bvadd (val x) ...)`) needs the combined `_DT_AUFLIA` /
        // `_DT_AUFLRA` / `_DT_AUFLIRA` / `_DT_UFBV` / `_DT_AUFBV` / `_DT_AX`
        // solver so the other theory is reasoned about together with the
        // datatype axioms. The content-driven `Some("ALL") | None` branch
        // already chooses these categories, but an EXPLICIT DT-family declared
        // logic (e.g. `(set-logic QF_DT)`) routes straight to the pure `QfDt`
        // category, where `with_datatypes()` is a no-op and the content is never
        // widened. The pure-DT solver then admits a wrong SAT on deep chained
        // selectors over an aliased constructor (Int and BitVec both observed;
        // #dt-routing, round-3 logic-gating pattern). Mirror the ALL-branch
        // selection here regardless of the declared logic, using the SAME logic
        // strings so routing is identical.
        if matches!(category, LogicCategory::QfDt) {
            let f = &assertion_features;
            let widened = if f.has_int || f.has_real {
                if f.has_int && f.has_real {
                    Some("_DT_AUFLIRA")
                } else if f.has_real {
                    Some("_DT_AUFLRA")
                } else {
                    Some("_DT_AUFLIA")
                }
            } else if f.has_bv || f.has_arrays {
                if f.has_bv && f.has_arrays {
                    Some("_DT_AUFBV")
                } else if f.has_bv {
                    Some("_DT_UFBV")
                } else {
                    Some("_DT_AX")
                }
            } else if f.has_uf {
                // SOUNDNESS (#dt-uf-congruence wrong-sat): a pure DT + uninterpreted
                // function formula (no Int/Real/BV/Array) otherwise stays `QfDt` and
                // dispatches to the bare `solve_dt` (DtSolver only — constructor/
                // selector/tester/acyclicity, NO congruence over an arbitrary UF).
                // So `(= sk d1c0) ∧ ¬(p sk) ∧ (p d1c0)` was wrongly SAT: `p(sk)` and
                // `p(d1c0)` stayed independent Boolean atoms. Route to `_DT_AX`
                // (`solve_dt_ax` → solve_array_euf) which adds the DT axioms AND runs
                // full EUF congruence closure over `p`. Also fixes the singleton-
                // datatype forced-equality cases (EUF + tester/selector axioms force
                // `sk = d1c0`). Pure UF-free DT problems keep the fast `solve_dt`.
                Some("_DT_AX")
            } else {
                None
            };
            if let Some(logic) = widened {
                category = LogicCategory::from_logic(logic);
            }
        }

        let mut features = assertion_features.clone();
        // Extend features with declared symbols so narrowing respects all
        // theories the consumer has declared, not just those in assertions (#7442).
        features.extend_with_declarations(
            self.ctx
                .symbol_iter()
                .map(|(name, info)| (name.as_str(), info.arg_sorts.as_slice(), &info.sort)),
        );
        category = category.align_linear_arithmetic_sorts(&features);
        category = category.narrow_linear_combo_with_features(&features);
        // Widen pure arithmetic logics to UF-combined variants when UF terms
        // are present. Consumers may declare QF_LIA but add UF terms via
        // declare-fun; without widening, the LIA solver returns unknown (#7442).
        category = category.widen_with_uf(&features);
        category = category.with_nonlinear(&features);

        // Treat declared Seq logics as an upper bound too. QuantifierConsumer can emit
        // QF_SEQLIA for windows whose Seq-sorted terms only flow through UF
        // proxies such as `seq_len`. Without native `seq.*` operators, those
        // terms are satisfiability-equivalent to EUF carriers plus arithmetic;
        // forcing the Seq solver loses completeness on reducer #9227.
        if assertion_features.has_seq
            && !assertion_features.has_seq_ops
            && !assertion_has_datatypes
            && matches!(
                category,
                LogicCategory::QfSeq
                    | LogicCategory::QfSeqBv
                    | LogicCategory::QfSeqlia
                    | LogicCategory::QfS
                    | LogicCategory::QfSlia
                    | LogicCategory::QfSnia
            )
        {
            category = LogicCategory::from_logic(assertion_features.infer_logic())
                .narrow_linear_combo_with_features(&features)
                .widen_with_uf(&features)
                .with_nonlinear(&features);
        }

        // The declared logic is an upper bound. QuantifierConsumer frequently declares a
        // combined logic and then pushes a window containing only Boolean
        // structure; routing those windows through AUFLIA loses completeness in
        // incremental mode. Keep declaration-extended features for consumers,
        // but dispatch syntactically pure Boolean assertions through SAT.
        if !assertions.is_empty()
            && assertions
                .iter()
                .all(|&term| self.assertion_is_pure_bool_formula(term))
        {
            category = LogicCategory::Propositional;
        }

        // Likewise, declarations are an upper bound for theory routing. If the
        // live assertion window is pure arithmetic, unused UF/array/datatype
        // declarations should not force AUFLIA/DT-AUFLIA and lose LIA/LRA
        // completeness in incremental verifier base probes.
        if !assertions.is_empty()
            && assertion_footprint_is_pure_arithmetic(&assertion_features)
            && !assertion_has_datatypes
        {
            // `infer_logic` classifies the live arithmetic window from the broad
            // `has_int`/`has_real`, which treats bare integer numerals as Int.
            // Re-apply `align_linear_arithmetic_sorts` so the genuine Int-sort
            // rule governs: a Real-only window carrying only integer LITERALS
            // (declared QF_LRA) stays in the LRA family rather than being
            // promoted to QF_LIRA and misrouted to solve_lira (#qf-lra-lit-misroute).
            category = LogicCategory::from_logic(assertion_features.infer_logic())
                .align_linear_arithmetic_sorts(&assertion_features);
        }

        if !features.has_int
            && !features.has_real
            && !features.has_bv
            && !features.has_arrays
            && !features.has_uf
            && !features.has_strings
            && !features.has_seq
        {
            category = match category {
                LogicCategory::QfLia
                | LogicCategory::QfLra
                | LogicCategory::QfLira
                | LogicCategory::Lia
                | LogicCategory::Lra
                | LogicCategory::Lira => LogicCategory::Propositional,
                other => other,
            };
        }

        if assertion_features.has_seq_ops
            && !assertion_features.has_arrays
            && !assertion_has_datatypes
            && !matches!(
                category,
                LogicCategory::QfSeq
                    | LogicCategory::QfSeqBv
                    | LogicCategory::QfSeqlia
                    | LogicCategory::QfS
                    | LogicCategory::QfSlia
                    | LogicCategory::QfSnia
            )
        {
            category = if features.has_int {
                LogicCategory::QfSeqlia
            } else {
                LogicCategory::QfSeq
            };
        }

        (category, features)
    }

    fn assertion_is_pure_bool_formula(&self, root: TermId) -> bool {
        let terms = &self.ctx.terms;
        let mut stack = vec![root];

        while let Some(term) = stack.pop() {
            if *terms.sort(term) != Sort::Bool {
                return false;
            }

            match terms.get(term) {
                TermData::Const(Constant::Bool(_)) | TermData::Var(_, _) => {}
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(cond, then_br, else_br) => {
                    stack.push(*cond);
                    stack.push(*then_br);
                    stack.push(*else_br);
                }
                TermData::App(sym, args) => match sym.name() {
                    "and" | "or" | "xor" => stack.extend(args.iter().copied()),
                    "not" if args.len() == 1 => stack.push(args[0]),
                    "=>" if args.len() == 2 => {
                        stack.push(args[0]);
                        stack.push(args[1]);
                    }
                    "=" if args.len() == 2
                        && *terms.sort(args[0]) == Sort::Bool
                        && *terms.sort(args[1]) == Sort::Bool =>
                    {
                        stack.push(args[0]);
                        stack.push(args[1]);
                    }
                    "distinct"
                        if args.len() >= 2
                            && args.iter().all(|&arg| *terms.sort(arg) == Sort::Bool) =>
                    {
                        stack.extend(args.iter().copied());
                    }
                    _ if args.is_empty() => {}
                    _ => return false,
                },
                TermData::Const(_)
                | TermData::Let(_, _)
                | TermData::Forall(_, _, _)
                | TermData::Exists(_, _, _)
                | _ => return false,
            }
        }

        true
    }
}

fn assertion_footprint_is_pure_arithmetic(features: &StaticFeatures) -> bool {
    (features.has_int || features.has_real)
        && !features.has_bv
        && !features.has_arrays
        && !features.has_strings
        && !features.has_seq
        && !features.has_regex
        && !features.has_fpa
        && !features.has_uf
        && !features.has_bv_int_conversion
}
