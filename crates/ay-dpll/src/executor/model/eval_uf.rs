// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UF (uninterpreted function) model evaluation helpers.
//!
//! Extracted from mod.rs (Packet 6 Step 2).

use ay_bv::BvModel;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use ay_euf::EufModel;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::{EvalValue, Model};
use crate::executor_format::format_bitvec;

use super::Executor;

impl Executor {
    /// Convert an evaluated value into the atom format used in EUF function tables.
    pub(super) fn eval_value_to_model_atom(&self, value: &EvalValue) -> Option<String> {
        match value {
            EvalValue::Bool(true) => Some("true".to_string()),
            EvalValue::Bool(false) => Some("false".to_string()),
            EvalValue::Element(elem) => Some(elem.clone()),
            EvalValue::Rational(r) => {
                if r.is_integer() {
                    Some(r.numer().to_string())
                } else {
                    Some(format!("(/ {} {})", r.numer(), r.denom()))
                }
            }
            EvalValue::BitVec { value, width } => Some(format_bitvec(value, *width)),
            EvalValue::Fp(fp_val) => Some(fp_val.to_smtlib()),
            EvalValue::String(s) => Some(s.clone()),
            EvalValue::Seq(_) => None, // Seq values have no atomic representation
            // Exact NRA algebraic value: rational-valued expressions render as
            // rationals, irrational ones in z3 `root-obj` syntax.
            EvalValue::Algebraic(a) => match a.to_number() {
                Some(ay_nra::RealScalar::Rational(r)) => {
                    if r.is_integer() {
                        Some(r.numer().to_string())
                    } else {
                        Some(format!("(/ {} {})", r.numer(), r.denom()))
                    }
                }
                Some(ay_nra::RealScalar::Algebraic(n)) => Some(n.alpha().to_smtlib()),
                None => None,
            },
            EvalValue::Unknown => None,
        }
    }

    /// Whether a term is an interpreted ARITHMETIC composite (`+ - * div mod
    /// abs` application, or an `ite`) — a defined function of its subterms
    /// whose model value must be COMPUTED, never read from EUF's fabricated
    /// per-class completion ints (#uflia-arith-arg-key).
    fn is_arith_composite(terms: &ay_core::TermStore, term: TermId) -> bool {
        match terms.get(term) {
            TermData::App(sym, _) => {
                matches!(sym.name(), "+" | "-" | "*" | "div" | "mod" | "abs")
            }
            TermData::Ite(..) => true,
            _ => false,
        }
    }

    /// Build the lookup key for one UF application argument in EUF function tables.
    fn uf_table_arg_key(&self, model: &Model, euf_model: &EufModel, arg: TermId) -> Option<String> {
        // A lambda body reuses the same argument TermId at several concrete
        // beta instances. While a contextual binding is active, every table
        // key must therefore come from recursive evaluation under that binding;
        // SAT/LIA/EUF values keyed only by `arg` belong to the ambient term and
        // can name a different function point. An unevaluable/non-atomic value
        // fails closed instead of manufacturing a placeholder that might match.
        if super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, arg) {
            return self.eval_value_to_model_atom(&self.evaluate_term(model, arg));
        }
        if matches!(self.ctx.terms.sort(arg), Sort::Bool) {
            if let Some(value) = self.term_value(&model.sat_model, &model.term_to_var, arg) {
                return Some(if value {
                    "true".to_string()
                } else {
                    "false".to_string()
                });
            }
            if let Some(raw) = euf_model.term_values.get(&arg) {
                if raw == "true" || raw == "false" {
                    return Some(raw.clone());
                }
            }
            if let EvalValue::Bool(value) = self.evaluate_term(model, arg) {
                return Some(if value {
                    "true".to_string()
                } else {
                    "false".to_string()
                });
            }
            return Some(format!("@?{}", arg.0));
        }

        let arg_sort = self.ctx.terms.sort(arg);
        if matches!(arg_sort, Sort::Int) {
            // #uflia-gate-model-read: for Int LEAF args (vars/consts) the
            // emitted model value is LIA's — get-model prints Int leaves
            // LIA-first (pinned by get_model_int_prefers_lia_over_stale_euf_
            // term_value). EUF's int_values may hold a FABRICATED completion
            // value for a leaf it never constrained (preprocessing substituted
            // the leaf out of EUF's view, e.g. x:=1 rewriting (f x) to (f 1)),
            // so keying the function table by it reads a DIFFERENT point than
            // the emitted model — the exact self-inconsistency the independent
            // model gate refutes (ModelViolates → spurious unknown). App args
            // use the committed numeric class view: combined-model extraction
            // now runs LIA fixup before merge and synchronizes every scoped
            // e-class peer into BOTH EUF maps, so a stale opaque registration
            // default cannot intentionally diverge here.
            if !matches!(self.ctx.terms.get(arg), TermData::App(_, _)) {
                if let Some(ref lia_model) = model.lia_model {
                    if let Some(value) = lia_model.values.get(&arg) {
                        return Some(value.to_string());
                    }
                }
            }
            // #uflia-arith-arg-key: an ARITHMETIC composite arg (`(+ fmt1
            // (- fmt0) (- 2))`) is a defined function of its leaves — its
            // model value is COMPUTED bottom-up from the emitted leaf values,
            // never read from EUF's fabricated per-class completion ints.
            // Reading int_values for it keyed the table at a point that
            // contradicts the emitted model (preprocessing had rewritten the
            // composite out of the solver's view, so its class int was pure
            // fabrication), which broke UF congruence under the gate's eyes
            // and degraded genuine sats on the QF_UFLIA wisas family. Opaque
            // (UF) apps keep int_values-first (#5432).
            if Self::is_arith_composite(&self.ctx.terms, arg) {
                if let EvalValue::Rational(r) = self.evaluate_term(model, arg) {
                    if r.is_integer() {
                        return Some(r.numer().to_string());
                    }
                }
            }
            if let Some(value) = euf_model.int_values.get(&arg) {
                return Some(value.to_string());
            }
        }

        if let Some(raw) = euf_model.term_values.get(&arg) {
            return Some(raw.clone());
        }

        if matches!(self.ctx.terms.get(arg), TermData::Const(_)) {
            if let Some(key) = self.eval_value_to_model_atom(&self.evaluate_term(model, arg)) {
                return Some(key);
            }
        }

        // #uflia-arith-arg-key: in a QUANTIFIER-FREE problem, an INTERPRETED-
        // arithmetic argument composite — `(+ aux2 1)`, `(- n 1)`, `(* 2 k)`,
        // etc. — whose specific `TermId` the committed model tables miss is
        // nonetheless a pure LIA/LRA function of its leaves and evaluates to a
        // concrete scalar. AUFLIA preprocessing routinely mints a FRESH `TermId`
        // for the same arithmetic expression (VariableSubstitution /
        // PropagateValues), so the function-table ROW is keyed under the
        // preprocessed instance while validation re-keys under the restored
        // ORIGINAL instance; the two share a value but not an id, and the row's
        // own key resolves through `term_values`/LIA to the same concrete atom.
        // Evaluating the composite here yields that SAME atom, so the lookup keys
        // align and the committed row (the solver's own model value) is read.
        //
        // Sound: this reads the model's genuine value for the argument — it can
        // only make the lookup KEY faithful to the model, never fabricate a table
        // row or a satisfying value; an unevaluable composite keeps the `@?id`
        // fail-safe. Restricted to arithmetic-operator apps (never a UF
        // application), so no function-table row cross-reference / divergence is
        // introduced.
        //
        // GATED to quantifier-free problems (`!original_problem_had_quantifiers`):
        // in a QF problem a SAT verdict rests entirely on ground reasoning, so a
        // faithful ground function-table read is exactly the completeness this
        // needs. In a QUANTIFIED problem the independent evaluator may report
        // `cannot-confirm`, and resolving an
        // arg-key for an MBQI-instantiated term — e.g. `(+ (f 3) 1)` from a
        // `forall x. .. f(x+1) ..` body — would let an incomplete path validate
        // ground instances of a quantifier shape ay does NOT certify complete
        // (the finite-table certificate deliberately fails closed on shifted
        // arguments). Keeping the conservative `@?id` fail-safe there preserves
        // that guard; the improvement is confined to the QF fragment it targets.
        if !self.original_problem_had_quantifiers
            && matches!(arg_sort, Sort::Int | Sort::Real)
            && Self::is_interpreted_arith_composite(self.ctx.terms.get(arg))
        {
            if let Some(key) = self.eval_value_to_model_atom(&self.evaluate_term(model, arg)) {
                return Some(key);
            }
        }

        Some(format!("@?{}", arg.0))
    }

    /// True when `term` is an INTERPRETED arithmetic composite — an application
    /// of a built-in arithmetic operator (`+`, `-`, `*`, `/`, `div`, `mod`,
    /// `abs`, `to_real`, `to_int`) — as opposed to an uninterpreted function
    /// application. Such a term evaluates to a concrete scalar purely from its
    /// leaves and never owns a UF function table, so evaluating it during
    /// function-table key resolution cannot re-enter a table's congruent-row
    /// reference graph (#uflia-arith-arg-key).
    fn is_interpreted_arith_composite(term: &TermData) -> bool {
        matches!(
            term,
            TermData::App(sym, _)
                if matches!(
                    sym.name(),
                    "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_real" | "to_int"
                )
        )
    }

    /// Resolve an APPLICATION-valued function-table placeholder (`@?id`, where
    /// `id` is itself a UF application) to a model atom through COMMITTED,
    /// NON-RECURSIVE reads: the pinned constant (`func_app_const_terms`), then
    /// the committed class value (`int_values` for Int, `term_values`
    /// otherwise).
    ///
    /// Deliberately NEVER calls `evaluate_term` on the application itself.
    /// `evaluate_term` of a UF app re-enters `evaluate_uf_app_from_function_
    /// table`, and congruent rows of a table reference each other cyclically
    /// (`f(x) -> @?a` / `f(1) -> @?b`), so that recursion is mutually recursive:
    /// the #eval-cycle-guard turns it from a divergence into a bounded but
    /// EXPONENTIAL re-exploration of the tables' reference graph. Every atom a
    /// table can supply is a COMMITTED value anyway — the pin or the class
    /// value — so nothing is lost by reading it directly.
    ///
    /// The pinned constant is a leaf, so evaluating it cannot re-enter a table.
    ///
    /// Exposed to `crate::executor::mbqi` so the DT-MBQI-Sat certificate's
    /// EUF-extraction faithfulness pass can read the SAME committed anchors —
    /// independently of the arg-keyed function-table synthesis `evaluate_term`
    /// uses to build the F4 tables — and cross-check the two for agreement.
    pub(in crate::executor) fn committed_app_atom(
        &self,
        model: &Model,
        euf_model: &EufModel,
        term_id: TermId,
    ) -> Option<String> {
        // Every source below is an ambient, TermId-keyed commitment.  A
        // dependent application denotes a different point in the active beta
        // environment and must be evaluated through its arguments instead.
        if super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id) {
            return None;
        }

        // #uflia-arith-arg-key: a SPECULATIVE (fabricated per-class) value is
        // not a COMMITTED read. Returning it here let a congruent row
        // (`s_count(fmt1-2) -> @?560`) resolve `(s_count 3)` to a fabricated
        // int that contradicts the LIA value committed for the target's own
        // class — the table scan must instead skip this row and reach the
        // committed one (`s_count(3) -> 2`). Terms with only a speculative
        // value stay resolvable through the caller's own-term fallbacks, so
        // EUF-only-constrained models (distinct-heavy families) are unchanged.
        if euf_model.speculative_int_terms.contains(&term_id) {
            return euf_model
                .func_app_const_terms
                .get(&term_id)
                .map(|&const_id| self.evaluate_term(model, const_id))
                .and_then(|ev| self.eval_value_to_model_atom(&ev));
        }
        euf_model
            .func_app_const_terms
            .get(&term_id)
            .map(|&const_id| self.evaluate_term(model, const_id))
            .and_then(|ev| self.eval_value_to_model_atom(&ev))
            .or_else(|| {
                if matches!(self.ctx.terms.sort(term_id), Sort::Int) {
                    euf_model
                        .int_values
                        .get(&term_id)
                        .map(|value| value.to_string())
                } else {
                    None
                }
            })
            .or_else(|| euf_model.term_values.get(&term_id).cloned())
    }

    /// Evaluate UF applications via extracted function tables when available.
    pub(super) fn evaluate_uf_app_from_function_table(
        &self,
        model: &Model,
        name: &str,
        args: &[TermId],
        result_sort: &Sort,
        target_term_id: TermId,
    ) -> Option<EvalValue> {
        let euf_model = model.euf_model.as_ref()?;
        let table = euf_model.function_tables.get(name)?;

        let resolve_table_atom = |raw: &str| -> Option<String> {
            let Some(term_id) = raw
                .strip_prefix("@?")
                .and_then(|id_str| id_str.parse::<u32>().ok())
                .map(TermId)
                .filter(|term_id| (term_id.0 as usize) < self.ctx.terms.len())
            else {
                return Some(raw.to_string());
            };

            // Function-table rows are concrete ambient model points, not
            // templates.  Reinterpreting a placeholder term under the active
            // binder can make an ambient row spuriously match another beta
            // point; reading its ambient value has the dual failure.
            if super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id) {
                return None;
            }

            let resolved = if matches!(self.ctx.terms.sort(term_id), Sort::Int) {
                // #uflia-gate-model-read: LIA-first for Int LEAF atoms,
                // mirroring uf_table_arg_key, so a row keyed by a leaf
                // term resolves to the SAME atom as a lookup of that
                // leaf (see the rationale there).
                let lia_leaf = if !matches!(self.ctx.terms.get(term_id), TermData::App(_, _)) {
                    model
                        .lia_model
                        .as_ref()
                        .and_then(|lia_model| lia_model.values.get(&term_id))
                        .map(ToString::to_string)
                } else {
                    None
                };
                let arithmetic_composite = if Self::is_arith_composite(&self.ctx.terms, term_id) {
                    match self.evaluate_term(model, term_id) {
                        EvalValue::Rational(r) if r.is_integer() => Some(r.numer().to_string()),
                        _ => None,
                    }
                } else {
                    None
                };
                lia_leaf
                    .or(arithmetic_composite)
                    .or_else(|| euf_model.int_values.get(&term_id).map(ToString::to_string))
                    .or_else(|| euf_model.term_values.get(&term_id).cloned())
            } else {
                euf_model.term_values.get(&term_id).cloned()
            }
            .or_else(|| {
                // #uf-table-entry-nonrec: an APP-valued ENTRY atom is
                // resolved by committed reads only — exactly as a row's
                // APP-valued RESULT atom already is (the arm below).
                // This arm used to run a FULL `evaluate_term` on the
                // app, which re-enters this very table scan for a
                // congruent row, whose own entry atoms re-enter again.
                // Every row of every lookup re-walked that reference
                // graph, so the #eval-cycle-guard's fail-closed cut
                // bounded the MEMORY but left the TIME exponential —
                // and the seq_* tables' cross-references form one giant
                // SCC, so the #eval-lowlink memo cannot admit anything
                // inside it either. That was the 30s slice_index
                // verification-consumer spin: ~29s in ONE `evaluate_term`.
                //
                // Resolution-preserving: a table atom's value is always
                // a COMMITTED one (the pinned constant or the class
                // value), which `committed_app_atom` reads directly.
                // All the dropped recursion could ADD is the app's own
                // arg-keyed TABLE lookup — and for the sorts that reach
                // here that cannot even yield an atom: measured over the
                // three slice_index fixtures, 100% of these fallbacks
                // were `(Seq Int)`-sorted and 100% returned `None`
                // (`eval_value_to_model_atom` has no atomic form for
                // `EvalValue::Seq`, and `parse_model_value_string` none
                // for `Sort::Seq`) — the recursion was computed, then
                // thrown away.
                if matches!(self.ctx.terms.get(term_id), TermData::App(_, _)) {
                    return self.committed_app_atom(model, euf_model, term_id);
                }
                // Leaf atom (var/const): evaluating it reads the theory
                // models directly and cannot re-enter a function table.
                self.eval_value_to_model_atom(&self.evaluate_term(model, term_id))
            });

            // Preserve unresolved, binder-independent placeholders as opaque
            // atoms exactly as before.  Only dependent placeholders fail the
            // row match above.
            Some(resolved.unwrap_or_else(|| raw.to_string()))
        };

        let arg_key: Vec<String> = args
            .iter()
            .map(|&arg| self.uf_table_arg_key(model, euf_model, arg))
            .collect::<Option<_>>()?;

        // #uflia-gate-model-read: scan ALL rows matching the argument point
        // instead of taking only the first. The first match can be the
        // target's own SELF-ROW (`f(x) -> @?target`), whose result resolves to
        // nothing — previously that aborted the whole lookup and the caller
        // fell through to EUF's fabricated completion value, reading a model
        // point that contradicts the emitted witness (spurious ModelViolates).
        // Skipping unresolvable rows lets the lookup reach the congruent
        // pinned row (`f(1) -> 10`). An APP-valued result placeholder resolves
        // ONLY via the pinned constant (func_app_const_terms): full
        // evaluate_term recursion between congruent rows (f(x)->@?a /
        // f(1)->@?b) is mutually recursive and diverges.
        let mut resolved: Option<String> = None;
        for (entry_args, raw_result) in table.iter() {
            let matches_point = entry_args.len() == arg_key.len()
                && entry_args.iter().zip(&arg_key).all(|(entry_arg, key)| {
                    resolve_table_atom(entry_arg).as_deref() == Some(key.as_str())
                });
            if !matches_point {
                continue;
            }
            let candidate = match raw_result
                .strip_prefix("@?")
                .and_then(|id_str| id_str.parse::<u32>().ok())
                .map(TermId)
                .filter(|term_id| (term_id.0 as usize) < self.ctx.terms.len())
            {
                Some(term_id)
                    if super::dt_model::term_depends_on_scoped_binding(
                        &self.ctx.terms,
                        term_id,
                    ) =>
                {
                    None
                }
                Some(term_id) if term_id == target_term_id => {
                    // Self-row: keep scanning for a resolvable congruent row.
                    None
                }
                Some(term_id) if matches!(self.ctx.terms.get(term_id), TermData::App(_, _)) => {
                    // Congruent-app row: resolve via the pinned constant, or —
                    // when no constant was pinned (func_app_const_terms empty,
                    // e.g. preprocessing substituted a:=1 so EUF only merged
                    // (f 1)/(f 2) and the ORPHANED originals (f a)/(f b) got
                    // fabricated completion values) — via direct NON-RECURSIVE
                    // reads of the committed class value. Shared with the ENTRY
                    // atom resolver (#uf-table-entry-nonrec): both sides of a
                    // row now read app placeholders the same, non-diverging way.
                    self.committed_app_atom(model, euf_model, term_id)
                }
                Some(term_id) => self.eval_value_to_model_atom(&self.evaluate_term(model, term_id)),
                None => Some(raw_result.clone()),
            };
            if let Some(c) = candidate {
                if !c.starts_with("@?") {
                    resolved = Some(c);
                    break;
                }
            }
        }
        let resolved_result = resolved?;
        let parsed = self.parse_model_value_string(&resolved_result, &Some(result_sort.clone()));
        // If parsing returned Unknown, the function table had a placeholder value
        // (e.g., "@?{id}" for Int/Real-sorted results built before term_values
        // were populated). Fall through to per-sort model lookups which have
        // correct data via func_app_const_terms or int_values (#4686).
        match parsed {
            EvalValue::Unknown => None,
            other => Some(other),
        }
    }

    /// Evaluate an uninterpreted function application by consulting theory models.
    ///
    /// This is the catch-all handler for `TermData::App` terms that do not match
    /// any known built-in theory operation (arithmetic, BV, arrays, strings, etc.).
    /// It covers DT constructors, UF function tables, SAT-literal fallback for
    /// Bool-sorted UF predicates, per-sort theory model lookups (Int, Real, BV, FP),
    /// EUF model lookups, and assertion-equality resolution for DT selectors.
    ///
    /// Extracted from mod.rs for code health (#5970).
    pub(super) fn evaluate_uninterpreted_app(
        &self,
        model: &Model,
        name: &str,
        args: &[TermId],
        sort: &Sort,
        term_id: TermId,
    ) -> EvalValue {
        let context_dependent =
            super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id);
        // Equality-only Seq carriers are solved through EUF, whose raw
        // `term_values` entry is an opaque class label rather than a sequence.
        // Completion materializes that class as a concrete `EvalValue::Seq` in
        // the common completion slot. Read the concrete witness before any
        // function-table/EUF fallback so UF applications, validation, and
        // get-value share the same interpretation. Context-dependent terms are
        // excluded: a TermId-keyed ambient value cannot represent a lambda
        // body's distinct beta instances.
        if !context_dependent && matches!(sort, Sort::Seq(_)) {
            if let Some(value @ EvalValue::Seq(_)) = model.completed_values.get(&term_id) {
                return value.clone();
            }
        }
        // DT constructor recognition: nullary constructors like `Green`
        // or `Nothing` are 0-arity applications that should evaluate to
        // their constructor name, not Unknown. This is needed for pure
        // QF_DT where there is no EUF model to look up (#5450).
        if args.is_empty() && self.ctx.is_constructor(name).is_some() {
            return EvalValue::Element(name.to_string());
        }
        // #dt-depth-structural: evaluate an acyclicity-instrumentation depth
        // application (`__ay_dt_depth_<dt>`, injected by
        // `dt_acyclicity_depth_axioms_up_to`) by the ACTUAL constructor depth
        // of the argument's resolved datatype value. This must run BEFORE the
        // UF-function-table / LIA / EUF lookups: the committed entries those
        // hold for these internal terms can be mutually INCONSISTENT for
        // CONGRUENT arguments (extraction reads different sources per term),
        // which made the strict validation gate reject ay's own injected depth
        // congruence / monotonicity axioms on trivially-SAT recursive-datatype
        // inputs. The structural depth is a genuine function of the model
        // VALUE, so those axioms hold under it by construction (a consistent
        // model completion). FAIL-CLOSED: a CYCLIC or unresolvable value has
        // no finite structural depth (`None`), and we fall through to the
        // committed theory values exactly as before — a cyclic witness keeps
        // its term-level depth contradiction (`depth(x) = depth(cons(.. x))`
        // vs `depth(cons(.. x)) >= depth(x) + 1`) and can never validate as
        // sat through this path.
        if !context_dependent && name.starts_with("__ay_dt_depth_") && args.len() == 1 {
            if let Some(d) = self.dt_structural_depth(model, args[0], 256) {
                return EvalValue::Rational(BigRational::from(d));
            }
        }
        if !context_dependent
            && matches!(sort, Sort::Int)
            && name == "sk"
            && args.len() == 2
            && matches!(self.ctx.terms.sort(args[0]), Sort::Array(_))
            && matches!(self.ctx.terms.sort(args[1]), Sort::Array(_))
        {
            // #qf-auflia-sk: the APPLICATION's own model value is
            // authoritative when the solver assigned one — every other
            // assertion was checked against THAT index. Overriding it with an
            // independently computed witness produced a DIFFERENT (also
            // valid) witness index, so `(= i (sk a b))` evaluated false and
            // in-loop validation degraded genuine sats (the storecomm/
            // storeinv `_pp_` skolemized-extensionality families: 30 of the
            // 120-file QF_AUFLIA 60s sample). The witness search is the
            // FALLBACK for models that never pinned the application.
            if let Some(ref euf_model) = model.euf_model {
                if let Some(&const_term_id) = euf_model.func_app_const_terms.get(&term_id) {
                    return self.evaluate_term(model, const_term_id);
                }
                if let Some(raw) = euf_model.term_values.get(&term_id) {
                    if let EvalValue::Rational(r) =
                        self.parse_model_value_string(raw, &Some(Sort::Int))
                    {
                        return EvalValue::Rational(r);
                    }
                }
            }
            if let Some(ref lia_model) = model.lia_model {
                if let Some(val) = lia_model.values.get(&term_id) {
                    return EvalValue::Rational(BigRational::from(val.clone()));
                }
            }
            if let Some(witness) = self.array_extensional_witness_index(model, args[0], args[1]) {
                return witness;
            }
        }
        // An uninterpreted-sort UF application's OWN committed element
        // (`term_values[term_id]`) is authoritative over the arg-keyed function
        // table (#uflia-uninterp-eq-recover). The extracted function table bakes
        // in the element `term_values` held at extraction time, but the model
        // repair `recover_uninterpreted_equalities_from_assertions` may update
        // `term_values[term_id]` AFTERWARD (unifying an app with a var it is
        // asserted equal to — e.g. `a == mk_mut_ref(..)`), leaving the table
        // entry stale. Reading the term's own element first honours the repair.
        // Sound: it is the term's committed interpretation, and validation
        // re-checks every assertion under it.
        if !context_dependent && matches!(sort, Sort::Uninterpreted(_)) {
            if let Some(ref euf_model) = model.euf_model {
                if let Some(elem) = euf_model.term_values.get(&term_id) {
                    return EvalValue::Element(elem.clone());
                }
            }
        }
        // #dt-depth-structural: NEVER read an acyclicity depth application from
        // the arg-keyed UF function table. The table resolves congruent rows
        // through EUF-derived values, while the per-term LIA entries below are
        // the values that actually satisfied the injected depth axioms in the
        // solve — mixing the two sources across the terms of ONE axiom
        // (`(<= (+ (depth (tl y)) 1) (depth (cons (hd y) (tl y)))))` reading
        // one side from the table and the other from LIA) fabricates a
        // violation of an axiom the committed model satisfies. LIA (already
        // documented authoritative for depth terms below) is used instead.
        let is_dt_depth_app = name.starts_with("__ay_dt_depth_");
        // #uflia-own-value-first: an Int/Real-sorted UF application's OWN
        // committed value — the explicit assertion pin (`func_app_const_terms`)
        // or the LIA-merged `term_values` entry — is authoritative over the
        // arg-keyed function-table scan. The table rows key and resolve their
        // atoms through EUF's fabricated per-class completion ints
        // (`int_values`), so a CONGRUENT row (`s_count(fmt1-2) -> @?560` when
        // the model gives `fmt1-2 = 3`) can resolve `(s_count 3)` to a
        // fabricated class int that contradicts the LIA value the solver
        // actually committed — the strict gate then refutes the solver's own
        // consistent model and degrades a genuine sat to unknown (SMT-COMP
        // QF_UFLIA wisas/xs_* family). Reading the term's own committed value
        // first is exactly what `Sort::Uninterpreted` already does above.
        // Sound: validation still re-checks every assertion under the value.
        if !is_dt_depth_app && matches!(sort, Sort::Int | Sort::Real) {
            if let Some(ref euf_model) = model.euf_model {
                if let Some(&const_term_id) = euf_model.func_app_const_terms.get(&term_id) {
                    return self.evaluate_term(model, const_term_id);
                }
                // Speculative (fabricated per-class) values are NOT committed —
                // never treat them as the app's own authoritative value
                // (#uflia-arith-arg-key).
                if !euf_model.speculative_int_terms.contains(&term_id) {
                    if let Some(raw) = euf_model.term_values.get(&term_id) {
                        if let EvalValue::Rational(r) =
                            self.parse_model_value_string(raw, &Some(sort.clone()))
                        {
                            return EvalValue::Rational(r);
                        }
                    }
                }
            }
        }
        if !is_dt_depth_app {
            if let Some(value) =
                self.evaluate_uf_app_from_function_table(model, name, args, sort, term_id)
            {
                return value;
            }
        }
        // Function-table rows are keyed by the recursively evaluated argument
        // values, so the lookup above is valid in a beta environment. Every
        // remaining source is keyed only by this application's TermId (SAT,
        // LIA/LRA/BV/FP, EUF pins, or asserted selector equalities). Reusing
        // one of those ambient commitments for a body application that
        // contains an active binder would conflate distinct beta instances.
        // Binder-independent applications remain eligible for the ordinary
        // fallbacks even while an unrelated binding is active.
        if context_dependent {
            return EvalValue::Unknown;
        }
        // Bool SAT-literal fallback is sound only for true UF predicates.
        // For known theory predicates (e.g., str.contains, str.in_re),
        // taking the SAT literal would bypass semantic validation.
        if matches!(sort, Sort::Bool) && !Self::is_known_theory_symbol(name) {
            if let Some(b) = self.term_value(&model.sat_model, &model.term_to_var, term_id) {
                return EvalValue::Bool(b);
            }
        }
        // For non-Bool applications, consult models by term ID.
        // For user-visible UF/selector apps (#5432), check EUF
        // func_app_const_terms first—it tracks explicit
        // `(= (sel x) const)` assertions and is authoritative.
        // The LIA model may have stale default values for terms
        // introduced via assert_shared_equality.
        // For solver-internal depth terms (`__ay_dt_depth_*`),
        // LIA is authoritative since it computes actual depth values.
        let is_depth_term = name.starts_with("__ay_dt_depth_");
        match sort {
            Sort::Int => {
                // For non-depth terms, EUF func_app_const_terms
                // is authoritative (#5432).
                if !is_depth_term {
                    if let Some(ref euf_model) = model.euf_model {
                        if let Some(&const_term_id) = euf_model.func_app_const_terms.get(&term_id) {
                            return self.evaluate_term(model, const_term_id);
                        }
                        if let Some(raw) = euf_model.term_values.get(&term_id) {
                            if let EvalValue::Rational(r) =
                                self.parse_model_value_string(raw, &Some(Sort::Int))
                            {
                                return EvalValue::Rational(r);
                            }
                        }
                    }
                }
                // LIA/LRA: authoritative for depth terms,
                // fallback for non-depth terms.
                if let Some(ref lia_model) = model.lia_model {
                    if let Some(val) = lia_model.values.get(&term_id) {
                        return EvalValue::Rational(BigRational::from(val.clone()));
                    }
                }
                if let Some(ref lra_model) = model.lra_model {
                    if let Some(val) = lra_model.values.get(&term_id) {
                        return EvalValue::Rational(val.clone());
                    }
                }
                // For depth terms, also check EUF after LIA misses.
                if is_depth_term {
                    if let Some(ref euf_model) = model.euf_model {
                        if let Some(&const_term_id) = euf_model.func_app_const_terms.get(&term_id) {
                            return self.evaluate_term(model, const_term_id);
                        }
                    }
                }
                if model.lia_model.is_some() || model.lra_model.is_some() {
                    return EvalValue::Unknown;
                }
                if let Some(ref euf_model) = model.euf_model {
                    if let Some(val) = euf_model.int_values.get(&term_id) {
                        return EvalValue::Rational(BigRational::from(val.clone()));
                    }
                }
            }
            Sort::Real => {
                // For non-depth terms, EUF is authoritative (#5432).
                if !is_depth_term {
                    if let Some(ref euf_model) = model.euf_model {
                        if let Some(&const_term_id) = euf_model.func_app_const_terms.get(&term_id) {
                            return self.evaluate_term(model, const_term_id);
                        }
                        if let Some(raw) = euf_model.term_values.get(&term_id) {
                            if let EvalValue::Rational(r) =
                                self.parse_model_value_string(raw, &Some(Sort::Real))
                            {
                                return EvalValue::Rational(r);
                            }
                        }
                    }
                }
                if let Some(ref lra_model) = model.lra_model {
                    if let Some(val) = lra_model.values.get(&term_id) {
                        return EvalValue::Rational(val.clone());
                    }
                }
                if model.lra_model.is_some() {
                    return EvalValue::Unknown;
                }
            }
            Sort::BitVec(bv) => {
                if let Some(ref bv_model) = model.bv_model {
                    if let Some(val) = bv_model.values.get(&term_id) {
                        return EvalValue::BitVec {
                            value: val.clone(),
                            width: bv.width,
                        };
                    }
                    // UF congruence fallback (#5461): if f(y) is not
                    // in the BV model (wasn't in assertions), find a
                    // congruent application f(x) whose arguments
                    // evaluate to the same values.
                    if let Some(val) =
                        self.find_congruent_bv_app(model, bv_model, name, args, term_id)
                    {
                        return EvalValue::BitVec {
                            value: val,
                            width: bv.width,
                        };
                    }
                }
                if let Some(ref euf_model) = model.euf_model {
                    if let Some(raw) = euf_model.term_values.get(&term_id) {
                        if let EvalValue::BitVec { value, width } =
                            self.parse_model_value_string(raw, &Some(Sort::BitVec(bv.clone())))
                        {
                            return EvalValue::BitVec { value, width };
                        }
                    }
                }
                // Congruence fallback already handled by
                // find_congruent_bv_app above (#5461).
                if model.bv_model.is_some() {
                    return EvalValue::Unknown;
                }
            }
            Sort::FloatingPoint(..) => {
                // FP-sorted unrecognized application: check FP model
                if let Some(ref fp_model) = model.fp_model {
                    if let Some(val) = fp_model.values.get(&term_id) {
                        return EvalValue::Fp(val.clone());
                    }
                }
            }
            _ => {}
        }
        // Then try EUF model
        if let Some(ref euf_model) = model.euf_model {
            if let Some(elem) = euf_model.term_values.get(&term_id) {
                return EvalValue::Element(elem.clone());
            }
            // Check for function application constant values (#385)
            // For UF applications returning Int/Real/BV, we may have recorded
            // the constant term from assertions like (= (f x) 100)
            if let Some(&const_term_id) = euf_model.func_app_const_terms.get(&term_id) {
                return self.evaluate_term(model, const_term_id);
            }
        }
        // For unrecognized Bool predicates, return Unknown instead of
        // defaulting to false, as they may be theory predicates we
        // can't evaluate without model values.
        if matches!(sort, Sort::Bool) {
            return EvalValue::Unknown;
        }
        // Final fallback: resolve from assertion equalities.
        // In QF_DT, selector values are only constrained by
        // assertions like (= (ival x) 42) with no theory model.
        // Only extract from constant terms to avoid recursion (#5432).
        // Restrict to DT-internal symbols (selectors) to prevent
        // circular self-validation of non-DT apps (#5494).
        if !self.is_dt_internal_symbol(name) {
            return EvalValue::Unknown;
        }
        // Resolve `(sel var)` through an asserted equality
        // `(= var (Ctor ... field ...))` by plucking the constructor argument
        // at the selector's field position. This is the indirect case that the
        // direct `(= (sel x) const)` scan below does not cover (#5450).
        if let Some(val) = self.eval_selector_via_constructor(model, name, args) {
            return val;
        }
        for &assertion in &self.ctx.assertions {
            if let TermData::App(eq_sym, eq_args) = self.ctx.terms.get(assertion) {
                if eq_sym.name() == "=" && eq_args.len() == 2 {
                    // Check this assertion is true in the SAT model (#5497).
                    let eq_true = self
                        .term_value(&model.sat_model, &model.term_to_var, assertion)
                        .unwrap_or(false);
                    if !eq_true {
                        continue;
                    }
                    let other = if eq_args[0] == term_id {
                        Some(eq_args[1])
                    } else if eq_args[1] == term_id {
                        Some(eq_args[0])
                    } else {
                        None
                    };
                    if let Some(other_term) = other {
                        if matches!(self.ctx.terms.get(other_term), TermData::Const(_)) {
                            return self.evaluate_term(model, other_term);
                        }
                    }
                }
            }
        }
        EvalValue::Unknown
    }

    /// Resolve an Unknown equality between two applications of the SAME
    /// uninterpreted function whose arguments pairwise evaluate to equal
    /// known values (#uflia-orphaned-congruence).
    ///
    /// TRUE-direction only: `f(v) = f(v)` holds by congruence in EVERY model,
    /// including one where `f` has no committed interpretation at all —
    /// preprocessing can substitute a forced equality away (e.g. `x = y`
    /// rewrites `(f x) = (f y)` to a tautology), leaving both ORPHANED apps
    /// with no function-table row, no `int_values`/`term_values` entry, and no
    /// pinned constant, so each evaluates Unknown and the ground validator
    /// degraded a genuine sat to unknown. Unequal argument values return
    /// `None` (NOT false): a non-injective function may still identify them.
    /// This never weakens the gate — it only derives what the congruence
    /// axiom forces, from committed argument values.
    pub(super) fn eq_via_uf_congruence(
        &self,
        model: &Model,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<EvalValue> {
        let (TermData::App(sym_l, args_l), TermData::App(sym_r, args_r)) =
            (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs))
        else {
            return None;
        };
        if sym_l.name() != sym_r.name() || args_l.len() != args_r.len() || args_l.is_empty() {
            return None;
        }
        // Restrict to true uninterpreted symbols: theory symbols with known
        // argument values evaluate directly; keep this path narrow.
        if Self::is_known_theory_symbol(sym_l.name()) {
            return None;
        }
        for (&arg_l, &arg_r) in args_l.iter().zip(args_r.iter()) {
            if arg_l == arg_r {
                // Syntactically identical argument: equal in every model,
                // even when its value is not independently evaluable.
                continue;
            }
            let val_l = self.evaluate_term(model, arg_l);
            if matches!(val_l, EvalValue::Unknown) {
                return None;
            }
            let val_r = self.evaluate_term(model, arg_r);
            if matches!(val_r, EvalValue::Unknown) {
                return None;
            }
            if !matches!(Self::eval_values_equal_exact(&val_l, &val_r), Some(true)) {
                return None;
            }
        }
        Some(EvalValue::Bool(true))
    }

    /// Find a congruent BV UF application in the BV model (#5461).
    ///
    /// When `f(y)` is not in `bv_model.values` (because it only appeared in
    /// `get-value`, not in assertions), search for another application
    /// `f(x)` of the same function where all arguments evaluate to the same
    /// BV values. Returns the BV value of the congruent application.
    pub(super) fn find_congruent_bv_app(
        &self,
        model: &Model,
        bv_model: &BvModel,
        func_name: &str,
        target_args: &[TermId],
        target_term_id: TermId,
    ) -> Option<BigInt> {
        // Evaluate the target arguments to get their model values.
        let target_arg_vals: Vec<EvalValue> = target_args
            .iter()
            .map(|&a| self.evaluate_term(model, a))
            .collect();
        // If any argument is Unknown, we cannot determine congruence.
        if target_arg_vals
            .iter()
            .any(|v| matches!(v, EvalValue::Unknown))
        {
            return None;
        }

        // Search BV model entries for a congruent application.
        for (&candidate_tid, candidate_val) in &bv_model.values {
            if candidate_tid == target_term_id {
                continue;
            }
            // A BV model entry is an ambient TermId-keyed result.  Even when
            // its arguments happen to evaluate to the target values after
            // contextual substitution, the stored result belongs to the
            // ambient application point, not this beta instance.
            if super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, candidate_tid) {
                continue;
            }
            if let TermData::App(sym, cand_args) = self.ctx.terms.get(candidate_tid) {
                if sym.name() != func_name || cand_args.len() != target_args.len() {
                    continue;
                }
                // Check if all arguments evaluate to the same values.
                let args_match =
                    cand_args
                        .iter()
                        .zip(target_arg_vals.iter())
                        .all(|(&cand_arg, target_val)| {
                            let cand_val = self.evaluate_term(model, cand_arg);
                            matches!(
                                Self::eval_values_equal_exact(&cand_val, target_val),
                                Some(true)
                            )
                        });
                if args_match {
                    return Some(candidate_val.clone());
                }
            }
        }
        None
    }
}
