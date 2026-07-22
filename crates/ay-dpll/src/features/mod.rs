// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Static feature analysis for SMT formulas.
//!
//! This module provides automatic logic detection when `set-logic` is not specified.
//! It analyzes formula features (sorts, symbols, quantifiers) to infer the
//! appropriate logic for solving.
//!
//! Based on Z3's approach: `reference/z3/src/ast/static_features.cpp`

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{
    term::{Symbol, TermData},
    Sort, TermId, TermStore,
};

/// Static features detected from a formula.
///
/// These features determine which theories are needed to solve the formula,
/// enabling automatic logic detection when `set-logic` is not specified.
#[derive(Default, Debug, Clone)]
pub(crate) struct StaticFeatures {
    /// Formula contains Int-sorted terms
    pub has_int: bool,
    /// Formula contains *genuine* Int-sort evidence — an Int-sorted variable,
    /// an Int-sorted uninterpreted-function application/declared symbol, or an
    /// integer-introducing operator (`div`/`mod`/`rem`/`to_int`).
    ///
    /// `has_int` is set by ANY Int-sorted subterm, including bare numerals
    /// (`Const(Int(n))`) and arithmetic/`ite` terms whose Int sort derives only
    /// from numerals. Per SMT-LIB, numerals in a Real context denote Reals
    /// (QF_LRA has NO Int sort), so a numeral being typed `Int` by local
    /// elaboration is NOT evidence that the formula needs integer reasoning.
    ///
    /// `has_int_var` excludes that numeral noise: it is true only when the
    /// formula genuinely mentions the Int sort via a variable, UF, or
    /// integer-only operator. Logic-family alignment uses this (not `has_int`)
    /// to decide whether to promote a Real-family declared logic to a mixed
    /// `*LIRA` variant, so a declared QF_LRA carrying only integer LITERALS
    /// stays QF_LRA and is solved soundly by the LRA solver (#qf-lra-lit-misroute).
    pub has_int_var: bool,
    /// Formula contains Real-sorted terms
    pub has_real: bool,
    /// Formula contains BitVec-sorted terms
    pub has_bv: bool,
    /// Formula contains Array-sorted terms
    pub has_arrays: bool,
    /// Formula contains String-sorted terms
    pub has_strings: bool,
    /// Formula contains generic Seq-sorted terms (not String)
    pub has_seq: bool,
    /// Formula contains native SMT-LIB `seq.*` operators.
    ///
    /// A Seq sort by itself can be treated as an uninterpreted carrier sort.
    /// Native sequence operators require the sequence theory solver.
    pub has_seq_ops: bool,
    /// Formula contains native SMT-LIB finite-set operators that need the set
    /// theory solver: `set.card` / `set.subset` (opaque, axiom-injected) or any
    /// out-of-fragment combinator (`set.union`/`set.inter`/`set.minus`/…).
    ///
    /// Membership and the array-decidable constructors (`set.member`,
    /// `set.insert`, `set.remove`, `set.singleton`, `set.empty`) are reduced to
    /// `select`/`store` during elaboration and need no set solver — they are
    /// decided soundly by the array theory. Only `set.card`/`set.subset`/the
    /// combinators survive as set-specific symbols, and they MUST route to the
    /// set theory so the ground card axioms are injected (otherwise `set.card`
    /// would be an unconstrained opaque UF → unsound).
    pub has_set_ops: bool,
    /// Formula contains native SMT-LIB multiset operators that need the multiset
    /// theory solver: `multiset.count` / `multiset.subset` (count + subset over
    /// the `Multiset(T) = Array(T → Int)` count carrier) or any out-of-fragment
    /// combinator (`multiset.union`/`multiset.inter`/`multiset.diff`/…).
    ///
    /// The array-decidable constructors (`multiset.insert`, `multiset.remove`,
    /// `multiset.singleton`, `multiset.empty`) are reduced to `select`/`store`
    /// during elaboration and need no multiset solver — they are decided soundly
    /// by the array theory. `multiset.count`/`multiset.subset`/the combinators
    /// survive as multiset-specific symbols and MUST route to the multiset
    /// theory so the ground count axioms (`count >= 0`, subset↔count) are
    /// injected (otherwise `multiset.subset` would degrade to opaque UF).
    pub has_multiset_ops: bool,
    /// Formula contains native SMT-LIB finite-map operators that need the map
    /// theory solver: the surviving constructors `map.insert` / `map.remove`,
    /// the domain projection `map.dom`, the submap predicate `map.subset`, or
    /// any out-of-fragment image op (`map.values`/`map.fold`/…) over the
    /// `Map(K, V) = Array(K → V)` value carrier (+ `Array(K → Bool)` domain).
    ///
    /// The readers `map.get`/`map.contains_key`/`map.empty` are reduced to
    /// `ite`/`select`/`store`/const-array during elaboration and need no map
    /// solver — they are decided soundly by the array theory. The surviving
    /// `map.*` symbols MUST route to the map theory so the ground subset↔key
    /// obligations are injected (otherwise `map.subset` would degrade to opaque
    /// UF) and out-of-fragment ops fail closed.
    pub has_map_ops: bool,
    /// Formula contains RegLan-sorted terms or regex operators
    pub has_regex: bool,
    /// Formula contains FloatingPoint-sorted terms
    pub has_fpa: bool,
    /// Formula contains uninterpreted functions (arity > 0)
    pub has_uf: bool,
    /// Formula contains quantifiers (forall/exists)
    pub has_quantifiers: bool,
    /// Formula contains non-linear Int arithmetic (* with ≥2 non-constant Int args)
    pub has_nonlinear_int: bool,
    /// Formula contains non-linear Real arithmetic (* with ≥2 non-constant Real args)
    pub has_nonlinear_real: bool,
    /// Formula contains BV↔Int conversion functions (bv2nat, int2bv)
    pub has_bv_int_conversion: bool,
    /// Formula contains integer div/mod operations.
    /// These prevent CEGQI bound extraction from converging (#6889).
    pub has_int_div_mod: bool,
    /// Formula contains an `is_int` predicate over a Real-sorted argument.
    ///
    /// `is_int(r)` constrains the integrality of a real expression. Pure-LRA
    /// routing cannot decide it (LRA reasons over the rationals and ignores
    /// integrality). The NRA solver carries an exact univariate decision
    /// procedure that CAN decide `is_int` over an affine/univariate real
    /// expression (find a rational witness making it an integer in the feasible
    /// region), so `is_int`-bearing QF_LRA/QF_NRA problems are routed to the NRA
    /// solver instead of pure LRA.
    pub has_is_int_real: bool,
    /// Number of non-UF theories used
    pub num_theories: usize,
}

impl StaticFeatures {
    /// Collect features from a set of terms.
    ///
    /// Walks all terms reachable from `root_ids` and detects which theories
    /// are required based on sorts and operations used.
    pub(crate) fn collect(terms: &TermStore, root_ids: &[TermId]) -> Self {
        let mut features = Self::default();
        let mut visited = HashSet::default();

        for &id in root_ids {
            features.collect_term(terms, id, &mut visited);
        }

        // Count non-UF theories
        features.num_theories = [
            features.has_int,
            features.has_real,
            features.has_bv,
            features.has_arrays,
            features.has_strings,
            features.has_seq_ops,
            features.has_fpa,
        ]
        .iter()
        .filter(|&&x| x)
        .count();

        features
    }

    /// Extend feature detection with declared function/constant symbols (#7442).
    ///
    /// `StaticFeatures::collect` walks only assertion term trees. When a consumer
    /// declares UF functions or array-sorted constants via `declare-fun` /
    /// `declare-const` but the assertion tree happens not to contain those terms
    /// (e.g., after push/pop), `collect` misses the UF/array requirement. This
    /// causes `narrow_linear_combo_with_features` to incorrectly strip UF/array
    /// support (e.g., AUFLIA → LIA), breaking formulas that need those theories.
    ///
    /// This method scans declared symbol sorts to ensure the features reflect
    /// all theories that the consumer has declared, not just those visible in
    /// the current assertion tree.
    pub(crate) fn extend_with_declarations<'a>(
        &mut self,
        symbols: impl Iterator<Item = (&'a str, &'a [Sort], &'a Sort)>,
    ) {
        for (name, arg_sorts, ret_sort) in symbols {
            // Non-builtin symbols with arguments are UF
            if !arg_sorts.is_empty() && !is_builtin_symbol_name(name) {
                self.has_uf = true;
            }
            // Check return sort and argument sorts for theory features
            self.detect_sort_theory(ret_sort);
            for sort in arg_sorts {
                self.detect_sort_theory(sort);
            }
            // A declared symbol whose signature mentions the Int sort is genuine
            // Int-sort evidence (a real Int variable/function), as opposed to a
            // numeral that local elaboration typed Int. This keeps a genuinely
            // mixed declared logic (e.g. QF_LIRA with `(declare-fun i () Int)`
            // and `(declare-fun r () Real)`) routing to the mixed solver while a
            // Real-only declared logic that merely carries integer literals does
            // not (#qf-lra-lit-misroute).
            if Self::sort_mentions_int(ret_sort) || arg_sorts.iter().any(Self::sort_mentions_int) {
                self.has_int_var = true;
            }
        }
        // Recount theories after extension
        self.num_theories = [
            self.has_int,
            self.has_real,
            self.has_bv,
            self.has_arrays,
            self.has_strings,
            self.has_seq_ops,
            self.has_fpa,
        ]
        .iter()
        .filter(|&&x| x)
        .count();
    }

    fn collect_term(&mut self, terms: &TermStore, id: TermId, visited: &mut HashSet<TermId>) {
        if !visited.insert(id) {
            return;
        }

        // Check sort - detect which theory is needed
        let term_sort = terms.sort(id);
        self.detect_sort_theory(term_sort);

        // Check term structure for UF/quantifiers
        match terms.get(id) {
            TermData::App(sym, args) => {
                // Check for UF (uninterpreted function applications).
                // Nullary UF applications (declare-fun f () Int) are App nodes with
                // empty args — they must also set has_uf to prevent incorrect logic
                // narrowing (e.g., AUFLIA → LIA) which strips UF support (#6498).
                if !is_builtin_symbol(sym) {
                    self.has_uf = true;
                    // A non-builtin (UF) application whose RESULT sort is Int is
                    // genuine Int-sort evidence: it is a declared symbol with an
                    // Int range, not a numeral that local elaboration happened to
                    // type Int. (Int-sorted UF *arguments* are detected when those
                    // argument terms are walked — a numeral passed to a UF stays a
                    // numeral and must not count.)
                    if matches!(term_sort, Sort::Int) {
                        self.has_int_var = true;
                    }
                }

                let name = sym.name();
                if name == "bv2nat" || name == "int2bv" {
                    self.has_bv_int_conversion = true;
                }
                // `is_int(r)` over a Real argument needs the NRA exact univariate
                // decider (LRA ignores integrality). Detect it so the dispatcher
                // can route to the NRA solver instead of pure LRA (#9139).
                if name == "is_int" && args.len() == 1 && matches!(terms.sort(args[0]), Sort::Real)
                {
                    self.has_is_int_real = true;
                }
                if is_regex_symbol_name(name) {
                    self.has_regex = true;
                    // Regex belongs to the SMT-LIB strings family.
                    self.has_strings = true;
                }
                if is_seq_symbol_name(name) {
                    self.has_seq_ops = true;
                    self.has_seq = true;
                }
                if is_set_solver_symbol_name(name) {
                    self.has_set_ops = true;
                }
                if is_multiset_solver_symbol_name(name) {
                    self.has_multiset_ops = true;
                }
                if is_map_solver_symbol_name(name) {
                    self.has_map_ops = true;
                }

                // Detect non-linear arithmetic:
                // - Multiplication: * with ≥2 non-constant arguments
                // - Real division: / with non-constant divisor (see below)
                if name == "*" && args.len() >= 2 {
                    let non_const_count = args
                        .iter()
                        .filter(|&&arg| !matches!(terms.get(arg), TermData::Const(_)))
                        .count();
                    if non_const_count >= 2 {
                        // Result sort determines Int vs Real non-linearity
                        match term_sort {
                            Sort::Int => self.has_nonlinear_int = true,
                            Sort::Real => self.has_nonlinear_real = true,
                            _ => {}
                        }
                    }
                }
                // Integer div/mod/rem: these create opaque auxiliary variables
                // in LIA preprocessing that prevent CEGQI bound extraction
                // from converging (#6889). Detected separately from nonlinear
                // so CEGQI can bail early without upgrading the logic.
                //
                // `rem` MUST be included (#nia-symbolic-rem-bypass): without it a
                // `rem`-only formula satisfies `has_only_uf_lia_theories` and
                // takes the UF/LIA fast path, which treats a symbolic `(rem x y)`
                // as an UNINTERPRETED function (freely assigned) — a wrong-SAT
                // (e.g. `y>0 ∧ (rem x y) >= y` returned sat). Flagging it routes
                // `rem` through the div/mod-aware pipeline, where `mod_div_elim`
                // lowers it to `mod`/`ite` and it is solved on the NIA path or
                // soundly degraded to `unknown` on the LIA path, exactly like
                // `mod`.
                if (name == "div" || name == "mod" || name == "rem")
                    && matches!(term_sort, Sort::Int)
                {
                    self.has_int_div_mod = true;
                }
                // Int-*introducing* builtin operators are genuine Int-sort
                // evidence (#qf-lra-lit-misroute): they produce a value whose
                // INTEGRALITY must be reasoned about, not a numeral that local
                // elaboration happened to type Int.
                //   - `div`/`mod`/`rem`: Int-only operators (not in the Real
                //     signature) → require integer reasoning.
                //   - `to_int(r)`: the Real→Int floor → its Int result is a
                //     genuine integer constraint that needs the LIRA solver
                //     (pure LRA ignores integrality and returns unknown here).
                // Unlike `+`/`-`/`*`/`ite`, whose Int sort can derive purely from
                // numeral operands, these operators introduce genuine integers
                // even when applied to numerals/reals, so they flip `has_int_var`.
                if matches!(name, "div" | "mod" | "rem" | "to_int")
                    && matches!(term_sort, Sort::Int)
                {
                    self.has_int_var = true;
                }
                // Real division "/" by a non-constant IS genuinely nonlinear
                // (x/y = x * (1/y)), so detect it for NRA routing.
                // Integer "div"/"mod" are excluded — they create opaque terms
                // that LIA treats as fresh variables. Detecting them upgrades
                // QF_AUFLIA → QF_UFNIA which returns Unknown immediately (#6165).
                if name == "/"
                    && args.len() >= 2
                    && !matches!(terms.get(args[1]), TermData::Const(_))
                {
                    match term_sort {
                        Sort::Int => self.has_nonlinear_int = true,
                        Sort::Real => self.has_nonlinear_real = true,
                        _ => {}
                    }
                }

                // Recurse into children
                for &child in args {
                    self.collect_term(terms, child, visited);
                }
            }
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                self.has_quantifiers = true;
                // Check variable sorts
                for (_name, sort) in vars {
                    self.detect_sort_theory(sort);
                }
                self.collect_term(terms, *body, visited);
            }
            TermData::Not(inner) => {
                self.collect_term(terms, *inner, visited);
            }
            TermData::Ite(cond, then_term, else_term) => {
                self.collect_term(terms, *cond, visited);
                self.collect_term(terms, *then_term, visited);
                self.collect_term(terms, *else_term, visited);
            }
            TermData::Let(bindings, body) => {
                for (_name, term) in bindings {
                    self.collect_term(terms, *term, visited);
                }
                self.collect_term(terms, *body, visited);
            }
            TermData::Var(_, _) => {
                // An Int-sorted *variable* is genuine Int-sort evidence: it is a
                // declared/bound symbol of Int sort, not a numeral. (A bare
                // numeral is `Const(Int(_))`, handled below, and is NOT genuine
                // Int evidence — in a Real context it denotes a Real.)
                if matches!(term_sort, Sort::Int) {
                    self.has_int_var = true;
                }
            }
            TermData::Const(_) => {
                // No children to recurse into. A `Const(Int(_))` numeral is
                // intentionally NOT counted as genuine Int evidence (#qf-lra-lit-misroute).
            }
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TermData variant in collect_term(): {other:?}"),
        }
    }

    /// Whether `sort` mentions the Int sort anywhere (directly, or as an array
    /// index/element or sequence element). Used to flag genuine Int-sort
    /// evidence from a declared symbol's signature (#qf-lra-lit-misroute).
    fn sort_mentions_int(sort: &Sort) -> bool {
        match sort {
            Sort::Int => true,
            Sort::Array(arr) => {
                Self::sort_mentions_int(&arr.index_sort)
                    || Self::sort_mentions_int(&arr.element_sort)
            }
            Sort::Seq(elem) => Self::sort_mentions_int(elem),
            _ => false,
        }
    }

    fn detect_sort_theory(&mut self, sort: &Sort) {
        match sort {
            Sort::Int => self.has_int = true,
            Sort::Real => self.has_real = true,
            Sort::BitVec(_) => self.has_bv = true,
            Sort::Array(arr) => {
                self.has_arrays = true;
                // Recurse into array index/element sorts
                self.detect_sort_theory(&arr.index_sort);
                self.detect_sort_theory(&arr.element_sort);
            }
            Sort::String => self.has_strings = true,
            Sort::RegLan => {
                self.has_regex = true;
                self.has_strings = true;
            }
            Sort::FloatingPoint(_, _) => self.has_fpa = true,
            Sort::Seq(elem) => {
                // Generic sequence sort — distinct from String theory
                self.has_seq = true;
                // Without native `seq.*` operations, a Seq sort is just an
                // equality/UF carrier. Keep EUF enabled so Seq-sorted UF
                // proxies do not narrow to pure arithmetic (#9227).
                self.has_uf = true;
                self.detect_sort_theory(elem);
            }
            Sort::Uninterpreted(_) => {
                // Equality over uninterpreted-sort terms still needs EUF routing.
                // Without this, mixed Int + uninterpreted-sort equality windows
                // can be narrowed to pure LIA and lose congruence reasoning.
                self.has_uf = true;
            }
            Sort::Datatype(_) | Sort::Bool => {
                // Datatypes are routed through declaration context; Bool alone is propositional.
            }
            // All current Sort variants handled above (#5692).
            other => unreachable!("unhandled Sort variant in detect_sort_theory(): {other:?}"),
        }
    }
}

mod logic_inference;

/// Built-in SMT-LIB operator names that should NOT trigger `has_uf`.
const BUILTIN_SYMBOLS: &[&str] = &[
    // Boolean
    "and",
    "or",
    "not",
    "xor",
    "=>",
    "ite",
    "=",
    "distinct",
    // Arithmetic + conversions
    "+",
    "-",
    "*",
    "/",
    "div",
    "mod",
    "abs",
    "<",
    "<=",
    ">",
    ">=",
    "to_real",
    "to_int",
    "is_int",
    // Bitvectors
    "bvadd",
    "bvsub",
    "bvmul",
    "bvudiv",
    "bvsdiv",
    "bvurem",
    "bvsrem",
    "bvneg",
    "bvand",
    "bvor",
    "bvxor",
    "bvnot",
    "bvshl",
    "bvlshr",
    "bvashr",
    "bvult",
    "bvule",
    "bvugt",
    "bvuge",
    "bvslt",
    "bvsle",
    "bvsgt",
    "bvsge",
    "concat",
    "extract",
    "repeat",
    "zero_extend",
    "sign_extend",
    "rotate_left",
    "rotate_right",
    "bvcomp",
    "bv2nat",
    "int2bv",
    // Arrays
    "select",
    "store",
    "const-array",
    "default",
    // Sequences (#7442: prevent misclassification as UF)
    "seq.len",
    "seq.unit",
    "seq.empty",
    "seq.++",
    "seq.nth",
    "seq.contains",
    "seq.extract",
    "seq.prefixof",
    "seq.suffixof",
    "seq.indexof",
    "seq.last_indexof",
    "seq.replace",
    // Strings
    "str.++",
    "str.len",
    "str.at",
    "str.substr",
    "str.contains",
    "str.prefixof",
    "str.suffixof",
    "str.indexof",
    "str.replace",
    "str.replace_all",
    "str.replace_re",
    "str.replace_re_all",
    "str.to_int",
    "str.to.int",
    "int.to.str",
    "str.from_int",
    "str.to_code",
    "str.from_code",
    "str.to_lower",
    "str.to_upper",
    "str.is_digit",
    "str.<",
    "str.<=",
];

/// Check if a symbol is a built-in SMT-LIB operator.
fn is_builtin_symbol(sym: &Symbol) -> bool {
    is_builtin_symbol_name(sym.name())
}

/// Check if a symbol name is a built-in SMT-LIB operator (#7442).
pub(crate) fn is_builtin_symbol_name(name: &str) -> bool {
    is_regex_symbol_name(name)
        || is_seq_symbol_name(name)
        || is_set_solver_symbol_name(name)
        || is_multiset_solver_symbol_name(name)
        || is_map_solver_symbol_name(name)
        || BUILTIN_SYMBOLS.contains(&name)
        // as-array[f] and map[f] are array theory builtins, not UF applications
        || name.starts_with("as-array[")
        || name.starts_with("map[")
}

fn is_seq_symbol_name(name: &str) -> bool {
    name.starts_with("seq.")
}

/// Set-theory symbols that survive elaboration and require the set solver.
///
/// `set.member`/`set.insert`/`set.remove`/`set.singleton`/`set.empty` are
/// reduced to `select`/`store` and never appear as named apps. Only the
/// cardinality/subset symbols and the (currently fail-closed) combinators reach
/// the feature scanner, so detecting `set.` covers exactly those.
fn is_set_solver_symbol_name(name: &str) -> bool {
    name.starts_with("set.")
}

/// Multiset-theory symbols that survive elaboration and require the multiset
/// solver.
///
/// `multiset.insert`/`multiset.remove`/`multiset.singleton`/`multiset.empty`
/// are reduced to `select`/`store` and never appear as named apps. Only the
/// count/subset symbols and the (currently fail-closed) combinators reach the
/// feature scanner, so detecting `multiset.` covers exactly those.
fn is_multiset_solver_symbol_name(name: &str) -> bool {
    name.starts_with("multiset.")
}

/// Map-theory symbols that survive elaboration and require the map solver.
///
/// `map.get`/`map.contains_key`/`map.empty` are reduced to `ite`/`select`/
/// `store`/const-array and never appear as named apps. Only the surviving
/// constructors (`map.insert`/`map.remove`), the domain projection (`map.dom`),
/// the submap predicate (`map.subset`), and the (fail-closed) image ops reach
/// the feature scanner, so detecting `map.` covers exactly those.
fn is_map_solver_symbol_name(name: &str) -> bool {
    name.starts_with("map.")
}

fn is_regex_symbol_name(name: &str) -> bool {
    matches!(
        name,
        "str.to_re"
            | "str.to.re"
            | "str.in_re"
            | "str.in.re"
            | "re.++"
            | "re.union"
            | "re.inter"
            | "re.*"
            | "re.+"
            | "re.opt"
            | "re.range"
            | "re.comp"
            | "re.diff"
            | "re.none"
            | "re.all"
            | "re.allchar"
    )
}

#[cfg(test)]
mod tests;
