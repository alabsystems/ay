// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================================
// Benchmark corpus row classification: the exact, bidirectional lists; the
// independent Z3 oracle that confirms every row no Carcara `valid` covers is
// `corpus_oracle.rs`
// ============================================================================

/// Files whose names contain `false_unsat` (plus the historical Hamiltonian
/// canary) are SAT regression inputs, not UNSAT proof obligations.  They were
/// previously counted as generic "skips", which blurred the denominator of
/// the external-proof gate.  Every row is checked against Z3 below.
const ORACLE_SAT_CORPUS_ROWS: &[&str] = &[
    "QF_LIA_false_unsat_20var_bb",
    "QF_LIA_false_unsat_disjunction_6205",
    "QF_LIA_false_unsat_implication_6206",
    "QF_LIA_false_unsat_step2_6207",
    "QF_LIA_mini_hamiltonian_unsat",
    "regression_false_unsat_cegqi_entailed_inner_forall",
    "regression_false_unsat_cegqi_entailed_inner_forall_nnf",
    "regression_false_unsat_cegqi_entailed_inner_forall_or_not",
    "regression_false_unsat_cegqi_entailed_inner_forall_witness",
];

/// Independently oracle-confirmed UNSAT rows whose exact proof surfaces are
/// not yet supported.  These are NOT counted as proof parity.  The gate below
/// requires AY to return fail-closed `unknown` for every one; SAT, timeout,
/// execution failure, or an unchecked proof is a hard failure.
const ORACLE_UNSAT_UNSUPPORTED_ROWS: &[&str] = &[
    // Retired 2026-09-26: `QF_LIA_ring_2exp16_5vars_cascade_unsat`. Its
    // 43-literal LIA lemma (t161) is satisfiable over ℚ and refuted only by a
    // chain of Chvátal-Gomory cuts; it is now `IntCgCutChain`, re-derived and
    // re-validated by the strict checker and printed as one `la_generic` per
    // cut plus resolution (`proof_validation::lia_cut_chain`,
    // `alethe_printer/equality_lattice/cut_chain.rs`); Carcara `valid` at
    // standard, strict and certified rigor (`cut_chain_strict.rs`).
    // `cascade_v2` left this list for `ORACLE_UNSAT_EXPORT_REFUSED_ROWS`: its
    // `mod` purification is now the strictly checked `divmod_def`.
    // The differential gate's uf-arith g6_100167 left this list for
    // `ORACLE_UNSAT_EXPORT_REFUSED_ROWS`, as `cascade_v2` did.
    // The unsat twin (divisor requirement y! = 1) of the Verus zero-divisor
    // query added by 298870e37. AY answers `unsat` without proofs, but its
    // refutation rests on the `div`/`mod` purification definition, an
    // unverified `trust` step (as for `cascade_v2` and g6 above), so under
    // `:produce-proofs` strict certification withholds it (`unknown`).
    // z3 4.12.5 (file header) and 4.8.12 (with the z3-specific `set-option`
    // lines removed): unsat.
    "wrong-verdict_unsat_verus_zero_divisor_after_int_const_subst_twin",
    // MODEL_CHECKER_CONSUMER model-checking controls added 2026-09-13/14 (checked against Z3
    // only; proof mode was off when they were written). AY has never certified
    // any of them: its refutation ends in an unchecked whole-problem `hole` or
    // `trust` step or a `Generic` FP lemma (the FP row), so the strict gate
    // withholds it. The five `uf_*` controls and `total_projection` left this
    // list when the instance-seeded authored equality closure
    // (`authored_equality_closure/ground_instances.rs`) began re-deriving
    // them: the `uf_*` rows verify, `total_projection` is holey below.
    // `test_carcara_model_checker_consumer_unsupported_rows_fail_closed` runs exactly these
    // and also pins that AY still decides each one UNSAT without proofs, or,
    // for its `QUARANTINED_MODEL_CHECKER_CONSUMER_ROWS`, that the nested-array quarantine is
    // what withholds that plain UNSAT.
    //
    // Retired 2026-09-29: `..._nested_array_residual_pbterm_same_key_unsat`,
    // `..._store_miss_residual_inner_miss_conflict_unsat`,
    // `..._store_miss_residual_newest_store_hit_unsat`,
    // `..._quantified_counterexample_wide_key136_premise_false_unsat` and
    // `..._quantified_counterexample_branching_vec_query_false_unsat`, each
    // refuted over its authored roots by ground congruence closure with
    // read-over-write (`arrays_idx`/`arrays_row`), closed bit-vector
    // evaluation, instances of authored universals and, for the record row,
    // the field-wise twins of record-constant equalities
    // (`executor/proof/authored_ground_closure.rs`) projected through the
    // parsed-equal `and_pos` conjunct (b4933f3b3); Carcara `valid` with no
    // allowance (`ground_closure.rs`).
    //
    // WHY THE REST STAY (measured 2026-09-26 on ae8cb6ed5 with z3 4.8.12 and
    // carcara 1.1.0 git 9a352ee, reading each problem with its datatypes as
    // uninterpreted sorts with free constructor/selector functions, constant
    // arrays as a free function of the fill value, and parameterized
    // `define-fun`s as `declare-fun`s -- all pinned carcara can use, which has
    // no datatype rule, no constant-array rule and no beta reduction):
    // * FP row: carcara cannot parse the problem ("sort 'FloatingPoint' is
    //   not defined").
    // * `nested_premise_false`, `nested_query_false`: carcara cannot parse the
    //   problem ("sort error: expected '(Outer)', got '(Inner)'": both
    //   datatypes declare `fld_len`, and carcara keeps one selector per name).
    // * `typed_vec_pins_cell64`: carcara cannot parse `(as mkVec Vec)` ("not a
    //   valid qualified operator"), and the reading is `sat` anyway.
    // * `pbterm_ancestor_default`, `vec_ancestor_conflict`,
    //   `branching_vec_premise_false`, `deep_vec_iteration_query_false`: z3
    //   answers `sat` on that reading and `unsat` once the selector-over-
    //   constructor axioms `(sel_i (C x_1 .. x_n)) = x_i` are added (the
    //   first also needs its constant array read back, `unknown` without):
    //   no carcara proof exists.
    // * `total_wide_keys`: `sat` on that reading (the body of `summary` is
    //   what refutes it); see the `define-fun` note on the holey rows below.
    "model_checker_consumer_fp_relation_symbolic_sum_identity_unsat",
    "model_checker_consumer_nested_array_residual_pbterm_ancestor_default_unsat",
    "model_checker_consumer_nested_residual_vec_ancestor_conflict_unsat",
    "model_checker_consumer_quantified_counterexample_branching_vec_premise_false_unsat",
    "model_checker_consumer_quantified_counterexample_deep_vec_iteration_query_false_unsat",
    // Its binder bounds are datatype FIELDS, so only the derived-bound finite
    // expansion refutes it, and the plain verdict is the exact finite-expansion
    // semantic certificate replayed from the authored roots
    // (#source-derived-unsat-replay): a checked theorem with no Alethe
    // rendering, which proof mode therefore withholds. Pinned carcara 1.1.0
    // has no array or datatype rules for a rendered alternative. Its outer
    // array's elements carry arrays in datatype fields, so the plain verdict
    // also passes the nested-array quarantine, which admits that theorem as a
    // rung (#nested-array-quarantine-datatype-fields).
    "model_checker_consumer_quantified_counterexample_nested_premise_false_unsat",
    // Ground-refutable (the queried row-33 cell is 7 by the fact's own
    // constant array). Proof mode fails closed inside AY: the datatype and
    // nested-array reasoning has no strict rules, so the ground refutation ends
    // in a whole-problem `trust` step that strict certification withholds, and
    // carcara never receives a proof. Plain mode is withheld too: its
    // authored-ground-core leg (#ground-core-corroboration) refutes a core
    // that keeps arrays inside the datatype fields of an outer array's
    // elements, and that nested-array UNSAT has no authority beyond a fresh
    // executor re-deciding it (#nested-array-quarantine-datatype-fields).
    "model_checker_consumer_quantified_counterexample_nested_query_false_unsat",
    "model_checker_consumer_quantified_counterexample_total_wide_keys_unsat",
    // ORACLE EVIDENCE DEPENDS ON THE Z3 VERSION (measured 2026-09-24 at
    // ad60a0707, -T:10/30/120). z3 4.8.12 answers `unsat` on the whole file
    // in 0.03 s. Neither 4.16.0 nor 5.1.0 decides it at any limit: `timeout`
    // at -T:10 (1.9-2.2 GB RSS), `unknown` after 26-35 s at -T:30 and -T:120
    // (5.6 GB RSS, reason-unknown "Overflow encountered when expanding
    // vector"). All three refute its quantifier-free assertions (v0 pinned
    // twice, disagreeing at index 64) in 0.01 s, which is the route the oracle
    // takes there. No second oracle: cvc5 1.4.0 (Python API) rejects the
    // input, `(as const ...)` over the non-value `f0`.
    "model_checker_consumer_quantified_counterexample_typed_vec_pins_cell64_unsat",
    // The A-UFA-g6-div0 abort row (3840ffb06) left this list for
    // `ORACLE_UNSAT_EXPORT_REFUSED_ROWS`, as `cascade_v2` did.
    // Added by 7b4a463df (the 2026-09-23 quantifier hunt, D1) for its wrong
    // `sat`, not its proof. Plain mode answers `unknown (incomplete
    // quantifier-unhandled)`; under `:produce-proofs` the refutation needs the
    // datatype tester lemma `(= ((_ is w) a3) (= a3 (w (g a3))))`, a `Generic`
    // lemma strict mode declines (`--debug-cert`), so AY answers `unknown`.
    // z3 5.1.0 -T:10 answers `unsat`. Measured 2026-09-29 on origin/main
    // e62749aa4 plus the series that added this entry.
    "wrong-verdict_unsat_ufdt_forall_field_sort_four_values",
];

/// Independently oracle-confirmed UNSAT rows that AY decides `unsat` under
/// `:produce-proofs` with an internally strict-checked proof, but whose Alethe
/// export `get-proof` REFUSES with an explicit `UNVERIFIABLE PROOF` error
/// instead of printing a document (the non-strict default keeps a certified
/// verdict whose artifact cannot be rendered; see 5b570c0b1, and
/// `--strict-proofs` for the fail-closed alternative). These are NOT counted
/// as proof parity. The gate requires exactly that refusal, never a partial
/// document, and Z3 must independently answer `unsat`; a row that gains a
/// printable proof must then pass carcara and leave this list.
const ORACLE_UNSAT_EXPORT_REFUSED_ROWS: &[&str] = &[
    // Its refutation assumes the datatype-field expansions of authored record
    // equalities (`(= v6 v7)` as the conjunction of its four field
    // equalities) and the selector reading of an authored constructor
    // equation. Pinned carcara 1.1.0 has no datatype rules to derive the
    // latter from the authored assertions, so no printer bridge can make the
    // document checkable; the printer refuses it (an `and_pos` whose source
    // no longer prints as an and-term). Exception class (b) of the proposed
    // ledger (the development design notes, section
    // 5.7): measured 2026-09-23 on 908d6b160 plus this change, carcara 1.1.0
    // (git 9a352ee), z3 `unsat`. Retire when carcara gains datatype rules or
    // AY derives the field expansions from the authored assertions.
    "model_checker_consumer_quantified_counterexample_deep_vec_iteration_premise_false_unsat",
    // `cascade_v2` states the divisibility of `ring_2exp16_5vars_cascade` as
    // `(= (mod x_i 3) 0)`. Its refutation rests on the `mod` purification
    // (`x1 = 3·q + r`, `0 <= r < 3`), which the strict checker now validates
    // as `divmod_def` (`q := (div x1 3)`, `r := (mod x1 3)` over the shared
    // `FreshDefRegistry`), so AY answers `unsat` under `:produce-proofs`
    // where it used to withhold `unknown` at the `trust` step. No document
    // follows: pinned carcara 1.1.0 has no div/mod axiom (`mod_simplify`,
    // `div_simplify` and `evaluate` fold constants only; `la_generic` treats a
    // non-constant `mod` as an opaque atom) and an Alethe proof cannot
    // declare the minted `q`/`r`, so the exporter refuses. z3 5.1.0: unsat.
    "QF_LIA_ring_2exp16_5vars_cascade_v2_unsat",
    // The differential gate's uf-arith g6_100167 (A-UFA-g6-div0 forged-guard
    // witness, added by fb2d6082e0). Its refutation rests on the purification
    // of `(mod x1 3)` (the zero divisors are irrelevant to it), now a strictly
    // checked `divmod_def` exactly as for `cascade_v2` above, so AY answers
    // `unsat` and the exporter refuses the document for the same two reasons.
    // z3 5.1.0: unsat.
    "abort_unsat_uflia_div0_forged_guard_g6_100167",
    // Added to the corpus by 3840ffb06 (A-UFA-g6-div0) for its abort, not its
    // proof. It used to answer `unknown` under `:produce-proofs`: the only
    // proof strict mode saw rested on a declined `Generic` lemma over the zero
    // divisors. The strict proof AY now admits never touches them. `x0 = 6`
    // and `x0 = (mod (f x0) (- 2))` contradict the remainder bound `r < 2`,
    // which is a checked `divmod_def` with `r := (mod (f x0) (- 2))`. That
    // pair is recovered from its mint-site record, because the purification
    // equation is not in the refutation. The exporter refuses the document
    // for the same two reasons as `cascade_v2`. z3 5.1.0: unsat.
    "wrong-verdict_unsat_uflia_div0_reconfirm_g6_100000",
];

/// AY PUBLISHES A PROOF CARCARA CAN ONLY CALL `holey` — externally UNVERIFIED.
///
/// A separate bucket from `ORACLE_UNSAT_UNSUPPORTED_ROWS` on purpose: there AY
/// withholds (answers `unknown`); here AY answers `unsat` and publishes a
/// document whose every step pinned Carcara re-derives, with NO allowance,
/// EXCEPT the listed number of disclosed `hole` steps. AY's own strict
/// checker accepts each hole (it checks the step natively), but no external
/// checker has: `holey` is not verification, so these rows are never counted
/// as verified, each needs Z3's independent `unsat`, and the set is exact in
/// both directions — a row that becomes `valid` or changes its hole count
/// fails until this list is updated, and an unlisted `holey` row fails.
///
/// Until 2026-09-23 the corpus runner passed `--allowed-rules trust` and read
/// Carcara's exit status, which is 0 for `holey`, so every row below was
/// counted as externally verified. Measured on ay `8d9e105fa` and `69efb137d`, carcara 1.1.0
/// [git 9a352ee], z3 4.16.0 `unsat` on every row; each document carries ONE
/// `hole` step and no `trust` step:
/// * `model_checker_consumer_quantified_artifact_total_function_unsat` t5 (`(f w)` at the
///   `choice` witness `w` is the constant body `(_ bv1 2)`) and
///   `model_checker_consumer_quantified_counterexample_total_default_unsat` t9 (the instance
///   `(summary #b0..01000000)` is `#b0`). Each checked step holds only once a
///   PARAMETERIZED problem `define-fun` is unfolded, and no proof of either
///   problem can be carcara `valid` in the gate's reading. z3 answers `sat`
///   on each with its `define-fun` read as a `declare-fun`, so every
///   refutation uses the definition. Pinned carcara, run without
///   `--apply-function-defs`, holds that definition only as the premise
///   `(= f (lambda ..))`. From it `ho_cong` yields `(= (f a) ((lambda ..) a))`
///   and no rule reduces that application: there is no beta rule (`beta` is
///   an unknown rule), `evaluate` and `refl` read the application unreduced,
///   `rare_rewrite` needs a `--rare-file` (an allowance), and `lia_generic` is
///   a hole. Measured 2026-09-26 on 9896793af and pinned against the real
///   checker by `define_fun_reading.rs`. They retire when the pinned checker
///   can unfold a definition, or if the gate adopts `--apply-function-defs`.
///   Adopting that flag is an owner decision: at 9896793af it turns the
///   verified `signed_range64_missing_negative` row `invalid`, because that
///   row's nullary bridge assumes the premise `(= a body)`, which only the
///   default reading holds (LIMITATIONS.md).
/// * `model_checker_consumer_quantified_counterexample_total_projection_unsat` t2: the
///   `eq_transitive` edge through the authored `(= (identity local) local)`.
///   AY holds it with the problem `define-fun` unfolded (`identity` is the
///   constant `(_ bv0 136)`); pinned carcara, run without
///   `--apply-function-defs`, reads `identity` as declared, so the printed
///   chain cannot meet the unfolded constant. Measured 2026-09-25 on
///   ad60a0707 plus the instance-seeded closure: the same document with that
///   edge spelled `eq_transitive` is `invalid` ("broken transitivity chain")
///   and `valid` under `--apply-function-defs`.
///
/// Retired 2026-09-25: `model_checker_consumer_nested_residual_vec_alias_conflict_unsat`
/// (t10) and `model_checker_consumer_quantified_counterexample_wide_key136_truncated_pin_unsat`
/// (t4) held an `eq_transitive` whose printed chain was broken only by the
/// authored spelling of a closed bit-vector term AY had folded (`(bvadd
/// (_ bv63 64) (_ bv1 64))` against `#b0...01000000` under `select`/`fld_vec`/
/// `fld_len`; a 136-bit `concat` against its folded constant). The printer
/// now proves that link (`evaluate`, lifted by `cong`) and closes the chain
/// with checked rules, so both are Carcara `valid` with no allowance
/// (`closed_spelling_chain.rs`).
///
/// Retired 2026-09-26: the two `model_checker_consumer_quantified_models_signed_range64_*`
/// rows (t5 `fill`, t10 `missing_negative`). Their guarded-instance lemma is
/// decided by its closed signed guards (and, for `missing_negative`, a store
/// read through the nullary `define-fun` premise `(= a body)`), which the
/// printer's closed-atom lowering (`ay-proof` `alethe_printer/closed_guard.rs`)
/// re-derives with `pbblast_bv*` plus `la_generic`, never carcara's signed
/// `evaluate`; both are Carcara `valid` with no allowance (`closed_guard.rs`).
const ORACLE_UNSAT_HOLEY_PROOF_ROWS: &[(&str, usize)] = &[
    // Retired 2026-09-25: `QF_ABV_wide_mul_unsat` (t2, a two-literal
    // `bvmul`-by-zero bit-blast lemma printed over the authored
    // `(bvugt (select (store a #x00 (bvmul x y)) #x00) #x00000000)`). The
    // authored assume is now bridged to the canonical `(bvult 0 (bvmul x y))`
    // with `pbblast_bvugt`/`pbblast_bvult`, `arrays_idx` and `cong`, and the
    // lemma is the complete blast of its atoms' conjunction, opened by
    // `and_neg`; Carcara `valid` with no allowance (`bv_conflict_clause.rs`).
    // Retired 2026-09-26: `QF_LIA_ring_2exp12_3vars_deep_unsat` (t20) and
    // `QF_LIA_ring_2exp8_5vars_modular_unsat` (t37). Each held an
    // `IntGuardedSplitGap` lemma whose literals are all negated integer
    // equalities (3 and 4 of them) and which only an INTEGER combination
    // refutes (`E1 + 3·E2 + E3` is `-4096·(3c1 + c2 + c3) + 11788 = 0`,
    // `4096 ∤ 11788`); the unit divisibility lowering of `b39a5c9c8` covered
    // one equality only. The printer now lowers it through that combination,
    // recovered from the strict checker's own elimination: one `la_generic`
    // lattice split, two `la_generic` rows and two resolutions; Carcara
    // `valid` with no allowance (`alethe_printer/equality_lattice.rs`).
    // Retired 2026-09-26: `QF_NIA_simple_product_unsat` (t5, the native SOS
    // `ay-nra-sos` certificate refuting `1 <= x <= 2`, `1 <= y <= 2`,
    // `x*y = 7` through the product `(x-1)(2-y) >= 0`). The printer now
    // lowers a strict-checked SOS certificate to `la_mult_pos`/`la_mult_neg`
    // products and squares, `poly_simp` normal forms and one `la_generic`
    // with the certificate's own coefficients; Carcara `valid` with no
    // allowance (`nra_sos_lowering.rs`).
    // Added with the arrays repair's abort witness (fix-up session 5; main
    // 9ea9b8b5dd panicked on it in `--z3-mode`). Under `:produce-proofs` AY
    // answers `unsat` with one `hole` step: the unit negation of the first
    // assertion, `(not (= ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b11)
    // (store (select (store m0 true b0) true) #b11 #b00)))` — a const array
    // against a store whose read at `#b11` is `#b00`, a read-over-write lemma
    // the printer emits without a rule chain; pinned carcara 1.1.0 answers
    // `holey`. z3 5.1.0 -T:10 answers `unsat`. Measured 2026-09-29 on the
    // integration train (origin/main eee00234b7 plus the six repair branches).
    ("abort_unsat_bv_dense_range_bool_index_nestfin_2909_0018", 1),
    (
        "model_checker_consumer_quantified_artifact_total_function_unsat",
        1,
    ),
    (
        "model_checker_consumer_quantified_counterexample_total_default_unsat",
        1,
    ),
    (
        "model_checker_consumer_quantified_counterexample_total_projection_unsat",
        1,
    ),
    // Added by 7b4a463df (the 2026-09-23 quantifier hunt, D1) for its wrong
    // `sat`. Under `:produce-proofs` AY answers `unsat` with two `hole` steps,
    // each the constructor expansion of a one-element list equation
    // (`(= (= b (cons u nil)) (and ((_ is cons) b) (= (tl b) nil) (= u (hd
    // b))))`): a `Generic` datatype lemma with no rule in pinned carcara 1.1.0,
    // which answers `holey`. z3 5.1.0 -T:10 answers `unsat`. Measured
    // 2026-09-29 on origin/main e62749aa4 plus the series that added this entry.
    ("wrong-verdict_unsat_ufdt_forall_field_sort_list_cells", 2),
];

/// The six exact semantic-publication regressions that motivated the checked
/// divisibility wire lowering and authored-surface repair. They are named here
/// so none can silently slide back into an oracle-backed UNKNOWN bucket. Each
/// must publish a proof that Carcara verifies (`valid`, no allowance); none
/// is listed in `ORACLE_UNSAT_HOLEY_PROOF_ROWS`.
const REQUIRED_DIVISIBILITY_PUBLICATION_ROWS: &[&str] = &[
    "QF_LIA_ring_2exp12_3vars_deep_unsat",
    "QF_LIA_ring_2exp4_3vars_0ite_unsat",
    "QF_LIA_ring_2exp8_3vars_crt_unsat",
    "QF_LIA_ring_2exp8_4vars_carry_unsat",
    "QF_LIA_ring_2exp8_5vars_modular_unsat",
    "QF_UFLIA_unsat_congruence_to_lia",
];

/// The focused lattice-lowering rows; all four must be Carcara `valid`. Each
/// natively refutes a multi-equality `IntGuardedSplitGap` lemma, which the
/// all-equality lattice lowering prints as one `la_generic` split. Before it,
/// `0ite` and `carry` published only through the authored divisibility
/// replacement (a unit Divisibility lemma), which the wire-gap retry still
/// reaches when a native proof keeps another gap; `crt` in
/// `REQUIRED_DIVISIBILITY_PUBLICATION_ROWS` still prints the unit lowering.
/// (This list once called all four complete when only an exit-code runner had
/// confirmed it; `deep` and `modular` were then listed holey from 2026-09-23
/// to 2026-09-26.)
const CHECKED_DIVISIBILITY_WIRE_ROWS: &[&str] = &[
    "QF_LIA_ring_2exp12_3vars_deep_unsat",
    "QF_LIA_ring_2exp4_3vars_0ite_unsat",
    "QF_LIA_ring_2exp8_4vars_carry_unsat",
    "QF_LIA_ring_2exp8_5vars_modular_unsat",
];

/// The listed hole count of a `holey` row, or `None` when it is not listed.
fn listed_holey_row(label: &str) -> Option<usize> {
    ORACLE_UNSAT_HOLEY_PROOF_ROWS
        .iter()
        .find(|(listed, _)| *listed == label)
        .map(|(_, holes)| *holes)
}

/// Every unchecked (`hole` or `trust`) step line of a published document.
fn unchecked_proof_steps(proof: &str) -> Vec<&str> {
    proof
        .lines()
        .filter(|line| {
            [":rule hole", ":rule trust"].iter().any(|rule| {
                line.match_indices(rule).any(|(at, _)| {
                    matches!(line.as_bytes().get(at + rule.len()), Some(b')' | b' '))
                })
            })
        })
        .collect()
}

/// `source` with every top-level `assert` that mentions a quantifier removed
/// and every other command kept verbatim, so it asserts a subset of the row's
/// own premises. `None` when nothing would be removed or the script is not
/// splittable.
fn quantifier_free_subset(source: &str) -> Option<String> {
    let forms = top_level_forms(source)?;
    let quantified = |form: &str| {
        form.starts_with("(assert")
            && form
                .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
                .any(|token| token == "forall" || token == "exists")
    };
    let kept: Vec<&str> = forms.iter().copied().filter(|f| !quantified(f)).collect();
    (kept.len() < forms.len()).then(|| kept.join("\n"))
}

/// The top-level s-expressions of an SMT-LIB script, comments dropped;
/// `None` when the parentheses do not balance or a string or quoted symbol is
/// present (the splitter does not model either, so it declines).
fn top_level_forms(source: &str) -> Option<Vec<&str>> {
    if source.contains('"') || source.contains('|') {
        return None;
    }
    let mut forms = Vec::new();
    let (mut depth, mut start, mut in_comment) = (0usize, 0usize, false);
    for (at, ch) in source.char_indices() {
        match ch {
            '\n' => in_comment = false,
            _ if in_comment => {}
            ';' => in_comment = true,
            '(' => {
                if depth == 0 {
                    start = at;
                }
                depth += 1;
            }
            ')' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    forms.push(&source[start..=at]);
                }
            }
            _ => {}
        }
    }
    (depth == 0).then_some(forms)
}

#[test]
fn quantifier_free_subset_drops_only_quantified_asserts() {
    let script = "; header (\n(declare-const x Int)\n(assert (forall ((i Int)) (> i x)))\n\
                  (assert (= x 1)) ; note )\n(assert (not (exists ((j Int)) (= j x))))\n(check-sat)\n";
    assert_eq!(
        quantifier_free_subset(script).as_deref(),
        Some("(declare-const x Int)\n(assert (= x 1))\n(check-sat)")
    );
    // A symbol that merely contains the keyword is not a quantifier.
    assert_eq!(quantifier_free_subset("(assert forall_x)"), None);
    // Unbalanced, string-bearing or quoted-symbol scripts decline.
    assert_eq!(
        quantifier_free_subset("(assert (forall ((i Int)) true)"),
        None
    );
    assert_eq!(
        quantifier_free_subset("(assert (forall ((|i j| Int)) true))"),
        None
    );
}
