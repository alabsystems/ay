// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact census for dynamic Alethe rule placeholders found by wire coverage.

use std::collections::{BTreeMap, BTreeSet};

pub(super) fn assert_expected(placeholders: &BTreeMap<String, BTreeSet<String>>) {
    let actual = placeholders
        .iter()
        .map(|(name, sites)| (name.as_str(), sites.len()))
        .collect::<BTreeMap<_, _>>();
    // Each count below is a REVIEWED site list, so that a new dynamic `:rule`
    // producer fails here until it is connected to the inventory the external
    // carcara probe reads. A fixed `:rule name` needs no such routing.
    //
    // ## The constant (`UNPROVED_STEP_RULE`, and fifteen positional `{}` sites)
    //
    // `UNPROVED_STEP_RULE` is a CONSTANT, not a computed rule name: every
    // expansion prints the one checker-implemented unproved marker. The
    // scanner cannot resolve constants, so it reports the identifier as a
    // dynamic placeholder wherever it is captured inline, and as the empty
    // name wherever it is substituted positionally. The exemption is pinned to
    // the constant's VALUE by the assertion below, so it cannot become a
    // hiding place: if the constant is ever redefined to a rule name carcara
    // does not implement, this fails here rather than shipping it.
    //
    // The five inline captures are the equality-congruence and
    // equality-transitivity refusals: `alethe_printer_eq_congruent.rs` (two),
    // `alethe_printer_eq_congruent_pred.rs` and
    // `alethe_printer_eq_transitive.rs` (two). `b83b2fa1d refactor(proof):
    // isolate eq-transitive surface guards` introduced this spelling -- the
    // emitted wire text is byte-identical, only the spelling moved.
    //
    // FIFTEEN of the eighteen positional sites print the same constant: in
    // `alethe_printer.rs` the printed-arithmetic refusal, the printed-Skolem
    // refusal, the three fresh definitional lowerings `format_fresh_def_bound` /
    // `format_fresh_def_eq` / `format_divmod_def` (which have no Alethe rule to claim:
    // pinned carcara implements no rule for a solver introducing and defining
    // a symbol, and `divmod_def` answers `unknown rule`) and the
    // `forall_inst` surface refusal; and one each in `nra_sos.rs`,
    // `printed_la_disequality.rs` (the printed `la_disequality` refusal),
    // `printed_or.rs`, `printed_resolution.rs` (`printed_hole_over`),
    // `promoted_lia.rs` (the evaluation fallback taken when the ground
    // formatter declines) and `surface_and_pos.rs` (the Skolem-override
    // fallback). The negative-literal-surface fix (`bac4e4cd2`) added three
    // more, each the honest hole where a printed spelling cannot be bridged:
    // `evaluate_literal.rs` (a value with no Alethe spelling,
    // `ValueSpelling::Unspellable`), `printed_simplify.rs` (a printed step
    // that is not an instance of its rule over the text it ships) and
    // `refused_surface_hole.rs` (a refused surface step kept as a hole rather
    // than losing the unsat).
    //
    // ## The three positional sites that carry a real rule name
    //
    // `promoted_lia.rs` prints the already-inventoried promoted Farkas rule.
    //
    // `707ac89b43 proof(bv): certify bounded E5 shift contradictions` added
    // `alethe_printer/bv_mul_zero/shift_monotonicity.rs`, which prints one
    // Alethe step per Tseitin clause of its Boolean circuit and takes each
    // step's rule from `CnfStep::rule`. That name set is closed and
    // enumerable: `CnfStep` has one private constructor,
    // `BoolCircuit::add_clause`, called only from `BoolCircuit::build_cnf`,
    // whose arms spell exactly ten `&'static str` rules -- `true`, `false`,
    // `and_pos`, `and_neg`, `or_pos`, `or_neg`, `equiv_pos1`, `equiv_pos2`,
    // `equiv_neg1`, `equiv_neg2`. Bumping this count on its own would have
    // been a rubber stamp, so `dynamic_printer_rule_candidates` reads those
    // ten literals straight out of that production table and feeds them to the
    // external probe. carcara 1.1.0 (git 9a352ee) implements all ten, and the
    // probe -- not this comment -- is what re-proves that every run.
    //
    // `alethe_printer/complete_blast.rs` prints `Blasted::rule`, chosen by
    // `blast_operation`'s operator tables. `Blasted` stores the private
    // `CheckableRule` type, so an unchecked spelling cannot reach its writer.
    //
    // ## The `rule` sites
    //
    // Three are bounded selectors: `sko_forall`/`sko_ex` after strict Skolem-step
    // validation, `promoted_lia.rs`'s early return, which is reached only
    // when the rule already IS `UNPROVED_STEP_RULE`, and `respelled_atom.rs`'s
    // operand bridge (`d22d4f03f`), which picks `refl` or `poly_simp` and
    // otherwise returns `None` before a step is written. That selector is a
    // closed production table, `respelled_operand_rule`, whose WHOLE body the
    // sibling `respelled_operand_rules` reads out of production and feeds to
    // the probe, saying there what that proves and what it does not. The
    // duality site selects its two rules from the fixed decoder table too.
    //
    // The other six are typed emitters: `bv_packed.rs` (`named_step`),
    // `complete_blast.rs` (`theory_atom`), `complete_blast/transport.rs`
    // (`ClauseEmit::Rule`, planned through `Blaster::plan`),
    // `closed_guard/emit.rs` (`command`),
    // `ground_substitution/derivation.rs` (`step`) and `shadowed_stores.rs`
    // (`step`). Their raw entry points convert to `CheckableRule` before a
    // separate writer can format bytes. Complete blast carries the typed value
    // in both `Blasted` and `ClauseEmit`, so later layers cannot reintroduce an
    // unchecked string.
    //
    // The tenth is `complete_blast/order.rs` `equate` (see the count below).
    // The eleventh and twelfth are two more typed emitters:
    //
    // * `alethe_printer/mul_overflow_cert/proof.rs` (`write_step`,
    //   `519f0611d`), the one writer of the u128/i128 multiplication-overflow
    //   certificate. Its names are `&'static str` literals spread across that
    //   subtree (`GateDef::rule`, `emit`, `emit_named`, `close`, `drup`); it
    //   `write_step` converts every name to `CheckableRule`, using the typed
    //   `hole` value for an unknown name.
    // * `alethe_printer/constant_skolem_bridge.rs` (`bridge_command`), the one
    //   writer of the anchored bridge that derives `(= BODY b)` for a Skolem
    //   instance the store folded to `true` / `false`, and of the
    //   `sko_forall` / `sko_ex` that closes it. Its rules come from
    //   `ConstantBridgeStep::rule` (`eq_simplify`, `comp_simplify`, `cong`,
    //   `not_simplify`, `trans`) and from the judged Skolem step
    //   (`sko_forall`, `sko_ex`); `bridge_command` refuses any name that cannot
    //   become a `CheckableRule` and the step is then the hole.
    //
    // The probe of that array covers both.
    //
    // `CheckableRule` has a private field and canonicalizes through
    // `CHECKABLE_ALETHE_RULES`, so the typed writers cannot represent any
    // other spelling. Its unit tests cover every member, reject invented and
    // trust-only names, and pin the hole fallback. The external probe covers
    // every member of that same array.
    //
    // ## `blast_rule` and `simplify_rule`
    //
    // Each has TWO sites, and both pairs are fed by the SAME production table:
    // `decode_idempotent_bv_gate`, whose arms this test reads field-by-field.
    // The second pair is the zero-test duality's gate bridge
    // (`alethe_printer/bv_ult_zero.rs`), which lowers the very same
    // `(bvand v v)` / `(bvor v v)` collapse. It previously spliced its rule
    // names out of a connective fragment (`:rule bitblast_{conn}` and `:rule
    // {conn}_simplify`); that spelling put a name the checker cannot resolve
    // (`bitblast_`) into the literal inventory while hiding the real names
    // from it, so the site now carries complete rule names from the shared
    // table.
    //
    // ## Test code is excluded by DECLARATION, not by file name
    //
    // `707ac89b43` also put its test module INLINE in
    // `shift_monotonicity.rs`, and a filename suffix (`*_tests.rs`) used to be
    // the ONLY exclusion this scan had for test code. The inline module
    // therefore entered the scan as production and contributed both a phantom
    // `:rule {rule}` site (a loop over eight expected names) and -- worse -- a
    // literal `:rule trust` taken from a NEGATIVE assertion. `trust` is the
    // fallback AY deliberately refuses to emit (#8821) and is a name the
    // installed carcara answers `unknown rule` for, so accepting the site
    // would have failed the external probe over a rule AY never writes.
    //
    // The suffix convention could not hold: the idiomatic `#[cfg(test)] mod
    // tests;` spelling puts a plain `tests.rs` (or a `corpus.rs`) beside the
    // production module, and ELEVEN such files were being scanned as
    // production -- `complete_blast/tests.rs` among them, carrying that same
    // literal `:rule trust`. `printer_source_paths` now reads the
    // `#[cfg(test)]` module declarations and excludes what they name,
    // transitively, so the scan sees only what the printer emits.
    assert_eq!(
        ay_core::UNPROVED_STEP_RULE,
        "hole",
        "the const-substituted placeholder exempted below must remain the \
         checker-implemented unproved marker"
    );
    let expected = BTreeMap::from([
        ("", 18),
        ("UNPROVED_STEP_RULE", 5),
        ("blast_rule", 2),
        ("non_strict_rule", 1),
        // 10: complete_blast/order.rs `equate` prints `pbblast_{op}` for a
        // derived comparison (73810d00d); its raw entry point must first
        // construct a `CheckableRule`.
        // 11: mul_overflow_cert/proof.rs `write_step`, and 12:
        // constant_skolem_bridge.rs `bridge_command` (typed emitters, above).
        ("rule", 12),
        ("rule_name", 2),
        ("simplify_rule", 2),
        ("strict_rule", 1),
        ("wire", 2),
        ("wire_rule", 1),
    ]);
    assert_eq!(
        actual, expected,
        "unaccounted dynamic :rule placeholder; connect its producer to the wire-rule inventory"
    );
}
