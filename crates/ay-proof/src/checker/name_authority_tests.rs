// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DRIFT-PROOF NAME-AUTHORITY LINT for the strict theory-lemma validators.
//!
//! # The bug class this exists to kill
//!
//! A theory-lemma kind is a licence to believe a clause with no derivation
//! behind it, so every strict validator must RE-DERIVE its fact from the clause
//! alone. In this term representation the only handle a validator has on an
//! operator is its SPELLING (`TermData::App(Symbol::Named(name), args)`), so
//! "re-derive from the clause" silently depends on one unstated premise:
//!
//! > the spelling the validator matches actually denotes the native theory
//! > operator, and cannot be a user symbol wearing the same name.
//!
//! That premise is owned by `ay-frontend`, not by the checker.
//! [`RESERVED_OP_NAMES`] rejects a declaration of a builtin spelling outright;
//! the `MapTarget` and `DeclarationActivated` rows of
//! `EXCLUDED_DECLARABLE_OP_NAMES` keep the spelling declarable but still
//! canonical (a `MapTarget` declaration is rewritten to a private core
//! identity, so the raw spelling continues to mean the builtin; a
//! `DeclarationActivated` declaration is accepted ONLY at the native signature
//! and is documented to REQUEST the native semantics). Everything else — every
//! `IndexedOnly` and `DeclaredShadowed` name, every name in neither table —
//! remains an ORDINARY user symbol whose spelling carries no theory meaning at
//! all. `ay_frontend::is_canonical_theory_operator_identity` is exactly this
//! predicate.
//!
//! When a validator matches a spelling the frontend does not own, its
//! acceptance is keyed on a LABEL rather than re-derived, and a user
//! declaration of that spelling turns the validator into a forgery oracle.
//! Two instances of this class have already shipped and been fixed by hand:
//!
//! * an `ArrayRowChain` sub-schema decided "this is an array map" from a
//!   function NAME beginning `map[`, and published `unsat` on a satisfiable
//!   goal;
//! * `string_ground`'s ground evaluator gave native `str.to_code` /
//!   `str.from_code` / `str.from_int` / `str.is_digit` semantics to the
//!   invented dotted spellings `str.to.code` / `str.from.code` /
//!   `str.from.int` / `str.is.digit`, which `ay-frontend` does not reserve, no
//!   elaborator arm produces, and z3 5.0.0 rejects outright ("unknown constant
//!   str.to.code"). The ONLY way such an application can exist is a user
//!   `(declare-fun str.to.code (String) Int)` — an uninterpreted function the
//!   evaluator would then have "proved" a ground tautology about.
//!
//! Both were found by adversarial reading. This lint makes the class
//! MECHANICAL: it re-extracts, at test time, every operator spelling the
//! strict validators test a symbol name against, and fails on any spelling
//! that is not a canonical theory-operator identity and is not classified
//! below with a written authentication argument.
//!
//! [`RESERVED_OP_NAMES`]: ay_frontend::is_reserved_op_name
//!
//! # Why the exception table is small and must stay small
//!
//! Every row in [`NAME_AUTHORITY_EXCEPTIONS`] is a place where the checker
//! depends on something OTHER than the frontend's reserved-name discipline.
//! Each row must carry the argument for why that dependence is sound. Adding a
//! row is the reviewable act; the lint's value is that a new unauthenticated
//! spelling cannot be added silently.
//!
//! # What this lint deliberately does NOT catch
//!
//! It certifies that a validator only keys on spellings the frontend OWNS. It
//! cannot judge whether the frontend is right to own them. One family is worth
//! recording, because an audit of this class will keep rediscovering it:
//! `set.subset` / `map.subset` / `multiset.subset` / `map.dom` are
//! `DeclarationActivated`, so they count as canonical here — a `declare-fun` at
//! the native collection signature is the documented route by which `deductive-checks`
//! ACTIVATES AY's native collection solvers. The consequence is a definitive
//! verdict split from the pinned oracle on a legal, declaration-complete input:
//!
//! ```text
//! (declare-fun set.subset ((Array Int Bool) (Array Int Bool)) Bool)
//! (declare-const a (Array Int Bool))
//! (assert (not (set.subset a a)))          ; z3 5.0.0: sat   AY: unsat
//! ```
//!
//! ```text
//! (declare-fun multiset.subset ((Array Int Int) (Array Int Int)) Bool)
//! (declare-const a (Array Int Int)) (declare-const b (Array Int Int))
//! (assert (multiset.subset a b))
//! (assert (> (select a 0) (select b 0))) ; z3 5.0.0: sat   AY: unsat
//! ```
//!
//! (Both measured on this build.) `subset_axiom`'s schemas are CORRECT for the
//! native predicate the declaration requests — `a ⊆ a` and
//! `a ⊆ b → count(a,e) ≤ count(b,e)` hold in every model of the collection
//! theories, and the module independently re-derives the native signature and
//! carrier element sort rather than trusting the frontend gate. The split lives
//! in `ay-frontend`'s activation contract (which symbol the declaration binds),
//! not in a validator, so it is out of scope for this lint and must NOT be
//! "fixed" by weakening `subset_axiom`. Recorded here so the next audit of this
//! bug class does not have to rediscover it.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// Why a spelling the strict validators match on is sound even though
/// `ay-frontend` does not classify it as a canonical theory-operator identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NameAuthority {
    /// Reachable ONLY through a `Symbol::Indexed` destructuring, so the bare
    /// named spelling — the only form a user declaration can produce — never
    /// reaches the match. `ay-frontend` classifies these `IndexedOnly` for
    /// exactly this reason: the `(_ …)` form is theory syntax, the bare form
    /// is an ordinary declaration identity.
    ///
    /// This is a LOCAL re-derivation, not an upstream dependence: every site
    /// destructures the `Symbol` itself. For the nullary FP special literals
    /// the site additionally pins the indices against the term's recorded
    /// `Sort::FloatingPoint(eb, sb)`, so an indexed lookalike at the wrong
    /// format is rejected too.
    IndexedOnlyDispatch,
    /// A SORT name, not a term-symbol name. Sorts live in a separate namespace
    /// from function symbols (`ay-frontend`'s reserved tables deliberately do
    /// not cover `sorts.rs`), so a function declaration can never collide with
    /// one.
    SortName,
}

/// The COMPLETE list of spellings the strict validators match on that
/// `ay_frontend::is_canonical_theory_operator_identity` does not vouch for.
///
/// Adding a row here is the reviewable act. The lint below fails if any
/// extracted spelling is neither canonical nor listed, and also fails if a row
/// here becomes redundant (the extractor no longer sees it, or the frontend
/// started vouching for it) — so the table cannot silently rot into a blanket
/// allow-list.
const NAME_AUTHORITY_EXCEPTIONS: &[(&str, NameAuthority)] = &[
    // `regex_length::indexed_regex_min_length` / `regex_empty`'s indexed arm
    // both destructure `Symbol::Indexed(name, indices)` before comparing.
    ("re.^", NameAuthority::IndexedOnlyDispatch),
    // Nullary FP special literals: `fp_bounded::is_fp_literal_symbol` and
    // `fp_ground::eval_app`'s `Symbol::Indexed` arm both require the indexed
    // form AND indices equal to the recorded FP format.
    ("+zero", NameAuthority::IndexedOnlyDispatch),
    ("-zero", NameAuthority::IndexedOnlyDispatch),
    ("+oo", NameAuthority::IndexedOnlyDispatch),
    ("-oo", NameAuthority::IndexedOnlyDispatch),
    ("NaN", NameAuthority::IndexedOnlyDispatch),
    // `rounding_mode::rm_literal_index` gates on `Sort::Uninterpreted("RoundingMode")`.
    ("RoundingMode", NameAuthority::SortName),
];

/// Prefix/suffix operations applied to a symbol NAME, classified.
///
/// A prefix test is the sharpest form of this bug class — the `map[` forgery
/// was exactly one — because it matches an OPEN set of spellings rather than a
/// closed one, so no reserved-name table can ever cover it. Every site must be
/// listed here with its authentication argument, and the lint fails on an
/// unlisted one.
///
/// Entries are `(file, prefix_literal, why_it_is_authenticated)`.
const NAME_PREFIX_DEPENDENCES: &[(&str, &str, &str)] = &[
    (
        "datatype_axiom.rs",
        "is-",
        "SMT-LIB 2.6 §4.2.3 fixes the discriminator spelling as `is-` ++ \
         constructor. The prefix alone decides NOTHING: the residue must be a \
         constructor REGISTERED in the executor-supplied `DatatypeDecls`, the \
         application must be Bool-sorted, and the subject's sort must be that \
         constructor's own datatype (`sort_matches_datatype`). Without the \
         registry the whole kind fails closed. The spelling is authenticated \
         upstream too: `ay-frontend`'s dynamic `DatatypeMemberCollision` gate \
         rejects declaring `is-<ctor>` for a live datatype, and the offline \
         bundle path derives the SAME `is-{constructor}` name into the \
         authenticated declaration namespace (`bundle::validate_declaration_context`).",
    ),
    (
        "bv_bitblast.rs",
        "bv",
        "The SMT-LIB indexed bit-vector numeral `(_ bv<value> <width>)`. \
         Matched only inside the `Symbol::Indexed` arm of `lower_bv_app`, and \
         the residue must parse as a `u128` numeral with exactly one index; a \
         bare `Symbol::Named` never reaches it. The indexed form is theory \
         syntax that no `declare-fun` can produce.",
    ),
];

/// Directory holding the strict validators.
fn checker_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src/checker")
}

/// Every non-test source file under `src/checker/`.
fn validator_sources() -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(checker_dir())
        .expect("read src/checker")
        .map(|entry| entry.expect("dir entry").path())
        .filter(|path| {
            path.extension().is_some_and(|ext| ext == "rs")
                && path.file_name().is_some_and(|name| {
                    let name = name.to_string_lossy();
                    !name.ends_with("_tests.rs") && name != "tests.rs"
                })
        })
        .collect();
    files.sort();
    files
}

/// String literals in `text`, in order. Handles `\"` escapes; deliberately does
/// not handle raw strings (the validators contain none, and the sanity anchors
/// below would fail loudly if that changed and hid vocabulary).
fn string_literals(text: &str) -> Vec<String> {
    let bytes: Vec<char> = text.chars().collect();
    let mut out = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != '"' {
            index += 1;
            continue;
        }
        let mut literal = String::new();
        index += 1;
        while index < bytes.len() && bytes[index] != '"' {
            if bytes[index] == '\\' && index + 1 < bytes.len() {
                literal.push(bytes[index + 1]);
                index += 2;
                continue;
            }
            literal.push(bytes[index]);
            index += 1;
        }
        index += 1;
        out.push(literal);
    }
    out
}

/// Operator spellings are short single tokens. Prose (error messages, doc
/// text) contains whitespace, braces, parentheses or quotes and is dropped —
/// the same filter the sibling frontend drift test uses.
fn looks_like_op_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= 40
        && !name
            .chars()
            .any(|c| c.is_whitespace() || "{}():'\\\"".contains(c))
}

/// Whether `line` is a comment or doc line (no executable name test on it).
fn is_comment(line: &str) -> bool {
    let trimmed = line.trim_start();
    trimmed.starts_with("//") || trimmed.starts_with('*')
}

/// Extract the spellings a line tests a symbol name against.
///
/// Recognized forms, covering every shape the validators actually use:
///
/// * `sym.name() == "op"` / `name != "op"` / `"op" == name`
/// * a match arm of bare string literals: `"a" | "b" => …`
/// * a tuple match arm keyed on the name: `("a" | "b", 2) => …`
/// * `matches!(name, "a" | "b")`
/// * `const OP: &str = "op";` and `const OPS: [&str; N] = ["a", "b"];`
/// * `name.starts_with("p")` / `ends_with` / `strip_prefix` / `strip_suffix`
fn name_test_literals(line: &str) -> Vec<String> {
    if is_comment(line) {
        return Vec::new();
    }
    let trimmed = line.trim();
    let mut out = Vec::new();

    // `== "op"` / `!= "op"` and the mirrored `"op" ==` / `"op" !=`.
    let mut rest = line;
    while let Some(position) = rest.find("== \"").or_else(|| rest.find("!= \"")) {
        let after = &rest[position + 3..];
        let literals = string_literals(after);
        if let Some(first) = literals.first() {
            out.push(first.clone());
        }
        rest = &after[1..];
    }
    for window in ["\" ==", "\" !=", "\"=="] {
        if let Some(position) = line.find(window) {
            let literals = string_literals(&line[..=position]);
            if let Some(last) = literals.last() {
                out.push(last.clone());
            }
        }
    }

    // Bare-literal and tuple match arms.
    let without_pipe = trimmed.strip_prefix('|').map_or(trimmed, str::trim_start);
    // A TUPLE arm (`("set.member", 2) => …`) keys the match on the name in
    // position 0 and is terminated by the `,` before the next tuple element.
    // A BARE arm (`"a" | "b" => …`) is terminated by `=>`, a guard, or an
    // arm continuation at end of line. The distinction matters: without it a
    // plain argument line (`err(step, "and_neg", "…")` renders `"and_neg",`
    // on its own line) would be mistaken for a name test, and the lint would
    // demand theory authority for every Alethe RULE label.
    let is_tuple = without_pipe.starts_with('(');
    let arm = if is_tuple {
        without_pipe[1..].trim_start()
    } else {
        without_pipe
    };
    if arm.starts_with('"') {
        // Consume `"a" | "b" | …` and require an arm terminator, so a bare
        // string expression (an error message, a `.to_string()` receiver) is
        // not mistaken for a pattern.
        let mut cursor = arm;
        let mut literals = Vec::new();
        loop {
            if !cursor.starts_with('"') {
                literals.clear();
                break;
            }
            let Some(end) = cursor[1..].find('"') else {
                literals.clear();
                break;
            };
            literals.push(cursor[1..=end].to_string());
            cursor = cursor[end + 2..].trim_start();
            if let Some(after_pipe) = cursor.strip_prefix('|') {
                cursor = after_pipe.trim_start();
                continue;
            }
            break;
        }
        let terminated = if is_tuple {
            cursor.starts_with(',')
        } else {
            cursor.is_empty() || cursor.starts_with("=>") || cursor.starts_with("if ")
        };
        if terminated {
            out.extend(literals);
        }
    }

    // `matches!(scrutinee, "a" | "b")`.
    if let Some(position) = line.find("matches!(") {
        let after = &line[position..];
        if let Some(comma) = after.find(',') {
            out.extend(string_literals(&after[comma..]));
        }
    }

    // `const OP: &str = "op";` / `const OPS: [&str; N] = […];`
    if trimmed.starts_with("const ") && trimmed.contains("str") && trimmed.contains('=') {
        out.extend(string_literals(trimmed));
    }

    // Prefix/suffix probes.
    for probe in [
        "starts_with(",
        "ends_with(",
        "strip_prefix(",
        "strip_suffix(",
    ] {
        let mut rest = line;
        while let Some(position) = rest.find(probe) {
            let after = &rest[position + probe.len()..];
            if let Some(first) = string_literals(after).first() {
                out.push(first.clone());
            }
            rest = &after[1..];
        }
    }

    out.retain(|literal| looks_like_op_name(literal));
    out
}

/// Prefix/suffix probe sites: `(file, literal)`.
fn prefix_probe_sites() -> BTreeSet<(String, String)> {
    let mut sites = BTreeSet::new();
    for file in validator_sources() {
        let name = file
            .file_name()
            .expect("file name")
            .to_string_lossy()
            .into_owned();
        let source = std::fs::read_to_string(&file)
            .unwrap_or_else(|error| panic!("read {}: {error}", file.display()));
        for line in source.lines() {
            if is_comment(line) {
                continue;
            }
            for probe in [
                "starts_with(",
                "ends_with(",
                "strip_prefix(",
                "strip_suffix(",
            ] {
                let mut rest = line;
                while let Some(position) = rest.find(probe) {
                    let after = &rest[position + probe.len()..];
                    // Only a probe with a STRING-literal argument tests a
                    // symbol spelling; `starts_with(pattern.as_slice())` and
                    // friends compare data, not names.
                    let trimmed = after.trim_start();
                    if trimmed.starts_with('"') {
                        if let Some(literal) = string_literals(after).first() {
                            sites.insert((name.clone(), literal.clone()));
                        }
                    }
                    rest = &after[1..];
                }
            }
        }
    }
    sites
}

/// All spellings the strict validators test a symbol name against, with the
/// `file:line` sites that test them.
fn extracted_name_tests() -> BTreeMap<String, Vec<String>> {
    let mut extracted: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for file in validator_sources() {
        let short = file
            .file_name()
            .expect("file name")
            .to_string_lossy()
            .into_owned();
        let source = std::fs::read_to_string(&file)
            .unwrap_or_else(|error| panic!("read {}: {error}", file.display()));
        for (index, line) in source.lines().enumerate() {
            for literal in name_test_literals(line) {
                extracted
                    .entry(literal)
                    .or_default()
                    .push(format!("{short}:{}", index + 1));
            }
        }
    }
    extracted
}

fn exception_class(name: &str) -> Option<NameAuthority> {
    NAME_AUTHORITY_EXCEPTIONS
        .iter()
        .find_map(|&(spelling, class)| (spelling == name).then_some(class))
}

/// THE LINT. Every operator spelling a strict validator keys on must be a
/// spelling `ay-frontend` guarantees denotes the native theory operator, or a
/// classified exception with a written authentication argument.
#[test]
fn every_validator_name_test_is_a_canonical_theory_operator_identity() {
    let extracted = extracted_name_tests();

    // EXTRACTION SANITY. Without these the lint could rot into a vacuous pass
    // (an extractor that finds nothing classifies nothing). The anchors span
    // every recognized syntactic form and every theory family.
    assert!(
        extracted.len() >= 120,
        "extraction looks broken: only {} spellings found",
        extracted.len()
    );
    for anchor in [
        "select",      // `sym == "select"` comparison, arrays
        "store",       // ditto
        "set.card",    // `const OP_CARD: &str = …`
        "set.subset",  // `const SUBSET_OPS: [&str; 3] = […]`
        "set.member",  // `("set.member", 2) =>` tuple arm
        "str.to_code", // `("str.to_code", 1) =>` tuple arm
        "str.len",
        "re.none",  // regex tuple arm
        "re.^",     // indexed-only regex operator
        "bvadd",    // bit-vector match arm
        "fp.isNaN", // FP predicate match arm
        "NaN",      // nullary FP literal
        "is-",      // the `strip_prefix` datatype-tester probe
        "bv",       // the `strip_prefix` indexed BV numeral probe
        "=",
        "or",
        "not",
        "ite",
    ] {
        assert!(
            extracted.contains_key(anchor),
            "extraction failed to find `{anchor}` — the extractor is broken, so \
             this lint is not actually checking anything"
        );
    }

    // Prefix literals are checked by their own lint below, not as spellings.
    let prefix_literals: BTreeSet<String> = NAME_PREFIX_DEPENDENCES
        .iter()
        .map(|&(_, literal, _)| literal.to_string())
        .collect();

    let mut unauthenticated: Vec<String> = Vec::new();
    for (name, sites) in &extracted {
        if prefix_literals.contains(name) {
            continue;
        }
        if ay_frontend::is_canonical_theory_operator_identity(name) {
            continue;
        }
        if exception_class(name).is_some() {
            continue;
        }
        unauthenticated.push(format!("`{name}` at {}", sites.join(", ")));
    }
    unauthenticated.sort();

    assert!(
        unauthenticated.is_empty(),
        "strict validators key on {} spelling(s) `ay-frontend` does not \
         guarantee denote the native theory operator. A user \
         `(declare-fun <spelling> …)` produces an ORDINARY uninterpreted \
         symbol with that exact spelling, so the validator would hand out a \
         theory tautology about a function it knows nothing about — the \
         `map[` / `str.to.code` bug class. Fix by re-deriving from a spelling \
         the frontend owns (reserve it, or drop the arm), NEVER by widening. \
         If the site is genuinely authenticated by something else, add a row \
         to NAME_AUTHORITY_EXCEPTIONS with the argument.\n  {}",
        unauthenticated.len(),
        unauthenticated.join("\n  ")
    );
}

/// The exception table may not rot into a blanket allow-list: every row must
/// still be needed (the extractor still sees it) and still be an exception
/// (the frontend still does not vouch for it).
#[test]
fn name_authority_exception_table_has_no_dead_or_redundant_rows() {
    let extracted = extracted_name_tests();
    for &(name, class) in NAME_AUTHORITY_EXCEPTIONS {
        assert!(
            extracted.contains_key(name),
            "NAME_AUTHORITY_EXCEPTIONS row `{name}` ({class:?}) is DEAD: no \
             strict validator tests that spelling any more. Delete the row."
        );
        assert!(
            !ay_frontend::is_canonical_theory_operator_identity(name),
            "NAME_AUTHORITY_EXCEPTIONS row `{name}` ({class:?}) is REDUNDANT: \
             `ay-frontend` now classifies it as a canonical theory-operator \
             identity, so the exception (and its weaker argument) must go."
        );
    }
    let mut seen = BTreeSet::new();
    for &(name, _) in NAME_AUTHORITY_EXCEPTIONS {
        assert!(
            seen.insert(name),
            "NAME_AUTHORITY_EXCEPTIONS lists `{name}` twice"
        );
    }
}

/// No strict validator may acquire a NEW prefix/suffix dependence on a symbol
/// spelling. A prefix test matches an OPEN set of names, so no reserved-name
/// table can ever cover it — it is the sharpest form of this bug class (the
/// `map[` forgery was exactly one) and every site needs its own argument.
#[test]
fn every_symbol_name_prefix_probe_is_classified() {
    let sites = prefix_probe_sites();
    assert!(
        !sites.is_empty(),
        "extraction looks broken: no prefix probes found at all"
    );

    let classified: BTreeSet<(String, String)> = NAME_PREFIX_DEPENDENCES
        .iter()
        .map(|&(file, literal, _)| (file.to_string(), literal.to_string()))
        .collect();

    let unclassified: Vec<String> = sites
        .difference(&classified)
        .map(|(file, literal)| format!("{file}: {literal:?}"))
        .collect();
    assert!(
        unclassified.is_empty(),
        "UNCLASSIFIED symbol-name prefix/suffix probe(s) in the strict \
         validators. A prefix decides membership of an OPEN set of spellings, \
         so no reserved-name table can authenticate it — this is how the \
         `map[` array-map forgery published `unsat` on a satisfiable goal. \
         Re-derive the fact from a registry instead, or add a row to \
         NAME_PREFIX_DEPENDENCES stating what authenticates the residue:\n  {}",
        unclassified.join("\n  ")
    );

    let dead: Vec<String> = classified
        .difference(&sites)
        .map(|(file, literal)| format!("{file}: {literal:?}"))
        .collect();
    assert!(
        dead.is_empty(),
        "DEAD NAME_PREFIX_DEPENDENCES row(s) — the probe is gone, delete the \
         row so the table cannot become a blanket allow-list:\n  {}",
        dead.join("\n  ")
    );

    // Every row must actually carry an argument, not an empty placeholder.
    for &(file, literal, why) in NAME_PREFIX_DEPENDENCES {
        assert!(
            why.len() >= 80,
            "NAME_PREFIX_DEPENDENCES row ({file}, {literal:?}) has no real \
             authentication argument"
        );
    }
}

/// The four invented dotted string spellings must stay OUT of the ground
/// evaluator, and their real SMT-LIB 2.6 counterparts must stay in.
///
/// This pins the concrete instance the lint above generalizes: `ay-frontend`
/// owns `str.to_code` (it is in `RESERVED_OP_NAMES`, so no declaration can
/// shadow it) and does not own `str.to.code` (it is in neither table and no
/// elaborator arm produces it, so a `(declare-fun str.to.code (String) Int)`
/// keeps that exact spelling as an ordinary uninterpreted function). z3 5.0.0
/// agrees: it rejects the dotted spelling with "unknown constant str.to.code".
#[test]
fn ground_evaluator_owns_only_frontend_owned_string_spellings() {
    for owned in [
        "str.to_code",
        "str.from_code",
        "str.from_int",
        "str.is_digit",
        // Genuine SMT-LIB 2.5 dotted aliases that ARE reserved, so the
        // evaluator may keep them.
        "str.to.int",
        "str.to.re",
        "str.in.re",
    ] {
        assert!(
            ay_frontend::is_canonical_theory_operator_identity(owned),
            "`{owned}` must be a canonical theory-operator identity for the \
             ground evaluator to be allowed to interpret it"
        );
    }
    for forged in [
        "str.to.code",
        "str.from.code",
        "str.from.int",
        "str.is.digit",
    ] {
        assert!(
            !ay_frontend::is_canonical_theory_operator_identity(forged),
            "`{forged}` is now frontend-owned; if that is deliberate, the \
             ground evaluator may interpret it again"
        );
        assert!(
            !extracted_name_tests().contains_key(forged),
            "the ground evaluator interprets `{forged}`, a spelling any user \
             may `declare-fun`; that makes it a forgery oracle for \
             TheoryLemmaKind::StringGroundEval"
        );
    }
}
