//! Drift guard: the Clean island embedded in `src/trust_surface.rs` must be
//! the canonical `clean/veripb_kernel.lean`, comment-stripped and ASCII-ised.
//!
//! `clean check` runs on the `.lean` file; `compiler_consumer` runs on the island. If the
//! two ever diverge, the thing that was proved is not the thing that was
//! compiled. This test fails in that case.
//!
//! (It runs under stock cargo even though `trust_surface.rs` is never
//! compiled by stock cargo: the test reads the file as text.)

use std::path::PathBuf;

use veripb_core_proved::{Wide, guard};

fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// The transform documented in `src/trust_surface.rs`: drop Lean comments,
/// rewrite the two non-ASCII tokens, collapse blank runs.
fn strip_and_asciify(src: &str) -> String {
    let chars: Vec<char> = src.chars().collect();
    let mut out = String::new();
    let mut i = 0usize;
    let mut depth = 0usize;
    while i < chars.len() {
        let two: String = chars[i..(i + 2).min(chars.len())].iter().collect();
        if two == "/-" {
            depth += 1;
            i += 2;
            continue;
        }
        if two == "-/" && depth > 0 {
            depth -= 1;
            i += 2;
            continue;
        }
        if depth > 0 {
            i += 1;
            continue;
        }
        if two == "--" {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        out.push(chars[i]);
        i += 1;
    }
    let out = out.replace('\u{2192}', "->").replace('\u{2200}', "forall");

    let mut res: Vec<String> = Vec::new();
    let mut blank = false;
    for line in out.split('\n') {
        let line = line.trim_end().to_string();
        if line.is_empty() {
            if blank || res.is_empty() {
                continue;
            }
            blank = true;
        } else {
            blank = false;
        }
        res.push(line);
    }
    while res.last().map(|l| l.is_empty()).unwrap_or(false) {
        res.pop();
    }
    let mut s = res.join("\n");
    s.push('\n');
    s
}

/// The island body: everything between `clean {` and its closing brace.
///
/// The terminator `"\n}\n"` is unambiguous because no line of the island body
/// starts with `}` (a Lean declaration never does), and `scripts/regen-island.py`
/// rewrites exactly this slice.
fn island_body(surface: &str) -> &str {
    const OPEN: &str = "clean {\n";
    let start = surface
        .find(OPEN)
        .expect("no clean island in trust_surface.rs")
        + OPEN.len();
    let end = start
        + surface[start..]
            .find("\n}\n")
            .expect("no island terminator in trust_surface.rs");
    &surface[start..end]
}

/// Every `ensures ... by <theorem>` citation site of the surface, as
/// **(function, theorem)** in source order.
///
/// Pinning the *pair*, not just the theorem name, is what stops a citation
/// migrating: `by capcoeff_i64_le_coeff` on some fresh two-line function
/// satisfies "the name still appears in the file" while saying nothing about
/// `cap_coeff_i64_le_coeff`, the one whose body is pinned to the real
/// `veripb_core_proved::cap_coeff`. The two halves of the claim — *this*
/// theorem discharges *this* function's clause, and *this* function has the
/// real body — only compose when both are pinned to the same function name.
///
/// compiler_consumer reports each site as ``citation `<theorem>` kernel-discharges this
/// postcondition statement: ... the imported definition of `<function>` ``;
/// if a citation on a `min` site silently disappears the build stays green
/// with the postcondition demoted to a solver obligation (measured
/// 2026-08-24: it stays green *and* the obligation total is unchanged,
/// because the solver re-proves it unaided — so only a list of names and
/// sites can see it). The two rule-guard citations added on 2026-08-24 are
/// the exception: their clauses come back `Unknown` from the native
/// verifier, so deleting either `by` turns compiler_consumer red on its own. That
/// makes them the first citations here whose *absence* is visible without
/// this table — which is a reason to trust them more, not a reason to leave
/// them out of it.
/// `scripts/verify-proofs.sh` gates these same pairs against that log; this
/// test gates them against the source, where stock `cargo test` sees them
/// without a compiler_consumer build.
const CITATION_SITES: [(&str, &str); 20] = [
    ("cap_coeff_le_self_u64", "capcoeff_le_self"),
    ("cap_coeff_call_site", "capcoeff_le_self"),
    ("cap_coeff_le_other_u64", "capcoeff_le_other"),
    ("cap_coeff_bounds_u64", "capcoeff_min_bounds"),
    ("cap_coeff_i64", "capcoeff_i64_min_full"),
    ("cap_coeff_i64_le_coeff", "capcoeff_i64_le_coeff"),
    ("cap_coeff_i64_le_degree", "capcoeff_i64_le_degree"),
    ("cap_coeff_i64_le_capcoeff", "capcoeff_i64_le_capcoeff"),
    ("saturated_degree", "u64_le_refl"),
    ("weaken_factor_nonneg", "weaken_factor_sign_exact"),
    ("fits_i64_lower_wide", "guard_fits_lower_exact"),
    // The width guard's other half, sayable since the BitVec.ofNat multi-limb
    // lift (first-party/clean 05f6b0b3d) removed the 2^64 island-numeral
    // threshold: the upper conjunct decides `x <= i64::MAX` exactly.
    ("fits_i64_upper_wide", "guard_fits_upper_exact"),
    // The COMPLETE two-sided guard as the one conjunction the real
    // `guard::fits_i64` body computes, via compiler_consumer's bool-conjunction
    // recognizer/mint. Claims: true accepts exactly [i64::MIN, i64::MAX],
    // false rejects exactly its complement. Mutation-verified: an off-by-one
    // in either bound, `&&`->`||`, or deleting the `by` each turn the strict
    // island build red.
    ("fits_i64_wide", "guard_fits_exact"),
    // The first Option-valued citations: overflow-checked arithmetic leaves
    // (i128, the checker's exact-arithmetic width), admitted through compiler_consumer's
    // CheckedArithmetic lane and discharged against the kernel's checkedOp128
    // model. The claims are deliberately the op-DISCRIMINATING ones reachable
    // this increment: commutativity for add/mul (sub is not commutative, so a
    // sub body minted as add cannot close them) and the diagonal
    // `csub_wide(a, a) != None` for sub (false for the constant-None model
    // and unprovable for add/mul's theorems). The full Some/None
    // characterizations are staged behind three named capabilities -- see the
    // doc comments in trust_surface.rs.
    ("cadd_wide", "checkedAdd128_comm"),
    ("cadd_wide", "checkedAdd128_isSome_of_inI64"),
    ("csub_wide", "checkedSub128_self_isSome"),
    ("csub_wide", "checkedSub128_isSome_of_inI64"),
    ("cmul_wide", "checkedMul128_comm"),
    ("cmul_wide", "checkedMul128_isSome_of_inI64"),
    // The first CONSUMER-shape citation: the narrowing twin of
    // `guard::narrow`. Its other clause (`result == narrowWide(x)`, the
    // full functional equation) is UNCITED -- it closes by delta-defeq
    // against the island definition -- so only the guarded one appears
    // here, which is why this table has one row for that function's two
    // clauses.
    ("narrow_wide_in_range", "narrowWide_isSome_of_fits"),
];

/// The signature and body every citation site is pinned to, as
/// **(function, signature, body)**.
///
/// Four of the nine citations that existed when this table was written were
/// pinned (the `cap_coeff_i64*` twins, against the real
/// `cap_coeff`); the other five were not, so their bodies could drift away
/// from the theorem their `ensures` clause cites while every test stayed
/// green. A citation is a claim that *this* computation has *that* property,
/// and an unpinned body makes the claim about nothing in particular.
///
/// The `u64` group states the same `min` over the unsigned width the general
/// `capCoeff` lemmas are demonstrated at, which is why it compares with `<`
/// rather than `<=`: over `u64` the two agree, and the island theorems for
/// this group are stated over the term this body mints.
/// `saturated_degree` is the reflexivity control — documented in
/// `trust_surface.rs` as *not* a soundness property — and is pinned for the
/// same reason as the rest: so that it stays the trivial identity it is
/// advertised as, rather than quietly acquiring content.
///
/// The last four rows are the rule-guard twins, and for them the body text is
/// the *whole* claim: `{ w >= 0 }`, the two single-bound comparisons, and the
/// two-sided conjunction are each exactly the computation the cited theorem
/// is about — operator, literal and connective. A one-character edit to any
/// of them is a different contract.
/// `the_rule_guard_twins_have_the_predicate_of_the_real_guards` is the other
/// half: it pins these against the guards in `src/lib.rs` that the checker
/// actually runs.
const CITATION_BODIES: [(&str, &str, &str); 17] = [
    (
        "cap_coeff_le_self_u64",
        "pub fn cap_coeff_le_self_u64(c: u64, d: u64) -> u64",
        "{ if c < d { c } else { d } }",
    ),
    (
        "cap_coeff_call_site",
        "pub fn cap_coeff_call_site(c: u64, d: u64) -> u64",
        "{ cap_coeff_u64(c, d) }",
    ),
    (
        "cap_coeff_le_other_u64",
        "pub fn cap_coeff_le_other_u64(c: u64, d: u64) -> u64",
        "{ if c < d { c } else { d } }",
    ),
    (
        "cap_coeff_bounds_u64",
        "pub fn cap_coeff_bounds_u64(c: u64, d: u64) -> u64",
        "{ if c < d { c } else { d } }",
    ),
    (
        "cap_coeff_i64",
        "pub fn cap_coeff_i64(degree: i64, coeff: i64) -> i64",
        "{ if coeff <= degree { coeff } else { degree } }",
    ),
    (
        "cap_coeff_i64_le_coeff",
        "pub fn cap_coeff_i64_le_coeff(degree: i64, coeff: i64) -> i64",
        "{ if coeff <= degree { coeff } else { degree } }",
    ),
    (
        "cap_coeff_i64_le_degree",
        "pub fn cap_coeff_i64_le_degree(degree: i64, coeff: i64) -> i64",
        "{ if coeff <= degree { coeff } else { degree } }",
    ),
    (
        "cap_coeff_i64_le_capcoeff",
        "pub fn cap_coeff_i64_le_capcoeff(degree: i64, coeff: i64) -> i64",
        "{ if coeff <= degree { coeff } else { degree } }",
    ),
    (
        "saturated_degree",
        "pub fn saturated_degree(degree: u64) -> u64",
        "{ degree }",
    ),
    (
        "weaken_factor_nonneg",
        "pub fn weaken_factor_nonneg(w: i64) -> bool",
        "{ w >= 0 }",
    ),
    (
        "fits_i64_lower_wide",
        "pub fn fits_i64_lower_wide(x: i128) -> bool",
        "{ x >= -9223372036854775808 }",
    ),
    (
        "fits_i64_upper_wide",
        "pub fn fits_i64_upper_wide(x: i128) -> bool",
        "{ x <= 9223372036854775807 }",
    ),
    // For the conjunction twin the body text is the ENTIRE claim twice over:
    // both operators, both literals, and the connective are exactly what
    // `guard_fits_exact` is about, and the same conjunction (modulo the
    // const-folded `Wide::from(...)` spelling) is the body of the real
    // `guard::fits_i64` that the checker runs.
    (
        "fits_i64_wide",
        "pub fn fits_i64_wide(x: i128) -> bool",
        "{ x >= -9223372036854775808 && x <= 9223372036854775807 }",
    ),
    // The checked-arithmetic leaves: each body is ONE bare checked call, and
    // that is the entire point — the recognizer keys the op off the
    // CheckedBinaryOp the call inlines to, so the body text pins which
    // mathematical operation the citation is a claim about.
    (
        "cadd_wide",
        "pub fn cadd_wide(a: i128, b: i128) -> Option<i128>",
        "{ a.checked_add(b) }",
    ),
    (
        "csub_wide",
        "pub fn csub_wide(a: i128, b: i128) -> Option<i128>",
        "{ a.checked_sub(b) }",
    ),
    (
        "cmul_wide",
        "pub fn cmul_wide(a: i128, b: i128) -> Option<i128>",
        "{ a.checked_mul(b) }",
    ),
    // The narrowing twin: the body IS the claim, and every token of it --
    // the guard call, the cast, and which arm carries `Some` -- is what the
    // GuardedNarrow mint reads. An arms-swapped or unguarded edit here is a
    // different function, and the recognizer refuses both.
    (
        "narrow_wide_in_range",
        "pub fn narrow_wide_in_range(x: i128) -> Option<i64>",
        "{ if fits_i64_wide(x) { Some(x as i64) } else { None } }",
    ),
];

#[test]
fn island_matches_the_checked_lean_kernel() {
    let lean = std::fs::read_to_string(crate_dir().join("clean/veripb_kernel.lean"))
        .expect("clean/veripb_kernel.lean must exist");
    let surface = std::fs::read_to_string(crate_dir().join("src/trust_surface.rs"))
        .expect("src/trust_surface.rs must exist");

    let expected = strip_and_asciify(&lean);
    // `strip_and_asciify` ends with a newline; the body slice stops just
    // before the newline that opens the `"\n}\n"` terminator.
    let actual = format!("{}\n", island_body(&surface));

    // Equality, not `starts_with`: a prefix check leaves everything appended
    // after the kernel unpinned, and that region is where the
    // citation-discharging theorems used to live -- outside `clean check` and
    // outside the exported proof bundle.
    assert!(
        actual == expected,
        "the Clean island in src/trust_surface.rs is not exactly the \
         comment-stripped, ASCII form of clean/veripb_kernel.lean \
         (island {} bytes, expected {} bytes, first difference at byte {}); \
         run scripts/regen-island.py, or the proof and the program have \
         drifted apart",
        actual.len(),
        expected.len(),
        actual
            .as_bytes()
            .iter()
            .zip(expected.as_bytes())
            .position(|(a, b)| a != b)
            .map_or_else(|| "end-of-file".to_string(), |i| i.to_string()),
    );
}

#[test]
fn island_still_carries_the_cited_theorems() {
    let surface = std::fs::read_to_string(crate_dir().join("src/trust_surface.rs")).unwrap();
    let body = island_body(&surface);
    for (_, name) in CITATION_SITES {
        assert!(
            body.contains(&format!("theorem {name} ")),
            "the island no longer declares `{name}`, which an `ensures ... by \
             {name}` citation discharges; without it compiler_consumer silently demotes \
             that postcondition to an unproved obligation"
        );
    }
}

/// Every citation is still attached to the function it is a claim about.
///
/// The name-only pin this replaces was satisfiable by a citation that had
/// migrated anywhere in the file — including onto a function whose body is
/// not the one `the_i64_cap_functions_have_the_body_of_the_real_cap_coeff`
/// checks. Equality of the whole site list (not containment) also means a
/// *new* citation cannot appear unreviewed: it has to be added to the table,
/// and the reviewer has to say what it claims.
#[test]
fn every_citation_sits_on_the_function_whose_body_is_pinned() {
    let surface = std::fs::read_to_string(crate_dir().join("src/trust_surface.rs")).unwrap();
    let found = citation_sites(&surface);
    let expected: Vec<(String, String)> = CITATION_SITES
        .iter()
        .map(|(f, t)| ((*f).to_string(), (*t).to_string()))
        .collect();
    assert_eq!(
        found, expected,
        "the `ensures ... by <theorem>` sites of trust_surface.rs are not the \
         pinned ones. A citation that has moved to a different function still \
         satisfies a name-only check while claiming nothing about the function \
         whose body is pinned to `veripb_core_proved::cap_coeff`; a citation \
         that has appeared adds an unreviewed row to the headline count."
    );

    // The same list, in the shape `scripts/verify-proofs.sh` pins from the
    // compiler_consumer log -- so the two gates cannot disagree about what is cited.
    let pins = std::fs::read_to_string(crate_dir().join("clean/proved-core-expected.txt")).unwrap();
    let pin = |key: &str| -> String {
        pins.lines()
            .find_map(|l| l.strip_prefix(&format!("{key}=")))
            .unwrap_or_else(|| panic!("clean/proved-core-expected.txt has no `{key}` pin"))
            .to_string()
    };
    let mut names: Vec<&str> = CITATION_SITES.iter().map(|(_, t)| *t).collect();
    names.sort_unstable();
    assert_eq!(
        pin("island_cited_names"),
        names.join(","),
        "`island_cited_names` in clean/proved-core-expected.txt is not the \
         sorted list of theorems this file's citations cite"
    );
    let mut sites: Vec<String> = CITATION_SITES
        .iter()
        .map(|(f, t)| format!("{f}:{t}"))
        .collect();
    sites.sort();
    assert_eq!(
        pin("island_citation_sites"),
        sites.join(","),
        "`island_citation_sites` in clean/proved-core-expected.txt is not the \
         sorted `<function>:<theorem>` list this file spells"
    );
    assert_eq!(
        pin("island_citations"),
        CITATION_SITES.len().to_string(),
        "`island_citations` in clean/proved-core-expected.txt is not the number \
         of citation sites in this file"
    );

    // `citation_sites` reads *functions*: it looks for lines that open with
    // `pub fn`. A citation on anything else -- a method inside an `impl`, a
    // `pub const`, a `pub unsafe fn` -- is invisible to it, and invisible to
    // the equality above too, because a site it cannot see is simply absent
    // from `found`. That is a silent hole in the headline count, so the two
    // are cross-checked here against a scan that reads no structure at all.
    let rust = &surface[surface.find("\n}\n").expect("island terminator")..];
    // Count CITATIONS, not `ensures` clauses. The invariant this gate exists
    // for is that no `by <theorem>` escapes attribution to a `pub fn` -- a
    // citation on any other item would be counted by neither table and could
    // claim anything. An `ensures` with NO `by` is a different, legitimate
    // thing: the uncited defeq lane discharges it against an island
    // definition (the f43/f45/f49 mechanism, and `narrow_wide`'s functional
    // equation), minting no citation site by design, so counting clauses
    // would now fail on a correct file.
    let is_by_token = |line: &&str| {
        let t = line.trim_start();
        !t.starts_with("//")
            && t.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .any(|word| word == "by")
    };
    let clauses = rust.lines().filter(is_by_token).count();
    assert_eq!(
        clauses,
        found.len(),
        "trust_surface.rs has {clauses} `ensures` clause(s) but `citation_sites` \
         reads {}. A citation written on an item that does not open with \
         `pub fn` is counted by neither the table above nor the headline in \
         README and the development design notes -- teach the reader the new shape \
         rather than letting the count go quietly wrong.",
        found.len()
    );
}

/// Every citation site's signature and body are pinned, not just the four
/// `i64` twins.
///
/// See [`CITATION_BODIES`]. `the_i64_cap_functions_have_the_body_of_the_real_cap_coeff`
/// pins the twins against `veripb_core_proved::cap_coeff`, which is the claim
/// that matters most because SATURATE runs that body; this pins the remaining
/// five against themselves, so that a citation cannot go on claiming a
/// property of a computation that has since changed underneath it.
#[test]
fn every_citation_site_has_a_pinned_signature_and_body() {
    let surface = std::fs::read_to_string(crate_dir().join("src/trust_surface.rs")).unwrap();

    let mut pinned: Vec<&str> = CITATION_BODIES.iter().map(|(f, _, _)| *f).collect();
    let mut cited: Vec<&str> = CITATION_SITES.iter().map(|(f, _)| *f).collect();
    pinned.sort_unstable();
    pinned.dedup();
    cited.sort_unstable();
    cited.dedup();
    assert_eq!(
        pinned, cited,
        "CITATION_BODIES and CITATION_SITES name different functions, so some \
         citation site has no pinned body or some pin has no citation"
    );

    for (name, signature, body) in CITATION_BODIES {
        assert_eq!(
            fn_signature(&surface, name),
            signature,
            "`trust_surface::{name}` no longer has the signature its citation \
             was reviewed against"
        );
        assert_eq!(
            fn_body(&surface, name),
            body,
            "`trust_surface::{name}` no longer has the body its `ensures` clause \
             was reviewed against, so the citation is a claim about a \
             computation nobody has looked at"
        );
    }
}

/// The `ensures` clause every citation site is pinned to.
///
/// The clause is the *claim*: `fn_signature` stops at it and `fn_body` starts
/// after it, so it sat between two pins and inside neither. Weakening
/// `cap_coeff_i64`'s to the two upper bounds — the exact pair `trust_surface.rs`
/// documents as insufficient, since they are satisfied by a cap returning
/// `i64::MIN`, which makes SATURATE unsound — left every test here green.
///
/// `by <theorem>` is not part of these strings; which theorem discharges which
/// function is pinned by [`CITATION_SITES`].
const CITATION_CLAUSES: [(&str, &str); 20] = [
    ("cap_coeff_le_self_u64", "result <= c"),
    ("cap_coeff_call_site", "cap_coeff_u64(c, d) <= c"),
    ("cap_coeff_le_other_u64", "result <= d"),
    ("cap_coeff_bounds_u64", "result <= c && result <= d"),
    (
        "cap_coeff_i64",
        "result <= coeff && result <= degree && (result >= degree || result >= coeff)",
    ),
    ("cap_coeff_i64_le_coeff", "result <= coeff"),
    ("cap_coeff_i64_le_degree", "result <= degree"),
    (
        "cap_coeff_i64_le_capcoeff",
        "!(degree <= coeff) || result >= degree",
    ),
    ("saturated_degree", "result <= degree"),
    (
        "weaken_factor_nonneg",
        "(!result || w >= 0) && (result || w < 0)",
    ),
    (
        "fits_i64_lower_wide",
        "(!result || x >= -9223372036854775808) && (result || x < -9223372036854775808)",
    ),
    (
        "fits_i64_upper_wide",
        "(!result || x <= 9223372036854775807) && (result || x > 9223372036854775807)",
    ),
    (
        "fits_i64_wide",
        "(!result || (x >= -9223372036854775808 && x <= 9223372036854775807)) \
         && (result || (x < -9223372036854775808 || x > 9223372036854775807))",
    ),
    ("cadd_wide", "result == cadd_wide(b, a)"),
    (
        "cadd_wide",
        "fits_i64_wide(a) ==> fits_i64_wide(b) ==> cadd_wide(a, b) != None",
    ),
    ("csub_wide", "csub_wide(a, a) != None"),
    (
        "csub_wide",
        "fits_i64_wide(a) ==> fits_i64_wide(b) ==> csub_wide(a, b) != None",
    ),
    ("cmul_wide", "result == cmul_wide(b, a)"),
    (
        "cmul_wide",
        "fits_i64_wide(a) ==> fits_i64_wide(b) ==> cmul_wide(a, b) != None",
    ),
    (
        "narrow_wide_in_range",
        "fits_i64_wide(x) ==> narrow_wide_in_range(x) != None",
    ),
];

/// Functions a citation's *body* calls, which therefore carry part of its claim
/// without carrying a clause of their own.
///
/// `cap_coeff_call_site` states its postcondition over the call
/// `cap_coeff_u64(c, d)` rather than over `result`, which is the whole point of
/// that site — but nothing pinned `cap_coeff_u64`, so the function the clause is
/// *about* could be rewritten with every test green.
const PINNED_HELPERS: [(&str, &str, &str); 1] = [(
    "cap_coeff_u64",
    "pub fn cap_coeff_u64(c: u64, d: u64) -> u64",
    "{ if c < d { c } else { d } }",
)];

/// Every citation's clause is the one it was reviewed with, and the helpers a
/// clause is stated over are pinned too.
#[test]
fn every_citation_clause_and_the_helpers_it_names_are_pinned() {
    let surface = std::fs::read_to_string(crate_dir().join("src/trust_surface.rs")).unwrap();

    let mut clause_names: Vec<&str> = CITATION_CLAUSES.iter().map(|(f, _)| *f).collect();
    let mut cited: Vec<&str> = CITATION_SITES.iter().map(|(f, _)| *f).collect();
    clause_names.sort_unstable();
    cited.sort_unstable();
    cited.dedup();
    clause_names.dedup();
    assert_eq!(
        clause_names, cited,
        "CITATION_CLAUSES and CITATION_SITES name different functions, so some \
         citation's claim is unpinned"
    );

    // Rows for the same function must be ADJACENT and in clause order; the
    // comparison is the full ordered per-function list, so a clause dropped,
    // added, or reordered in either slot changes it.
    let mut expected: Vec<(&str, Vec<&str>)> = Vec::new();
    for (f, c) in CITATION_CLAUSES {
        match expected.last_mut() {
            Some((lf, v)) if *lf == f => v.push(c),
            _ => expected.push((f, vec![c])),
        }
    }
    for (name, clauses) in expected {
        assert_eq!(
            fn_ensures_clauses(&surface, name),
            clauses,
            "`trust_surface::{name}` no longer claims what its citations were \
             reviewed against. The theorems that discharge it may still exist \
             and still apply -- to weaker statements."
        );
    }
    for (name, signature, body) in PINNED_HELPERS {
        assert_eq!(fn_signature(&surface, name), signature);
        assert_eq!(
            fn_body(&surface, name),
            body,
            "`trust_surface::{name}` is named inside a citation's `ensures` \
             clause, so rewriting it changes what that citation claims"
        );
    }
}

/// The surface holds exactly one Clean island, and nothing in it is compiled
/// away.
///
/// Both are ways to make the pins describe something other than what compiler_consumer
/// reads. A *second* `clean { }` block is kernel-checked alongside the first
/// and can declare an axiom, which would discharge anything, while
/// `island_matches_the_checked_lean_kernel` compares only the first block
/// against the `.lean`. And `#[cfg(any())]` on a pinned function keeps its text
/// in the file for the pins to match while removing it from the compilation
/// the citation is discharged in.
#[test]
fn the_surface_holds_one_island_and_compiles_all_of_it() {
    let surface = std::fs::read_to_string(crate_dir().join("src/trust_surface.rs")).unwrap();

    let islands = surface
        .lines()
        // `starts_with("clean {")` — with the space — was bypassed by opening
        // the second island as `clean{`. Measured: a byte-identical second
        // island written that way left all seventeen island_sync tests green
        // while compiler_consumer kernel-checked it and printed a SECOND
        // "kernel-checked: 1 declaration(s) registered" line. That
        // declaration is in no checked source: not in the .lean, not in
        // `clean check`, not in the exported bundle — and an axiom there
        // would discharge anything. Match the keyword and the brace with
        // arbitrary whitespace (including none) between them.
        .filter(|line| {
            let t = line.trim_start();
            t.strip_prefix("clean")
                .is_some_and(|rest| rest.trim_start().starts_with('{'))
        })
        .count();
    assert_eq!(
        islands, 1,
        "trust_surface.rs opens {islands} Clean islands. Only the first is \
         compared against clean/veripb_kernel.lean, so a second one is \
         unreviewed kernel input -- an `axiom` there discharges anything."
    );

    // `#[cfg(...)]` inside the surface, other than the crate-level gate that
    // keeps the whole module out of a stock build, removes code from the
    // compilation while leaving it in the file.
    let rust = &surface[surface.find("\n}\n").expect("island terminator")..];
    let cfgs: Vec<&str> = rust
        .lines()
        .map(str::trim_start)
        .filter(|line| line.starts_with("#[cfg"))
        .collect();
    assert!(
        cfgs.is_empty(),
        "trust_surface.rs carries {cfgs:?}. A pinned function behind a false \
         `cfg` is text this file matches and code compiler_consumer never sees."
    );
}

#[test]
fn island_body_is_pure_ascii() {
    // A `clean { ... }` island is lexed as Rust token trees, so a non-ASCII
    // byte in it is a hard compile error under compiler_consumer. Catch it here instead.
    let surface = std::fs::read_to_string(crate_dir().join("src/trust_surface.rs")).unwrap();
    let island = island_body(&surface);
    assert!(
        island.is_ascii(),
        "the Clean island must be pure ASCII (Rust token-tree lexing)"
    );
    assert!(!island.contains('`'), "backticks do not lex as Rust tokens");
}

#[test]
fn trust_surface_is_not_part_of_the_stock_build() {
    // A build without the feature (the default) must not read the Trust surface.
    let lib = std::fs::read_to_string(crate_dir().join("src/lib.rs")).unwrap();
    // Exact adjacency, including the `#[rustfmt::skip]` that keeps the
    // formatter off the island file (see the comment at that line).
    let decl = lib
        .split("#[cfg(feature = \"trust-surface\")]\n")
        .nth(1)
        .expect("trust_surface must stay behind an off-by-default cfg");
    let decl: String = decl
        .lines()
        .filter(|l| !l.trim_start().starts_with("//"))
        .take(2)
        .collect::<Vec<_>>()
        .join("\n");
    assert_eq!(
        decl, "#[rustfmt::skip]\npub mod trust_surface;",
        "trust_surface must stay behind an off-by-default cfg, and keep the \
         #[rustfmt::skip] that keeps `targo fmt --check` off the island file"
    );
}

/// Byte offset of the one line that *declares* `pub fn <name>(`.
///
/// Anchored on a line start — the whole line, less indentation, must begin
/// with the signature — and required to be **unique**. Both halves matter,
/// and the second is not belt-and-braces:
///
/// * A plain `src.find("pub fn cap_coeff(")` matches the first *textual*
///   occurrence, comments included. This crate quotes bodies in doc comments
///   as a matter of style, so a line reading
///   `/// pub fn cap_coeff(degree: Coeff, coeff: Coeff) -> Coeff { ... }`
///   above the real function captured the search: the decoy brace-matched to
///   the expected literal, every assertion passed, and the real body could
///   then say `coeff < degree` — behaviour-identical for `min`, so no other
///   test noticed — while the island theorem is stated over `coeff <= degree`.
///   That defeats the only compiler-checked contract on real code here. A
///   `///` line does not survive the line-start anchor.
/// * Uniqueness closes the follow-up: a decoy that *is* at a line start (in a
///   `/* */` block, in a string literal, in an inner module) is no longer a
///   silent capture but a loud ambiguity.
fn fn_decl_offset(src: &str, name: &str) -> usize {
    let sig = format!("pub fn {name}(");
    let mut hits: Vec<(usize, usize)> = Vec::new(); // (byte offset, line number)
    let mut at = 0usize;
    for (n, line) in src.split_inclusive('\n').enumerate() {
        let indent = line.len() - line.trim_start().len();
        if line[indent..].starts_with(&sig) {
            hits.push((at + indent, n + 1));
        }
        at += line.len();
    }
    assert_eq!(
        hits.len(),
        1,
        "expected exactly one line declaring `{sig}`, found {} (at line(s) {:?}). \
         Zero means the function was renamed or reformatted; more than one means \
         the source is ambiguous about which body this test is pinning -- which is \
         precisely how a decoy line hides an edit to the real one.",
        hits.len(),
        hits.iter().map(|(_, n)| *n).collect::<Vec<_>>(),
    );
    hits[0].0
}

/// The *signature* of the named `pub fn`: everything from `pub fn` up to the
/// opening brace, less any `ensures` clause, with whitespace collapsed.
///
/// [`fn_body`] starts at the first `{`, so the parameter and return types sat
/// outside every pin. Retyping `trust_surface::cap_coeff_i64` from `i64` to
/// `u64` therefore left its pinned body byte-identical to
/// `veripb_core_proved::cap_coeff` while making it a different function --
/// an *unsigned* minimum, discharging an island theorem stated over `Int`, and
/// claiming nothing about the `i64` capping the checker performs. The body is
/// only the same computation as the real one if it is reading the same types.
///
/// The `ensures` clause is deliberately excluded: it is checked separately,
/// against the citation table, and folding it in here would make one
/// expectation answer two questions.
fn fn_signature(src: &str, name: &str) -> String {
    let at = fn_decl_offset(src, name);
    let open = at + src[at..].find('{').expect("function has no body");
    let text = &src[at..open];
    let head = match text.find("ensures ") {
        Some(i) => &text[..i],
        None => text,
    };
    head.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The `ensures` clause of the named `pub fn`, whitespace-collapsed, with the
/// `by <theorem>` citation removed.
///
/// [`fn_signature`] stops at the clause and [`fn_body`] starts after it, so the
/// clause itself — the actual *claim* — sat between two pins and inside
/// neither. Weakening `cap_coeff_i64`'s clause to the two upper bounds, the
/// exact pair `trust_surface.rs` documents as insufficient (they are satisfied
/// by a cap returning `i64::MIN`, which makes SATURATE unsound), left every
/// test here green. `scripts/verify-proofs.sh` catches it from the compiler_consumer log,
/// but that needs a toolchain; this needs `cargo test`.
///
/// The `by` is stripped because which theorem discharges the clause is already
/// pinned, per function, by [`CITATION_SITES`]. Splitting the two keeps each
/// expectation answering one question.
fn fn_ensures_clauses(src: &str, name: &str) -> Vec<String> {
    let at = fn_decl_offset(src, name);
    let open = at + src[at..].find('{').expect("function has no body");
    let mut text = &src[at..open];
    let mut out = Vec::new();
    while let Some(i) = text.find("ensures") {
        text = &text[i + "ensures".len()..];
        let end = text.find("ensures").unwrap_or(text.len());
        let seg = &text[..end];
        let clause = match seg.rfind(" by ") {
            Some(j) => &seg[..j],
            None => seg,
        };
        out.push(clause.split_whitespace().collect::<Vec<_>>().join(" "));
        text = &text[end..];
    }
    assert!(!out.is_empty(), "`pub fn {name}` has no `ensures` clause");
    out
}

/// The body of the named `pub fn`, with all whitespace collapsed to single
/// spaces.
///
/// Brace-matched from the first `{` after the signature, so an `ensures`
/// clause between the return type and the body is skipped (it contains no
/// braces) and nested blocks are handled.
fn fn_body(src: &str, name: &str) -> String {
    let at = fn_decl_offset(src, name);
    let open = at + src[at..].find('{').expect("function has no body");
    let mut depth = 0usize;
    let mut end = open;
    for (i, ch) in src[open..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    end = open + i + 1;
                    break;
                }
            }
            _ => {}
        }
    }
    assert!(end > open, "unbalanced braces in `{name}`");
    src[open..end]
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

/// The one compiler-checked contract on real code rests on
/// `trust_surface::cap_coeff_i64` having the *same body* as
/// `veripb_core_proved::cap_coeff` -- the function the checker runs. Nothing
/// enforced that: editing `cap_coeff`'s body to `coeff < degree` left every
/// test green while silently falsifying the headline claim, because the
/// contract is discharged against the copy in `trust_surface.rs`.
///
/// The two are not literally byte-identical (one is formatted across five
/// lines, the others on one), so what is pinned -- and what the docs now say
/// -- is that they are **token-identical**: equal after whitespace collapse.
#[test]
fn the_i64_cap_functions_have_the_body_of_the_real_cap_coeff() {
    let lib = std::fs::read_to_string(crate_dir().join("src/lib.rs")).unwrap();
    let surface = std::fs::read_to_string(crate_dir().join("src/trust_surface.rs")).unwrap();

    let real = fn_body(&lib, "cap_coeff");
    assert_eq!(
        real, "{ if coeff <= degree { coeff } else { degree } }",
        "`cap_coeff` changed shape; re-derive the island theorems before \
         updating this expectation -- they are stated over the `if` term the \
         E6 Select mint produces for exactly this body"
    );
    // `Coeff` is the crate's alias for `i64`; the twins spell the width out,
    // because the island is read by compiler_consumer, which has no alias to follow.
    assert_eq!(
        fn_signature(&lib, "cap_coeff"),
        "pub fn cap_coeff(degree: Coeff, coeff: Coeff) -> Coeff",
        "`cap_coeff` changed signature. The body pin below compares text; text \
         that reads different types is a different function, however identical \
         it looks."
    );

    for name in [
        "cap_coeff_i64",
        "cap_coeff_i64_le_coeff",
        "cap_coeff_i64_le_degree",
        "cap_coeff_i64_le_capcoeff",
    ] {
        assert_eq!(
            fn_body(&surface, name),
            real,
            "`trust_surface::{name}` no longer has the body of \
             `veripb_core_proved::cap_coeff`, so its compiler-checked contract \
             says nothing about the function the checker actually runs -- which \
             is the entire claim the development design notes §4.1 and README make for it"
        );
        assert_eq!(
            fn_signature(&surface, name),
            format!("pub fn {name}(degree: i64, coeff: i64) -> i64"),
            "`trust_surface::{name}` is no longer the `i64` twin of \
             `veripb_core_proved::cap_coeff`. Retyping it to `u64` leaves the \
             body pin above byte-identical while turning the function into an \
             unsigned minimum -- a different computation, discharging an island \
             theorem stated over `Int`, and saying nothing about the capping \
             SATURATE performs. The width is the claim."
        );
    }
}

/// The two rule-guard citations claim something about the checks
/// `weaken_degree` / `multiply` and `guard::fits_i64` actually perform. The
/// compiler proves the claim about the *twin* in `trust_surface.rs`; this test
/// is the other half of the bridge, and it is the half that would rot.
///
/// It pins three things, in increasing order of what a reader would miss:
///
/// 1. the twins' bodies and signatures, so a retype (`i128` to `i64` on the
///    guard, say) cannot leave the text pin below byte-identical;
/// 2. the real predicates in `src/lib.rs`, as text, so an edit to the guard
///    that changes which comparison it makes turns this red rather than
///    quietly falsifying the doc comments in `trust_surface.rs`;
/// 3. the composition, *executed*: `guard::fits_i64` is a conjunction, and
///    all three of its citations — each half on its own twin, and the whole
///    conjunction on `fits_i64_wide` — are claims about the comparisons the
///    real guard makes. The boundary sweep below runs the real function
///    against the two literal comparisons the twins are pinned to, at every
///    value where a wrong bound could hide.
#[test]
fn the_rule_guard_twins_have_the_predicate_of_the_real_guards() {
    let lib = std::fs::read_to_string(crate_dir().join("src/lib.rs")).unwrap();
    let surface = std::fs::read_to_string(crate_dir().join("src/trust_surface.rs")).unwrap();

    // (1) The twins. `CITATION_BODIES` already pins these; repeating the two
    // that matter here keeps the failure message next to the explanation.
    assert_eq!(
        fn_signature(&surface, "fits_i64_lower_wide"),
        "pub fn fits_i64_lower_wide(x: i128) -> bool",
        "the width-guard twin is no longer stated at `Wide` (`i128`). At `i64` \
         the same body is a different claim: `x >= i64::MIN` is vacuous there, \
         and the guard's whole purpose is to be exact at a width the value can \
         still exceed."
    );
    assert_eq!(
        fn_body(&surface, "fits_i64_lower_wide"),
        format!("{{ x >= {} }}", i64::MIN),
        "the width-guard twin no longer compares against `i64::MIN`"
    );
    assert_eq!(
        fn_signature(&surface, "fits_i64_upper_wide"),
        "pub fn fits_i64_upper_wide(x: i128) -> bool",
        "the upper width-guard twin is no longer stated at `Wide` (`i128`)"
    );
    assert_eq!(
        fn_body(&surface, "fits_i64_upper_wide"),
        format!("{{ x <= {} }}", i64::MAX),
        "the upper width-guard twin no longer compares against `i64::MAX`"
    );
    assert_eq!(
        fn_signature(&surface, "fits_i64_wide"),
        "pub fn fits_i64_wide(x: i128) -> bool",
        "the conjunction twin is no longer stated at `Wide` (`i128`)"
    );
    assert_eq!(
        fn_body(&surface, "fits_i64_wide"),
        format!("{{ x >= {} && x <= {} }}", i64::MIN, i64::MAX),
        "the conjunction twin's body is no longer the exact two-sided \
         conjunction `guard_fits_exact` is about — and that body is the whole \
         claim: both operators, both literals, and the connective"
    );
    assert_eq!(
        fn_signature(&surface, "weaken_factor_nonneg"),
        "pub fn weaken_factor_nonneg(w: i64) -> bool",
        "the sign-guard twin is no longer stated at the coefficient width"
    );
    assert_eq!(
        fn_body(&surface, "weaken_factor_nonneg"),
        "{ w >= 0 }",
        "the sign-guard twin no longer tests the sign"
    );

    // (2) The real predicates, as text.
    assert_eq!(
        fn_body(&lib, "fits_i64"),
        "{ x >= Wide::from(Coeff::MIN) && x <= Wide::from(Coeff::MAX) }",
        "`guard::fits_i64` changed shape. The cited twins are its two \
         conjuncts and the conjunction itself; if the real guard is no longer \
         that conjunction, the citations are claims about comparisons the \
         checker does not make."
    );
    // (2b) The real sign-guard LEAF, and the delegation chain from the rules
    // to it. Since the rules route their sign test through
    // `<Coeff as CoeffDomain>::is_nonneg`, the predicate itself is no longer
    // pinned only by text: `factor_nonneg` carries `weaken_factor_sign_exact`
    // on the real body. What still has to be pinned by text is that the rules
    // OPEN with that delegation, and that the delegation reaches the leaf.
    assert_eq!(
        fn_body(&lib, "factor_nonneg"),
        "{ w >= 0 }",
        "`factor_nonneg` no longer tests the sign. It is the body every rule's \
         sign guard reaches at the narrow domain, and `weaken_factor_sign_exact` \
         is cited about THIS comparison."
    );
    assert!(
        lib.contains("fn is_nonneg(x: &Self) -> bool {\n        factor_nonneg(*x)\n    }"),
        "`<Coeff as CoeffDomain>::is_nonneg` no longer delegates to \
         `factor_nonneg`. The rules call the trait method; if it stops \
         reaching the contracted leaf, the contract is a fact about a \
         function the checker no longer runs."
    );
    assert!(
        lib.contains(
            "fn eq_ok(stored: &Self, truth: &Wide) -> bool {\n        \
             guard::eq_ok(*stored, *truth)\n    }"
        ),
        "`<Coeff as CoeffDomain>::eq_ok` no longer delegates to \
         `guard::eq_ok`. `guard::eq_ok` carries the contract that its body IS \
         the island's `eqOkW` -- a SIGN-EXTENDING comparison. Inlining a \
         truncating comparison here instead is the wrap bug that contract \
         exists to catch, and nothing else would see it."
    );
    // ...and the three exact-arithmetic leaves are what `Exact` at `Wide`
    // computes through. A rule that stops going through these methods is a
    // rule whose arithmetic no longer runs a contracted body.
    for (method, leaf) in [
        ("checked_add", "add_degree_wide"),
        ("checked_sub", "sub_degree_wide"),
        ("checked_mul", "mul_coeff_wide"),
    ] {
        assert!(
            lib.contains(&format!(
                "fn {method}(&self, rhs: &Self) -> Option<Self> {{\n        \
                 {leaf}(*self, *rhs)\n    }}"
            )),
            "`<Wide as Exact>::{method}` no longer delegates to `{leaf}`, the \
             leaf carrying the compiler-checked contract. Every rule's exact \
             arithmetic reaches the leaf through this method and nothing else."
        );
    }

    // `fn_body` cannot read these two: both are generic (`pub fn
    // weaken_degree<C: CoeffDomain>`), so the `pub fn <name>(` line it looks
    // for does not exist. The sign check is the first statement of each, and
    // that prefix is what is pinned.
    //
    // MULTIPLY and DIVIDE need `k > 0`, which is `is_nonneg(k) && k != 0`;
    // the `is_nonneg` half is the half a theorem is cited about, and it must
    // be the one that runs.
    for (rule, opening) in [
        (
            "weaken_degree",
            "if !C::is_nonneg(&w) {\n        return Err(GuardError::NonPositiveFactor);",
        ),
        (
            "multiply",
            "if !C::is_nonneg(&k) || k == C::zero() {\n        return Err(GuardError::NonPositiveFactor);",
        ),
        (
            "divide_with",
            "if !C::is_nonneg(&k) || k == C::zero() {\n        return Err(GuardError::NonPositiveFactor);",
        ),
    ] {
        let at = lib
            .find(&format!("pub fn {rule}<C: CoeffDomain>"))
            .unwrap_or_else(|| panic!("`{rule}` is no longer a generic rule in src/lib.rs"));
        // The sign test must be the function's FIRST statement, not merely
        // present somewhere near the top. A windowed `contains` is satisfied
        // by DEAD CODE: `let skip = true; if skip {} else if w < C::zero() {
        // return Err(..); }` keeps the pinned text verbatim while the guard
        // never runs -- measured, and the whole suite stayed green while
        // `weaken_degree(x >= 1, -5)` turned a satisfiable constraint into a
        // contradiction. Slice from the signature's opening brace and require
        // the guard to be what comes next.
        let body_at = at
            + lib[at..]
                .find('{')
                .unwrap_or_else(|| panic!("`{rule}` has no body"));
        let first = lib[body_at + 1..].trim_start();
        assert!(
            first.starts_with(opening),
            "`{rule}` no longer OPENS with the sign check \
             `weaken_factor_sign_exact` is cited about. The kernel hypotheses \
             it discharges are `entails_weaken_checked`'s and \
             `entails_multiply`'s `Int.le 0 _`. The twin's body is \
             `weaken_degree`'s test exactly (negated); `multiply`'s `k <= 0` \
             is stricter than the hypothesis and merely implies it. Without \
             the check in the rule, the contract is a fact about a comparison \
             the checker no longer makes."
        );
    }

    // (3) The composition, executed. `fits_i64` accepts exactly the values the
    // two literal comparisons accept, checked at every boundary and one step
    // either side of each -- which is where an off-by-one bound would live.
    let lower = |x: Wide| x >= Wide::from(i64::MIN);
    let upper = |x: Wide| x <= Wide::from(i64::MAX);
    let mut probes: Vec<Wide> = vec![0, 1, -1, Wide::MIN, Wide::MAX];
    for anchor in [Wide::from(i64::MIN), Wide::from(i64::MAX), 0] {
        for delta in [-2, -1, 0, 1, 2] {
            probes.push(anchor.saturating_add(delta));
        }
    }
    for x in probes {
        assert_eq!(
            guard::fits_i64(x),
            lower(x) && upper(x),
            "`guard::fits_i64({x})` is not the conjunction of the two bounds \
             the trust_surface twins are pinned to"
        );
        // Each cited half on its own, so a failure says which conjunct moved.
        assert!(
            !guard::fits_i64(x) || lower(x),
            "`guard::fits_i64` accepted {x}, which is below `i64::MIN` -- the \
             exact thing `guard_fits_lower_exact` says it never does"
        );
        assert!(
            !guard::fits_i64(x) || upper(x),
            "`guard::fits_i64` accepted {x}, which is above `i64::MAX` -- the \
             exact thing `guard_fits_upper_exact` says it never does"
        );
    }
}

/// The narrowing twin is the real `guard::narrow`, token for token.
///
/// `narrow_wide` carries the first CONSUMER-shape contract in this crate,
/// and the whole value of that contract is that it is a claim about the
/// function the checker actually calls. Nothing else pins that: the
/// citation names `narrow_wide`, the island names `narrowWide`, and both
/// would be perfectly happy discharging against a lookalike that guards or
/// casts differently. So pin the real body here, and pin the ONE
/// substitution the twin is allowed to make.
///
/// The substitution is `fits_i64` -> [`fits_i64_wide`], and it is not a
/// weakening: `fits_i64_wide` is itself a cited twin of `fits_i64`, pinned
/// against it by `the_rule_guard_twins_have_the_predicate_of_the_real_guards`
/// and carrying `guard_fits_exact` — so the guard the twin consults is
/// compiler-proved to decide the same predicate as the guard the real
/// function consults. The chain is: real body == twin body modulo that one
/// name; twin's guard == real guard (proved); twin's whole equation ==
/// `narrowWide` (proved, by the citation this test protects).
#[test]
fn the_narrow_twin_has_the_body_of_the_real_narrow() {
    let lib = std::fs::read_to_string(crate_dir().join("src/lib.rs")).unwrap();
    let surface = std::fs::read_to_string(crate_dir().join("src/trust_surface.rs")).unwrap();

    let real = fn_body(&lib, "narrow");
    assert_eq!(
        real, "{ if fits_i64(x) { Some(x as Coeff) } else { None } }",
        "`guard::narrow` changed shape. Every narrowing site on the \
         soundness path routes through it, and `narrow_wide`'s contract is a \
         claim about THIS body -- if the real one no longer guards, no longer \
         casts, or swaps its arms, the contract is about a function that no \
         longer exists."
    );

    // Both twins, and the single substitution either is allowed to make.
    // `narrow_wide` carries the functional equation (uncited, defeq lane);
    // `narrow_wide_in_range` carries the guarded citation. A contract on a
    // body that has drifted from the real one proves nothing, so both are
    // pinned, and pinned to the SAME text.
    assert_eq!(
        fn_body(&surface, "narrow_wide"),
        fn_body(&surface, "narrow_wide_in_range"),
        "the two narrowing twins have drifted apart; they must be the same \
         body, because they are two halves of one claim about one real \
         function"
    );
    let twin = fn_body(&surface, "narrow_wide");
    assert_eq!(
        twin,
        real.replace("fits_i64(", "fits_i64_wide(")
            .replace("Some(x as Coeff)", "Some(x as i64)"),
        "the narrowing twin is no longer the real `guard::narrow` under the \
         pinned substitutions (`fits_i64` -> `fits_i64_wide`, `Coeff` -> its \
         concrete `i64`). A twin that has drifted proves nothing about the \
         checker."
    );

    // ...and the guard it calls is the compiler-proved twin of the real one,
    // so the substitution above carries a proof rather than an assumption.
    assert_eq!(
        fn_body(&surface, "fits_i64_wide"),
        format!("{{ x >= {} && x <= {} }}", i64::MIN, i64::MAX),
        "`fits_i64_wide` is the guard `narrow_wide` consults; if it drifts, \
         the narrowing twin's guard is no longer the real guard's twin"
    );
}

/// **`impl CoeffDomain for Coeff` must precede `impl Exact for Wide`.**
///
/// Not style. compiler_consumer's E9 in-walk citation discharge — the lane that actually
/// grades an obligation — resolves a clause's program-function calls against
/// the facet table as accumulated so far, and bodies are walked callee-first
/// in impl-block order. `guard::fits_i64` gets its facet record when the first
/// caller reaching it is walked, and that caller is
/// `<Coeff as CoeffDomain>::narrow`. The three exact-arithmetic leaves have
/// `guard::fits_i64(_)` as their clause hypothesis and are pulled in as
/// `<Wide as Exact>::checked_*`'s callees, so with the blocks the other way
/// round the discharge fails closed and all three drop from `2 proved` to
/// `0 proved, 2 unknown`.
///
/// Measured 2026-08-26, and the failure is invisible to everything a reader
/// would normally check: compiler_consumer exits 0 and still prints its
/// `kernel-discharges` note for each leaf, because that note comes from the
/// diagnostic-only E9 *sweep* which runs after the whole walk. Only the
/// per-function verdict line and `wholecrate_proved_floor` see it.
#[test]
fn the_coeff_domain_impl_precedes_the_wide_exact_impl() {
    let lib = std::fs::read_to_string(crate_dir().join("src/lib.rs")).unwrap();
    let coeff = lib
        .find("\nimpl CoeffDomain for Coeff {")
        .expect("`impl CoeffDomain for Coeff` is gone from src/lib.rs");
    let wide = lib
        .find("\nimpl Exact for Wide {")
        .expect("`impl Exact for Wide` is gone from src/lib.rs");
    assert!(
        coeff < wide,
        "`impl Exact for Wide` now precedes `impl CoeffDomain for Coeff`. \
         compiler_consumer walks bodies callee-first in impl-block order, so this order \
         decides whether `guard::fits_i64` has a facet record by the time the \
         three arithmetic leaves' citations are graded in-walk. With it \
         reversed, `add_degree_wide`, `sub_degree_wide` and `mul_coeff_wide` \
         report `0 proved, 2 unknown` -- while compiler_consumer still exits 0 and still \
         prints a `kernel-discharges` note for each of them, because that note \
         is the diagnostic-only post-walk sweep."
    );
}

/// A whole source with every run of whitespace collapsed to one space, so a
/// pin below is about the tokens and not about the formatter.
fn norm(src: &str) -> String {
    src.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// **The exact-width order decisions really run the contracted leaves.**
///
/// [`wide_nonneg`](veripb_core_proved::wide_nonneg) and
/// [`wide_at_least`](veripb_core_proved::wide_at_least) carry contracts cited
/// by `wide_sign_exact` / `wide_le_exact`. Those contracts are worth exactly
/// as much as the claim that the rule bodies REACH them — and until this test
/// existed, nothing checked that.
///
/// The failure mode is silent in every direction one would look. Put
/// `divide_with` back on a bare `prod >= *x && prod < bound` and `mir` back on
/// the trait's own `<`-and-`>=` defaults, and: both leaves still report
/// `2 proved, 0 failed, 0 unknown`, because a contract is about the body it
/// sits on and not about who calls it; `wholecrate_proved_floor` never moves,
/// for the same reason; and every behavioural test stays green, because the
/// two spellings compute the same function. The contracts would then be twins
/// sitting beside the live code — the exact shape this crate has spent its
/// history eliminating — while every number in the ledger still said nine,
/// then eleven, proved contracts on real functions.
///
/// So pin the wiring, at both ends: the two `impl Exact for Wide` methods
/// that delegate to the leaves, the two trait defaults that are spelled in
/// terms of those methods (rather than as their own comparisons), and the
/// three call sites that take the decisions.
#[test]
fn the_exact_order_decisions_route_through_the_contracted_leaves() {
    let lib = norm(&std::fs::read_to_string(crate_dir().join("src/lib.rs")).unwrap());
    let mir = norm(&std::fs::read_to_string(crate_dir().join("src/mir.rs")).unwrap());

    // End one: `<Wide as Exact>` is where the generic decision becomes the
    // concrete-typed leaf. Without these two delegations every call site below
    // runs a comparison no theorem is cited about.
    for (what, text) in [
        (
            "is_nonneg",
            "fn is_nonneg(&self) -> bool { wide_nonneg(*self) }",
        ),
        (
            "at_least",
            "fn at_least(&self, rhs: &Self) -> bool { wide_at_least(*self, *rhs) }",
        ),
    ] {
        assert!(
            lib.contains(text),
            "`<Wide as Exact>::{what}` no longer delegates to the contracted \
             leaf. The leaf keeps its `2 proved` verdict either way -- a \
             contract is about the body it sits on -- so this delegation is \
             the only thing that makes the proof about the code the checker \
             runs. Expected to find: {text}"
        );
    }

    // End two: the trait's own sign/positivity tests must be spelled in terms
    // of the two contracted methods. `<` and `>` have no theorem at this
    // width; `!is_nonneg()` and `at_least(&one())` are the same decisions
    // taken by the comparisons that do.
    for (what, text) in [
        (
            "is_negative",
            "fn is_negative(&self) -> bool { !self.is_nonneg() }",
        ),
        (
            "is_positive",
            "fn is_positive(&self) -> bool { self.at_least(&Self::one()) }",
        ),
    ] {
        assert!(
            lib.contains(text),
            "`Exact::{what}` is no longer spelled through the contracted \
             comparison. Rewriting it as its own `<` or `>` is behaviourally \
             identical and silently drops every MIR sign re-check off the \
             proved leaf. Expected to find: {text}"
        );
    }

    // The three decisions themselves. DIVIDE's two ceiling bounds
    // (`intCeilDiv_ub` / `intCeilDiv_min`)...
    assert!(
        lib.contains("(Some(prod), Some(bound)) => prod.at_least(x) && !prod.at_least(&bound),"),
        "`divide_with`'s ceiling check no longer takes both bounds through \
         `Exact::at_least`. This is the check that rejects a quotient which is \
         not THE ceiling -- upstream defect 4's shape -- and the strict half \
         is the half that rules out an overshooting map."
    );
    assert!(
        !lib.contains("prod >= *x"),
        "`divide_with` has a bare `prod >= *x` again; the ceiling bound is \
         back on an uncontracted comparison"
    );

    // ...and MIR's `intFloorMod_nonneg` / `intFloorMod_lt` pair, on a
    // remainder that has never been narrowed.
    assert!(
        mir.contains("if r.is_negative() || r.at_least(&kw) || witness != *a {"),
        "`mir::checked_remainder`'s two order re-checks are no longer the \
         contracted ones. `r` here is a floor-remainder living only inside the \
         guard arithmetic, which is why these cite the `key128` theorems and \
         not `weaken_factor_sign_exact`."
    );
    assert!(
        !mir.contains("r >= kw"),
        "`mir::checked_remainder` has a bare `r >= kw` again; \
         `intFloorMod_lt` is back on an uncontracted comparison"
    );
    assert!(
        mir.contains("if mapped.is_negative() {"),
        "`mir`'s `mirF_nonneg` re-check on the produced coefficient is gone"
    );
}

/// The contracts that sit on the crate's REAL functions, as
/// **(function, clause, theorem)**.
///
/// These are the ones that matter most and, until this table existed, the
/// ones nothing pinned. Every other citation in this crate sits on a twin in
/// `trust_surface.rs` and is pinned three ways (site, clause, body); the
/// contracts on `lib.rs` itself were guarded only by
/// `wholecrate_proved_floor`, which counts PROVED OBLIGATIONS. That number
/// catches a contract being deleted — the floor drops — but not a contract
/// being WEAKENED: swap a clause for a vacuous one that still discharges
/// three obligations and the floor never moves.
///
/// So pin the claim itself. A contract on a real function is the strongest
/// thing this crate says, and the failure mode it must not have is quietly
/// becoming a weaker sentence that still passes.
///
/// The clause text is normalised to single spaces, exactly as
/// [`fn_attribute_contracts`] extracts it.
const REAL_FUNCTION_CONTRACTS: [(&str, &str, &str); 21] = [
    (
        "fits_i64",
        "(!result || (x >= -9223372036854775808 && x <= 9223372036854775807)) \
         && (result || (x < -9223372036854775808 || x > 9223372036854775807))",
        "guard_fits_exact",
    ),
    // The one UNCITED contract, and the empty theorem field is the POINT:
    // the clause says this body IS the island definition, and definitional
    // equality against the E6-admitted body is the whole proof, so there is
    // no theorem to name. That route now fails loudly when it does not hold
    // (`uncited ensures ... was not discharged`), which is what makes an
    // empty citation legitimate HERE and nowhere else -- see
    // UNCITED_BY_ISLAND_DEFEQ, which is what distinguishes this from a
    // citation someone forgot to write.
    ("eq_ok", "result == eqOkW(machine, truth)", ""),
    (
        "narrow",
        "guard::fits_i64(x) ==> guard::narrow(x) != None",
        "narrowWide_isSome_of_fits",
    ),
    // The three exact-arithmetic leaves. Each is the body
    // `<Wide as Exact>::checked_add` / `_sub` / `_mul` delegates to, and the
    // rules compute through those methods -- so these are contracts on the
    // arithmetic the checker runs, not on twins beside it.
    //
    // Read the clause for exactly what it says: a TOTALITY claim (operands
    // already known to fit `i64` never make the operation refuse), over the
    // kernel's MACHINE layer (`BitVec 128` / `guardFitsW` / `checkedAdd128`).
    // That layer is not yet joined to the rule layer (`entails_add_checked`,
    // stated over `Int` with `fitsI64` / `eqOkB`), so none of these discharges
    // a rule theorem's hypothesis today.
    (
        "add_degree_wide",
        "guard::fits_i64(a) ==> guard::fits_i64(b) ==> add_degree_wide(a, b) != None",
        "checkedAdd128_isSome_of_inI64",
    ),
    (
        "sub_degree_wide",
        "guard::fits_i64(a) ==> guard::fits_i64(b) ==> sub_degree_wide(a, b) != None",
        "checkedSub128_isSome_of_inI64",
    ),
    (
        "mul_coeff_wide",
        "guard::fits_i64(a) ==> guard::fits_i64(b) ==> mul_coeff_wide(a, b) != None",
        "checkedMul128_isSome_of_inI64",
    ),
    // The sign side condition of every scaling rule, on the body
    // `<Coeff as CoeffDomain>::is_nonneg` calls. Unlike the three above, this
    // clause is a COMPLETE characterisation (both directions), so it cannot be
    // satisfied by a constant `false` -- see the doc comment on the function.
    (
        "factor_nonneg",
        "(!result || w >= 0) && (result || w < 0)",
        "weaken_factor_sign_exact",
    ),
    // The two ORDER decisions, at the EXACT-arithmetic width. `factor_nonneg`
    // above decides a sign on a STORED coefficient; these two decide on values
    // that live only inside the guard arithmetic -- a floor-remainder, a
    // `mirF` image, a `k * q` product -- which have not been narrowed and need
    // not fit `i64` at all, so their contracts are stated at `i128` (the
    // `key128` sign-flip order key) and cite the `wide_*` theorems.
    //
    // `<Wide as Exact>::is_nonneg` / `::at_least` are one-line delegations to
    // exactly these, and the trait's `is_negative` / `is_positive` are spelled
    // as `!is_nonneg()` / `at_least(&one())` -- so `divide_with`'s two ceiling
    // bounds and all three of `mir`'s order re-checks run these bodies. Both
    // clauses are COMPLETE characterisations, which is what makes the negated
    // readings legitimate: a one-way implication would say nothing about the
    // `false` branch the call sites also depend on.
    // The two contracts on functions returning a CONSTRAINT rather than a
    // scalar, both in the CLOSURE form -- the signature form cannot bind a
    // projection off an aggregate result. Native-verified only; see
    // UNCITED_NATIVE_ONLY. `pack_constraint` is how EVERY rule packages its
    // result, so each rule's output degree is checked; neither says
    // anything about the terms.
    (
        "pack_constraint",
        "move |ret: &Constraint<Coeff>| ret.degree == d",
        "",
    ),
    (
        "weaken_apply",
        "move |ret: &Constraint<Coeff>| ret.degree == r",
        "",
    ),
    (
        "wide_nonneg",
        "(!result || x >= 0) && (result || x < 0)",
        "wide_sign_exact",
    ),
    (
        "wide_at_least",
        "(!result || a >= b) && (result || a < b)",
        "wide_le_exact",
    ),
    // The four nullary constants, and they are a TIER BELOW every other row
    // in this table -- see UNCITED_NATIVE_ONLY for what that means.
    ("zero", "result == 0", ""),
    ("one", "result == 1", ""),
    ("zero", "result == 0", ""),
    ("one", "result == 1", ""),
    // The `Lit` constructors, which the ADMISSIBLE-COVERAGE gate demanded once
    // struct construction entered the closed fragment. An uncontracted
    // admissible function raises NO obligation, so nothing else in the crate
    // could see they were unproved -- that gate is the only thing that can.
    //
    // `negate` is the one with content: it must flip the SIGN and never the
    // variable, because a `negate` that rewrote `var` would silently change
    // which literal a rule is about. Both theorems are stated over the
    // FLATTENED signature the per-field import is minted at, which is why
    // `negate`'s carries an inert `Bool` binder for `self.negated`.
    ("pos", "result.var == var", "litctor_var_preserved"),
    ("neg", "result.var == var", "litctor_var_preserved"),
    (
        "negate",
        "result.var == self.var",
        "litnegate_var_preserved",
    ),
    (
        "cap_coeff",
        "result <= coeff && result <= degree && (result >= degree || result >= coeff)",
        "capcoeff_i64_min_full",
    ),
    (
        "cap_coeff_wide",
        "result <= coeff && result <= degree && (result >= degree || result >= coeff)",
        "capcoeff_i128_min_full",
    ),
    // SATURATE's per-term step -- the first per-term rule contract on a real
    // function. UNCITED, and listed in UNCITED_NATIVE_ONLY for a STATED reason
    // rather than by omission: the clause is PROVED by the native full verifier
    // and discriminated (the twin body ignoring the cap is refuted on the
    // identical clause), but it cannot be kernel-cited because the citation
    // lane has no sort for a field projection of the result -- a toolchain gap,
    // not a soundness gap. `capcoeff_i64_le_degree` is the theorem waiting for
    // it. ONE comparison, not the full min characterisation, because the
    // three-conjunct form is TRUE and measured falsely refuted by the
    // conjunction defect.
    (
        "sat_term",
        "result.coeff <= degree",
        "satterm_coeff_le_degree",
    ),
];

/// The real functions whose contract legitimately carries NO citation,
/// each with the island definition it discharges against.
///
/// This is deliberately an allowlist and not "an empty theorem field is
/// fine". A forgotten `by` also produces an empty field, and before the
/// toolchain learned to fail loudly on an undischarged uncited clause, such
/// a contract was INERT -- it reported `proved` while the body could be
/// mutated arbitrarily. Naming the definition here means the exemption is a
/// reviewed decision about one function, and the test below checks the
/// clause really names that definition and the definition really exists.
const UNCITED_BY_ISLAND_DEFEQ: [(&str, &str); 1] = [("eq_ok", "eqOkW")];

/// Contracts that are **native-verified only** -- proved by compiler_consumer's own
/// verifier, NOT by a Clean kernel citation and NOT by island definitional
/// equality.
///
/// This is a weaker guarantee than every other row in
/// `REAL_FUNCTION_CONTRACTS`, and it is a separate list precisely so the
/// difference cannot be lost by an empty theorem field looking like the
/// `eq_ok` case. What these carry: compiler_consumer's full verifier discharges the
/// postcondition and *refutes* a wrong one -- perturbing either body to the
/// wrong constant turns the build red with `0 proved, 2 failed` and
/// `verified_counterexample = true`, which is real regression value. What
/// they do NOT carry: a proof term the Clean kernel checked, or one a third
/// party can replay from the bundle.
///
/// Why they cannot be raised to the citation tier, measured rather than
/// assumed: the uncited definitional-equality route declines any clause that
/// names no island definition (`NO-ISLAND-CALL ... uncited defeq route
/// declines the whole function`), so `result == 0` can never reach
/// `downstream proof consumer-citation` however the lookup is keyed. Raising it needs a
/// clause of the form `result == <island def>(..)`, and no island definition
/// of the right nullary carrier exists -- `sextWide` is
/// `BitVec 64 -> BitVec 128`, and a clause call is checked against the
/// callee's declared type and never coerced to it.
const UNCITED_NATIVE_ONLY: [&str; 6] = [
    "zero",
    "one",
    "zero",
    "one",
    "weaken_apply",
    "pack_constraint",
];

/// Every `#[cfg_attr(feature = "trust-surface", trust::ensures(...))]` in a
/// Rust source, as **(function, clause, theorem)** with the clause
/// whitespace-normalised and the ` by <theorem>` suffix split off.
fn fn_attribute_contracts(src: &str) -> Vec<(String, String, String)> {
    let mut out = Vec::new();
    let mut rest = src;
    while let Some(at) = rest.find("trust::ensures(") {
        let after = &rest[at + "trust::ensures(".len()..];
        // Balance the parentheses of the clause payload.
        let mut depth = 1usize;
        let mut end = 0usize;
        for (i, c) in after.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = i;
                        break;
                    }
                }
                _ => {}
            }
        }
        let payload: String = after[..end]
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        // The function this attribute is attached to: the next `fn <name>`.
        let tail = &after[end..];
        let name = tail
            .find("fn ")
            .map(|i| {
                tail[i + 3..]
                    .chars()
                    .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                    .collect::<String>()
            })
            .unwrap_or_default();
        let (clause, theorem) = match payload.rfind(" by ") {
            Some(i) => (
                payload[..i].to_string(),
                payload[i + 4..].trim().to_string(),
            ),
            None => (payload.clone(), String::new()),
        };
        out.push((name, clause, theorem));
        rest = tail;
    }
    out
}

/// The crate's real functions still claim what they were reviewed claiming.
///
/// Deleting one of these contracts is caught by `wholecrate_proved_floor`;
/// WEAKENING one is caught only here.
#[test]
fn every_real_function_contract_is_the_one_it_was_reviewed_with() {
    let lib = std::fs::read_to_string(crate_dir().join("src/lib.rs")).unwrap();
    let found = fn_attribute_contracts(&lib);
    let expected: Vec<(String, String, String)> = REAL_FUNCTION_CONTRACTS
        .iter()
        .map(|(f, c, t)| {
            (
                (*f).to_string(),
                c.split_whitespace().collect::<Vec<_>>().join(" "),
                (*t).to_string(),
            )
        })
        .collect();
    assert_eq!(
        found, expected,
        "the compiler-checked contracts on this crate's REAL functions are not \
         the pinned ones. A contract here is a claim about the body the checker \
         actually runs, so a changed clause is a changed claim, a changed \
         theorem is a different proof, and a removed row is a guarantee that \
         silently stopped existing. Update the table in the same commit that \
         changes the contract, and say in the message what the new claim is."
    );
    // Each cited theorem must exist in the kernel, or the citation is rot.
    let lean = std::fs::read_to_string(crate_dir().join("clean/veripb_kernel.lean")).unwrap();
    for (f, clause, thm) in REAL_FUNCTION_CONTRACTS {
        // An uncited contract is legitimate ONLY on the island-defeq route,
        // where the clause names a `clean { }` definition and the kernel
        // judges the body to BE it. That route fails loudly when it does not
        // hold, so it is a real proof. An uncited clause of any other shape
        // takes the opaque lane and proves nothing -- so the exemption is an
        // explicit allowlist, naming the definition, rather than "the
        // theorem field happened to be empty", which a forgotten `by` also
        // produces.
        if let Some((_, def)) = UNCITED_BY_ISLAND_DEFEQ.iter().find(|(g, _)| *g == f) {
            assert!(
                thm.is_empty(),
                "`{f}` is allowlisted as discharging by island defeq, but it \
                 now carries the citation `{thm}` -- decide which route it \
                 takes and update both places"
            );
            assert!(
                lean.contains(&format!("def {def} ")),
                "`{f}` discharges by defeq against `{def}`, which is not a \
                 definition in clean/veripb_kernel.lean"
            );
            let (_, clause, _) = REAL_FUNCTION_CONTRACTS
                .iter()
                .find(|(g, _, _)| *g == f)
                .expect("row we just matched");
            assert!(
                clause.contains(def),
                "`{f}` is allowlisted against `{def}` but its clause does not \
                 name it: {clause}"
            );
            continue;
        }
        if thm.is_empty() && UNCITED_NATIVE_ONLY.contains(&f) {
            // Native-verified only, and deliberately listed as such. The
            // clause must stay trivial: the exemption is for a constant whose
            // value the native verifier can settle, not a licence for any
            // uncited clause that happens to name a function called `zero`.
            // The exemption is per-clause, not per-name: each allowlisted
            // function's clause is pinned here too, so widening the list
            // cannot quietly license an arbitrary uncited predicate.
            let permitted = clause == "result == 0"
                || clause == "result == 1"
                || clause == "move |ret: &Constraint<Coeff>| ret.degree == r"
                || clause == "move |ret: &Constraint<Coeff>| ret.degree == d";
            assert!(
                permitted,
                "`{f}` is allowlisted as native-verified-only, but its clause \
                 is `{clause}`. That exemption covers the nullary constants, the \
                 ADD/WEAKEN output-degree claims -- and nothing else; anything \
                 richer must cite a theorem."
            );
            continue;
        }
        assert!(
            !thm.is_empty(),
            "the contract on `{f}` cites no theorem; an uncited attribute clause \
             takes the opaque lane and proves nothing"
        );
        assert!(
            lean.contains(&format!("theorem {thm} ")),
            "`{f}` cites `{thm}`, which is not a theorem in clean/veripb_kernel.lean"
        );
    }
}

/// The keywords `clean check` counts a declaration by.
const DECL_KEYWORDS: [&str; 7] = [
    "theorem ",
    "def ",
    "lemma ",
    "abbrev ",
    "instance ",
    "structure ",
    "inductive ",
];

/// Declaration names in the `.lean`, in file order, each paired with whether
/// it sits inside `namespace VeriPbCore` — which is what decides whether it
/// is reachable as `VeriPbCore.<name>`. (The citation-discharging theorems at
/// the end of the file, and the `decide_le_exact` helper they share, are
/// deliberately outside it.)
fn lean_declarations(lean: &str) -> Vec<(String, bool)> {
    let mut inside = false;
    let mut out = Vec::new();
    for line in lean.lines() {
        if line.starts_with("namespace VeriPbCore") {
            inside = true;
        } else if line.starts_with("end VeriPbCore") {
            inside = false;
        } else if let Some(kw) = DECL_KEYWORDS.iter().find(|kw| line.starts_with(**kw)) {
            let name: String = line[kw.len()..]
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '\'')
                .collect();
            out.push((name, inside));
        }
    }
    out
}

/// Declarations in the `.lean`, counted the way `clean check` counts them.
fn lean_declaration_count(lean: &str) -> usize {
    lean_declarations(lean).len()
}

/// Every file of the workspace that can carry a Clean citation, `target/` and
/// `.git/` aside.
///
/// `.rs` was the original sweep, and it was too narrow: the citations that
/// carry the most weight are in `README.md` and the development design notes, where a
/// rotted theorem name is a published claim rather than a comment. `.sh` is
/// here for `scripts/verify-proofs.sh`, which names theorems in the text it
/// prints. A file type this misses is a file type where a false claim is
/// unchecked, so the extension list is deliberately generous rather than
/// minimal.
fn workspace_citation_sources(dir: &std::path::Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).expect("readable directory") {
        let path = entry.expect("readable entry").path();
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        if path.is_dir() {
            if name != "target" && name != ".git" {
                workspace_citation_sources(&path, out);
            }
        } else if path
            .extension()
            .is_some_and(|e| e == "rs" || e == "md" || e == "sh")
        {
            out.push(path);
        }
    }
}

/// **Nothing in the Rust half of this project may cite a Clean theorem that
/// does not exist.**
///
/// A `VeriPbCore.<name>` mention is a claim that the fact stated in Rust is
/// the machine-checked one, and it is the *only* form that claim takes for
/// the ~400 declarations no `ensures` clause cites. Nothing checked those
/// names, and three of them had rotted: `normalize.rs` cited the kernel
/// controls `ctrl_norm_merge` / `ctrl_norm_cancel` / `ctrl_norm_flip`, while
/// the kernel has only the six split forms (`..._terms` / `..._degree`) — so
/// three unit tests advertised a kernel control that was not there. (Those
/// names are written unqualified right here for the obvious reason: this
/// test sweeps its own source too.)
///
/// The sweep is over raw text, deliberately: these names live in doc
/// comments, in `//` comments and in prose far more often than in code, and a
/// gate that only looked at code would miss every one of the three.
#[test]
fn every_clean_name_the_rust_sources_cite_is_a_kernel_declaration() {
    let lean = std::fs::read_to_string(crate_dir().join("clean/veripb_kernel.lean")).unwrap();
    let decls = lean_declarations(&lean);
    let namespaced: std::collections::BTreeSet<&str> = decls
        .iter()
        .filter(|(_, inside)| *inside)
        .map(|(n, _)| n.as_str())
        .collect();
    assert!(
        namespaced.len() > 300,
        "only {} declarations parsed out of clean/veripb_kernel.lean -- the \
         parser has lost the file, and a gate that recognises nothing accepts \
         everything",
        namespaced.len()
    );

    let mut sources = Vec::new();
    workspace_citation_sources(&crate_dir().join(".."), &mut sources);
    sources.sort();
    assert!(
        sources.len() > 50,
        "only {} Rust sources found; the sweep is not reaching the workspace",
        sources.len()
    );

    // Both spellings. `VeriPbCore.` is Clean's own; `VeriPbCore::` is what a
    // Rust author reaches for out of habit, and it used to walk straight past
    // the gate.
    const MARKS: [&str; 2] = ["VeriPbCore.", "VeriPbCore::"];
    let mut dangling: Vec<String> = Vec::new();
    let mut seen = 0usize;
    for path in &sources {
        let text = std::fs::read_to_string(path).expect("readable citation source");
        let lines: Vec<&str> = text.lines().collect();
        for (n, line) in lines.iter().enumerate() {
            for mark in MARKS {
                let mut rest = *line;
                while let Some(i) = rest.find(mark) {
                    rest = &rest[i + mark.len()..];
                    let mut name: String = rest
                        .chars()
                        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '\'')
                        .collect();
                    // A name wrapped onto the continuation of a doc comment:
                    // `VeriPbCore.` ends the line and the identifier starts the
                    // next. Reading line by line silently dropped these.
                    if name.is_empty() && rest.trim().is_empty() {
                        if let Some(next) = lines.get(n + 1) {
                            let body = next
                                .trim_start()
                                .trim_start_matches("///")
                                .trim_start_matches("//!")
                                .trim_start_matches("//")
                                .trim_start_matches('*')
                                .trim_start();
                            name = body
                                .chars()
                                .take_while(|c| {
                                    c.is_ascii_alphanumeric() || *c == '_' || *c == '\''
                                })
                                .collect();
                        }
                    }
                    if name.is_empty() {
                        continue;
                    }
                    seen += 1;
                    if namespaced.contains(name.as_str()) {
                        continue;
                    }
                    // A split-form rename is the failure mode that happened;
                    // say so instead of leaving the reader to grep the .lean.
                    let near: Vec<&str> = namespaced
                        .iter()
                        .copied()
                        .filter(|d| d.starts_with(name.as_str()) || name.starts_with(d))
                        .collect();
                    let hint = if near.is_empty() {
                        String::new()
                    } else {
                        format!(" (did you mean {}?)", near.join(" / "))
                    };
                    dangling.push(format!(
                        "{}:{}: {mark}{name}{hint}",
                        path.strip_prefix(crate_dir().join("..")).unwrap().display(),
                        n + 1,
                    ));
                }
            }
        }
    }
    assert!(
        seen > 50,
        "only {seen} `VeriPbCore.<name>` mentions found across {} sources -- the \
         extractor is broken, and a gate that finds nothing to check passes \
         vacuously",
        sources.len()
    );
    assert!(
        dangling.is_empty(),
        "these Rust sources cite Clean declarations that do not exist in \
         clean/veripb_kernel.lean (or that are declared outside `namespace \
         VeriPbCore`, so `VeriPbCore.<name>` does not name them):\n  {}\n\
         Each one is a claim that a Rust item mirrors a machine-checked fact, \
         with no machine-checked fact behind it.",
        dangling.join("\n  ")
    );
}

/// Backtick-quoted tokens that look like a Clean declaration whose name has
/// rotted, but are not citations at all.
///
/// Kept as an explicit list with a reason each, and checked to be *minimal* by
/// [`the_lookalike_allowlist_is_still_needed`] — an entry that stops being
/// flagged, or whose file stops containing it, fails rather than lingering.
///
/// Each entry is scoped to the file it is allowed in, not global:
/// `ctrl_norm_merge` is a legitimate mention in this file, which documents the
/// rot, and a rotted citation anywhere else. A global entry would excuse the
/// second along with the first — which it did, until this was scoped.
const NOT_CLEAN_CITATIONS: &[(&str, &str, &str)] = &[
    (
        "ctrl_norm_cancel",
        "veripb-core-proved/tests/island_sync.rs",
        "named in this file's own documentation as one of the three citations \
         that had rotted; the gate sweeps its own source",
    ),
    (
        "ctrl_norm_flip",
        "veripb-core-proved/tests/island_sync.rs",
        "as above",
    ),
    (
        "ctrl_norm_merge",
        "veripb-core-proved/tests/island_sync.rs",
        "as above",
    ),
];

/// **A bare Clean name may not have rotted either.**
///
/// The qualified gate above covers `VeriPbCore.<name>`, which is a minority of
/// how this crate refers to the kernel: most mentions are backtick-quoted bare
/// names in prose and doc comments, and *none* of them was checked. Inserting
/// the truncated `ctrl_norm_merge` — one of the three names that really had
/// rotted, and the reason the qualified gate exists — left the whole suite
/// green.
///
/// Gating bare names in general is not possible: `add_constraint` is a Rust
/// function, not a broken citation, and no rule can read intent out of prose.
/// What *is* decidable is the shape rot actually takes here. The kernel's
/// refactors split declarations into suffixed forms (`ctrl_norm_merge` became
/// `ctrl_norm_merge_terms` and `ctrl_norm_merge_degree`), so a citation rots by
/// becoming a strict prefix of a declaration — or, when a name is absorbed, by
/// having one as a strict prefix. Both are flagged, at `_` boundaries so that
/// `add` and `add_constraint` are not confused for one another.
///
/// This does **not** catch an invented name unrelated to any declaration, and
/// no claim is made that it does. It catches the rot that happened, and the
/// class it belongs to.
#[test]
fn every_bare_clean_name_is_a_kernel_declaration_or_declared_not_to_be() {
    let lean = std::fs::read_to_string(crate_dir().join("clean/veripb_kernel.lean")).unwrap();
    let decls = lean_declarations(&lean);
    // EVERY declaration, not just the ones inside `namespace VeriPbCore`.
    // The rot question this gate asks is "is this backticked token itself a
    // declaration, or only a longer form of one?", and for that a declaration
    // counts wherever it sits. Filtering to the namespace made every name in
    // the tail region -- the citation-discharging theorems and their whole
    // supporting development, which are deliberately OUTSIDE the namespace --
    // unrecognisable, so documenting one of them (`fitsI64_of_bounds`, a real
    // theorem, next to the `fitsI64` it inverts) was reported as rot. A gate
    // that cries wolf on true names teaches its readers to reach for the
    // suppression list, which is the one thing it must never do.
    let namespaced: std::collections::BTreeSet<&str> =
        decls.iter().map(|(n, _)| n.as_str()).collect();
    assert!(
        namespaced.len() > 300,
        "only {} declarations parsed; a gate that recognises nothing accepts \
         everything",
        namespaced.len()
    );

    let mut sources = Vec::new();
    workspace_citation_sources(&crate_dir().join(".."), &mut sources);
    sources.sort();
    let mut rotted: Vec<String> = Vec::new();
    for path in &sources {
        let relative = path
            .strip_prefix(crate_dir().join(".."))
            .unwrap()
            .to_string_lossy()
            .into_owned();
        let text = std::fs::read_to_string(path).expect("readable citation source");
        for (n, line) in text.lines().enumerate() {
            for token in backticked(line) {
                let allowed = NOT_CLEAN_CITATIONS
                    .iter()
                    .any(|(t, file, _)| *t == token && *file == relative);
                if !looks_like_a_split_rename(&token, &namespaced) || allowed {
                    continue;
                }
                let opens = |r: &str| {
                    r.starts_with('_') || r.chars().next().is_some_and(|c| c.is_ascii_uppercase())
                };
                let near: Vec<&str> = namespaced
                    .iter()
                    .copied()
                    .filter(|d| {
                        d.strip_prefix(token.as_str()).is_some_and(opens)
                            || token.strip_prefix(*d).is_some_and(opens)
                    })
                    .collect();
                rotted.push(format!(
                    "{relative}:{}: `{token}` (kernel has {})",
                    n + 1,
                    near.join(" / "),
                ));
            }
        }
    }
    assert!(
        rotted.is_empty(),
        "these backtick-quoted names differ from a kernel declaration only by a \
         trailing `_`-separated segment, which is exactly how a citation rots \
         when the kernel splits a declaration:\n  {}\n\
         Either correct the name, or add it to `NOT_CLEAN_CITATIONS` with a \
         reason if it is not a citation at all.",
        rotted.join("\n  ")
    );
}

/// Every allowlist entry is still doing work.
#[test]
fn the_lookalike_allowlist_is_still_needed() {
    let lean = std::fs::read_to_string(crate_dir().join("clean/veripb_kernel.lean")).unwrap();
    let decls = lean_declarations(&lean);
    let namespaced: std::collections::BTreeSet<&str> = decls
        .iter()
        .filter(|(_, inside)| *inside)
        .map(|(n, _)| n.as_str())
        .collect();
    let mut sources = Vec::new();
    workspace_citation_sources(&crate_dir().join(".."), &mut sources);
    sources.sort();
    for (token, file, reason) in NOT_CLEAN_CITATIONS {
        assert!(
            looks_like_a_split_rename(token, &namespaced),
            "`{token}` is allowlisted as a Clean-name lookalike ({reason}), but \
             it no longer resembles any declaration -- drop the entry"
        );
        let path = crate_dir().join("..").join(file);
        let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
            panic!("`{token}` is allowlisted in {file} ({reason}), which cannot be read: {e}")
        });
        assert!(
            text.contains(&format!("`{token}`")),
            "`{token}` is allowlisted in {file} ({reason}) but no longer appears \
             there -- drop the entry, or move it to the file that needs it"
        );
        assert!(
            sources.iter().any(|p| p == &path),
            "`{token}` is allowlisted in {file}, which the sweep does not visit, \
             so the entry excuses nothing"
        );
    }
}

/// The backtick-quoted tokens of one line, `` `like_this` ``.
fn backticked(line: &str) -> Vec<String> {
    line.split('`')
        .skip(1)
        .step_by(2)
        .filter(|t| {
            !t.is_empty()
                && t.chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
        })
        .map(str::to_string)
        .collect()
}

/// `token` is not a declaration, but some declaration extends it by a whole
/// further segment, or vice versa.
///
/// A segment boundary is an underscore *or* a capital letter, because the
/// kernel names in two styles: `ctrl_norm_merge_terms` splits on `_`, and a
/// name like `capCoeff` splits on case, so a longer form of it that added a
/// further capitalised word would be rot. The `_`-only rule missed every
/// camelCase name, which is most of the kernel's own vocabulary.
fn looks_like_a_split_rename(token: &str, namespaced: &std::collections::BTreeSet<&str>) -> bool {
    if namespaced.contains(token) || token.len() < 4 {
        return false;
    }
    /// `rest` opens a new segment: it starts a new `_`-separated word, or a new
    /// camelCase word.
    fn opens_a_segment(rest: &str) -> bool {
        rest.starts_with('_') || rest.chars().next().is_some_and(|c| c.is_ascii_uppercase())
    }
    // Only tokens that already look like a kernel *theorem* name are
    // considered, so an ordinary English word in prose is never a candidate.
    //
    // The initial must be lower-case, which is the line between the two things
    // a shared name can mean here. Theorems and definitions are `snake_case` or
    // `lowerCamel` (`capCoeff`, `entails_saturate`), and a longer version of one
    // is rot. Types are `UpperCamel` (`Lit`, `Constraint`, `Term`) and are
    // *deliberately* mirrored by Rust types of the same name, so `LitData`
    // extending `Lit` is the correspondence working, not a broken citation.
    let plausible = token.chars().next().is_some_and(|c| c.is_ascii_lowercase())
        && (token.contains('_') || token.chars().any(|c| c.is_ascii_uppercase()));
    if !plausible {
        return false;
    }
    namespaced.iter().any(|d| {
        d.chars().next().is_some_and(|c| c.is_ascii_lowercase())
            && (d.strip_prefix(token).is_some_and(opens_a_segment)
                || token.strip_prefix(*d).is_some_and(opens_a_segment))
    })
}

/// `ensures … by <theorem>` citation sites in the Rust half of the surface,
/// as **(function, theorem)** in source order.
///
/// Read per *function* rather than per line: the slice from a `pub fn` line
/// to the `{` that opens its body is the whole signature (a clause too long
/// for one line puts its `by` on a continuation line, and that continuation
/// is inside this slice), it cannot contain a comment — doc comments sit
/// above the `pub fn` line — and the `by` it ends with therefore belongs to
/// *this* function and no other.
fn citation_sites(surface: &str) -> Vec<(String, String)> {
    let rust = &surface[surface.find("\n}\n").expect("island terminator")..];
    let mut out = Vec::new();
    let mut at = 0usize;
    for line in rust.split_inclusive('\n') {
        let indent = line.len() - line.trim_start().len();
        at += line.len();
        let Some(rest) = line[indent..].strip_prefix("pub fn ") else {
            continue;
        };
        let name: String = rest
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        let start = at - line.len() + indent;
        let open = start
            + rust[start..]
                .find('{')
                .unwrap_or_else(|| panic!("`pub fn {name}` has no body"));
        let sig = &rust[start..open];
        if !sig.contains("ensures ") {
            continue;
        }
        // EVERY `by <theorem>` in the signature, in clause order — a function
        // may carry several `ensures ... by ...` contracts (the checked
        // leaves carry an op-discriminating one AND a hypothesis-guarded
        // one), and a citation dropped from EITHER slot must change this
        // list.
        let mut tail = sig;
        while let Some((_, rest)) = tail.split_once(" by ") {
            let theorem: String = rest
                .trim_start()
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            assert!(
                !theorem.is_empty(),
                "`pub fn {name}` has a `by` with no Clean theorem name after it"
            );
            out.push((name.clone(), theorem));
            tail = rest;
        }
    }
    out
}

/// The public claims about kernel size are load-bearing -- they are how a
/// reader calibrates "the kernel is machine-checked" -- and they have drifted
/// silently more than once (332/336/339 against an actual 417). Derive them
/// from the sources and fail here, under stock cargo, rather than waiting for
/// someone with both toolchains to notice.
///
/// The obligation *measurement* is deliberately not made here: it is not
/// derivable without running compiler_consumer, and `scripts/verify-proofs.sh` owns it,
/// gating against `island_proved_obligations` in
/// `clean/proved-core-expected.txt`. What IS checked here is that the prose
/// does not restate a different total from the pin -- the figure is not
/// written out in this comment for the same reason.
#[test]
fn the_public_declaration_and_citation_counts_are_the_measured_ones() {
    let lean = std::fs::read_to_string(crate_dir().join("clean/veripb_kernel.lean")).unwrap();
    let surface = std::fs::read_to_string(crate_dir().join("src/trust_surface.rs")).unwrap();
    let repo = crate_dir().join("..");
    let read = |p: &str| std::fs::read_to_string(repo.join(p)).unwrap();

    let decls = lean_declaration_count(&lean);
    let cites = citation_sites(&surface).len();

    // The island is the stripped `.lean` (pinned by the test above), so compiler_consumer
    // registers exactly this many declarations -- one number, not two.
    let docs = read("the development design notes");
    for phrase in [
        format!("{decls} passed, 0 failed"),
        format!("{decls} declaration(s) registered"),
        format!("{decls} declarations"),
        format!("all **{cites}** citations"),
    ] {
        assert!(
            docs.contains(&phrase),
            "the development design notes does not say `{phrase}`; the kernel has {decls} \
             declarations and {cites} citation sites, measured from the sources"
        );
    }
    // The crate-level `//!` header is the first thing a `cargo doc` reader
    // sees, and it is the copy that drifted furthest (332 against 417).
    assert!(
        std::fs::read_to_string(crate_dir().join("src/lib.rs"))
            .unwrap()
            .contains(&format!("{decls} declarations, 0 failed")),
        "veripb-core-proved/src/lib.rs's crate header quotes a stale declaration count; \
         it is {decls}"
    );

    // The obligation total cannot be measured without compiler_consumer, but it CAN be
    // kept from drifting: `scripts/verify-proofs.sh` gates the measurement
    // against `island_proved_obligations`, and every figure written into prose
    // has to be that one. This is what was missing when the total went 25 to
    // 29 and three comments kept saying 25.
    let pins = std::fs::read_to_string(crate_dir().join("clean/proved-core-expected.txt")).unwrap();
    let obligations = pins
        .lines()
        .find_map(|l| l.strip_prefix("island_proved_obligations="))
        .expect("clean/proved-core-expected.txt has no `island_proved_obligations` pin")
        .trim();
    // A window around the pin rather than every integer: `N/N` and
    // `N proved / N` are specific enough shapes that a false positive is
    // unlikely, but "3/3" and the like do appear in unrelated prose, so the
    // scan is confined to totals near the blessed one -- which is where a
    // stale figure actually lands.
    let blessed: i64 = obligations
        .parse()
        .expect("island_proved_obligations is not a number");
    let window: Vec<String> = ((blessed - 8).max(10)..=(blessed + 8))
        .filter(|n| *n != blessed)
        .map(|n| n.to_string())
        .collect();
    let this_file = read("veripb-core-proved/tests/island_sync.rs");
    for (file, text) in [
        ("the development design notes", &docs),
        ("veripb-core-proved/tests/island_sync.rs", &this_file),
        ("veripb-core-proved/src/trust_surface.rs", &surface),
    ] {
        let stale: Vec<&String> = window
            .iter()
            .filter(|n| {
                text.contains(&format!("{n}/{n}")) || text.contains(&format!("{n} proved / {n}"))
            })
            .collect();
        assert!(
            stale.is_empty(),
            "{file} writes an obligation total of {stale:?}; the blessed one is \
             `island_proved_obligations={obligations}` in \
             clean/proved-core-expected.txt. Prefer referring to the pin by \
             name to restating the number."
        );
    }
}

/// The `<!-- census:begin -->` paragraph of the development design notes §7.4 must be
/// the census `tests/kernel_verify_expected.txt` actually spells.
///
/// This is a *regeneration* gate, not a phrase-containment one. Containment
/// catches a stale integer but cannot catch an extra enumerated row, and an
/// extra row is precisely how this paragraph broke: it carried
/// "1 on variable-form MIR" — a category no corpus instance has ever produced
/// — alongside four integers that were each wrong by the time anyone read
/// them. So the whole paragraph is rebuilt here from the snapshot and
/// compared; on a mismatch the failure prints the paragraph to paste back.
///
/// Two deliberate choices:
///
/// * The `NOT composed (...)` parser **panics** on a shape it does not
///   recognise rather than skipping the line. A silently unparsed line would
///   shrink the census instead of failing it.
/// * An obstacle reason with no prose clause in `CENSUS_PROSE` is a hard
///   failure. That is the hook that makes a *new* non-composition reason
///   impossible to omit from the doc, which is the half a count-only gate
///   would miss.
///
/// Home: this file rather than `tests/kernel_verify.rs`, because it needs
/// only two file reads — no corpus run, no `--release` binary, no toolchain.
#[test]
fn the_composition_census_in_the_docs_is_the_measured_one() {
    /// Obstacle reason -> the clause §7.4 spells for it, in the order the
    /// paragraph lists them. The count is prefixed, so the first entry reads
    /// "35 enumeration/bounds proofs ..." and the rest "7 on a ...".
    const CENSUS_PROSE: &[(&str, &str)] = &[
        (
            "solution-exclusion-unmodelled",
            "enumeration/bounds proofs resting on excluded solutions \
             (`solution-exclusion-unmodelled`)",
        ),
        (
            "strengthening-subproof-unmodelled",
            "on a `qed`-stored strengthening constraint \
             (`strengthening-subproof-unmodelled`)",
        ),
        (
            "red-witness-unmodelled",
            "on a witnessed `red` (`red-witness-unmodelled`)",
        ),
        (
            "red-witness-touches-database",
            "on a `red` whose witness moves a stored constraint \
             (`red-witness-touches-database`)",
        ),
        (
            "assertion-unverified",
            "on an assertion (`assertion-unverified`)",
        ),
        (
            "red-goal-discharge-not-kernel-verified",
            "on a `red` whose proofgoal discharges were not all kernel-verified \
             (`red-goal-discharge-not-kernel-verified`)",
        ),
        (
            "red-witness-later-preserved",
            "on a `red` whose witness variable later joined the preserved set \
             (`red-witness-later-preserved`)",
        ),
    ];

    let repo = crate_dir().join("..");
    let snapshot = std::fs::read_to_string(repo.join("tests/kernel_verify_expected.txt")).unwrap();

    let compose: Vec<&str> = snapshot
        .lines()
        .filter(|l| l.contains("[compose]: kernel-compose: "))
        .collect();
    let total = compose.len();
    let composed = compose
        .iter()
        .filter(|l| l.contains("kernel-compose: COMPOSED"))
        .count();
    let no_refutation = compose
        .iter()
        .filter(|l| l.contains("no refutation conclusion to compose"))
        .count();

    let mut obstacles: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
    for line in compose.iter().filter(|l| l.contains("NOT composed")) {
        let why = line
            .split_once("NOT composed (")
            .and_then(|(_, rest)| rest.split_once(')'))
            .map(|(why, _)| why)
            .unwrap_or_else(|| panic!("unrecognised `NOT composed` line shape:\n{line}"));
        // Two shapes, and both must be named rather than skipped. A SLOT
        // obstacle says which id had no justification; a WHOLE-RUN obstacle
        // (`mixed-verdict-inductions-unmodelled`) is about the run's shape and
        // names no id, because there is no single slot at fault -- every slot
        // may be justified while no single theorem covers their combination.
        // A reason with neither shape still panics: the point of this parser
        // is that a new obstacle cannot shrink the census by going unread.
        let reason = match why.strip_prefix("no kernel-justified slot at id ") {
            Some(rest) => rest.split_once(": ").map(|(_, reason)| reason),
            None => CENSUS_PROSE.iter().any(|(r, _)| *r == why).then_some(why),
        }
        .unwrap_or_else(|| {
            panic!(
                "the census parser does not recognise the non-composition obstacle \
                 `{why}`; teach it that shape (and give it a clause in CENSUS_PROSE) \
                 rather than letting the census quietly shrink"
            )
        });
        *obstacles.entry(reason).or_default() += 1;
    }
    let not_composed: usize = obstacles.values().sum();

    // Fail loudly on a parse miss instead of silently reporting a smaller
    // corpus than the snapshot holds.
    assert_eq!(
        total,
        composed + no_refutation + not_composed,
        "the `kernel-compose:` lines do not partition the corpus: {total} lines, \
         {composed} composed + {no_refutation} without a refutation conclusion + \
         {not_composed} not composed"
    );
    assert!(total > 0, "no `[compose]` lines in the snapshot");

    let clauses: Vec<String> = CENSUS_PROSE
        .iter()
        .filter_map(|(reason, prose)| {
            obstacles.remove(reason).map(|n| {
                format!(
                    "{n} {}",
                    prose.split_whitespace().collect::<Vec<_>>().join(" ")
                )
            })
        })
        .collect();
    assert!(
        obstacles.is_empty(),
        "the corpus produces non-composition reasons with no clause in CENSUS_PROSE: \
         {obstacles:?} — add each one to the table and to the development design notes §7.4, so a \
         new hole cannot enter the census by silence"
    );
    let breakdown = match clauses.split_last() {
        Some((last, rest)) if !rest.is_empty() => format!("{} and {last}", rest.join(", ")),
        _ => clauses.join(""),
    };
    let refutations = composed + not_composed;
    // The all-composing case needs its own sentence. The breakdown clause is
    // built from the obstacles, and with none it rendered as "The 0 that do
    // not break down as ." -- which is not English and, worse, reads like a
    // truncation rather than the strongest statement this file can make.
    let tail = if not_composed == 0 {
        "Every one of them does.".to_string()
    } else {
        format!("The {not_composed} that do not break down as {breakdown}.")
    };
    let expected = format!(
        "Over the shipped corpus, {refutations} of the {total} accepted instances reach a \
         refutation conclusion at all (the rest conclude `NONE`, `SAT`, or a bound met by a \
         solution), and **{composed} of those {refutations} compose end to end**. {tail}"
    );

    let docs = std::fs::read_to_string(repo.join("the development design notes")).unwrap();
    let fenced = docs
        .split_once("<!-- census:begin -->")
        .and_then(|(_, rest)| rest.split_once("<!-- census:end -->"))
        .map(|(body, _)| body)
        .expect("the development design notes has lost its `<!-- census:begin -->` fence");
    assert_eq!(
        fenced.split_whitespace().collect::<Vec<_>>().join(" "),
        expected,
        "the development design notes §7.4's composition census is not the one \
         tests/kernel_verify_expected.txt spells. Replace the text between the \
         `census:begin`/`census:end` fences with:\n\n{expected}\n"
    );
}

/// **`guard` is a complete module of a real program whose every definition is
/// machine-proved.**
///
/// This is the property the whole exercise is aimed at, and it holds today for
/// exactly one module: every function in `mod guard` carries a
/// compiler-checked `ensures` that compiler_consumer discharges against the Clean kernel.
/// It is worth gating rather than merely observing, because it is the kind of
/// claim that decays silently — one helper added without a contract and the
/// module is no longer exhaustively proved, while nothing else in the tree
/// notices, since a function with no contract simply has no obligations.
///
/// The bar is deliberately "carries a contract", not "carries a *citation*":
/// `guard::eq_ok` is uncited on purpose (its clause says the body IS the island
/// definition `eqOkW`, and definitional equality is the whole proof), and
/// `UNCITED_BY_ISLAND_DEFEQ` is what keeps that from being an excuse anywhere
/// else.
///
/// Scope, stated so the test is not read as more than it is: `guard` is the
/// width-guard layer, not a checking rule. The rules themselves call these
/// three and are not proved.
#[test]
fn every_definition_in_the_guard_module_is_contracted() {
    let lib = std::fs::read_to_string(crate_dir().join("src/lib.rs")).unwrap();
    let start = lib
        .find("\npub mod guard {")
        .expect("src/lib.rs must declare `pub mod guard`");
    // The module ends at the first column-0 `}`.
    let rest = &lib[start + 1..];
    let end = rest
        .find("\n}\n")
        .expect("`pub mod guard` must be closed at column 0");
    let module = &rest[..end];

    let fns: Vec<&str> = module
        .lines()
        .filter_map(|l| l.trim_start().strip_prefix("pub fn "))
        .filter_map(|r| r.split(['(', '<']).next())
        .collect();
    assert!(
        fns.len() >= 3,
        "found only {} function(s) in `mod guard` -- the parser has lost the \
         module and this test would be vacuous: {fns:?}",
        fns.len()
    );

    let contracted: Vec<&str> = REAL_FUNCTION_CONTRACTS.iter().map(|(f, _, _)| *f).collect();
    let missing: Vec<&&str> = fns.iter().filter(|f| !contracted.contains(f)).collect();
    assert!(
        missing.is_empty(),
        "`mod guard` is the one module in this crate whose every definition is \
         machine-proved, and these no longer are: {missing:?}.\n\
         Either give them a compiler-checked `ensures` (and add them to \
         REAL_FUNCTION_CONTRACTS), or move them out of `guard` -- but do not \
         leave the module claiming a completeness it no longer has. The claim \
         is repeated in README.md and the development design notes"
    );

    // The number is quoted in prose; keep the two from drifting apart.
    assert_eq!(
        fns.len(),
        3,
        "`mod guard` now has {} definitions, not 3. The docs say \"all three\"; \
         update them together with this number.",
        fns.len()
    );
}

/// Every rule packages its result through the CONTRACTED `pack_constraint`.
///
/// This is a source-text pin, and it exists because the compiler cannot see
/// the wiring. Measured: a contract constrains the callee's BODY, not who
/// calls it or with what. Routing all seven rules through `C::pack` moved no
/// gated magnitude at all -- `proved` stayed at 114 and `incomplete` at 400 --
/// so reverting any of them to a bare `Constraint { terms, degree }` literal
/// would leave compiler_consumer byte-identically green and every pin satisfied.
///
/// Read the guarantee at its real strength: `pack_constraint` says the
/// constraint handed back carries the degree it was GIVEN. That the rule
/// computed the right degree to give it is a separate claim, and not this
/// one. What this pins is only that the packaging step stays on the
/// contracted path.
#[test]
fn every_rule_packages_its_result_through_the_contracted_leaf() {
    let lib = std::fs::read_to_string(crate_dir().join("src/lib.rs")).unwrap();
    let mir = std::fs::read_to_string(crate_dir().join("src/mir.rs")).unwrap();

    let lib_sites = lib.matches("C::pack(").count();
    let mir_sites = mir.matches("C::pack(").count();
    assert_eq!(
        (lib_sites, mir_sites),
        (5, 2),
        "the rules route {lib_sites} + {mir_sites} constructions through the \
         contracted packager, expected 5 + 2 (ADD, MULTIPLY, DIVIDE, SATURATE, \
         NEGATE in lib.rs; MIR and MIR-variable in mir.rs).\n\
         If a rule was added, route it through `CoeffDomain::pack` and raise \
         this count. If one was un-routed, that is the regression this test \
         exists for -- no gated magnitude would have noticed."
    );

    // And no rule may go back to building the literal directly. The two
    // legitimate literal sites are `pack_constraint` itself and the trait's
    // default body; `literal_axiom` builds a constant, not a rule result.
    for (name, src) in [("lib.rs", &lib), ("mir.rs", &mir)] {
        assert!(
            !src.contains("Ok(Constraint { terms, degree })"),
            "{name} still builds a rule result as a bare `Constraint` literal; \
             route it through `CoeffDomain::pack` so the packaging step stays \
             on the contracted path"
        );
    }
}
