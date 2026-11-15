// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One problem per construct. Every row's Carcara outcome was measured with
//! `carcara parse` (carcara 1.1.0, git 9a352ee) on the problem alone: each
//! REFUSED row stops Carcara's parser with the quoted error, and each
//! ACCEPTED row parses. AY's frontend reads every row.

use super::AuthoredProblemSurface;

pub(super) fn gap_of(problem: &str) -> Option<String> {
    let commands = ay_frontend::parse(problem).expect("AY parses the fixture");
    let mut surface = AuthoredProblemSurface::default();
    for command in &commands {
        surface.observe(command);
    }
    surface.gap().map(str::to_string)
}

const DT: &str = "(set-logic ALL)(declare-datatype E ((A) (B (b Int))))(declare-const e E)";
const VEC: &str = "(set-logic ALL)(declare-datatype Vec ((mkVec (len Int))))(declare-const v Vec)";
const LIST: &str = "(set-logic ALL)\
    (declare-datatype L (par (T) ((nil) (cons (hd T) (tl (L T))))))(declare-const l (L Int))";

/// `(label, problem, fragment of the disclosed reason, Carcara's own error)`.
const REFUSED: &[(&str, &str, &str, &str)] = &[
    (
        "qualified monomorphic constructor, applied (typed_vec_pins_cell64)",
        "(assert (= v ((as mkVec Vec) 1)))",
        "(as mkVec Vec)",
        "not a valid qualified operator: 'mkVec'",
    ),
    (
        "qualified nullary monomorphic constructor",
        "(assert (= e (as A E)))",
        "(as A E)",
        "not a valid qualified operator: 'A'",
    ),
    (
        "qualified declared constant",
        "(declare-const x Int)(assert (= (as x Int) 1))",
        "(as x Int)",
        "not a valid qualified operator: 'x'",
    ),
    (
        "qualified declared function",
        "(declare-fun f (Int) Int)(assert (= ((as f Int) 1) 1))",
        "(as f Int)",
        "not a valid qualified operator: 'f'",
    ),
    (
        "parametric nullary constructor without `as`",
        "(assert (= l nil))",
        "without `(as nil",
        "expected '(L Int)', got '(L T)'",
    ),
    (
        "z3 tester `is-C`",
        "(assert (is-A e))",
        "`is-A`",
        "identifier 'is-A' is not defined",
    ),
    (
        "`match` (constructor pattern with a field)",
        "(assert (= 1 (match e ((A 0) ((B x) x)))))",
        "`match`",
        "panicked at carcara/src/parser/mod.rs:1368",
    ),
    (
        "`lambda` as an array",
        "(declare-const a (Array Int Int))(assert (= a (lambda ((x Int)) x)))",
        "`lambda`",
        "expected '(Array Int Int)', got '(Func Int Int)'",
    ),
    (
        "`iff`",
        "(declare-const p Bool)(assert (iff p p))",
        "`iff`",
        "identifier 'iff' is not defined",
    ),
    (
        "`bv2nat`",
        "(declare-const b (_ BitVec 4))(assert (= (bv2nat b) 2))",
        "`bv2nat`",
        "identifier 'bv2nat' is not defined",
    ),
    (
        "`(_ int2bv 4)`",
        "(declare-const n Int)(assert (= ((_ int2bv 4) n) #x0))",
        "(_ int2bv",
        "not a valid indexed operator: 'int2bv'",
    ),
    (
        "`bvredor`",
        "(declare-const b (_ BitVec 4))(assert (= (bvredor b) #b1))",
        "`bvredor`",
        "identifier 'bvredor' is not defined",
    ),
    (
        "`bvnego`",
        "(declare-const b (_ BitVec 4))(assert (bvnego b))",
        "`bvnego`",
        "identifier 'bvnego' is not defined",
    ),
    (
        "`bvuaddo`",
        "(declare-const b (_ BitVec 4))(assert (bvuaddo b b))",
        "`bvuaddo`",
        "identifier 'bvuaddo' is not defined",
    ),
    (
        "`(_ divisible 3)`",
        "(declare-const n Int)(assert ((_ divisible 3) n))",
        "(_ divisible",
        "not a valid indexed operator: 'divisible'",
    ),
    (
        "`^`",
        "(declare-const n Int)(assert (= (^ n 2) 3))",
        "`^`",
        "identifier '^' is not defined",
    ),
    (
        "`str.to_lower`",
        "(declare-const s String)(assert (= (str.to_lower s) \"a\"))",
        "`str.to_lower`",
        "identifier 'str.to_lower' is not defined",
    ),
    (
        "`str.to.int`",
        "(declare-const s String)(assert (= (str.to.int s) 3))",
        "`str.to.int`",
        "identifier 'str.to.int' is not defined",
    ),
    (
        "`re.nostr`",
        "(declare-const s String)(assert (str.in_re s re.nostr))",
        "`re.nostr`",
        "identifier 're.nostr' is not defined",
    ),
    (
        "`(_ char #x41)`",
        "(declare-const s String)(assert (= s (str.from_code (str.to_code (_ char #x41)))))",
        "(_ char",
        "not a valid indexed operator: 'char'",
    ),
    (
        "`(_ as-array f)`",
        "(declare-fun f (Int) Int)(declare-const a (Array Int Int))(assert (= a (_ as-array f)))",
        "(_ as-array",
        "not a valid indexed operator: 'as-array'",
    ),
    (
        "FloatingPoint sort",
        "(declare-const x (_ FloatingPoint 8 24))(assert (fp.isNaN x))",
        "FloatingPoint",
        "sort 'FloatingPoint' is not defined",
    ),
    (
        "RoundingMode sort",
        "(declare-const r RoundingMode)(assert (= r RNE))",
        "RoundingMode",
        "sort 'RoundingMode' is not defined",
    ),
    (
        "Seq sort",
        "(declare-const s (Seq Int))(assert (= (seq.len s) 3))",
        "`Seq`",
        "sort 'Seq' is not defined",
    ),
    (
        "reserved word as a bound variable",
        "(assert (forall ((step Int)) (> step 0)))",
        "`step`",
        "unexpected token: 'step'",
    ),
    (
        "reserved word as a let variable",
        "(assert (let ((cl 1)) (> cl 0)))",
        "`cl`",
        "unexpected token: 'cl'",
    ),
    (
        "reserved word as a constant",
        "(declare-const cl Int)(assert (= cl 1))",
        "`cl`",
        "unexpected token: 'cl'",
    ),
    (
        "`let` with no binding",
        "(declare-const p Bool)(assert (let () p))",
        "no binder",
        "expected non-empty sequence",
    ),
    (
        "`forall` with no binder",
        "(declare-const p Bool)(assert (forall () p))",
        "no binder",
        "expected non-empty sequence",
    ),
    (
        "`exists` with no binder, under a `let`",
        "(declare-const p Bool)(assert (let ((a p)) (exists () a)))",
        "no binder",
        "expected non-empty sequence",
    ),
    (
        "`!` with no attribute",
        "(declare-const p Bool)(assert (! p))",
        "no attribute",
        "expected non-empty sequence",
    ),
    (
        "unary `distinct`",
        "(declare-const x Int)(assert (distinct x))",
        "`distinct`",
        "expected at least 2 arguments, got 1",
    ),
    (
        "unary `+`",
        "(declare-const n Int)(assert (= n (+ n)))",
        "`+`",
        "expected at least 2 arguments, got 1",
    ),
    (
        "unary `str.++`",
        "(declare-const s String)(assert (= s (str.++ s)))",
        "`str.++`",
        "expected at least 2 arguments, got 1",
    ),
    (
        "ternary `bvsub`",
        "(declare-const a (_ BitVec 4))(assert (= a (bvsub a a a)))",
        "`bvsub`",
        "expected 2 arguments, got 3",
    ),
    (
        "Int numeral beside an Int in `+` with a decimal",
        "(declare-const x Int)(assert (= (+ x 1.5) 2.0))",
        "`+`",
        "expected 'Int', got 'Real'",
    ),
    (
        "Int numeral equated with a Real",
        "(declare-const x Real)(assert (= x 1))",
        "`=`",
        "expected 'Real', got 'Int'",
    ),
    (
        "Int argument of a Real function",
        "(declare-fun f (Real) Real)(assert (= (f 1) 1.0))",
        "`f`",
        "expected 'Real', got 'Int'",
    ),
    (
        "Int numeral times a Real",
        "(declare-const r Real)(assert (= r (* 2 r)))",
        "`*`",
        "expected 'Int', got 'Real'",
    ),
    (
        "`/` of Int numerals outside a real-only logic",
        "(declare-const x Real)(assert (= x (/ 1 2)))",
        "`/`",
        "expected 'Real', got 'Int'",
    ),
    (
        "`to_int` of an Int",
        "(declare-const n Int)(assert (= n (to_int 1)))",
        "`to_int`",
        "expected 'Real', got 'Int'",
    ),
    (
        "`abs` of a Real",
        "(declare-const r Real)(assert (= r (abs r)))",
        "`abs`",
        "expected 'Int', got 'Real'",
    ),
    (
        "mixed `ite` branches",
        "(declare-const c Bool)(declare-const r Real)(assert (= r (ite c 1 1.0)))",
        "`ite`",
        "expected 'Int', got 'Real'",
    ),
    (
        "Bool in arithmetic",
        "(declare-const p Bool)(declare-const n Int)(assert (= n (+ p 1)))",
        "`+`",
        "expected 'Int' or 'Real', got 'Bool'",
    ),
    (
        "bit-vector width mismatch",
        "(declare-const a (_ BitVec 4))(declare-const b (_ BitVec 8))(assert (= b (bvadd a b)))",
        "`bvadd`",
        "expected '(_ BitVec 4)', got '(_ BitVec 8)'",
    ),
    (
        "Int value of a Real `const` array",
        "(declare-const a (Array Int Real))(assert (= a ((as const (Array Int Real)) 0)))",
        "(as const (Array Int Real))",
        "expected '(Array ? Int)', got '(Array Int Real)'",
    ),
    (
        "`define-fun` body coerced to its Real result",
        "(define-fun r () Real 1)(assert (> r 0.0))",
        "body of `r`",
        "expected 'Real', got 'Int'",
    ),
    (
        "surrogate escape in a string literal",
        "(declare-const s String)(assert (= s \"\\u{d800}\"))",
        "surrogate",
        "invalid Unicode value: 0x'd800'",
    ),
];

/// `(x)` for a constant stops Carcara's parser ("expected non-empty
/// sequence") and z3's ("invalid function application, arguments missing");
/// AY's frontend no longer reads it either, so no problem reaches the surface
/// with it.
#[test]
fn a_nullary_application_does_not_parse() {
    assert!(ay_frontend::parse("(declare-const x Int)(assert (= (x) 1))").is_err());
}

#[test]
fn every_construct_pinned_carcara_cannot_parse_is_unsupported() {
    for (label, body, fragment, carcara) in REFUSED {
        let prelude = if body.contains("nil") {
            LIST
        } else if body.contains("mkVec") {
            VEC
        } else {
            DT
        };
        let problem = format!("{prelude}{body}(check-sat)");
        let gap = gap_of(&problem).unwrap_or_else(|| {
            panic!("{label}: disclosed supported, but Carcara says `{carcara}`")
        });
        assert!(
            gap.contains(fragment),
            "{label}: the reason must name `{fragment}`: {gap}"
        );
    }
}

/// Each problem parses in pinned Carcara, so the surface stays supported.
const ACCEPTED: &[(&str, &str)] = &[
    ("plain datatype, selector and indexed tester", "(assert (= v (mkVec 1)))(assert ((_ is mkVec) v))(assert (= (len v) 1))"),
    ("qualified parametric nullary constructor", "(assert (= l (as nil (L Int))))"),
    ("qualified parametric constructor, applied", "(assert (= l ((as cons (L Int)) 1 (as nil (L Int)))))"),
    ("unqualified parametric constructor and selector", "(assert (= (hd l) 1))(assert (= l (cons 1 l)))"),
    ("`const` array", "(declare-const a (Array Int Int))(assert (= a ((as const (Array Int Int)) 0)))"),
    ("define-sort with a parameter", "(define-sort M (T) (Array T T))(declare-const m (M Int))(assert (= (select m 0) 1))"),
    ("parametric declared sort", "(declare-sort S 1)(declare-const a (S Int))(declare-const b (S Int))(assert (distinct a b))"),
    ("define-fun, define-fun-rec, define-funs-rec", "(define-fun g ((x Int)) Int (+ x 1))\
        (define-fun-rec f ((x Int)) Int (ite (<= x 0) 0 (f (- x 1))))\
        (define-funs-rec ((h ((x Int)) Int)) ((ite (<= x 0) 0 (h (- x 1)))))(assert (= (f (g 1)) (h 1)))"),
    ("mixed Int/Real in a comparison", "(declare-const x Real)(assert (< x 1))(assert (> x 2))"),
    (":named label reused, :pattern skipped", "(declare-const p Bool)(declare-fun f (Int) Int)\
        (assert (! p :named a1))(assert (not a1))(assert (forall ((x Int)) (! (= (f x) x) :pattern ((f x)))))"),
    ("let shadowing a constant", "(declare-const x Int)(assert (let ((x true)) x))"),
    ("non-empty `let`, `exists` and `!` lists", "(declare-const p Bool)(declare-const v0 Int)\
        (assert (! (let ((a p)) (exists ((y Int)) (or a (= y v0)))) :named n))"),
    ("check-sat-assuming and push/pop", "(declare-const p Bool)(push 1)(declare-const q Bool)(pop 1)(check-sat-assuming (p (not p)))"),
    ("bit-vector operators", "(declare-const a (_ BitVec 4))(assert (= a (bvadd a a a)))\
        (assert (= (bvcomp a a) #b1))(assert (= ((_ extract 3 2) (concat a a)) #b00))(assert (= (ubv_to_int a) (int.pow2 2)))"),
    ("negative and decimal literals, to_real", "(declare-const r Real)(declare-const n Int)\
        (assert (= r -1.5))(assert (= n -1))(assert (= r (to_real n)))(assert (= r (- 1.0)))"),
    ("strings and regular expressions", "(declare-const s String)\
        (assert (str.in_re s ((_ re.loop 1 2) (str.to_re \"a\"))))(assert (= (str.len s) (str.to_code \"\\u{41}\")))"),
    ("mutually recursive datatypes", "(declare-datatypes ((T 0) (F 0)) (((node (val Int) (kids F))) ((fnil) (fcons (hd2 T) (tl2 F)))))\
        (declare-const t T)(assert (= (val t) 1))"),
    ("abs and n-ary chains", "(declare-const n Int)(declare-const p Bool)(assert (= (abs n) 1))(assert (and p))(assert (=> p p p))(assert (< 0 n 5))"),
];

#[test]
fn problems_pinned_carcara_parses_stay_supported() {
    for (label, body) in ACCEPTED {
        let prelude = if body.contains("nil") || body.contains("(hd l)") {
            LIST
        } else {
            VEC
        };
        let problem = format!("{prelude}{body}(check-sat)");
        assert_eq!(
            gap_of(&problem),
            None,
            "{label}: Carcara parses this problem"
        );
    }
}

#[test]
fn real_only_logics_read_numerals_as_reals() {
    // Carcara reads `1` as `1.0` when the logic has reals and no integers, and
    // only then (`Parser::interpret_ints_as_reals`).
    let real_only =
        "(set-logic QF_LRA)(declare-const x Real)(assert (= x 1))(assert (= x (/ 1 2)))";
    assert_eq!(gap_of(real_only), None);
    let mixed = "(set-logic QF_LIRA)(declare-const x Real)(assert (= x 1))";
    assert!(gap_of(mixed).is_some_and(|gap| gap.contains("`=`")));
}

#[test]
fn the_first_gap_is_kept_and_survives_later_commands() {
    let problem = "(set-logic ALL)(declare-const x Int)(push 1)(assert (= (as x Int) 1))(pop 1)\
        (assert (iff true true))(check-sat)";
    let gap = gap_of(problem).expect("a popped scope is still in the file Carcara reads");
    assert!(gap.contains("(as x Int)"), "{gap}");
}
