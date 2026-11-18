// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checks on the ascribed spelling of a datatype constructor, `(as nil L1)`,
//! and the test scripts of the readers of model text
//! (#overloaded-nil-surface).

use ay_core::quote_symbol;
use ay_frontend::SExpr;

/// The constructor `c` when `sexp` is `(as c S)`, `c` a symbol, `S` a symbol
/// or a list headed by one, and `ay_core::ascription_may_name_constructor`
/// admits `c` under `S`; else `None` (for example for an abstract element
/// `(as @S!0 S)` or for `(as seq.empty (Seq Int))`).
fn ascribed_nullary_constructor(sexp: &SExpr) -> Option<&str> {
    let [head, constructor, sort] = sexp.as_list()? else {
        return None;
    };
    if !head.is_symbol("as") {
        return None;
    }
    let constructor = constructor.as_symbol()?;
    let compound_sort_head = match sort {
        SExpr::Symbol(_) => None,
        SExpr::List(items) => Some(items.first()?.as_symbol()?),
        _ => return None,
    };
    ay_core::ascription_may_name_constructor(constructor, compound_sort_head).then_some(constructor)
}

/// Whether `ascribed` reads as `bare`: their
/// `ay_core::bare_constructor_spelling` texts are equal, their lines give
/// equal `ay_core::model_constant_definition` readings, and
/// `ay_frontend::sexp::parse_sexps` parses both texts with
/// [`same_parsed_reading`] holding.
///
/// A text the frontend does not parse keeps no ascription: the text-only
/// readings alone do not settle it. `bare_constructor_spelling` replaces an
/// ascription inside a list headed `as`, where [`same_parsed_reading`]
/// requires the two forms to be the same, and it reads a run such as `p|q`
/// as one atom where the frontend opens a quoted symbol.
pub(crate) fn reads_as_bare(bare: &str, ascribed: &str) -> bool {
    if ay_core::bare_constructor_spelling(ascribed) != ay_core::bare_constructor_spelling(bare) {
        return false;
    }
    if !ascribed
        .lines()
        .map(ay_core::model_constant_definition)
        .eq(bare.lines().map(ay_core::model_constant_definition))
    {
        return false;
    }
    let (Ok(bare), Ok(ascribed)) = (
        ay_frontend::sexp::parse_sexps(bare),
        ay_frontend::sexp::parse_sexps(ascribed),
    ) else {
        return false;
    };
    same_parsed_reading(&bare, &ascribed)
}

/// Where a term of the parsed form sits, for [`same_parsed_reading`].
#[derive(Clone, Copy, PartialEq, Eq)]
enum Position {
    /// An argument: here `(as c S)` may stand for the symbol `c`.
    Argument,
    /// The head of a list: no ascription is accepted here.
    Head,
    /// Inside a list headed `as`: the two forms must be the same.
    Verbatim,
}

/// Whether the parsed forms are equal except where `ascribed` holds
/// `(as c S)` and `bare` holds the symbol `c`, [`ascribed_nullary_constructor`]
/// giving `c`.
///
/// That difference is accepted only at an argument position: not at the head
/// of a list, and nowhere inside a list headed `as`, which may be the
/// application of a constructor named `as`. A bare name the frontend parses
/// as no symbol, such as `true` or `:k`, matches no ascription.
fn same_parsed_reading(bare: &[SExpr], ascribed: &[SExpr]) -> bool {
    if bare.len() != ascribed.len() {
        return false;
    }
    let headed_as = |items: &[SExpr]| items.first().is_some_and(|head| head.is_symbol("as"));
    let mut pending: Vec<(&SExpr, &SExpr, Position)> = bare
        .iter()
        .zip(ascribed)
        .map(|(bare, ascribed)| (bare, ascribed, Position::Argument))
        .collect();
    while let Some((bare, ascribed, position)) = pending.pop() {
        match (bare, ascribed) {
            (SExpr::Symbol(name), SExpr::List(_)) => {
                let constructor = ascribed_nullary_constructor(ascribed)
                    .filter(|_| position == Position::Argument);
                if constructor != Some(name.as_str()) {
                    return false;
                }
            }
            (SExpr::List(bare), SExpr::List(ascribed)) => {
                if bare.len() != ascribed.len() {
                    return false;
                }
                let verbatim =
                    position == Position::Verbatim || headed_as(bare) || headed_as(ascribed);
                for (at, pair) in bare.iter().zip(ascribed).enumerate() {
                    let position = match (verbatim, at) {
                        (true, _) => Position::Verbatim,
                        (false, 0) => Position::Head,
                        (false, _) => Position::Argument,
                    };
                    pending.push((pair.0, pair.1, position));
                }
            }
            (SExpr::List(_), _) | (_, SExpr::List(_)) => return false,
            (bare, ascribed) => {
                if bare != ascribed {
                    return false;
                }
            }
        }
    }
    true
}

/// One case of the declarable-name matrix: a script that asserts a nullary
/// constructor, which `Other` declares too, at one of four positions (the top
/// level and nested in a constructor application, an array element, an array
/// index, a function table). Test support for readers of model text.
#[doc(hidden)]
#[derive(Debug, Clone)]
pub struct AscriptionCase {
    /// The constructor, the sort and the position, for a failure message.
    pub label: String,
    /// Declarations and assertions; satisfiable.
    pub script: String,
    /// The ascriptions this case's model may print, each with the token
    /// `AscriptionCase::bare` puts in its place.
    pub ascriptions: Vec<(String, String)>,
    /// Text `AscriptionCase::solve` requires in the printed model: the
    /// constructor, ascribed, in place.
    pub expected: Vec<String>,
    /// The constructor's name, unquoted.
    name: String,
}

impl AscriptionCase {
    /// One script for each of four positions: the top level and nested, an
    /// array element, an array index, a function table.
    fn cells(constructor: &str, sort_head: &str, arity: usize) -> Vec<Self> {
        let c = quote_symbol(constructor);
        let parameters: Vec<String> = (0..arity).map(|at| format!("T{at}")).collect();
        let arguments: Vec<&str> = (0..arity)
            .map(|at| if at % 2 == 0 { "Int" } else { "Bool" })
            .collect();
        let (declaration, sort) = if arity == 0 {
            (
                format!("(declare-datatypes (({sort_head} 0)) (((mk (fst Int)) ({c}))))"),
                sort_head.to_string(),
            )
        } else {
            let fields: Vec<String> = parameters
                .iter()
                .enumerate()
                .map(|(at, parameter)| format!("(f{at} {parameter})"))
                .collect();
            (
                format!(
                    "(declare-datatypes (({sort_head} {arity})) \
                     ((par ({}) ((mk {}) ({c})))))",
                    parameters.join(" "),
                    fields.join(" ")
                ),
                format!("({sort_head} {})", arguments.join(" ")),
            )
        };
        let here = format!("(as {c} {sort})");
        let other = format!("(as {c} Other)");
        let declarations = format!(
            "{declaration}\n\
             (declare-datatypes ((Other 0)) (((omk (ofst Int)) ({c}))))\n\
             (declare-datatypes ((W 0)) (((w (w1 {sort}) (w2 Other)))))\n"
        );
        let positions = [
            (
                "top level and nested",
                format!(
                    "(declare-const top {sort})\n\
                     (declare-const nested W)\n\
                     (assert (= top {here}))\n\
                     (assert (= nested (w {here} {other})))\n"
                ),
                vec![
                    format!("(define-fun top () {sort} {here})"),
                    format!("(define-fun nested () W (w {here} {other}))"),
                ],
            ),
            (
                "array element",
                format!(
                    "(declare-const elements (Array Int {sort}))\n\
                     (declare-const compound (Array Int W))\n\
                     (assert (= (select elements 3) {here}))\n\
                     (assert (= (select compound 4) (w {here} {other})))\n"
                ),
                vec![format!(" 3 {here})"), format!(" 4 (w {here} {other}))")],
            ),
            (
                "array index",
                format!(
                    "(declare-const indices (Array {sort} Int))\n\
                     (assert (= (select indices {here}) 7))\n"
                ),
                vec![format!(" {here} 7)")],
            ),
            (
                "function table",
                format!(
                    "(declare-fun count ({sort} Int) Int)\n\
                     (declare-fun pick (Int) {sort})\n\
                     (assert (= (count {here} 1) 5))\n\
                     (assert (= (count {here} 2) 6))\n\
                     (assert (= (pick 1) {here}))\n"
                ),
                vec![format!("(= x0 {here})"), format!("    {here})")],
            ),
        ];
        positions
            .into_iter()
            .map(|(position, body, expected)| Self {
                label: format!("constructor {constructor} of {sort}, {position}"),
                script: format!("{declarations}{body}"),
                expected,
                ascriptions: vec![(here.clone(), c.clone()), (other.clone(), c.clone())],
                name: constructor.to_string(),
            })
            .collect()
    }

    /// `printed` with each ascription of this case replaced by the
    /// constructor's `ay_core::quote_symbol` token (`|pop|`), the text a
    /// value of it prints bare.
    pub fn bare(&self, printed: &str) -> String {
        self.ascriptions
            .iter()
            .fold(printed.to_string(), |text, (ascribed, name)| {
                text.replace(ascribed.as_str(), name)
            })
    }

    /// The name of the constructor this case ascribes, unquoted.
    pub fn constructor(&self) -> &str {
        &self.name
    }

    /// Solve the script: the solver, holding the declarations, and the model
    /// text it prints. `Err` says what went wrong, [`Self::label`] included,
    /// for example a missing `expected` text.
    pub fn solve(&self) -> Result<(crate::api::Solver, String), String> {
        let mut solver = crate::api::Solver::new(crate::api::Logic::All);
        solver
            .parse_smtlib2(&self.script)
            .map_err(|error| format!("{}: {error}", self.label))?;
        let result = solver.check_sat();
        if result != crate::api::SolveResult::Sat {
            return Err(format!("{}: check-sat answered {result:?}", self.label));
        }
        let model = solver
            .try_get_model_str()
            .map_err(|error| format!("{}: {error}", self.label))?;
        for expected in &self.expected {
            if !model.contains(expected.as_str()) {
                return Err(format!(
                    "{}: the model does not print {expected}:\n{model}",
                    self.label
                ));
            }
        }
        Ok((solver, model))
    }
}

/// The constructor names of the matrix: ordinary ones, names that look like
/// theory values but a script can declare (`const`, `bag.empty`,
/// `set.universe`), and a reserved word an ascription must quote (`pop`).
/// Each is tried under each sort spelling of [`MATRIX_SORTS`].
#[doc(hidden)]
pub const MATRIX_CONSTRUCTORS: [&str; 6] =
    ["nil", "leaf", "const", "bag.empty", "set.universe", "pop"];

/// The sort spellings of the matrix, as a sort constructor and its arity: a
/// sort symbol, a quoted one, a quoted one holding a space, bare
/// (`|My List|`) and as the head of a sort application (`|My Pair|`), and
/// the sort application of a parametric datatype, named ordinarily or like a
/// theory sort constructor a script may declare (`Tuple`, `Bag`,
/// `Relation`).
#[doc(hidden)]
pub const MATRIX_SORTS: [(&str, usize); 9] = [
    ("L1", 0),
    ("|L#1|", 0),
    ("|My List|", 0),
    ("|My Pair|", 2),
    ("List", 1),
    ("Pair", 2),
    ("Tuple", 2),
    ("Bag", 1),
    ("Relation", 2),
];

/// See [`MATRIX_CONSTRUCTORS`] and [`MATRIX_SORTS`].
#[doc(hidden)]
pub fn constructor_ascription_matrix() -> Vec<AscriptionCase> {
    let mut cases = Vec::new();
    for constructor in MATRIX_CONSTRUCTORS {
        for (sort_head, arity) in MATRIX_SORTS {
            cases.extend(AscriptionCase::cells(constructor, sort_head, arity));
        }
    }
    cases
}

/// The constructor names of the [`OverloadPair`] scripts, unquoted: plain
/// names, reserved words, and names that print quoted, such as `true` and
/// `my nil`. Each prints ascribed at `top` (checked by
/// `every_reader_returns_the_same_whether_or_not_a_constructor_is_overloaded`).
#[doc(hidden)]
pub const OVERLOAD_ASCRIBED_CONSTRUCTORS: [&str; 21] = [
    "nil", "pop", "let", "const", "leaf", "exit", "true", "false", ":k", "a#b", "a;b", "a,b",
    "a'b", "a{b", "a[b", "a`b", "a|b", "|x", "y|", "my nil", "x(y",
];

/// The pairs [`overload_pairs`] makes for each constructor name: under two
/// sorts, one per [`AsSecond`] and one of function tables.
#[doc(hidden)]
pub const OVERLOAD_PAIR_VARIANTS: usize = 10;

/// One script twice: with a nullary constructor that a second datatype,
/// `Other`, also declares, and with `Other` declaring `unshared` in its
/// place. Test support for readers of model text.
#[doc(hidden)]
#[derive(Debug, Clone)]
pub struct OverloadPair {
    /// The constructor, the sort and the variant, for a failure message.
    pub label: String,
    /// The constructor's name.
    pub constructor: String,
    /// The list sort that declares it, as a script writes it.
    pub sort: String,
    /// The script whose `Other` datatype declares the constructor too.
    pub overloaded: String,
    /// The same script, `Other` declaring `unshared` in its place.
    pub renamed: String,
    /// The terms a `(get-value)` asks of either script.
    pub queries: &'static str,
    /// Whether the script is the function-table variant, which holds no
    /// record `r` and no application `p` of a constructor named `as`.
    pub tables: bool,
}

/// What the second field of the constructor named `as` holds in an
/// [`OverloadPair`] script; the first holds the list's constructor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AsSecond {
    /// An enumerator, `e1`: for `nil`, `(as nil e1)`.
    Enumerator,
    /// A list: for `nil`, `(as nil (cons 1 nil))`.
    List,
    /// An enumerator named like the second datatype, `Other`: for `nil`,
    /// `(as nil Other)`, also the text of the ascription of `Other`'s own
    /// `nil` where it shares the name.
    PartnerSort,
    /// An enumerator named like the list sort itself: for `nil` of `L1`,
    /// `(as nil L1)`, also the text of the ascription of the first field's
    /// value alone.
    OwnSort,
}

impl AsSecond {
    const ALL: [Self; 4] = [
        Self::Enumerator,
        Self::List,
        Self::PartnerSort,
        Self::OwnSort,
    ];

    fn label(self) -> &'static str {
        match self {
            Self::Enumerator => "an enumeration",
            Self::List => "a list",
            Self::PartnerSort => "an enumerator named like the second datatype",
            Self::OwnSort => "an enumerator named like the list sort",
        }
    }
}

impl OverloadPair {
    /// The script for `constructor` of the list sort `sort`, the second
    /// datatype declaring `partner`.
    ///
    /// The script places the constructor at the top level, in a list, in a
    /// record, in an array and in a function table, beside a string literal
    /// holding `|`, `)` and the text of an ascription, negative numerals, the
    /// application `p` of a constructor named `as` (its fields pinned by
    /// selectors, the second as `as_second` says), and the constructors of
    /// `Odd`, whose names hold a bar or a double quote.
    fn script(constructor: &str, partner: &str, sort: &str, as_second: AsSecond) -> String {
        let c = quote_symbol(constructor);
        let partner = quote_symbol(partner);
        let here = format!("(as {c} {sort})");
        let (odd, odd1, odd2) = if matches!(as_second, AsSecond::List | AsSecond::OwnSort) {
            (r#"(|p\|q|) (|c"d|)"#, r"|p\|q|", r#"|c"d|"#)
        } else {
            (r"(|\|u|) (|v\||)", r"|\|u|", r"|v\||")
        };
        // The first enumerator of `E`, the sort of the second field, and
        // the value that field holds.
        let (enumerator, second_sort, second) = match as_second {
            AsSecond::Enumerator => ("e1", "E".to_string(), "e1".to_string()),
            AsSecond::List => ("e1", sort.to_string(), format!("(cons 1 {here})")),
            AsSecond::PartnerSort => ("Other", "E".to_string(), "Other".to_string()),
            AsSecond::OwnSort => (sort, "E".to_string(), sort.to_string()),
        };
        format!(
            "(declare-datatypes (({sort} 0)) ((({c}) (halt) (cons (hd Int) (tl {sort})))))\n\
             (declare-datatypes ((Other 0)) ((({partner}) (omk (ofst Int)))))\n\
             (declare-datatypes ((E 0)) ((({enumerator}) (e2))))\n\
             (declare-datatypes ((Odd 0)) (({odd})))\n\
             (declare-datatypes ((W 0)) (((w (w1 {sort}) (w2 {sort})))))\n\
             (declare-datatypes ((P 0)) (((|as| (f1 {sort}) (f2 {second_sort})))))\n\
             (declare-datatypes ((Rec 0)) (((rec (label String) (o1 Odd) (tail {sort}) \
             (o2 Odd) (last {sort}) (count Int)))))\n\
             (declare-const top {sort}) (declare-const two {sort})\n\
             (declare-const nested W) (declare-const p P) (declare-const r Rec)\n\
             (declare-const n Int) (declare-const arw (Array Int W))\n\
             (declare-fun pick (Int) {sort})\n\
             (assert (= top {here}))\n\
             (assert (= two (cons 1 (cons (- 2) {here}))))\n\
             (assert (= nested (w top (as halt {sort}))))\n\
             (assert (= (f1 p) {here})) (assert (= (f2 p) {second}))\n\
             (assert (= r (rec \"| (as nil L1) )\" {odd1} {here} {odd2} {here} (- 7))))\n\
             (assert (= (select arw 4) (w top top)))\n\
             (assert (= (pick 1) {here}))\n\
             (assert (= n (- 5)))\n"
        )
    }

    /// The function-table variant: the constructor as an argument of `count`
    /// and the result of `pick`, beside the constants `top`, `two`, `nested`
    /// and `n`.
    fn table_script(constructor: &str, partner: &str, sort: &str) -> String {
        let c = quote_symbol(constructor);
        let partner = quote_symbol(partner);
        let here = format!("(as {c} {sort})");
        format!(
            "(declare-datatypes (({sort} 0)) ((({c}) (halt) (cons (hd Int) (tl {sort})))))\n\
             (declare-datatypes ((Other 0)) ((({partner}) (omk (ofst Int)))))\n\
             (declare-datatypes ((W 0)) (((w (w1 {sort}) (w2 {sort})))))\n\
             (declare-const top {sort}) (declare-const two {sort})\n\
             (declare-const nested W) (declare-const n Int)\n\
             (declare-fun count ({sort} Int) Int)\n\
             (declare-fun pick (Int) {sort})\n\
             (assert (= top {here}))\n\
             (assert (= two (cons 1 (cons (- 2) {here}))))\n\
             (assert (= nested (w top (as halt {sort}))))\n\
             (assert (= (count {here} 1) 5))\n\
             (assert (= (count {here} 2) 6))\n\
             (assert (= (pick 1) {here}))\n\
             (assert (= n (- 5)))\n"
        )
    }

    /// Solve `script`: the solver, holding the declarations, and the model
    /// text it prints.
    pub fn solve(&self, script: &str) -> Result<(crate::api::Solver, String), String> {
        let mut solver = crate::api::Solver::new(crate::api::Logic::All);
        solver
            .parse_smtlib2(script)
            .map_err(|error| format!("{}: {error}", self.label))?;
        let result = solver.check_sat();
        if result != crate::api::SolveResult::Sat {
            return Err(format!("{}: check-sat answered {result:?}", self.label));
        }
        let model = solver
            .try_get_model_str()
            .map_err(|error| format!("{}: {error}", self.label))?;
        Ok((solver, model))
    }
}

/// Every name of [`OVERLOAD_ASCRIBED_CONSTRUCTORS`], as the constructor of a
/// list sort named plainly and with a space, in five variants: one per
/// [`AsSecond`], beside the `Odd` names `|u` and `v|` or `p|q` and `c"d`, and
/// function tables.
#[doc(hidden)]
pub fn overload_pairs() -> Vec<OverloadPair> {
    debug_assert_eq!(OVERLOAD_PAIR_VARIANTS, 2 * (AsSecond::ALL.len() + 1));
    let mut pairs = Vec::new();
    for constructor in OVERLOAD_ASCRIBED_CONSTRUCTORS {
        for sort in ["L1", "|My List|"] {
            for as_second in AsSecond::ALL {
                pairs.push(OverloadPair {
                    label: format!(
                        "constructor {constructor} of {sort}, `as` over {}",
                        as_second.label()
                    ),
                    constructor: constructor.to_string(),
                    sort: sort.to_string(),
                    overloaded: OverloadPair::script(constructor, constructor, sort, as_second),
                    renamed: OverloadPair::script(constructor, "unshared", sort, as_second),
                    queries: "top two nested p r (select arw 4) (pick 1) n",
                    tables: false,
                });
            }
            pairs.push(OverloadPair {
                label: format!("constructor {constructor} of {sort}, function tables"),
                constructor: constructor.to_string(),
                sort: sort.to_string(),
                overloaded: OverloadPair::table_script(constructor, constructor, sort),
                renamed: OverloadPair::table_script(constructor, "unshared", sort),
                queries: "top two nested (pick 1) (count top 1) n",
                tables: true,
            });
        }
    }
    pairs
}

/// A script whose model holds the application of a constructor named `as`
/// that prints as `(|as| Unit Unit)`, with nothing overloaded: `Unit` is a
/// datatype and its only constructor.
#[doc(hidden)]
pub const AS_APPLICATION_UNIT: &str = "\
(declare-datatypes ((Unit 0)) (((Unit))))
(declare-datatypes ((P 0)) (((|as| (f1 Unit) (f2 Unit)))))
(declare-datatypes ((Q 0)) (((q (g1 P) (g2 Int)))))
(declare-const p P) (declare-const qq Q)
(declare-fun f (Int) P)
(assert (= (f1 p) Unit))
(assert (= (g1 qq) p))
(assert (= (f 1) p))
";

/// The same, printing `(|as| nil L1)`: `L1` is the list datatype that
/// declares `nil` and an enumerator of the second field's sort.
#[doc(hidden)]
pub const AS_APPLICATION_OWN_SORT: &str = "\
(declare-datatypes ((L1 0)) (((nil) (cons (hd Int) (tl L1)))))
(declare-datatypes ((E 0)) (((L1) (e2))))
(declare-datatypes ((P 0)) (((|as| (f1 L1) (f2 E)))))
(declare-datatypes ((Q 0)) (((q (g1 P) (g2 Int)))))
(declare-const p P) (declare-const qq Q)
(declare-fun f (Int) P)
(assert (= (f1 p) nil)) (assert (= (f2 p) L1))
(assert (= (g1 qq) p))
(assert (= (f 1) p))
";

/// A script twice, as an [`OverloadPair`] holds one: the application of a
/// constructor named `as` prints `(|as| nil Other)` in both, and `Other` is a
/// datatype that declares `nil` in the first and `unshared` in the second.
/// The function `f` returns that application.
#[doc(hidden)]
pub fn as_application_pair() -> (String, String) {
    let script = |partner: &str| {
        format!(
            "(declare-datatypes ((T 0)) (((nil) (cons (hd Int) (tl T)))))\n\
             (declare-datatypes ((Other 0)) ((({partner}) (omk (ofst Int)))))\n\
             (declare-datatypes ((E 0)) (((Other) (e2))))\n\
             (declare-datatypes ((P 0)) (((|as| (f1 T) (f2 E)))))\n\
             (declare-datatypes ((Q 0)) (((q (g1 P) (g2 Int)))))\n\
             (declare-const p P) (declare-const qq Q) (declare-const t T)\n\
             (declare-fun f (Int) P)\n\
             (assert (= (f1 p) (as nil T))) (assert (= (f2 p) Other))\n\
             (assert (= (g1 qq) p))\n\
             (assert (= (f 1) p))\n\
             (assert (= t (cons 1 (as nil T))))\n"
        )
    };
    (script("nil"), script("unshared"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sexp(text: &str) -> SExpr {
        ay_frontend::sexp::parse_sexp(text).expect("one s-expression")
    }

    /// Each entry of `ASCRIPTION_THEORY_VALUE_HEADS` is a reserved symbol,
    /// and each declaration below of a constructor of that name is refused.
    /// For each entry `H` of `ASCRIPTION_THEORY_SORT_HEADS`, no response of
    /// the script below, in these logics and postures, holds `(as nil (H `.
    #[test]
    fn the_syntactic_rule_refuses_only_names_the_frontend_reserves() {
        for head in ay_core::ASCRIPTION_THEORY_VALUE_HEADS {
            assert!(
                ay_frontend::is_reserved_symbol(head),
                "{head} is declarable, so it may name a constructor"
            );
            for script in [
                format!("(declare-datatypes ((D 0)) (((mk) ({head}))))"),
                format!("(declare-datatype D ((mk) ({head})))"),
                format!("(declare-datatypes ((D 0)) (((mk) (|{head}|))))"),
            ] {
                let mut executor = crate::Executor::new();
                let commands = ay_frontend::parse(&script).expect("parse");
                assert!(
                    executor.execute_all(&commands).is_err(),
                    "{script} must be refused"
                );
            }
        }
        for sort_head in ay_core::ASCRIPTION_THEORY_SORT_HEADS {
            for z3_mode in [true, false] {
                for logic in [
                    "",
                    "(set-logic ALL)",
                    "(set-logic QF_DT)",
                    "(set-logic QF_UF)",
                ] {
                    let script = format!(
                        "{logic}\n\
                         (declare-datatypes (({sort_head} 1)) \
                         ((par (T) ((mk (fst T)) (nil)))))\n\
                         (declare-datatypes ((L2 0)) (((cons (hd Int) (tl L2)) (nil))))\n\
                         (declare-const v ({sort_head} Int))\n\
                         (assert (= v (as nil ({sort_head} Int))))\n\
                         (check-sat)\n(get-model)\n(get-value (v))\n"
                    );
                    let Ok(commands) = ay_frontend::parse(&script) else {
                        continue;
                    };
                    let mut executor = crate::Executor::new();
                    executor.set_competition_mode(z3_mode);
                    let Ok(outputs) = executor.execute_all(&commands) else {
                        continue;
                    };
                    let ascribed = format!("(as nil ({sort_head} ");
                    for output in &outputs {
                        assert!(
                            !output.contains(&ascribed),
                            "a declared {sort_head} prints a constructor the readers refuse \
                             ({logic}, z3_mode={z3_mode}): {output}"
                        );
                    }
                }
            }
        }
    }

    /// Texts `reads_as_bare` accepts, then texts it rejects.
    #[test]
    fn an_ascription_is_kept_only_where_every_reader_takes_it_as_the_bare_text() {
        for (bare, ascribed) in [
            ("nil", "(as nil L1)"),
            ("(w nil nil)", "(w (as nil L1) (as nil L1))"),
            ("(w  nil\n nil)", "(w  (as nil L1)\n (as nil L1))"),
            (
                "((x nil) (y (cons 1 nil)))",
                "((x (as nil L1)) (y (cons 1 (as nil L1))))",
            ),
            (
                "(store ((as const (Array Int L1)) nil) 4 nil)",
                "(store ((as const (Array Int L1)) (as nil L1)) 4 (as nil L1))",
            ),
            (
                "(model\n  (define-fun t () |My List| nil)\n)",
                "(model\n  (define-fun t () |My List| (as nil |My List|))\n)",
            ),
            // Quoted tokens, as `Executor::dt_value_head` prints names that
            // need quoting.
            ("|true|", "(as |true| L1)"),
            ("(w |a#b| ||)", "(w (as |a#b| L1) (as || L1))"),
            (r"(rec |y\|| nil)", r"(rec |y\|| (as nil L1))"),
        ] {
            assert!(reads_as_bare(bare, ascribed), "{ascribed}");
        }
        for (bare, ascribed) in [
            // A field of a list headed `as` ascribed.
            ("(as nil e1)", "(as (as nil L1) e1)"),
            (
                "(as nil (cons 1 nil))",
                "(as (as nil L1) (cons 1 (as nil L1)))",
            ),
            // The text-only reading takes both of these for `a`, and the
            // parsed form does not.
            ("(as a k)", "(as a (as k L2))"),
            // Here the bare text holds a name the frontend reads as no symbol
            // of that name.
            ("true", "(as |true| L1)"),
            ("(w true halt)", "(w (as |true| L1) halt)"),
            (":k", "(as |:k| L1)"),
            ("a#b", "(as |a#b| L1)"),
            ("a:b", "(as |a:b| L1)"),
            // One quoted symbol, `|x nil y|`, is not three fields.
            ("(rec |x nil y| nil)", "(rec |x (as nil L1) y| nil)"),
            // An ascription at the head of an application.
            ("(nil 1)", "((as nil L1) 1)"),
            // Another constructor than the bare text names.
            ("nil", "(as halt L1)"),
            // Other changes.
            ("(w nil nil)", "(w (as nil L1) nil nil)"),
            ("(w nil halt)", "(w (as nil L1) stop)"),
            // In the parsed form, the bars of `y|` and `z|` pair with the
            // bars of `|My List|`.
            (
                "(m (d y| L1 nil) (d t |My List| nil) (d z| L1 nil))",
                "(m (d y| L1 nil) (d t |My List| (as nil |My List|)) (d z| L1 nil))",
            ),
        ]
        .into_iter()
        .chain(UNPARSED_PAIRS)
        {
            assert!(!reads_as_bare(bare, ascribed), "{ascribed}");
        }
    }

    /// Pairs of a bare text and an ascribed one, for example with the
    /// unclosed bar of `p|q` or the token `a#b`, that
    /// `a_text_the_frontend_does_not_parse_keeps_no_ascription` checks.
    const UNPARSED_PAIRS: [(&str, &str); 3] = [
        ("(rec p|q nil c\"d)", "(rec p|q (as nil L1) c\"d)"),
        ("(as a#b nil)", "(as a#b (as nil L1))"),
        (
            "((a y|) (t nil) (b z|) (c a#b))",
            "((a y|) (t (as nil |My List|)) (b z|) (c a#b))",
        ),
    ];

    /// For each pair of `UNPARSED_PAIRS`, the `bare_constructor_spelling`
    /// texts are equal and `parse_sexps` refuses both texts, and
    /// `reads_as_bare` rejects the pair.
    #[test]
    fn a_text_the_frontend_does_not_parse_keeps_no_ascription() {
        for (bare, ascribed) in UNPARSED_PAIRS {
            assert_eq!(
                ay_core::bare_constructor_spelling(bare),
                ay_core::bare_constructor_spelling(ascribed),
                "{ascribed}"
            );
            assert!(ay_frontend::sexp::parse_sexps(bare).is_err(), "{bare}");
            assert!(
                ay_frontend::sexp::parse_sexps(ascribed).is_err(),
                "{ascribed}"
            );
            assert!(!reads_as_bare(bare, ascribed), "{ascribed}");
        }
    }

    /// `ascribed_nullary_constructor` gives the constructor paired with each
    /// text below.
    #[test]
    fn the_parsed_rule_is_the_shared_syntactic_one() {
        for (text, constructor) in [
            ("(as nil L1)", Some("nil")),
            ("(as const L1)", Some("const")),
            ("(as bag.empty (Bag Int))", Some("bag.empty")),
            ("(as nil (Tuple Int Bool))", Some("nil")),
            ("(as nil (Relation Int Int))", Some("nil")),
            ("(as seq.empty (Seq Int))", None),
            ("(as nil (Array Int Int))", None),
            ("(as ff3 (_ FiniteField 7))", None),
            ("(as @S!0 S)", None),
            ("(as nil)", None),
            ("(as nil ())", None),
        ] {
            assert_eq!(
                ascribed_nullary_constructor(&sexp(text)),
                constructor,
                "{text}"
            );
        }
    }
}
