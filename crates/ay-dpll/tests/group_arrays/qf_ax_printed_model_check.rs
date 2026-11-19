// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY-N9: the model `(get-model)` prints for a QF_AX `sat` must satisfy the
//! assertions when read back by a checker that shares no code with ay.
//!
//! SMT-COMP 2026 model validation rejected ay's model of a QF_AX instance
//! (two arrays over uninterpreted sorts, cells swapped eight times, the
//! arrays asserted different): the internal model was right, but the
//! printer dropped every array cell whose index was a witness element
//! (`@ay!wit!xidx!1`) and replaced the witness default by `@x9!0`, so the
//! printed arrays were not the validated ones.
//!
//! The checker below reads the printed `define-fun`s and evaluates the
//! asserted terms itself: `let`, the Boolean connectives, `=`, `distinct`,
//! `ite`, `select` and `store`, with abstract values compared by spelling and
//! arrays by denotation (equal at every index either side names and equal
//! defaults). For `unsat` answers of the randomised test a brute-force search
//! over small finite universes looks for a model ay should have found.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use rand::Rng;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::collections::HashMap;
use std::time::{Duration, Instant};

// ---------------------------------------------------------------- s-expressions

#[derive(Clone, Debug, PartialEq)]
enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

fn parse_sexps(text: &str) -> Vec<Sx> {
    let chars: Vec<char> = text.chars().collect();
    let mut pos = 0usize;
    let mut out = Vec::new();
    loop {
        skip_blank(&chars, &mut pos);
        if pos >= chars.len() {
            return out;
        }
        out.push(parse_one(&chars, &mut pos));
    }
}

fn skip_blank(chars: &[char], pos: &mut usize) {
    while *pos < chars.len() {
        if chars[*pos].is_whitespace() {
            *pos += 1;
        } else if chars[*pos] == ';' {
            while *pos < chars.len() && chars[*pos] != '\n' {
                *pos += 1;
            }
        } else {
            return;
        }
    }
}

fn parse_one(chars: &[char], pos: &mut usize) -> Sx {
    skip_blank(chars, pos);
    if chars[*pos] == '(' {
        *pos += 1;
        let mut items = Vec::new();
        loop {
            skip_blank(chars, pos);
            assert!(*pos < chars.len(), "unbalanced s-expression");
            if chars[*pos] == ')' {
                *pos += 1;
                return Sx::List(items);
            }
            items.push(parse_one(chars, pos));
        }
    }
    let mut atom = String::new();
    if chars[*pos] == '|' {
        *pos += 1;
        while chars[*pos] != '|' {
            atom.push(chars[*pos]);
            *pos += 1;
        }
        *pos += 1;
        return Sx::Atom(atom);
    }
    while *pos < chars.len() && !chars[*pos].is_whitespace() && !"();".contains(chars[*pos]) {
        atom.push(chars[*pos]);
        *pos += 1;
    }
    Sx::Atom(atom)
}

fn atom(sx: &Sx) -> Option<&str> {
    match sx {
        Sx::Atom(a) => Some(a),
        Sx::List(_) => None,
    }
}

// --------------------------------------------------------------------- values

#[derive(Clone, Debug)]
enum V {
    Bool(bool),
    /// An abstract element of an uninterpreted sort, by spelling.
    Elem(String),
    /// Default and stores, oldest first (the last store at an index wins).
    Array(Box<V>, Vec<(V, V)>),
}

fn select(array: &V, index: &V) -> V {
    let V::Array(default, stores) = array else {
        panic!("select on a non-array {array:?}");
    };
    stores
        .iter()
        .rev()
        .find(|(k, _)| equal(k, index, None))
        .map_or_else(|| (**default).clone(), |(_, v)| v.clone())
}

/// Equality. With `universe`, arrays are compared at every element of the
/// finite index universe; without, by denotation over an unbounded universe:
/// equal defaults and agreement at every index either side names.
fn equal(a: &V, b: &V, universe: Option<&[V]>) -> bool {
    match (a, b) {
        (V::Bool(x), V::Bool(y)) => x == y,
        (V::Elem(x), V::Elem(y)) => x == y,
        (V::Array(da, sa), V::Array(db, sb)) => match universe {
            Some(elements) => elements
                .iter()
                .all(|k| equal(&select(a, k), &select(b, k), universe)),
            None => {
                equal(da, db, None)
                    && sa
                        .iter()
                        .chain(sb.iter())
                        .all(|(k, _)| equal(&select(a, k), &select(b, k), None))
            }
        },
        _ => panic!("ill-sorted comparison {a:?} = {b:?}"),
    }
}

// ------------------------------------------------------------------ evaluator

struct Eval<'a> {
    universe: Option<&'a [V]>,
}

impl Eval<'_> {
    fn eval(&self, term: &Sx, env: &HashMap<String, V>) -> V {
        match term {
            Sx::Atom(name) => match name.as_str() {
                "true" => V::Bool(true),
                "false" => V::Bool(false),
                _ => env
                    .get(name)
                    .unwrap_or_else(|| panic!("no value for `{name}`"))
                    .clone(),
            },
            Sx::List(items) => self.eval_app(items, env),
        }
    }

    fn eval_app(&self, items: &[Sx], env: &HashMap<String, V>) -> V {
        // `(as tok S)`: an abstract value of the model.
        if atom(&items[0]) == Some("as") {
            return V::Elem(atom(&items[1]).expect("abstract value").to_string());
        }
        // `((as const (Array I E)) v)`.
        if let Sx::List(head) = &items[0] {
            assert_eq!(atom(&head[0]), Some("as"));
            assert_eq!(atom(&head[1]), Some("const"));
            return V::Array(Box::new(self.eval(&items[1], env)), Vec::new());
        }
        let op = atom(&items[0]).expect("operator");
        let args = &items[1..];
        let bool_of = |t: &Sx| match self.eval(t, env) {
            V::Bool(b) => b,
            other => panic!("expected Bool, got {other:?}"),
        };
        match op {
            "let" => {
                let Sx::List(bindings) = &args[0] else {
                    panic!("let bindings");
                };
                let mut inner = env.clone();
                for binding in bindings {
                    let Sx::List(pair) = binding else {
                        panic!("let binding");
                    };
                    let name = atom(&pair[0]).expect("let name").to_string();
                    inner.insert(name, self.eval(&pair[1], env));
                }
                self.eval(&args[1], &inner)
            }
            "not" => V::Bool(!bool_of(&args[0])),
            "and" => V::Bool(args.iter().all(bool_of)),
            "or" => V::Bool(args.iter().any(bool_of)),
            "=>" => V::Bool(!bool_of(&args[0]) || bool_of(&args[1])),
            "xor" => V::Bool(bool_of(&args[0]) != bool_of(&args[1])),
            "ite" => {
                if bool_of(&args[0]) {
                    self.eval(&args[1], env)
                } else {
                    self.eval(&args[2], env)
                }
            }
            "=" => {
                let values: Vec<V> = args.iter().map(|t| self.eval(t, env)).collect();
                V::Bool(
                    values
                        .windows(2)
                        .all(|w| equal(&w[0], &w[1], self.universe)),
                )
            }
            "distinct" => {
                let values: Vec<V> = args.iter().map(|t| self.eval(t, env)).collect();
                let mut all = true;
                for i in 0..values.len() {
                    for j in i + 1..values.len() {
                        all &= !equal(&values[i], &values[j], self.universe);
                    }
                }
                V::Bool(all)
            }
            "select" => select(&self.eval(&args[0], env), &self.eval(&args[1], env)),
            "store" => {
                let V::Array(default, mut stores) = self.eval(&args[0], env) else {
                    panic!("store on a non-array");
                };
                stores.push((self.eval(&args[1], env), self.eval(&args[2], env)));
                V::Array(default, stores)
            }
            other => panic!("operator `{other}` is outside the checker's fragment"),
        }
    }
}

// ------------------------------------------------------------- script access

/// Declared constants of `script` (name, sort) and its asserted terms.
fn declarations_and_assertions(script: &str) -> (Vec<(String, Sx)>, Vec<Sx>) {
    let mut decls = Vec::new();
    let mut asserts = Vec::new();
    for command in parse_sexps(script) {
        let Sx::List(items) = command else { continue };
        match atom(&items[0]) {
            Some("declare-fun") => {
                assert_eq!(items[2], Sx::List(Vec::new()), "only constants");
                decls.push((atom(&items[1]).unwrap().to_string(), items[3].clone()));
            }
            Some("declare-const") => {
                decls.push((atom(&items[1]).unwrap().to_string(), items[2].clone()));
            }
            Some("assert") => asserts.push(items[1].clone()),
            _ => {}
        }
    }
    (decls, asserts)
}

/// Read ay's printed model into constant values.
fn read_model(model_text: &str) -> HashMap<String, V> {
    let mut env = HashMap::new();
    let checker = Eval { universe: None };
    for top in parse_sexps(model_text) {
        let Sx::List(items) = top else {
            panic!("model is not a list: {model_text}");
        };
        let start = usize::from(atom(&items[0]) == Some("model"));
        for def in &items[start..] {
            let Sx::List(parts) = def else {
                panic!("model entry {def:?}");
            };
            assert_eq!(atom(&parts[0]), Some("define-fun"), "{model_text}");
            assert_eq!(parts[2], Sx::List(Vec::new()), "only constants");
            let value = checker.eval(&parts[4], &HashMap::new());
            env.insert(atom(&parts[1]).unwrap().to_string(), value);
        }
    }
    env
}

/// Solve `script` (which ends in `(check-sat)` and `(get-model)`); returns the
/// answer and, for `sat`, the printed model.
fn solve(script: &str) -> (String, Option<String>) {
    let commands = parse(script).expect("parse");
    let mut exec = Executor::new();
    // A case that runs out of time answers `unknown`, which checks nothing
    // and is allowed; the deadline keeps the randomised test bounded.
    exec.set_deadline(Some(Instant::now() + Duration::from_secs(5)));
    let outputs = exec.execute_all(&commands).expect("execute_all");
    let answer = outputs[0].trim().to_string();
    let model = (answer == "sat").then(|| outputs[1].clone());
    (answer, model)
}

/// Every assertion of `script` holds in `model_text`, read independently.
fn assert_printed_model_holds(script: &str, model_text: &str) {
    // A constant no assertion mentions may be left out of the model; the
    // evaluator panics on any constant it needs and does not find.
    let (_, asserts) = declarations_and_assertions(script);
    assert!(
        !model_text.trim_start().starts_with("(error"),
        "`sat` without a printable model:\n{model_text}\nscript:\n{script}"
    );
    let env = read_model(model_text);
    let checker = Eval { universe: None };
    for (i, assertion) in asserts.iter().enumerate() {
        let value = checker.eval(assertion, &env);
        assert!(
            matches!(value, V::Bool(true)),
            "assertion {i} is false in the printed model:\n{model_text}\nscript:\n{script}"
        );
    }
}

// ------------------------------------------------------------- the instance

/// SMT-COMP 2026 ModelValidation/QF_AX/e70901ec… (scrambled), verbatim.
/// cvc5, yices2 and SMTInterpol answer `sat` with models Dolmen accepts.
const N9_INSTANCE: &str = r"
(set-option :print-success false)
(set-option :produce-models true)
(set-logic QF_AX)
(declare-sort x17 0)
(declare-sort x9 0)
(declare-fun x2 () x17)
(declare-fun x24 () (Array x17 x9))
(declare-fun x10 () x17)
(declare-fun x29 () x17)
(declare-fun x18 () x17)
(declare-fun x25 () x17)
(declare-fun x28 () x17)
(declare-fun x5 () x17)
(declare-fun x23 () (Array x17 x9))
(declare-fun x11 () x17)
(declare-fun x4 () x17)
(assert (let ((x26 (store x24 x25 (select x23 x25))) (x21 (store x23 x25 (select x24 x25)))) (let ((x16 (store x21 x2 (select x26 x2))) (x8 (store x26 x2 (select x21 x2)))) (let ((x20 (store x16 x11 (select x8 x11))) (x3 (store x8 x11 (select x16 x11)))) (let ((x12 (store x20 x29 (select x3 x29))) (x27 (store x3 x29 (select x20 x29)))) (let ((x6 (store x12 x18 (select x27 x18))) (x15 (store x27 x18 (select x12 x18)))) (let ((x19 (store x6 x28 (select x15 x28))) (x22 (store x15 x28 (select x6 x28)))) (let ((x1 (store x22 x10 (select x19 x10))) (x13 (store x19 x10 (select x22 x10)))) (let ((x14 (store x13 x4 (select x1 x4))) (x7 (store x1 x4 (select x13 x4)))) (= (store x14 x25 (select x7 x5)) (store x7 x5 (select x14 x5))))))))))))
(assert (not (= x24 x23)))
(check-sat)
(get-model)
";

/// Before the fix ay printed `x23` and `x24` with their `@ay!wit!xidx!0` cell
/// only and default `@x9!0`; the first assertion is then false (with every
/// swap index at one element and `x5` at another it needs
/// `x24[x25] = x24[x5]`).
#[test]
#[timeout(60_000)]
fn n9_qf_ax_swap_printed_model_satisfies_assertions() {
    let (answer, model) = solve(N9_INSTANCE);
    assert_eq!(answer, "sat", "three reference solvers answer sat");
    assert_printed_model_holds(N9_INSTANCE, &model.expect("sat prints a model"));
}

// ----------------------------------------------------------- random formulas

const INDICES: [&str; 4] = ["i0", "i1", "i2", "i3"];
const ELEMENTS: [&str; 2] = ["e0", "e1"];
const ARRAYS: [&str; 2] = ["a0", "a1"];

fn header() -> String {
    let mut s = String::from(
        "(set-option :produce-models true)\n(set-logic QF_AX)\n\
         (declare-sort I 0)\n(declare-sort E 0)\n",
    );
    for i in INDICES {
        s.push_str(&format!("(declare-fun {i} () I)\n"));
    }
    for e in ELEMENTS {
        s.push_str(&format!("(declare-fun {e} () E)\n"));
    }
    for a in ARRAYS {
        s.push_str(&format!("(declare-fun {a} () (Array I E))\n"));
    }
    s
}

fn pick<'a>(rng: &mut ChaCha8Rng, names: &[&'a str]) -> &'a str {
    names[rng.gen_range(0..names.len())]
}

fn gen_array(rng: &mut ChaCha8Rng, depth: u32) -> String {
    if depth == 0 || rng.gen_bool(0.35) {
        return pick(rng, &ARRAYS).to_string();
    }
    let base = gen_array(rng, depth - 1);
    let index = pick(rng, &INDICES);
    let value = gen_element(rng, depth - 1);
    format!("(store {base} {index} {value})")
}

fn gen_element(rng: &mut ChaCha8Rng, depth: u32) -> String {
    if depth == 0 || rng.gen_bool(0.5) {
        return pick(rng, &ELEMENTS).to_string();
    }
    let array = gen_array(rng, depth - 1);
    format!("(select {array} {})", pick(rng, &INDICES))
}

fn gen_literal(rng: &mut ChaCha8Rng) -> String {
    let atom = match rng.gen_range(0..3) {
        0 => format!("(= {} {})", gen_array(rng, 3), gen_array(rng, 3)),
        1 => format!("(= {} {})", gen_element(rng, 3), gen_element(rng, 3)),
        _ => format!("(= {} {})", pick(rng, &INDICES), pick(rng, &INDICES)),
    };
    if rng.gen_bool(0.4) {
        format!("(not {atom})")
    } else {
        atom
    }
}

/// A generic small QF_AX formula: 2 to 4 clauses of one or two literals.
fn gen_generic(rng: &mut ChaCha8Rng) -> String {
    let mut s = header();
    for _ in 0..rng.gen_range(2..=4) {
        let clause = if rng.gen_bool(0.3) {
            format!("(or {} {})", gen_literal(rng), gen_literal(rng))
        } else {
            gen_literal(rng)
        };
        s.push_str(&format!("(assert {clause})\n"));
    }
    s.push_str("(check-sat)\n(get-model)\n");
    s
}

/// The shape of the SMT-COMP instance: swap cells of `a0` and `a1` a few
/// times, assert the final chains equal after one more crossed write, and
/// assert the bases different.
fn gen_swap(rng: &mut ChaCha8Rng) -> String {
    let mut s = header();
    let steps = rng.gen_range(1..=3);
    let mut body = String::new();
    let mut close = String::new();
    let (mut x, mut y) = ("a0".to_string(), "a1".to_string());
    for k in 0..steps {
        let j = pick(rng, &INDICES);
        let (nx, ny) = (format!("x{k}"), format!("y{k}"));
        body.push_str(&format!(
            "(let (({nx} (store {x} {j} (select {y} {j}))) ({ny} (store {y} {j} (select {x} {j})))) "
        ));
        close.push(')');
        (x, y) = (nx, ny);
    }
    let (p, q) = (pick(rng, &INDICES), pick(rng, &INDICES));
    body.push_str(&format!(
        "(= (store {x} {p} (select {y} {q})) (store {y} {q} (select {x} {p})))"
    ));
    s.push_str(&format!("(assert {body}{close})\n"));
    s.push_str("(assert (not (= a0 a1)))\n");
    if rng.gen_bool(0.5) {
        s.push_str(&format!("(assert {})\n", gen_literal(rng)));
    }
    s.push_str("(check-sat)\n(get-model)\n");
    s
}

/// Search every interpretation over index universes of 1 to 3 elements and
/// element universes of 1 or 2 elements; `true` when one satisfies `script`.
fn has_small_model(script: &str) -> bool {
    let (decls, asserts) = declarations_and_assertions(script);
    for n_index in 1..=3usize {
        for n_elem in 1..=2usize {
            let index_values: Vec<V> = (0..n_index).map(|k| V::Elem(format!("i!{k}"))).collect();
            let elem_values: Vec<V> = (0..n_elem).map(|k| V::Elem(format!("e!{k}"))).collect();
            let arrays: Vec<V> = (0..n_elem.pow(n_index as u32))
                .map(|code| {
                    let mut c = code;
                    let mut stores = Vec::new();
                    for idx in &index_values {
                        stores.push((idx.clone(), elem_values[c % n_elem].clone()));
                        c /= n_elem;
                    }
                    V::Array(Box::new(elem_values[0].clone()), stores)
                })
                .collect();
            let domains: Vec<&[V]> = decls
                .iter()
                .map(|(_, sort)| match atom(sort) {
                    Some("I") => index_values.as_slice(),
                    Some("E") => elem_values.as_slice(),
                    _ => arrays.as_slice(),
                })
                .collect();
            let checker = Eval {
                universe: Some(&index_values),
            };
            let mut counters = vec![0usize; decls.len()];
            loop {
                let env: HashMap<String, V> = decls
                    .iter()
                    .zip(&counters)
                    .zip(&domains)
                    .map(|(((name, _), &c), dom)| (name.clone(), dom[c].clone()))
                    .collect();
                if asserts
                    .iter()
                    .all(|a| matches!(checker.eval(a, &env), V::Bool(true)))
                {
                    return true;
                }
                let mut k = 0;
                loop {
                    if k == counters.len() {
                        break;
                    }
                    counters[k] += 1;
                    if counters[k] < domains[k].len() {
                        break;
                    }
                    counters[k] = 0;
                    k += 1;
                }
                if k == counters.len() {
                    break;
                }
            }
        }
    }
    false
}

/// Randomised: every `sat` model ay prints for a small QF_AX formula holds
/// under the independent checker, and no `unsat` has a small finite model.
#[test]
#[timeout(600_000)]
fn random_small_qf_ax_printed_models_hold() {
    let mut rng = ChaCha8Rng::seed_from_u64(0xA7_0009);
    let (mut sat, mut unsat, mut unknown) = (0usize, 0usize, 0usize);
    for case in 0..160 {
        let script = if case % 2 == 0 {
            gen_generic(&mut rng)
        } else {
            gen_swap(&mut rng)
        };
        let (answer, model) = solve(&script);
        match answer.as_str() {
            "sat" => {
                sat += 1;
                assert_printed_model_holds(&script, &model.expect("sat prints a model"));
            }
            "unsat" => {
                unsat += 1;
                assert!(
                    !has_small_model(&script),
                    "case {case}: ay answers unsat, but a finite model exists:\n{script}"
                );
            }
            _ => unknown += 1,
        }
    }
    eprintln!("random QF_AX: sat={sat} unsat={unsat} unknown={unknown}");
    assert!(
        sat >= 40,
        "too few sat answers to exercise the printer: {sat}"
    );
}
