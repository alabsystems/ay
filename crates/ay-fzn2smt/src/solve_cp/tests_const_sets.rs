// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Shared by the CP and SMT back ends' constant-set-operand tests (AY-OTHER-7).
// Each case is one set constraint with a constant operand over small
// variables; every assignment of the variables is fixed in turn and the
// verdict must match the brute-force predicate.

#[derive(Clone, Copy)]
enum CaseVar {
    Set(&'static str, i64, i64),
    Bool(&'static str),
    Int(&'static str, i64, i64),
}

#[derive(Clone, Debug, PartialEq)]
enum CaseVal {
    Set(Vec<i64>),
    Bool(bool),
    Int(i64),
}

type Assignment = Vec<(&'static str, CaseVal)>;

struct ConstSetCase {
    name: &'static str,
    prelude: &'static str,
    vars: &'static [CaseVar],
    constraint: &'static str,
    holds: fn(&dyn Fn(&str) -> CaseVal) -> bool,
}

fn set_of(v: CaseVal) -> Vec<i64> {
    match v {
        CaseVal::Set(s) => s,
        other => panic!("expected a set, got {other:?}"),
    }
}

fn bool_of(v: CaseVal) -> bool {
    match v {
        CaseVal::Bool(b) => b,
        other => panic!("expected a bool, got {other:?}"),
    }
}

fn int_of(v: CaseVal) -> i64 {
    match v {
        CaseVal::Int(i) => i,
        other => panic!("expected an int, got {other:?}"),
    }
}

fn sorted(mut v: Vec<i64>) -> Vec<i64> {
    v.sort_unstable();
    v.dedup();
    v
}

fn union(a: &[i64], b: &[i64]) -> Vec<i64> {
    sorted(a.iter().chain(b).copied().collect())
}

fn inter(a: &[i64], b: &[i64]) -> Vec<i64> {
    a.iter().copied().filter(|x| b.contains(x)).collect()
}

fn minus(a: &[i64], b: &[i64]) -> Vec<i64> {
    a.iter().copied().filter(|x| !b.contains(x)).collect()
}

fn const_set_cases() -> Vec<ConstSetCase> {
    use CaseVar::*;
    vec![
        ConstSetCase {
            // MiniZinc's disjoint(): `set_intersect(S1, S2, 1..0)`.
            name: "intersect_empty_range_result",
            prelude: "",
            vars: &[Set("a", 1, 3), Set("b", 1, 3)],
            constraint: "set_intersect(a, b, 1..0)",
            holds: |v| inter(&set_of(v("a")), &set_of(v("b"))).is_empty(),
        },
        ConstSetCase {
            name: "intersect_literal_operand",
            prelude: "",
            vars: &[Set("a", 1, 4), Set("c", 1, 4)],
            constraint: "set_intersect(a, {2, 4}, c)",
            holds: |v| set_of(v("c")) == inter(&set_of(v("a")), &[2, 4]),
        },
        ConstSetCase {
            name: "intersect_empty_literal_operand",
            prelude: "",
            vars: &[Set("a", 1, 2), Set("c", 1, 2)],
            constraint: "set_intersect({}, a, c)",
            holds: |v| {
                let _ = v("a");
                set_of(v("c")).is_empty()
            },
        },
        ConstSetCase {
            name: "union_literal_operand",
            prelude: "",
            vars: &[Set("a", 1, 3), Set("c", 1, 4)],
            constraint: "set_union(a, {2, 3}, c)",
            holds: |v| set_of(v("c")) == union(&set_of(v("a")), &[2, 3]),
        },
        ConstSetCase {
            name: "diff_range_minuend",
            prelude: "",
            vars: &[Set("a", 1, 3), Set("c", 1, 4)],
            constraint: "set_diff(2..4, a, c)",
            holds: |v| set_of(v("c")) == minus(&[2, 3, 4], &set_of(v("a"))),
        },
        ConstSetCase {
            name: "symdiff_operand_outside_universe",
            prelude: "",
            vars: &[Set("a", 1, 2), Set("c", 1, 5)],
            constraint: "set_symdiff(a, {1, 5}, c)",
            holds: |v| {
                let a = set_of(v("a"));
                set_of(v("c")) == union(&minus(&a, &[1, 5]), &minus(&[1, 5], &a))
            },
        },
        ConstSetCase {
            name: "eq_range",
            prelude: "",
            vars: &[Set("a", 1, 3)],
            constraint: "set_eq(a, 1..2)",
            holds: |v| set_of(v("a")) == vec![1, 2],
        },
        ConstSetCase {
            name: "ne_empty",
            prelude: "",
            vars: &[Set("a", 1, 3)],
            constraint: "set_ne(a, {})",
            holds: |v| !set_of(v("a")).is_empty(),
        },
        ConstSetCase {
            name: "subset_literal",
            prelude: "",
            vars: &[Set("a", 1, 3)],
            constraint: "set_subset(a, {1, 3})",
            holds: |v| set_of(v("a")).iter().all(|x| [1, 3].contains(x)),
        },
        ConstSetCase {
            name: "superset_par_identifier",
            prelude: "set of int: K = {1, 3};\n",
            vars: &[Set("a", 1, 3)],
            constraint: "set_superset(a, K)",
            holds: |v| [1, 3].iter().all(|x| set_of(v("a")).contains(x)),
        },
        ConstSetCase {
            name: "le_literal_lexicographic",
            prelude: "",
            vars: &[Set("a", 1, 3)],
            constraint: "set_le(a, {2})",
            holds: |v| set_of(v("a")) <= vec![2],
        },
        ConstSetCase {
            name: "card_of_range",
            prelude: "",
            vars: &[Int("x", 0, 4)],
            constraint: "set_card(2..4, x)",
            holds: |v| int_of(v("x")) == 3,
        },
        ConstSetCase {
            name: "eq_reif_literal",
            prelude: "",
            vars: &[Set("a", 1, 2), Bool("r")],
            constraint: "set_eq_reif(a, {1}, r)",
            holds: |v| bool_of(v("r")) == (set_of(v("a")) == vec![1]),
        },
        ConstSetCase {
            name: "subset_reif_constant_left",
            prelude: "",
            vars: &[Set("a", 1, 3), Bool("r")],
            constraint: "set_subset_reif({2}, a, r)",
            holds: |v| bool_of(v("r")) == set_of(v("a")).contains(&2),
        },
    ]
}

fn case_assignments(vars: &[CaseVar]) -> Vec<Assignment> {
    let mut all: Vec<Assignment> = vec![Vec::new()];
    for var in vars {
        let (name, values): (&'static str, Vec<CaseVal>) = match *var {
            CaseVar::Set(name, lo, hi) => {
                let width = (hi - lo + 1) as u32;
                let values = (0..(1u32 << width))
                    .map(|mask| {
                        CaseVal::Set(
                            (0..width)
                                .filter(|bit| mask & (1 << bit) != 0)
                                .map(|bit| lo + i64::from(bit))
                                .collect(),
                        )
                    })
                    .collect();
                (name, values)
            }
            CaseVar::Bool(name) => (name, vec![CaseVal::Bool(false), CaseVal::Bool(true)]),
            CaseVar::Int(name, lo, hi) => (name, (lo..=hi).map(CaseVal::Int).collect()),
        };
        all = all
            .into_iter()
            .flat_map(|prefix| {
                values.iter().map(move |value| {
                    let mut next = prefix.clone();
                    next.push((name, value.clone()));
                    next
                })
            })
            .collect();
    }
    all
}

/// The case's model with every variable fixed by its declaration, so the
/// constraint under test is the only thing deciding the verdict.
fn fixed_case_model(case: &ConstSetCase, assignment: &Assignment) -> String {
    let mut fzn = case.prelude.to_string();
    for (var, (_, value)) in case.vars.iter().zip(assignment) {
        let decl = match (var, value) {
            (CaseVar::Set(name, lo, hi), CaseVal::Set(s)) => {
                let elems: Vec<String> = s.iter().map(i64::to_string).collect();
                format!(
                    "var set of {lo}..{hi}: {name} = {{{}}};\n",
                    elems.join(", ")
                )
            }
            (CaseVar::Bool(name), CaseVal::Bool(b)) => format!("var bool: {name} = {b};\n"),
            (CaseVar::Int(name, lo, hi), CaseVal::Int(i)) => {
                format!("var {lo}..{hi}: {name} = {i};\n")
            }
            _ => unreachable!("assignment follows the variable list"),
        };
        fzn.push_str(&decl);
    }
    fzn.push_str(&format!(
        "constraint {};\nsolve satisfy;\n",
        case.constraint
    ));
    fzn
}

/// Run every case against `verdict(model) -> Some(true)` (sat) or
/// `Some(false)` (unsat); `None` is a failure.
fn check_const_set_cases(verdict: impl Fn(&str) -> Option<bool>) {
    for case in const_set_cases() {
        for assignment in case_assignments(case.vars) {
            let lookup = |name: &str| {
                assignment
                    .iter()
                    .find(|(n, _)| *n == name)
                    .map(|(_, v)| v.clone())
                    .expect("case variable")
            };
            let expected = (case.holds)(&lookup);
            let model = fixed_case_model(&case, &assignment);
            assert_eq!(
                verdict(&model),
                Some(expected),
                "case {}: assignment {assignment:?}\n{model}",
                case.name
            );
        }
    }
}

#[test]
fn constant_set_operands_match_brute_force() {
    check_const_set_cases(|model| match super::tests::parse_and_solve(model) {
        ay_cp::engine::CpSolveResult::Sat(_) => Some(true),
        ay_cp::engine::CpSolveResult::Unsat => Some(false),
        _ => None,
    });
}

/// The full warehouse constraint shape: `disjoint` flattened by MiniZinc, with
/// the probe that decides the CP route accepting it.
#[test]
fn disjoint_from_minizinc_is_supported_by_the_cp_probe() {
    let model = ay_flatzinc_parser::parse_flatzinc(
        "var set of 1..3: a;\nvar set of 1..3: b;\n\
         constraint set_intersect(a, b, 1..0);\nsolve satisfy;\n",
    )
    .expect("parse failed");
    let unsupported = super::unsupported_constraints(&model).expect("probe must not fail");
    assert!(unsupported.is_empty(), "{unsupported:?}");
}
