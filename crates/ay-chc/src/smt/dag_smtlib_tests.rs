// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the DAG-linear printer and counter (C-P2).
//!
//! The INV-12 differential (`dag_printer_matches_tree_printer_under_z3`)
//! prints ≥ 10 000 random shared DAGs over Bool/Int/Real (ITE, arithmetic,
//! comparisons, connectives) both ways and asks z3 to prove each pair
//! equivalent; it is skipped when `z3` is not on `PATH`.

use super::*;
use crate::{ChcSort, ChcVar};
use std::io::Write as _;
use std::process::{Command, Stdio};

const CAPS: DagCaps = DagCaps {
    max_unique_nodes: 1 << 20,
    max_depth: 512,
};

fn op(op: ChcOp, args: &[&Arc<ChcExpr>]) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::Op(
        op,
        args.iter().map(|a| Arc::clone(a)).collect(),
    ))
}

fn var(name: &str, sort: ChcSort) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::var(ChcVar::new(name, sort)))
}

fn dag_text(root: &ChcExpr) -> String {
    let mut out = String::new();
    write_asserts_dag(&mut out, &[root], CAPS).unwrap();
    out
}

fn tree_text(root: &ChcExpr) -> String {
    format!("(assert {})\n", InvariantModel::expr_to_smtlib(root))
}

#[test]
fn unshared_formulas_print_byte_identical_to_the_tree_printer() {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let r = ChcExpr::var(ChcVar::new("r", ChcSort::Real));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Bool));
    let bv = ChcExpr::var(ChcVar::new("|odd name|", ChcSort::BitVec(8)));
    let arr = ChcExpr::var(ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    ));
    let formulas = vec![
        ChcExpr::and_all([
            ChcExpr::le(ChcExpr::Int(-3), x.clone()),
            ChcExpr::ne(x.clone(), ChcExpr::Int(7)),
            ChcExpr::implies(b.clone(), ChcExpr::lt(r.clone(), ChcExpr::Real(-1, 3))),
        ]),
        ChcExpr::eq(
            ChcExpr::ite(
                b.clone(),
                ChcExpr::neg(x.clone()),
                ChcExpr::mul(ChcExpr::Int(2), x.clone()),
            ),
            ChcExpr::Op(
                ChcOp::Mod,
                vec![Arc::new(x.clone()), Arc::new(ChcExpr::Int(5))],
            ),
        ),
        ChcExpr::Op(
            ChcOp::BvULe,
            vec![
                Arc::new(ChcExpr::Op(
                    ChcOp::BvExtract(7, 0),
                    vec![Arc::new(bv.clone())],
                )),
                Arc::new(ChcExpr::BitVec(3, 8)),
            ],
        ),
        ChcExpr::eq(
            ChcExpr::select(arr.clone(), x.clone()),
            ChcExpr::select(
                ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Int(0))),
                ChcExpr::Int(1),
            ),
        ),
        ChcExpr::not(ChcExpr::or(b.clone(), ChcExpr::ge(r, ChcExpr::Real(5, 2)))),
    ];
    for formula in &formulas {
        assert_eq!(dag_text(formula), tree_text(formula));
    }
}

#[test]
fn shared_nodes_are_bound_once_level_by_level() {
    let a = var("a", ChcSort::Int);
    let b = var("b", ChcSort::Int);
    let sum = op(ChcOp::Add, &[&a, &b]);
    let prod = op(ChcOp::Mul, &[&sum, &sum]);
    let root = ChcExpr::Op(ChcOp::Lt, vec![Arc::clone(&prod), Arc::clone(&prod)]);
    let mut out = String::new();
    let stats = write_asserts_dag(&mut out, &[&root], CAPS).unwrap();
    assert_eq!(
        out,
        "(assert (let ((_d0 (+ a b))) (let ((_d1 (* _d0 _d0))) (< _d1 _d1))))\n"
    );
    assert_eq!(stats.shared_nodes, 2);
    assert_eq!(stats.unique_nodes, 5);
    assert_eq!(stats.max_depth, 3);
}

#[test]
fn binder_prefix_never_captures_a_formula_symbol() {
    let clash = var("_d0", ChcSort::Int);
    let other = var("_d_1", ChcSort::Int);
    let sum = op(ChcOp::Add, &[&clash, &other]);
    let root = ChcExpr::Op(ChcOp::Eq, vec![Arc::clone(&sum), Arc::clone(&sum)]);
    let text = dag_text(&root);
    assert_eq!(
        text,
        "(assert (let ((_d__0 (+ _d0 _d_1))) (= _d__0 _d__0)))\n"
    );
}

/// e_{i+1} = (+ e_i e_i): a 2^20-leaf tree that is a 41-node DAG.
fn doubling_chain(levels: usize) -> Arc<ChcExpr> {
    let mut e = var("x", ChcSort::Int);
    for _ in 0..levels {
        e = op(ChcOp::Add, &[&e, &e]);
    }
    e
}

#[test]
fn counting_is_linear_in_distinct_nodes() {
    let root = doubling_chain(20);
    let stats = count_dag(&[root.as_ref()], CAPS).unwrap();
    assert_eq!(stats.unique_nodes, 21);
    assert_eq!(stats.shared_nodes, 19);
    assert_eq!(stats.max_depth, 20);
    // The same root twice counts once.
    let twice = count_dag(&[root.as_ref(), root.as_ref()], CAPS).unwrap();
    assert_eq!(twice.unique_nodes, 21);
    let text = dag_text(&root);
    assert!(
        text.len() < 1_000,
        "DAG text must stay linear: {} bytes",
        text.len()
    );
}

#[test]
fn caps_refuse_and_leave_the_output_untouched() {
    let root = doubling_chain(20);
    let tight = DagCaps {
        max_unique_nodes: 20,
        max_depth: 512,
    };
    assert_eq!(
        count_dag(&[root.as_ref()], tight),
        Err(DagError::UniqueNodeCap)
    );
    let shallow = DagCaps {
        max_unique_nodes: 1 << 20,
        max_depth: 19,
    };
    assert_eq!(
        count_dag(&[root.as_ref()], shallow),
        Err(DagError::DepthCap)
    );
    let mut out = String::from("keep");
    assert!(write_asserts_dag(&mut out, &[root.as_ref()], shallow).is_err());
    assert_eq!(out, "keep");
    // A shared node first met shallowly and later deeply is still charged at
    // its deepest occurrence.
    let leaf_chain = doubling_chain(3);
    let mut deep = Arc::clone(&leaf_chain);
    for _ in 0..5 {
        deep = op(ChcOp::Neg, &[&deep]);
    }
    let root = ChcExpr::Op(ChcOp::Eq, vec![Arc::clone(&leaf_chain), deep]);
    let at_limit = DagCaps {
        max_unique_nodes: 1 << 20,
        max_depth: 9,
    };
    assert_eq!(count_dag(&[&root], at_limit).unwrap().max_depth, 9);
    let below_limit = DagCaps {
        max_unique_nodes: 1 << 20,
        max_depth: 8,
    };
    assert_eq!(count_dag(&[&root], below_limit), Err(DagError::DepthCap));
}

#[test]
fn parser_markers_are_unsupported() {
    let marker = ChcExpr::IsTesterMarker("C".to_owned());
    assert_eq!(
        count_dag(&[&marker], CAPS),
        Err(DagError::Unsupported("internal parser marker"))
    );
}

// ---------------------------------------------------------------------------
// INV-12 differential: random shared DAGs, tree vs DAG printing, z3-checked.
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Bool,
    Int,
    Real,
}

/// Pools of already-built nodes per sort; new nodes reuse pool members, so
/// sharing is pervasive and nested.
struct Pools {
    bools: Vec<Arc<ChcExpr>>,
    ints: Vec<Arc<ChcExpr>>,
    reals: Vec<Arc<ChcExpr>>,
}

impl Pools {
    fn new() -> Self {
        let mut pools = Self {
            bools: Vec::new(),
            ints: Vec::new(),
            reals: Vec::new(),
        };
        for i in 0..3 {
            pools.bools.push(var(&format!("b{i}"), ChcSort::Bool));
            pools.ints.push(var(&format!("i{i}"), ChcSort::Int));
            pools.reals.push(var(&format!("r{i}"), ChcSort::Real));
        }
        pools.ints.push(Arc::new(ChcExpr::Int(-2)));
        pools.ints.push(Arc::new(ChcExpr::Int(5)));
        pools.reals.push(Arc::new(ChcExpr::Real(-3, 4)));
        pools.reals.push(Arc::new(ChcExpr::Real(7, 1)));
        pools
    }

    fn pick(&self, rng: &mut Rng, kind: Kind) -> Arc<ChcExpr> {
        let pool = match kind {
            Kind::Bool => &self.bools,
            Kind::Int => &self.ints,
            Kind::Real => &self.reals,
        };
        // Bias toward recent (deeper) nodes.
        let len = pool.len();
        let idx = if rng.below(3) == 0 {
            rng.below(len)
        } else {
            len - 1 - rng.below(len.min(6))
        };
        Arc::clone(&pool[idx])
    }

    fn newest(&self, kind: Kind) -> &Arc<ChcExpr> {
        let pool = match kind {
            Kind::Bool => &self.bools,
            Kind::Int => &self.ints,
            Kind::Real => &self.reals,
        };
        &pool[pool.len() - 1]
    }

    fn grow(&mut self, rng: &mut Rng) {
        let kind = [Kind::Bool, Kind::Int, Kind::Real][rng.below(3)];
        let node = match kind {
            Kind::Bool => {
                let num = if rng.below(2) == 0 {
                    Kind::Int
                } else {
                    Kind::Real
                };
                match rng.below(7) {
                    0 => op(
                        ChcOp::And,
                        &[&self.pick(rng, Kind::Bool), &self.pick(rng, Kind::Bool)],
                    ),
                    1 => op(
                        ChcOp::Or,
                        &[&self.pick(rng, Kind::Bool), &self.pick(rng, Kind::Bool)],
                    ),
                    2 => op(ChcOp::Not, &[&self.pick(rng, Kind::Bool)]),
                    3 => op(
                        ChcOp::Implies,
                        &[&self.pick(rng, Kind::Bool), &self.pick(rng, Kind::Bool)],
                    ),
                    4 => op(
                        [ChcOp::Le, ChcOp::Lt, ChcOp::Ge, ChcOp::Gt][rng.below(4)],
                        &[&self.pick(rng, num), &self.pick(rng, num)],
                    ),
                    5 => op(
                        [ChcOp::Eq, ChcOp::Ne][rng.below(2)],
                        &[&self.pick(rng, num), &self.pick(rng, num)],
                    ),
                    _ => op(
                        ChcOp::Ite,
                        &[
                            &self.pick(rng, Kind::Bool),
                            &self.pick(rng, Kind::Bool),
                            &self.pick(rng, Kind::Bool),
                        ],
                    ),
                }
            }
            Kind::Int | Kind::Real => match rng.below(5) {
                0 => op(
                    ChcOp::Add,
                    &[
                        &self.pick(rng, kind),
                        &self.pick(rng, kind),
                        &self.pick(rng, kind),
                    ],
                ),
                1 => op(ChcOp::Sub, &[&self.pick(rng, kind), &self.pick(rng, kind)]),
                2 => op(ChcOp::Neg, &[&self.pick(rng, kind)]),
                3 => {
                    let constant = if kind == Kind::Int {
                        Arc::new(ChcExpr::Int(3))
                    } else {
                        Arc::new(ChcExpr::Real(1, 2))
                    };
                    op(ChcOp::Mul, &[&constant, &self.pick(rng, kind)])
                }
                _ => op(
                    ChcOp::Ite,
                    &[
                        &self.pick(rng, Kind::Bool),
                        &self.pick(rng, kind),
                        &self.pick(rng, kind),
                    ],
                ),
            },
        };
        match kind {
            Kind::Bool => self.bools.push(node),
            Kind::Int => self.ints.push(node),
            Kind::Real => self.reals.push(node),
        }
    }
}

fn z3_available() -> bool {
    Command::new("z3")
        .arg("-version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

/// Strip `(assert ` and `)\n` from a one-root printout.
fn assert_body(text: &str) -> &str {
    text.strip_prefix("(assert ")
        .and_then(|rest| rest.strip_suffix(")\n"))
        .unwrap()
}

#[test]
fn dag_printer_matches_tree_printer_under_z3() {
    if !z3_available() {
        eprintln!("skipping INV-12 differential: z3 not on PATH");
        return;
    }
    const EXPRESSIONS: usize = 10_000;
    const BATCH: usize = 500;
    let mut rng = Rng(0x5eed_2026_0922_d1d1);
    let mut checked = 0usize;
    let mut with_lets = 0usize;
    while checked < EXPRESSIONS {
        let mut script = String::new();
        for sort in ["Bool", "Int", "Real"] {
            let prefix = &sort[..1].to_lowercase();
            for i in 0..3 {
                script.push_str(&format!("(declare-const {prefix}{i} {sort})\n"));
            }
        }
        for _ in 0..BATCH {
            let mut pools = Pools::new();
            let steps = 8 + rng.below(56);
            for _ in 0..steps {
                pools.grow(&mut rng);
            }
            // The newest node of a random sort: deep, and usually shared below.
            let kind = [Kind::Bool, Kind::Int, Kind::Real][rng.below(3)];
            let root = Arc::clone(pools.newest(kind));
            let tree = tree_text(&root);
            let dag = dag_text(&root);
            if dag.contains("(let ") {
                with_lets += 1;
            }
            script.push_str(&format!(
                "(push 1)\n(assert (not (= {} {})))\n(check-sat)\n(pop 1)\n",
                assert_body(&tree),
                assert_body(&dag)
            ));
        }
        let mut child = Command::new("z3")
            .args(["-in", "-smt2", "-T:120"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(script.as_bytes())
            .unwrap();
        let output = child.wait_with_output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let verdicts: Vec<&str> = stdout.lines().map(str::trim).collect();
        assert_eq!(verdicts.len(), BATCH, "z3 output: {stdout}");
        for (i, verdict) in verdicts.iter().enumerate() {
            assert_eq!(*verdict, "unsat", "mismatch at batch item {i}: {stdout}");
        }
        checked += BATCH;
    }
    assert!(
        with_lets * 2 > EXPRESSIONS,
        "the generator must exercise sharing: {with_lets} of {EXPRESSIONS} used let"
    );
}
