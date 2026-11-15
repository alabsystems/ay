// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A datatype sort costs its type text, not its flattened leaf count.
//!
//! The struct DAG of model-checker-consumer's ask
//! (the development design notes):
//!
//! ```text
//! D0 = (_ BitVec 32),  Dk = Dk_mk(Dk_a: D(k-1), Dk_b: D(k-1))
//! ```
//!
//! is `O(k)` lines of SMT-LIB with `2^k` scalar leaves. Through ay's CHC front
//! end, a `ChcVar`'s `Hash` must stay constant and the normalized proof
//! identity must grow by the same bytes per level; parsing all `k` up to 64
//! must return at all, since a walk of the tree expansion would not. (The
//! parser's resolution work is asserted linear by the `resolve_sorts` unit
//! tests, which can count it.)
//!
//! The deterministic test below asserts that. The timing table the ask
//! reported is printed by the measurement harness, which runs only with the
//! `measurement-harness-tests` feature:
//!
//! ```text
//! targo --unverified test -p ay-chc --features measurement-harness-tests \
//!     --test datatype_identity_cost -- --nocapture
//! ```

use ay_chc::{normalized_chc_input, ChcParser, ChcProblem, ChcVar};
use std::hash::{Hash, Hasher};

#[path = "datatype_identity_cost/solving.rs"]
mod solving;

/// The sort every level bottoms out in, any declaration it needs, and the
/// value the query compares the all-`a` leaf with.
#[derive(Clone, Copy)]
struct Leaf {
    prelude: Option<&'static str>,
    sort: &'static str,
    value: &'static str,
}

/// The ask's leaf.
const BITVEC32: Leaf = Leaf {
    prelude: None,
    sort: "(_ BitVec 32)",
    value: "#x00000005",
};

/// A recursive leaf: its finite snapshot keeps a cut placeholder at the
/// bottom of every level above it.
const LIST: Leaf = Leaf {
    prelude: Some("(declare-datatype List ((nil) (cons (head Int) (tail List))))"),
    sort: "List",
    value: "nil",
};

/// `gen_struct_dag.py datatype k`, byte for byte: one `declare-datatype` per
/// level, one `Dk` column passed from `bb0` to `bb1`, and a refutable query on
/// the all-`a` leaf.
fn struct_dag_smt2(k: usize) -> String {
    struct_dag_over(BITVEC32, k)
}

/// [`struct_dag_smt2`] over any leaf.
fn struct_dag_over(leaf: Leaf, k: usize) -> String {
    let mut out = vec!["(set-logic HORN)".to_owned()];
    out.extend(leaf.prelude.map(str::to_owned));
    for level in 1..=k {
        out.push(format!(
            "(declare-datatype D{level} ((D{level}_mk (D{level}_a {inner}) (D{level}_b {inner}))))",
            inner = inner_sort(leaf, level)
        ));
    }
    out.extend(struct_dag_rules(leaf, k));
    out.join("\n") + "\n"
}

/// The same levels in one `declare-datatypes` block, where each level names
/// the one below before it is declared. The parser keeps such forward
/// references as finite snapshots (a placeholder two levels down), so this is
/// a different problem from [`struct_dag_smt2`]; its cost must be linear too.
fn struct_dag_one_block_smt2(k: usize) -> String {
    let names: Vec<String> = (1..=k).map(|level| format!("(D{level} 0)")).collect();
    let bodies: Vec<String> = (1..=k)
        .map(|level| {
            format!(
                "((D{level}_mk (D{level}_a {inner}) (D{level}_b {inner})))",
                inner = inner_sort(BITVEC32, level)
            )
        })
        .collect();
    let mut out = vec![
        "(set-logic HORN)".to_owned(),
        format!(
            "(declare-datatypes ({}) ({}))",
            names.join(" "),
            bodies.join(" ")
        ),
    ];
    out.extend(struct_dag_rules(BITVEC32, k));
    out.join("\n") + "\n"
}

fn inner_sort(leaf: Leaf, level: usize) -> String {
    if level == 1 {
        leaf.sort.to_owned()
    } else {
        format!("D{}", level - 1)
    }
}

fn struct_dag_rules(leaf: Leaf, k: usize) -> Vec<String> {
    let top = format!("D{k}");
    let mut read = "bb1_v0".to_owned();
    for level in (1..=k).rev() {
        read = format!("(D{level}_a {read})");
    }
    vec![
        format!("(declare-var bb0_v0 {top})"),
        format!("(declare-var bb1_v0 {top})"),
        "(declare-rel error ())".to_owned(),
        format!("(declare-rel bb0 ({top}))"),
        format!("(declare-rel bb1 ({top}))"),
        "(rule (=> true (bb0 bb0_v0)))".to_owned(),
        "(rule (=> (bb0 bb0_v0) (bb1 bb0_v0)))".to_owned(),
        format!(
            "(rule (=> (and (bb1 bb1_v0) (= {read} {value})) error))",
            value = leaf.value
        ),
        "(query error)".to_owned(),
    ]
}

fn parse(input: &str) -> ChcProblem {
    ChcParser::parse(input).expect("struct DAG parses")
}

/// A variable of the problem's `Dk` column, as the ask hashed it.
fn column_variable(problem: &ChcProblem) -> ChcVar {
    let predicate = problem
        .get_predicate_by_name("bb0")
        .expect("bb0 is declared");
    ChcVar::new("bb0_v0", predicate.arg_sorts[0].clone())
}

/// Counts the bytes a `Hash` implementation feeds: its hashing work.
#[derive(Default)]
struct CountingHasher(usize);

impl Hasher for CountingHasher {
    fn finish(&self) -> u64 {
        0
    }

    fn write(&mut self, bytes: &[u8]) {
        self.0 += bytes.len();
    }
}

fn hash_work<T: Hash>(value: &T) -> usize {
    let mut hasher = CountingHasher::default();
    value.hash(&mut hasher);
    hasher.0
}

#[test]
fn generator_matches_the_asks_committed_repro() {
    // model-checker-consumer's `struct_dag_datatype_k4.smt2`, as committed beside the ask.
    let expected = "(set-logic HORN)
(declare-datatype D1 ((D1_mk (D1_a (_ BitVec 32)) (D1_b (_ BitVec 32)))))
(declare-datatype D2 ((D2_mk (D2_a D1) (D2_b D1))))
(declare-datatype D3 ((D3_mk (D3_a D2) (D3_b D2))))
(declare-datatype D4 ((D4_mk (D4_a D3) (D4_b D3))))
(declare-var bb0_v0 D4)
(declare-var bb1_v0 D4)
(declare-rel error ())
(declare-rel bb0 (D4))
(declare-rel bb1 (D4))
(rule (=> true (bb0 bb0_v0)))
(rule (=> (bb0 bb0_v0) (bb1 bb0_v0)))
(rule (=> (and (bb1 bb1_v0) (= (D1_a (D2_a (D3_a (D4_a bb1_v0)))) #x00000005)) error))
(query error)
";
    assert_eq!(struct_dag_smt2(4), expected);
}

#[test]
fn struct_dag_parse_hash_and_identity_are_linear_in_k() {
    // From k = 11 on every name a level spells (its own and the two below it,
    // which a forward-reference snapshot names) has the same width, so each
    // level adds the same type text and the identity must grow by the same
    // number of bytes.
    // Under the old spelling it doubled per level (about 147 bytes per leaf
    // per occurrence): its step at k = 64 alone would be ~2^70 bytes.
    const MAX_VARIABLE_HASH_WORK: usize = 96;
    let encodings: [(&str, fn(usize) -> String, fn(usize) -> usize); 3] = [
        // One definition per level.
        ("declare-datatype per level", struct_dag_smt2, |k| k),
        // Plus `List`'s outer and inner snapshot lists.
        (
            "declare-datatype per level over List",
            |k| struct_dag_over(LIST, k),
            |k| k + 2,
        ),
        // Plus each level's forward-reference snapshot of the level below.
        (
            "one declare-datatypes block",
            struct_dag_one_block_smt2,
            |k| 2 * k - 2,
        ),
    ];
    for (encoding, generate, definitions_at) in encodings {
        let mut identity_sizes = Vec::new();
        for k in 1..=64 {
            let problem = parse(&generate(k));
            let identity = normalized_chc_input(&problem);
            identity_sizes.push(identity.len());
            let definitions = identity
                .lines()
                .filter(|line| line.starts_with("constructors @"))
                .count();
            if k >= 2 {
                assert_eq!(definitions, definitions_at(k), "{encoding}, k={k}");
            }

            let variable = column_variable(&problem);
            let work = hash_work(&variable);
            assert!(
                work <= MAX_VARIABLE_HASH_WORK,
                "{encoding}, k={k}: hashing one ChcVar fed {work} bytes"
            );
            // A second, independent parse yields an equal sort and identity.
            let again = parse(&generate(k));
            assert_eq!(variable, column_variable(&again), "{encoding}, k={k}");
            assert_eq!(identity, normalized_chc_input(&again), "{encoding}, k={k}");
        }
        let steps: Vec<usize> = identity_sizes[10..]
            .windows(2)
            .map(|pair| pair[1] - pair[0])
            .collect();
        assert!(
            steps.windows(2).all(|pair| pair[0] == pair[1]),
            "{encoding}: identity steps for k = 11..=64 differ: {steps:?}"
        );
    }
}

/// The ask's table, re-measured: `ChcVar` hash, normalized input size and
/// time, plus the parse and an `Eq` of two independently parsed sorts.
#[cfg(feature = "measurement-harness-tests")]
#[test]
fn measure_struct_dag_identity_cost() {
    use std::collections::hash_map::DefaultHasher;
    use std::time::{Duration, Instant};

    fn median(mut samples: Vec<Duration>) -> Duration {
        samples.sort();
        samples[samples.len() / 2]
    }

    eprintln!(
        "{:>3} {:>22} {:>12} {:>12} {:>14} {:>12} {:>12}",
        "k", "leaves 2^k", "parse", "ChcVar hash", "identity B", "identity", "Eq (2 parses)"
    );
    for k in [4usize, 6, 8, 10, 12, 14, 16, 24, 32, 48, 64] {
        let input = struct_dag_smt2(k);
        let mut parses = Vec::new();
        let mut problem = None;
        for _ in 0..5 {
            let start = Instant::now();
            problem = Some(parse(&input));
            parses.push(start.elapsed());
        }
        let problem = problem.expect("parsed");
        let other = parse(&input);
        let variable = column_variable(&problem);
        let other_variable = column_variable(&other);

        let hashes = (0..101)
            .map(|_| {
                let start = Instant::now();
                let mut hasher = DefaultHasher::new();
                variable.hash(&mut hasher);
                std::hint::black_box(hasher.finish());
                start.elapsed()
            })
            .collect();
        let equalities = (0..101)
            .map(|_| {
                let start = Instant::now();
                std::hint::black_box(variable == other_variable);
                start.elapsed()
            })
            .collect();
        let mut identity_len = 0;
        let identities = (0..5)
            .map(|_| {
                let start = Instant::now();
                identity_len = normalized_chc_input(&problem).len();
                start.elapsed()
            })
            .collect();
        let leaves = if k < 128 {
            (1u128 << k).to_string()
        } else {
            "-".to_owned()
        };
        eprintln!(
            "{k:>3} {leaves:>22} {:>12.1?} {:>12.1?} {identity_len:>14} {:>12.1?} {:>12.1?}",
            median(parses),
            median(hashes),
            median(identities),
            median(equalities)
        );
    }
}
