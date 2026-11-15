//! Regression tests for the constraint a reification `L ==> C` / `L <== C` is
//! stored as.
//!
//! The parser encodes an implication with a big-M term per premise literal.
//! Two defects lived here, both of them "the guard measures a different
//! quantity than the code stores":
//!
//! * the `==>` arms used the reified constraint's *normalized degree* as the
//!   big-M coefficient. That is the textbook encoding only for a non-negative
//!   degree. For a negative degree -- exactly when the reified constraint is
//!   trivially true, so the reification is a tautology -- each pushed term had
//!   a negative coefficient, `normalize()` flipped it to `|degree| * Lj` and
//!   raised the degree to `(k - 1) * |degree|`. With two or more premise
//!   literals a tautology was therefore stored as a real constraint.
//! * `is_overflow_safe_leq` guarded `degree - 1` for the `... <== ... <= ...`
//!   branch, which stores `degree + 1`; at `degree == N::MAX` the guard passed
//!   and the increment wrapped to `N::MIN`, so the forcing reification
//!   normalized into a trivially true row instead of escalating a width tier.
//!
//! Both are checked here against a `BigInt` oracle: for every assignment, the
//! stored constraint must be satisfied exactly when the documented semantics
//! of the reification is.

use std::fs::File;
use std::io::{BufReader, Write};

use ahash::AHashMap;
use malachite_bigint::BigInt;
use veripb_formula::prelude::*;
use veripb_formula::var_name_manager::{VarNameManager, VarNameRecorder};
use veripb_parser::error::ParserError;
use veripb_parser::io::MaybeCompressed;
use veripb_parser::pbp_parser::parser::{ParserArgs, parse_proof};
use veripb_parser::pbp_parser::proof_processor::ProofProcessor;
use veripb_rules::VeriPBRule;

const VARS: usize = 3;

/// A [`ProofProcessor`] that keeps the constraint of every `a` (assertion)
/// rule, which the parser stores verbatim as it parsed it.
#[derive(Default)]
struct Collector {
    var_names: VarNameManager,
    constraints: Vec<PBConstraintEnum>,
}

impl VarNameRecorder for Collector {
    fn add_by_name(&mut self, name: &str) -> VarIdx {
        self.var_names.add_by_name(name)
    }
}

impl ProofProcessor for Collector {
    type Error = ParserError;

    fn process_version(&mut self, _major: i64, _minor: i64) {}

    fn process_var_name(
        &mut self,
        _line: usize,
        name: &str,
        _is_aux_var: bool,
    ) -> Result<usize, Self::Error> {
        Ok(self.var_names.add_by_name(name))
    }

    fn process_rule(&mut self, _line: usize, rule: VeriPBRule) -> Result<(), Self::Error> {
        if let VeriPBRule::AssertionRule(assertion) = rule {
            self.constraints
                .push(assertion.constraint.constraint.clone());
        }
        Ok(())
    }

    fn should_trace(&self, _line: usize) -> bool {
        false
    }

    fn last_returned_constraint_id(&mut self) -> Option<isize> {
        None
    }
}

/// Parse a proof consisting only of `a` rules, returning the stored
/// constraints or the parse error.
fn parse_assertions(assertions: &[String]) -> Result<Vec<PBConstraintEnum>, ParserError> {
    let mut proof = String::from("pseudo-Boolean proof version 3.0\nf 0;\n");
    for assertion in assertions {
        proof.push_str(assertion);
        proof.push('\n');
    }
    proof.push_str("output NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n");

    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let path = dir.path().join("t.pbp");
    let mut file = File::create(&path).expect("failed to create temporary proof");
    file.write_all(proof.as_bytes())
        .expect("failed to write temporary proof");
    file.flush().expect("failed to flush temporary proof");

    let size = std::fs::metadata(&path).unwrap().len();
    // Upstream made `Parser::new`/`parse` private behind `parse_proof`, which is
    // now the only supported entry point; it also takes the file size as an
    // `Option<u64>` and a `MaybeCompressed` reader so a proof can be gzip/xz/zstd
    // compressed. This test writes a PLAIN proof, so it wraps in the `Plain`
    // variant and drives the same code path as before.
    let mut reader = MaybeCompressed::Plain(BufReader::new(
        File::open(&path).expect("failed to reopen temporary proof"),
    ));
    let mut collector = Collector::default();
    parse_proof(
        Some(size),
        &mut reader,
        &mut collector,
        AHashMap::new(),
        ParserArgs {
            show_progress: false,
            trace_enabled: false,
            store_assertion_annotations: false,
        },
    )?;
    Ok(collector.constraints)
}

/// Parse a proof consisting only of `a` rules and return the stored constraints.
fn stored_constraints(assertions: &[String]) -> Vec<PBConstraintEnum> {
    parse_assertions(assertions).expect("the proof must parse")
}

/// The degree of a stored constraint, whatever representation it ended up in.
fn degree_of(constraint: &PBConstraintEnum) -> BigInt {
    match constraint {
        PBConstraintEnum::Clause(c) => (*c.get_degree()).into(),
        PBConstraintEnum::Cardinality(c) => (*c.get_degree()).into(),
        PBConstraintEnum::GeneralPBI64(c) => (*c.get_degree()).into(),
        PBConstraintEnum::GeneralPBI128(c) => (*c.get_degree()).into(),
        PBConstraintEnum::GeneralPBBigInt(c) => c.get_degree().clone(),
    }
}

/// Whether the stored constraint is satisfied by `assignment` (bit `i` is the
/// value of variable `x{i + 1}`).
fn stored_holds(constraint: &PBConstraintEnum, assignment: usize) -> bool {
    let mut sum = BigInt::from(0);
    for index in 0..constraint.len() {
        let term = constraint.get_term(index).unwrap();
        let value = (assignment >> term.get_lit().get_var()) & 1 == 1;
        if value != term.get_lit().is_negated() {
            sum += term.get_coeff();
        }
    }
    sum >= degree_of(constraint)
}

/// A term of the reified constraint, as written in the proof text.
#[derive(Clone, Copy)]
struct Term {
    coeff: i64,
    var: usize,
    negated: bool,
}

/// A premise literal, as written in the proof text.
#[derive(Clone, Copy)]
struct Premise {
    var: usize,
    negated: bool,
}

struct Case {
    premises: &'static [Premise],
    right_implication: bool,
    terms: &'static [Term],
    less_equal: bool,
    degree: i64,
}

impl Case {
    /// The `a` rule that states this reification.
    fn render(&self) -> String {
        let mut out = String::from("a ");
        for premise in self.premises {
            if premise.negated {
                out.push('~');
            }
            out.push_str(&format!("x{} ", premise.var + 1));
        }
        if !self.premises.is_empty() {
            out.push_str(if self.right_implication {
                "==> "
            } else {
                "<== "
            });
        }
        for term in self.terms {
            out.push_str(&format!(
                "{:+} {}x{} ",
                term.coeff,
                if term.negated { "~" } else { "" },
                term.var + 1
            ));
        }
        out.push_str(if self.less_equal { "<= " } else { ">= " });
        out.push_str(&format!("{} ;", self.degree));
        out
    }

    /// The documented meaning of the reification under `assignment`.
    fn semantics(&self, assignment: usize) -> bool {
        let premises_hold = self.premises.iter().all(|premise| {
            let value = (assignment >> premise.var) & 1 == 1;
            value != premise.negated
        });
        let mut sum: i64 = 0;
        for term in self.terms {
            let value = (assignment >> term.var) & 1 == 1;
            if value != term.negated {
                sum += term.coeff;
            }
        }
        let inner = if self.less_equal {
            i128::from(sum) <= i128::from(self.degree)
        } else {
            i128::from(sum) >= i128::from(self.degree)
        };
        if self.premises.is_empty() {
            inner
        } else if self.right_implication {
            !premises_hold || inner
        } else {
            !inner || premises_hold
        }
    }
}

const TERM_SETS: [&[Term]; 3] = [
    &[Term {
        coeff: 1,
        var: 0,
        negated: false,
    }],
    &[
        Term {
            coeff: 2,
            var: 0,
            negated: false,
        },
        Term {
            coeff: -1,
            var: 1,
            negated: true,
        },
    ],
    // A premise literal that shares a variable with the reified constraint:
    // the pushed big-M term then merges during normalization.
    &[Term {
        coeff: 1,
        var: 1,
        negated: false,
    }],
];

const PREMISE_SETS: [&[Premise]; 4] = [
    &[],
    &[Premise {
        var: 1,
        negated: false,
    }],
    &[
        Premise {
            var: 1,
            negated: false,
        },
        Premise {
            var: 2,
            negated: false,
        },
    ],
    &[
        Premise {
            var: 1,
            negated: true,
        },
        Premise {
            var: 2,
            negated: false,
        },
    ],
];

/// Degrees spanning the sign change and both `i64` boundaries, which is where
/// the big-M coefficient and the overflow guards used to disagree.
const DEGREES: [i64; 11] = [
    i64::MIN,
    i64::MIN + 1,
    -3,
    -2,
    -1,
    0,
    1,
    2,
    3,
    i64::MAX - 1,
    i64::MAX,
];

#[test]
fn reification_is_stored_with_its_documented_semantics() {
    let mut cases = Vec::new();
    for premises in PREMISE_SETS {
        for right_implication in [true, false] {
            // `<==` is only *grammatical* after exactly one premise literal
            // (`Parser::literals`, the `count == 1` guard on
            // `Token::LeftImplication`), so the other premise sets have no
            // `<==` spelling to check rather than an unchecked one. That
            // refusal is pinned below by
            // `left_implication_takes_exactly_one_premise_literal`, so this
            // `continue` cannot quietly become a coverage hole if the grammar
            // is widened.
            if !right_implication && premises.len() != 1 {
                continue;
            }
            for terms in TERM_SETS {
                for less_equal in [true, false] {
                    for degree in DEGREES {
                        cases.push(Case {
                            premises,
                            right_implication,
                            terms,
                            less_equal,
                            degree,
                        });
                    }
                }
            }
        }
    }

    let assertions: Vec<String> = cases.iter().map(Case::render).collect();
    let stored = stored_constraints(&assertions);
    assert_eq!(stored.len(), cases.len(), "one constraint per `a` rule");

    for (case, constraint) in cases.iter().zip(stored.iter()) {
        for assignment in 0..(1usize << VARS) {
            assert_eq!(
                stored_holds(constraint, assignment),
                case.semantics(assignment),
                "`{}` under assignment {assignment:03b} (stored degree {})",
                case.render(),
                degree_of(constraint),
            );
        }
    }
}

/// `<==` after two or more premise literals is not a reification the parser
/// stores badly -- it is not a reification the grammar admits at all.
///
/// This is the companion to the `continue` in the case generator above: the
/// oracle test covers `<==` at premise-set size 1 only, and the honest reason
/// is that size 1 is the only size there is. Without this test that looks
/// like an untested arm; with it, the arm is pinned as unreachable, and
/// widening the grammar without widening the oracle turns this red.
#[test]
fn left_implication_takes_exactly_one_premise_literal() {
    for size in [0usize, 2, 3] {
        let premises: Vec<String> = (1..=size).map(|i| format!("x{i} ")).collect();
        let rule = format!("a {}<== 1 x9 >= 1 ;", premises.concat());
        let err = parse_assertions(std::slice::from_ref(&rule))
            .err()
            .unwrap_or_else(|| panic!("`{rule}` parsed, but `<==` takes exactly one premise"));
        let rendered = err.to_string();
        assert!(
            rendered.contains("`<==`"),
            "`{rule}` was rejected, but not for the reason this test is about: {rendered}"
        );
    }

    // The positive control: one premise literal is accepted.
    assert_eq!(
        stored_constraints(&["a x1 <== 1 x9 >= 1 ;".to_string()]).len(),
        1
    );
}

#[test]
fn left_implication_of_a_less_equal_bound_stores_the_incremented_degree() {
    // The direct pin for the `degree - 1` / `degree + 1` mismatch: at
    // `i64::MAX` the stored degree is `2^63`, which no longer fits `i64`, and
    // the escalation ladder has to be entered rather than the increment
    // wrapping to `i64::MIN` (which normalized to the trivially true
    // `2^63 ~x1 >= 0`, forcing nothing).
    let stored = stored_constraints(&[
        "a x1 <== <= 9223372036854775806 ;".to_string(),
        "a x1 <== <= 9223372036854775807 ;".to_string(),
        "a x1 <== <= 9223372036854775808 ;".to_string(),
        "a x1 <== <= 170141183460469231731687303715884105726 ;".to_string(),
        "a x1 <== <= 170141183460469231731687303715884105727 ;".to_string(),
        "a x1 <== <= 170141183460469231731687303715884105728 ;".to_string(),
    ]);

    let expected = [
        "9223372036854775807",
        "9223372036854775808",
        "9223372036854775809",
        "170141183460469231731687303715884105727",
        "170141183460469231731687303715884105728",
        "170141183460469231731687303715884105729",
    ];
    for (constraint, expected) in stored.iter().zip(expected) {
        let expected: BigInt = expected.parse().unwrap();
        assert_eq!(degree_of(constraint), expected);
        assert_eq!(constraint.len(), 1, "the reification must force x1");
        assert_eq!(constraint.get_term(0).unwrap().get_coeff(), &expected);
        assert!(
            !constraint.get_term(0).unwrap().get_lit().is_negated(),
            "a wrapped degree normalized the term onto ~x1 and forced nothing"
        );
    }
}
