// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-mode semantic validation for `TheoryLemmaKind::FpClassification` proof
//! steps (#trust-count→0).
//!
//! This is the floating-point analogue of the bounded Bool/BV evaluator in
//! [`super::bv_bitblast`]: a `FpClassification` lemma clause is accepted only
//! when it is TRUE under EVERY assignment of its (small-width) FP variables.
//! The evaluator enumerates all `2^(eb+sb)` bit patterns of each FP-sorted
//! variable, reconstructs each as a concrete IEEE 754 value, evaluates the
//! clause, and requires it true for every assignment. If any assignment
//! falsifies the clause the lemma is rejected — so a non-tautology can never be
//! accepted (no false-UNSAT).
//!
//! ## Why a standalone evaluator
//!
//! `ay-proof` depends only on `ay-core` (which owns `Sort::FloatingPoint`) and
//! `num-bigint`/`num-rational`. The full FP evaluator lives in `ay-fp`, but
//! `ay-fp` pulls the SAT / bit-blast stack, which the proof checker must not
//! depend on. So the ~exact closed-form logic (classification, abs, neg, fp.eq,
//! structural `=`, and the exact-rational comparisons) is re-implemented here
//! over a self-contained `FpVal`, reasoning purely with integer/rational
//! arithmetic. This is exactly the same closed-form semantics proven in
//! `ay-fp`'s `FpModelValue`, but with no native-float dependency, so it is
//! amenable to independent (e.g. Lean) re-verification.
//!
//! ## Scope (fail-closed boundary)
//!
//! Supported FP operations: the classification predicates (`fp.isNaN`,
//! `fp.isInfinite`, `fp.isZero`, `fp.isNormal`, `fp.isSubnormal`,
//! `fp.isPositive`, `fp.isNegative`), the sign/structural unary ops (`fp.abs`,
//! `fp.neg`), equality (`=` structural and `fp.eq` IEEE), and the comparisons
//! (`fp.lt`, `fp.leq`, `fp.gt`, `fp.geq`, evaluated exactly over `BigRational`).
//! Boolean connectives (`not`/`and`/`or`/`xor`/`=>`/`ite`) and FP literals
//! (`+zero`/`-zero`/`+oo`/`-oo`/`NaN`/`(fp s e m)`) are supported as glue.
//!
//! ALL FP ARITHMETIC OPERATIONS (`fp.add`, `fp.sub`, `fp.mul`, `fp.div`,
//! `fp.fma`, `fp.sqrt`, `fp.rem`, `fp.min`, `fp.max`, `fp.roundToIntegral`, the
//! conversions `to_fp`/`fp.to_*`) are intentionally UNSUPPORTED here — they
//! require a correctly-rounded exact-rational arithmetic evaluator that does not
//! yet exist in the checker, and the only existing evaluator (`eval_fp.rs`) is
//! f64-based double-rounding, unsuitable as a proof oracle. There is one
//! width-independent path: the five IEEE exponent/significand classes (NaN,
//! infinity, zero, normal, and subnormal) form an exact disjoint partition, so
//! their pairwise-exclusion clauses are checked symbolically. Any other clause
//! mentioning an unsupported op, or whose enumerated FP width exceeds the bound,
//! fails closed.

use num_bigint::BigInt;
use num_rational::BigRational;

use ay_core::{Constant, FpOp, ProofId, Sort, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

/// Total enumerated FP bits across all distinct FP variables in one clause. A
/// Float16 variable is 16 bits = 65536 patterns; the checker is a validator,
/// not a second bit-blaster, so cap the WHOLE clause's FP-variable bit budget.
/// Float8-class (e.g. (3,5) = 8 bits) and a single Float16 variable both fit.
const MAX_FP_ASSIGNMENT_BITS: u32 = 16;

/// Recognize whether `clause` is a strict-checkable FP classification/sign/
/// structural/comparison lemma — i.e. whether [`validate_fp_classification`]
/// would accept it. The exact inverse of the validator: the proof classifier
/// (`ay-dpll`) calls this to upgrade a `Generic`/trust FP lemma into the
/// strict-checkable `FpClassification` kind ONLY when strict mode will
/// independently re-validate it by either an exact IEEE class-partition rule or
/// exhaustive bounded evaluation — so the classifier and checker cannot drift.
/// A non-tautological clause, an unsupported FP op, or a too-wide clause outside
/// that exact schema is rejected.
#[must_use]
pub fn recognize_fp_classification(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_fp_classification(terms, ProofId(0), clause).is_ok()
}

/// Like [`recognize_fp_classification`], but on acceptance also returns the
/// principal FP operation of the clause (for the `FpClassification { operation }`
/// annotation's rendering / diagnostics). Returns `None` exactly when the
/// validator would reject. The op is purely descriptive — validation re-derives
/// soundness from the clause, never from this op — so any FP op present in an
/// accepted clause is a sound choice; we pick the first in clause order for
/// determinism.
#[must_use]
pub fn recognize_fp_classification_op(terms: &TermStore, clause: &[TermId]) -> Option<FpOp> {
    if !recognize_fp_classification(terms, clause) {
        return None;
    }
    for &lit in clause {
        if let Some(op) = principal_fp_op(terms, lit, &mut Vec::new()) {
            return Some(op);
        }
    }
    // An accepted clause must mention an FP sub-term; if it is purely a
    // structural `=` over FP variables with no named FP op, default to
    // StructuralEq (the principal relation).
    Some(FpOp::StructuralEq)
}

/// Recognize an exact IEEE-754 rounding-mode finite-domain axiom.
///
/// This is the public producer/checker handshake for
/// `TheoryLemmaKind::FpRoundingModeDomain`: producers may promote a derived
/// assertion only when this function accepts it, and strict mode independently
/// calls the same validator again. An accepted clause must contain at least one
/// exact fixed-domain theorem (other literals are ordinary clause weakening):
///
/// * the conjunction of all ten pairwise disequalities among `RNE`, `RNA`,
///   `RTP`, `RTN`, and `RTZ`, or one exact distinct pair produced when that
///   conjunction is flattened at the assertion boundary; or
/// * a five-way disjunction saying one non-literal `RoundingMode` term equals
///   each of those five values exactly once; or
/// * the negation of the complete 15-edge pairwise-distinct conjunction over
///   exactly six `RoundingMode` terms (the five-value pigeonhole theorem).
///
/// Partial domains, extra values, aliases, duplicate cases, and non-RM terms
/// fail closed.
#[must_use]
pub fn recognize_fp_rounding_mode_domain(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_fp_rounding_mode_domain(terms, ProofId(0), clause).is_ok()
}

fn rm_literal_index(terms: &TermStore, term: TermId) -> Option<usize> {
    if !matches!(terms.sort(term), Sort::Uninterpreted(name) if name == "RoundingMode") {
        return None;
    }
    let TermData::App(symbol, args) = terms.get(term) else {
        return None;
    };
    if !args.is_empty() {
        return None;
    }
    match symbol.name() {
        "RNE" => Some(0),
        "RNA" => Some(1),
        "RTP" => Some(2),
        "RTN" => Some(3),
        "RTZ" => Some(4),
        _ => None,
    }
}

fn binary_equality(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    if terms.sort(term) != &Sort::Bool {
        return None;
    }
    let TermData::App(symbol, args) = terms.get(term) else {
        return None;
    };
    (symbol.name() == "=" && args.len() == 2).then(|| (args[0], args[1]))
}

fn is_rm_pairwise_disequality(terms: &TermStore, term: TermId) -> bool {
    let TermData::Not(equality) = terms.get(term) else {
        return false;
    };
    let Some((lhs, rhs)) = binary_equality(terms, *equality) else {
        return false;
    };
    matches!(
        (rm_literal_index(terms, lhs), rm_literal_index(terms, rhs)),
        (Some(i), Some(j)) if i != j
    )
}

fn is_exact_rm_distinctness(terms: &TermStore, term: TermId) -> bool {
    let TermData::App(symbol, conjuncts) = terms.get(term) else {
        return false;
    };
    if symbol.name() != "and" || conjuncts.len() != 10 {
        return false;
    }

    let mut pairs = [[false; 5]; 5];
    for &conjunct in conjuncts {
        let TermData::Not(equality) = terms.get(conjunct) else {
            return false;
        };
        let Some((lhs, rhs)) = binary_equality(terms, *equality) else {
            return false;
        };
        let (Some(mut i), Some(mut j)) =
            (rm_literal_index(terms, lhs), rm_literal_index(terms, rhs))
        else {
            return false;
        };
        if i == j {
            return false;
        }
        if i > j {
            std::mem::swap(&mut i, &mut j);
        }
        if std::mem::replace(&mut pairs[i][j], true) {
            return false;
        }
    }

    (0..5).all(|i| ((i + 1)..5).all(|j| pairs[i][j]))
}

fn is_exact_rm_coverage(terms: &TermStore, term: TermId) -> bool {
    let TermData::App(symbol, disjuncts) = terms.get(term) else {
        return false;
    };
    if symbol.name() != "or" || disjuncts.len() != 5 {
        return false;
    }

    let mut covered = [false; 5];
    let mut subject = None;
    for &disjunct in disjuncts {
        let Some((lhs, rhs)) = binary_equality(terms, disjunct) else {
            return false;
        };
        let (mode, candidate) = match (rm_literal_index(terms, lhs), rm_literal_index(terms, rhs)) {
            (Some(mode), None) => (mode, rhs),
            (None, Some(mode)) => (mode, lhs),
            _ => return false,
        };
        if !matches!(terms.sort(candidate), Sort::Uninterpreted(name) if name == "RoundingMode")
            || std::mem::replace(&mut covered[mode], true)
        {
            return false;
        }
        match subject {
            Some(existing) if existing != candidate => return false,
            None => subject = Some(candidate),
            _ => {}
        }
    }

    subject.is_some() && covered.into_iter().all(std::convert::identity)
}

fn is_exact_rm_six_term_pigeonhole(terms: &TermStore, term: TermId) -> bool {
    let TermData::Not(distinct) = terms.get(term) else {
        return false;
    };
    let TermData::App(symbol, conjuncts) = terms.get(*distinct) else {
        return false;
    };
    if terms.sort(*distinct) != &Sort::Bool || symbol.name() != "and" || conjuncts.len() != 15 {
        return false;
    }

    let mut subjects = Vec::with_capacity(6);
    let mut pairs = Vec::with_capacity(15);
    for &conjunct in conjuncts {
        let TermData::Not(equality) = terms.get(conjunct) else {
            return false;
        };
        let Some((mut lhs, mut rhs)) = binary_equality(terms, *equality) else {
            return false;
        };
        if lhs == rhs
            || !matches!(terms.sort(lhs), Sort::Uninterpreted(name) if name == "RoundingMode")
            || !matches!(terms.sort(rhs), Sort::Uninterpreted(name) if name == "RoundingMode")
        {
            return false;
        }
        if lhs.0 > rhs.0 {
            std::mem::swap(&mut lhs, &mut rhs);
        }
        if pairs.contains(&(lhs, rhs)) {
            return false;
        }
        pairs.push((lhs, rhs));
        if !subjects.contains(&lhs) {
            subjects.push(lhs);
        }
        if !subjects.contains(&rhs) {
            subjects.push(rhs);
        }
    }
    if subjects.len() != 6 {
        return false;
    }

    for (index, &lhs) in subjects.iter().enumerate() {
        for &rhs in &subjects[index + 1..] {
            let pair = if lhs.0 < rhs.0 {
                (lhs, rhs)
            } else {
                (rhs, lhs)
            };
            if !pairs.contains(&pair) {
                return false;
            }
        }
    }
    true
}

/// Strictly validate the complete fixed-domain schema for SMT-LIB
/// `RoundingMode`.
pub(crate) fn validate_fp_rounding_mode_domain(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.is_empty() || clause.iter().any(|term| terms.sort(*term) != &Sort::Bool) {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "fp_rm_domain must be a non-empty Boolean clause".to_string(),
        });
    }
    if clause.iter().any(|&literal| {
        is_rm_pairwise_disequality(terms, literal)
            || is_exact_rm_distinctness(terms, literal)
            || is_exact_rm_coverage(terms, literal)
            || is_exact_rm_six_term_pigeonhole(terms, literal)
    }) {
        Ok(())
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "fp_rm_domain contains no exact canonical-mode disequality, complete five-value distinctness/coverage schema, or complete six-term pigeonhole theorem".to_string(),
        })
    }
}

/// One member of the exact IEEE exponent/significand partition.
///
/// These predicates depend only on whether the exponent is zero/all-ones and
/// whether the trailing significand is zero. Consequently, exactly one member
/// holds for every well-sorted floating-point value, independently of its
/// width, sign, or how the value was computed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FpValueClass {
    Nan,
    Infinite,
    Zero,
    Normal,
    Subnormal,
}

/// Recognize a positive application of one exact IEEE value-class predicate.
///
/// The argument itself may be an arbitrary FP expression. The partition law is
/// about its resulting IEEE bit pattern, so no evaluation of that expression is
/// needed. Requiring the exact unary Bool-over-FP shape prevents a user symbol
/// with the same text but a different signature from becoming proof authority.
fn fp_value_class_atom(terms: &TermStore, term: TermId) -> Option<(TermId, FpValueClass)> {
    if terms.sort(term) != &Sort::Bool {
        return None;
    }
    let TermData::App(symbol, args) = terms.get(term) else {
        return None;
    };
    let [argument] = args.as_slice() else {
        return None;
    };
    if !matches!(terms.sort(*argument), Sort::FloatingPoint(_, _)) {
        return None;
    }
    let Symbol::Named(operator) = symbol else {
        return None;
    };
    let class = match operator.as_str() {
        "fp.isNaN" => FpValueClass::Nan,
        "fp.isInfinite" => FpValueClass::Infinite,
        "fp.isZero" => FpValueClass::Zero,
        "fp.isNormal" => FpValueClass::Normal,
        "fp.isSubnormal" => FpValueClass::Subnormal,
        _ => return None,
    };
    Some((*argument, class))
}

/// Collect class atoms that must be true when `term` is true.
///
/// Only conjunction is decomposed: truth of `and` entails truth of each child.
/// Ignoring every other shape is fail-closed. The recursion limit mirrors the
/// bounded evaluator and prevents an adversarial proof from exhausting the
/// checker stack.
fn collect_required_fp_value_classes(
    terms: &TermStore,
    term: TermId,
    required: &mut Vec<(TermId, FpValueClass)>,
    depth: usize,
) {
    if depth > 512 {
        return;
    }
    if let Some(atom) = fp_value_class_atom(terms, term) {
        required.push(atom);
        return;
    }
    if let TermData::App(Symbol::Named(operator), args) = terms.get(term) {
        if operator == "and" && terms.sort(term) == &Sort::Bool {
            for &argument in args {
                collect_required_fp_value_classes(terms, argument, required, depth + 1);
            }
        }
    }
}

/// Check a width-independent IEEE class-partition tautology.
///
/// A clause is false only when every negated literal's inner proposition is
/// true. For `not P` and `not Q` (including atoms nested beneath a true `and`),
/// that would require both class predicates to hold. Distinct members of the
/// exact five-way partition cannot hold on the same FP value, so finding such a
/// pair independently proves the whole clause, even if it contains weakening
/// literals that this rule does not inspect.
fn is_exact_fp_value_class_exclusion(terms: &TermStore, clause: &[TermId]) -> bool {
    let mut required = Vec::new();
    for &literal in clause {
        if let TermData::Not(inner) = terms.get(literal) {
            collect_required_fp_value_classes(terms, *inner, &mut required, 0);
        }
    }
    required.iter().enumerate().any(|(index, &(term, class))| {
        required[index + 1..]
            .iter()
            .any(|&(other_term, other_class)| term == other_term && class != other_class)
    })
}

/// Validate an `FpClassification` lemma in strict mode by an exact symbolic
/// IEEE partition rule or exhaustive bounded evaluation over its FP variables.
///
/// Every literal must be `Bool`-sorted (a classification/comparison/equality
/// clause is propositional). The clause must mention at least one FP-sorted
/// sub-term (otherwise it is not an FP lemma — route it elsewhere). Outside the
/// width-independent class-exclusion schema, all FP variables must be enumerable
/// within the bit budget, and every assignment of those variables must satisfy
/// the clause.
pub(crate) fn validate_fp_classification(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "fp_classification clause must be non-empty".to_string(),
        });
    }
    for &lit in clause {
        if !matches!(terms.sort(lit), Sort::Bool) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "fp_classification literal has non-Bool sort {:?}; the clause \
                     must be propositional",
                    terms.sort(lit)
                ),
            });
        }
    }

    // The five core IEEE classes are defined by the mutually exclusive
    // exponent/significand cases (zero/nonzero exponent, all-ones exponent,
    // zero/nonzero trailing significand). This proof is width-parametric and
    // does not depend on the bit-blaster that produced the UNSAT candidate.
    if is_exact_fp_value_class_exclusion(terms, clause) {
        return Ok(());
    }

    // Collect the FP-sorted variables, fail closed on any unsupported op/term.
    let mut vars: Vec<FpVar> = Vec::new();
    let mut mentions_fp = false;
    for &lit in clause {
        collect_fp_vars(terms, lit, &mut vars, &mut mentions_fp, &mut Vec::new()).ok_or_else(
            || ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "fp_classification clause contains an unsupported or \
                         too-wide FP/Bool term; strict mode only accepts lemmas \
                         it can exhaustively evaluate (no FP arithmetic ops)"
                    .to_string(),
            },
        )?;
    }
    if !mentions_fp {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "fp_classification clause mentions no floating-point sub-term".to_string(),
        });
    }

    let total_bits: u32 = vars.iter().map(|v| v.eb + v.sb).sum();
    if total_bits > MAX_FP_ASSIGNMENT_BITS {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "fp_classification clause needs {total_bits} FP-variable bits, \
                 above strict bounded checker limit {MAX_FP_ASSIGNMENT_BITS}"
            ),
        });
    }

    let assignment_count: u64 = 1u64 << total_bits;
    for assignment in 0..assignment_count {
        let env = build_env(&vars, assignment);
        let mut clause_true = false;
        for &lit in clause {
            let Some(value) = eval_bool(terms, lit, &env) else {
                return Err(ProofCheckError::InvalidTheoryLemma {
                    step: step_id,
                    reason: "fp_classification clause contains a literal the strict \
                             bounded checker cannot evaluate"
                        .to_string(),
                });
            };
            if value {
                clause_true = true;
                break;
            }
        }
        if !clause_true {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "fp_classification clause is falsified by a bounded FP \
                         assignment (not a tautology)"
                    .to_string(),
            });
        }
    }

    Ok(())
}

/// Map a named FP operation symbol to its [`FpOp`]. Only the ops this checker
/// supports map to `Some`; everything else (including all FP arithmetic) is
/// `None`.
fn fp_op_of_name(name: &str) -> Option<FpOp> {
    Some(match name {
        "fp.abs" => FpOp::Abs,
        "fp.neg" => FpOp::Neg,
        "fp.isNaN" => FpOp::IsNaN,
        "fp.isInfinite" => FpOp::IsInfinite,
        "fp.isZero" => FpOp::IsZero,
        "fp.isNormal" => FpOp::IsNormal,
        "fp.isSubnormal" => FpOp::IsSubnormal,
        "fp.isPositive" => FpOp::IsPositive,
        "fp.isNegative" => FpOp::IsNegative,
        "fp.eq" => FpOp::Eq,
        "fp.lt" => FpOp::Lt,
        "fp.leq" => FpOp::Le,
        "fp.gt" => FpOp::Gt,
        "fp.geq" => FpOp::Ge,
        _ => return None,
    })
}

/// First named FP operation found (pre-order) in `term`, for the descriptive
/// `FpClassification { operation }` annotation. Best-effort; soundness does not
/// depend on it.
fn principal_fp_op(terms: &TermStore, term: TermId, stack: &mut Vec<TermId>) -> Option<FpOp> {
    if stack.len() > 512 {
        return None;
    }
    stack.push(term);
    let result = match terms.get(term) {
        TermData::App(sym, args) => {
            let here = fp_op_of_name(sym.name());
            if here.is_some() {
                here
            } else {
                let mut found = None;
                for &a in args {
                    if let Some(op) = principal_fp_op(terms, a, stack) {
                        found = Some(op);
                        break;
                    }
                }
                found
            }
        }
        TermData::Not(inner) => principal_fp_op(terms, *inner, stack),
        TermData::Ite(c, t, e) => principal_fp_op(terms, *c, stack)
            .or_else(|| principal_fp_op(terms, *t, stack))
            .or_else(|| principal_fp_op(terms, *e, stack)),
        _ => None,
    };
    stack.pop();
    result
}

// ===========================================================================
// Self-contained exact FP value (mirrors ay-fp's FpModelValue exact arms).
// ===========================================================================

/// A concrete IEEE 754 value reconstructed from a raw `eb+sb`-bit pattern.
/// Stored as the decoded fields; classification/sign/equality/comparison are
/// pure integer/rational logic over these fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FpVal {
    /// True if the sign bit is set (negative).
    sign: bool,
    /// Raw biased exponent field (eb bits).
    exponent: u64,
    /// Raw stored significand field (sb-1 bits, no hidden bit).
    significand: u64,
    /// Exponent bit width.
    eb: u32,
    /// Significand bit width (including the hidden bit).
    sb: u32,
}

impl FpVal {
    /// Decode a raw IEEE 754 bit pattern (`eb+sb` bits, MSB sign) into fields.
    fn from_bits(bits: u64, eb: u32, sb: u32) -> Self {
        let stored_bits = sb - 1;
        let sig_mask = if stored_bits >= 64 {
            u64::MAX
        } else {
            (1u64 << stored_bits) - 1
        };
        let exp_mask = if eb >= 64 { u64::MAX } else { (1u64 << eb) - 1 };
        let significand = bits & sig_mask;
        let exponent = (bits >> stored_bits) & exp_mask;
        let sign = ((bits >> (eb + stored_bits)) & 1) == 1;
        Self {
            sign,
            exponent,
            significand,
            eb,
            sb,
        }
    }

    fn max_exp(&self) -> u64 {
        if self.eb >= 64 {
            u64::MAX
        } else {
            (1u64 << self.eb) - 1
        }
    }

    fn is_nan(&self) -> bool {
        self.exponent == self.max_exp() && self.significand != 0
    }

    fn is_infinite(&self) -> bool {
        self.exponent == self.max_exp() && self.significand == 0
    }

    fn is_zero(&self) -> bool {
        self.exponent == 0 && self.significand == 0
    }

    fn is_normal(&self) -> bool {
        self.exponent != 0 && self.exponent != self.max_exp()
    }

    fn is_subnormal(&self) -> bool {
        self.exponent == 0 && self.significand != 0
    }

    fn is_positive(&self) -> bool {
        // +0 is positive; -0, NaN, and any negative value are not. With +0
        // having sign=0 and -0 having sign=1, this is exactly `!sign` once NaN
        // is excluded.
        if self.is_nan() {
            return false;
        }
        !self.sign
    }

    fn is_negative(&self) -> bool {
        // -0 is negative; +0, NaN, and any positive are not.
        if self.is_nan() {
            return false;
        }
        self.sign
    }

    /// `fp.abs`: clear the sign bit (NaN stays NaN, sign cleared).
    fn abs(&self) -> Self {
        Self {
            sign: false,
            ..*self
        }
    }

    /// `fp.neg`: flip the sign bit (including NaN — bit-level negate).
    fn neg(&self) -> Self {
        Self {
            sign: !self.sign,
            ..*self
        }
    }

    /// SMT-LIB structural equality (`=` on FP sort): the abstract FP value
    /// identity. There is a SINGLE NaN value (so NaN = NaN), and +0 and -0 are
    /// DISTINCT (different bit patterns). For finite/inf non-NaN values, equal
    /// iff their raw fields match.
    fn structural_eq(&self, other: &Self) -> bool {
        if self.eb != other.eb || self.sb != other.sb {
            return false;
        }
        if self.is_nan() || other.is_nan() {
            // Single abstract NaN value: NaN = NaN, NaN != non-NaN.
            return self.is_nan() && other.is_nan();
        }
        self.sign == other.sign
            && self.exponent == other.exponent
            && self.significand == other.significand
    }

    /// IEEE 754 equality (`fp.eq`): NaN != anything (incl NaN), +0 == -0,
    /// otherwise equal real value.
    fn fp_eq(&self, other: &Self) -> bool {
        if self.is_nan() || other.is_nan() {
            return false;
        }
        if self.is_zero() && other.is_zero() {
            return true;
        }
        if self.is_infinite() && other.is_infinite() {
            return self.sign == other.sign;
        }
        if self.is_infinite() || other.is_infinite() {
            return false;
        }
        // Both finite non-zero: compare exact rational value.
        match (self.to_rational(), other.to_rational()) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    }

    /// Exact rational value of a FINITE number. `None` for NaN/inf.
    fn to_rational(self) -> Option<BigRational> {
        if self.is_nan() || self.is_infinite() {
            return None;
        }
        if self.is_zero() {
            return Some(BigRational::from_integer(BigInt::from(0)));
        }
        let bias = (1u64 << (self.eb - 1)) - 1;
        let stored_bits = self.sb - 1;
        let sig_int = if self.exponent == 0 {
            BigInt::from(self.significand)
        } else {
            (BigInt::from(1u64) << stored_bits as usize) + BigInt::from(self.significand)
        };
        let exp_shift: i64 = if self.exponent == 0 {
            1i64 - bias as i64 - i64::from(stored_bits)
        } else {
            self.exponent as i64 - bias as i64 - i64::from(stored_bits)
        };
        let result = if exp_shift >= 0 {
            BigRational::from_integer(sig_int << (exp_shift as u64))
        } else {
            BigRational::new(sig_int, BigInt::from(1u64) << ((-exp_shift) as u64))
        };
        Some(if self.sign { -result } else { result })
    }

    /// Total IEEE-754 order helper for `fp.lt`/`leq`/`gt`/`geq`. Returns the
    /// comparison of the real values, with infinities handled exactly. NaN
    /// operands are handled by the caller (all FP comparisons are false on NaN).
    /// Returns `None` only if a NaN slips in (caller guards).
    fn cmp_real(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering;
        if self.is_nan() || other.is_nan() {
            return None;
        }
        // Map each value to an extended-real category for total ordering.
        // -inf < finite < +inf; +0 == -0.
        let rank = |v: &Self| -> (i8, Option<BigRational>) {
            if v.is_infinite() {
                if v.sign {
                    (-1, None) // -inf
                } else {
                    (1, None) // +inf
                }
            } else {
                (0, v.to_rational())
            }
        };
        let (ra, qa) = rank(self);
        let (rb, qb) = rank(other);
        match ra.cmp(&rb) {
            Ordering::Equal => match (qa, qb) {
                (Some(a), Some(b)) => Some(a.cmp(&b)),
                // both infinities of the same sign
                (None, None) => Some(Ordering::Equal),
                _ => None,
            },
            other => Some(other),
        }
    }
}

// ===========================================================================
// Variable collection + environment.
// ===========================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FpVar {
    term: TermId,
    eb: u32,
    sb: u32,
}

/// Operations the evaluator supports. Anything not listed here makes
/// `collect_fp_vars`/`eval_*` fail closed.
fn fp_op_arity(name: &str) -> Option<usize> {
    match name {
        "fp.abs" | "fp.neg" | "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal"
        | "fp.isSubnormal" | "fp.isPositive" | "fp.isNegative" => Some(1),
        "fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq" => Some(2),
        _ => None,
    }
}

/// Whether `symbol` applied to zero arguments at `term` is an FP nullary
/// special literal `(_ +zero eb sb)` / `(_ NaN eb sb)` / …
///
/// The INDEXED form is required, and its indices must be exactly the recorded
/// `Sort::FloatingPoint(eb, sb)`. This is a re-derivation, not a spelling test:
/// `ay-frontend` classifies these five names `IndexedOnly`, meaning the bare
/// `Symbol::Named("NaN")` spelling stays an ordinary user-declarable identity —
/// so matching on the name alone would hand IEEE semantics to whatever a
/// problem happens to have declared. (The live frontend mints declared nullary
/// symbols as `TermData::Var`, and `bundle::validate_named_app_signature`
/// rejects a bare-named FP literal outright, but neither of those is a fact
/// this validator can see; requiring the indexed form makes the check local.)
fn is_fp_literal_symbol(terms: &TermStore, term: TermId, symbol: &Symbol, args: &[TermId]) -> bool {
    let Symbol::Indexed(name, indices) = symbol else {
        return false;
    };
    if !args.is_empty() || !matches!(name.as_str(), "+zero" | "-zero" | "+oo" | "-oo" | "NaN") {
        return false;
    }
    matches!(terms.sort(term), Sort::FloatingPoint(eb, sb) if indices.as_slice() == [*eb, *sb])
}

/// Walk `term`, collecting FP-sorted variables (dedup) and flagging whether any
/// FP-sorted sub-term appears. Returns `None` (fail closed) on any unsupported
/// FP op, FP arithmetic op, or unrecognized term shape.
fn collect_fp_vars(
    terms: &TermStore,
    term: TermId,
    vars: &mut Vec<FpVar>,
    mentions_fp: &mut bool,
    stack: &mut Vec<TermId>,
) -> Option<()> {
    if stack.len() > 512 {
        return None;
    }
    stack.push(term);
    if let Sort::FloatingPoint(_, _) = terms.sort(term) {
        *mentions_fp = true;
    }
    let result = match terms.get(term) {
        TermData::Const(Constant::Bool(_)) => Some(()),
        // FP-sorted variable: record it for enumeration.
        TermData::Var(_, _) => match terms.sort(term) {
            Sort::FloatingPoint(eb, sb) => {
                if !vars.iter().any(|v| v.term == term) {
                    vars.push(FpVar {
                        term,
                        eb: *eb,
                        sb: *sb,
                    });
                }
                Some(())
            }
            Sort::Bool => Some(()),
            _ => None,
        },
        TermData::Not(inner) => {
            let inner = *inner;
            collect_fp_vars(terms, inner, vars, mentions_fp, stack)
        }
        TermData::Ite(c, t, e) => {
            let (c, t, e) = (*c, *t, *e);
            collect_fp_vars(terms, c, vars, mentions_fp, stack)?;
            collect_fp_vars(terms, t, vars, mentions_fp, stack)?;
            collect_fp_vars(terms, e, vars, mentions_fp, stack)
        }
        TermData::App(sym, args) => {
            let name = sym.name();
            // FP nullary literal `(_ +zero eb sb)` etc. Decided before the
            // argument clone so the `Symbol` itself never has to be cloned.
            let is_fp_literal = is_fp_literal_symbol(terms, term, sym, args);
            let args = args.clone();
            if is_fp_literal {
                Some(())
            } else if name == "fp" && args.len() == 3 {
                // `(fp signBv expBv sigBv)` — concrete literal; the BV args are
                // constants, not enumerable variables. Recurse only to confirm
                // they are constants (fail closed otherwise).
                for a in &args {
                    if !matches!(terms.get(*a), TermData::Const(Constant::BitVec { .. })) {
                        // A non-constant `fp` argument would make this a derived
                        // value, not a literal — out of scope.
                        stack.pop();
                        return None;
                    }
                }
                Some(())
            } else if let Some(arity) = fp_op_arity(name) {
                if args.len() != arity {
                    None
                } else {
                    let mut ok = Some(());
                    for a in &args {
                        if collect_fp_vars(terms, *a, vars, mentions_fp, stack).is_none() {
                            ok = None;
                            break;
                        }
                    }
                    ok
                }
            } else if matches!(name, "=" | "and" | "or" | "xor" | "=>") {
                // Boolean/structural-eq connective. For `=`, operands may be FP
                // (structural FP equality) or Bool; either is fine — recurse.
                let mut ok = Some(());
                for a in &args {
                    if collect_fp_vars(terms, *a, vars, mentions_fp, stack).is_none() {
                        ok = None;
                        break;
                    }
                }
                ok
            } else {
                // Unknown op — includes ALL FP arithmetic ops, conversions,
                // rounding modes, etc. Fail closed.
                None
            }
        }
        _ => None,
    };
    stack.pop();
    result
}

/// Per-variable concrete assignment for one enumeration step.
struct Env {
    /// (term, value) bindings for FP variables.
    fp: Vec<(TermId, FpVal)>,
}

fn build_env(vars: &[FpVar], assignment: u64) -> Env {
    let mut fp = Vec::with_capacity(vars.len());
    let mut shift = 0u32;
    for v in vars {
        let width = v.eb + v.sb;
        let mask = if width >= 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        let bits = (assignment >> shift) & mask;
        fp.push((v.term, FpVal::from_bits(bits, v.eb, v.sb)));
        shift += width;
    }
    Env { fp }
}

// ===========================================================================
// Evaluation.
// ===========================================================================

/// Evaluate a Bool-sorted term under `env`. Returns `None` if a sub-term is
/// not evaluable (fail closed — never guesses).
fn eval_bool(terms: &TermStore, term: TermId, env: &Env) -> Option<bool> {
    match terms.get(term) {
        TermData::Const(Constant::Bool(b)) => Some(*b),
        TermData::Var(_, _) => None, // Bool variables: out of scope for FP lemmas.
        TermData::Not(inner) => Some(!eval_bool(terms, *inner, env)?),
        TermData::Ite(c, t, e) => {
            if eval_bool(terms, *c, env)? {
                eval_bool(terms, *t, env)
            } else {
                eval_bool(terms, *e, env)
            }
        }
        TermData::App(sym, args) => {
            let name = sym.name();
            match name {
                // FP classification predicates.
                "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal" | "fp.isSubnormal"
                | "fp.isPositive" | "fp.isNegative"
                    if args.len() == 1 =>
                {
                    let v = eval_fp(terms, args[0], env)?;
                    Some(match name {
                        "fp.isNaN" => v.is_nan(),
                        "fp.isInfinite" => v.is_infinite(),
                        "fp.isZero" => v.is_zero(),
                        "fp.isNormal" => v.is_normal(),
                        "fp.isSubnormal" => v.is_subnormal(),
                        "fp.isPositive" => v.is_positive(),
                        "fp.isNegative" => v.is_negative(),
                        _ => unreachable!(),
                    })
                }
                // IEEE equality and comparisons.
                "fp.eq" if args.len() == 2 => {
                    let a = eval_fp(terms, args[0], env)?;
                    let b = eval_fp(terms, args[1], env)?;
                    Some(a.fp_eq(&b))
                }
                "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq" if args.len() == 2 => {
                    let a = eval_fp(terms, args[0], env)?;
                    let b = eval_fp(terms, args[1], env)?;
                    // NaN ⇒ all comparisons false.
                    let Some(ord) = a.cmp_real(&b) else {
                        return Some(false);
                    };
                    use std::cmp::Ordering;
                    Some(match name {
                        "fp.lt" => ord == Ordering::Less,
                        "fp.leq" => ord != Ordering::Greater,
                        "fp.gt" => ord == Ordering::Greater,
                        "fp.geq" => ord != Ordering::Less,
                        _ => unreachable!(),
                    })
                }
                // Structural `=`: dispatch on operand sort.
                "=" if args.len() == 2 => match terms.sort(args[0]) {
                    Sort::FloatingPoint(_, _) => {
                        let a = eval_fp(terms, args[0], env)?;
                        let b = eval_fp(terms, args[1], env)?;
                        Some(a.structural_eq(&b))
                    }
                    Sort::Bool => {
                        let a = eval_bool(terms, args[0], env)?;
                        let b = eval_bool(terms, args[1], env)?;
                        Some(a == b)
                    }
                    _ => None,
                },
                "and" => {
                    let mut acc = true;
                    for &a in args {
                        acc &= eval_bool(terms, a, env)?;
                    }
                    Some(acc)
                }
                "or" => {
                    let mut acc = false;
                    for &a in args {
                        acc |= eval_bool(terms, a, env)?;
                    }
                    Some(acc)
                }
                "xor" => {
                    let mut acc = false;
                    for &a in args {
                        acc ^= eval_bool(terms, a, env)?;
                    }
                    Some(acc)
                }
                "=>" if args.len() == 2 => {
                    let a = eval_bool(terms, args[0], env)?;
                    let b = eval_bool(terms, args[1], env)?;
                    Some(!a || b)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Evaluate an FP-sorted term under `env`. Returns `None` if not evaluable.
fn eval_fp(terms: &TermStore, term: TermId, env: &Env) -> Option<FpVal> {
    match terms.get(term) {
        TermData::Var(_, _) => env.fp.iter().find(|(t, _)| *t == term).map(|(_, v)| *v),
        TermData::Ite(c, t, e) => {
            if eval_bool(terms, *c, env)? {
                eval_fp(terms, *t, env)
            } else {
                eval_fp(terms, *e, env)
            }
        }
        TermData::App(sym, args) => {
            let name = sym.name();
            match name {
                "fp.abs" if args.len() == 1 => Some(eval_fp(terms, args[0], env)?.abs()),
                "fp.neg" if args.len() == 1 => Some(eval_fp(terms, args[0], env)?.neg()),
                // FP nullary literals `(_ +zero eb sb)` etc. The INDEXED form
                // only — see `is_fp_literal_symbol`.
                "+zero" | "-zero" | "+oo" | "-oo" | "NaN"
                    if is_fp_literal_symbol(terms, term, sym, args) =>
                {
                    let (eb, sb) = fp_sort_of(terms, term)?;
                    Some(literal_fpval(name, eb, sb))
                }
                // `(fp signBv expBv sigBv)` literal.
                "fp" if args.len() == 3 => fp_from_triple(terms, args[0], args[1], args[2]),
                _ => None,
            }
        }
        _ => None,
    }
}

fn fp_sort_of(terms: &TermStore, term: TermId) -> Option<(u32, u32)> {
    match terms.sort(term) {
        Sort::FloatingPoint(eb, sb) => Some((*eb, *sb)),
        _ => None,
    }
}

/// Build the concrete value for an FP special-constant literal.
fn literal_fpval(name: &str, eb: u32, sb: u32) -> FpVal {
    let stored_bits = sb - 1;
    let max_exp = if eb >= 64 { u64::MAX } else { (1u64 << eb) - 1 };
    match name {
        "+zero" => FpVal {
            sign: false,
            exponent: 0,
            significand: 0,
            eb,
            sb,
        },
        "-zero" => FpVal {
            sign: true,
            exponent: 0,
            significand: 0,
            eb,
            sb,
        },
        "+oo" => FpVal {
            sign: false,
            exponent: max_exp,
            significand: 0,
            eb,
            sb,
        },
        "-oo" => FpVal {
            sign: true,
            exponent: max_exp,
            significand: 0,
            eb,
            sb,
        },
        // Canonical quiet NaN: exponent all-ones, MSB of stored significand set.
        "NaN" => FpVal {
            sign: false,
            exponent: max_exp,
            significand: if stored_bits == 0 {
                0
            } else {
                1u64 << (stored_bits - 1)
            },
            eb,
            sb,
        },
        _ => unreachable!("literal_fpval called with non-literal {name}"),
    }
}

/// Decode a `(fp signBv expBv sigBv)` literal from its constant BV arguments.
fn fp_from_triple(terms: &TermStore, s: TermId, e: TermId, m: TermId) -> Option<FpVal> {
    let (sign_val, sign_w) = bv_const(terms, s)?;
    let (exp_val, exp_w) = bv_const(terms, e)?;
    let (sig_val, sig_w) = bv_const(terms, m)?;
    if sign_w != 1 {
        return None;
    }
    let eb = exp_w;
    let sb = sig_w + 1; // stored significand is sb-1 bits.
    let sign = sign_val == 1;
    Some(FpVal {
        sign,
        exponent: exp_val,
        significand: sig_val,
        eb,
        sb,
    })
}

/// Extract a small (≤64-bit) bitvector constant's value and width.
fn bv_const(terms: &TermStore, term: TermId) -> Option<(u64, u32)> {
    match terms.get(term) {
        TermData::Const(Constant::BitVec { value, width }) => {
            use num_traits::ToPrimitive;
            let v = value.to_u64()?;
            Some((v, *width))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build `(_ FloatingPoint eb sb)` variable.
    fn fp_var(terms: &mut TermStore, name: &str, eb: u32, sb: u32) -> TermId {
        terms.mk_var(name, Sort::FloatingPoint(eb, sb))
    }
    fn app1(terms: &mut TermStore, op: &str, a: TermId, sort: Sort) -> TermId {
        terms.mk_app(Symbol::named(op), vec![a], sort)
    }
    fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
        terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool)
    }

    #[test]
    fn accepts_abs_idempotence_float8() {
        // (= (fp.abs (fp.abs x)) (fp.abs x)) over (3,5) = 8 enumerated bits.
        let mut t = TermStore::new();
        let x = fp_var(&mut t, "x", 3, 5);
        let fp = Sort::FloatingPoint(3, 5);
        let abs_x = app1(&mut t, "fp.abs", x, fp.clone());
        let abs_abs_x = app1(&mut t, "fp.abs", abs_x, fp.clone());
        let lemma = eq(&mut t, abs_abs_x, abs_x);
        assert!(
            validate_fp_classification(&t, ProofId(0), &[lemma]).is_ok(),
            "abs idempotence must validate"
        );
        assert_eq!(
            recognize_fp_classification_op(&t, &[lemma]),
            Some(FpOp::Abs)
        );
    }

    #[test]
    fn accepts_neg_involution_float8() {
        // (= (fp.neg (fp.neg x)) x)
        let mut t = TermStore::new();
        let x = fp_var(&mut t, "x", 3, 5);
        let fp = Sort::FloatingPoint(3, 5);
        let neg_x = app1(&mut t, "fp.neg", x, fp.clone());
        let neg_neg_x = app1(&mut t, "fp.neg", neg_x, fp.clone());
        let lemma = eq(&mut t, neg_neg_x, x);
        assert!(validate_fp_classification(&t, ProofId(0), &[lemma]).is_ok());
    }

    #[test]
    fn accepts_nan_not_normal_float8() {
        // (not (and (fp.isNaN x) (fp.isNormal x)))
        let mut t = TermStore::new();
        let x = fp_var(&mut t, "x", 3, 5);
        let is_nan = app1(&mut t, "fp.isNaN", x, Sort::Bool);
        let is_normal = app1(&mut t, "fp.isNormal", x, Sort::Bool);
        let conj = t.mk_app(Symbol::named("and"), vec![is_nan, is_normal], Sort::Bool);
        let lemma = t.mk_not(conj);
        assert!(validate_fp_classification(&t, ProofId(0), &[lemma]).is_ok());
    }

    #[test]
    fn accepts_all_wide_ieee_class_exclusions_symbolically() {
        // The exact IEEE value classes are pairwise disjoint at every width.
        // Float32 deliberately exceeds the exhaustive checker budget, so each
        // acceptance below must come from the width-independent partition rule.
        let mut t = TermStore::new();
        let x = fp_var(&mut t, "x", 8, 24);
        let predicates = [
            "fp.isNaN",
            "fp.isInfinite",
            "fp.isZero",
            "fp.isNormal",
            "fp.isSubnormal",
        ]
        .map(|name| app1(&mut t, name, x, Sort::Bool));

        for (left_index, &left) in predicates.iter().enumerate() {
            for &right in &predicates[left_index + 1..] {
                // This is the exact clause produced by the trust closer for
                // two separately authored positive classification assertions.
                let not_left = t.mk_not(left);
                let not_right = t.mk_not(right);
                assert!(
                    validate_fp_classification(&t, ProofId(0), &[not_left, not_right]).is_ok(),
                    "every pair of distinct IEEE value classes must be disjoint"
                );

                // The same theorem may remain packed as one authored `and`.
                let conjunction = t.mk_app(Symbol::named("and"), vec![left, right], Sort::Bool);
                // Preserve the explicit packed proof literal. `mk_not` is a
                // formula smart constructor and would De Morgan-normalize this
                // to an `or`, whereas proof clauses retain raw literal shape.
                let packed = t.mk_not_raw(conjunction);
                assert!(
                    validate_fp_classification(&t, ProofId(0), &[packed]).is_ok(),
                    "a packed pair of distinct IEEE value classes must be disjoint"
                );
            }
        }
    }

    #[test]
    fn wide_partition_rule_rejects_non_exclusions() {
        let mut t = TermStore::new();
        let x = fp_var(&mut t, "x", 8, 24);
        let y = fp_var(&mut t, "y", 8, 24);
        let zero_x = app1(&mut t, "fp.isZero", x, Sort::Bool);
        let zero_y = app1(&mut t, "fp.isZero", y, Sort::Bool);
        let normal_y = app1(&mut t, "fp.isNormal", y, Sort::Bool);
        let positive_x = app1(&mut t, "fp.isPositive", x, Sort::Bool);
        let not_zero_x = t.mk_not(zero_x);
        let not_zero_y = t.mk_not(zero_y);
        let not_normal_y = t.mk_not(normal_y);
        let not_positive_x = t.mk_not(positive_x);

        assert!(
            validate_fp_classification(&t, ProofId(0), &[not_zero_x, not_normal_y]).is_err(),
            "classes of different FP terms need not be disjoint"
        );
        assert!(
            validate_fp_classification(&t, ProofId(0), &[not_zero_x, not_zero_y]).is_err(),
            "repeating one class is not an exclusion theorem"
        );
        assert!(
            validate_fp_classification(&t, ProofId(0), &[not_zero_x, not_positive_x]).is_err(),
            "+zero is both zero and positive, so sign predicates are not partition members"
        );
    }

    #[test]
    fn wide_partition_rule_rejects_indexed_builtin_lookalikes() {
        // Indexed symbols can carry the same display name as a builtin, but
        // they are not that builtin's core identity. Float32 keeps this test
        // outside the exhaustive fallback so only the symbolic theorem could
        // (incorrectly) authorize either mutant.
        let mut t = TermStore::new();
        let x = fp_var(&mut t, "x", 8, 24);
        let indexed_nan = t.mk_app(Symbol::indexed("fp.isNaN", vec![0]), vec![x], Sort::Bool);
        let normal = app1(&mut t, "fp.isNormal", x, Sort::Bool);
        let not_indexed_nan = t.mk_not(indexed_nan);
        let not_normal = t.mk_not(normal);
        assert!(
            validate_fp_classification(&t, ProofId(0), &[not_indexed_nan, not_normal]).is_err(),
            "an indexed class lookalike must not receive builtin partition authority"
        );

        let nan = app1(&mut t, "fp.isNaN", x, Sort::Bool);
        let indexed_and = t.mk_app(
            Symbol::indexed("and", vec![0]),
            vec![nan, normal],
            Sort::Bool,
        );
        let packed = t.mk_not_raw(indexed_and);
        assert!(
            validate_fp_classification(&t, ProofId(0), &[packed]).is_err(),
            "an indexed connective lookalike must not be decomposed as builtin and"
        );
    }

    #[test]
    fn rejects_nontautology_abs_eq_x() {
        // (= (fp.abs x) x) is NOT a tautology: false for negative x.
        // ADVERSARIAL: a non-tautological FP equality must be REJECTED
        // (accepting it would be a false-UNSAT).
        let mut t = TermStore::new();
        let x = fp_var(&mut t, "x", 3, 5);
        let fp = Sort::FloatingPoint(3, 5);
        let abs_x = app1(&mut t, "fp.abs", x, fp);
        let lemma = eq(&mut t, abs_x, x);
        assert!(
            validate_fp_classification(&t, ProofId(0), &[lemma]).is_err(),
            "(= (fp.abs x) x) is not a tautology and MUST be rejected"
        );
        assert!(recognize_fp_classification_op(&t, &[lemma]).is_none());
    }

    #[test]
    fn rejects_fp_eq_reflexivity_because_nan() {
        // (fp.eq x x) is NOT a tautology: false when x is NaN (IEEE: NaN != NaN).
        let mut t = TermStore::new();
        let x = fp_var(&mut t, "x", 3, 5);
        let lemma = t.mk_app(Symbol::named("fp.eq"), vec![x, x], Sort::Bool);
        assert!(
            validate_fp_classification(&t, ProofId(0), &[lemma]).is_err(),
            "(fp.eq x x) is false on NaN and must be rejected"
        );
    }

    #[test]
    fn accepts_structural_eq_reflexivity() {
        // (= x x) on FP IS a tautology (SMT structural `=` is reflexive, incl NaN).
        let mut t = TermStore::new();
        let x = fp_var(&mut t, "x", 3, 5);
        let lemma = eq(&mut t, x, x);
        // Note: mk_app of (= x x) is built raw here so it does not fold.
        assert!(validate_fp_classification(&t, ProofId(0), &[lemma]).is_ok());
    }

    #[test]
    fn rejects_fp_arithmetic_op() {
        // Any FP arithmetic op must fail closed even inside an otherwise-true shape.
        let mut t = TermStore::new();
        let x = fp_var(&mut t, "x", 3, 5);
        let fp = Sort::FloatingPoint(3, 5);
        // (= (fp.add rm x x) (fp.add rm x x)) — would be reflexively true but
        // fp.add is unsupported, so the collector must fail closed. The rounding
        // mode slot is an uninterpreted placeholder; its sort is irrelevant
        // because the collector rejects the `fp.add` symbol itself.
        let rm = t.mk_var("rm", Sort::Uninterpreted("RoundingMode".to_string()));
        let add = t.mk_app(Symbol::named("fp.add"), vec![rm, x, x], fp);
        let lemma = eq(&mut t, add, add);
        assert!(
            validate_fp_classification(&t, ProofId(0), &[lemma]).is_err(),
            "any clause mentioning fp.add must fail closed"
        );
    }

    #[test]
    fn rejects_too_wide_fp() {
        // Float32 (8,24) = 32 bits exceeds MAX_FP_ASSIGNMENT_BITS — fail closed.
        let mut t = TermStore::new();
        let x = fp_var(&mut t, "x", 8, 24);
        let fp = Sort::FloatingPoint(8, 24);
        let abs_x = app1(&mut t, "fp.abs", x, fp.clone());
        let abs_abs_x = app1(&mut t, "fp.abs", abs_x, fp);
        let lemma = eq(&mut t, abs_abs_x, abs_x);
        assert!(
            validate_fp_classification(&t, ProofId(0), &[lemma]).is_err(),
            "Float32-width FP lemma must exceed the bit budget and fail closed"
        );
    }
}
