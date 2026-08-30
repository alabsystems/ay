// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked Alethe lowering for bounded logical-right-shift monotonicity.
//!
//! The accepted shape is the exact E5 contradiction
//! `0 < x /\ x <= (x >> k)`, after AY's constant-shift normalization has
//! rewritten the shift to `concat(0_k, extract(x, width-1, k))`.  Carcara has
//! no `bvlshr` or `zero_extend` proof rule, but it does independently check the
//! `bitblast_const`, `bitblast_extract`, `bitblast_concat`, `bitblast_ult`,
//! pseudo-Boolean comparison, propositional, and `drat` rules used here.

#[cfg(test)]
#[path = "shift_monotonicity_tests.rs"]
mod tests;

use super::super::{parse_printed_bitvec_literal, AlethePrinter};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId};
use std::fmt::Write as _;

/// Exhaustive RUP emits `2^(w+1)-1` clauses. Eight bits is 511 clauses and is
/// the ratified E5 carrier; wider words stay on the honest `hole` path.
const MAX_SHIFT_MONOTONIC_WIDTH: u32 = 8;

#[derive(Clone, Copy)]
struct ShiftShape {
    literal: TermId,
    root: TermId,
    positive: TermId,
    non_strict: TermId,
    zero: TermId,
    value: TermId,
    shifted: TermId,
    high_zero: TermId,
    extract: TermId,
    width: u32,
    shift: u32,
}

struct ShiftText {
    literal: String,
    root: String,
    positive: String,
    non_strict: String,
    strict: String,
    zero: String,
    value: String,
    shifted: String,
    high_zero: String,
    extract: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum BoolExpr {
    Atom(String),
    App(&'static str, Vec<BoolLit>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct BoolLit {
    var: usize,
    negated: bool,
}

impl BoolLit {
    fn flip(self) -> Self {
        Self {
            var: self.var,
            negated: !self.negated,
        }
    }
}

struct CnfStep {
    clause: Vec<i32>,
    rule: &'static str,
    suffix: String,
    rendered: String,
}

#[derive(Default)]
struct BoolCircuit {
    exprs: Vec<BoolExpr>,
    ids: HashMap<BoolExpr, usize>,
    clauses: Vec<CnfStep>,
}

impl BoolCircuit {
    fn intern(&mut self, expr: BoolExpr) -> BoolLit {
        let var = if let Some(&var) = self.ids.get(&expr) {
            var
        } else {
            let var = self.exprs.len();
            self.exprs.push(expr.clone());
            self.ids.insert(expr, var);
            var
        };
        BoolLit {
            var,
            negated: false,
        }
    }

    fn atom(&mut self, text: impl Into<String>) -> BoolLit {
        self.intern(BoolExpr::Atom(text.into()))
    }

    fn app(&mut self, op: &'static str, args: Vec<BoolLit>) -> BoolLit {
        self.intern(BoolExpr::App(op, args))
    }

    fn integer(lit: BoolLit) -> i32 {
        let value = i32::try_from(lit.var + 1).expect("bounded E5 circuit fits i32");
        if lit.negated {
            -value
        } else {
            value
        }
    }

    fn text(&self, lit: BoolLit) -> String {
        let body = match &self.exprs[lit.var] {
            BoolExpr::Atom(atom) => atom.clone(),
            BoolExpr::App(op, args) => format!(
                "({op} {})",
                args.iter()
                    .map(|&arg| self.text(arg))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        };
        if lit.negated {
            format!("(not {body})")
        } else {
            body
        }
    }

    fn negated_text(&self, lit: BoolLit) -> String {
        // Alethe's tautology rules are syntactic. In particular, negating the
        // term `(not false)` must print `(not (not false))`, not `false`.
        format!("(not {})", self.text(lit))
    }

    fn clause_text(&self, clause: &[i32]) -> String {
        let mut out = String::from("(cl");
        for &integer in clause {
            let var = usize::try_from(integer.unsigned_abs() - 1)
                .expect("bounded E5 circuit index fits usize");
            let _ = write!(
                out,
                " {}",
                self.text(BoolLit {
                    var,
                    negated: integer < 0,
                })
            );
        }
        out.push(')');
        out
    }

    fn syntax_clause(terms: &[String]) -> String {
        format!(
            "(cl{})",
            terms
                .iter()
                .map(|term| format!(" {term}"))
                .collect::<String>()
        )
    }

    fn add_clause(
        &mut self,
        lits: Vec<BoolLit>,
        rule: &'static str,
        suffix: String,
        syntax: Option<Vec<String>>,
    ) {
        let clause = lits.into_iter().map(Self::integer).collect::<Vec<_>>();
        let rendered = syntax
            .as_deref()
            .map(Self::syntax_clause)
            .unwrap_or_else(|| self.clause_text(&clause));
        self.clauses.push(CnfStep {
            clause,
            rule,
            suffix,
            rendered,
        });
    }

    fn build_cnf(&mut self) -> Option<()> {
        for var in 0..self.exprs.len() {
            let gate = BoolLit {
                var,
                negated: false,
            };
            match self.exprs[var].clone() {
                BoolExpr::Atom(atom) => {
                    if atom == "false" {
                        self.add_clause(vec![gate.flip()], "false", String::new(), None);
                    } else if atom == "true" {
                        self.add_clause(vec![gate], "true", String::new(), None);
                    }
                }
                BoolExpr::App("and", args) => {
                    for (index, &arg) in args.iter().enumerate() {
                        self.add_clause(
                            vec![gate.flip(), arg],
                            "and_pos",
                            format!(" :args ({index})"),
                            Some(vec![self.negated_text(gate), self.text(arg)]),
                        );
                    }
                    let mut lits = vec![gate];
                    lits.extend(args.iter().map(|arg| arg.flip()));
                    let mut syntax = vec![self.text(gate)];
                    syntax.extend(args.iter().map(|&arg| self.negated_text(arg)));
                    self.add_clause(lits, "and_neg", String::new(), Some(syntax));
                }
                BoolExpr::App("or", args) => {
                    let mut lits = vec![gate.flip()];
                    lits.extend(args.iter().copied());
                    let mut syntax = vec![self.negated_text(gate)];
                    syntax.extend(args.iter().map(|&arg| self.text(arg)));
                    self.add_clause(lits, "or_pos", String::new(), Some(syntax));
                    for (index, &arg) in args.iter().enumerate() {
                        self.add_clause(
                            vec![gate, arg.flip()],
                            "or_neg",
                            format!(" :args ({index})"),
                            Some(vec![self.text(gate), self.negated_text(arg)]),
                        );
                    }
                }
                BoolExpr::App("=", args) => {
                    let [a, b] = args.as_slice() else {
                        return None;
                    };
                    let (a, b) = (*a, *b);
                    self.add_clause(
                        vec![gate.flip(), a, b.flip()],
                        "equiv_pos1",
                        String::new(),
                        Some(vec![
                            self.negated_text(gate),
                            self.text(a),
                            self.negated_text(b),
                        ]),
                    );
                    self.add_clause(
                        vec![gate.flip(), a.flip(), b],
                        "equiv_pos2",
                        String::new(),
                        Some(vec![
                            self.negated_text(gate),
                            self.negated_text(a),
                            self.text(b),
                        ]),
                    );
                    self.add_clause(
                        vec![gate, a.flip(), b.flip()],
                        "equiv_neg1",
                        String::new(),
                        Some(vec![
                            self.text(gate),
                            self.negated_text(a),
                            self.negated_text(b),
                        ]),
                    );
                    self.add_clause(
                        vec![gate, a, b],
                        "equiv_neg2",
                        String::new(),
                        Some(vec![self.text(gate), self.text(a), self.text(b)]),
                    );
                }
                BoolExpr::App(_, _) => return None,
            }
        }
        Some(())
    }
}

fn unsigned_lt(circuit: &mut BoolCircuit, lhs: &[BoolLit], rhs: &[BoolLit]) -> Option<BoolLit> {
    if lhs.len() != rhs.len() || lhs.is_empty() {
        return None;
    }
    let mut result = circuit.app("and", vec![lhs[0].flip(), rhs[0]]);
    for index in 1..lhs.len() {
        let same = circuit.app("=", vec![lhs[index], rhs[index]]);
        let prefix = circuit.app("and", vec![same, result]);
        let strict = circuit.app("and", vec![lhs[index].flip(), rhs[index]]);
        result = circuit.app("or", vec![prefix, strict]);
    }
    Some(result)
}

fn normalize_clause(clause: &[i32]) -> Option<Vec<i32>> {
    let mut out = Vec::with_capacity(clause.len());
    for &literal in clause {
        if out.contains(&-literal) {
            return None;
        }
        if !out.contains(&literal) {
            out.push(literal);
        }
    }
    Some(out)
}

fn rup_conflict(clauses: &[Vec<i32>], goal: &[i32]) -> bool {
    // RUP checks `clauses /\ not(goal)` by unit propagation.
    let mut assignment = HashMap::<usize, bool>::default();
    for &literal in goal {
        let var = literal.unsigned_abs() as usize;
        let value = literal < 0;
        match assignment.insert(var, value) {
            Some(previous) if previous != value => return true,
            _ => {}
        }
    }
    loop {
        let mut changed = false;
        for clause in clauses {
            let mut satisfied = false;
            let mut unknown = Vec::new();
            for &literal in clause {
                let var = literal.unsigned_abs() as usize;
                match assignment.get(&var) {
                    Some(&value) if value == (literal > 0) => {
                        satisfied = true;
                        break;
                    }
                    Some(_) => {}
                    None => unknown.push(literal),
                }
            }
            if satisfied {
                continue;
            }
            let [unit] = unknown.as_slice() else {
                if unknown.is_empty() {
                    return true;
                }
                continue;
            };
            let var = unit.unsigned_abs() as usize;
            let value = *unit > 0;
            match assignment.insert(var, value) {
                Some(previous) if previous != value => return true,
                Some(_) => {}
                None => changed = true,
            }
        }
        if !changed {
            return false;
        }
    }
}

fn exhaustive_rup(
    circuit: &BoolCircuit,
    bits: &[BoolLit],
    positive: BoolLit,
    strict: BoolLit,
) -> Option<Vec<Vec<i32>>> {
    let mut database = circuit
        .clauses
        .iter()
        .map(|step| normalize_clause(&step.clause))
        .collect::<Option<Vec<_>>>()?;
    database.push(vec![BoolCircuit::integer(positive)]);
    database.push(vec![-BoolCircuit::integer(strict)]);
    let atom_vars = bits
        .iter()
        .map(|&bit| BoolCircuit::integer(bit))
        .collect::<Vec<_>>();
    let assignments = 1_usize.checked_shl(u32::try_from(bits.len()).ok()?)?;
    let mut additions = Vec::with_capacity(assignments.saturating_mul(2).saturating_sub(1));
    let mut cubes = Vec::with_capacity(assignments);
    for assignment in 0..assignments {
        let clause = atom_vars
            .iter()
            .enumerate()
            .map(|(index, &var)| {
                if assignment & (1_usize << index) == 0 {
                    var
                } else {
                    -var
                }
            })
            .collect::<Vec<_>>();
        if !rup_conflict(&database, &clause) {
            return None;
        }
        database.push(clause.clone());
        additions.push(clause.clone());
        cubes.push(clause);
    }
    for &var in &atom_vars {
        let mut next = Vec::with_capacity(cubes.len() / 2);
        for pair in cubes.chunks_exact(2) {
            let [left, right] = pair else {
                return None;
            };
            if !left.contains(&var) || !right.contains(&-var) {
                return None;
            }
            let resolvent = left
                .iter()
                .copied()
                .filter(|literal| literal.unsigned_abs() != var.unsigned_abs())
                .collect::<Vec<_>>();
            let other = right
                .iter()
                .copied()
                .filter(|literal| literal.unsigned_abs() != var.unsigned_abs())
                .collect::<Vec<_>>();
            if normalize_clause(&resolvent)? != normalize_clause(&other)?
                || !rup_conflict(&database, &resolvent)
            {
                return None;
            }
            database.push(resolvent.clone());
            additions.push(resolvent.clone());
            next.push(resolvent);
        }
        cubes = next;
    }
    (cubes.as_slice() == [Vec::<i32>::new()]).then_some(additions)
}

impl AlethePrinter<'_> {
    pub(super) fn format_bv_shift_monotonicity(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let [literal] = clause else {
            return None;
        };
        let shape = self.decode_shift_shape(*literal)?;
        if shape.width == 0
            || shape.width > MAX_SHIFT_MONOTONIC_WIDTH
            || shape.shift == 0
            || shape.shift >= shape.width
        {
            return None;
        }
        let text = self.shift_text(shape)?;
        let mut circuit = BoolCircuit::default();
        let false_lit = circuit.atom("false");
        let bits = (0..shape.width)
            .map(|index| circuit.atom(format!("((_ @bit_of {index}) {})", text.value)))
            .collect::<Vec<_>>();
        let zero_bits = vec![false_lit; shape.width as usize];
        let positive_bool = unsigned_lt(&mut circuit, &zero_bits, &bits)?;
        let mut shifted_bits = bits[shape.shift as usize..].to_vec();
        shifted_bits.extend(std::iter::repeat_n(false_lit, shape.shift as usize));
        let strict_bool = unsigned_lt(&mut circuit, &shifted_bits, &bits)?;
        circuit.build_cnf()?;
        let additions = exhaustive_rup(&circuit, &bits, positive_bool, strict_bool)?;

        let bbzero = format!(
            "(@bbterm {})",
            std::iter::repeat_n("false", shape.width as usize)
                .collect::<Vec<_>>()
                .join(" ")
        );
        let bbhigh = format!(
            "(@bbterm {})",
            std::iter::repeat_n("false", shape.shift as usize)
                .collect::<Vec<_>>()
                .join(" ")
        );
        let bbextract = format!(
            "(@bbterm {})",
            bits[shape.shift as usize..]
                .iter()
                .map(|&bit| circuit.text(bit))
                .collect::<Vec<_>>()
                .join(" ")
        );
        let bbshifted = format!(
            "(@bbterm {})",
            shifted_bits
                .iter()
                .map(|&bit| circuit.text(bit))
                .collect::<Vec<_>>()
                .join(" ")
        );
        let positive_surface = circuit.text(positive_bool);
        let strict_surface = circuit.text(strict_bool);
        let sx = Self::pbblast_value_sum(&text.value, shape.width);
        let sz = Self::pbblast_value_sum(&text.shifted, shape.width);
        let a = format!("(>= (- {sz} {sx}) 0)");
        let b = format!("(>= (- {sx} {sz}) 1)");
        let ab = format!("(= {a} (not {b}))");

        let mut out = format!(
            "(step {id}.c0 (cl (= {zero} {bbzero})) :rule bitblast_const)\n\
             (step {id}.pc (cl (= {positive} (bvult {bbzero} {value}))) :rule cong :premises ({id}.c0))\n\
             (step {id}.pb (cl (= (bvult {bbzero} {value}) {positive_surface})) :rule bitblast_ult)\n\
             (step {id}.pe (cl (= {positive} {positive_surface})) :rule trans :premises ({id}.pc {id}.pb))\n\
             (step {id}.ch (cl (= {high_zero} {bbhigh})) :rule bitblast_const)\n\
             (step {id}.ex (cl (= {extract} {bbextract})) :rule bitblast_extract)\n\
             (step {id}.zc (cl (= {shifted} (concat {bbhigh} {bbextract}))) :rule cong :premises ({id}.ch {id}.ex))\n\
             (step {id}.zb (cl (= (concat {bbhigh} {bbextract}) {bbshifted})) :rule bitblast_concat)\n\
             (step {id}.ze (cl (= {shifted} {bbshifted})) :rule trans :premises ({id}.zc {id}.zb))\n\
             (step {id}.rc (cl (= {strict} (bvult {bbshifted} {value}))) :rule cong :premises ({id}.ze))\n\
             (step {id}.rb (cl (= (bvult {bbshifted} {value}) {strict_surface})) :rule bitblast_ult)\n\
             (step {id}.re (cl (= {strict} {strict_surface})) :rule trans :premises ({id}.rc {id}.rb))\n\
             (step {id}.qa (cl (= {non_strict} {a})) :rule pbblast_bvule)\n\
             (step {id}.rp (cl (= {strict} {b})) :rule pbblast_bvult)\n\
             (step {id}.f1 (cl (not {a}) (not {b})) :rule la_generic :args (1 1))\n\
             (step {id}.f2 (cl {a} {b}) :rule la_generic :args (1 1))\n\
             (step {id}.n1 (cl {ab} (not {a}) (not (not {b}))) :rule equiv_neg1)\n\
             (step {id}.n2 (cl {ab} {a} (not {b})) :rule equiv_neg2)\n\
             (step {id}.ar1 (cl {ab} (not {b})) :rule resolution :premises ({id}.n2 {id}.f1))\n\
             (step {id}.ar2 (cl {ab} (not (not {b})) {b}) :rule resolution :premises ({id}.n1 {id}.f2))\n\
             (step {id}.ar3 (cl {ab} (not (not {b}))) :rule resolution :premises ({id}.ar2 {id}.ar1))\n\
             (step {id}.nn (cl (not (not (not {b}))) {b}) :rule not_not)\n\
             (step {id}.ar4 (cl {ab} {b}) :rule resolution :premises ({id}.ar3 {id}.nn))\n\
             (step {id}.aeq (cl {ab}) :rule resolution :premises ({id}.ar4 {id}.ar1))\n\
             (step {id}.qb (cl (= {non_strict} (not {b}))) :rule trans :premises ({id}.qa {id}.aeq))\n\
             (step {id}.nr (cl (= (not {strict}) (not {b}))) :rule cong :premises ({id}.rp))\n\
             (step {id}.nrs (cl (= (not {b}) (not {strict}))) :rule symm :premises ({id}.nr))\n\
             (step {id}.qr (cl (= {non_strict} (not {strict}))) :rule trans :premises ({id}.qb {id}.nrs))",
            zero = text.zero,
            positive = text.positive,
            value = text.value,
            high_zero = text.high_zero,
            extract = text.extract,
            shifted = text.shifted,
            strict = text.strict,
            non_strict = text.non_strict,
        );

        let mut cnf_ids = Vec::with_capacity(circuit.clauses.len());
        for (index, step) in circuit.clauses.iter().enumerate() {
            let step_id = format!("{id}.cnf{index}");
            cnf_ids.push(step_id.clone());
            let _ = write!(
                out,
                "\n(step {step_id} {} :rule {}{})",
                step.rendered, step.rule, step.suffix
            );
        }
        let _ = write!(
            out,
            "\n(anchor :step {id}.prsp0)\n\
             (assume {id}.prsp.hp {positive_surface})\n\
             (assume {id}.prsp.hnr (not {strict_surface}))"
        );
        let args = additions
            .iter()
            .map(|clause| circuit.clause_text(clause))
            .collect::<Vec<_>>()
            .join(" ");
        cnf_ids.push(format!("{id}.prsp.hp"));
        cnf_ids.push(format!("{id}.prsp.hnr"));
        let premises = cnf_ids.join(" ");
        let _ = write!(
            out,
            "\n(step {id}.prsp.ref (cl) :rule drat :premises ({premises}) :args ({args}))\n\
             (step {id}.prsp0 (cl (not {positive_surface}) (not (not {strict_surface})) false) :rule subproof :discharge ({id}.prsp.hp {id}.prsp.hnr))\n\
             (step {id}.prsp (cl (not {positive_surface}) (not (not {strict_surface}))) :rule resolution :premises ({id}.prsp0 {id}.cnf0))\n\
             (step {id}.prnn (cl (not (not (not {strict_surface}))) {strict_surface}) :rule not_not)\n\
             (step {id}.pr (cl (not {positive_surface}) {strict_surface}) :rule resolution :premises ({id}.prsp {id}.prnn))\n\
             (step {id}.pp (cl (not {positive}) {positive_surface}) :rule equiv1 :premises ({id}.pe))\n\
             (step {id}.rr (cl {strict} (not {strict_surface})) :rule equiv2 :premises ({id}.re))\n\
             (step {id}.pR (cl (not {positive}) {strict_surface}) :rule resolution :premises ({id}.pp {id}.pr))\n\
             (step {id}.prw (cl (not {positive}) {strict}) :rule resolution :premises ({id}.pR {id}.rr))\n\
             (step {id}.qn (cl (not {non_strict}) (not {strict})) :rule equiv1 :premises ({id}.qr))\n\
             (step {id}.pq (cl (not {positive}) (not {non_strict})) :rule resolution :premises ({id}.prw {id}.qn))\n\
             (step {id}.ap (cl (not {root}) {positive}) :rule and_pos :args (0))\n\
             (step {id}.aq (cl (not {root}) {non_strict}) :rule and_pos :args (1))\n\
             (step {id}.pqa (cl (not {non_strict}) (not {root})) :rule resolution :premises ({id}.pq {id}.ap))\n\
             (step {id} (cl {literal}) :rule resolution :premises ({id}.pqa {id}.aq))",
            positive = text.positive,
            strict = text.strict,
            non_strict = text.non_strict,
            root = text.root,
            literal = text.literal,
        );
        self.charge(out.len() as u64);
        Some(out)
    }

    fn decode_shift_shape(&self, literal: TermId) -> Option<ShiftShape> {
        let TermData::Not(root) = self.terms.get(literal) else {
            return None;
        };
        let root = *root;
        let TermData::App(Symbol::Named(and), root_args) = self.terms.get(root) else {
            return None;
        };
        let [positive, non_strict] = root_args.as_slice() else {
            return None;
        };
        if and != "and" || self.terms.sort(root) != &Sort::Bool {
            return None;
        }
        let (positive, non_strict) = (*positive, *non_strict);
        let TermData::App(Symbol::Named(ult), positive_args) = self.terms.get(positive) else {
            return None;
        };
        let [zero, value] = positive_args.as_slice() else {
            return None;
        };
        if ult != "bvult" || self.terms.sort(positive) != &Sort::Bool {
            return None;
        }
        let (zero, value) = (*zero, *value);
        let Sort::BitVec(bits) = self.terms.sort(value) else {
            return None;
        };
        let width = bits.width;
        if !matches!(
            self.terms.get(zero),
            TermData::Const(Constant::BitVec { value, width: zero_width })
                if *zero_width == width && *value == 0u32.into()
        ) {
            return None;
        }
        let TermData::App(Symbol::Named(ule), non_strict_args) = self.terms.get(non_strict) else {
            return None;
        };
        let [same_value, shifted] = non_strict_args.as_slice() else {
            return None;
        };
        if ule != "bvule"
            || self.terms.sort(non_strict) != &Sort::Bool
            || *same_value != value
            || self.terms.sort(*shifted) != self.terms.sort(value)
        {
            return None;
        }
        let shifted = *shifted;
        let TermData::App(Symbol::Named(concat), concat_args) = self.terms.get(shifted) else {
            return None;
        };
        let [high_zero, extract] = concat_args.as_slice() else {
            return None;
        };
        if concat != "concat" {
            return None;
        }
        let (high_zero, extract) = (*high_zero, *extract);
        let TermData::Const(Constant::BitVec {
            value: high_value,
            width: shift,
        }) = self.terms.get(high_zero)
        else {
            return None;
        };
        if *high_value != 0u32.into() {
            return None;
        }
        let shift = *shift;
        if self.terms.sort(high_zero) != &Sort::bitvec(shift) {
            return None;
        }
        let TermData::App(Symbol::Indexed(extract_op, indices), extract_args) =
            self.terms.get(extract)
        else {
            return None;
        };
        let extract_width = width.checked_sub(shift)?;
        if extract_op != "extract"
            || indices.as_slice() != [width.checked_sub(1)?, shift]
            || extract_args.as_slice() != [value]
            || self.terms.sort(extract) != &Sort::bitvec(extract_width)
            || shift.checked_add(extract_width)? != width
        {
            return None;
        }
        Some(ShiftShape {
            literal,
            root,
            positive,
            non_strict,
            zero,
            value,
            shifted,
            high_zero,
            extract,
            width,
            shift,
        })
    }

    fn shift_text(&self, shape: ShiftShape) -> Option<ShiftText> {
        let zero = self.format_term(shape.zero);
        let value = self.format_term(shape.value);
        let high_zero = self.format_term(shape.high_zero);
        let extract = self.format_term(shape.extract);
        let shifted = self.format_term(shape.shifted);
        let positive = self.format_term(shape.positive);
        let non_strict = self.format_term(shape.non_strict);
        let root = self.format_term(shape.root);
        let literal = self.format_term(shape.literal);
        let (zero_value, zero_width) = parse_printed_bitvec_literal(&zero)?;
        let (high_value, high_width) = parse_printed_bitvec_literal(&high_zero)?;
        if zero_value != 0u32.into()
            || zero_width != shape.width
            || high_value != 0u32.into()
            || high_width != shape.shift
            || extract
                != format!(
                    "((_ extract {} {}) {value})",
                    shape.width.checked_sub(1)?,
                    shape.shift
                )
            || shifted != format!("(concat {high_zero} {extract})")
            || positive != format!("(bvult {zero} {value})")
            || non_strict != format!("(bvule {value} {shifted})")
            || root != format!("(and {positive} {non_strict})")
            || literal != format!("(not {root})")
        {
            return None;
        }
        Some(ShiftText {
            literal,
            root,
            positive,
            non_strict,
            strict: format!("(bvult {shifted} {value})"),
            zero,
            value,
            shifted,
            high_zero,
            extract,
        })
    }
}
