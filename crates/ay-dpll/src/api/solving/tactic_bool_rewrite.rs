// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Counted Boolean De Morgan rewriting for simplify's real `elim_and` option.
//! Standard identity: AND(a...) = NOT(OR(NOT(a)...)). No new free symbols.
//! Theory predicates and declared Boolean applications are opaque atoms.
use super::field_to_bv::Borrowed;
use super::tactic_parameters::Steps;
use super::tactics::TacticFailure;
use ay_core::term::{
    reserve_counted, CountedBuiltin as Op, CountedTermBuilder, TermConstructionAdmission,
};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ConjunctionMode {
    Retain,
    Eliminate,
}

fn failed() -> TacticFailure {
    TacticFailure::new("parameterized simplify requires an admitted Boolean expression")
}

fn boolean_application(
    store: &TermStore,
    id: TermId,
    symbol: &Symbol,
    args: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<bool, TacticFailure> {
    owner
        .admit(
            args.len()
                .checked_mul(2)
                .and_then(|work| work.checked_add(symbol.name().len()))
                .ok_or_else(failed)?,
            0,
        )
        .map_err(|_| failed())?;
    if args.iter().any(|child| child.index() >= id.index()) {
        return Err(failed());
    }
    let Symbol::Named(name) = symbol else {
        return Ok(false);
    };
    // An equal printed name never turns a declared predicate into a Boolean
    // connective. Preserving its exact term requires no declaration adoption.
    if store.is_declared_function(name) {
        return Ok(false);
    }
    match name.as_str() {
        "=" | "distinct" => {
            if args.len() < 2 {
                return Err(failed());
            }
            if store.sort(args[0]) != &Sort::Bool {
                return Ok(false);
            }
            if args.iter().any(|arg| store.sort(*arg) != &Sort::Bool) {
                return Err(failed());
            }
            Ok(true)
        }
        "and" | "or" | "xor" | "not" | "=>" | "ite" => {
            let arity = match name.as_str() {
                "not" => args.len() == 1,
                "=>" => args.len() == 2,
                "ite" => args.len() == 3,
                _ => !args.is_empty(),
            };
            if !arity || args.iter().any(|arg| store.sort(*arg) != &Sort::Bool) {
                return Err(failed());
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

pub(super) fn rewrite(
    store: &mut TermStore,
    roots: &[TermId],
    conjunctions: ConjunctionMode,
    budget: &mut Steps,
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<TermId>, TacticFailure> {
    let n = store.len();
    let mut seen = Vec::new();
    reserve_counted(&mut seen, n, owner).map_err(|_| failed())?;
    owner.admit(n, 0).map_err(|_| failed())?;
    seen.resize(n, false);
    let mut mapped = Vec::new();
    reserve_counted(&mut mapped, n, owner).map_err(|_| failed())?;
    owner.admit(n, 0).map_err(|_| failed())?;
    mapped.resize(n, None);
    let mut todo = Vec::new();
    reserve_counted(&mut todo, roots.len(), owner).map_err(|_| failed())?;
    owner.admit(roots.len(), 0).map_err(|_| failed())?;
    todo.extend_from_slice(roots);
    while let Some(id) = todo.pop() {
        owner.admit(1, 0).map_err(|_| failed())?;
        if id.index() >= n || store.sort(id) != &Sort::Bool {
            return Err(failed());
        }
        if seen[id.index()] {
            continue;
        }
        seen[id.index()] = true;
        let children: &[TermId] = match store.get(id) {
            TermData::Var(..) | TermData::Const(Constant::Bool(_)) => {
                mapped[id.index()] = Some(id);
                &[]
            }
            TermData::Not(a) => std::slice::from_ref(a),
            TermData::App(symbol, args) => {
                if boolean_application(store, id, symbol, args, owner)? {
                    args
                } else {
                    mapped[id.index()] = Some(id);
                    &[]
                }
            }
            TermData::Ite(a, b, c) => {
                reserve_counted(&mut todo, 3, owner).map_err(|_| failed())?;
                for child in [*a, *b, *c] {
                    if child.index() >= id.index() {
                        return Err(failed());
                    }
                    todo.push(child);
                }
                continue;
            }
            _ => return Err(failed()),
        };
        owner.admit(children.len(), 0).map_err(|_| failed())?;
        reserve_counted(&mut todo, children.len(), owner).map_err(|_| failed())?;
        for &child in children {
            if child.index() >= id.index() {
                return Err(failed());
            }
            todo.push(child);
        }
    }
    let borrowed = Borrowed(owner);
    let mut builder = CountedTermBuilder::with_admission(store, &borrowed).map_err(|_| failed())?;
    let mut args = Vec::new();
    for index in 0..n {
        if !seen[index] {
            continue;
        }
        budget.visit(owner)?;
        if mapped[index].is_some() {
            continue;
        }
        let id = TermId(index as u32);
        args.clear();
        let (op, children): (Option<Op>, &[TermId]) = match builder.terms().get(id) {
            TermData::Var(..) | TermData::Const(Constant::Bool(_)) => {
                mapped[index] = Some(id);
                continue;
            }
            TermData::Not(a) => (Some(Op::Not), std::slice::from_ref(a)),
            TermData::Ite(a, b, c) => {
                let ids = [*a, *b, *c];
                reserve_counted(&mut args, 3, owner).map_err(|_| failed())?;
                for child in ids {
                    args.push(mapped[child.index()].ok_or_else(failed)?);
                }
                mapped[index] = Some(builder.apply(Op::Ite, &args).map_err(|_| failed())?);
                continue;
            }
            TermData::App(Symbol::Named(name), children) => {
                let op = match name.as_str() {
                    "and" => Op::And,
                    "or" => Op::Or,
                    "not" => Op::Not,
                    "=>" => Op::Implies,
                    "xor" => Op::Xor,
                    "=" => Op::Eq,
                    "distinct" => Op::Distinct,
                    "ite" => Op::Ite,
                    _ => return Err(failed()),
                };
                (Some(op), children)
            }
            _ => return Err(failed()),
        };
        owner.admit(children.len(), 0).map_err(|_| failed())?;
        reserve_counted(&mut args, children.len(), owner).map_err(|_| failed())?;
        for child in children {
            args.push(mapped[child.index()].ok_or_else(failed)?);
        }
        let op = op.ok_or_else(failed)?;
        let value = if conjunctions == ConjunctionMode::Eliminate && op == Op::And {
            eliminate_and(&mut builder, &mut args)?
        } else {
            builder.apply(op, &args).map_err(|_| failed())?
        };
        mapped[index] = Some(value);
    }
    let mut result = Vec::new();
    reserve_counted(&mut result, roots.len(), owner).map_err(|_| failed())?;
    for root in roots {
        owner.admit(1, 0).map_err(|_| failed())?;
        result.push(mapped[root.index()].ok_or_else(failed)?);
    }
    builder.finish().map_err(|_| failed())?;
    owner.check().map_err(|_| failed())?;
    Ok(result)
}

pub(super) fn eliminate_and(
    builder: &mut CountedTermBuilder<'_, '_, Borrowed<'_>>,
    args: &mut [TermId],
) -> Result<TermId, TacticFailure> {
    for arg in args.iter_mut() {
        *arg = builder.apply(Op::Not, &[*arg]).map_err(|_| failed())?;
    }
    let disjunction = builder.apply(Op::Or, args).map_err(|_| failed())?;
    builder.apply(Op::Not, &[disjunction]).map_err(|_| failed())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use ay_model_check::{EvalOutcome, ModelValue, ModelView};
    use std::sync::Arc;

    struct Values<'a> {
        vars: [TermId; 4],
        predicate: TermId,
        integer: i32,
        bits: u32,
        field: u32,
        mask: u8,
        owner: &'a CountedAdmission,
    }
    impl ModelView for Values<'_> {
        fn has_evaluation_admission(&self) -> bool {
            true
        }
        fn admit_evaluation_work(&self, work: usize, bytes: usize) -> Result<(), String> {
            self.owner.admit(work, bytes).map_err(|e| e.to_string())
        }
        fn leaf_value(&self, id: TermId) -> Option<ModelValue> {
            match self.vars.iter().position(|var| *var == id)? {
                0 => Some(ModelValue::Int(self.integer.into())),
                1 => Some(ModelValue::BitVec {
                    width: 4,
                    value: self.bits.into(),
                }),
                2 => Some(ModelValue::Int(self.field.into())),
                _ => Some(ModelValue::Bool(self.mask & 1 != 0)),
            }
        }
        fn uf_app_value(&self, id: TermId) -> Option<ModelValue> {
            (id == self.predicate).then_some(ModelValue::Bool(self.mask & 2 != 0))
        }
    }

    #[test]
    fn tactic_parameters_preserve_mixed_theory_atoms_and_reference_equivalence() {
        const DECLARATIONS: &str = "(set-logic ALL)
            (declare-const i Int) (declare-const b (_ BitVec 4))
            (declare-const f (_ FiniteField 5)) (declare-const p Bool)
            (declare-fun pred (Int) Bool)";
        let mut solver = crate::api::Solver::new(crate::api::Logic::All);
        let roots = solver
            .parse_smtlib2(&format!(
                "{DECLARATIONS}
                 (assert (> i 0)) (assert (bvult b #x3))
                 (assert (= (ff.mul f f) #f1m5)) (assert p) (assert (pred i))"
            ))
            .unwrap();
        let vars = ["i", "b", "f", "p"].map(|name| {
            solver
                .executor
                .context()
                .symbol_info(name)
                .unwrap()
                .term
                .unwrap()
        });
        let predicate = roots.last().unwrap().id();
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(1 << 20, 16 << 20),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        let terms = &mut solver.executor.context_mut().terms;
        let root = terms.mk_app(
            Symbol::named("and"),
            roots.iter().map(|term| term.id()).collect::<Vec<_>>(),
            Sort::Bool,
        );
        let rewritten = rewrite(
            terms,
            &[root],
            ConjunctionMode::Eliminate,
            &mut Steps::new(None),
            &owner,
        )
        .unwrap()[0];
        assert_ne!(root, rewritten);
        for integer in [-1, 0, 1] {
            for bits in [0, 2, 3, 15] {
                for field in [0, 1, 2, 4] {
                    for mask in 0..4 {
                        let view = Values {
                            vars,
                            predicate,
                            integer,
                            bits,
                            field,
                            mask,
                            owner: &owner,
                        };
                        let evaluator = ay_model_check::Evaluator::new(terms, &view);
                        let expected =
                            integer > 0 && bits < 3 && field * field % 5 == 1 && mask == 3;
                        for term in [root, rewritten] {
                            assert!(
                                matches!(evaluator.evaluate(term), EvalOutcome::Value(ModelValue::Bool(value)) if value == expected)
                            );
                        }
                    }
                }
            }
        }
        let before = solver.executor.format_term(root);
        let after = solver.executor.format_term(rewritten);
        let input = tempfile::NamedTempFile::new().unwrap();
        let script = format!("{DECLARATIONS}\n(assert (xor {before} {after}))\n(check-sat)\n");
        use sha2::Digest;
        eprintln!(
            "AY-TEST-INPUT suite=parameterized-simplify-theory-atoms sha256={:x}",
            sha2::Sha256::digest(script.as_bytes())
        );
        std::fs::write(input.path(), script).unwrap();
        let output = ay_test_support::z3::require_z3("parameterized-simplify-theory-atoms")
            .command()
            .args(["-smt2", "-T:5", "memory_max_size=256"])
            .arg(input.path())
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "unsat");
    }

    #[test]
    fn tactic_parameters_declared_connective_spelling_stays_opaque() {
        let mut terms = TermStore::new();
        terms.register_declared_function("and");
        let a = terms.mk_var("a", Sort::Bool);
        let b = terms.mk_var("b", Sort::Bool);
        let predicate = terms.mk_app(Symbol::named("and"), [a, b], Sort::Bool);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(1 << 20, 16 << 20),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        assert_eq!(
            rewrite(
                &mut terms,
                &[predicate],
                ConjunctionMode::Eliminate,
                &mut Steps::new(None),
                &owner
            )
            .unwrap(),
            vec![predicate]
        );
    }
}
