// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An integer equality forced by two bounds. Rational Farkas arithmetic
//! cannot directly prove a positive equality: split its disequality into
//! the two orders, tighten each supplied bound with checked integer
//! `la_generic`, then resolve. Recognition and publication use the same
//! bounded plan over the actual printed literals.

use super::super::la_generic_surface::printed_la_generic_holds;
use super::*;

struct Plan {
    equality: String,
    sides: [String; 2],
    guards: [String; 2],
    clause: String,
}

pub(super) fn lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    kind: &ay_core::TheoryLemmaKind,
    overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, overrides, Some(MAX_WORK))
        .with_assembled_rendering(AssembledRendering::CachedWithinBudget);
    plan(&printer, clause, kind).is_some() && !printer.work_budget_exhausted()
}

pub(super) fn render(
    printer: &AlethePrinter<'_>,
    id: ProofId,
    clause: &[TermId],
    kind: &ay_core::TheoryLemmaKind,
) -> Option<String> {
    let plan = plan(printer, clause, kind)?;
    if printer.work_budget_exhausted() {
        return None;
    }
    let Plan {
        equality,
        sides: [lo, hi],
        guards: [glo, ghi],
        clause,
    } = plan;
    Some(format!(
        "(step {id}.eq (cl (or {equality} (not {lo}) (not {hi}))) :rule la_disequality)\n\
         (step {id}.flat (cl {equality} (not {lo}) (not {hi})) :rule or :premises ({id}.eq))\n\
         (step {id}.lo (cl {lo} {glo}) :rule la_generic :args (1 1))\n\
         (step {id}.hi (cl {hi} {ghi}) :rule la_generic :args (1 1))\n\
         (step {id}.r (cl {equality} (not {hi}) {glo}) :rule resolution :premises ({id}.flat {id}.lo))\n\
         (step {id} {clause} :rule resolution :premises ({id}.r {id}.hi))"
    ))
}

fn plan(
    printer: &AlethePrinter<'_>,
    clause: &[TermId],
    kind: &ay_core::TheoryLemmaKind,
) -> Option<Plan> {
    if printer.work_budget_exhausted()
        || clause.len() != 3
        || !matches!(kind, ay_core::TheoryLemmaKind::IntGuardedSplitGap)
        || !ay_core::proof_validation::recognize_int_guarded_split_gap(printer.terms, clause)
    {
        return None;
    }
    let mut equality_index = None;
    for (index, &literal) in clause.iter().enumerate() {
        match printer.terms.get(literal) {
            TermData::App(op, args)
                if op.name() == "="
                    && args.len() == 2
                    && args
                        .iter()
                        .all(|&arg| *printer.terms.sort(arg) == Sort::Int) =>
            {
                if equality_index.replace(index).is_some() {
                    return None;
                }
            }
            TermData::Not(inner) => match printer.terms.get(*inner) {
                TermData::App(op, args)
                    if matches!(op.name(), "<" | "<=" | ">" | ">=")
                        && args.len() == 2
                        && args
                            .iter()
                            .all(|&arg| *printer.terms.sort(arg) == Sort::Int) => {}
                _ => return None,
            },
            _ => return None,
        }
    }
    let equality_index = equality_index?;
    let printed = printer.format_clause(clause);
    let literals = split_application(&printed, "cl")?;
    if literals.len() != 3 {
        return None;
    }
    let equality = literals[equality_index].clone();
    let [left, right]: [String; 2] = split_application(&equality, "=")?.try_into().ok()?;
    let sides = [
        format!("(<= {left} {right})"),
        format!("(<= {right} {left})"),
    ];
    let guards: Vec<_> = literals
        .into_iter()
        .enumerate()
        .filter_map(|(index, literal)| (index != equality_index).then_some(literal))
        .collect();
    for order in [[0, 1], [1, 0]] {
        if (0..2).all(|i| printed_la_generic_holds(&[&sides[i], &guards[order[i]]], &["1", "1"])) {
            return Some(Plan {
                equality,
                sides,
                guards: [guards[order[0]].clone(), guards[order[1]].clone()],
                clause: printed,
            });
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(sort: Sort, upper: i64, reversed: bool) -> (TermStore, ProofStep, TermId) {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", sort);
        let two = terms.mk_int(BigInt::from(2));
        let upper = terms.mk_int(BigInt::from(upper));
        let mut app = |op: &str, args: &[TermId]| terms.mk_app(Symbol::named(op), args, Sort::Bool);
        let equality = app("=", &[two, x]);
        let lower = app("<=", &[two, x]);
        let high = app("<", &[x, upper]);
        let low = terms.mk_not_raw(lower);
        let high_not = terms.mk_not_raw(high);
        let clause = if reversed {
            vec![high_not, low, equality]
        } else {
            vec![equality, low, high_not]
        };
        (
            terms,
            ProofStep::TheoryLemma {
                theory: "LIA".into(),
                clause,
                farkas: None,
                kind: ay_core::TheoryLemmaKind::IntGuardedSplitGap,
                lia: None,
            },
            high,
        )
    }

    #[test]
    fn singleton_interval_uses_checked_integer_bounds_in_either_clause_order() {
        for reversed in [false, true] {
            let (terms, step, _) = fixture(Sort::Int, 3, reversed);
            crate::checker::validate_step(&terms, &mut Vec::new(), ProofId(0), &step, true, None)
                .expect("actual native guarded split theorem");
            assert!(lia_lattice_lowering_supported(&terms, &step, None));
            let text = AlethePrinter::new(&terms)
                .format_step(&step, ProofId(9))
                .expect("render");
            assert!(!text.contains(":rule hole"), "{text}");
            assert!(text.contains(":rule la_disequality"));
            let commands =
                la_generic_surface::printed_arith_commands(&text).expect("read emitted arithmetic");
            assert_eq!(commands.len(), 2);
            for command in commands {
                match command {
                    la_generic_surface::PrintedArithCommand::LaGeneric(command) => {
                        assert!(printed_la_generic_holds(&command.literals, &command.args));
                    }
                    _ => panic!("unexpected arithmetic"),
                }
            }
        }
    }

    #[test]
    fn nonsingleton_or_noninteger_interval_cannot_gain_an_equality() {
        for (sort, upper) in [(Sort::Int, 4), (Sort::Real, 3)] {
            let (terms, step, _) = fixture(sort, upper, false);
            assert!(!lia_lattice_lowering_supported(&terms, &step, None));
            let text = AlethePrinter::new(&terms)
                .format_step(&step, ProofId(9))
                .expect("render");
            assert!(text.contains(":rule hole"), "{text}");
        }
    }

    #[test]
    fn changed_printed_bound_is_refused_by_screen_and_renderer() {
        let (terms, step, high) = fixture(Sort::Int, 3, false);
        let mut overrides = HashMap::default();
        overrides.insert(high, "(< x 4)".to_string());
        assert!(!lia_lattice_lowering_supported(
            &terms,
            &step,
            Some(&overrides)
        ));
        let printer =
            AlethePrinter::new_with_overrides_and_budget(&terms, Some(&overrides), Some(MAX_WORK));
        let ProofStep::TheoryLemma { clause, kind, .. } = &step else {
            unreachable!()
        };
        assert!(render(&printer, ProofId(9), clause, kind).is_none());
        let stopped = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(0));
        assert!(render(&stopped, ProofId(9), clause, kind).is_none());
    }
}
