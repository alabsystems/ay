// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn packed_aggregate_original_compiler_queries_export_complete_derivations() {
    for (name, problem) in [
        (
            "scalar-pair",
            include_str!("fixtures/aggregate_scalar_pair.smt2"),
        ),
        ("hfa", include_str!("fixtures/aggregate_hfa.smt2")),
    ] {
        let mut context = ay_frontend::Context::new();
        for command in ay_frontend::parse(problem).expect("original query") {
            context.process_command(&command).expect("elaboration");
        }
        assert_eq!(context.assertions.len(), 1);
        let parsed = context.assertions_parsed()[0].clone();
        let root = raw_fixture_term(&mut context, &parsed);
        let TermData::Not(equality) = context.terms.get(root) else {
            panic!("negated equality")
        };
        let printer = AlethePrinter::new(&context.terms);
        let TermData::App(_, sides) = context.terms.get(*equality) else {
            panic!("equality")
        };
        let mut diagnostic = PackedProof::new(&printer, ProofId(7)).expect("prefix");
        let left = diagnostic.vector(sides[0], 0);
        let right = diagnostic.vector(sides[1], 0);
        println!(
            "{name}: left={} right={} bytes={} nodes={} spellings={}",
            left.is_some(),
            right.is_some(),
            diagnostic.out.len() + diagnostic.definitions.len(),
            diagnostic.visited,
            diagnostic.spellings.len()
        );
        let steps = printer
            .format_bv_packed_identity(ProofId(7), &[*equality])
            .expect(name);
        assert!(!steps.contains(":rule hole") && !steps.contains(":rule trust"));
        let proof = format!(
            "(assume a {})\n{steps}(step done (cl) :rule resolution :premises (a t7))\n",
            printer.format_term(root)
        );
        let certificate = serde_json::json!({"type":"alethe_certificate", "version":"1.0", "problem":problem, "proof":proof});
        let path = std::env::temp_dir().join(format!(
            "ay-packed-aggregate-{}-{name}.json",
            std::process::id()
        ));
        std::fs::write(&path, serde_json::to_vec(&certificate).expect("JSON"))
            .expect("certificate");
        println!("independent replay certificate: {}", path.display());
    }
}

// The ordinary frontend folds shifts and constant additions. This fixture
// builder keeps the captured syntax: an independently checked certificate
// must match the unchanged compiler assertion, including those operations.
pub(super) fn raw_fixture_term(
    context: &mut ay_frontend::Context,
    term: &ay_frontend::Term,
) -> TermId {
    use ay_frontend::{QualifiedIdentifier, Term};
    let inferred = context
        .elaborate_surface_subterm(term)
        .expect("well-sorted fixture");
    let sort = context.terms.sort(inferred).clone();
    let (symbol, args) = match term {
        Term::Const(_) | Term::Symbol(_) => return inferred,
        Term::IndexedApp(_, _, args) if args.is_empty() => return inferred,
        Term::App(name, args) => (Symbol::named(name), args),
        Term::IndexedApp(name, indices, args) => (
            Symbol::indexed(
                name,
                indices
                    .iter()
                    .map(|i| i.as_numeral().expect("numeral").parse().expect("u32"))
                    .collect(),
            ),
            args,
        ),
        Term::QualifiedApp(QualifiedIdentifier::Symbol(name), _, args) if name == "const" => {
            (Symbol::named("const-array"), args)
        }
        _ => panic!("outside captured fixture grammar"),
    };
    let args: Vec<_> = args
        .iter()
        .map(|arg| raw_fixture_term(context, arg))
        .collect();
    if symbol.name() == "not" {
        assert_eq!(args.len(), 1);
        context.terms.mk_not_raw(args[0])
    } else if symbol.name() == "ite" {
        assert_eq!(args.len(), 3);
        context.terms.mk_ite_raw(args[0], args[1], args[2])
    } else {
        context.terms.mk_app(symbol, args, sort)
    }
}
