/// Parse `assertion` over `script` and return the context, its canonical
/// root and the authored syntax.
#[cfg(test)]
fn elaborated_root(script: &str, assertion: &str) -> (Context, TermId, FrontendTerm) {
    let mut ctx = Context::new();
    for command in ay_frontend::parse(script).expect("parse") {
        ctx.process_command(&command).expect("declare");
    }
    let commands = ay_frontend::parse(&format!("(assert {assertion})")).expect("parse");
    let [ay_frontend::Command::Assert(authored)] = commands.as_slice() else {
        panic!("one assertion expected");
    };
    let canonical = ctx
        .elaborate_surface_subterm(authored)
        .expect("assertion elaborates");
    (ctx, canonical, authored.clone())
}

/// #iff-split-implied-authority: the universal of an authored `(= q F)` /
/// `(=> q F)` is paired with its canonical quantifier, and collecting it as
/// a quantified root spells it as written (binder `v`, `>`) together with its
/// canonicalized body atom — what the restoration pass installs beside the
/// root's own spelling. The ordinary plan still declines the whole root (a
/// binder below a non-quantifier root), so nothing else changes.
#[test]
fn a_universal_under_a_boolean_equality_or_implication_keeps_its_authored_spelling() {
    let declarations = "(declare-const p Bool) (declare-const q Bool)";
    let universal = "(forall ((v Int)) (> (+ (* v (ite p 0 2)) v) (- 2)))";
    for root in [
        format!("(= q {universal})"),
        format!("(= {universal} q)"),
        format!("(=> q {universal})"),
    ] {
        let (mut ctx, canonical, authored) = elaborated_root(declarations, &root);
        assert!(
            surface_override_collection_work(&ctx.terms, canonical).is_none(),
            "{root}: the ordinary plan's bound is unchanged"
        );
        let (quantifier, parsed) = connective_quantifier_pair(&ctx.terms, canonical, &authored)
            .unwrap_or_else(|| panic!("{root}: the universal operand pairs"));
        assert!(matches!(ctx.terms.get(quantifier), TermData::Forall(..)));
        let parsed = parsed.clone();
        let mut overrides = HashMap::default();
        assert!(collect_surface_term_overrides(
            &mut ctx,
            quantifier,
            &parsed,
            &mut overrides
        ));
        assert_eq!(
            overrides.get(&quantifier).map(String::as_str),
            Some(universal),
            "{root}: the universal keeps its authored spelling: {overrides:?}"
        );
        assert!(
            overrides
                .values()
                .any(|spelling| spelling == "(> (+ (* v (ite p 0 2)) v) (- 2))"),
            "{root}: the canonicalized body atom keeps its authored spelling: {overrides:?}"
        );
    }
}

/// Only one direct quantified operand is paired: two cannot be told apart,
/// and a quantifier below the operand is not this shape.
#[test]
fn only_one_direct_quantified_operand_is_paired() {
    for (assertion, paired) in [
        ("(= q (forall ((v Int)) (> v 0)))", true),
        ("(=> q (exists ((v Int)) (> v 0)))", true),
        (
            "(= (forall ((u Int)) (> u 1)) (forall ((v Int)) (> v 0)))",
            false,
        ),
        ("(= q (and q (forall ((v Int)) (> v 0))))", false),
        ("(and q (forall ((v Int)) (> v 0)))", false),
    ] {
        let (ctx, canonical, authored) = elaborated_root("(declare-const q Bool)", assertion);
        assert_eq!(
            connective_quantifier_pair(&ctx.terms, canonical, &authored).is_some(),
            paired,
            "{assertion}"
        );
    }
}
