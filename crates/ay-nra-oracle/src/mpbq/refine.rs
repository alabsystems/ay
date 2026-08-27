// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Isolating-interval refinement checks.

use super::*;

mod exact;
mod narrowed;

/// Whether a reference root supplied a usable enclosure.
pub(super) enum RootCheck {
    Unusable,
    Matched(u64),
}

pub(super) struct RefineCase<'a> {
    z3: &'a Z3,
    g: &'a GenBq,
    roots: &'a [Ast],
}

pub(super) fn z3_roots_inside(z3: &Z3, roots: &[Ast], lo: Ast, hi: Ast) -> Option<Vec<usize>> {
    let mut inside = Vec::new();
    for (index, root) in roots.iter().copied().enumerate() {
        if z3.lt(lo, root)? && z3.lt(root, hi)? {
            inside.push(index);
        }
    }
    Some(inside)
}

/// Refine every usable z3 root enclosure and validate the returned certificate.
pub(crate) fn check_refine(z3: &Z3, g: &GenBq, sab: Sabotage) -> Outcome {
    let coefficients = g
        .poly
        .iter()
        .cloned()
        .map(BigRational::from)
        .collect::<Vec<_>>();
    let Some(roots) = z3.roots(&coefficients) else {
        return Outcome::Skipped("z3 declined to isolate roots");
    };
    if roots.is_empty() {
        return Outcome::Skipped("no real roots");
    }
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(&mut comparisons, check_arbitrary_step_bound(g)) {
        return outcome;
    }
    let case = RefineCase {
        z3,
        g,
        roots: &roots,
    };
    let mut ran = false;
    for (index, root) in roots.iter().copied().enumerate() {
        let Some((lo, hi)) = z3.bracket(root, 40) else {
            continue;
        };
        let result = if lo == hi {
            exact::check_exact_root(&case, index, root, &lo)
        } else {
            narrowed::check_narrowed_root(&case, sab, index, root, &lo, &hi)
        };
        match result {
            Ok(RootCheck::Unusable) => {}
            Ok(RootCheck::Matched(n)) => {
                ran = true;
                comparisons += n;
            }
            Err(outcome) => return outcome,
        }
    }
    if !ran {
        return Outcome::Skipped("no usable isolating enclosure");
    }
    Outcome::Match(comparisons)
}

fn check_arbitrary_step_bound(g: &GenBq) -> Outcome {
    let a = OBq::new(g.x.0.clone(), g.x.1);
    let b = OBq::new(g.y.0.clone(), g.y.1);
    let (wide, narrow) = if a.cmp_bq(&b) == Ordering::Greater {
        (a, b)
    } else {
        (b, a)
    };
    if narrow.sign() <= 0 || wide.cmp_bq(&narrow) != Ordering::Greater {
        return Outcome::Match(0);
    }
    let Some(bound) = obq_refine_step_bound(&wide, &narrow) else {
        return Outcome::Match(0);
    };
    match wide.div_two_pow(bound) {
        Some(shrunk) if shrunk.cmp_bq(&narrow) != Ordering::Greater => Outcome::Match(1),
        _ => Divergence::outcome(
            "bq-refine",
            "identity",
            format!("step bound {bound} is insufficient: width/2^{bound} still exceeds target"),
            vec![
                ("width".into(), render_bq(&wide)),
                ("target".into(), render_bq(&narrow)),
            ],
        ),
    }
}
