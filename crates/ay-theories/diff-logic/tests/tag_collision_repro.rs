use ay_diff_logic::{AssertOutcome, IncrementalDiffGraph, RStar};
use num_rational::BigRational;

fn q(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}

/// Two edges sharing ONE tag (exactly what `x - y = c` lowers to) and a cycle
/// that uses the SECOND of them. The engine's self-certification looked the tag
/// up with `edges.iter().find(|e| e.tag == t)`, which returns the FIRST edge, so
/// it summed the wrong weight.
#[test]
fn equality_style_shared_tag_cycle() {
    let mut g: IncrementalDiffGraph<RStar> = IncrementalDiffGraph::new(3);
    // Atom `x - y = 3` under tag 0: edges y->x : 3 and x->y : -3.
    let e_pos = g.register_edge(1, 2, RStar::finite(q(3)), 0);
    let e_neg = g.register_edge(2, 1, RStar::finite(q(-3)), 0);
    // Atom `x - y < 3` under tag 1: edge y->x : (3, -1).
    let e_lt = g.register_edge(1, 2, RStar::new(q(3), -1), 1);

    assert_eq!(g.assert_edge(e_pos), AssertOutcome::Consistent);
    assert_eq!(g.assert_edge(e_neg), AssertOutcome::Consistent);
    // x - y = 3 AND x - y < 3 is UNSAT: cycle e_lt (y->x, 3-eps) + e_neg (x->y, -3)
    // has weight (0, -1) < 0.
    match g.assert_edge(e_lt) {
        AssertOutcome::Conflict(tags) => {
            assert!(!tags.is_empty());
            assert!(tags.contains(&0) && tags.contains(&1), "tags: {tags:?}");
        }
        AssertOutcome::Consistent => panic!("missed the negative cycle"),
    }
}
