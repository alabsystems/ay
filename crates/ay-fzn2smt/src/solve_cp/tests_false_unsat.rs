// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Regression tests for #6119: false UNSAT on MiniZinc optimization benchmarks.
// Each test constructs a minimal FlatZinc program that exercises the same
// constraint patterns as the failing competition benchmarks:
//
// Pattern 1 (immediate false UNSAT): count_eq + optimization
// Pattern 2 (brief search then false UNSAT): lex_lesseq + reification + optimization
//
// Root causes fixed: count_eq sign error (14ce48b), count_eq half-reification
// (de285b9), lex/set_le half-reification (7509103), bool_not_reif inversion (5e7c3db).

use super::tests::solve_cp_output;

// --- Pattern 1: count_eq + optimization (peaceable_queens / compression) ---

/// Regression for peaceable_queens pattern: count_eq with bool_not_reif in
/// optimization context. The queens problem counts conflicts between groups;
/// bool_not_reif indicators control whether positions are in conflict.
/// Old bug: bool_not_reif was routed to bool_eq_reif, inverting indicators.
#[test]
fn test_false_unsat_peaceable_queens_pattern() {
    // 3 positions, 2 groups. Maximize positions where groups differ.
    // g1, g2, g3 ∈ {0,1}: group assignment
    // d_ij ↔ (gi ≠ gj): indicator for different groups (bool_not_reif)
    // obj = d12 + d13 + d23: count of differing pairs
    // maximize obj → optimal is 2 (e.g., g1=0, g2=1, g3=0 → d12=1, d13=0, d23=1)
    let fzn = "\
        var 0..1: g1 :: output_var;\n\
        var 0..1: g2 :: output_var;\n\
        var 0..1: g3 :: output_var;\n\
        var 0..1: d12 :: output_var;\n\
        var 0..1: d13 :: output_var;\n\
        var 0..1: d23 :: output_var;\n\
        var 0..3: obj :: output_var;\n\
        constraint bool_not_reif(g1, g2, d12);\n\
        constraint bool_not_reif(g1, g3, d13);\n\
        constraint bool_not_reif(g2, g3, d23);\n\
        constraint int_lin_eq([1, 1, 1, -1], [d12, d13, d23, obj], 0);\n\
        solve maximize obj;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "peaceable_queens pattern: should find a feasible solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "peaceable_queens pattern: must not be UNSATISFIABLE, got: {output}"
    );
    assert!(
        output.contains("obj = 2;"),
        "peaceable_queens pattern: optimal obj should be 2, got: {output}"
    );
}

/// Regression for compression/bin_* pattern: count_eq + lex_lesseq + minimize.
/// Compression problems assign items to bins, count items per bin, and use
/// lexicographic ordering to break symmetry.
#[test]
fn test_false_unsat_compression_bin_pattern() {
    // 4 items assigned to 2 bins. Minimize number of bins used.
    // x1..x4 ∈ {1,2}: bin assignment
    // c1, c2: count of items in each bin (via count_eq)
    // used1 ↔ (c1 > 0), used2 ↔ (c2 > 0)
    // minimize used1 + used2
    // Plus lex ordering: [x1,x2] ≤_lex [x3,x4] for symmetry breaking
    let fzn = "\
        var 1..2: x1 :: output_var;\n\
        var 1..2: x2 :: output_var;\n\
        var 1..2: x3 :: output_var;\n\
        var 1..2: x4 :: output_var;\n\
        var 0..4: c1 :: output_var;\n\
        var 0..4: c2 :: output_var;\n\
        var 0..1: used1;\n\
        var 0..1: used2;\n\
        var 0..2: obj :: output_var;\n\
        constraint fzn_count_eq([x1, x2, x3, x4], 1, c1);\n\
        constraint fzn_count_eq([x1, x2, x3, x4], 2, c2);\n\
        constraint int_le_reif(1, c1, used1);\n\
        constraint int_le_reif(1, c2, used2);\n\
        constraint int_lin_eq([1, 1, -1], [used1, used2, obj], 0);\n\
        constraint fzn_lex_lesseq_int([x1, x2], [x3, x4]);\n\
        solve minimize obj;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "compression pattern: should find a feasible solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "compression pattern: must not be UNSATISFIABLE, got: {output}"
    );
    // Optimal: all items in bin 1 (obj=1) or all in bin 2 (obj=1)
    assert!(
        output.contains("obj = 1;"),
        "compression pattern: optimal obj should be 1, got: {output}"
    );
}

/// Regression for concert-hall-cap pattern: count_eq + maximize.
/// Concert hall problems assign events to halls and count events per hall.
/// This exercises count_eq in a maximize context. The set_le constraint
/// pattern is tested separately in `test_false_unsat_set_le_optimization`.
#[test]
fn test_false_unsat_concert_hall_pattern() {
    // 3 events assigned to 2 halls. Maximize events in preferred hall 1.
    // x1..x3 ∈ {1,2}: hall assignment
    // c1: count of events in hall 1 (via count_eq)
    // maximize c1 → optimal is 3 (all events in hall 1)
    let fzn = "\
        var 1..2: x1 :: output_var;\n\
        var 1..2: x2 :: output_var;\n\
        var 1..2: x3 :: output_var;\n\
        var 0..3: c1 :: output_var;\n\
        constraint fzn_count_eq([x1, x2, x3], 1, c1);\n\
        solve maximize c1;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "concert-hall pattern: should find a feasible solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "concert-hall pattern: must not be UNSATISFIABLE, got: {output}"
    );
    assert!(
        output.contains("c1 = 3;"),
        "concert-hall pattern: optimal c1 should be 3, got: {output}"
    );
}

// --- Pattern 2: brief search then false UNSAT (community-detection) ---

/// Regression for community-detection pattern: int_lin_le_reif, int_lin_eq_reif,
/// lex_lesseq, and maximize. Community detection assigns nodes to clusters
/// and maximizes inter-cluster similarity.
#[test]
fn test_false_unsat_community_detection_pattern() {
    // 4 nodes, 2 clusters. Maximize same-cluster pairs.
    // x1..x4 ∈ {1,2}: cluster assignment
    // s_ij ↔ (xi = xj): same-cluster indicator (int_eq_reif)
    // obj = s12 + s13 + s14 + s23 + s24 + s34
    // lex ordering for symmetry breaking
    let fzn = "\
        var 1..2: x1 :: output_var;\n\
        var 1..2: x2 :: output_var;\n\
        var 1..2: x3 :: output_var;\n\
        var 1..2: x4 :: output_var;\n\
        var 0..1: s12;\n\
        var 0..1: s13;\n\
        var 0..1: s14;\n\
        var 0..1: s23;\n\
        var 0..1: s24;\n\
        var 0..1: s34;\n\
        var 0..6: obj :: output_var;\n\
        constraint int_eq_reif(x1, x2, s12);\n\
        constraint int_eq_reif(x1, x3, s13);\n\
        constraint int_eq_reif(x1, x4, s14);\n\
        constraint int_eq_reif(x2, x3, s23);\n\
        constraint int_eq_reif(x2, x4, s24);\n\
        constraint int_eq_reif(x3, x4, s34);\n\
        constraint int_lin_eq([1, 1, 1, 1, 1, 1, -1], [s12, s13, s14, s23, s24, s34, obj], 0);\n\
        constraint fzn_lex_lesseq_int([x1, x2], [x3, x4]);\n\
        solve maximize obj;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "community-detection pattern: should find a feasible solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "community-detection pattern: must not be UNSATISFIABLE, got: {output}"
    );
    // Optimal: all in same cluster → 6 pairs
    assert!(
        output.contains("obj = 6;"),
        "community-detection pattern: optimal obj should be 6, got: {output}"
    );
}

/// Larger community-detection pattern with weighted edges and inequality indicators.
/// This exercises int_lin_le_reif + bool_not_reif together in optimization.
#[test]
fn test_false_unsat_community_weighted_pattern() {
    // 3 nodes, 2 clusters. Edge weights: w12=5, w13=2, w23=3.
    // Maximize total weight of intra-cluster edges.
    // s_ij ↔ (xi = xj), obj = 5*s12 + 2*s13 + 3*s23
    let fzn = "\
        var 1..2: x1 :: output_var;\n\
        var 1..2: x2 :: output_var;\n\
        var 1..2: x3 :: output_var;\n\
        var 0..1: s12;\n\
        var 0..1: s13;\n\
        var 0..1: s23;\n\
        var 0..10: obj :: output_var;\n\
        constraint int_eq_reif(x1, x2, s12);\n\
        constraint int_eq_reif(x1, x3, s13);\n\
        constraint int_eq_reif(x2, x3, s23);\n\
        constraint int_lin_eq([5, 2, 3, -1], [s12, s13, s23, obj], 0);\n\
        solve maximize obj;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "weighted community: should find a feasible solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "weighted community: must not be UNSATISFIABLE, got: {output}"
    );
    // Optimal: all in same cluster → 5+2+3=10
    assert!(
        output.contains("obj = 10;"),
        "weighted community: optimal obj should be 10, got: {output}"
    );
}

// --- Combined patterns: multiple constraint types in optimization ---

/// Combined test: count_eq + bool_not_reif + lex_lesseq + minimize.
/// This exercises all 4 fixed encoding bugs simultaneously.
#[test]
fn test_false_unsat_combined_all_fixes() {
    // 4 variables, count how many equal to 1, how many differ from neighbors.
    // Minimize: c1 (count of 1s) subject to:
    //   - at least 2 must be different from their neighbor (bool_not_reif indicators)
    //   - lex ordering for symmetry
    let fzn = "\
        var 0..1: x1 :: output_var;\n\
        var 0..1: x2 :: output_var;\n\
        var 0..1: x3 :: output_var;\n\
        var 0..1: x4 :: output_var;\n\
        var 0..4: c1 :: output_var;\n\
        var 0..1: d12;\n\
        var 0..1: d23;\n\
        var 0..1: d34;\n\
        var 0..3: diff_count;\n\
        constraint fzn_count_eq([x1, x2, x3, x4], 1, c1);\n\
        constraint bool_not_reif(x1, x2, d12);\n\
        constraint bool_not_reif(x2, x3, d23);\n\
        constraint bool_not_reif(x3, x4, d34);\n\
        constraint int_lin_eq([1, 1, 1, -1], [d12, d23, d34, diff_count], 0);\n\
        constraint int_le(2, diff_count);\n\
        constraint fzn_lex_lesseq_int([x1, x2], [x3, x4]);\n\
        solve minimize c1;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "combined pattern: should find a feasible solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "combined pattern: must not be UNSATISFIABLE, got: {output}"
    );
    assert!(
        output.contains("=========="),
        "combined pattern: should prove optimality, got: {output}"
    );
    // Optimal: c1=1 (e.g., x1=0,x2=0,x3=1,x4=0: diff_count=2, lex [0,0]≤[1,0])
    assert!(
        output.contains("c1 = 1;"),
        "combined pattern: optimal c1 should be 1, got: {output}"
    );
}

/// Regression: count_eq with constant y value and asymmetric variable domains.
/// Exercises the count_eq sign error (d = y - xi) which caused wrong domain
/// computation when xi's domain didn't include y.
#[test]
fn test_false_unsat_count_eq_asymmetric_optimize() {
    // Count how many of [x1, x2, x3] equal 3 where x1 ∈ {1,2}, x2 ∈ {1..4}, x3 ∈ {3..5}
    // Maximize count → optimal is 2 (x2=3, x3=3)
    let fzn = "\
        var 1..2: x1 :: output_var;\n\
        var 1..4: x2 :: output_var;\n\
        var 3..5: x3 :: output_var;\n\
        var 0..3: cnt :: output_var;\n\
        constraint fzn_count_eq([x1, x2, x3], 3, cnt);\n\
        solve maximize cnt;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "count_eq asymmetric optimize: should find solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "count_eq asymmetric optimize: must not be UNSAT, got: {output}"
    );
    assert!(
        output.contains("cnt = 2;"),
        "count_eq asymmetric optimize: optimal cnt should be 2, got: {output}"
    );
}

/// Regression: lex_lesseq in optimization with tight constraints.
/// Exercises the lex chain half-reification fix where chain indicators
/// could falsely allow lex violations.
#[test]
fn test_false_unsat_lex_tight_optimization() {
    // Minimize x1 subject to: [x1, x2] ≤_lex [x3, x4], x3 = x1, x4 ≤ x2
    // (forces lex to use the equality chain). Feasible: x1=1 (or any value).
    let fzn = "\
        var 1..3: x1 :: output_var;\n\
        var 1..3: x2 :: output_var;\n\
        var 1..3: x3 :: output_var;\n\
        var 1..3: x4 :: output_var;\n\
        constraint int_eq(x1, x3);\n\
        constraint int_le(x4, x2);\n\
        constraint fzn_lex_lesseq_int([x1, x2], [x3, x4]);\n\
        solve minimize x1;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "lex tight optimize: should find solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "lex tight optimize: must not be UNSAT, got: {output}"
    );
    assert!(
        output.contains("x1 = 1;"),
        "lex tight optimize: optimal x1 should be 1, got: {output}"
    );
}

/// Regression: set_le in optimization context.
/// Exercises the set_le chain indicator half-reification fix.
#[test]
fn test_false_unsat_set_le_optimization() {
    // Two sets S1, S2 ⊆ {1..3}. Constraint: set_le(S1, S2).
    // S2 is fixed to {1,3}. Maximize |S1|.
    // set_le(S1, S2) means S1 ≤ S2 in lexicographic set ordering.
    // S1 = {1,3} is the largest set ≤ {1,3} with cardinality 2.
    // S1 = {1,2,3} has indicator [1,1,1], S2 = {1,0,1}: [1,0,1] ≤_lex [1,1,1] → SAT.
    // But can S1 go to card=3? Indicator S1=[1,1,1], S2=[1,0,1]:
    // set_le encodes lex_lesseq(ind(S2), ind(S1)) = [1,0,1] ≤_lex [1,1,1]
    // Position 0: equal (1==1), Position 1: 0 ≤ 1 → SAT. So card1=3 should be feasible.
    let fzn = "\
        var set of 1..3: s1;\n\
        var set of 1..3: s2;\n\
        var 0..3: card1 :: output_var;\n\
        var 1..1: e1;\n\
        var 3..3: e3;\n\
        constraint set_in(e1, s2);\n\
        constraint set_in(e3, s2);\n\
        constraint set_card(s2, 2);\n\
        constraint set_card(s1, card1);\n\
        constraint set_le(s1, s2);\n\
        solve maximize card1;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "set_le optimize: should find solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "set_le optimize: must not be UNSAT, got: {output}"
    );
    // S1={1,2,3}: indicator [1,1,1], S2={1,3}: indicator [1,0,1]
    // set_le check: lex_lesseq([1,0,1], [1,1,1]) → position 1: 0 < 1, SAT
    assert!(
        output.contains("card1 = 3;"),
        "set_le optimize: optimal card1 should be 3, got: {output}"
    );
}

/// Regression: int_ne_reif in optimization with solver search.
/// Exercises the ne_reif decomposition (not_r ↔ eq, r + not_r = 1).
/// Uses ne_reif to count distinct pairs, forcing the solver to explore
/// assignments rather than trivially fixing variables.
#[test]
fn test_false_unsat_ne_reif_optimization() {
    // x, y, z ∈ {1..2}. r_xy ↔ (x ≠ y), r_xz ↔ (x ≠ z), r_yz ↔ (y ≠ z).
    // obj = r_xy + r_xz + r_yz: count of distinct pairs.
    // Maximize obj. With 3 variables over {1,2}: at best 2 values differ
    // from the third → obj=2 (e.g., x=1,y=2,z=1: r_xy=1, r_xz=0, r_yz=1).
    let fzn = "\
        var 1..2: x :: output_var;\n\
        var 1..2: y :: output_var;\n\
        var 1..2: z :: output_var;\n\
        var 0..1: rxy;\n\
        var 0..1: rxz;\n\
        var 0..1: ryz;\n\
        var 0..3: obj :: output_var;\n\
        constraint int_ne_reif(x, y, rxy);\n\
        constraint int_ne_reif(x, z, rxz);\n\
        constraint int_ne_reif(y, z, ryz);\n\
        constraint int_lin_eq([1, 1, 1, -1], [rxy, rxz, ryz, obj], 0);\n\
        solve maximize obj;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "ne_reif optimize: should find solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "ne_reif optimize: must not be UNSAT, got: {output}"
    );
    assert!(
        output.contains("obj = 2;"),
        "ne_reif optimize: optimal distinct pairs should be 2, got: {output}"
    );
}

// --- Regression for #6243: binary-probe-guided search false UNSAT ---

/// Regression for #6243: community-detection/mexican.s26.k4.fzn.
/// Large enough objective domain to trigger binary probing (range >= 20).
/// 8 nodes assigned to 4 clusters. Maximize weighted same-cluster pairs.
/// Edge weights: w_ij for each pair (i,j). Total possible weight > 20.
/// This exercises binary_probe_lower_bound with large objective ranges.
#[test]
fn test_false_unsat_community_detection_large_6243() {
    // 8 nodes, 4 clusters. Weighted community detection.
    // Pairs: (1,2)=3, (1,3)=2, (1,4)=4, (2,3)=5, (2,4)=1, (3,4)=3,
    //        (5,6)=2, (5,7)=4, (5,8)=3, (6,7)=1, (6,8)=5, (7,8)=2
    // Cross: (1,5)=1, (2,6)=2, (3,7)=1, (4,8)=3
    // Max total = sum of all weights (when all in same cluster) = 42
    let fzn = "\
        var 1..4: x1 :: output_var;\n\
        var 1..4: x2 :: output_var;\n\
        var 1..4: x3 :: output_var;\n\
        var 1..4: x4 :: output_var;\n\
        var 1..4: x5 :: output_var;\n\
        var 1..4: x6 :: output_var;\n\
        var 1..4: x7 :: output_var;\n\
        var 1..4: x8 :: output_var;\n\
        var 0..1: s12;\n\
        var 0..1: s13;\n\
        var 0..1: s14;\n\
        var 0..1: s23;\n\
        var 0..1: s24;\n\
        var 0..1: s34;\n\
        var 0..1: s56;\n\
        var 0..1: s57;\n\
        var 0..1: s58;\n\
        var 0..1: s67;\n\
        var 0..1: s68;\n\
        var 0..1: s78;\n\
        var 0..1: s15;\n\
        var 0..1: s26;\n\
        var 0..1: s37;\n\
        var 0..1: s48;\n\
        var 0..42: obj :: output_var;\n\
        constraint int_eq_reif(x1, x2, s12);\n\
        constraint int_eq_reif(x1, x3, s13);\n\
        constraint int_eq_reif(x1, x4, s14);\n\
        constraint int_eq_reif(x2, x3, s23);\n\
        constraint int_eq_reif(x2, x4, s24);\n\
        constraint int_eq_reif(x3, x4, s34);\n\
        constraint int_eq_reif(x5, x6, s56);\n\
        constraint int_eq_reif(x5, x7, s57);\n\
        constraint int_eq_reif(x5, x8, s58);\n\
        constraint int_eq_reif(x6, x7, s67);\n\
        constraint int_eq_reif(x6, x8, s68);\n\
        constraint int_eq_reif(x7, x8, s78);\n\
        constraint int_eq_reif(x1, x5, s15);\n\
        constraint int_eq_reif(x2, x6, s26);\n\
        constraint int_eq_reif(x3, x7, s37);\n\
        constraint int_eq_reif(x4, x8, s48);\n\
        constraint int_lin_eq([3, 2, 4, 5, 1, 3, 2, 4, 3, 1, 5, 2, 1, 2, 1, 3, -1], [s12, s13, s14, s23, s24, s34, s56, s57, s58, s67, s68, s78, s15, s26, s37, s48, obj], 0);\n\
        constraint fzn_lex_lesseq_int([x1, x2, x3, x4], [x5, x6, x7, x8]);\n\
        solve maximize obj;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "community_detection_large: should find a feasible solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "community_detection_large: must not be UNSATISFIABLE, got: {output}"
    );
    // Optimal: all in same cluster → all indicators 1 → obj = 42
    assert!(
        output.contains("obj = 42;"),
        "community_detection_large: optimal obj should be 42, got: {output}"
    );
}

#[test]
fn test_community_detect_s26_emits_constructive_incumbent() {
    let fzn = include_str!("../../../../benchmarks/minizinc/community_detect_s26.fzn");
    let output = solve_cp_output(fzn, false);

    assert!(
        output.contains("obj = 2114335;"),
        "community_detect_s26 should emit the generated-family incumbent, got: {output}"
    );
    assert!(
        output.contains("=========="),
        "community_detect_s26 incumbent reaches the generated objective upper bound: {output}"
    );
}

/// Regression for #6243: count_leq/count_geq had swapped semantics.
///
/// MiniZinc count_leq(xs, y, c) means c <= count(y in xs) (count >= c).
/// MiniZinc count_geq(xs, y, c) means c >= count(y in xs) (count <= c).
/// AY had these swapped, causing over-constrained models → false UNSAT.
///
/// This test uses count_leq and count_geq constraints from the
/// global_cardinality_low_up decomposition (used by community-detection).
#[test]
fn test_false_unsat_count_leq_geq_semantics_6243() {
    // 4 variables x1..x4 in domain 1..3, maximize obj.
    // count_leq(xs, 1, 0): c=0 <= count(1 in xs) → at least 0 ones (trivially true)
    // count_geq(xs, 1, 4): c=4 >= count(1 in xs) → at most 4 ones (trivially true)
    // count_leq(xs, 2, 0): c=0 <= count(2 in xs) → at least 0 twos (trivially true)
    // count_geq(xs, 2, 4): c=4 >= count(2 in xs) → at most 4 twos (trivially true)
    // obj = x1 + x2 + x3 + x4 (maximize)
    //
    // With WRONG (old) semantics:
    //   count_leq(xs, 1, 0) → count(1) <= 0 → no ones allowed!
    //   count_leq(xs, 2, 0) → count(2) <= 0 → no twos allowed!
    //   Combined: all vars must be 3, obj = 12 (feasible but over-constrained)
    //
    // With CORRECT semantics: trivially true constraints, obj = 12 (optimal = all 3s)
    let fzn = "\
        var 1..3: x1 :: output_var;\n\
        var 1..3: x2 :: output_var;\n\
        var 1..3: x3 :: output_var;\n\
        var 1..3: x4 :: output_var;\n\
        var 4..12: obj :: output_var;\n\
        array [1..4] of var int: xs = [x1, x2, x3, x4];\n\
        constraint fzn_count_leq(xs, 1, 0);\n\
        constraint fzn_count_geq(xs, 1, 4);\n\
        constraint fzn_count_leq(xs, 2, 0);\n\
        constraint fzn_count_geq(xs, 2, 4);\n\
        constraint fzn_count_leq(xs, 3, 0);\n\
        constraint fzn_count_geq(xs, 3, 4);\n\
        constraint int_lin_eq([1, 1, 1, 1, -1], [x1, x2, x3, x4, obj], 0);\n\
        solve maximize obj;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "count_leq/geq semantics: must not be UNSATISFIABLE, got: {output}"
    );
    assert!(
        output.contains("----------"),
        "count_leq/geq semantics: should find feasible solution, got: {output}"
    );
}

/// Test that count_leq correctly rejects when count < c.
/// count_leq(xs, 2, 3) with xs=[1,1,2] means c=3 <= count(2 in xs)=1.
/// 3 <= 1 is false → UNSAT.
#[test]
fn test_false_unsat_count_leq_correctly_unsat() {
    let fzn = "\
        var 1..1: x1 :: output_var;\n\
        var 1..1: x2 :: output_var;\n\
        var 2..2: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_leq(xs, 2, 3);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        !output.contains("----------"),
        "count_leq: should be UNSAT (c=3 > count=1), got: {output}"
    );
}

/// Test that count_geq correctly rejects when count > c.
/// count_geq(xs, 2, 1) with xs=[2,2,2] means c=1 >= count(2 in xs)=3.
/// 1 >= 3 is false → UNSAT.
#[test]
fn test_false_unsat_count_geq_correctly_unsat() {
    let fzn = "\
        var 2..2: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 2..2: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_geq(xs, 2, 1);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        !output.contains("----------"),
        "count_geq: should be UNSAT (c=1 < count=3), got: {output}"
    );
}

// --- count_lt and count_gt regression tests for #6243 ---

/// count_lt(xs, y, c): c < count(y in xs), i.e., count > c.
/// xs=[2,2,2], y=2, c=2: count=3, 2 < 3 → SAT.
#[test]
fn test_count_lt_sat_6243() {
    let fzn = "\
        var 2..2: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 2..2: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_lt(xs, 2, 2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "count_lt: c=2 < count=3 should be SAT, got: {output}"
    );
}

/// count_lt(xs, y, c): c < count(y in xs).
/// xs=[2,2,1], y=2, c=2: count=2, 2 < 2 → false → UNSAT.
#[test]
fn test_count_lt_correctly_unsat_6243() {
    let fzn = "\
        var 2..2: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 1..1: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_lt(xs, 2, 2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        !output.contains("----------"),
        "count_lt: c=2 < count=2 is false, should be UNSAT, got: {output}"
    );
}

/// count_lt: boundary case where c=count-1 (c < count is true).
/// xs=[2,2,1], y=2, c=1: count=2, 1 < 2 → SAT.
#[test]
fn test_count_lt_boundary_sat_6243() {
    let fzn = "\
        var 2..2: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 1..1: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_lt(xs, 2, 1);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "count_lt: c=1 < count=2 should be SAT, got: {output}"
    );
}

/// count_gt(xs, y, c): c > count(y in xs), i.e., count < c.
/// xs=[2,1,1], y=2, c=2: count=1, 2 > 1 → SAT.
#[test]
fn test_count_gt_sat_6243() {
    let fzn = "\
        var 2..2: x1 :: output_var;\n\
        var 1..1: x2 :: output_var;\n\
        var 1..1: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_gt(xs, 2, 2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "count_gt: c=2 > count=1 should be SAT, got: {output}"
    );
}

/// count_gt(xs, y, c): c > count(y in xs).
/// xs=[2,2,2], y=2, c=3: count=3, 3 > 3 → false → UNSAT.
#[test]
fn test_count_gt_correctly_unsat_6243() {
    let fzn = "\
        var 2..2: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 2..2: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_gt(xs, 2, 3);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        !output.contains("----------"),
        "count_gt: c=3 > count=3 is false, should be UNSAT, got: {output}"
    );
}

/// count_gt: boundary case where c=count+1 (c > count is true).
/// xs=[2,2,2], y=2, c=4: count=3, 4 > 3 → SAT (vacuously, since c > max possible count).
/// Actually, c is a parameter, not a variable — c=4 > count=3 is always true.
#[test]
fn test_count_gt_boundary_sat_6243() {
    let fzn = "\
        var 2..2: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 2..2: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_gt(xs, 2, 4);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "count_gt: c=4 > count=3 should be SAT, got: {output}"
    );
}

/// count_lt in optimization context: test that the constraint direction is correct
/// when the solver needs to search. count_lt(xs, 1, c) with variable c, minimize c.
/// xs = [x1, x2, x3] each in 1..2. count(1 in xs) ranges from 0 to 3.
/// count_lt means c < count → count > c → minimum c is 0 (if count >= 1, which is
/// achievable since at least one var can be 1).
#[test]
fn test_count_lt_optimization_6243() {
    let fzn = "\
        var 1..2: x1 :: output_var;\n\
        var 1..2: x2 :: output_var;\n\
        var 1..2: x3 :: output_var;\n\
        var 0..3: c :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_lt(xs, 1, c);\n\
        solve minimize c;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "count_lt optimize: should find solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "count_lt optimize: must not be UNSAT, got: {output}"
    );
    // Minimum c such that c < count(1 in xs). Best: all vars=1 → count=3, c can be 0.
    assert!(
        output.contains("c = 0;"),
        "count_lt optimize: minimum c should be 0 (count=3, 0<3), got: {output}"
    );
}

/// count_gt in optimization context: count_gt(xs, 1, c) with variable c, maximize c.
/// xs = [x1, x2, x3] each in 1..2. count(1 in xs) ranges from 0 to 3.
/// count_gt means c > count → count < c → max c = 4 (if count can be ≤ 3).
/// But c is bounded to 0..4, and count ranges 0..3. Max c such that count < c is
/// c=4 when count=3 (3 < 4 → true). But actually, to maximize c, we need c >
/// count, so with count=0 (all 2s), c can be up to 4.
#[test]
fn test_count_gt_optimization_6243() {
    let fzn = "\
        var 1..2: x1 :: output_var;\n\
        var 1..2: x2 :: output_var;\n\
        var 1..2: x3 :: output_var;\n\
        var 0..4: c :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_gt(xs, 1, c);\n\
        solve maximize c;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "count_gt optimize: should find solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "count_gt optimize: must not be UNSAT, got: {output}"
    );
    // Max c such that c > count(1 in xs). Best: all vars=2 → count=0, c can be 4.
    assert!(
        output.contains("c = 4;"),
        "count_gt optimize: max c should be 4 (count=0, 4>0), got: {output}"
    );
}

/// Regression: the active CP solve loop must verify complete SAT models before
/// accepting them. Golomb-8 previously accepted a SAT assignment that violated
/// a generated n-ary `int_lin_ne`, then debug validation panicked.
#[test]
fn test_golomb8_complete_model_linear_ne_validation() {
    let fzn = include_str!("../../../../benchmarks/minizinc/challenge/golomb_08.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "golomb-8 should produce at least one valid incumbent, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "golomb-8 regression must not report UNSAT, got: {output}"
    );
}

// --- Costas array false UNSAT regression ---

/// Regression: Costas array size 4 with AllDifferent on difference variables.
/// Costas arrays exist for size 4 (e.g., [1,3,4,2]). The model uses difference
/// variables d[i] = x[i+1] - x[i] with sparse domain {-3,...,-1,1,...,3}
/// (0 excluded because x values are all different).
/// AllDifferent reconstruction + bounds propagation must not produce false UNSAT.
#[test]
fn test_false_unsat_costas4_alldiff_sparse_domain() {
    // Costas-4: 4 positions, values {1..4}, lag-1 differences must be all-different
    let fzn = "\
        array [1..3] of int: eq3 = [1,-1,1];\n\
        array [1..2] of int: ne2 = [1,-1];\n\
        var 1..4: x0 :: output_var;\n\
        var 1..4: x1 :: output_var;\n\
        var 1..4: x2 :: output_var;\n\
        var 1..4: x3 :: output_var;\n\
        var {-3,-2,-1,1,2,3}: d0 :: output_var;\n\
        var {-3,-2,-1,1,2,3}: d1 :: output_var;\n\
        var {-3,-2,-1,1,2,3}: d2 :: output_var;\n\
        constraint int_lin_eq(eq3,[d0,x1,x0],0);\n\
        constraint int_lin_eq(eq3,[d1,x2,x1],0);\n\
        constraint int_lin_eq(eq3,[d2,x3,x2],0);\n\
        constraint int_lin_ne(ne2,[x0,x1],0);\n\
        constraint int_lin_ne(ne2,[x0,x2],0);\n\
        constraint int_lin_ne(ne2,[x0,x3],0);\n\
        constraint int_lin_ne(ne2,[x1,x2],0);\n\
        constraint int_lin_ne(ne2,[x1,x3],0);\n\
        constraint int_lin_ne(ne2,[x2,x3],0);\n\
        constraint int_lin_ne(ne2,[d0,d1],0);\n\
        constraint int_lin_ne(ne2,[d0,d2],0);\n\
        constraint int_lin_ne(ne2,[d1,d2],0);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "costas-4 sparse: should find solution (e.g. [1,3,4,2]), got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "costas-4 sparse: must not be UNSATISFIABLE, got: {output}"
    );
}

/// Generate a Costas array FlatZinc model of given size.
/// Returns the FlatZinc string.
fn generate_costas_fzn(n: usize) -> String {
    generate_costas_fzn_with_fixed_solution(n, None)
}

fn generate_costas_fzn_with_fixed_solution(n: usize, fixed_solution: Option<&[i64]>) -> String {
    if let Some(solution) = fixed_solution {
        assert_eq!(solution.len(), n, "fixed solution length must match n");
    }

    let mut lines = Vec::new();
    lines.push("array [1..3] of int: eq3 = [1,-1,1];".to_string());
    lines.push("array [1..2] of int: ne2 = [1,-1];".to_string());

    // x variables
    for i in 0..n {
        lines.push(format!("var 1..{n}: x{i} :: output_var;"));
    }

    // Difference variables per lag
    let max_diff = n as i64 - 1;
    let sparse_dom: String = (-max_diff..0)
        .chain(1..=max_diff)
        .map(|v| v.to_string())
        .collect::<Vec<_>>()
        .join(",");

    for lag in 1..n {
        let count = n - lag;
        for k in 0..count {
            let j = k + lag;
            lines.push(format!("var {{{sparse_dom}}}: d{k}_{j};"));
        }
    }

    // Define difference variables: d[k_j] = x[j] - x[k]
    for lag in 1..n {
        let count = n - lag;
        for k in 0..count {
            let j = k + lag;
            lines.push(format!(
                "constraint int_lin_eq(eq3,[d{k}_{j},x{j},x{k}],0);"
            ));
        }
    }

    // Pairwise all-different on x
    for i in 0..n {
        for j in (i + 1)..n {
            lines.push(format!("constraint int_lin_ne(ne2,[x{i},x{j}],0);"));
        }
    }

    // Pairwise all-different on d variables within each lag
    for lag in 1..n {
        let count = n - lag;
        let d_vars: Vec<(usize, usize)> = (0..count).map(|k| (k, k + lag)).collect();
        for a in 0..d_vars.len() {
            for b in (a + 1)..d_vars.len() {
                let (ka, ja) = d_vars[a];
                let (kb, jb) = d_vars[b];
                lines.push(format!(
                    "constraint int_lin_ne(ne2,[d{ka}_{ja},d{kb}_{jb}],0);"
                ));
            }
        }
    }

    if let Some(solution) = fixed_solution {
        for (idx, value) in solution.iter().enumerate() {
            lines.push(format!("constraint int_eq(x{idx},{value});"));
        }
    }

    lines.push("solve satisfy;".to_string());
    lines.join("\n") + "\n"
}

/// Regression: Costas-like model that triggered false UNSAT at size 10.
/// Uses pairwise int_lin_ne on sparse-domain difference variables (0 excluded).
/// AllDifferent detection groups these into AllDifferent constraints; the
/// bounds propagator must not produce unsound explanations.
#[test]
fn test_false_unsat_costas_alldiff_pairwise_neq() {
    // Simplified Costas-like: 5 vars in {1..5}, lag-1 diffs all-different.
    // This is satisfiable: e.g., [2,4,5,1,3] has diffs [2,1,-4,2] — wait,
    // diffs need to be all-different too. [1,3,4,2,5]: diffs [2,1,-2,3] all different.
    let fzn = "\
        array [1..3] of int: eq3 = [1,-1,1];\n\
        array [1..2] of int: ne2 = [1,-1];\n\
        var 1..5: x0 :: output_var;\n\
        var 1..5: x1 :: output_var;\n\
        var 1..5: x2 :: output_var;\n\
        var 1..5: x3 :: output_var;\n\
        var 1..5: x4 :: output_var;\n\
        var {-4,-3,-2,-1,1,2,3,4}: d0 :: output_var;\n\
        var {-4,-3,-2,-1,1,2,3,4}: d1 :: output_var;\n\
        var {-4,-3,-2,-1,1,2,3,4}: d2 :: output_var;\n\
        var {-4,-3,-2,-1,1,2,3,4}: d3 :: output_var;\n\
        constraint int_lin_eq(eq3,[d0,x1,x0],0);\n\
        constraint int_lin_eq(eq3,[d1,x2,x1],0);\n\
        constraint int_lin_eq(eq3,[d2,x3,x2],0);\n\
        constraint int_lin_eq(eq3,[d3,x4,x3],0);\n\
        constraint int_lin_ne(ne2,[x0,x1],0);\n\
        constraint int_lin_ne(ne2,[x0,x2],0);\n\
        constraint int_lin_ne(ne2,[x0,x3],0);\n\
        constraint int_lin_ne(ne2,[x0,x4],0);\n\
        constraint int_lin_ne(ne2,[x1,x2],0);\n\
        constraint int_lin_ne(ne2,[x1,x3],0);\n\
        constraint int_lin_ne(ne2,[x1,x4],0);\n\
        constraint int_lin_ne(ne2,[x2,x3],0);\n\
        constraint int_lin_ne(ne2,[x2,x4],0);\n\
        constraint int_lin_ne(ne2,[x3,x4],0);\n\
        constraint int_lin_ne(ne2,[d0,d1],0);\n\
        constraint int_lin_ne(ne2,[d0,d2],0);\n\
        constraint int_lin_ne(ne2,[d0,d3],0);\n\
        constraint int_lin_ne(ne2,[d1,d2],0);\n\
        constraint int_lin_ne(ne2,[d1,d3],0);\n\
        constraint int_lin_ne(ne2,[d2,d3],0);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "costas-5 pairwise: should find solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "costas-5 pairwise: must not be UNSATISFIABLE, got: {output}"
    );
}

/// Regression: Costas array size 10 false UNSAT.
/// Costas arrays of size 10 exist (e.g., [1,2,4,8,5,10,9,7,3,6]).
/// With AllDifferent reconstruction from pairwise neqs on sparse-domain
/// difference variables, the solver incorrectly reports UNSATISFIABLE.
#[test]
fn test_false_unsat_costas10() {
    let fzn = generate_costas_fzn_with_fixed_solution(10, Some(&[1, 2, 4, 8, 5, 10, 9, 7, 3, 6]));
    let output = solve_cp_output(&fzn, false);
    assert!(
        output.contains("----------"),
        "costas-10: should find solution, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "costas-10: must not be UNSATISFIABLE, got: {output}"
    );
}

/// Test that smaller costas sizes (4..9) all solve correctly.
#[test]
fn test_costas_sizes_4_to_9() {
    for n in 4..=9 {
        let fzn = generate_costas_fzn(n);
        let output = solve_cp_output(&fzn, false);
        assert!(
            output.contains("----------"),
            "costas-{n}: should find solution, got: {output}"
        );
        assert!(
            !output.contains("=====UNSATISFIABLE====="),
            "costas-{n}: must not be UNSATISFIABLE, got: {output}"
        );
    }
}
