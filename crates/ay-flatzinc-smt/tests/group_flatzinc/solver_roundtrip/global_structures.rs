// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `solver_roundtrip` to preserve test FQNs.

#[test]
fn roundtrip_circuit() {
    let ay = exact_ay();
    // 3-node circuit: successors form a single Hamiltonian cycle
    let fzn = "array [1..3] of var 1..3: succ :: output_array([1..3]);\n\
               constraint fzn_circuit(succ);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let (code, stdout, stderr) = run_ay(&result.smtlib, &ay);
    assert_eq!(code, 0, "ay stderr: {stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat");

    let values = parse_get_value(lines[1]);
    let s: Vec<i64> = (1..=3)
        .map(|i| {
            values
                .get(&format!("succ_{i}"))
                .unwrap()
                .parse::<i64>()
                .expect("parse succ_i")
        })
        .collect();

    // Verify it's a permutation of {1, 2, 3}
    let mut sorted = s.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, vec![1, 2, 3], "must be a permutation: {s:?}");

    // Verify no self-loops
    for (i, &v) in s.iter().enumerate() {
        assert_ne!(v, i as i64 + 1, "self-loop at node {}: {s:?}", i + 1);
    }

    // Verify single cycle: start at node 1, follow successors, must visit all
    let mut visited = [false; 3];
    let mut current = 0usize; // 0-indexed
    for _ in 0..3 {
        assert!(
            !visited[current],
            "cycle revisits node {}: {s:?}",
            current + 1
        );
        visited[current] = true;
        current = (s[current] - 1) as usize; // follow successor (1-indexed)
    }
    assert!(visited.iter().all(|&v| v), "not all nodes visited: {s:?}");
    assert_eq!(current, 0, "cycle must return to start: {s:?}");
}

#[test]
fn roundtrip_cumulative() {
    let ay = exact_ay();
    // 2 tasks: durations [3, 2], resources [2, 3], capacity 4
    // They can't overlap since 2+3=5 > 4, so one must finish before the other starts
    let fzn = "array [1..2] of var 0..10: s :: output_array([1..2]);\n\
               array [1..2] of int: d = [3, 2];\n\
               array [1..2] of int: r = [2, 3];\n\
               int: cap = 4;\n\
               constraint fzn_cumulative(s, d, r, cap);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let (code, stdout, stderr) = run_ay(&result.smtlib, &ay);
    assert_eq!(code, 0, "ay stderr: {stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat");

    let values = parse_get_value(lines[1]);
    let s1 = parse_smt_int(values.get("s_1").unwrap());
    let s2 = parse_smt_int(values.get("s_2").unwrap());
    // Tasks don't overlap: s1+3 <= s2 OR s2+2 <= s1
    assert!(
        s1 + 3 <= s2 || s2 + 2 <= s1,
        "tasks must not overlap: s1={s1}, s2={s2}, d=[3,2], r=[2,3], cap=4"
    );
}

/// Regression test for #321: cumulative triple-overlap soundness.
///
/// 3 tasks: durations [10,10,10], resources [2,2,2], capacity 5.
/// Every PAIR fits (2+2=4 <= 5), but all three overlapping uses 6 > 5.
/// The old pairwise encoding allowed all three to overlap (unsound).
/// The event-point encoding must force at least one task to not overlap
/// with the other two.
#[test]
fn roundtrip_cumulative_triple_overlap() {
    let ay = exact_ay();
    let fzn = "array [1..3] of var 0..30: s :: output_array([1..3]);\n\
               array [1..3] of int: d = [10, 10, 10];\n\
               array [1..3] of int: r = [2, 2, 2];\n\
               int: cap = 5;\n\
               constraint fzn_cumulative(s, d, r, cap);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let (code, stdout, stderr) = run_ay(&result.smtlib, &ay);
    assert_eq!(code, 0, "ay stderr: {stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat", "should be sat (tasks can be sequenced)");

    // Parse all get-value lines (may span multiple lines for many variables)
    let value_str = lines[1..].join(" ");
    let values = parse_get_value(&value_str);
    let s1 = parse_smt_int(values.get("s_1").unwrap());
    let s2 = parse_smt_int(values.get("s_2").unwrap());
    let s3 = parse_smt_int(values.get("s_3").unwrap());
    let d = 10;

    // Verify: at no point do all 3 tasks overlap simultaneously.
    // For each task's start time, count how many tasks are active.
    for &t in &[s1, s2, s3] {
        let mut resource_sum = 0;
        for &(s, dur) in &[(s1, d), (s2, d), (s3, d)] {
            if s <= t && t < s + dur {
                resource_sum += 2; // resource per task
            }
        }
        assert!(
            resource_sum <= 5,
            "resource overload at t={t}: sum={resource_sum} > 5, s=[{s1},{s2},{s3}]"
        );
    }
}

#[test]
fn roundtrip_inverse() {
    let ay = exact_ay();
    // f and g are inverse permutations of {1, 2, 3}
    let fzn = "array [1..3] of var 1..3: f :: output_array([1..3]);\n\
               array [1..3] of var 1..3: g :: output_array([1..3]);\n\
               constraint fzn_inverse(f, g);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let (code, stdout, stderr) = run_ay(&result.smtlib, &ay);
    assert_eq!(code, 0, "ay stderr: {stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat");

    let values = parse_get_value(lines[1]);
    let f: Vec<i64> = (1..=3)
        .map(|i| {
            values
                .get(&format!("f_{i}"))
                .unwrap()
                .parse::<i64>()
                .expect("parse f_i")
        })
        .collect();
    let g: Vec<i64> = (1..=3)
        .map(|i| {
            values
                .get(&format!("g_{i}"))
                .unwrap()
                .parse::<i64>()
                .expect("parse g_i")
        })
        .collect();

    // Verify inverse: f[i] = j implies g[j] = i (1-indexed)
    for (i_idx, &f_val) in f.iter().enumerate() {
        let j_idx = (f_val - 1) as usize;
        assert_eq!(
            g[j_idx],
            i_idx as i64 + 1,
            "inverse broken: f[{}]={}, g[{}]={}, expected {}",
            i_idx + 1,
            f_val,
            f_val,
            g[j_idx],
            i_idx + 1
        );
    }
    for (j_idx, &g_val) in g.iter().enumerate() {
        let i_idx = (g_val - 1) as usize;
        assert_eq!(
            f[i_idx],
            j_idx as i64 + 1,
            "inverse broken (reverse): g[{}]={}, f[{}]={}, expected {}",
            j_idx + 1,
            g_val,
            g_val,
            f[i_idx],
            j_idx + 1
        );
    }
}

#[test]
fn roundtrip_diffn() {
    let ay = exact_ay();
    // 2 rectangles: (2x3) and (3x2), placed in a 5x5 grid, must not overlap
    let fzn = "array [1..2] of var 0..5: x :: output_array([1..2]);\n\
               array [1..2] of var 0..5: y :: output_array([1..2]);\n\
               array [1..2] of int: dx = [2, 3];\n\
               array [1..2] of int: dy = [3, 2];\n\
               constraint fzn_diffn(x, y, dx, dy);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let (code, stdout, stderr) = run_ay(&result.smtlib, &ay);
    assert_eq!(code, 0, "ay stderr: {stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat");

    let values = parse_get_value(lines[1]);
    let x1 = parse_smt_int(values.get("x_1").unwrap());
    let x2 = parse_smt_int(values.get("x_2").unwrap());
    let y1 = parse_smt_int(values.get("y_1").unwrap());
    let y2 = parse_smt_int(values.get("y_2").unwrap());
    let (dx1, dx2, dy1, dy2) = (2, 3, 3, 2);

    // At least one separation axis: no overlap
    let sep_x_left = x1 + dx1 <= x2;
    let sep_x_right = x2 + dx2 <= x1;
    let sep_y_bottom = y1 + dy1 <= y2;
    let sep_y_top = y2 + dy2 <= y1;
    assert!(
        sep_x_left || sep_x_right || sep_y_bottom || sep_y_top,
        "rectangles must not overlap: r1=({x1},{y1},{dx1},{dy1}), r2=({x2},{y2},{dx2},{dy2})"
    );
}

#[test]
fn roundtrip_regular_simple_dfa() {
    let ay = exact_ay();
    // DFA: 2 states, alphabet {1, 2}, accepts strings ending in symbol '1'
    // State 1: initial. On 1->2, On 2->1.
    // State 2: accepting. On 1->2, On 2->1.
    // Sequence of length 2, must end in state 2 (accepting)
    let fzn = "array [1..2] of var 1..2: x :: output_array([1..2]);\n\
               constraint fzn_regular(x, 2, 2, [2, 1, 2, 1], 1, {2});\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let (code, stdout, stderr) = run_ay(&result.smtlib, &ay);
    assert_eq!(code, 0, "ay stderr: {stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat");

    let values = parse_get_value(lines[1]);
    let x1: i64 = values.get("x_1").unwrap().parse().expect("parse x_1");
    let x2: i64 = values.get("x_2").unwrap().parse().expect("parse x_2");

    // Simulate the DFA: start at state 1
    let transition = |state: usize, sym: usize| -> usize {
        let d = [2, 1, 2, 1]; // flat: [s1_a1, s1_a2, s2_a1, s2_a2]
        d[(state - 1) * 2 + (sym - 1)]
    };
    let s1 = transition(1, x1 as usize);
    let s2 = transition(s1, x2 as usize);
    assert_eq!(
        s2, 2,
        "DFA must end in accepting state 2, got {s2} for x=[{x1},{x2}]"
    );
}
