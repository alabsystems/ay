// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_theta_lambda_tree_basic() {
    // 4 tasks: est=[0,25,30,32], durations=[5,9,5,10]
    // Matches Pumpkin's test_tree_built_correctly
    let mut tree = ThetaLambdaTree::new(4);
    // Tasks already sorted by EST: [0,1,2,3]
    tree.reset(&[0, 1, 2, 3]);

    // Add all to Theta
    tree.add_to_theta(0, 5, 5); // ect=5
    tree.add_to_theta(1, 25 + 9, 9); // ect=34
    tree.add_to_theta(2, 30 + 5, 5); // ect=35
    tree.add_to_theta(3, 32 + 10, 10); // ect=42

    // Remove task 2 from Theta, add to Lambda
    tree.remove_from_theta(2);
    tree.add_to_lambda(2, 30 + 5, 5);

    // Verify node values match Pumpkin's test
    // Leaf nodes (indices 3..6 in 0-indexed tree with n_internal=3)
    assert_eq!(tree.nodes[3].ect, 5);
    assert_eq!(tree.nodes[3].sum_p, 5);
    assert_eq!(tree.nodes[4].ect, 34);
    assert_eq!(tree.nodes[4].sum_p, 9);
    assert_eq!(tree.nodes[5].ect, EMPTY); // Lambda (gray)
    assert_eq!(tree.nodes[5].ect_bar, 35);
    assert_eq!(tree.nodes[6].ect, 42);
    assert_eq!(tree.nodes[6].sum_p, 10);

    // Root: ect of Theta
    assert_eq!(tree.ect(), 44);
    assert_eq!(tree.sum_p(), 24);
    assert_eq!(tree.ect_bar(), 49);
}

#[test]
fn test_theta_only() {
    let mut tree = ThetaLambdaTree::new(3);
    tree.reset(&[0, 1, 2]);

    tree.add_to_theta(0, 10, 5); // est=5, dur=5, ect=10
    tree.add_to_theta(1, 25, 10); // est=15, dur=10, ect=25
    tree.add_to_theta(2, 35, 5); // est=30, dur=5, ect=35

    // ect(Theta) = max(35, max(25, 10+10) + 5) = max(35, 25+5) = max(35, 30) = 35
    // Actually: ect = max of all (est_i + sum_p for tasks >= est_i)
    assert_eq!(tree.sum_p(), 20);
    // With these values: root ect should be max(35, 25+5, 10+15) = 35
    assert!(tree.ect() >= 35);
}

#[test]
fn test_responsible_ect_bar() {
    // 3 tasks: est=[0, 2, 3], durations=[5, 10, 5]
    // Task 1 in Lambda should increase ECT when added to Theta.
    //
    // Theta = {task0, task2}: ECT = max(0+5+5, 3+5) = 10
    // Theta ∪ {task1}: ECT = max(0+20, 2+15, 3+5) = 20
    // → task 1 is responsible, ect_bar should be 20.
    let mut tree = ThetaLambdaTree::new(3);
    tree.reset(&[0, 1, 2]);

    tree.add_to_theta(0, 5, 5); // est=0, ect=5
    tree.add_to_theta(1, 12, 10); // est=2, ect=12
    tree.add_to_theta(2, 8, 5); // est=3, ect=8

    // Move task 1 from Theta to Lambda
    tree.remove_from_theta(1);
    tree.add_to_lambda(1, 12, 10);

    // Theta = {0, 2}: ECT = 10, sum_p = 10
    assert_eq!(tree.ect(), 10);
    assert_eq!(tree.sum_p(), 10);

    // ect_bar should be > 10 because adding task 1 increases ECT
    assert!(
        tree.ect_bar() > tree.ect(),
        "Lambda task should increase ECT"
    );

    // Task 1 should be the responsible Lambda task
    let responsible = tree.responsible_ect_bar();
    assert_eq!(responsible, Some(1));
}

#[test]
fn test_conflict_detection() {
    // 3 tasks that can't fit: est=[0,0,0], dur=[5,5,5], lct all <= 10
    let mut tree = ThetaLambdaTree::new(3);
    tree.reset(&[0, 1, 2]);

    tree.add_to_theta(0, 5, 5);
    tree.add_to_theta(1, 5, 5);
    tree.add_to_theta(2, 5, 5);

    // ect(Theta) = 15 (all must run sequentially from est=0)
    assert_eq!(tree.ect(), 15);
    assert_eq!(tree.sum_p(), 15);
}
