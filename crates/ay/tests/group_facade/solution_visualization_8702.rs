// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Facade tests for solution visualization helpers (#8702).

#[test]
fn facade_renders_n_queens_ascii() {
    let model = r#"(model
  (define-fun q1 () Int 2)
  (define-fun q2 () Int 4)
  (define-fun q3 () Int 1)
  (define-fun q4 () Int 3)
)"#;

    let rendered = ay::api::render_solution_visualization(
        "; N-Queens",
        model,
        ay::api::VisualizationFormat::Ascii,
    )
    .expect("n-queens visualization");

    assert!(rendered.contains("; ay visualization: n-queens 4x4"));
    assert!(rendered.contains("| . | Q | . | . |"));
}
