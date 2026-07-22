// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(crate) const SAFE_INPUT: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert
  (forall ((x Int))
    (=>
      (= x 0)
      (Inv x))))
(assert
  (forall ((x Int))
    (=>
      (and (Inv x) (< x 5))
      (Inv (+ x 1)))))
(assert
  (forall ((x Int))
    (=>
      (and (Inv x) (>= x 10))
      false)))
(check-sat)
(exit)
"#;
