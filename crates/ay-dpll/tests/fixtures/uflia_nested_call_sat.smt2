; Copyright 2026 Andrew Yates
; Author: Andrew Yates
; Licensed under the Apache License, Version 2.0
; Exact immutable 4de consumer dump; wrapper/nullary syntax translation only.
(set-option :timeout 10000)
(set-option :produce-models true)
(declare-const v0 Bool) ; b
(declare-const v1 Bool) ; c
(declare-const v2 Int) ; x
(declare-fun nl_mul (Int Int) Int)
(declare-fun nl_div (Int Int) Int)
(declare-fun nl_mod (Int Int) Int)
(declare-fun clip_u8_oob (Int) Int)
(declare-fun clip_u16_oob (Int) Int)
(declare-fun clip_u32_oob (Int) Int)
(declare-fun clip_u64_oob (Int) Int)
(declare-fun clip_i8_oob (Int) Int)
(declare-fun clip_i16_oob (Int) Int)
(declare-fun clip_i32_oob (Int) Int)
(declare-fun clip_i64_oob (Int) Int)
(declare-fun clip_nat_oob (Int) Int)
(declare-fun sf0 (Int) Int)
(declare-fun rf0 (Int) Int)
(assert (ite (= v2 1) v0 (= v2 1)))
(assert (= (sf0 (sf0 v2)) (sf0 (sf0 1))))
(assert (= (sf0 0) 0))
(assert (= (sf0 0) (rf0 0)))
(assert (= (sf0 2) (rf0 2)))
(assert (= (rf0 0) 0))
(assert (= (rf0 2) (+ 2 (rf0 1))))
(assert (not (= (sf0 2) 3)))
(check-sat)
(get-model)
