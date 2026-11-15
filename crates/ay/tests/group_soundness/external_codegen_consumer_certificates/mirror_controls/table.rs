// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One hand-spelled control per mirrored rule: a step the consumer accepts,
//! and the edit that makes it one the consumer refuses. Each step was derived
//! by reading Clean 7330fa6c's rule, not by running the mirror, and both
//! verdicts were confirmed with a Clean built from that checker source
//! (2026-09-30); with `CLEAN_PATH` set the test confirms them again.

/// `rule`: the step's rule; `assertions`: problem assertions an `assume`
/// in `steps` cites; `steps`: the commands, the last being the rule's step;
/// `edit`: (text, replacement) applied once to that last command.
pub(super) struct Control {
    pub(super) rule: &'static str,
    pub(super) assertions: &'static [&'static str],
    pub(super) steps: &'static str,
    pub(super) edit: (&'static str, &'static str),
}

const fn control(
    rule: &'static str,
    assertions: &'static [&'static str],
    steps: &'static str,
    edit: (&'static str, &'static str),
) -> Control {
    Control {
        rule,
        assertions,
        steps,
        edit,
    }
}

pub(super) const CONTROLS: &[Control] = &[
    control("true", &[], "(step t (cl true) :rule true)", ("(cl true)", "(cl false)")),
    control("false", &[], "(step t (cl (not false)) :rule false)", ("(not false)", "(not true)")),
    control("not_not", &[], "(step t (cl (not (not (not p))) p) :rule not_not)", (" p)", " q)")),
    control("and_pos", &[], "(step t (cl (not (and p q r)) q) :rule and_pos :args (1))", ("(1)", "(2)")),
    control("and_neg", &[], "(step t (cl (and p q) (not p) (not q)) :rule and_neg)", ("(not q))", "q)")),
    control("or_pos", &[], "(step t (cl (not (or p q)) p q) :rule or_pos)", (" p q)", " q p)")),
    control("or_neg", &[], "(step t (cl (or p q) (not q)) :rule or_neg :args (1))", ("(1)", "(0)")),
    control("xor_pos1", &[], "(step t (cl (not (xor p q)) p q) :rule xor_pos1)", (" p q)", " (not p) q)")),
    control("xor_pos2", &[], "(step t (cl (not (xor p q)) (not p) (not q)) :rule xor_pos2)", ("(not q))", "q)")),
    control("xor_neg1", &[], "(step t (cl (xor p q) p (not q)) :rule xor_neg1)", ("(not q))", "q)")),
    control("xor_neg2", &[], "(step t (cl (xor p q) (not p) q) :rule xor_neg2)", ("(not p) q)", "p q)")),
    control("implies_pos", &[], "(step t (cl (not (=> p q)) (not p) q) :rule implies_pos)", ("(not p) q)", "p q)")),
    control("implies_neg1", &[], "(step t (cl (=> p q) p) :rule implies_neg1)", (" p)", " q)")),
    control("implies_neg2", &[], "(step t (cl (=> p q) (not q)) :rule implies_neg2)", ("(not q))", "(not p))")),
    control("equiv_pos1", &[], "(step t (cl (not (= p q)) p (not q)) :rule equiv_pos1)", ("(not q))", "q)")),
    control("equiv_pos2", &[], "(step t (cl (not (= p q)) (not p) q) :rule equiv_pos2)", ("(not p) q)", "p q)")),
    control("equiv_neg1", &[], "(step t (cl (= p q) (not p) (not q)) :rule equiv_neg1)", ("(not p) (not q))", "p (not q))")),
    control("equiv_neg2", &[], "(step t (cl (= p q) p q) :rule equiv_neg2)", (" p q)", " p (not q))")),
    control("ite_pos1", &[], "(step t (cl (not (ite p q r)) p r) :rule ite_pos1)", (" p r)", " p q)")),
    control("ite_pos2", &[], "(step t (cl (not (ite p q r)) (not p) q) :rule ite_pos2)", ("(not p) q)", "(not p) r)")),
    control("ite_neg1", &[], "(step t (cl (ite p q r) p (not r)) :rule ite_neg1)", ("(not r))", "(not q))")),
    control("ite_neg2", &[], "(step t (cl (ite p q r) (not p) (not q)) :rule ite_neg2)", ("(not q))", "(not r))")),
    control("equiv1", &["(= p q)"], "(assume h (= p q))\n(step t (cl (not p) q) :rule equiv1 :premises (h))", ("(cl (not p) q)", "(cl p q)")),
    control("equiv2", &["(= p q)"], "(assume h (= p q))\n(step t (cl p (not q)) :rule equiv2 :premises (h))", ("(cl p (not q))", "(cl p q)")),
    control("not_equiv1", &["(not (= p q))"], "(assume h (not (= p q)))\n(step t (cl p q) :rule not_equiv1 :premises (h))", ("(cl p q)", "(cl (not p) q)")),
    control("not_equiv2", &["(not (= p q))"], "(assume h (not (= p q)))\n(step t (cl (not p) (not q)) :rule not_equiv2 :premises (h))", ("(cl (not p)", "(cl p")),
    control("ite1", &["(ite p q r)"], "(assume h (ite p q r))\n(step t (cl p r) :rule ite1 :premises (h))", ("(cl p r)", "(cl p q)")),
    control("ite2", &["(ite p q r)"], "(assume h (ite p q r))\n(step t (cl (not p) q) :rule ite2 :premises (h))", ("(cl (not p) q)", "(cl (not p) r)")),
    control("not_ite1", &["(not (ite p q r))"], "(assume h (not (ite p q r)))\n(step t (cl p (not r)) :rule not_ite1 :premises (h))", ("(cl p (not r))", "(cl p (not q))")),
    control("not_ite2", &["(not (ite p q r))"], "(assume h (not (ite p q r)))\n(step t (cl (not p) (not q)) :rule not_ite2 :premises (h))", ("(not q))", "(not r))")),
    control("xor1", &["(xor p q)"], "(assume h (xor p q))\n(step t (cl p q) :rule xor1 :premises (h))", ("(cl p q)", "(cl q p)")),
    control("xor2", &["(xor p q)"], "(assume h (xor p q))\n(step t (cl (not p) (not q)) :rule xor2 :premises (h))", ("(not q))", "q)")),
    control("not_xor1", &["(not (xor p q))"], "(assume h (not (xor p q)))\n(step t (cl p (not q)) :rule not_xor1 :premises (h))", ("(cl p (not q))", "(cl p q)")),
    control("not_xor2", &["(not (xor p q))"], "(assume h (not (xor p q)))\n(step t (cl (not p) q) :rule not_xor2 :premises (h))", ("(cl (not p) q)", "(cl p q)")),
    control("implies", &["(=> p q)"], "(assume h (=> p q))\n(step t (cl (not p) q) :rule implies :premises (h))", ("(cl (not p) q)", "(cl p q)")),
    control("not_implies1", &["(not (=> p q))"], "(assume h (not (=> p q)))\n(step t (cl p) :rule not_implies1 :premises (h))", ("(cl p)", "(cl q)")),
    control("not_implies2", &["(not (=> p q))"], "(assume h (not (=> p q)))\n(step t (cl (not q)) :rule not_implies2 :premises (h))", ("(cl (not q))", "(cl (not p))")),
    control("and", &["(and p q r)"], "(assume h (and p q r))\n(step t (cl q) :rule and :premises (h) :args (1))", ("(1)", "(2)")),
    control("not_or", &["(not (or p q))"], "(assume h (not (or p q)))\n(step t (cl (not q)) :rule not_or :premises (h) :args (1))", ("(1)", "(0)")),
    control("or", &["(or p q)"], "(assume h (or p q))\n(step t (cl p q) :rule or :premises (h))", ("(cl p q)", "(cl q p)")),
    control("not_and", &["(not (and p q))"], "(assume h (not (and p q)))\n(step t (cl (not p) (not q)) :rule not_and :premises (h))", ("(cl (not p) (not q))", "(cl (not q) (not p))")),
    control("contraction", &["(or p p q)"], "(assume h (or p p q))\n(step c (cl p p q) :rule or :premises (h))\n(step t (cl p q) :rule contraction :premises (c))", ("(cl p q)", "(cl p)")),
    control("reordering", &["(or p q)"], "(assume h (or p q))\n(step c (cl p q) :rule or :premises (h))\n(step t (cl q p) :rule reordering :premises (c))", ("(cl q p)", "(cl q q)")),
    control("resolution", &["(or p q)", "(not p)"], "(assume h1 (or p q))\n(assume h2 (not p))\n(step c (cl p q) :rule or :premises (h1))\n(step t (cl q) :rule resolution :premises (c h2) :args (p true))", ("(p true)", "(p false)")),
    control("th_resolution", &["(or p q)", "(not p)"], "(assume h1 (or p q))\n(assume h2 (not p))\n(step c (cl p q) :rule or :premises (h1))\n(step t (cl q) :rule th_resolution :premises (c h2))", ("(cl q)", "(cl r)")),
    control("drup", &["(or p q)", "(not p)"], "(assume h1 (or p q))\n(assume h2 (not p))\n(step c (cl p q) :rule or :premises (h1))\n(step t (cl q) :rule drup :premises (c h2) :args ((cl q)))", ("(cl q) :rule drup", "(cl r) :rule drup")),
    control("eq_reflexive", &[], "(step t (cl (= p p)) :rule eq_reflexive)", ("(= p p)", "(= p q)")),
    control("eq_transitive", &[], "(step t (cl (not (= p q)) (not (= q r)) (= r p)) :rule eq_transitive)", ("(= r p)", "(= r s)")),
    control("eq_congruent", &[], "(step t (cl (not (= p q)) (= (not p) (not q))) :rule eq_congruent)", ("(not q)))", "(not r)))")),
    control("eq_congruent_pred", &[], "(step t (cl (not (= p q)) (not (= r r)) (not (and p r)) (and q r)) :rule eq_congruent_pred)", ("(and q r))", "(and q p))")),
    control("refl", &[], "(step t (cl (= (= p q) (= q p))) :rule refl)", ("(= q p)", "(= q r)")),
    control("trans", &["(= p q)", "(= q r)"], "(assume h1 (= p q))\n(assume h2 (= q r))\n(step t (cl (= p r)) :rule trans :premises (h1 h2))", ("(= p r)", "(= p s)")),
    control("cong", &["(= p q)"], "(assume h (= p q))\n(step t (cl (= (and p r) (and q r))) :rule cong :premises (h))", ("(and q r)", "(and q s)")),
    control("symm", &["(= p q)"], "(assume h (= p q))\n(step t (cl (= q p)) :rule symm :premises (h))", ("(cl (= q p))", "(cl (= p q))")),
    control("not_symm", &["(not (= p q))"], "(assume h (not (= p q)))\n(step t (cl (not (= q p))) :rule not_symm :premises (h))", ("(cl (not (= q p)))", "(cl (not (= p q)))")),
    control("subproof", &[], "(anchor :step t)\n(assume t.a p)\n(step t.r (cl (= p p)) :rule eq_reflexive)\n(step t (cl (not p) (= p p)) :rule subproof :discharge (t.a))", ("(cl (not p)", "(cl p")),
    control("arrays_idx", &[], "(step t (cl (= (select (store m p q) p) q)) :rule arrays_idx)", ("p) q))", "p) r))")),
    control("arrays_row", &["(not (= p q))"], "(assume h (not (= p q)))\n(step t (cl (= (select (store m p r) q) (select m q))) :rule arrays_row :premises (h))", ("(select m q)", "(select m p)")),
    control("arrays_row_contra", &["(not (= (select (store m p r) q) (select m q)))"], "(assume h (not (= (select (store m p r) q) (select m q))))\n(step t (cl (= p q)) :rule arrays_row_contra :premises (h))", ("(cl (= p q))", "(cl (= p r))")),
    control("and_simplify", &[], "(step t (cl (= (and true p q) (and p q))) :rule and_simplify)", ("(and p q))", "(and q p))")),
    control("or_simplify", &[], "(step t (cl (= (or p false q) (or p q))) :rule or_simplify)", ("(or p q))", "(or q p))")),
    control("ite_simplify", &[], "(step t (cl (= (ite true p q) p)) :rule ite_simplify)", ("q) p)", "q) q)")),
    control("equiv_simplify", &[], "(step t (cl (= (= p true) p)) :rule equiv_simplify)", ("true) p)", "true) (not p))")),
    control("ite_intro", &[], "(step t (cl (= (= (ite p q r) s) (and (= (ite p q r) s) (ite p (= q (ite p q r)) (= r (ite p q r)))))) :rule ite_intro)", ("(= r (ite", "(= s (ite")),
    control("evaluate", &[], "(step t (cl (= (and ((_ @bit_of 1) #b10) (bvult #b01 (bvadd #b01 #b10))) true)) :rule evaluate)", ("true))", "false))")),
    control("poly_simp", &[], "(step t (cl (= (bvmul (@bbterm a b) #b11) (bvneg (@bbterm a b)))) :rule poly_simp)", ("#b11", "#b10")),
    control("bitblast_const", &[], "(step t (cl (= #b10 (@bbterm false true))) :rule bitblast_const)", ("(@bbterm false true)", "(@bbterm true false)")),
    control("bitblast_var", &[], "(step t (cl (= ((_ extract 1 0) (@bbterm a b)) (@bbterm ((_ @bit_of 0) ((_ extract 1 0) (@bbterm a b))) ((_ @bit_of 1) ((_ extract 1 0) (@bbterm a b)))))) :rule bitblast_var)", ("(@bbterm ((_ @bit_of 0)", "(@bbterm ((_ @bit_of 1)")),
    control("bitblast_and", &[], "(step t (cl (= (bvand (@bbterm a b) (@bbterm c d)) (@bbterm (and a c) (and b d)))) :rule bitblast_and)", ("(and b d)", "(and d b)")),
    control("bitblast_or", &[], "(step t (cl (= (bvor (@bbterm a b) (@bbterm c d)) (@bbterm (or a c) (or b d)))) :rule bitblast_or)", ("(or b d)", "(or d b)")),
    control("bitblast_xor", &[], "(step t (cl (= (bvxor (@bbterm a b) (@bbterm c d)) (@bbterm (xor a c) (xor b d)))) :rule bitblast_xor)", ("(xor b d)", "(xor d b)")),
    control("bitblast_xnor", &[], "(step t (cl (= (bvxnor (@bbterm a b) (@bbterm c d)) (@bbterm (= a c) (= b d)))) :rule bitblast_xnor)", ("(= b d)", "(= d b)")),
    control("bitblast_not", &[], "(step t (cl (= (bvnot (@bbterm a b)) (@bbterm (not a) (not b)))) :rule bitblast_not)", ("(not b)", "b")),
    control("bitblast_neg", &[], "(step t (cl (= (bvneg (@bbterm a b)) (@bbterm (xor (xor (not a) false) true) (xor (xor (not b) false) (or (and (not a) false) (and (xor (not a) false) true)))))) :rule bitblast_neg)", ("(xor (xor (not a) false) true)", "(xor (xor (not a) false) false)")),
    control("bitblast_equal", &[], "(step t (cl (= (= (@bbterm a b) (@bbterm c d)) (and (= a c) (= b d)))) :rule bitblast_equal)", ("(and (= a c) (= b d))", "(and (= b d) (= a c))")),
    control("bitblast_comp", &[], "(step t (cl (= (bvcomp (@bbterm a b) (@bbterm c d)) (@bbterm (and (= a c) (= b d))))) :rule bitblast_comp)", ("(and (= a c) (= b d))", "(and (= b d) (= a c))")),
    control("bitblast_ult", &[], "(step t (cl (= (bvult (@bbterm a b) (@bbterm c d)) (or (and (= b d) (and (not a) c)) (and (not b) d)))) :rule bitblast_ult)", ("(and (not b) d)", "(and (not d) b)")),
    control("bitblast_slt", &[], "(step t (cl (= (bvslt (@bbterm a b) (@bbterm c d)) (or (and (= b d) (and (not a) c)) (and b (not d))))) :rule bitblast_slt)", ("(and b (not d))", "(and (not b) d)")),
    control("bitblast_add", &[], "(step t (cl (= (bvadd (@bbterm a b) (@bbterm c d)) (@bbterm (xor (xor a c) false) (xor (xor b d) (or (and a c) (and (xor a c) false)))))) :rule bitblast_add)", ("(xor (xor a c) false)", "(xor (xor a c) true)")),
    control("bitblast_mult", &[], "(step t (cl (= (bvmul (@bbterm a b) (@bbterm c d)) (@bbterm (and c a) (xor (xor (and c b) (and d a)) false)))) :rule bitblast_mult)", ("(@bbterm (and c a)", "(@bbterm (and a c)")),
    control("bitblast_extract", &[], "(step t (cl (= ((_ extract 1 1) (@bbterm a b c)) (@bbterm b))) :rule bitblast_extract)", ("(@bbterm b))", "(@bbterm c))")),
    control("bitblast_concat", &[], "(step t (cl (= (concat (@bbterm a) (@bbterm b c)) (@bbterm b c a))) :rule bitblast_concat)", ("(@bbterm b c a)", "(@bbterm a b c)")),
    control("bitblast_sign_extend", &[], "(step t (cl (= ((_ sign_extend 1) (@bbterm a b)) (@bbterm a b b))) :rule bitblast_sign_extend)", ("(@bbterm a b b)", "(@bbterm a b a)")),
    control("bitblast_shl", &[], GUARD_SHL, ("(ite c a b)", "(ite c b a)")),
    control("bitblast_lshr", &[], GUARD_LSHR, ("(ite (not c) a b)", "(ite (not c) b a)")),
    control("bitblast_ashr", &[], ASHR, ("(ite v (ite c b b) b)", "(ite v (ite c b b) false)")),
    control("bitblast_udiv", &[], UDIV, ("false true)))", "false false)))")),
    control("bitblast_urem", &[], UREM, ("(xor (xor s0 (not b)) true)", "(xor (xor s0 (not b)) false)")),
    control("la_generic", &[], "(define-fun x0 () Int ((_ @int_of 0) (@bbterm a b)))\n(define-fun x1 () Int ((_ @int_of 1) (@bbterm a b)))\n(step t (cl (not (>= (- x0 x1) 0)) (not (>= (- x1 x0) 1))) :rule la_generic :args (1 1))", ("(1 1)", "(1 2)")),
    control("pbblast_bveq", &[], "(define-fun x0 () Int ((_ @int_of 0) (@bbterm a b)))\n(define-fun x1 () Int ((_ @int_of 1) (@bbterm a b)))\n(define-fun y0 () Int ((_ @int_of 0) (@bbterm c d)))\n(define-fun y1 () Int ((_ @int_of 1) (@bbterm c d)))\n(step t (cl (= (= (@bbterm a b) (@bbterm c d)) (= (- (+ x0 (* 2 x1)) (+ y0 (* 2 y1))) 0))) :rule pbblast_bveq)", ("(* 2 y1)", "(* 2 y0)")),
    control("pbblast_bvult", &[], "(define-fun x0 () Int ((_ @int_of 0) (@bbterm a b)))\n(define-fun x1 () Int ((_ @int_of 1) (@bbterm a b)))\n(define-fun y0 () Int ((_ @int_of 0) (@bbterm c d)))\n(define-fun y1 () Int ((_ @int_of 1) (@bbterm c d)))\n(step t (cl (= (bvult (@bbterm a b) (@bbterm c d)) (>= (- (+ y0 (* 2 y1)) (+ x0 (* 2 x1))) 1))) :rule pbblast_bvult)", ("(- (+ y0 (* 2 y1))", "(- (+ x0 (* 2 x1))")),
    control("pbblast_bvugt", &[], "(define-fun x0 () Int ((_ @int_of 0) (@bbterm a b)))\n(define-fun x1 () Int ((_ @int_of 1) (@bbterm a b)))\n(define-fun y0 () Int ((_ @int_of 0) (@bbterm c d)))\n(define-fun y1 () Int ((_ @int_of 1) (@bbterm c d)))\n(step t (cl (= (bvugt (@bbterm a b) (@bbterm c d)) (>= (- (+ x0 (* 2 x1)) (+ y0 (* 2 y1))) 1))) :rule pbblast_bvugt)", (") 1))", ") 2))")),
    control("pbblast_bvuge", &[], "(define-fun x0 () Int ((_ @int_of 0) (@bbterm a b)))\n(define-fun x1 () Int ((_ @int_of 1) (@bbterm a b)))\n(define-fun y0 () Int ((_ @int_of 0) (@bbterm c d)))\n(define-fun y1 () Int ((_ @int_of 1) (@bbterm c d)))\n(step t (cl (= (bvuge (@bbterm a b) (@bbterm c d)) (>= (- (+ x0 (* 2 x1)) (+ y0 (* 2 y1))) 0))) :rule pbblast_bvuge)", ("(* 2 x1)", "(* 4 x1)")),
    control("pbblast_bvule", &[], "(define-fun x0 () Int ((_ @int_of 0) (@bbterm a b)))\n(define-fun x1 () Int ((_ @int_of 1) (@bbterm a b)))\n(define-fun y0 () Int ((_ @int_of 0) (@bbterm c d)))\n(define-fun y1 () Int ((_ @int_of 1) (@bbterm c d)))\n(step t (cl (= (bvule (@bbterm a b) (@bbterm c d)) (>= (- (+ y0 (* 2 y1)) (+ x0 (* 2 x1))) 0))) :rule pbblast_bvule)", ("(+ x0 (* 2 x1))", "(+ x0 (* 2 y1))")),
    control("pbblast_bvslt", &[], "(define-fun x0 () Int ((_ @int_of 0) (@bbterm a b)))\n(define-fun x1 () Int ((_ @int_of 1) (@bbterm a b)))\n(define-fun y0 () Int ((_ @int_of 0) (@bbterm c d)))\n(define-fun y1 () Int ((_ @int_of 1) (@bbterm c d)))\n(step t (cl (= (bvslt (@bbterm a b) (@bbterm c d)) (>= (+ (- y0 (* 2 y1)) (- (* 2 x1) x0)) 1))) :rule pbblast_bvslt)", ("(* 2 x1)", "(* 2 x0)")),
    control("pbblast_bvsgt", &[], "(define-fun x0 () Int ((_ @int_of 0) (@bbterm a b)))\n(define-fun x1 () Int ((_ @int_of 1) (@bbterm a b)))\n(define-fun y0 () Int ((_ @int_of 0) (@bbterm c d)))\n(define-fun y1 () Int ((_ @int_of 1) (@bbterm c d)))\n(step t (cl (= (bvsgt (@bbterm a b) (@bbterm c d)) (>= (+ (- x0 (* 2 x1)) (- (* 2 y1) y0)) 1))) :rule pbblast_bvsgt)", ("(- x0 (* 2 x1))", "(- y0 (* 2 x1))")),
    control("pbblast_bvsge", &[], "(define-fun x0 () Int ((_ @int_of 0) (@bbterm a b)))\n(define-fun x1 () Int ((_ @int_of 1) (@bbterm a b)))\n(define-fun y0 () Int ((_ @int_of 0) (@bbterm c d)))\n(define-fun y1 () Int ((_ @int_of 1) (@bbterm c d)))\n(step t (cl (= (bvsge (@bbterm a b) (@bbterm c d)) (>= (+ (- x0 (* 2 x1)) (- (* 2 y1) y0)) 0))) :rule pbblast_bvsge)", ("(* 2 y1) y0)", "(* 2 y1) x0)")),
    control("pbblast_bvsle", &[], "(define-fun x0 () Int ((_ @int_of 0) (@bbterm a b)))\n(define-fun x1 () Int ((_ @int_of 1) (@bbterm a b)))\n(define-fun y0 () Int ((_ @int_of 0) (@bbterm c d)))\n(define-fun y1 () Int ((_ @int_of 1) (@bbterm c d)))\n(step t (cl (= (bvsle (@bbterm a b) (@bbterm c d)) (>= (+ (- y0 (* 2 y1)) (- (* 2 x1) x0)) 0))) :rule pbblast_bvsle)", (") 0))", ") 1))")),
];

/// `bvshl` of two-bit words: one shifter layer (the amount's bit 0), then
/// every bit guarded by `u`, `(bvult amount #b10)` bit-blasted over
/// `((_ @bit_of i) #b10)`.
const GUARD_SHL: &str = "(define-fun u () Bool (or (and (= d ((_ @bit_of 1) #b10)) (and (not c) ((_ @bit_of 0) #b10))) (and (not d) ((_ @bit_of 1) #b10))))\n\
    (step t (cl (= (bvshl (@bbterm a b) (@bbterm c d)) (@bbterm (ite u (ite c false a) false) \
    (ite u (ite c a b) false)))) :rule bitblast_shl)";

/// `bvlshr` of two-bit words, the same guard.
const GUARD_LSHR: &str = "(define-fun u () Bool (or (and (= d ((_ @bit_of 1) #b10)) (and (not c) ((_ @bit_of 0) #b10))) (and (not d) ((_ @bit_of 1) #b10))))\n\
    (step t (cl (= (bvlshr (@bbterm a b) (@bbterm c d)) (@bbterm (ite u (ite (not c) a b) false) \
    (ite u (ite c false b) false)))) :rule bitblast_lshr)";

/// `bvashr` by an amount below the width (Clean's `safe_shift` admits it):
/// the overshift fills with the sign bit `b`; the edit is the measured
/// zero fill.
const ASHR: &str = "(define-fun v () Bool (or (and (= false ((_ @bit_of 1) #b10)) \
    (and (not c) ((_ @bit_of 0) #b10))) (and (not false) ((_ @bit_of 1) #b10))))\n\
    (step t (cl (= (bvashr (@bbterm a b) (@bbterm c false)) (@bbterm (ite v (ite (not c) a b) b) \
    (ite v (ite c b b) b)))) :rule bitblast_ashr)";

/// `bvudiv` of one-bit words: Clean's long division at n = 1, the carry OUT
/// of the top bit, then the zero divisor's all-ones quotient.
const UDIV: &str = "(define-fun o () Bool (ite (= a true) true false))\n(define-fun s0 () Bool (xor (xor false false) o))\n(define-fun c1 () Bool (or (and s0 (not b)) (and (xor s0 (not b)) true)))\n(define-fun c2 () Bool (or (and a (not b)) (and (xor a (not b)) true)))\n\
    (step t (cl (= (bvudiv (@bbterm a) (@bbterm b)) (@bbterm (ite (and (= b false)) true \
    (ite (not c2) false (ite (not c1) false true)))))) :rule bitblast_udiv)";

/// `bvurem` of one-bit words: the remainder becomes the difference when it is
/// at least the divisor, and is the dividend under a zero divisor.
const UREM: &str = "(define-fun o () Bool (ite (= a true) true false))\n(define-fun s0 () Bool (xor (xor false false) o))\n(define-fun c1 () Bool (or (and s0 (not b)) (and (xor s0 (not b)) true)))\n(define-fun c2 () Bool (or (and a (not b)) (and (xor a (not b)) true)))\n\
    (step t (cl (= (bvurem (@bbterm a) (@bbterm b)) (@bbterm (ite (and (= b false)) a \
    (ite (not c2) a (ite (not c1) s0 (xor (xor s0 (not b)) true))))))) :rule bitblast_urem)";
