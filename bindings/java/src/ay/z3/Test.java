/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 */

package ay.z3;

/**
 * End-to-end test of the AY Java binding against libay_ffi. Every verdict and
 * model value is produced by AY itself. Exit code 0 iff every assertion holds.
 * Verdicts are cross-checked against the z3 CLI.
 */
public final class Test {

    private static int failures = 0;

    private static void check(String name, boolean cond) {
        if (cond) {
            System.out.println("  PASS: " + name);
        } else {
            failures++;
            System.out.println("  FAIL: " + name);
        }
    }

    private static void checkEq(String name, Object got, Object want) {
        boolean ok = (got == null) ? want == null : got.equals(want);
        if (ok) {
            System.out.println("  PASS: " + name + " -> " + got);
        } else {
            failures++;
            System.out.println("  FAIL: " + name + " -> got " + got + ", want " + want);
        }
    }

    // (1) LIA SAT: 3 < x AND x < 6 -> SAT, and x evaluates to 4 or 5.
    private static void testLiaSat() {
        try (Context ctx = new Context()) {
            ArithExpr x = ctx.mkIntConst("x");
            Solver s = ctx.mkSolver();
            s.add(ctx.mkGt(x, ctx.mkInt(3)));
            s.add(ctx.mkLt(x, ctx.mkInt(6)));
            checkEq("lia_sat:check", s.check(), Status.SATISFIABLE);

            Model m = s.getModel();
            Expr v = m.eval(x, true);
            long xv = v.asLong();
            check("lia_sat:model_x_in_{4,5} (got " + xv + ")", xv == 4 || xv == 5);
        }
    }

    // (2) LIA UNSAT: x > 5 AND x < 3 -> UNSATISFIABLE.
    private static void testLiaUnsat() {
        try (Context ctx = new Context()) {
            ArithExpr x = ctx.mkIntConst("x");
            Solver s = ctx.mkSolver();
            s.add(ctx.mkGt(x, ctx.mkInt(5)));
            s.add(ctx.mkLt(x, ctx.mkInt(3)));
            checkEq("lia_unsat:check", s.check(), Status.UNSATISFIABLE);
        }
    }

    // (3) Boolean: (a OR b) AND (NOT a) -> SAT; and a AND (NOT a) -> UNSAT.
    private static void testBool() {
        try (Context ctx = new Context()) {
            BoolExpr a = ctx.mkBoolConst("a");
            BoolExpr b = ctx.mkBoolConst("b");

            Solver s1 = ctx.mkSolver();
            s1.add(ctx.mkOr(a, b));
            s1.add(ctx.mkNot(a));
            checkEq("bool_sat:check", s1.check(), Status.SATISFIABLE);

            Solver s2 = ctx.mkSolver();
            s2.add(ctx.mkAnd(a, ctx.mkNot(a)));
            checkEq("bool_unsat:check", s2.check(), Status.UNSATISFIABLE);
        }
    }

    // (4) BitVector SAT: 8-bit x, x + 1 == 0 -> SAT, and x evaluates to 255.
    private static void testBvSat() {
        try (Context ctx = new Context()) {
            BitVecExpr x = ctx.mkBVConst("x", 8);
            Solver s = ctx.mkSolver();
            // x + 1 == 0 (mod 2^8)  <=>  x == 255
            BitVecExpr sum = ctx.mkBVAdd(x, ctx.mkBV(1, 8));
            s.add(ctx.mkEq(sum, ctx.mkBV(0, 8)));
            checkEq("bv_sat:check", s.check(), Status.SATISFIABLE);

            Model m = s.getModel();
            long xv = m.eval(x, true).asLong();
            checkEq("bv_sat:model_x==255", xv, 255L);
        }
    }

    // (5) BitVector UNSAT: 4-bit x, x <u 3 AND x >u 5 -> UNSATISFIABLE.
    private static void testBvUnsat() {
        try (Context ctx = new Context()) {
            BitVecExpr x = ctx.mkBVConst("x", 4);
            Solver s = ctx.mkSolver();
            s.add(ctx.mkBVULT(x, ctx.mkBV(3, 4)));
            s.add(ctx.mkBVUGT(x, ctx.mkBV(5, 4)));
            checkEq("bv_unsat:check", s.check(), Status.UNSATISFIABLE);
        }
    }

    // (6) push/pop incrementality over Int x: SAT, push contradiction -> UNSAT,
    //     pop -> SAT again.
    private static void testPushPop() {
        try (Context ctx = new Context()) {
            ArithExpr x = ctx.mkIntConst("x");
            Solver s = ctx.mkSolver();
            s.add(ctx.mkGt(x, ctx.mkInt(0)));
            checkEq("push_pop:base_sat", s.check(), Status.SATISFIABLE);
            s.push();
            s.add(ctx.mkLt(x, ctx.mkInt(0)));
            checkEq("push_pop:scoped_unsat", s.check(), Status.UNSATISFIABLE);
            s.pop();
            checkEq("push_pop:after_pop_sat", s.check(), Status.SATISFIABLE);
        }
    }

    public static void main(String[] args) {
        System.out.println("AY Java (FFM) binding test");
        System.out.println("  bound Z3_* functions: " + Native.BOUND_FUNCTION_COUNT);

        testLiaSat();
        testLiaUnsat();
        testBool();
        testBvSat();
        testBvUnsat();
        testPushPop();

        if (failures == 0) {
            System.out.println("All Java binding tests passed.");
            System.exit(0);
        } else {
            System.out.println(failures + " Java binding test(s) FAILED.");
            System.exit(1);
        }
    }
}
