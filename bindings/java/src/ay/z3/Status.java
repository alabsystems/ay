/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 */

package ay.z3;

/**
 * Result of {@link Solver#check()} — the three-valued SMT verdict, mirroring
 * {@code com.microsoft.z3.Status}.
 */
public enum Status {
    UNSATISFIABLE,
    UNKNOWN,
    SATISFIABLE;

    /**
     * Map a {@code Z3_lbool} (as returned by {@code Z3_solver_check}) to a
     * {@code Status}: {@code Z3_L_TRUE(1) -> SATISFIABLE},
     * {@code Z3_L_FALSE(-1) -> UNSATISFIABLE}, {@code Z3_L_UNDEF(0) -> UNKNOWN}.
     */
    static Status fromLbool(int lbool) {
        if (lbool > 0) return SATISFIABLE;
        if (lbool < 0) return UNSATISFIABLE;
        return UNKNOWN;
    }
}
