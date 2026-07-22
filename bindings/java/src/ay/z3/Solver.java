/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 */

package ay.z3;

import java.lang.foreign.MemorySegment;

/**
 * An incremental SMT solver, mirroring {@code com.microsoft.z3.Solver}.
 * Every verdict and model is produced by AY itself; this wrapper only marshals
 * calls across the FFI.
 */
public final class Solver {

    private final Context ctx;
    private final MemorySegment handle;

    Solver(Context ctx) {
        this.ctx = ctx;
        try {
            this.handle = (MemorySegment) Native.mk_solver.invoke(ctx.ref());
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** Assert one or more Boolean constraints ({@code Z3_solver_assert}). */
    public void add(BoolExpr... constraints) {
        try {
            for (BoolExpr c : constraints) {
                Native.solver_assert.invoke(ctx.ref(), handle, c.ast);
            }
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** Create a new backtracking scope ({@code Z3_solver_push}). */
    public void push() {
        try {
            Native.solver_push.invoke(ctx.ref(), handle);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** Pop {@code n} backtracking scopes ({@code Z3_solver_pop}). */
    public void pop(int n) {
        try {
            Native.solver_pop.invoke(ctx.ref(), handle, n);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** Pop one backtracking scope. */
    public void pop() {
        pop(1);
    }

    /** Remove all assertions and scopes ({@code Z3_solver_reset}). */
    public void reset() {
        try {
            Native.solver_reset.invoke(ctx.ref(), handle);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** Check satisfiability of the asserted constraints ({@code Z3_solver_check}). */
    public Status check() {
        try {
            int r = (int) Native.solver_check.invoke(ctx.ref(), handle);
            return Status.fromLbool(r);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** The model from the last SATISFIABLE {@link #check()} ({@code Z3_solver_get_model}). */
    public Model getModel() {
        try {
            MemorySegment m = (MemorySegment) Native.solver_get_model.invoke(ctx.ref(), handle);
            if (m == null || m.address() == 0) {
                throw new AyZ3Exception("no model available (last check was not SAT?)");
            }
            return new Model(ctx, m);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }

    /** SMT-LIB rendering of the solver's assertions ({@code Z3_solver_to_string}). */
    @Override
    public String toString() {
        try {
            MemorySegment s = (MemorySegment) Native.solver_to_string.invoke(ctx.ref(), handle);
            return Native.jstr(s);
        } catch (Throwable t) {
            throw AyZ3Exception.wrap(t);
        }
    }
}
