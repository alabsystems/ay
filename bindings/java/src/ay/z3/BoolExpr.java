/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 */

package ay.z3;

/** A Boolean-sorted expression. Mirrors {@code com.microsoft.z3.BoolExpr}. */
public final class BoolExpr extends Expr {
    BoolExpr(Context ctx, long ast) {
        super(ctx, ast);
    }
}
