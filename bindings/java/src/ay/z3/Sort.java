/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 */

package ay.z3;

import java.lang.foreign.MemorySegment;

/**
 * An SMT sort (type), wrapping a native {@code Z3_sort} pointer. Mirrors
 * {@code com.microsoft.z3.Sort}. Create sorts via {@link Context}.
 */
public class Sort {

    final Context ctx;
    /** Native {@code Z3_sort} handle (a real pointer). */
    final MemorySegment seg;

    Sort(Context ctx, MemorySegment seg) {
        this.ctx = ctx;
        this.seg = seg;
    }

    /** The context that owns this sort. */
    public Context getContext() {
        return ctx;
    }
}
