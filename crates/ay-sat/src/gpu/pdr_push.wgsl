// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// GPU PDR lemma pushing pre-filter for IC3/PDR frame propagation.
//
// Each thread checks one lemma against all frame clauses to determine
// if the lemma is subsumed by any frame clause. If a frame clause
// subsumes the lemma (every literal of the frame clause appears in
// the lemma), then the lemma is definitely pushable — the frame
// already contains a stronger constraint.
//
// This is a fast pre-filter; the full inductiveness check requires
// SAT queries (F_i /\ T |= clause'). Lemmas that pass this filter
// can skip the expensive SAT call.
//
// Literal encoding: u32 where positive = var*2, negative = var*2+1.

@group(0) @binding(0) var<storage, read> lemma_literals: array<u32>;
@group(0) @binding(1) var<storage, read> lemma_offsets: array<u32>;
@group(0) @binding(2) var<storage, read> frame_literals: array<u32>;
@group(0) @binding(3) var<storage, read> frame_offsets: array<u32>;
@group(0) @binding(4) var<storage, read> params: array<u32>;
@group(0) @binding(5) var<storage, read_write> results: array<u32>;

@compute @workgroup_size(256)
fn pdr_push_check(@builtin(global_invocation_id) gid: vec3<u32>) {
    let lemma_idx = gid.x;
    let num_lemmas = params[0];
    let num_frame_clauses = params[1];

    // Out-of-bounds guard.
    if lemma_idx >= num_lemmas {
        return;
    }

    // Lemma boundaries.
    let lem_start = lemma_offsets[lemma_idx];
    let lem_end = lemma_offsets[lemma_idx + 1u];
    let lem_len = lem_end - lem_start;

    // Check if ANY frame clause subsumes this lemma.
    // Frame clause f subsumes lemma l iff every literal in f also appears in l
    // (f is a subset of l as a set of literals).
    // Since f is a clause (disjunction), f ⊆ l means f is a STRONGER
    // constraint that implies l — so l is redundant at this frame level.
    for (var fi = 0u; fi < num_frame_clauses; fi = fi + 1u) {
        let f_start = frame_offsets[fi];
        let f_end = frame_offsets[fi + 1u];
        let f_len = f_end - f_start;

        // Frame clause can only subsume lemma if |frame| <= |lemma|.
        if f_len > lem_len {
            continue;
        }

        // Check if every literal in frame clause fi appears in the lemma.
        var all_found: bool = true;
        for (var kf = f_start; kf < f_end; kf = kf + 1u) {
            let frame_lit = frame_literals[kf];
            var found: bool = false;
            for (var kl = lem_start; kl < lem_end; kl = kl + 1u) {
                if lemma_literals[kl] == frame_lit {
                    found = true;
                    break;
                }
            }
            if !found {
                all_found = false;
                break;
            }
        }

        if all_found {
            // At least one frame clause subsumes this lemma — it is pushable.
            results[lemma_idx] = 1u;
            return;
        }
    }
}
