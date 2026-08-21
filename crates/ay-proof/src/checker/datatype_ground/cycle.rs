// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;

/// Iterative three-color DFS cycle detection over the class graph.
pub(super) fn has_cycle(edges: &HashMap<u64, Vec<u64>>, roots: &[u64]) -> bool {
    const WHITE: u8 = 0;
    const GRAY: u8 = 1;
    const BLACK: u8 = 2;
    let mut color: HashMap<u64, u8> = HashMap::default();
    for &start in roots {
        if *color.get(&start).unwrap_or(&WHITE) != WHITE {
            continue;
        }
        let mut stack: Vec<(u64, usize)> = vec![(start, 0)];
        color.insert(start, GRAY);
        while let Some(&mut (node, ref mut cursor)) = stack.last_mut() {
            let children = edges.get(&node).map_or(&[][..], Vec::as_slice);
            if *cursor < children.len() {
                let child = children[*cursor];
                *cursor += 1;
                match *color.get(&child).unwrap_or(&WHITE) {
                    GRAY => return true,
                    WHITE => {
                        color.insert(child, GRAY);
                        stack.push((child, 0));
                    }
                    _ => {}
                }
            } else {
                color.insert(node, BLACK);
                stack.pop();
            }
        }
    }
    false
}
