// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tree-decomposition-guided branching scores (sharpsat-td, CP 2021).
//!
//! Builds the primal graph of the formula, runs an external anytime
//! tree-decomposition heuristic (FlowCutter, PACE-17 format) under a time
//! budget, finds the centroid bag, and scores each variable by proximity to
//! the centroid: vars introduced near the centroid get the largest boost, so
//! branching splits the decomposition at balanced separators — which is what
//! makes component caching hit.
//!
//! The external binary is optional (`AY_FLOWCUTTER` env or an explicit path);
//! when absent or on any failure the result is `None` and branching falls
//! back to pure VSADS. Scores only bias the branching order — they cannot
//! affect soundness.

use std::collections::HashSet;
use std::io::Write;
use std::process::{Command, Stdio};
use std::time::Duration;

/// Guard limits mirroring GANAK's defaults: skip TD on huge/dense graphs.
const TD_MAX_VARS: usize = 150_000;
const TD_MAX_EDGES_PER_VAR: usize = 30;
const TD_MAX_DENSITY: f64 = 0.30;

/// Compute per-variable TD scores, or `None` when unavailable.
///
/// `clauses` are signed DIMACS literals over `num_vars` variables;
/// `budget` is the FlowCutter wall-clock budget; `decow` is the score weight
/// (competition value: 100).
pub fn td_scores(
    num_vars: usize,
    clauses: &[Vec<i32>],
    budget: Duration,
    decow: f64,
    flow_cutter: &std::path::Path,
) -> Option<Vec<f64>> {
    if num_vars == 0 || num_vars > TD_MAX_VARS || !decow.is_finite() || decow < 0.0 {
        return None;
    }
    // Primal graph: edge between every pair of vars sharing a clause.
    let mut edges: HashSet<(u32, u32)> = HashSet::new();
    for clause in clauses {
        // Cap the quadratic blowup of very long clauses.
        if clause.len() > 100 {
            continue;
        }
        for (i, &a) in clause.iter().enumerate() {
            for &b in &clause[i + 1..] {
                let (x, y) = (a.unsigned_abs(), b.unsigned_abs());
                if x == y {
                    continue;
                }
                let e = if x < y { (x, y) } else { (y, x) };
                edges.insert(e);
            }
        }
        if edges.len() > TD_MAX_EDGES_PER_VAR * num_vars {
            return None;
        }
    }
    let n = num_vars as f64;
    if edges.len() as f64 > TD_MAX_DENSITY * n * (n - 1.0) / 2.0 && num_vars > 64 {
        return None;
    }

    // PACE-17 graph format.
    let mut graph = format!("p tw {} {}\n", num_vars, edges.len());
    for (a, b) in &edges {
        graph.push_str(&format!("{a} {b}\n"));
    }

    // FlowCutter is anytime: it improves until stopped. The two-phase driver
    // only reaches this point for instances that survived phase 1, so spend
    // generously — but small graphs still converge almost immediately.
    let adaptive_secs = (1.0 + edges.len() as f64 / 2_000.0).min(budget.as_secs_f64());
    let budget = Duration::from_secs_f64(adaptive_secs);

    let td_text = run_flow_cutter(flow_cutter, &graph, budget)?;
    let td = parse_td(&td_text, num_vars)?;
    Some(scores_from_td(&td, num_vars, decow))
}

/// Run FlowCutter with the graph on stdin, stop at budget, return stdout.
///
/// PACE-17 protocol: the solver prints its best decomposition ON SIGTERM —
/// so the budget stop MUST be SIGTERM (with a grace period to flush), never
/// SIGKILL, or the output is empty.
fn run_flow_cutter(path: &std::path::Path, graph: &str, budget: Duration) -> Option<String> {
    let mut child = Command::new(path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    let pid = child.id();
    child.stdin.take()?.write_all(graph.as_bytes()).ok()?;
    let stdout = child.stdout.take()?;
    // Reader thread accumulates output while we wait out the budget.
    let reader = std::thread::spawn(move || {
        use std::io::Read;
        let mut buf = String::new();
        let mut r = std::io::BufReader::new(stdout);
        let _ = r.read_to_string(&mut buf);
        buf
    });
    let deadline = std::time::Instant::now() + budget;
    let mut termed_at: Option<std::time::Instant> = None;
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Ok(None) => {
                let now = std::time::Instant::now();
                match termed_at {
                    None => {
                        if now >= deadline {
                            // Polite stop: SIGTERM makes it print the best
                            // decomposition found so far.
                            let _ = Command::new("kill")
                                .args(["-TERM", &pid.to_string()])
                                .status();
                            termed_at = Some(now);
                        }
                    }
                    Some(t) => {
                        if now.duration_since(t) > Duration::from_secs(5) {
                            let _ = child.kill();
                            let _ = child.wait();
                            break;
                        }
                    }
                }
                std::thread::sleep(Duration::from_millis(30));
            }
            Err(_) => {
                let _ = child.kill();
                let _ = child.wait();
                break;
            }
        }
    }
    reader.join().ok()
}

struct TreeDecomp {
    /// bags[i] = variable ids (1-based) in bag i.
    bags: Vec<Vec<u32>>,
    /// adjacency between bags.
    adj: Vec<Vec<usize>>,
    width: usize,
}

/// Parse PACE-17 tree-decomposition output; keep the LAST complete
/// decomposition (FlowCutter is anytime and prints improving solutions,
/// each starting with a fresh `s td` header).
fn parse_td(text: &str, num_vars: usize) -> Option<TreeDecomp> {
    let mut complete: Option<TreeDecomp> = None;
    let mut current: Option<(usize, usize, TreeDecomp)> = None; // (nbags, bags_seen, td)
    for line in text.lines() {
        let mut tokens = line.split_whitespace();
        let Some(head) = tokens.next() else { continue };
        match head {
            "c" => {}
            "s" => {
                // Finish any previous complete decomposition first.
                if let Some((nbags, seen, td)) = current.take() {
                    if seen == nbags && nbags >= 1 {
                        complete = Some(td);
                    }
                }
                // s td <#bags> <width+1> <#vertices>
                if tokens.next() != Some("td") {
                    continue;
                }
                let nbags: usize = tokens.next()?.parse().ok()?;
                let width: usize = tokens.next()?.parse::<usize>().ok()?.saturating_sub(1);
                current = Some((
                    nbags,
                    0,
                    TreeDecomp {
                        bags: vec![Vec::new(); nbags + 1],
                        adj: vec![Vec::new(); nbags + 1],
                        width,
                    },
                ));
            }
            "b" => {
                if let Some((nbags, seen, td)) = current.as_mut() {
                    let Some(Ok(id)) = tokens.next().map(str::parse::<usize>) else {
                        continue;
                    };
                    if id == 0 || id > *nbags {
                        current = None;
                        continue;
                    }
                    td.bags[id] = tokens
                        .filter_map(|t| t.parse::<u32>().ok())
                        .filter(|&v| v >= 1 && v as usize <= num_vars)
                        .collect();
                    *seen += 1;
                }
            }
            _ => {
                // Bag-tree edge line: `<bag_a> <bag_b>`.
                if let Some((_, _, td)) = current.as_mut() {
                    let (Ok(a), Some(Ok(b))) = (
                        head.parse::<usize>(),
                        tokens.next().map(str::parse::<usize>),
                    ) else {
                        continue;
                    };
                    if a >= 1 && b >= 1 && a < td.adj.len() && b < td.adj.len() {
                        td.adj[a].push(b);
                        td.adj[b].push(a);
                    }
                }
            }
        }
    }
    if let Some((nbags, seen, td)) = current {
        if seen == nbags && nbags >= 1 {
            complete = Some(td);
        }
    }
    complete
}

/// Centroid-distance scores (sharpsat-td `PrepareTWScore`).
fn scores_from_td(td: &TreeDecomp, num_vars: usize, decow: f64) -> Vec<f64> {
    let nbags = td.bags.len();
    if nbags <= 1 {
        return vec![0.0; num_vars];
    }
    // Subtree sizes over the bag tree from an arbitrary root; centroid = bag
    // minimizing the largest component after removal.
    let root = 1usize;
    let mut order = Vec::with_capacity(nbags);
    let mut parent = vec![0usize; nbags];
    let mut visited = vec![false; nbags];
    order.push(root);
    visited[root] = true;
    let mut i = 0;
    while i < order.len() {
        let u = order[i];
        i += 1;
        for &v in &td.adj[u] {
            if !visited[v] {
                visited[v] = true;
                parent[v] = u;
                order.push(v);
            }
        }
    }
    let reachable = order.len();
    let mut subtree = vec![1usize; nbags];
    for &u in order.iter().rev() {
        if u != root {
            subtree[parent[u]] += subtree[u];
        }
    }
    let mut centroid = root;
    let mut best_worst = usize::MAX;
    for &u in &order {
        let mut worst = reachable - subtree[u];
        for &v in &td.adj[u] {
            if parent[v] == u {
                worst = worst.max(subtree[v]);
            }
        }
        if worst < best_worst {
            best_worst = worst;
            centroid = u;
        }
    }
    // BFS depth from the centroid; a variable's depth is the depth of the
    // first bag (closest to the centroid) containing it.
    let mut depth = vec![usize::MAX; nbags];
    let mut var_depth = vec![usize::MAX; num_vars + 1];
    let mut queue = std::collections::VecDeque::new();
    depth[centroid] = 0;
    queue.push_back(centroid);
    let mut max_depth = 0usize;
    while let Some(u) = queue.pop_front() {
        for &v in &td.bags[u] {
            let vd = &mut var_depth[v as usize];
            if depth[u] < *vd {
                *vd = depth[u];
            }
        }
        max_depth = max_depth.max(depth[u]);
        for &v in &td.adj[u] {
            if depth[v] == usize::MAX {
                depth[v] = depth[u] + 1;
                queue.push_back(v);
            }
        }
    }
    let max_depth = max_depth.max(1);
    // coef = decow * exp(n/width)/n, capped at 1e7 (sharpsat-td weight mode 1)
    let n = num_vars as f64;
    let width = td.width.max(1) as f64;
    let coef = if decow == 0.0 {
        0.0
    } else {
        (decow * (n / width).exp() / n).min(1e7)
    };
    let mut scores = vec![0.0; num_vars];
    for v in 1..=num_vars {
        let d = var_depth[v];
        if d != usize::MAX {
            scores[v - 1] = coef * ((max_depth - d) as f64) / max_depth as f64;
        }
    }
    scores
}

/// Resolve the FlowCutter binary: explicit path, else `AY_FLOWCUTTER` env,
/// else `flow_cutter_pace17` beside the current executable, else PATH.
pub fn find_flow_cutter(explicit: Option<&std::path::Path>) -> Option<std::path::PathBuf> {
    if let Some(p) = explicit {
        if p.exists() {
            return Some(p.to_path_buf());
        }
        return None;
    }
    if let Ok(env) = std::env::var("AY_FLOWCUTTER") {
        let p = std::path::PathBuf::from(env);
        if p.exists() {
            return Some(p);
        }
        return None;
    }
    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            let p = dir.join("flow_cutter_pace17");
            if p.exists() {
                return Some(p);
            }
        }
    }
    // PATH lookup.
    if let Ok(path_var) = std::env::var("PATH") {
        for dir in std::env::split_paths(&path_var) {
            let p = dir.join("flow_cutter_pace17");
            if p.exists() {
                return Some(p);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_simple_td_and_scores() {
        // Path graph 1-2-3-4-5: bags {1,2},{2,3},{3,4},{4,5} in a path.
        let td_text = "s td 4 2 5\nb 1 1 2\nb 2 2 3\nb 3 3 4\nb 4 4 5\n1 2\n2 3\n3 4\n";
        let td = parse_td(td_text, 5).expect("parses");
        assert_eq!(td.width, 1);
        let scores = scores_from_td(&td, 5, 100.0);
        // Middle variable(s) should have the highest score (centroid).
        let mid = scores[2];
        assert!(mid >= scores[0] && mid >= scores[4], "{scores:?}");
        assert!(scores.iter().all(|&s| s >= 0.0));
    }

    #[test]
    fn td_guard_skips_huge_inputs() {
        let clauses = vec![vec![1, 2]];
        assert!(td_scores(
            200_000,
            &clauses,
            Duration::from_millis(1),
            100.0,
            std::path::Path::new("/nonexistent"),
        )
        .is_none());
    }
}
