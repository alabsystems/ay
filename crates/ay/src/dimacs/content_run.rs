// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn run_dimacs_from_content_impl(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    input_path: Option<&str>,
) {
    run_dimacs_from_content_impl_body(content, stats_cfg, proof_config, input_path)
}
