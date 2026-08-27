// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn dimacs_run_stats_json(
    run_stats: &stats_output::RunStatistics,
    route_profile: VariantRouteProfile,
) -> String {
    dimacs_run_stats_json_body(run_stats, route_profile)
}
