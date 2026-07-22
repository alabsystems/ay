# SAT-COMP campaign benchmark harness

Reusable AY-vs-Kissat measurement + attribution tools for the SAT-COMP improvement
campaign. See the development design notes and memory
`sat-comp-win-goal` / `sat-improvement-loop-state`.

- `sat_compare.py <dir|list> <timeout_s> <out.json> [jobs]` — run AY (`--no-proof -t`)
  + Kissat on a CNF set, cross-check verdicts (flags soundness disagreements),
  compute solved + PAR-2, list the gap (Kissat solves / AY doesn't). jobs=1 for
  faithful timing (KEEP MACHINE QUIET during runs).
- `download_2025.py <hash|fn list> <outdir> <N> <max_xz_bytes>` — stratified GBD
  download of SAT-COMP main_2025 by content hash.
- `attribute.py <results.json>` — bucket instances, gap-by-family, slowdown ratios.
- `audit.py` — BVE-soundness audit (known-verdict corpus; flags wrong answers,
  counts Unknown regressions).
- `baseline_sat2025_t40.json` — session-01 baseline (AY 11 vs Kissat 15 @40s, 0 wrong).

Env: AY_BIN, KISSAT_BIN. Reference Kissat: build arminbiere/kissat. Independent
proof checkers: marijnheule/drat-trim (lrat-check).

Get main_2025 hash list:
  curl https://benchmark-database.de/getdatabase/track_main_2025 -o gbd.sqlite
  sqlite3 gbd.sqlite "SELECT t.hash,f.value FROM track t LEFT JOIN filename f ON t.hash=f.hash WHERE t.value='main_2025'"
