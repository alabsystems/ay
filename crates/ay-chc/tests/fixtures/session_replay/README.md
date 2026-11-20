# HornSmt session replay corpora (CHC-COMP 2026 Rung 1, design §10.1)

Each `<key>/` holds one dumped PDR query stream:

* `queries.smt2.gz` — the `q_<seq>_<thread>.smt2` scripts of the dump,
  concatenated in name order, each preceded by a `;; @file <name>` line
  (gzip; the replay test expands it with the system `gzip -dc`).
* `index.tsv` — the dump's index. Microbenchmark layout (om1relays,
  ak_s1min): `seq thread path result elapsed_ms nconj bytes t_ms n_renamed`;
  session-recorder layout (`AY_CHC_SESSION_DUMP`): `seq thread lane_result
  elapsed_us n_conj n_delta n_assumptions decisions unknown_reason`. The
  replay reads the verdict column (`result` / `lane_result`) as the
  "recorded" opinion.

| key | instance | source |
|---|---|---|
| om1relays | sally `oral_messages/om1_with_relays_agreement_000` (LRA) | microbenchmark dump, 3,000 scripts (the development design notes at `9598c4206`) |
| ak_s1min | sally `azadmanesh-kieckhafer/scenario1_min_received_000` (LRA) | microbenchmark dump, 727 scripts |
| s3_srvr_4 | vmt `cav12/s3_srvr_4.cil_000` (LRA) | `AY_CHC_SESSION_DUMP` recorder, Rung 1 board run (binary `ay-sess1-20260922` = b797bf825, 60 s, `--competition`), 903 routed queries |
| pushpop_repros | `repros/lra-pushpop-false-unsat-2026-09-18/*.smt2` (plain files) | the ay-dpll inc-engine false-UNSAT repros; replayed as push/pop scripts |

Regenerate a corpus: `AY_CHC_SESSION=1 AY_CHC_SESSION_DUMP=<dir> ay --chc --competition --timeout 60000 <instance>`
then `scripts/chc_session_replay.py pack <dir> <key>`; `scripts/chc_session_replay.py run <key>` replays it.
