# shellcheck shell=bash
# ay-script: sat26-memory-limit
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# The SAT Competition 2026 memory limit per solver run: "32GB" in the rules,
# recorded in competition/sat_profile_matrix.json as
# sat26_compliance.main_track_contract.memory_limit_gb = 32. The rules do not
# say whether that is GB or GiB, so the solver side reads it conservatively as
# 32,000,000,000 bytes (owner decision, 2026-09-12).
#
# Every SAT-COMP launcher passes it as a CEILING, never as an override:
#
#   --memory-ceiling-bytes N  ay's own limit becomes 90% of the smallest of N,
#                             the cgroup memory limit it runs under (its own
#                             cgroup and each visible ancestor), its RLIMIT_AS
#                             and RLIMIT_DATA, and the macOS govern kernel
#                             budget, so it is never looser than a limit the
#                             kernel already shows (ay_sys::memory_ceiling).
#   GOVERN_AY_MB=K            the kernel-held budget ay arms for itself on
#                             macOS (a no-op on Linux), otherwise physical
#                             RAM / 16. K is N rounded up to MiB, so it never
#                             binds below the ceiling, and the kernel kill
#                             line sits at the limit, about 11% above ay's
#                             own limit of 90% of it.
#
# Launchers also unset AY_GOVERN_ARMED and AY_ROOT_PID, so a runner started
# from an already-governed ay re-arms with this budget. The single-process
# launchers unset AY_CONCURRENCY and the test-harness markers (NEXTEST,
# NEXTEST_EXECUTION_MODE, AY_TEST), since an inherited value would split the
# ceiling. A launcher that races several ay processes in one job sets
# AY_CONCURRENCY so the shared bounds are split between them (ay_portfolio.sh).
#
# Sourced by prepare_sat26_submission.sh (the generated run.sh and the
# build-time PGO training run) and by ay_portfolio.sh. `ay submission generate
# sat` carries the same value as SAT_COMP_2026_MEMORY_LIMIT_BYTES, locked to
# this line by a unit test; scripts/tests/test_sat26_memory_pin.py fails if a
# generated runner omits the pin. scripts/sweep.py keeps the GENEROUS reading
# (32768 MiB) on purpose: it decides whether a memout under a harness cap is
# unmeasured, and there the safe side is the larger reading.
SAT26_MEMORY_LIMIT_BYTES=32000000000
SAT26_GOVERN_AY_MB=$(( (SAT26_MEMORY_LIMIT_BYTES + 1048575) / 1048576 ))
