#!/usr/bin/env bash
# Run each W8 verdict fixture through compiler_consumer -Z deductive-verify-full and report the
# VERBOSE verdict line (ground truth). Defaults to the stage1 compiler_consumer built at the
# gap-1 HEAD; override with TRUSTC=.../stage2/bin/compiler_consumer.
#
# IMPORTANT: rely on the printed verdict line, NOT the process exit code. Under
# the standalone (non-cargo) invocation the refutation/proof is always printed,
# but the exit code can be unstable across runs due to model_checker_consumer/verification_consumer owner
# reconciliation ordering. Also run each file in its OWN shell to avoid the
# same-shell run-order interaction.
#
# Expected verdicts:
#   repr_ge_pos.rs            -> PROVED (model_checker_consumer PdrInvariant)            [representable, non-vacuous POS]
#   repr_ge_neg.rs            -> REFUTED (verified_counterexample = true)  [representable, non-vacuous NEG]
#   blocker_call_in_ensures.rs-> UNSUPPORTED "lowered to boolean true" -> empty-counterexample fail-closed
#                                (the call-node blocker; NOT a real refutation)
#   eval_constraint_{pos,neg} -> same call-node blocker (postcondition calls eval_terms)
set -u
TRUST_ROOT="${TRUST_ROOT:-$HOME/trust}"
TRUSTC="${TRUSTC:-$(ls "$TRUST_ROOT"/build/*/stage1/bin/compiler_consumer 2>/dev/null | head -1)}"
if [ -z "$TRUSTC" ] || [ ! -x "$TRUSTC" ]; then
  echo "no stage1 compiler_consumer found under $TRUST_ROOT/build/*/stage1/bin (build one with ./x build in the trust checkout, or set TRUSTC=)" >&2
  exit 1
fi
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
for f in "$DIR"/*.rs; do
  name="$(basename "$f")"
  out="$("$TRUSTC" -Z deductive-verify-full --edition 2021 --crate-type lib "$f" -o /tmp/w8_"$name".rlib 2>&1)"
  verdict="$(printf '%s\n' "$out" | grep -iE "Trust verification:|verified_counterexample|lowered to boolean true|proved obligation .* with Pdr|FAILED \(|aborting" | head -3 | tr '\n' '|')"
  echo "=== $name"
  echo "    $verdict"
done
