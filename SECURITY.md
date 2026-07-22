# Security Policy

## Coverage

Security maintenance targets the most recent tagged release on the active 0.x
line. The `main` branch is patched opportunistically in the gaps between
releases. Historical snapshots, scratch worktrees, and anything checked out
under `reference/` are not maintained release artifacts and are out of scope.

## How To Report

Please do not file security problems as public GitHub issues.

Email `andrewyates.name@gmail.com` and include as much of the following as you
can:

- what the problem is and why it matters,
- the commands, APIs, or files involved,
- steps to reproduce,
- the exact commit hash or release tag you were running.

If the report needs to stay confidential beyond plain email, say so in your
first message and we can set up an encrypted channel.

## Handling

Reports are reviewed when time allows. Anything that looks valid is first
investigated in private, and a fix may land before the details are made public
if the severity calls for it.

## In And Out Of Scope

Examples of issues this policy covers:

- memory-safety or FFI-boundary faults,
- arbitrary command execution or sandbox escapes in shipped tooling,
- defects in proof or result validation that could silently undermine trust,
- packaging or release flaws that leak secrets or ship unsafe content.

Examples that are not treated as coordinated-disclosure security issues:

- benchmark-only regressions with no security consequence,
- problems limited to local `reference/` artifacts that never ship in a release,
- behavior in third-party forks unless it also reproduces on upstream AY.
