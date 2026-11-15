# Native final-exec policy

`FootprintLimit` prepares equal positive active/inactive fatal footprint limits
using Apple's native spawn-attribute setter. It does not launch, reserve memory,
measure RSS, install a sandbox, or manufacture a policy receipt. The launch owner
must apply it at the final payload exec and retain actual child custody.

The ABI and fatal flags follow Apple's maintained
[libsyscall setter](https://github.com/apple-oss-distributions/xnu/blob/main/libsyscall/wrappers/spawn/posix_spawn.c)
and [spawn attributes](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/sys/spawn_internal.h).
Setter success alone is no evidence of a live child's installed policy or of a
hard RSS quota. Unsupported native policy must remain an explicit refusal.

On macOS, `ExecutionSeal` installs one of two fixed self-restrictions: no fork,
or no fork and no exec. There is no caller-supplied sandbox profile. Installation
is irreversible; an error is not a rollback and must not trigger an ordinary
payload fallback. `fork_denied(pid)` is only a native observation and requires
separate process-lifetime authentication. There is deliberately no global
no-exec query API: `sandbox_check(process-exec)` returned EINVAL on the qualified
Mac with both no filter and a path filter. The fixed no-exec profile is instead
qualified by an actual owned child's rejected fork and `/usr/bin/true` exec.
Neither its local installation result nor an observation grants resources.

Native qualification also found that installing a second sandbox after the
no-fork profile is refused. Managed final-payload integration must not assume
that a prelude's first sandbox can be tightened after exec.
