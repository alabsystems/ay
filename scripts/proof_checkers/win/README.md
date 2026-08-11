# Building the proof checkers on Windows

`dpr-trim` and `dsr-trim` are vendored under `third_party/` but are POSIX C, so
until now no AY certificate could be validated on a Windows machine. This
directory supplies the missing platform headers so both build with MSVC.

    scripts\proof_checkers\win\build.bat

Produces `bin\dpr-trim.exe` and `bin\dsr-trim.exe`.

## The checker sources are never patched

A checker is the trust root for a certificate claim: patching one to make a proof
pass destroys the thing that makes the proof worth anything. So the upstream
sources are compiled **byte-identical**, and everything Windows lacks is supplied
on the include path instead:

| shim | why |
| --- | --- |
| `sys/time.h` | `struct timeval` + `gettimeofday`, used only for elapsed-time reporting and the optional timeout |
| `unistd.h` | `isatty` / `fileno`, which the CRT spells with a leading underscore |
| `getopt.h` | `getopt` / `getopt_long`; argument parsing only |
| `ay_force.h` | `getc_unlocked` / `putc_unlocked` -> `_getc_nolock` / `_putc_nolock` |

None of these is reachable from the checking logic. A bug in the `getopt` shim
fails loudly (wrong file opened, or an error exit); it cannot cause an invalid
proof to be accepted, because the verdict comes from code the shims never touch.

Two build details worth knowing:

- `/Dinline=` is required for `dsr-trim`. Its sources use the C99 extern-inline
  pattern — definition in a `.c`, plain prototype in a `.h` — which GCC emits a
  symbol for and MSVC's C mode does not, giving `unresolved external symbol
  get_witness_size` and friends. No inline functions are defined in the sources'
  headers, so this only turns them into ordinary functions.
- Because of that, the shims deliberately avoid `<windows.h>` and `<winsock2.h>`:
  those *do* define inline functions, which `/Dinline=` would then duplicate
  (`SocketNotificationRetrieveEvents already defined`). `sys/time.h` uses
  `_ftime64` from the CRT instead.

## Use the right checker — this is not cosmetic

**`dpr-trim` checks *propagation* redundancy (PR/DPR). `dsr-trim` checks
*substitution* redundancy (SR).** AY's aux-free symmetry route emits **SR**, so
`dpr-trim` reports `s NOT VERIFIED` on a perfectly valid AY certificate. That is
the checker refusing a proof system it does not implement, not a defect in the
proof.

Measured on a classic PHP(6) certificate from
`AY_SAT_COMPOSITE_SYMMETRY=1 AY_SAT_SYMMETRY_SR_AUXFREE=1 ay solve --proof`:

    dpr-trim  ->  s NOT VERIFIED   (failed at proof line 32)
    dsr-trim  ->  s VERIFIED UNSAT

Usage:

    bin\dsr-trim.exe <cnf> <dsr-proof> [lsr-output]
    bin\dpr-trim.exe <cnf> <drat-or-dpr-proof>

## Why this exists

It caught a real soundness defect. A change extending the PHP detector to the
*functional* encoding (commit `ce29f6adb`) produced answers that matched ground
truth and a certificate that looked fine — and `dsr-trim` rejected it with
`No UP contradiction for RAT clause 2751`. The emitted SR units were not
redundant, which on a satisfiable instance could have produced a false UNSAT.
The change was reverted in `39b95cccd`.

An unchecked certificate is not evidence. Run one of these against any proof
before a soundness or competition claim rests on it.
