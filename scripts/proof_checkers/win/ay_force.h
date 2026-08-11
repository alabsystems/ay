/* Force-included compatibility header for building UNMODIFIED upstream
 * dsr-trim/lsr-check sources with MSVC.
 *   - getc_unlocked/putc_unlocked: POSIX unlocked stdio; MSVC spells them
 *     _getc_nolock/_putc_nolock, identical semantics for a single-threaded
 *     reader.
 * Neither affects proof-checking logic. `inline` is neutralised on the command
 * line (/Dinline=) because the sources use the C99 extern-inline pattern that
 * MSVC's C mode does not emit definitions for; the sources have no inline
 * definitions in headers, so this only turns them into ordinary functions. */
#ifndef AY_FORCE_COMPAT_H
#define AY_FORCE_COMPAT_H
#include <stdio.h>
#ifndef getc_unlocked
#define getc_unlocked(s) _getc_nolock(s)
#endif
#ifndef putc_unlocked
#define putc_unlocked(c, s) _putc_nolock((c), (s))
#endif
#endif
