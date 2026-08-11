/* Minimal <sys/time.h> shim so UNMODIFIED upstream dpr-trim / dsr-trim sources
 * compile with MSVC.
 *
 * Their only POSIX dependency here is wall-clock timing: `struct timeval` and
 * `gettimeofday`, used for elapsed-time reporting and the optional timeout.
 * NOTHING in the verification logic touches it. Supplying this header on the
 * include path leaves the checker sources byte-identical to upstream, which
 * matters: the checker is the trust root for a certificate claim and must not
 * be patched to make a proof pass.
 *
 * Deliberately self-contained — it pulls in only <sys/timeb.h> from the CRT and
 * never <windows.h>/<winsock2.h>, because those define inline functions and the
 * dsr-trim build neutralises `inline` (its sources use the C99 extern-inline
 * pattern MSVC's C mode does not emit definitions for).
 */
#ifndef AY_WIN_SYS_TIME_SHIM_H
#define AY_WIN_SYS_TIME_SHIM_H

#include <sys/timeb.h>
#include <sys/types.h>

/* MSVC declares struct timeval only in winsock2.h, which we must not include. */
#ifndef _WINSOCK2API_
#ifndef _TIMEVAL_DEFINED
#define _TIMEVAL_DEFINED
struct timeval {
  long tv_sec;
  long tv_usec;
};
#endif
#endif

static int gettimeofday(struct timeval *tv, void *tz) {
  struct __timeb64 tb;
  (void)tz;
  if (tv == 0) {
    return -1;
  }
  _ftime64(&tb);
  tv->tv_sec = (long)tb.time;
  tv->tv_usec = (long)tb.millitm * 1000;
  return 0;
}

#endif /* AY_WIN_SYS_TIME_SHIM_H */
