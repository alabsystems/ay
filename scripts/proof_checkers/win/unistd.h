/* Minimal <unistd.h> shim for building UNMODIFIED upstream dsr-trim sources
 * with MSVC. Maps only the POSIX names the CRT spells differently; no
 * verification logic is involved. */
#ifndef AY_WIN_UNISTD_SHIM_H
#define AY_WIN_UNISTD_SHIM_H
#include <io.h>
#ifndef isatty
#define isatty _isatty
#endif
#ifndef fileno
#define fileno _fileno
#endif
#endif
