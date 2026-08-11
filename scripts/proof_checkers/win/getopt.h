/* Minimal getopt / getopt_long for MSVC, so the UNMODIFIED upstream dsr-trim
 * sources compile on Windows.
 *
 * Scope note: this replaces only ARGUMENT PARSING. None of dsr-trim's proof
 * checking touches it, and the checker's own sources stay byte-identical to
 * upstream — important, because the checker is the trust root for any
 * certificate claim and must not be patched to make a proof pass.
 *
 * A parsing bug here fails LOUDLY (wrong file opened, or an error exit), it
 * cannot cause an invalid proof to be accepted: the verdict comes from the
 * checking code, which this never touches.
 *
 * Supports the subset dsr-trim uses: short options with optional ':'/'::'
 * argument suffixes, long options (no_argument / required_argument /
 * optional_argument), "--" terminator, and "--name=value" form.
 */
#ifndef AY_WIN_GETOPT_SHIM_H
#define AY_WIN_GETOPT_SHIM_H

#include <stdio.h>
#include <string.h>

#define no_argument 0
#define required_argument 1
#define optional_argument 2

struct option {
  const char *name;
  int has_arg;
  int *flag;
  int val;
};

static char *optarg = 0;
static int optind = 1;
static int opterr = 1;
static int optopt = 0;

/* Index within a bundled short-option cluster such as "-abc". */
static int ay_optpos = 1;

static int ay_getopt_impl(int argc, char *const argv[], const char *optstring,
                          const struct option *longopts, int *longindex) {
  const char *p;
  char *arg;

  optarg = 0;
  if (longindex) {
    *longindex = -1;
  }

  if (optind >= argc) {
    return -1;
  }
  arg = argv[optind];
  if (arg == 0 || arg[0] != '-' || arg[1] == '\0') {
    return -1; /* non-option: stop, matching the POSIX default ordering */
  }
  if (arg[1] == '-' && arg[2] == '\0') {
    optind++; /* "--" terminator */
    return -1;
  }

  /* Long option: "--name" or "--name=value". */
  if (arg[1] == '-' && longopts) {
    const char *name = arg + 2;
    const char *eq = strchr(name, '=');
    size_t n = eq ? (size_t)(eq - name) : strlen(name);
    int i;
    for (i = 0; longopts[i].name; i++) {
      if (strlen(longopts[i].name) == n &&
          strncmp(longopts[i].name, name, n) == 0) {
        optind++;
        if (longindex) {
          *longindex = i;
        }
        if (longopts[i].has_arg == required_argument) {
          if (eq) {
            optarg = (char *)(eq + 1);
          } else if (optind < argc) {
            optarg = argv[optind++];
          } else {
            if (opterr) {
              fprintf(stderr, "%s: option '--%s' requires an argument\n",
                      argv[0], longopts[i].name);
            }
            optopt = longopts[i].val;
            return '?';
          }
        } else if (longopts[i].has_arg == optional_argument) {
          optarg = eq ? (char *)(eq + 1) : 0;
        } else if (eq) {
          if (opterr) {
            fprintf(stderr, "%s: option '--%s' takes no argument\n", argv[0],
                    longopts[i].name);
          }
          optopt = longopts[i].val;
          return '?';
        }
        if (longopts[i].flag) {
          *longopts[i].flag = longopts[i].val;
          return 0;
        }
        return longopts[i].val;
      }
    }
    if (opterr) {
      fprintf(stderr, "%s: unrecognized option '%s'\n", argv[0], arg);
    }
    optind++;
    return '?';
  }

  /* Short option, possibly bundled: "-a", "-abc", "-ovalue", "-o value". */
  optopt = arg[ay_optpos];
  p = strchr(optstring, optopt);
  if (optopt == ':' || p == 0) {
    if (opterr) {
      fprintf(stderr, "%s: invalid option -- '%c'\n", argv[0], optopt);
    }
    if (arg[++ay_optpos] == '\0') {
      optind++;
      ay_optpos = 1;
    }
    return '?';
  }
  if (p[1] == ':') {
    int optional = (p[2] == ':');
    if (arg[ay_optpos + 1] != '\0') {
      optarg = (char *)&arg[ay_optpos + 1];
      optind++;
    } else if (optional) {
      optarg = 0;
      optind++;
    } else if (optind + 1 < argc) {
      optarg = argv[optind + 1];
      optind += 2;
    } else {
      if (opterr) {
        fprintf(stderr, "%s: option requires an argument -- '%c'\n", argv[0],
                optopt);
      }
      optind++;
      ay_optpos = 1;
      return '?';
    }
    ay_optpos = 1;
    return optopt;
  }
  if (arg[++ay_optpos] == '\0') {
    optind++;
    ay_optpos = 1;
  }
  return optopt;
}

static int getopt(int argc, char *const argv[], const char *optstring) {
  return ay_getopt_impl(argc, argv, optstring, 0, 0);
}

static int getopt_long(int argc, char *const argv[], const char *optstring,
                       const struct option *longopts, int *longindex) {
  return ay_getopt_impl(argc, argv, optstring, longopts, longindex);
}

#endif /* AY_WIN_GETOPT_SHIM_H */
