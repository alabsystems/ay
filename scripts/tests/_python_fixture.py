# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Launch executable Python fixtures with this interpreter, including spaced paths."""
import shlex
import sys


def python_header():
    # A kernel shebang cannot quote sys.executable. The shell exec is inside a
    # Python string, so the same file remains the fixture's Python program.
    return (
        "#!/bin/sh\n"
        f"'''exec' {shlex.quote(sys.executable)} \"$0\" \"$@\"\n"
        "' '''\n"
    )


def python_path(root):
    """A minimal POSIX fixture PATH with the exact running Python available."""
    tools = root / "python-tools"
    tools.mkdir(exist_ok=True)
    launcher = tools / "python3"
    launcher.write_text("#!/bin/sh\nexec " + shlex.quote(sys.executable) + ' "$@"\n')
    launcher.chmod(0o755)
    return str(tools) + ":/usr/bin:/bin"
