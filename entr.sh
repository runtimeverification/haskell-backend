#!/usr/bin/env bash

# entr.sh: Run a command when project files change.

# Dependencies:
#   entr: https://github.com/eradman/entr
#   fd: https://github.com/sharkdp/fd

last=2  # last exit code

# entr runs the specified command whenever the listed files change,
# and exits with code 2 when a file is added to any watched directory.
# The loop restarts entr as long as it exits because of a new file.
# If entr exits for any other reason, the loop is terminated.
# This way, the script exits if the user interrupts it (for example).
while test "$last" -eq 2
do
    fd '(package.yaml|.*\.hs)' | entr -d -s "${@:-./hooks.sh}"
    last=$?
done