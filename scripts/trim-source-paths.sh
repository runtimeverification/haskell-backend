#!/bin/sh

sed \
    -e 's|/home/jenkins-slave/workspace/[^/]\+/||' \
    -i "$@"
