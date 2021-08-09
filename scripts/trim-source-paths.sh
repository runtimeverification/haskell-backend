#!/bin/sh

case $(uname) in
    # MacOS
    Darwin*)
        sed \
            -e 's|/home/jenkins-slave/workspace/[^/]\+/||' \
            -i '' "$@"
        ;;
    # This should be Linux
    *)
        sed \
            -e 's|/home/jenkins-slave/workspace/[^/]\+/||' \
            -i "$@"
        ;;
esac