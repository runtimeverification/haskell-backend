#!/usr/bin/env bash
# Run command in Docker
# Usage: ./docker/run.sh make test
docker run --rm --mount src=$(pwd),target=/home/user/kore,type=bind --workdir=/home/user/kore kore "$@"
