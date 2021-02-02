#!/usr/bin/env bash
# Run command in Docker
docker run --rm --mount src=$(pwd),target=/home/user/kore,type=bind --workdir=/home/user/kore kore "$@"