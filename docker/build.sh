#!/usr/bin/env bash
docker build --build-arg K_COMMIT=$(cat deps/k_release) --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) -t kore .
