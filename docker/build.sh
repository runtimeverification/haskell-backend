#!/usr/bin/env bash
docker build --build-arg K_COMMIT=$(cat deps/k_release | cut --delimiter="-" --field="2") --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) -t kore .
