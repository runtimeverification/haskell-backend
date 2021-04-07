#!/bin/sh
./test-add0.sh --rts-statistics statistics-add0
./test-branching-invalid.sh --rts-statistics statistics-branching-invalid
./test-branching-no-invalid.sh --rts-statistics statistics-branching-no-invalid
./test-pop1.sh --rts-statistics statistics-pop1
./test-straight-line-no-invalid.sh --rts-statistics statistics-straight-line-no-invalid
./test-straight-line.sh --rts-statistics statistics-straight-line
./test-sum-to-n.sh --rts-statistics statistics-sum-to-n
./test-sumTo10.sh --rts-statistics statistics-sumTo10

cat \
    statistics-add0 \
    statistics-branching-invalid \
    statistics-branching-no-invalid \
    statistics-pop1 \
    statistics-straight-line-no-invalid \
    statistics-straight-line \
    statistics-sum-to-n \
    statistics-sumTo10 \
    > ./statistics

rm \
    statistics-add0 \
    statistics-branching-invalid \
    statistics-branching-no-invalid \
    statistics-pop1 \
    statistics-straight-line-no-invalid \
    statistics-straight-line \
    statistics-sum-to-n \
    statistics-sumTo10