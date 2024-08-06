#! /bin/bash

set -eu

GNUPLOT="gnuplot -p"
#GNUPLOT=cat

INPUT=${1?"Need an input file"}


$GNUPLOT <<EOF

set style data histogram
set style histogram rowstacked gap 1
set style fill solid border -1
set boxwidth 0.9
set xtics rotate by 90 right

plot "$INPUT" \
         using 3:xtic(2) lt rgb "blue" title "Booster request time", \
      "" using 4:xtic(2) lt rgb "web-blue" title "Kore request time", \
      "" using 5:xtic(2) lt rgb "dark-violet" title "Booster simpl. time", \
      "" using 6:xtic(2) lt rgb "violet" title "Kore simpl. time"
EOF
