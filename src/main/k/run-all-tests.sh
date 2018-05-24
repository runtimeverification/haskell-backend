#!/bin/bash

echo "Kompiling ..."
kompile --backend java kore.k

total=0
fail=0
pass=0

echo "Testing ..."
for f in ../../test/resources/*.kore
do
  (( total += 1 ))
  echo "Parsing $f"
  krun --output none $f
  if [ $? -eq 0 ]
  then
    (( pass += 1 ))
  else
    (( fail += 1 ))
  fi
  echo "----- $pass/ $total ----"
done
