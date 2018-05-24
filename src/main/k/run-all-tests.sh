#!/bin/bash

echo "Kompiling ..."
kompile --backend java kore.k

total=0
error=0

echo "Testing ..."
for f in ../../test/resources/*.kore
do
  echo "Parsing $f"
  krun --output none $f
  (( total += 1 ))
  if [ $? -eq 0 ]
  then
    :
  else
    (( error += 1 ))
  fi
done

echo "Results (errors): $ERROR / $TOTAL"
