#!/bin/bash
# Run all tests in ../../test/resources,
# except string tests and exception tests.

echo "Kompiling ..."
kompile --backend java kore.k

total=0
fail=0
pass=0

echo "Testing ..."
for f in ../../test/resources/*.kore
do
  if [[ $f = *"exception"* ]] || [[ $f = *"string"* ]]
  then
    continue 
  fi
  (( total += 1 ))
  echo "Parsing $f"
  krun --output none $f
  if [ $? -eq 0 ]
  then
    (( pass += 1 ))
  else
    (( fail += 1 ))
  fi
  echo "----- pass / total : $pass/ $total ----"
done
