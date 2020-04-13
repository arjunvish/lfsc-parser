#!/bin/bash
for i in *.smt2
do
  j=${i/smt2/plf}
  k=./Proofs/$j
  echo $k
  cvc4 --dump-proofs --no-lfsc-letification $i | tail -n+2 > $k
done
