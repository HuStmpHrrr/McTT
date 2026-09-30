#!/bin/bash
# Build the experiment files in order. Run from anywhere.
cd /local/home/zhonhu/workspace/McTT/theories
for f in "$@"; do
  echo "== $f"
  rocq c -R . Mctt -R ../experiments/extension_invariance ExtInv ../experiments/extension_invariance/$f.v 2>&1 | grep -v "Hint Db\|mismatched-hint-db\|characters 0-5[0-9]:$"
done
