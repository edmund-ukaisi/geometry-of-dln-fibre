#!/usr/bin/env python3
# guards: box-threshold
# config: minAdm ground truths [1,3];[2,2,2];[2,2,3];[3,3,3];[3,3,4];[6,6,6]
# provenance: source worked examples (paper §minAdm) — battery genesis seed
"""Ground-truth self-test for the minAdm recursion the whole battery rests on.

Exit 0 = the recursion reproduces every worked example (box-threshold's
arithmetic foundation survives). A mismatch raises (exit 1 = the foundation is
broken)."""
import sys

from _minadm import self_test

self_test()
print("minAdm self-test: all 6 ground truths reproduced")
sys.exit(0)
