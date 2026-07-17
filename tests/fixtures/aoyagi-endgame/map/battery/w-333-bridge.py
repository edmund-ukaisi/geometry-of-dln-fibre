#!/usr/bin/env python3
# kills: route-shellspine-bridge
# config: M=(3,3,3), compare minAdm/2 against block-cost 3*3/2
# provenance: threads/genm-routeverify/routeverify-cert.md (five-fork night)
"""Refuter for the shell-spine bridge route.

The bridge would need shell-j ≤ pivotShell RHS. At (3,3,3): minAdm/2 = 3.5 but
the block cost 3·3/2 = 4.5, so the gap [3.5, 4.5) is nonempty and a c'=4 refuter
exists. Exit 1 (killed) when the gap is nonempty."""
import sys

from _minadm import minAdm

lhs = minAdm((3, 3, 3)) / 2          # 3.5
rhs = 3 * 3 / 2                       # 4.5
gap_nonempty = lhs < rhs
print(f"minAdm([3,3,3])/2 = {lhs}  block 3*3/2 = {rhs}  gap_nonempty={gap_nonempty}")
sys.exit(1 if gap_nonempty else 0)
