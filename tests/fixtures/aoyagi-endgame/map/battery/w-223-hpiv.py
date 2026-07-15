#!/usr/bin/env python3
# kills: route-b-s3floor
# config: M=(2,2,3), u=1; hpiv demands minAdm([1,3]) <= u*min(2,3)
# provenance: seat1 route-B audit (tailMinWidth incl. M1 ceiling)
"""Refuter for the route-B S3-floor route.

route-B's hpiv step at M=(2,2,3), u=1 demands minAdm([1,3]) ≤ u·min(2,3), i.e.
3 ≤ 2. That is false, so hpiv cannot hold and the route hits its ceiling. Exit 1
(killed) when the demanded inequality is FALSE."""
import sys

from _minadm import minAdm

demand = minAdm((1, 3)) <= 1 * min(2, 3)   # 3 <= 2  -> False
print(f"hpiv demands minAdm([1,3]) <= 1*min(2,3): {minAdm((1,3))} <= {1*min(2,3)} = {demand}")
sys.exit(1 if not demand else 0)
