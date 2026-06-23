import numpy as np
# LOAD-BEARING: does the iterated-rank-1 reading give the SAME achiever-leaf codim (so the value
# foldFamily_iInf is unaffected), or does the node-count difference corrupt the codim-list?
#
# The achiever leaf's threshold = ½·min(codim-list). For the value to be ½·minAdm, the codim-list's
# MIN must = minAdm (the C=∃ achiever). The codim-list = the per-divisor codims (one appendDivisor per
# recursion node). Whether the C1 2→0 is ONE rank-2 divisor (codim c_full) or TWO rank-1 divisors
# (codims c_A, c_B), the achiever's BINDING codim (the min) must be minAdm.
#
# CRITICAL: the divisor codim = (Mval M₀ T).toNat for the stratum T resolved at that node (PivotWitness).
# Under iterated rank-1, EACH rank-1 step resolves an INTERMEDIATE stratum (a finer rank pattern). The
# codims of the intermediate strata vs the single rank-2 stratum — do they preserve the min=minAdm?
#
# The key: the achiever T* is reached by the WHOLE path; its binding divisor (the codim = Mval M₀ T*)
# is what gives minAdm. Whether the path has 2 or 3 nodes, the BINDING node (the one with codim=minAdm)
# must be present. Under iterated rank-1, the intermediate strata have codims ≥ minAdm (they're admissible,
# C≥), and the achiever's binding stratum is still reached (it's the deepest/minimal one).
#
# Let me check: for the cascade path to T*, does the iterated rank-1 refinement KEEP the achiever's
# binding codim = minAdm in the codim-list? The min of the codim-list = min over the path's strata codims.
# Iterated rank-1 ADDS intermediate strata (finer), each codim ≥ minAdm. So the MIN is unchanged IF the
# binding stratum (codim minAdm) is still on the path — which it is (the path still reaches T*).
print("Codim consistency check (iterated rank-1 vs rank-r):")
print("""
  The achiever leaf's value = ½·MIN(codim-list). The codim-list = per-node codims (Mval M₀ T_node).
  - Iterated rank-1: MORE nodes (finer intermediate strata), each codim = Mval of an admissible
    intermediate T ⟹ each ≥ minAdm (C≥). The MIN is still minAdm IFF the binding stratum (the one
    with Mval = minAdm) is on the path.
  - rank-r: FEWER nodes (coarser), the binding stratum's codim directly.
  Either way, the achiever path REACHES T* (the cascade descends to it), and T*'s binding divisor has
  codim = Mval M₀ T* = minAdm. The intermediate rank-1 strata have codim ≥ minAdm (they don't beat it).
  ⟹ MIN(codim-list) = minAdm in BOTH readings. The VALUE is UNAFFECTED by the node-count choice.
""")
# The ONLY thing that differs: the codim-list LENGTH (3 vs 2 entries) and the intermediate codims.
# For C≥ (every divisor ≥ minAdm via PivotWitness), the iterated reading needs each intermediate rank-1
# stratum to be admissible with Mval ≥ minAdm — which holds (intermediate strata are admissible, deeper).
print("So pp2's flag is a NODE-COUNT/codim-list-LENGTH choice, NOT a value or termination issue:")
print("  - Termination: both terminate (ΣM drops ≥2 per node).")
print("  - Value: both give MIN(codim-list)=minAdm (the binding stratum is reached either way).")
print("  - C≥: both satisfy it (every node's codim = Mval of an admissible stratum ≥ minAdm).")
print("  The choice affects: node count (3 vs 2), codim-list length, and which PivotWitness strata appear.")
print()
print("RECOMMENDATION: follow the BANKED schurState (rank-1, drop=1/vertex) ⟹ ITERATED rank-1 (3 nodes")
print("for the witness). It's the live def; defining a rank-r variant is extra surface for no value gain.")
print("The formaliser's per-node ΣM-drop = 2 (uniform, simplest); node count = Σ(rank drops) = total rank")
print("dropped along the path. For t=(3,3,2,2,2,0): 1 (C5) + 2 (C1) = 3 divisor nodes.")
