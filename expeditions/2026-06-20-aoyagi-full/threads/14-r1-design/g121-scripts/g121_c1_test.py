import sympy as sp
# Stress-test (C1): can a pure sequence of COORDINATE-subspace blow-ups (no det-1 straightening)
# resolve ||prod(C)||^2? The worry for (C2): maybe the det-1 Schur is just a CONVENIENCE and pure
# coordinate blow-ups suffice (then (C1)).
#
# Test on node-2 residual: the rank-defect center is {r-pq=0} (bilinear). A coordinate-subspace
# blow-up blows up {y_1=...=y_c=0}. The center {r-pq=0} is NOT of that form. But you could blow up
# the COORDINATE subspaces {p=0,r=0}, {q=0,r=0}, etc., and try to resolve {r=pq} as a strict transform.
# Does that terminate with the RIGHT monomialThreshold (=lambdaCore), or a different (wrong) value?
#
# KEY INSIGHT: the issue is not whether {r-pq=0} is resolvable by SOME blow-ups (it is -- any variety is,
# by Hironaka). The issue is whether the SPECIFIC explicit-coordinate-blow-up machinery the project uses
# (g5_pivotNode = coordinate-subspace blow-ups) can produce the recursion with centers that STAY
# coordinate subspaces, WITHOUT the det-1 straightening keeping them coordinate.
#
# The det-1 Schur does TWO things:
#  (i) reduces the chain dims (strict transform = smaller ||prod(C')||^2) -- keeps the recursion SHAPE
#      (a matrix-chain core), so the NEXT center is again a rank-stratum = coordinate-subspace-able.
#  (ii) straightens the current rank-defect center to a coordinate subspace.
# WITHOUT (i), after a coordinate blow-up the residual is NOT a clean smaller-chain core -- it's a
# messier variety whose rank-defect centers are NOT coordinate subspaces, so the next coordinate blow-up
# can't be applied cleanly. The recursion would NOT close as a chain-core recursion.
print("=== Why (C1) pure-coordinate-blow-up does NOT close cleanly ===")
print("The det-1 Schur does TWO jobs: (i) reduce the chain (strict transform = smaller ||prod(C')||^2,")
print("keeping the recursion a MATRIX-CHAIN core), (ii) straighten the rank-defect center to a coord")
print("subspace. WITHOUT (i), a pure coordinate blow-up leaves a residual that is NOT a smaller chain-core,")
print("so its rank-defect centers are NOT coordinate subspaces => the next coordinate blow-up can't apply")
print("=> the recursion does NOT close as the clean chain-core recursion that gives ⨅ monomialThreshold.")
print()
print("So the det-1 Schur is what KEEPS the recursion a sequence of coordinate-subspace blow-ups of")
print("rank strata. It's the GL-straightening that makes the (C1)-style coordinate machinery applicable")
print("AT ALL nodes, not just node 1. => (C2): det-1 Schur GENUINELY NEEDED, NOT eliminable.")
print()
print("CAVEAT (honest): one COULD in principle resolve via Hironaka / general blow-ups of non-coordinate")
print("ideals (no det-1 Schur), but the project's chosen machinery is COORDINATE-subspace blow-ups")
print("(g5_pivotNode, S1.1 hsurj/hImE for monomial charts). For THAT machinery, the det-1 Schur is needed")
print("to keep every center a coordinate subspace. So (C2) for the project's route; (C1) only if you")
print("rebuild on general-ideal blow-up infra (which Mathlib lacks -- the rejected heavier path).")
