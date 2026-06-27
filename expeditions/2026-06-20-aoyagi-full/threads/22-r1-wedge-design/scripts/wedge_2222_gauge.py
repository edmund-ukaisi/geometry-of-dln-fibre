import sympy as sp
# (2,2,2,2): does the Aoyagi GAUGE (peel layer1 at rank1) give the disjoint-block form?
# After peeling layer1 at rank t1=1: C1 ~ [[1,0],[0,δ1]] (gauge), the product becomes
#   P = C1 C2 C3.  With C1 = diag(1, δ1) (after gauge), P = diag(1,δ1) (C2 C3).
#   Let Q = C2 C3 (2x2). P = [[Q00, Q01],[δ1 Q10, δ1 Q11]]. 
#   F = ||P||^2 = (Q00^2+Q01^2) + δ1^2(Q10^2+Q11^2) = ||Q row0||^2 + δ1^2 ||Q row1||^2.
# Now Q = C2 C3 is a FRESH (2,2,2) product! ||Q row0||^2 is the "surviving" (drops to 0 only via 
# Q's own resolution), δ1^2||Q row1||^2 is the dropped block coupled to δ1.
# This is RECURSIVE: F = ||(C2C3) row0||^2 + δ1^2 ||(C2C3) row1||^2. The achiever continues on C2C3.
print("(2,2,2,2) after gauge (C1=diag(1,δ1)): F = ||Q_row0||^2 + δ1^2||Q_row1||^2, Q=C2 C3.")
print("RECURSIVE: the achiever continues resolving Q (a (2,2,2) product). The blocks chain.")
print()
# So the wedge for L>=3 is INHERENTLY RECURSIVE (the disjoint blocks emerge layer by layer via the 
# gauge). It is NOT a single weighted blow-up. The multi-radial form F = Σ r_i^2 U_i holds AFTER 
# the full gauge chain straightens each layer.
#
# BUILD IMPLICATION: the wedge for general M requires the SAME recursive chart-production as the 
# upper bound (the gauge chain). For L=2 (RRR cores like (3,3,4)) it's a SINGLE gauge + the clean 
# weighted blow-up works. For L>=3 it chains.
print("VERDICT on wedge generality:")
print("  L=2 (RRR cores, incl. (3,3,4)): SINGLE gauge + clean weighted blow-up. F=u^2·U exact. LIGHT. ✓")
print("  L>=3: recursive gauge chain (same machinery as the upper-bound cover). NOT lighter.")
print()
# Cross-check: the prior route adjudication recommended hdiv (lower bound) as MORE tractable than 
# hfin (upper). That's true at L=2 (clean wedge). At L>=3 both need the chain. But the LOWER bound 
# still only needs ONE path (the achiever), so it's lighter than the FULL cover even at L>=3:
print("BUT the lower bound still only needs ONE achiever path's chart (not the full cover), so it's")
print("lighter than hfin even at L>=3: build the achiever's recursive chart, ignore all other strata.")
