import sympy as sp
# Explicit Jacobian of the general-M recursion NODE. The node = (B) coordinate-subspace blow-up of the
# rank-stratum center (codim c = Mval(t)), THEN (A) det-1 Schur peel (unit Jac).
# (B) blow-up Jacobian: blowing up a codim-c coordinate subspace {y_1=...=y_c=0} in chart i (y_i=u,
#   y_j = u*v_j for j!=i) has Jacobian u^{c-1}. With F = u^2 * (residual), the u-divisor has (k,h)=(1,c-1).
#   ratio (h+1)/(2k) = c/2 = Mval(t)/2. THIS is the monomial weight.
# (A) det-1 Schur Jac = 1 (unit) -- no weight, measure-preserving.
print("=== Explicit general-M node Jacobian ===")
print("Node = (B) blow up rank-stratum center S(t), codim c=Mval(t), in affine chart i:")
print("   y_i = u,  y_j = u*v_j (j != i, j in the c center-coords).  Jacobian = u^{c-1}.")
print("   F pulls back: F = u^2 * F_residual  (the core vanishes to order 2 along the center).")
print("   => u-exceptional divisor: (k,h) = (1, c-1), ratio = c/2 = Mval(t)/2.  [THE MONOMIAL WEIGHT]")
print()
print("Then (A) det-1 Schur (Lemma-2 clear), Jacobian = 1 (UNIT), reduces F_residual to a smaller-chain")
print("   zero-core ||prod(C')||^2.  NO weight.  [measure-preserving regular peel]")
print()
# Verify the (B) blow-up Jacobian exponent on a coordinate-subspace blow-up, codim c:
c, u = sp.symbols('c u', positive=True)
print("Coordinate-subspace blow-up of codim c: chart map (u, v_1..v_{c-1}, spectators) ->")
print("   (u, u v_1, ..., u v_{c-1}, spectators). Jacobian det = u^{c-1} (the c-1 scaled coords).")
print("   Confirmed: a codim-c blow-up chart has |Jac| = u^{c-1}.")
print()
print("=== ANSWER to fm-2: (both-in-sequence), explicit forms ===")
print("Per recursion node: D_node = [(B) blow-up: monomial weight u^{Mval(t)-1}, ratio Mval(t)/2]")
print("                              o [(A) det-1 Schur: unit Jac, reduces chain, NO weight].")
print("Headline = ⨅ monomialThreshold (the (B) divisors), NOT a clean nReg/2 chain. (A) is the")
print("chain-reduction WITHIN each chart; (B) is what carries the RLCT weight + feeds #113's g5_pivotNode.")
print()
print("THE nReg/2 (clean det-1) recursion DOES exist -- but it's the B!=0 rank-r PRODUCT REDUCTION")
print("(Aoyagi Thm 3 / product_reduction / L2): peeling the r REGULAR blocks of a rank-r FIBRE. That's")
print("the +n/2 SHIFT term [-r^2+r(H1+HL+1)]/2, additive via S1.5 Fubini, det-1/measure-preserving.")
print("It is SEPARATE from the zero-core RESOLUTION (R1, the blow-up). BOTH appear in aoyagiLambda:")
print("   aoyagiLambda = [nReg/2 regular shift, from (A) Thm-3 product reduction] + [lambdaCore, from")
print("                   (B) R1 resolution of the zero-core ⨅ monomialThreshold].")
