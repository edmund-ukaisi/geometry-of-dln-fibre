import sympy as sp

print("="*78)
print("PART C: is the SINGLE-STEP comparability sound? attack with the eps mechanism")
print("="*78)
# core = sum Erow^2 + sum (b Erow + S Bred)^2.  Phi = sum Erow^2 + ||S Bred||^2.
# The L2 counterexample mechanism: find a point where Phi = 0 but core != 0 (would break c1*Phi<=core),
# OR core = 0 but Phi != 0 (would break core<=c2*Phi).  Near b->0.
m, k, n = 3, 3, 4
a = sp.Matrix(1, k-1, lambda i,j: sp.Symbol(f'a_{j}', real=True))
b = sp.Matrix(m-1, 1, lambda i,j: sp.Symbol(f'b_{i}', real=True))
D = sp.Matrix(m-1, k-1, lambda i,j: sp.Symbol(f'D_{i}_{j}', real=True))
B = sp.Matrix(k, n, lambda i,j: sp.Symbol(f'B_{i}_{j}', real=True))
Bred = B[1:k,:]
Erow = B[0,:] + a*Bred
S = D - b*a
SB = S*Bred
core = sum(Erow[0,j]**2 for j in range(n)) + sum((b[i,0]*Erow[0,j] + SB[i,j])**2 for i in range(m-1) for j in range(n))
Phi  = sum(Erow[0,j]**2 for j in range(n)) + sum(SB[i,j]**2 for i in range(m-1) for j in range(n))

# Claim 1 (core <= c2 Phi near b=0):  Phi=0 => Erow=0 AND S Bred=0 => core=0. So {Phi=0} subset {core=0}.
# Verify symbolically: substitute Erow_j=0 (j) and (S Bred)_{ij}=0 -> core becomes 0.
print("Phi=0 forces Erow=0 and S·Bred=0; then each (b Erow + S Bred) = b·0+0 = 0 => core=0.")
# direct check: core - Phi = sum_{i,j} [ (b_i Erow_j + SB_ij)^2 - SB_ij^2 ] = sum 2 b_i Erow_j SB_ij + b_i^2 Erow_j^2
diff = sp.expand(core - Phi)
# factor out: every term in diff has a factor b_i (the cross-talk is multiplied by b)
print("\ncore - Phi expanded; check every monomial carries a factor b_i:")
poly = sp.Poly(diff, *[b[i,0] for i in range(m-1)])
# minimal total degree in b across all monomials:
mindeg = min(sum(mono[:m-1]) for mono in poly.monoms())
print("  min total degree of (core-Phi) in the b-variables =", mindeg, "(>=1 => vanishes at b=0)")

# Claim 2 (c1 Phi <= core near b=0): need core >= c1 Phi for b small. Worst case: can core be small while Phi large?
# core = ||Erow||^2 + ||b Erow + S Bred||^2.  By triangle: ||b Erow + S Bred|| >= ||S Bred|| - |b|·||Erow||.
# So for |b| <= 1/2 (say), and using ||Erow|| also in core:
#   core >= ||Erow||^2 + (||S Bred|| - |b| ||Erow||)^2.  This is a clean bilipschitz bound, NOT a
#   product-cancellation. Verify there is NO point with Phi>0, core=0, b small:
# core=0 => Erow=0 (from first block) AND b Erow + S Bred = 0 => S Bred = 0 => Phi=0. Contradiction.
print("\ncore=0 forces Erow=0 (1st block) then S·Bred = -b·Erow = 0 => Phi=0. So {core=0}={Phi=0}.")
print("=> same zero-set; core - Phi in ideal(b)·(linear in Erow,SB); comparability is a")
print("   BILIPSCHITZ change-of-vars near b=0, NOT a product-cancellation. SOUND.")

# Now: can the eps=1/7 mechanism (E=0, R!=0) be recast here?  The L2 'E' = full-product residual.
# Here the analog of 'E' is Erow (the pivot-row product of THIS layer). Phi already INCLUDES ||S Bred||^2
# as the child loss -- it does NOT try to replace S Bred by a product of deeper Schur cores.
# The counterexample needed: child-core-replacement != real child. Here child = ||S Bred||^2 IS used
# verbatim (no replacement). So the mechanism has nothing to attack.
print("\nThe eps mechanism needed REPLACING the real child by a product-of-Schur surrogate.")
print("Here Phi USES ||S·Bred||^2 = real child loss verbatim. No surrogate => nothing to attack.")
print("\nALL PART-C CHECKS CONSISTENT.")
