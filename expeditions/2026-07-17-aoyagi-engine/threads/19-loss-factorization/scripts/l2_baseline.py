#!/usr/bin/env python3
"""
L=2 (2,2,2) baseline — the fully-worked RRR case.

Purpose: establish the loss-pullback machinery on the case where BOTH the §8
one-shot and Aoyagi's recursion succeed, and confirm the LeafPullback-shape
factorization  F = (∏ divisor²) · residualCore  with residualCore a Morse form
bounded below by a positive multiple of the base form.

Chart (verify-r1-shortcut.md, exact): the layer-1 incidence chart
   A = α[[1,a],[b, a*b+δ]],   B = [[u-a*r, v-a*s],[r,s]]
then ONE blow-up of the codim-3 center {δ=u=v=0} in the δ-chart:
   δ = ρ, u = ρ*ξ, v = ρ*η.

F = ‖A·B‖²_F.

At L=2 the residual after the single blow-up is a NONDEGENERATE (Morse, rank-4)
quadratic — so ρ genuinely binds and the chart is normal-crossing in ONE step.
The divisors are α (layer-1 incidence) and ρ (residual blow-up).
"""
import sympy as sp

a,b,delta,u,v,r,s,alpha = sp.symbols('a b delta u v r s alpha', real=True)

A = alpha*sp.Matrix([[1,a],[b, a*b+delta]])
B = sp.Matrix([[u-a*r, v-a*s],[r,s]])
P = A*B
F = sum(P[i,j]**2 for i in range(2) for j in range(2))
F = sp.expand(F)
print("=== L=2 incidence-chart loss F = ‖A·B‖² ===")
print("F =", F)

# ---- one blow-up of {δ=u=v=0}: δ=ρ, u=ρξ, v=ρη ----
rho,xi,eta = sp.symbols('rho xi eta', real=True)
Fb = F.subs({delta:rho, u:rho*xi, v:rho*eta})
Fb = sp.expand(Fb)
print("\n=== after blow-up (δ=ρ, u=ρξ, v=ρη) ===")
print("Fb =", Fb)

# factor out the divisor monomial α²ρ²
core = sp.simplify(Fb/(alpha**2 * rho**2))
core = sp.expand(core)
print("\n=== residualCore = Fb/(α²ρ²) ===")
print("core =", core)

# Is core divisible by α or ρ? (leak check)
print("\ncore contains alpha?", core.has(alpha))
print("core contains rho?  ", core.has(rho))

# The residual as a matrix norm: ‖[[1,0],[b,1]]·[[ξ,η],[r,s]]‖²  (paper form)
Xmat = sp.Matrix([[1,0],[b,1]])*sp.Matrix([[xi,eta],[r,s]])
core_paper = sp.expand(sum(Xmat[i,j]**2 for i in range(2) for j in range(2)))
print("\ncore matches paper ‖[[1,0],[b,1]][[ξ,η],[r,s]]‖²?",
      sp.simplify(core - core_paper) == 0)

# ---- Morse check: Hessian rank of core at the deepest point of {ρ=0} ----
# free residual coords are (ξ,η,r,s); b is an incidence spectator.
# At the deepest point ξ=η=r=s=0, is the Hessian nondegenerate (rank 4)?
freevars = [xi,eta,r,s]
H = sp.hessian(core, freevars)
H0 = H.subs({xi:0,eta:0,r:0,s:0, b:0})
print("\n=== Hessian of core at deepest point (b=0) ===")
sp.pprint(H0)
print("Hessian rank =", H0.rank(), " (Morse iff = 4)")

# ---- lower/upper squeeze of core against baseForm = ξ²+η²+r²+s² on a box ----
# core = ‖(I + strictly-lower b)·[[ξ,η],[r,s]]‖² ; for |b|≤1 the linear map
# (I+lower b) has singular values bounded away from 0 and ∞, so
#   lo·(ξ²+η²+r²+s²) ≤ core ≤ hi·(ξ²+η²+r²+s²).
base = xi**2+eta**2+r**2+s**2
# exact eigen-squeeze: core = z^T (Lᵀ L ⊗ I?) ... compute via the 2x2 gram of L=[[1,0],[b,1]]
L = sp.Matrix([[1,0],[b,1]])
G = L.T*L                      # core = trace(Xᵀ G X)  with X=[[ξ,η],[r,s]]
eigs = G.eigenvals()
print("\n=== squeeze: eigenvalues of Gram Lᵀ L (b symbolic) ===")
for e,m in eigs.items():
    print("  eig:", sp.simplify(e), " mult", m)
# at b=1 (box corner) numeric eigs -> lo,hi
G1 = G.subs({b:1})
print("at b=1: eigs =", [sp.nsimplify(x) for x in G1.eigenvals()])
lo_num = min(float(x) for x in sp.Matrix(list(G1.eigenvals().keys())))
hi_num = max(float(x) for x in sp.Matrix(list(G1.eigenvals().keys())))
print(f"at b=1: lo≈{lo_num:.4f} (>0), hi≈{hi_num:.4f}")
print("\nVERDICT L=2: divisor monomial α²ρ², residual Morse rank-4, squeezed 0<lo≤core≤hi. HOLDS.")
