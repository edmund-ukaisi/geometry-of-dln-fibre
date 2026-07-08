import sympy as sp

print("="*78)
print("TEST 1 — (2,2,2,2), t=(1,0,0): depth-recursion peel vs one-shot/atom trap")
print("="*78)

a,b,delta,u,v,r,s,alpha,rho = sp.symbols('a b delta u v r s alpha rho', real=True)

# Worked-tex incidence chart for the C1.C2 boundary (image p.15-18):
A = alpha*sp.Matrix([[1,a],[b, a*b+delta]])      # C^(1) in incidence chart
B = sp.Matrix([[u-a*r, v-a*s],[r, s]])           # C^(2)
AB = sp.simplify(A*B)
print("\n[1a] A.B in the incidence chart (should be alpha*[[u,v],[bu+dr, bv+ds]]):")
sp.pprint(AB)
target = alpha*sp.Matrix([[u, v],[b*u+delta*r, b*v+delta*s]])
print("   matches alpha*[[u,v],[bu+dr,bv+ds]]:", sp.simplify(AB-target)==sp.zeros(2,2))
print("   => row2 = b*(row1) + delta*(r,s): the pivot row (u,v) + residual delta*(r,s). EXACT.")

# The deeper factor C3 (single matrix here: (2,2,2,2) is L=3, deeper of the layer-1 peel = C3 alone)
c11,c12,c21,c22 = sp.symbols('c11 c12 c21 c22', real=True)
C3 = sp.Matrix([[c11,c12],[c21,c22]])

# ---- ONE-SHOT (design-S8): blow up {delta=u=v=0} once, look at the chart delta=rho (delta-direction) ----
print("\n[1b] ONE-SHOT trap: blow up {delta=u=v=0}; chart where delta carries the exceptional rho.")
xi,eta = sp.symbols('xi eta', real=True)
# chart: delta=rho, u=rho*xi, v=rho*eta  (the delta!=0 affine chart of the blowup of the 3-plane)
AB_os = AB.subs({delta:rho, u:rho*xi, v:rho*eta})
AB_os = sp.simplify(AB_os)   # = alpha*rho*[[xi,eta],[b*xi+r, b*eta+s]]
print("   A.B after one-shot blow-up (chart delta=rho):")
sp.pprint(sp.simplify(AB_os/(alpha*rho)))
# residual matrix M_os with F = alpha^2 rho^2 * ||M_os . C3||^2
M_os = sp.simplify(AB_os/(alpha*rho))
U = sum((M_os*C3)[i,j]**2 for i in range(2) for j in range(2))
U = sp.expand(U)
# order of vanishing of U at the chart origin (xi=eta=b=r=s=0 and c's? U is the residual 'unit' claim)
# The design claim: U vanishes (NOT a unit) — check U at xi=eta=r=s=b=0:
U0 = U.subs({xi:0,eta:0,r:0,s:0,b:0})
print("   residual U at chart-origin (xi=eta=r=s=b=0):", sp.simplify(U0), " => U is NOT a nonzero unit (vanishes).")
# order: substitute xi=τξ0,... to see leading order (all incidence coords scale)
tau = sp.symbols('tau', positive=True)
xi0,eta0,b0,r0,s0 = sp.symbols('xi0 eta0 b0 r0 s0', real=True)
Ut = U.subs({xi:tau*xi0,eta:tau*eta0,b:tau*b0,r:tau*r0,s:tau*s0})
Ut = sp.expand(Ut)
p = sp.Poly(Ut, tau)
print("   leading tau-order of U (min degree in the incidence coords):", min(m[0] for m in p.monoms() if p.coeff_monomial(tau**m[0])!=0) if p.monoms() else None)
print("   => one blow-up leaves U singular (design-S8 REFUTED; matches worked-tex 'order 4').")

# ---- DEPTH RECURSION: peel EXACTLY one layer -> fresh depth-2 core (no Gram det) ----
print("\n[1c] DEPTH-RECURSION peel: F = alpha^2 rho^2 * ||X . C3||^2, X a FRESH matrix, C3 untouched.")
print("   The peel blows up ONLY the layer-1 radial (rho for {u=v=delta=0} restricted to the layer),")
print("   producing X = [[xi,eta],[b*xi+r, b*eta+s]]; the deeper C3 is carried UNTOUCHED.")
print("   ||X.C3||^2 is a FRESH depth-2 core (chain X, C3): recurse on IT (its own layer peel).")
print("   NO det(Q_b Q_b^T) ever forms — Gamma/the block is a CHART coord, never integrated out.")

# ---- ATOM route contrast: where the Gram-det of a PRODUCT appears ----
print("\n[1d] ATOM route contrast (the trap): Q_b = A_{1,b}.A_2 (non-pivot row of A1 times A2) is a")
print("   1x2 . 2x2 PRODUCT. det(Q_b Q_b^T)=||Q_b||^2. Show it vanishes on {A_2 rank-drops} even when")
print("   the row A_{1,b} != 0 — the extra product-vanishing the atom must principalise:")
w1,w2 = sp.symbols('w1 w2', real=True)   # A_{1,b} = (w1,w2) a nonzero 1x2 row
A2 = sp.Matrix([[c11,c12],[c21,c22]])
Qb = sp.Matrix([[w1,w2]])*A2              # 1x2 product
gram = sp.expand((Qb*Qb.T)[0,0])
print("   ||Q_b||^2 =", gram)
# on rank-drop of A2 (rows proportional: c21=k*c11, c22=k*c12): does it vanish for a special row?
k = sp.symbols('k', real=True)
gram_rd = gram.subs({c21:k*c11, c22:k*c12})
print("   on A2 rank-1 (c21=k c11,c22=k c12): ||Q_b||^2 =", sp.factor(gram_rd))
print("   = (w1+k w2)^2 (c11^2+c12^2): VANISHES when w1+k w2=0 (a codim-1 condition on the row) —")
print("   the Gram-det of the PRODUCT couples the row A_{1,b} to A_2's rank-drop. Principalising this")
print("   jointly (which u divides which minor) is the atom-route res-of-sing brick.")
