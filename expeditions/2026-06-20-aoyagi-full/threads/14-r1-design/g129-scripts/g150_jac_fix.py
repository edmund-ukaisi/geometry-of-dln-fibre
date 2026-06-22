import sympy as sp
# Fix the regular-coord ↔ product-residual identification. At w0 (all gauge coords 0), the LINEAR parts:
#   E00 = P[0,0]-1 = (X1+X2 + h.o.t.)            ∂/∂X1=1, ∂/∂X2=1 at w0
#   E01 = P[0,1]   = (Y1·? ...) let me read the linear part
#   E10 = P[1,0]   = (Z1+Z2-ish)
# The reduced T1,T2 give ‖T1 T2‖². To capture the 3 regular residuals (E00,E01,E10) as INDEPENDENT
# coords, pick a transversal. Compute the FULL Jacobian of (E00,E01,E10) wrt ALL 6 regular gauge coords
# at w0 and check rank 3 (so they ARE 3 independent regular directions).
r,m,n=1,2,2
def blk(p):
    return (sp.Matrix(r,r,sp.symbols(f'{p}X0:{r*r}')), sp.Matrix(r,n-r,sp.symbols(f'{p}Y0:{r*(n-r)}')),
            sp.Matrix(m-r,r,sp.symbols(f'{p}Z0:{(m-r)*r}')), sp.Matrix(m-r,n-r,sp.symbols(f'{p}T0:{(m-r)*(n-r)}')))
X1,Y1,Z1,T1=blk('a'); X2,Y2,Z2,T2=blk('b'); Ir=sp.eye(r)
C1=sp.Matrix(sp.BlockMatrix([[Ir+X1,Y1],[Z1,T1]])); C2=sp.Matrix(sp.BlockMatrix([[Ir+X2,Y2],[Z2,T2]]))
P=sp.expand(C1*C2)
E00=sp.expand(P[0,0]-1); E01=sp.expand(P[0,1]); E10=sp.expand(P[1,0])
reg = list(X1)+list(Y1)+list(Z1)+list(X2)+list(Y2)+list(Z2)
w0={s:0 for s in reg+list(T1)+list(T2)}
print("Linear parts at w0:")
for nm,E in [("E00",E00),("E01",E01),("E10",E10)]:
    lin = [(str(v), sp.diff(E,v).subs(w0)) for v in reg if sp.diff(E,v).subs(w0)!=0]
    print(f"  {nm} = {E}   linear: {lin}")
J = sp.Matrix([[sp.diff(E,v).subs(w0) for v in reg] for E in (E00,E01,E10)])
print("\nJacobian (3 × 6) rank at w0 =", J.rank(), " (=3 ⟹ E00,E01,E10 are 3 independent regular directions)")
print("""
⟹ The 3 regular residuals (E00,E01,E10) are independent regular coords (Jacobian rank 3 over the 6
gauge regular coords). Choosing a transversal (3 of the gauge coords, e.g. X1,Y2,Z1 per the linear
parts) completes them to a det-unit coordinate change: the chart maps (regular gauge coords) →
(E00,E01,E10, spectators) with a unit Jacobian block, KEEPS T1,T2 as reduced. So loss ∘ chart =
∑E² + ‖T1 T2‖² EXACTLY near w0. The NON-MP point: the Jacobian is a UNIT (nonzero, the rank-3 block
+ the spectator identity), NOT det=1 — hence jac_unit + rlctAtOn_unit_invariant_aux, not comp_homeomorph.
""")
print("nReg count check (2,2,2) r=1: regular residuals across the L=2 layers' product = r·(H_0+H_L−r) =")
print("  1·(2+2−1) = 3 ✓ (matches nReg = r(H_0 + H_last − r) in the DeepestGaugeChart interface).")
