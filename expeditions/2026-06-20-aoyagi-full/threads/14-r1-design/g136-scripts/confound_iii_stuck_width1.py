# Does the first-factor blow-up recursion get STUCK at a width-1 layer? The Schur straighten of a
# factor with a width-1 dimension: pivot is 1x1, Schur complement is (m1-1)x(m2-1). If m2=... the
# MIDDLE width is 1, then C1 is M^1 x 1 (column). Blow up {C1=0} (codim M^1). Hard pivot c0=1.
# Straighten: C1 = (1, *, ..., *)^T. The "Schur complement" D - b a: here a = (empty, the 1x0 row part),
# so S = D - b·a but D is 0x0 (no columns beyond pivot in a 5x1). The reduced first factor is empty.
# => the chain CANNOT continue the matrix-chain recursion; the residual after peeling the pivot row is
# ‖(reduced)‖^2 where reduced = the rest. Let me see EXACTLY what happens for (3,1,3).
import sympy as sp
# (3,1,3): C1 3x1, C2 1x3. f = ‖C1 C2‖^2.
C1=sp.Matrix(3,1, lambda i,j: sp.Symbol(f'c{i}')); C2=sp.Matrix(1,3, lambda i,j: sp.Symbol(f'd{j}'))
P=C1*C2; f=sp.expand(sum(P[i,j]**2 for i in range(3) for j in range(3)))
# blow up {C1=0} codim 3: c0=u, c1=u v1, c2=u v2 (pivot c0)
u,v1,v2=sp.symbols('u v1 v2', positive=True)
fb=f.subs({sp.Symbol('c0'):u, sp.Symbol('c1'):u*v1, sp.Symbol('c2'):u*v2})
fb=sp.expand(fb)
orders=[m[0] for m in sp.Poly(fb,u).monoms()]
print(f"(3,1,3) blow up {{C1=0}}: f∘φ u-order = {min(orders)} (k_E={min(orders)//2})")
# factor out u^2:
res=sp.simplify(fb/u**2)
print(f"  residual f∘φ/u² = {sp.factor(res)}")
# Is the residual a UNIT (nonzero at origin v=0) or does it still vanish (need more blow-up)?
res0=res.subs({u:0, v1:0, v2:0})
print(f"  residual at origin (u=v=0) = {res0}  => {'UNIT (terminates here!)' if res0!=0 else 'still singular'}")
# residual = ‖C2‖^2·(1+v1²+v2²) = (d0²+d1²+d2²)(1+v1²+v2²). At origin v=0: = d0²+d1²+d2², vanishes at d=0!
# So the residual STILL vanishes (on {C2=0}). Need to resolve C2 too. But the blow-up was on C1 only.
print()
print("  KEY: residual = (Σd_j²)(1+Σv_i²). The (1+Σv²) is a UNIT, but (Σd_j²) STILL VANISHES at d=0.")
print("  So one C1-blow-up does NOT fully resolve (3,1,3) -- the residual (Σd²) is a fresh smooth")
print("  block needing its OWN resolution. The recursion must ALSO blow up / Fubini the d-block.")
print("  This is the Fubini product structure: f∘φ = u²·(Σd²)·unit, threshold = min(C1-divisor, d-block).")
# divisor ratios: u-divisor: core u², Jac u^{codim-1}=u^2 => h=2,k=1 ratio 3/2? wait codim{C1=0}=3 => Jac u^2.
# u-divisor ratio = (2+1)/(2·1)=3/2. d-block (3 squares) ratio 3/2. minAdm(3,1,3)? 
def adm(M):
    L=len(M)-1; out=[]
    def rec(j,prev,cur):
        if j==L+1:
            if cur[-1]==0: out.append(tuple(cur[1:]))
            return
        for v in range(0,min(prev,M[j])+1): rec(j+1,v,cur+[v])
    rec(1,M[0],[M[0]]); return out
def Mval(M,t):
    L=len(M)-1; tt=[M[0]]+list(t); s=0
    for j in range(1,L+1): s+=(tt[j-1]-tt[j])*(M[j]-tt[j])
    return s
M=[3,1,3]; print(f"\n  minAdm(3,1,3)={min(Mval(M,t) for t in adm(M))} => rlct=½·that. u-divisor ratio 3/2, d-block 3/2.")
