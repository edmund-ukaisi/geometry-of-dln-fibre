#!/usr/bin/env python3
"""
DEEP-LEVEL (S=2 J>=1) full-chart shear ablation -- the EXACT second singular data point (PIN 2 / T8,T9).

Builds the corank-1 coupled block M = Dbar . S (Dbar 2x2 pivot-normalized, S 2x3, the 2x3 residual =
type T8; the 1x2 sub-row = T9) and an EXPLICIT faithful resolution chart g2 (mirrors gFaithful):
  Dbar = [[1, d01],[d10, d11]] , with the radial+join reading
     Delta' = d11 - sA*d01*d10 = E*beta        (Schur, blow-up of the coupling)
     peeled'[0,j] (T-row) = E*(1,t1,t2)[j]      (radial on the pivot row)
     recoord:  S[0,j] = E*(1,t1,t2)[j] - rA*d01*S[1,j]   (rA = the born recoord shear toggle)
     S[1,j] free residual.
Then M = Dbar.S is the actual loss; pull it back, factor the GCD monomial, read residual at center.
  rA = 1 : the born recoord present.   rA = 0 : recoord OFF (shear-free).
SINGULAR iff dropping the recoord over-vanishes (all residuals vanish at center).
"""
import sympy as sp

E,beta,t1,t2 = sp.symbols('E beta t1 t2')
d01,d10 = sp.symbols('d01 d10')
S10,S11,S12 = sp.symbols('S10 S11 S12')          # free residual (Delta'-block source row)
allc = [E,beta,t1,t2,d01,d10,S10,S11,S12]

def loss_gens(sA, rA):
    # radial/join reading of the resolution chart g2:
    d11 = E*beta + sA*d01*d10                     # Schur: Delta' = d11 - d01*d10 = E*beta
    Trow = [E*1, E*t1, E*t2]                      # peeled' T-row = E*(1,t1,t2)
    S0 = [Trow[j] - rA*d01*[S10,S11,S12][j] for j in range(3)]   # recoord shear on the pivot row
    S1 = [S10, S11, S12]
    Dbar = sp.Matrix([[1, d01],[d10, d11]])
    Smat = sp.Matrix([S0, S1])
    M = sp.expand(Dbar*Smat)                      # the actual 2x3 loss product
    return [sp.expand(M[i,j]) for i in range(2) for j in range(3)]

def monomial_gcd(polys):
    g=None
    for p in polys:
        if p==0: continue
        pp=sp.Poly(p,*allc)
        exps=[min(m[i] for m in pp.monoms()) for i in range(len(allc))]
        g=exps if g is None else [min(a,b) for a,b in zip(g,exps)]
    if g is None: return sp.Integer(1)
    return sp.prod([allc[i]**g[i] for i in range(len(allc))])

def report(name, sA, rA):
    G = loss_gens(sA, rA)
    m = monomial_gcd(G)
    quots=[sp.expand(sp.cancel(g/m)) for g in G]
    at0=[q.subs({s:0 for s in allc}) for q in quots]
    surv=any(v!=0 for v in at0)
    print(f"\n[{name}]  GCD monomial = {m}")
    print(f"   residuals at center = {at0}")
    print(f"   SURVIVOR: {surv}  =>  {'SMOOTH' if surv else 'SINGULAR (over-vanishes)'}")
    return surv

print("="*90)
print("DEEP corank-1 coupled block (T8 2x3 / T9 1x2 level): recoord-shear ablation")
print("="*90)
report("recoord ON + Schur ON  (the born shear present)", 1, 1)
report("recoord OFF (drop the born recoord)", 1, 0)
report("Schur OFF (drop the coupling Schur)", 0, 1)
report("BOTH OFF (blow-up only, shear-free)", 0, 0)

# --- also: the 1x2 sub-row (T9) in isolation ---
print("\n" + "="*90)
print("T9 in isolation: the deepest 1x2 row after the recoord")
print("="*90)
# the 1x2 T-row sub-block [M00, M01] with the recoord toggle
for rA in (1,0):
    d11 = E*beta + d01*d10
    Trow=[E*1, E*t1]
    S0=[Trow[j]-rA*d01*[S10,S11][j] for j in range(2)]
    Dbar=sp.Matrix([[1,d01],[d10,d11]]); Smat=sp.Matrix([S0,[S10,S11]])
    M=sp.expand(Dbar*Smat)
    row=[sp.expand(M[0,0]), sp.expand(M[0,1])]
    m=monomial_gcd(row)
    at0=[sp.expand(sp.cancel(r/m)).subs({s:0 for s in allc}) for r in row]
    print(f"  recoord {'ON ' if rA else 'OFF'} : GCD={m}, 1x2 residuals at center={at0}, "
          f"survivor={'YES (SMOOTH)' if any(v!=0 for v in at0) else 'NO (SINGULAR)'}")
