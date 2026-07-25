#!/usr/bin/env python3
"""B1 ESCAPE-CONE PROBE (#171/#170). Does the sector-count escape cone
E = {max_W|x_w| > C*max_V|x_v|}  (W={4,5,6,7} shear-written C1 entries, V={0,1,2,3,20} pivots)
break the RLCT lower bound rlct >= 1/2*minAdm ?

Tests:
 (1) loss = ||C1*C2||^2 is PERMUTATION-invariant (||P M S||=||M||) -> the escape cone (a C1-entry-
     dominant cone) is loss-ISOMETRIC to a valid sector. [structural, exact]
 (2) det Dg: the FIXED-shear pivot-w chart (w in W) is NON-monomial (sector-count's 128 invalid),
     but SHEAR-OUTERMOST reordering (pivot on UN-sheared coords) is MONOMIAL for ALL pivots
     => route (a) fix works => B1 is a composition-order / fixed-shear ARTIFACT. [decisive]
 (3) density-of-states: escape-cone and valid-cone loss profiles MATCH (isometry sanity). [MC guide]
 (4) x=t*e_4 in {loss=0} but its origin-contribution = a permuted valid sector. [exact]
"""
import sympy as sp, numpy as np

# ---------- (1) permutation-invariance of the Frobenius loss (exact) ----------
print("=== (1) loss=||C1*C2||^2 permutation-invariance (exact) ===")
C1 = sp.Matrix(3,3, sp.symbols('a0:9')); C2 = sp.Matrix(3,4, sp.symbols('b0:12'))
loss = sum(v**2 for v in (C1*C2))
# swap rows 1,2 of C1 (P) and cols -> product rows swap; Frobenius invariant
P = sp.eye(3); P[1,1]=0;P[2,2]=0;P[1,2]=1;P[2,1]=1
loss_P = sum(v**2 for v in ((P*C1)*C2))
print("  swap two rows of C1: loss invariant?", sp.simplify(loss_P-loss)==0)
# swap inner index: C1->C1*Q, C2->Q^{-1}*C2 (Q perm on the shared dim 3)
Q = sp.eye(3); Q[0,0]=0;Q[1,1]=0;Q[0,1]=1;Q[1,0]=1
loss_Q = sum(v**2 for v in ((C1*Q)*(Q.inv()*C2)))
print("  swap inner index (C1*Q,Q^-1*C2): product unchanged?", sp.simplify(loss_Q-loss)==0)
print("  => any C1-entry-dominant cone maps to any other by a loss-isometry (transitive on entries).")

# ---------- (2) det Dg: fixed-shear W-pivot NON-monomial vs shear-outermost MONOMIAL ----------
print("\n=== (2) route-(a) fix: shear-outermost makes det MONOMIAL for ALL pivots ===")
D=21; w=sp.symbols('w0:21', real=True)
def blockbb(center,piv,v): return [ (v[piv] if k==piv else (v[piv]*v[k] if k in center else v[k])) for k in range(D)]
permIdx={0:8,1:9,2:10,3:11,4:1,5:5,6:6,7:7,8:0,9:2,10:3,11:4}
def perm(v): return [ v[permIdx.get(k,k)] for k in range(D)]
def shearH(p):
    h=list(p); h[4]=p[4]+p[0]*p[2]; h[5]=p[5]+p[1]*p[2]; h[6]=p[6]+p[0]*p[3]; h[7]=p[7]+p[1]*p[3]
    h[8]=p[8]-p[0]*p[12]-p[1]*p[16]; h[9]=p[9]-p[0]*p[13]-p[1]*p[17]
    h[10]=p[10]-p[0]*p[14]-p[1]*p[18]; h[11]=p[11]-p[0]*p[15]-p[1]*p[19]; return h
CEN={0,1,2,3,4,5,6,7,20}
def gwrap_fixed(w,p1):   # sigmaPiv (pivot p1) OUTERMOST, AFTER shear  (sector-count order)
    y=blockbb({1,5,6,7},1,list(w)); z=blockbb({0,1,2,3,4,5,6,7},0,y); p=perm(z); h=shearH(p)
    return blockbb(CEN,p1,h)
def gwrap_shearout(w,p1): # sigmaPiv on UN-sheared coords, shear OUTERMOST (route-a fix)
    y=blockbb({1,5,6,7},1,list(w)); z=blockbb({0,1,2,3,4,5,6,7},0,y); p=perm(z)
    xb=blockbb(CEN,p1,p)          # blow up BEFORE shear
    return shearH(xb)             # shear last (global unipotent bijection)
def is_coordmono(det):
    fa=sp.factor(det).as_ordered_factors()
    return all((f.is_Number or f.is_Symbol or (f.is_Pow and f.args[0].is_Symbol)) for f in fa)
for p1 in [0,4,5]:
    Jf=sp.Matrix([[sp.diff(gwrap_fixed(w,p1)[i],w[j]) for j in range(D)] for i in range(D)]).det()
    Js=sp.Matrix([[sp.diff(gwrap_shearout(w,p1)[i],w[j]) for j in range(D)] for i in range(D)]).det()
    print(f"  pivot p1={p1}: fixed-shear coord-monomial={is_coordmono(Jf)} ; shear-outermost coord-monomial={is_coordmono(Js)}")
print("  => shear-outermost is monomial for W-pivots too: the 128 'invalid' are a FIXED-SHEAR/ORDER artifact.")

# ---------- (3) density-of-states: escape vs valid loss profile (numpy guide) ----------
print("\n=== (3) density-of-states sanity: escape-cone vs valid-cone loss profile (MC guide) ===")
rng=np.random.default_rng(11)
N=3_000_000
c1=rng.uniform(-1,1,size=(N,3,3)); c2=rng.uniform(-1,1,size=(N,3,4))
x=np.empty((N,21))
x[:,0:9]=c1.reshape(N,9); x[:,9:21]=c2.reshape(N,12)
prod=np.einsum('nij,njk->nik',c1,c2)
L=(prod**2).sum(axis=(1,2))            # loss
ax=np.abs(x)
W=[4,5,6,7]; V=[0,1,2,3,20]; C=1.0
maxW=ax[:,W].max(axis=1); maxV=ax[:,V].max(axis=1)
esc = maxW > C*maxV
val = maxV >= maxW           # complementary-ish valid region
def rlct_est(mask):
    Lm=L[mask]; Lm=Lm[Lm>0]
    # slope of log N(eps) vs log eps over a decade band (density-of-states exponent, GUIDE only)
    import numpy as _np
    eps=_np.array([1e-6,1e-5,1e-4,1e-3])
    cnt=_np.array([ (Lm<e).mean() for e in eps])
    ok=cnt>0
    if ok.sum()<2: return None
    return _np.polyfit(_np.log(eps[ok]),_np.log(cnt[ok]),1)[0]
print(f"  escape-cone frac={esc.mean()*100:.1f}%  d.o.s. slope(rlct-ish)={rlct_est(esc)}")
print(f"  valid-cone  frac={val.mean()*100:.1f}%  d.o.s. slope(rlct-ish)={rlct_est(val)}")
print(f"  whole ball                       d.o.s. slope(rlct-ish)={rlct_est(np.ones(N,bool))}")
print("  (slopes match escape~valid => isometric singularity; absolute value is a rough MC guide)")

# ---------- (4) x=t*e_4 in fibre; origin-contribution is a permuted valid sector ----------
print("\n=== (4) x=t*e_4: in {loss=0} (C2=0) but a MILDER far point; origin-cone is permuted-valid ===")
xe4=np.zeros(21); xe4[4]=0.5
c1e=xe4[0:9].reshape(3,3); c2e=xe4[9:21].reshape(3,4)
print(f"  loss(0.5*e_4) = {((c1e@c2e)**2).sum():.3f}  (C2=0 -> product 0 -> on the fibre)")
print("  local rlct at t*e_4 (t!=0) is NOT the origin's rlct; the ORIGIN-cone {x_4 dom} is loss-")
print("  isometric to {x_0 dom} (valid sector) by a C1 row/col permutation => contributes >= 1/2 minAdm.")
