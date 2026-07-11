import sympy as sp, itertools
from functools import lru_cache

# (A) q=3 coupled corner ADDs (charges add, not min), symbolic threshold = 1/2 sum(a_i+1).
print("(A) q=3 coupled corner  G=u0^2 U0 + u1^2 U1 + u2^2 U2 (U_i>0 units), measure |u0|^a0|u1|^a1|u2|^a2.")
print("    Blow up u1=u0 t1, u2=u0 t2 (u0 maximal): Jac du1du2 = u0^2 du0 dt1 dt2 (q-1=2).")
print("    integrand ~ u0^{a0+a1+a2 + 2 - 2c} * (unit) * t1^a1 t2^a2  =>  converges iff")
a0,a1,a2,c=sp.symbols('a0 a1 a2 c',positive=True)
expo = a0+a1+a2 + 2 - 2*c
thr = sp.solve(sp.Eq(expo,-1),c)[0]   # u0-power > -1
print(f"    exponent of u0 = {expo};  finite iff > -1  =>  c < {sp.simplify(thr)} = 1/2 * ( (a0+1)+(a1+1)+(a2+1) ).")
print("    => charges ADD for q=3 (same mechanism iterates for all q). MIN would need a shared divisor (radialAttach).")
print()

@lru_cache(None)
def minAdm(M):
    M=tuple(M)
    if len(M)<=1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
@lru_cache(None)
def cCodim(c,rho):
    c=tuple(c); L=len(c)-1
    if L==0: return 0
    if L==1:
        r=min(rho,c[0],c[1]); return (c[0]-r)*(c[1]-r)
    best=None; rng=range(0,max(c)+1)
    for T in itertools.product(rng,repeat=L):
        if any(T[i]<T[i+1] for i in range(L-1)): continue
        if T[0]>min(c[0],c[1]): continue
        if T[-1]>rho: continue
        if not all(T[j]<=min(T[j-1],c[j+1]) for j in range(1,L)): continue
        val=(c[0]-T[0])*(c[1]-T[0])+sum((T[j-1]-T[j])*(c[j+1]-T[j]) for j in range(1,L))
        if best is None or val<best: best=val
    return best if best is not None else 0

# (B) (4,3,3,3) E-table (Codex claimed (7,7,9,12))
print("(B) (4,3,3,3): E(rho)=cCodim((3,3,3);rho)+4*rho for rho=0..3  [Codex claim (7,7,9,12)]:")
M=(4,3,3,3); deeper=M[1:]; r=min(deeper)
E=[cCodim(deeper,rho)+M[0]*rho for rho in range(r+1)]
print(f"    deeper chain {deeper}, r={r}: E = {E}  minAdm={minAdm(M)}  (min E == minAdm: {min(E)==minAdm(M)})")
print()

# (C) anchor two-view reconciliation: decorated cut n0=ab=4 vs top-level collapsing-charge M0*q.
print("(C) Anchor (3,3,3,4) two views (both give 7/2; the 'n0' differs by view -> 'D/m >= n0' is view-dependent):")
print("    Top-level (front A0=3x3, deeper P=A1A2 chain (3,3,4), r=3):")
deeper=(3,3,4)
for q in range(0,4):
    rho=3-q; Dq=cCodim(deeper,rho); dq=3*rho
    print(f"      q={q} rho={rho}: D_q=cCodim={Dq}  M0*q(collapsing charge)={3*q}  d_q=M0*rho={dq} "
          f"| min(M0q,Dq)={min(3*q,Dq)} -> cell thr={sp.Rational(dq+min(3*q,Dq),2)}  (naive (Dq+dq)/2={sp.Rational(Dq+dq,2)})")
print("      => binding q=2: D_2=4 <= M0*q=6, so corner MIN picks the TUBE D_2=4 -> 1/2(3+4)=7/2. (D/m=4 < 6=M0q.)")
print("    Decorated cut t*=1 (a=b=2, n0=ab=4, n1=minAdm(1,3,4)=3): deeper A2=3x4, tube {rankA2<=1} cCodim((3,4);1)=6.")
print(f"      D/m=6 >= n0=ab=4 -> corner ADDS fully -> 1/2(4+3)=7/2.   [here D/m>=n0 HOLDS]")
print()
print("  => The SAME anchor: top-level reads D/m=4 < n0=6 (min bites tube); decorated reads D/m=6 >= n0=4 (adds).")
print("     Both yield 7/2. The scalar 'n0' and the direction of the inequality are VIEW-DEPENDENT bookkeeping;")
print("     the robust invariant is  min_rho(cCodim + M0*rho) = minAdm  with geometric cCodim and m=1.")
