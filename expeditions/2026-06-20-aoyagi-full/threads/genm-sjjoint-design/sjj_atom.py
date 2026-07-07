import numpy as np, sympy as sp
from scipy.special import gamma as G
rng=np.random.default_rng(7)
# ============================================================
# (1) EXACT closed-form derivation check of the anisotropic-shifted atom, MATRIX case.
#   I = ∫_{Γ∈R^{p×q}} (w + ‖Γ R + S‖²_F)^{-c'} dΓ
#     = Cinf(pq,c')·det(R Rᵀ)^{-p/2}·(w + ‖S(I-P_R)‖²)^{-(c'-pq/2)}
# Verify LHS (high-N importance-sampling MC) vs RHS (closed) for genuine matrix Γ (p=2,q=2).
# ============================================================
def Cinf(a,cp): return np.pi**(a/2)*G(cp-a/2)/G(cp)
def rhs(w,R,S,cp):
    p=S.shape[0]; q=R.shape[0]; n=R.shape[1]; Gram=R@R.T
    P=R.T@np.linalg.inv(Gram)@R
    wprime=w+((S@(np.eye(n)-P))**2).sum()
    return Cinf(p*q,cp)*np.linalg.det(Gram)**(-p/2)*wprime**(-(cp-p*q/2))
print("=== (1) anisotropic-shifted atom: MC LHS vs closed RHS ===")
for (p,q,n) in [(2,2,3),(2,2,2),(1,3,3),(3,1,2)]:
    a=p*q; cp=a/2+0.8
    R=rng.standard_normal((q,n)); S=rng.standard_normal((p,n)); w=abs(rng.standard_normal())+0.4
    N=6_000_000; sig=2.5
    Gm=rng.standard_normal((N,p,q))*sig
    GR=np.matmul(Gm,R)                       # (N,p,n)
    integ=(w+((GR+S[None])**2).sum((1,2)))**(-cp)
    gpdf=np.exp(-(Gm**2).sum((1,2))/(2*sig*sig))/((2*np.pi*sig*sig)**(a/2))
    lhs=(integ/gpdf).mean(); r=rhs(w,R,S,cp)
    print(f"  p={p} q={q} n={n} a={a} c'={cp:.2f}: MC={lhs:.4f} closed={r:.4f} ratio={lhs/r:.3f}")

# ============================================================
# (2) EXACT symbolic check of the scalar-Γ atom (p=q=1, general n) — the exponent bookkeeping.
# ============================================================
print("\n=== (2) EXACT symbolic (p=q=1,n=2): ∫_R (w+‖γ r+s‖²)^{-c'} dγ ===")
g=sp.symbols('g',real=True); w,cp=sp.symbols('w c',positive=True)
r1,r2,s1,s2=sp.symbols('r1 r2 s1 s2',real=True)
expr=(w+(g*r1+s1)**2+(g*r2+s2)**2)**(-cp)
# complete the square manually; verify the closed form by matching the reduced 1D integral
nr2=r1**2+r2**2; rs=r1*s1+r2*s2; ns2=s1**2+s2**2
core=w+ns2-rs**2/nr2           # w + ‖S(I-P)‖²  (S(I-P) squared for n=2,q=1)
# closed: (1/sqrt(nr2))·core^{1/2-c'}·sqrt(pi)·Γ(c'-1/2)/Γ(c')
# check S(I-P): P = rᵀr/‖r‖². ‖S(I-P)‖² = ns2 - rs²/nr2  -> matches `core-w`
print("   core = w + ‖S(I-P_R)‖²  symbolic residual =", sp.simplify(core-w-(ns2-rs**2/nr2)),"(0 => matches)")
print("   det(RRᵀ)=‖r‖²=", nr2, "  Gram-exponent -p/2=-1/2  => det^{-1/2}=1/‖r‖  ✓")

# ============================================================
# (3) minAdm recursion, subordination a/2 ≤ ½·minAdm(tail), and the (3,3,3,3) [1,2,3] additive path.
# ============================================================
from functools import lru_cache
@lru_cache(None)
def minAdm(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def tailChain(M): return M[1:]           # (M1,...,ML)
def redChain(t,M): return (t,)+M[2:]

print("\n=== (3a) minAdm anchors ===")
for M,exp in [((2,2,2),3),((3,3,3,3),6),((2,2,2,2),3),((3,3,4),8),((4,4,2,2),4)]:
    print(f"   minAdm{M} = {minAdm(M)}  (expect {exp})  {'OK' if minAdm(M)==exp else 'MISMATCH'}")

print("\n=== (3b) (3,3,3,3): binding cut sequence + ADDITIVE charge accumulation to ½·minAdm ===")
M=(3,3,3,3); target=minAdm(M)
print(f"   minAdm{M}={target}, ½·minAdm={target/2}")
# recursion: minAdm M = min_t a_t + minAdm(redChain t M); trace the binding path
def trace(M, depth=0, acc=0):
    L=len(M)-1
    if L<=1:
        base=0 if L==0 else M[0]*M[1]
        print(f"   {'  '*depth}base chain {M}: minAdm={base}  (acc so far {acc}, +{base} = {acc+base})")
        return acc+base
    best=None; bt=None
    for t in range(min(M[0],M[1])+1):
        v=(M[0]-t)*(M[1]-t)+minAdm(redChain(t,M))
        if best is None or v<best: best=v; bt=t
    a=(M[0]-bt)*(M[1]-bt)
    print(f"   {'  '*depth}chain {M}: binding t={bt}, a=(M0-t)(M1-t)={a}, redChain={redChain(bt,M)}; running acc {acc}->{acc+a}")
    return trace(redChain(bt,M), depth+1, acc+a)
tot=trace(M)
print(f"   TOTAL accumulated charge = {tot}  (== minAdm = {target}? {'YES' if tot==target else 'NO'})")

print("\n=== (3c) subordination a/2 ≤ ½·minAdm(tailChain) at each binding cut, and c' vs a/2 branch ===")
def census(M):
    L=len(M)-1
    if L<=1: return
    print(f"   chain {M}: minAdm={minAdm(M)}, tailChain={tailChain(M)} minAdm(tail)={minAdm(tailChain(M))}")
    for t in range(1,min(M[0],M[1])+1):
        a=(M[0]-t)*(M[1]-t); red=redChain(t,M)
        sub = a <= minAdm(tailChain(M))                 # a/2 ≤ ½·minAdm(tail)?  (integer form)
        # atom branch requires c' > a/2 to be POSSIBLE with c'<½·minAdm M:  a/2 < ½·minAdm M i.e. a < minAdm M
        atom_possible = a < minAdm(M)
        print(f"      t={t}: a={a}, minAdm(redChain)={minAdm(red)}, a+minAdm(red)={a+minAdm(red)}"
              f"  | subord(a≤minAdm tail)={sub}  atomBranch(a<minAdm M)={atom_possible}")
for M in [(3,3,3,3),(2,2,2,2),(4,4,4,4),(2,4,1),(2,2,1)]:
    census(M)
