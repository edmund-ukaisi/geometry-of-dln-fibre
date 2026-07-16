import numpy as np
rng = np.random.default_rng(2027)

# ============ PART (2): the HONEST coupled inner integral, edge params ============
# H(w) = int_{A_cor in [-1,1]^{2x3}} int_{Gamma in [-1,1]^{2x2}}
#          ( w + frobSq( Ccross + Gamma @ (A_cor @ Zf) ) )^{-c'}   dGamma dA_cor
# edge: a=b=2, rho=3, Zf = 3x3 rank 3, Ccross = 2x3 generic.
# Fit H(w) ~ w^{-beta}; reduction = c' - beta.  Need reduction >= 1 to lift 3.5 -> >=4.5.
# The front-charge OVERESTIMATE would give beta = c' - ab/2 = c' - 2 (reduction 2) TIMES Ch(Zf)=+inf.

Zf = rng.standard_normal((3,3))          # generic rank-3
Ccross = rng.standard_normal((2,3))      # generic cross term

def H_of_w(w, cprime, N=6_000_000):
    A = rng.uniform(-1,1,size=(N,2,3))
    G = rng.uniform(-1,1,size=(N,2,2))
    M = np.einsum('nij,jk->nik', A, Zf)          # A_cor @ Zf : 2x3
    GM = np.einsum('nij,njk->nik', G, M)         # Gamma @ M : 2x3
    base = w + np.sum((Ccross[None,:,:] + GM)**2, axis=(1,2))
    vol = (2.0**(2*3))*(2.0**(2*2))
    return vol * np.mean(base**(-cprime))

print("=== PART (2): honest coupled H(w) ~ w^{-beta}, edge a=b=2 rho=3 ===")
ws = np.array([2.0**(-k) for k in range(0,13)])
for cprime in [2.5, 3.5, 4.0, 4.49]:
    Hs = np.array([H_of_w(w, cprime) for w in ws])
    # fit slope in log-log over the small-w tail (last 7 pts)
    lo = 5
    b, a = np.polyfit(np.log(ws[lo:]), np.log(Hs[lo:]), 1)
    beta = -b
    print(f" c'={cprime:4.2f}: beta={beta:6.3f}  reduction=c'-beta={cprime-beta:5.3f}  "
          f"(trivial red=0 -> thr 3.5; need red>=1 for 4.5; charge red=2 -> 5.5)")
    print(f"        H(w) tail:", "  ".join(f"{h:.3g}" for h in Hs[-5:]))

# Control: the SEPARATED front charge Ch(Zf) = int_Acor det((A Zf)(A Zf)^T)^{-a/2}, should DIVERGE (edge)
print()
print("=== control: separated front charge Ch(Zf), edge (should DIVERGE, per Q1) ===")
def Ch(N=6_000_000, a=2):
    A = rng.uniform(-1,1,size=(N,2,3))
    M = np.einsum('nij,jk->nik', A, Zf)
    Gr = np.einsum('nij,nkj->nik', M, M)          # (A Zf)(A Zf)^T : 2x2
    det = np.maximum(np.linalg.det(Gr),0.0)
    # dyadic shell masses
    vol=2.0**(2*3)
    for k in range(14):
        hi=2.0**(-k); lo=2.0**(-(k+1))
        m=(det>lo)&(det<=hi)
        val=vol*np.mean((det[m]**(-a/2.0))*(m[m].astype(float)))*m.mean() if m.sum()>0 else 0.0
        # simpler: contribution
        contrib = vol*np.sum(det[m]**(-a/2.0))/N if m.sum()>0 else 0.0
        print(f"   k={k:2d} shell-mass={contrib:10.3f} n={int(m.sum())}") if k<8 else None
Ch()
