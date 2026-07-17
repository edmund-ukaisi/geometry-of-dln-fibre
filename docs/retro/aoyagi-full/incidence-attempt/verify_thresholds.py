import sympy as sp
from itertools import product

# ============================================================
# minAdm for L=0 chain (M0,M1,M2): min_r [(M0-r)(M1-r) + r*M2], r=0..min(M0,M1)
# ============================================================
def codim_r(M0,M1,M2,r): return (M0-r)*(M1-r)+r*M2
def minAdm(M0,M1,M2):
    rs=range(0,min(M0,M1)+1)
    vals={r:codim_r(M0,M1,M2,r) for r in rs}
    m=min(vals.values()); argmins=[r for r,v in vals.items() if v==m]
    return m, argmins, vals

for M in [(2,2,3),(4,4,4),(3,3,3),(6,6,6),(4,4,8)]:
    m,arg,vals=minAdm(*M)
    print(f"M={M}: minAdm={m} (T1={sp.Rational(m,2)}), argmin r={arg}, codims={vals}")
print()

# ============================================================
# REGIME I local-model threshold (R floored, corank-j incidence on shell-j, j<=b).
# After integrating D1 = M0*(M1-j) O(1)-quadratic dirs (valid c'>D1/2), the reduced
# integral J over (tau_1..tau_j in [0,eps], W_1..W_j in box R^{M0}) with weight
#   prod tau_i^{alpha} * Vandermonde(tau)   (alpha=(n-u)-b),  integrand (sum tau_i^2||W_i||^2)^{-s}, s=c'-D1/2.
#
# CORANK-1 (j=1, no Vandermonde): integral factors:
#   int_0^eps tau^{alpha-2s} dtau  (conv iff 2s<alpha+1)   x   int_box ||W||^{-2s} dW  (conv iff 2s<M0)
#   => s-threshold = min(alpha+1, M0)/2 ;  c'_thr = D1/2 + min(alpha+1,M0)/2
def regimeI_corank1_threshold(M0,M1,M2,u):
    a=M0-u; b=M1-u; n=M2; j=1
    D1=M0*(M1-j); alpha=(n-u)-b
    s_thr=sp.Rational(min(alpha+1, M0),2)
    cp_thr=sp.Rational(D1,2)+s_thr
    return cp_thr, dict(D1=D1,alpha=alpha,a=a,b=b)

# CORANK-j via W-substitution W_i=w_i/tau_i (VALID iff alpha-M0 > -1):
#   int_{R^{M0 j}}(sum||w_i||^2)^{-s} conv iff 2s<M0*j  ; leftover int prod tau^{alpha-M0} Vand dtau
#   conv (tau->0) iff alpha-M0>-1 (per var, c'-independent) . So s-threshold = M0*j/2 when valid.
def regimeI_corankj_threshold_via_sub(M0,M1,M2,u,j):
    a=M0-u; b=M1-u; n=M2
    D1=M0*(M1-j); alpha=(n-u)-b
    sub_valid = (alpha-M0 > -1)
    if sub_valid:
        s_thr=sp.Rational(M0*j,2)
        cp_thr=sp.Rational(D1,2)+s_thr
        return cp_thr, dict(D1=D1,alpha=alpha,sub_valid=True,note="s_thr=M0*j/2")
    else:
        return None, dict(D1=D1,alpha=alpha,sub_valid=False,note="W-sub INVALID (alpha-M0<=-1): use factored/Vandermonde analysis")

print("=== Corner (i): (2,2,3) u=1 j=1 ===")
cp,info=regimeI_corank1_threshold(2,2,3,1); print("  Regime-I corank-1 c'-threshold =",cp,info,"  T1=2")

print("=== Corner (ii): (4,4,4) u=3 j=1 (non-argmin cut; argmin r=2) ===")
cp,info=regimeI_corank1_threshold(4,4,4,3); print("  Regime-I corank-1 c'-threshold =",cp,info," T1=6, T2 (false)=6.5")

print("=== Corner (iii): (4,4,8) u=2 j=2 (corank-2, t*=0) ===")
cp,info=regimeI_corankj_threshold_via_sub(4,4,8,2,2); print("  Regime-I corank-2 c'-threshold =",cp,info," T1=8")
cp1,info1=regimeI_corank1_threshold(4,4,8,1); print("  (compare corank-1 (4,4,8)u=1:",cp1,")")

print()
print("=== Scan: Regime-I threshold vs T1 across cuts/coranks (t*=0 family (m,m,N)) ===")
for (M0,M1,M2) in [(4,4,8),(3,3,7),(5,5,12)]:
    m,arg,_=minAdm(M0,M1,M2); T1=sp.Rational(m,2)
    print(f" M=({M0},{M1},{M2}) T1={T1} argmin={arg}")
    for j in range(1, min(M0,M1)):
        u=0+j  # t*=0
        if M1-u<1: continue
        if j==1: cp,_=regimeI_corank1_threshold(M0,M1,M2,u)
        else: cp,_=regimeI_corankj_threshold_via_sub(M0,M1,M2,u,j)
        print(f"   u={u} j={j}: Regime-I c'-thr={cp}  (>=T1? {cp>=T1 if cp is not None else 'n/a'})")
