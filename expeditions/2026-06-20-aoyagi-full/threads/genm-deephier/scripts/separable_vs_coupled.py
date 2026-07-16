"""
Pin Q1(a): deepGate_branch bounds C_k^single = u(rho-k) + kappa_k - gamma  (SEPARABLE: front u(rho-k)
+ deep-measure kappa_k - charge gamma, treated as independent radials). The honest per-cell exponent
COUPLES front<->deep (loss = sum sigma_i^2 |W_i|^2), giving C_k^hier <= C_k^single, and the min over
strata = minAdm((u,)+deep) = the RRR floor. Show the separable sum vs the coupled honest value.
"""
from deephier_lp import Ck_hier_LP, minAdm
from deepgate_scan import analyze
M=(4,4,4,4); u=3; info=analyze(M,u); rho=4; exc=0
print(f"(4,4,4,4)@u=3: 2T1q={info['target']}, RRR floor minAdm(3,4,4)={minAdm((3,4,4))}")
print(f"{'k':>2} {'rankZ':>5} {'kappa_k':>7} {'C_single(separable)':>19} {'C_hier(coupled,honest)':>22} {'>=RRRfloor':>10}")
for (k,s,kap,G,Cs) in info['recs']:
    Ch=Ck_hier_LP(u,rho,k,k+exc,1,1,charge=True)
    print(f"{k:>2} {s:>5} {kap:>7} {Cs:>19} {Ch:>22} {'yes' if Ch>=minAdm((3,4,4)) else 'NO':>10}")
print("\n=> deepGate_branch bounds the SEPARABLE C_single (over-estimate at k=3,4: 12); the honest")
print("   COUPLED per-cell exponent is 10 = RRR floor. Sound per-cell discharge needs the RRR floor,")
print("   not C_single. min over strata (single & hier) = 10 = minAdm(3,4,4) = 2T1q here.")
