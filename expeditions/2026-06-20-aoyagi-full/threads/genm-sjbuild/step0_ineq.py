"""
STEP-0 correction (post-review): the bridge is an INEQUALITY 1/2*minAdm <= threshold, not a tight equality.
Check the precise, defensible statement across ALL load-bearing charts in the sweep:
  - is  N_0 * tau >= minAdm(N)  (tau = min deeper widths)  a valid clean lower bound? (Codex's argument)
  - is  t*N_last + (N_0-t)*tau >= minAdm(N)  (the joint pivot+block count) >= minAdm everywhere?
NO commitment to an exact joint-Morse-dim formula (unproven); this only tests the INEQUALITY has no
counterexample. The rigorous proof is the piece-6 obligation.
"""
from functools import lru_cache
import itertools

@lru_cache(None)
def minAdm(M):
    M=tuple(M); L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def redChain(t,M): return (t,)+tuple(M[2:])
def visit(M,seen):
    M=tuple(M)
    if M in seen or len(M)<3: return []
    seen.add(M); out=[M]
    for t in range(0,min(M[0],M[1])+1): out+=visit(redChain(t,M),seen)
    return out

viol_N0tau=[]; viol_joint=[]; lb_count=0
for arity in [3,4,5]:
    for N0 in itertools.product(range(1,7),repeat=arity):
        for cur in visit(N0,set()):
            m,n,rest=cur[0],cur[1],cur[2:]; mm=minAdm(cur)
            tau=min(rest) if rest else 0; nlast=cur[-1]
            for t in range(1,min(m,n)+1):
                p,q=m-t,n-t; r=min(q,tau) if rest else q
                if rest and r<q and p*r<mm:            # load-bearing
                    lb_count+=1
                    if m*tau < mm: viol_N0tau.append((cur,t,m*tau,mm))
                    if t*nlast+p*tau < mm: viol_joint.append((cur,t,t*nlast+p*tau,mm))

print(f"load-bearing charts examined: {lb_count}")
print(f"N_0*tau >= minAdm  violations: {len(viol_N0tau)}  (first few: {viol_N0tau[:5]})")
print(f"t*N_last+(N_0-t)*tau >= minAdm violations: {len(viol_joint)} (first few: {viol_joint[:5]})")
# report tightness spread of the joint bound on a few anchors
print("\njoint bound vs minAdm on sample load-bearing charts (bound, minAdm, tight?):")
for N in [(3,4,2),(4,4,2),(3,3,1),(4,5,2),(5,5,2,2)]:
    for cur in visit(N,set()):
        m,n,rest=cur[0],cur[1],cur[2:]; mm=minAdm(cur); tau=min(rest) if rest else 0; nlast=cur[-1]
        for t in range(1,min(m,n)+1):
            p,q=m-t,n-t; r=min(q,tau) if rest else q
            if rest and r<q and p*r<mm:
                b=t*nlast+p*tau
                print(f"  N={N} cur={cur} t={t}: joint bound={b}, minAdm={mm}, tight={b==mm}")
