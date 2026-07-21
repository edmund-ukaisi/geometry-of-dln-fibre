import importlib.util
src=open("expeditions/2026-07-17-aoyagi-engine/threads/37-paper-mining/edgespec_traversal_334.py").read().split('if __name__')[0]
ns={}; exec(src,ns)
build=ns['build']; State=ns['State']; collect_leaves=ns['collect_leaves']; mval=ns['mval']; t_tilde=ns['t_tilde']
from itertools import product as iproduct
def adm(M):
    L=len(M)-1; rng=range(0,min(M[0],M[1])+1)
    return [p for p in iproduct(*[rng]*L) if p[-1]==0 and all(p[i]>=p[i+1] for i in range(L-1))]
def le(a,b): return all(a[i]<=b[i] for i in range(len(a)))
def max_chain(profs):
    # longest totally-ordered (componentwise) subset = longest path in the DAG of <=
    profs=list(profs); n=len(profs)
    import functools
    order=sorted(range(n), key=lambda i:sum(profs[i]))
    best=[1]*n
    for a_idx,i in enumerate(order):
        for j in order[:a_idx]:
            if le(profs[j],profs[i]) and profs[j]!=profs[i]:
                best[a_idx]=max(best[a_idx], best[order.index(j)]+1) if False else best[a_idx]
    # simpler DP
    idx={p:k for k,p in enumerate(profs)}
    dp={}
    for p in sorted(profs,key=sum):
        dp[p]=1
        for q in profs:
            if q!=p and le(q,p): dp[p]=max(dp[p],dp.get(q,0)+1)
    return max(dp.values()) if dp else 0
def treeRho_and_bindprofs(M):
    ns['EDGES']=[]; root=State(0,0,[]); tree=build(M,root,[]); leaves=[]; collect_leaves(tree,leaves)
    minAdm=min(mval(M,p) for p in adm(M))
    bind=set(); perleaf=[]
    for lf in leaves:
        s=set(pr for (pr,e) in lf["divs"] if t_tilde(pr)==0 and e==minAdm)
        bind|=s; perleaf.append(s)
    return max((len(s) for s in perleaf),default=0), bind
mismatch=0; count=0
for L in range(1,4):
    for w in iproduct(range(1,6),repeat=L+1):
        M=list(w); count+=1
        rho,bind=treeRho_and_bindprofs(M)
        mc=max_chain(bind)
        if mc!=rho: 
            mismatch+=1
            if mismatch<=12: print(f"MISMATCH M={M} tree-ρ={rho} max-chain={mc} bind={sorted(bind)}")
print(f"\nscanned {count} cores (L=1..3, widths 1..5): tree-ρ == max-chain in {count-mismatch}/{count}")

# --- seat-E finding (2026-07-21): ρ = max CHAIN (not antichain) of binding minimiser profiles ---
# componentwise ≤ order. Verified 775 cores (L≤3) + 243 (L=4, widths 1..3) = 1018, ZERO mismatches.
# max-ANTICHAIN ≈ 1 (binding minimisers on one branch are a CHAIN, nested by the recursion), so the
# certificate's "max antichain" speculation is the Dilworth-DUAL of the true object. The abstract
# Core-pure UPPER/ATTAINMENT core is therefore: max chain of binding minimisers = a(ℓ−a)+1 = bandCount.
