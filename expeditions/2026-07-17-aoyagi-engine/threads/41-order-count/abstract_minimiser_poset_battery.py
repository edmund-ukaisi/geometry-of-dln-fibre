import importlib.util
src=open("expeditions/2026-07-17-aoyagi-engine/threads/37-paper-mining/edgespec_traversal_334.py").read().split('if __name__')[0]
ns={}; exec(src,ns)
build=ns['build']; State=ns['State']; collect_leaves=ns['collect_leaves']; mval=ns['mval']; t_tilde=ns['t_tilde']
from itertools import product as iproduct
def runmin(M,j): return min(M[:j+2])
def adm_correct(M):
    L=len(M)-1; rng=[range(0,runmin(M,p)+1) for p in range(L)]
    return [pr for pr in iproduct(*rng) if pr[-1]==0 and all(pr[i]>=pr[i+1] for i in range(L-1))]
def adm_loose(M):
    L=len(M)-1; rng=range(0,min(M[0],M[1])+1)
    return [pr for pr in iproduct(*[rng]*L) if pr[-1]==0 and all(pr[i]>=pr[i+1] for i in range(L-1))]
def le(a,b): return all(a[i]<=b[i] for i in range(len(a)))
def max_chain(profs):
    dp={}
    for p in sorted(profs,key=sum):
        dp[p]=1
        for q in profs:
            if q!=p and le(q,p): dp[p]=max(dp[p],dp.get(q,0)+1)
    return max(dp.values()) if dp else 0
def treeRho(M):
    ns['EDGES']=[]; root=State(0,0,[]); tree=build(M,root,[]); leaves=[]; collect_leaves(tree,leaves)
    mA=min(mval(M,p) for p in adm_loose(M))
    return max((sum(1 for (pr,e) in lf["divs"] if t_tilde(pr)==0 and e==mA) for lf in leaves),default=0)
mism=0; cnt=0; ex=[]
for L in range(1,4):
    for w in iproduct(range(1,6),repeat=L+1):
        M=list(w); cnt+=1
        A=adm_correct(M); m=min(mval(M,p) for p in A)
        mc=max_chain([p for p in A if mval(M,p)==m])
        rho=treeRho(M)
        if mc!=rho:
            mism+=1
            if mism<=10: ex.append((M,mc,rho))
print(f"abstract-correct-lattice max-chain == tree-ρ in {cnt-mism}/{cnt} (L=1..3, widths 1..5)")
for e in ex: print("  MISMATCH M,maxchain,ρ =",e)

# --- seat-E (2026-07-21): abstract (tree-free) confirmation of the Core-pure core ---
# max chain of the ABSTRACT correct-lattice (running-min rank-bounded) binding-minimiser poset
# == tree-ρ in 769/775 (L≤3, widths 1..5). The 6 exceptions are ALL degenerate minMval=0 collapses
# (a width-1 layer, tree-ρ=0, lambdaCore=0 — ρ not meaningful). So on the NON-DEGENERATE regime
# (all reduced widths positive ⟺ lambdaCore ≠ 0 ⟺ minMval ≥ 1), the tree-free identity
#   max chain(binding minimisers) = ρ = a(ℓ−a)+1
# holds cleanly. This is the render's DOMAIN CONDITION (weakest hypothesis) and confirms the
# UPPER/ATTAINMENT abstract core is genuinely Core-pure (no tree in the abstract lemma).
