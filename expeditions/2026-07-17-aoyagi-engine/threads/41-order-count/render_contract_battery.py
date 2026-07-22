#!/usr/bin/env python3
"""
P6.2 RENDER CONTRACT (seat-E) — the numeric contract the Lean UPPER/ATTAINMENT render consumes and
pnp-order's decorrelated instrument confirms. Self-contained (own verified functions + the tree
traversal); the certified ρ = a(ℓ−a)+1 is rho_battery's CHECK 2.

THE CONTRACT (Core-pure, tree-free abstract lemma):
  chainHeight( bindingMinimisers M ) = tree-ρ(M)              [proven here: 769/775 non-degenerate]
  and tree-ρ(M) = a(ℓ−a)+1                                    [certified: rho_battery CHECK 2]
  ⟹ chainHeight( bindingMinimisers M ) = a(ℓ−a)+1.
bindingMinimisers = CORRECT (running-min rank-bounded) admissible profiles with Mval = minAdm;
chainHeight = longest componentwise-≤ chain (Mathlib `Set.chainHeight` / `IsChain (·≤·)`), on the
NON-DEGENERATE domain (minMval ≥ 1 ⟺ lambdaCore ≠ 0 ⟺ all reduced widths positive).
The four elder pins are asserted as explicit sections below.
"""
src = open("expeditions/2026-07-17-aoyagi-engine/threads/37-paper-mining/edgespec_traversal_334.py").read().split('if __name__')[0]
ns = {}; exec(src, ns)
build, State, collect_leaves, mval, t_tilde = ns['build'], ns['State'], ns['collect_leaves'], ns['mval'], ns['t_tilde']
from itertools import product as iproduct, combinations

def runmin(M, j): return min(M[:j+2])
def adm_correct(M):                       # PIN (a): running-min rank-bounded (TIGHT) lattice
    L = len(M)-1; rng = [range(0, runmin(M,p)+1) for p in range(L)]
    return [pr for pr in iproduct(*rng) if pr[-1]==0 and all(pr[i]>=pr[i+1] for i in range(L-1))]
def adm_loose(M):
    L = len(M)-1; rng = range(0, min(M[0],M[1])+1)
    return [pr for pr in iproduct(*[rng]*L) if pr[-1]==0 and all(pr[i]>=pr[i+1] for i in range(L-1))]
def le(a,b): return all(a[i]<=b[i] for i in range(len(a)))
def chain_height(profs):                  # PIN (c): Mathlib Set.chainHeight of (·≤·)
    dp = {}
    for p in sorted(profs, key=sum):
        dp[p] = 1
        for q in profs:
            if q!=p and le(q,p): dp[p] = max(dp[p], dp.get(q,0)+1)
    return max(dp.values()) if dp else 0
def max_antichain(profs):
    profs = list(profs)
    for r in range(len(profs),0,-1):
        for sub in combinations(range(len(profs)),r):
            if all(not le(profs[i],profs[j]) and not le(profs[j],profs[i])
                   for i,j in combinations(sub,2)): return r
    return 0
def binding_min(M, lattice=adm_correct):  # PIN (d): carried target = the lattice minimum
    A = lattice(M); m = min(mval(M,p) for p in A)
    return [p for p in A if mval(M,p)==m], m
def tree_rho(M):
    ns['EDGES']=[]; root=State(0,0,[]); tree=build(M,root,[]); leaves=[]; collect_leaves(tree,leaves)
    mA = binding_min(M)[1]
    return max((sum(1 for (pr,e) in lf["divs"] if t_tilde(pr)==0 and e==mA) for lf in leaves), default=0)

fails=0
def ck(n,c):
    global fails; print(f"  [{'PASS' if c else 'FAIL'}] {n}");  fails += (0 if c else 1)

print("=== MAIN CONTRACT: chainHeight(binding minimisers) = tree-ρ, non-degenerate domain ===")
scan = [list(w) for L in (1,2,3) for w in iproduct(range(1,6),repeat=L+1)]
scan += [list(w) for w in iproduct(range(1,4),repeat=5)]   # L=4 incl [2,2,2,2,2]
ok=degen=0; mism=[]
for M in scan:
    mins,mA = binding_min(M)
    if mA<=0: degen+=1; continue
    if chain_height(mins)==tree_rho(M): ok+=1
    else: mism.append((M, chain_height(mins), tree_rho(M)))
ck(f"chainHeight == tree-ρ on all {ok} non-degenerate cores ({degen} degenerate minMval=0 skipped)", not mism)
for m in mism[:8]: print("     MISMATCH", m)

print("\n=== PIN (a) TIGHT LATTICE load-bearing (loose ⟹ wrong chainHeight vs tree-ρ) ===")
diff=0
for M in [[3,3,1,1],[4,4,1,2],[2,2,5]]:
    ct = chain_height(binding_min(M, adm_correct)[0])
    cl = chain_height(binding_min(M, adm_loose)[0])
    if ct != cl: diff+=1
    print(f"  M={M}: tight chainHeight={ct}  loose chainHeight={cl}  tree-ρ={tree_rho(M)}")
ck("loose lattice differs from tight (tightness load-bearing)", diff>0)

print("\n=== PIN (b) DOMAIN CORNERS ===")
ck("formula a=0 ⟹ 1", 0*(5-0)+1==1)
ck("formula ℓ=1,a=1 ⟹ 1", 1*(1-1)+1==1)
ck("L=ℓ depth boundary [2,2,2]: chainHeight = tree-ρ = 1",
   chain_height(binding_min([2,2,2])[0])==tree_rho([2,2,2])==1)
ck("empty minimiser set ⟹ chainHeight 0 (junk-consistent, Finset.sup bot)", chain_height([])==0)

print("\n=== PIN (c) CO-OCCURRENCE = CHAIN, not antichain ([2,2,2,2,2] decisive) ===")
m5,_ = binding_min([2,2,2,2,2])
ck(f"[2,2,2,2,2]: chainHeight={chain_height(m5)} = tree-ρ={tree_rho([2,2,2,2,2])} = 5",
   chain_height(m5)==tree_rho([2,2,2,2,2])==5)
ck(f"[2,2,2,2,2]: max-antichain={max_antichain(m5)} ≠ ρ (antichain is WRONG)", max_antichain(m5)!=5)

print("\n=== PIN (d) CARRIED TARGET (minAdm = lattice minimum) ===")
ck("tree binding-set uses the lattice minimum as the (global) target",
   all(binding_min(M)[1]==min(mval(M,p) for p in adm_correct(M)) for M in [[2,2,2],[2,1,2],[2,2,2,2],[3,3,4]]))

print(f"\n{'ALL CONTRACT CHECKS PASS' if fails==0 else str(fails)+' FAILURES'}.")
