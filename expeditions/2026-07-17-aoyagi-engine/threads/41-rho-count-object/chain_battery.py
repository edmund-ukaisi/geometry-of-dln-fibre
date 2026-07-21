#!/usr/bin/env python3
"""
Thread-41 CHAIN-reading confirmation (pnp, decorrelated — my own enumeration, written before reading
seat-E's chain_vs_antichain_battery.py in detail).

CLAIM to confirm/refute (elder-mandated, corrects my earlier ANTICHAIN speculation which is the
Dilworth DUAL of the truth):
  (A) on EVERY root-to-leaf branch (leaf), the binding (t̃=0, exp=minAdm) divisor profiles present are
      pairwise componentwise-comparable — a CHAIN under ≤.
  (B) ρ = max CHAIN length in the binding-minimiser poset = a(ℓ−a)+1 (both directions), and this equals
      thread-41's max-crossing ρ.
  (C) my earlier "max antichain" reading is WRONG: max antichain ≠ a(ℓ−a)+1 in general.
"""
import sys, os, importlib.util
from itertools import product as iproduct, combinations

EDGE = "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/expeditions/2026-07-17-aoyagi-engine/threads/37-paper-mining/edgespec_traversal_334.py"
spec = importlib.util.spec_from_file_location("edge334", EDGE); edge = importlib.util.module_from_spec(spec); spec.loader.exec_module(edge)

ok = True
def check(name, cond):
    global ok; c = bool(cond); ok &= c
    print(f"  [{'PASS' if c else 'FAIL'}] {name}")

_LC = {}
def tree_leaves(M):
    k = tuple(M)
    if k not in _LC:
        edge.EDGES = []; t = edge.build(M, edge.State(0,0,[]), []); L=[]; edge.collect_leaves(t,L); _LC[k]=L
    return _LC[k]
def minAdm(M):
    b = None
    for lf in tree_leaves(M):
        for (pr,ex) in lf["divs"]:
            if min(pr)==0: b = ex if b is None else min(b,ex)
    return b
def def3_a_ell(M):
    w=sorted(M); n=len(w); bm=2
    for m in range(2,n+1):
        if w[m-1]*(m-1) < sum(w[:m]): bm=m
    m=bm; ell=m-1; P=sum(w[:m]); Ms=-(-P//ell); a=P-(Ms-1)*ell; return a,ell
def rho_formula(M): a,ell=def3_a_ell(M); return a*(ell-a)+1

# --- poset order on profiles ---
def leq(u,v): return all(u[i]<=v[i] for i in range(len(u)))
def is_chain(S):
    S=list(S)
    return all(leq(S[i],S[j]) or leq(S[j],S[i]) for i in range(len(S)) for j in range(i+1,len(S)))
def max_chain_len(P):
    """longest chain in poset P under ≤ (longest path in the strict-< DAG; DP over a linear extension)."""
    P=list(P)
    # sort by coordinate-sum so u<v ⟹ u before v
    P.sort(key=lambda t: sum(t))
    best={}; ans=0
    for j,v in enumerate(P):
        b=1
        for i in range(j):
            u=P[i]
            if u!=v and leq(u,v):
                b=max(b, best[i]+1)
        best[j]=b; ans=max(ans,b)
    return ans
def max_antichain_len(P):
    """largest pairwise-INCOMPARABLE subset (brute; P is small)."""
    P=list(P); n=len(P)
    best=0
    # greedy upper then exact for small n
    if n>18:  # fallback: Dilworth (max antichain = min chain cover) — but n stays small here
        return None
    for r in range(n,0,-1):
        for sub in combinations(range(n),r):
            if all(not leq(P[i],P[j]) and not leq(P[j],P[i]) for i,j in combinations(sub,2)):
                return r
    return 0

def binding_min_set(M):
    """the binding-minimiser poset = distinct t̃=0, exp=minAdm profiles across the atlas."""
    mA=minAdm(M); S=set()
    for lf in tree_leaves(M):
        for (pr,ex) in lf["divs"]:
            if min(pr)==0 and ex==mA: S.add(pr)
    return S, mA
def leaf_binding_sets(M):
    mA=minAdm(M); out=[]
    for lf in tree_leaves(M):
        B={pr for (pr,ex) in lf["divs"] if min(pr)==0 and ex==mA}
        if B: out.append(B)
    return out
def rho_maxcross(M):
    return max(len(B) for B in leaf_binding_sets(M))

# ================= CHECK A: per-leaf binding sets are CHAINS =================
print("=== CHECK A: on every branch, the binding minimisers present form a CHAIN (pairwise ≤-comparable) ===")
notchain=[]
seen=set()
for L in (2,3,4):
    hi = 5 if L<=3 else 3
    for w in iproduct(range(1,hi+1),repeat=L+1):
        M=list(w); k=tuple(M)
        if k in seen: continue
        seen.add(k)
        for B in leaf_binding_sets(M):
            if not is_chain(B): notchain.append((M,sorted(B)))
print(f"  scanned {len(seen)} cores; leaves with a NON-chain binding set: {len(notchain)}")
for (M,B) in notchain[:6]: print(f"    NON-CHAIN M={M}: {B}")
check("every leaf's binding-minimiser set is a CHAIN (pairwise componentwise-comparable)", len(notchain)==0)

# ================= CHECK B: ρ = max chain = a(ℓ−a)+1 (both directions) =================
print("\n=== CHECK B: ρ = max-chain(binding poset) = a(ℓ−a)+1 = max-crossing, over kill-set + scan ===")
GROUND={(2,2,2):1,(3,3,4):1,(2,2,3,2):1,(2,2,2,2):3,(2,1,2):2}
for Mt,rk in GROUND.items():
    M=list(Mt); P,mA=binding_min_set(M); mc=max_chain_len(P); rf=rho_formula(M); rx=rho_maxcross(M)
    print(f"  M={M}: |poset|={len(P)}  max-chain={mc}  max-crossing={rx}  a(ℓ−a)+1={rf}  known ρ={rk}")
    check(f"M={M}: max-chain == max-crossing == a(ℓ−a)+1 == known ρ ({rk})", mc==rx==rf==rk)
mism=[]; both=[]
seen2=set()
for L in (2,3,4):
    hi = 5 if L<=3 else 3
    for w in iproduct(range(1,hi+1),repeat=L+1):
        M=list(w); k=tuple(M)
        if k in seen2: continue
        seen2.add(k)
        P,mA=binding_min_set(M); mc=max_chain_len(P); rf=rho_formula(M); rx=rho_maxcross(M)
        if not (mc==rx==rf): mism.append((M,mc,rx,rf))
print(f"  scanned {len(seen2)} cores; (max-chain, max-crossing, formula) mismatches: {len(mism)}")
for (M,mc,rx,rf) in mism[:8]: print(f"    MISMATCH M={M}: chain={mc} cross={rx} formula={rf}")
check("max-chain == max-crossing == a(ℓ−a)+1 for EVERY scanned core (both directions of the chain reading)",
      len(mism)==0)

# ================= CHECK C: the [2,2,2,2,2] witness + the antichain reading is WRONG =================
print("\n=== CHECK C: [2,2,2,2,2] chain witness + REFUTE the antichain reading ===")
M=[2,2,2,2,2]; P,mA=binding_min_set(M)
mc=max_chain_len(P); ma=max_antichain_len(P); rf=rho_formula(M)
print(f"  [2,2,2,2,2]: poset={sorted(P)}")
print(f"    max-chain={mc}  max-antichain={ma}  a(ℓ−a)+1={rf}")
# the specific comparabilities from the controller's note
p1110=(1,1,1,0); p2100=(2,1,0,0)
print(f"    (1,1,1,0) vs (2,1,0,0): ≤ either way? {leq(p1110,p2100) or leq(p2100,p1110)}  (incomparable ⟹ breaks a 6-chain)")
check("[2,2,2,2,2]: max-chain = 5 = a(ℓ−a)+1 (chain reading correct)", mc==5==rf)
check("[2,2,2,2,2]: (1,1,1,0) and (2,1,0,0) are INCOMPARABLE (why no 6-chain)",
      not(leq(p1110,p2100) or leq(p2100,p1110)))
# refute antichain reading: find a core where max-antichain != formula
anti_wrong=[]
for Mt in [(2,2,2,2,2),(2,2,2,2),(3,3,4),(2,2,2)]:
    M=list(Mt); P,_=binding_min_set(M); ma=max_antichain_len(P); rf=rho_formula(M)
    if ma!=rf: anti_wrong.append((M,ma,rf))
print(f"  antichain-reading counterexamples (max-antichain ≠ a(ℓ−a)+1): {anti_wrong}")
check("the ANTICHAIN reading is WRONG (∃ core with max-antichain ≠ a(ℓ−a)+1) — my earlier speculation refuted",
      len(anti_wrong)>0)

# ================= CHECK D: the MECHANISM — poset is graded between the Lemma-4 envelope endpoints =====
print("\n=== CHECK D: mechanism — binding poset has unique min T̃/max T̃', graded by coord-sum, ")
print("             max-chain = (sum(T̃')−sum(T̃))+1 = a(ℓ−a)+1 (the exponent-accumulation nesting) ===")
def unique_min(P):
    cands=[u for u in P if all(leq(u,v) for v in P)]
    return cands[0] if len(cands)==1 else None
def unique_max(P):
    cands=[u for u in P if all(leq(v,u) for v in P)]
    return cands[0] if len(cands)==1 else None
def covers(P):
    """covering relations u⋖v (no w strictly between)."""
    P=list(P); C=[]
    for u in P:
        for v in P:
            if u!=v and leq(u,v) and not any(w!=u and w!=v and leq(u,w) and leq(w,v) for w in P):
                C.append((u,v))
    return C
def min_maximal_chain(P):
    """SHORTEST saturated chain (covering steps) from the unique min to the unique max."""
    import collections
    P=list(P); C=covers(P)
    mn=[u for u in P if all(leq(u,v) for v in P)][0]
    mx=[u for u in P if all(leq(v,u) for v in P)][0]
    adj=collections.defaultdict(list)
    for (u,v) in C: adj[u].append(v)
    # BFS shortest #vertices from mn to mx along covers
    dist={mn:1}; q=collections.deque([mn])
    while q:
        u=q.popleft()
        for v in adj[u]:
            if v not in dist: dist[v]=dist[u]+1; q.append(v)
    return dist.get(mx)
def is_graded(P):
    """graded ⟺ every maximal chain min→max has the same length ⟺ shortest == longest."""
    return min_maximal_chain(P)==max_chain_len(P)
nomin=[]; graded_fail_nondegen=[]; graded_holds_nondegen=0
seen3=set()
for L in (2,3,4):
    hi = 5 if L<=3 else 3
    for w in iproduct(range(1,hi+1),repeat=L+1):
        M=list(w); k=tuple(M)
        if k in seen3: continue
        seen3.add(k)
        P,_=binding_min_set(M)
        a,ell=def3_a_ell(M); rf=a*(ell-a)+1
        mn=unique_min(P); mx=unique_max(P)
        # (D1) UNIVERSAL: unique min & max (Lemma-4 envelope endpoints T̃, T̃')
        if mn is None or mx is None: nomin.append((M,sorted(P)))
        # (D3) UNIVERSAL gradedness BY RANK: every maximal chain min→max has length a(ℓ−a)+1
        #      (the correct grading is by inversions / Young-cell count, NOT profile coord-sum)
        if mn is not None and mx is not None:
            if min_maximal_chain(P)==max_chain_len(P)==rf:
                graded_holds_nondegen+=1
            else:
                graded_fail_nondegen.append((M,min_maximal_chain(P),max_chain_len(P),rf))
print(f"  scanned {len(seen3)} cores.")
check("(D1) UNIVERSAL: the binding poset has a UNIQUE min T̃ and UNIQUE max T̃' (Lemma-4 envelope) — every core",
      len(nomin)==0)
for (M,P) in nomin[:5]: print(f"    NO unique min/max M={M}: {P}")
print(f"  (D3) GRADED-BY-RANK (every maximal chain min→max = a(ℓ−a)+1): holds {graded_holds_nondegen}, "
      f"fails {len(graded_fail_nondegen)}")
for (M,lo,hi_,rf) in graded_fail_nondegen[:5]: print(f"    graded-fail M={M}: shortest={lo} longest={hi_} formula={rf}")
check("(D3) UNIVERSAL: binding poset GRADED by rank — all maximal T̃→T̃' chains have length a(ℓ−a)+1 "
      "(height = ρ; the clean Lean-facing mechanism, coord-sum grading is NOT it)", len(graded_fail_nondegen)==0)
# illustrate the envelope on [2,2,2,2,2]
M=[2,2,2,2,2]; P,_=binding_min_set(M); a,ell=def3_a_ell(M)
mn=unique_min(P); mx=unique_max(P)
print(f"  [2,2,2,2,2]: T̃(min)={mn}  T̃'(max)={mx}  T̃'−T̃ sums to {sum(mx)-sum(mn)}=a(ℓ−a)={a*(ell-a)}; "
      f"a saturated coord-sum chain has {a*(ell-a)+1} vertices = ρ")

print(f"\nTHREAD-41 CHAIN-READING CONFIRMATION: {'PASS (EXIT 0)' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
