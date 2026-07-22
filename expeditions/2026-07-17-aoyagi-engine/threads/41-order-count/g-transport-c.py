#!/usr/bin/env python3
# guards: enc-transport
# config: (c) transport — the inversion-count adjacent-swap recursion is an order-iso
#         bindingSet(M) → bindingSet(sortedWidths M), both directions; inversions drop by 1 per swap.
# provenance: threads/41-order-count/codex/transport-c-* ; numeric check of the chosen (c) decomposition.
"""Kill-check for obligation (c). Verifies the design: repeatedly swapping an adjacent DESCENT (with
the swapR profile transport) composes to an order-isomorphism bindingSet(M) ≃o bindingSet(sorted M),
and each swap strictly reduces the inversion count. Exit 0 iff all pass over positive-width M, L≤4."""
from itertools import product as iproduct

def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def admissible(M,T):
    L=len(T)
    if any(T[j]>admBound(M,j) for j in range(L)): return False
    for i in range(L):
        for j in range(i,L):
            if T[j]>T[i]: return False
    return L>=1 and T[L-1]==0
def mval(M,T):
    L=len(T); t1=T[0]; tot=(M[0]-t1)*(M[1]-t1)
    for j in range(2,L+1): tot+=(T[j-2]-T[j-1])*(M[j]-T[j-1])
    return tot
def binding(M):
    L=len(M)-1; A=[T for T in iproduct(range(max(M)+1),repeat=L) if admissible(M,T)]
    m=min(mval(M,T) for T in A); return set(T for T in A if mval(M,T)==m)
def swapR(P,X,Q,A,B):
    if A<=B and B-A<=P-X: return X+(B-A)
    if B<A and A-B<=X-Q: return X-(A-B)
    return P+Q-X
def inversions(M): return sum(1 for i in range(len(M)) for j in range(i+1,len(M)) if M[i]>M[j])
def swap_step(M,T,k):  # swap widths k,k+1; transport T (change coord k-1) — k≥1
    M2=list(M); M2[k],M2[k+1]=M2[k+1],M2[k]
    T2=list(T)
    P = M[0] if k==1 else T[k-2]
    T2[k-1]=swapR(P,T[k-1],T[k],M[k],M[k+1])
    return tuple(M2),tuple(T2)
def transport(M,T):  # inversion-count recursion: swap the first adjacent descent until sorted
    M=tuple(M); T=tuple(T)
    while True:
        desc=[k for k in range(len(M)-1) if M[k]>M[k+1]]
        if not desc: return M,T
        k=desc[0]
        assert k>=1, (M,"k=0 descent: M0>M1 but t0=M0 not a profile coord")  # k=0 would need care
        inv_before=inversions(M)
        M,T=swap_step(M,T,k)
        assert inversions(M)==inv_before-1, ("inversion not -1",M,k)

fails=0
def check(n,c):
    global fails
    if not c: fails+=1; print(f"  [FAIL] {n}")

# NOTE: k=0 adjacent descent (M0>M1) is a real case — the swap M0↔M1 changes admBound_0=min(M0,M1)
# (symmetric!) so the profile is UNCHANGED, and t0=M0 vs M1... handle: for k=0 descent, swap widths,
# T unchanged (admBound_0 symmetric). Extend swap_step for k=0:
def swap_step_full(M,T,k):
    if k==0:
        M2=list(M); M2[0],M2[1]=M2[1],M2[0]; return tuple(M2),tuple(T)  # admBound_0 symmetric, T fixed
    return swap_step(M,T,k)
def transport_full(M,T):
    M=tuple(M); T=tuple(T)
    while True:
        desc=[k for k in range(len(M)-1) if M[k]>M[k+1]]
        if not desc: return M,T
        k=desc[0]; ib=inversions(M); M,T=swap_step_full(M,T,k)
        if inversions(M)!=ib-1: return ("INVFAIL",M,k)
    
def leq(u,v): return all(a<=b for a,b in zip(u,v))
seen=set(); invfail=0
for L in range(1,5):
    hi=4 if L<=3 else 3
    for M in iproduct(range(1,hi+1),repeat=L+1):
        if M in seen: continue
        seen.add(M)
        Ms=tuple(sorted(M))
        BM=binding(M); BS=binding(Ms)
        # transport each binding T of M; check lands in BS, bijection, order-embedding both ways
        img={}
        ok=True
        for T in BM:
            res=transport_full(M,T)
            if isinstance(res[0],str): invfail+=1; ok=False; break
            Mt,Tt=res
            if Mt!=Ms or Tt not in BS: ok=False; break
            img[T]=Tt
        if not ok: check(f"transport lands in bindingSet(sorted) M={M}",False); continue
        if set(img.values())!=BS or len(set(img.values()))!=len(BM):
            check(f"bijection bindingSet(M)→bindingSet(sorted) M={M}",False); continue
        emb=all(leq(x,y)==leq(img[x],img[y]) for x in BM for y in BM)
        check(f"order-embedding both directions M={M}",emb)
print(f"scanned {len(seen)} width-tuples; inversion-count failures={invfail}")
print("ALL PASS (EXIT 0)" if fails==0 and invfail==0 else f"{fails} fails, {invfail} invfails")
import sys; sys.exit(0 if fails==0 and invfail==0 else 1)
