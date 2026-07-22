#!/usr/bin/env python3
# guards: enc-swap, enc-transport, enc-ceilingM-bridge, enc-sorted-box, bindingSet_orderIso_boxPart
# config: Codex's adjacent-swap encoding realises {T in Adm : Mval=minAdm} =~o BoxPart(l,a) over
#         positive-width M, L<=4 (land + involution + bijection + both-direction monotone).
# provenance: threads/41-order-count/codex/enc-map-answer.md (Codex xhigh, route (a)); the kill-record
#         for OrderRealize.lean's four frontier obligations (swapBinding_orderIso / transport_sorted /
#         residueA_le_ell / sorted_orderIso_boxPart).  Codex's map, NOT the cert's Lemma-4 recipe;
#         both were verified — the equivalence is NOT needed (any valid iso discharges the Nonempty).
"""Kill-condition battery for the OrderRealize (3a) construction (route (a), Codex's map).

Implements Codex part-1/2: bubble-sort the widths transporting the profile by the value-preserving
adjacent-swap R, then on sorted widths take active steps x_i in {C-1,C}, a-subset A={i:x_i=C}, box
via reversed gaps. Asserts, over all positive-width M with L<=4: enc lands in BoxPart(l,a); enc is a
bijection onto BoxPart; dec is its two-sided inverse; and enc is an order-embedding BOTH directions
(the reverse is the load-bearing one — coord-sum rank fails it, cert part iii). Exit 0 iff all pass."""
from itertools import product as iproduct, combinations

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
    m=min(mval(M,T) for T in A); return [T for T in A if mval(M,T)==m], m

# --- ell / a (def3 selector, = qipM on sorted widths) ---
def qipA(d,l):
    N=len(d)-1; return sum(d[min(i,N)] for i in range(l+1))-l*d[min(l,N)]
def qipM(d):
    b=0
    for l in range(len(d)):
        if qipA(d,l)>=0: b=l
    return b
def ell_a(M):
    D=tuple(sorted(M)); l=qipM(D); S=sum(D[:l+1]); C=-(-S//l); return l, S-(C-1)*l

# --- Codex R (atomic value-preserving adjacent-swap on the middle coord) ---
def swapR(P,X,Q,A,B):
    if A<=B and B-A<=P-X: return X+(B-A)
    if B<A and A-B<=X-Q: return X-(A-B)
    return P+Q-X

# --- bubble-sort transport: sort widths ascending, transport T via R at each adjacent swap ---
def transport(M,T):
    M=list(M); T=list(T); L=len(T)
    swapped=True
    while swapped:
        swapped=False
        for k in range(L):                    # width positions k,k+1  (k=0..L-1)
            if M[k]>M[k+1]:
                if k>=1:
                    P = M[0] if k==1 else T[k-2]
                    X, Q, A, B = T[k-1], T[k], M[k], M[k+1]
                    T[k-1]=swapR(P,X,Q,A,B)
                M[k],M[k+1]=M[k+1],M[k]
                swapped=True
    return tuple(M), tuple(T)                  # (sorted D, transported U)

# --- sorted-widths enc: U -> box (active steps -> a-subset -> reversed gaps) ---
def enc_sorted(D,U,l,a):
    e=[D[0]-U[0]]+[U[i-1]-U[i] for i in range(1,len(U))]
    C=-(-sum(D[:l+1])//l)
    A=[i for i in range(l) if e[i]+D[i+1]==C]
    assert len(A)==a, (D,U,A,a)
    p=sorted(A)
    return tuple(p[a-1-i]-(a-1-i) for i in range(a))   # reversed gaps, antitone
def enc(M,T):
    l,a=ell_a(M); D,U=transport(M,T); return enc_sorted(D,U,l,a)

# --- BoxPart(l,a) ---
def boxpart(l,a):
    K=l-a
    if a==0: return [()]
    return [f for f in iproduct(range(K+1),repeat=a) if all(f[i]>=f[i+1] for i in range(a-1))]
def leq(u,v): return len(u)==len(v) and all(u[i]<=v[i] for i in range(len(u)))

# --- worked-example pin (hand-verified against Codex) ---
def pin():
    # M=[1,1,2,1]: (0,0,0)->box(0), (1,1,0)->box(1)   (BoxPart(2,1)={(0,),(1,)})
    assert enc((1,1,2,1),(0,0,0))==(0,), enc((1,1,2,1),(0,0,0))
    assert enc((1,1,2,1),(1,1,0))==(1,), enc((1,1,2,1),(1,1,0))

fails=0
def check(name,c):
    global fails
    if not c: fails+=1; print(f"  [FAIL] {name}")
    else: print(f"  [pass] {name}")

pin(); print("worked-example pins: OK")
seen=set()
for L in range(1,5):
    hi=4 if L<=3 else 3
    for M in iproduct(range(1,hi+1),repeat=L+1):
        if M in seen: continue
        seen.add(M)
        l,a=ell_a(M)
        if l==0 or not(0<=a<=l): continue
        P,_=binding(M); B=set(boxpart(l,a))
        imgs=[enc(M,T) for T in P]
        # (i) land + (ii) bijection onto BoxPart
        if set(imgs)!=B or len(imgs)!=len(set(imgs)):
            check(f"bijection M={M}", False); continue
        # (iii) order-embedding both directions
        emb=all(leq(x,y)==leq(enc(M,x),enc(M,y)) for x in P for y in P)
        check(f"order-embedding both directions M={M}", emb)
print(f"\nscanned {len([m for m in seen])} width-tuples")
print("ALL PASS (EXIT 0)" if fails==0 else f"{fails} FAILURES")
import sys; sys.exit(0 if fails==0 else 1)
