from itertools import product
from math import comb

# ---- Mval / Adm (unsorted, as Lambda.lean uses M directly) ----
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def admissible(M,T):
    L=len(T)
    if any(T[j]>admBound(M,j) for j in range(L)): return False
    for i in range(L):
        for j in range(i,L):
            if T[j]>T[i]: return False
    if L>=1 and T[L-1]!=0: return False
    return True
def Mval(M,T):
    L=len(T); s=0
    for j in range(L):
        tprev=M[0] if j==0 else T[j-1]; s+=(tprev-T[j])*(M[j+1]-T[j])
    return s
def adm_set(M):
    L=len(M)-1
    out=[]
    rng=range(max(M)+1)
    for T in product(rng,repeat=L):
        if admissible(M,T): out.append(T)
    return out
def minAdm(M):
    A=adm_set(M); return min(Mval(M,T) for T in A)
def minimisers(M):
    A=adm_set(M); m=min(Mval(M,T) for T in A)
    return [T for T in A if Mval(M,T)==m]

# ---- ell / residueA (sorted reconstruction) ----
def qipA(d,l):
    N=len(d)-1
    return sum(d[min(i,N)] for i in range(l+1)) - l*d[min(l,N)]
def qipM(d):
    N=len(d)-1
    best=0
    for l in range(N+1):
        if qipA(d,l)>=0: best=l
    return best
def qipS(d):
    N=len(d)-1; m=qipM(d)
    return sum(d[min(i,N)] for i in range(m+1))
def ell_a(M):
    d=tuple(sorted(M))  # shiftedSorted r=0 ascending
    l=qipM(d); S=qipS(d)
    cM=(S+l-1)//l
    a=S-(cM-1)*l
    return l,a

# ---- poset structure of minimiser set under pointwise <= ----
def chain_height(pts):
    # longest chain in the poset (pts under pointwise <=); return #nodes
    def le(x,y): return all(a<=b for a,b in zip(x,y))
    # DAG longest path
    import functools
    order=sorted(pts,key=lambda p:sum(p))
    idx={p:i for i,p in enumerate(order)}
    best={p:1 for p in order}
    for p in order:
        for q in order:
            if p!=q and le(p,q) and sum(p)<sum(q):
                if best[p]+1>best[q]: best[q]=best[p]+1
    return max(best.values())

traps={'M1=[1,1,2,1]':(1,1,2,1),'M2=[2,2,4,3]':(2,2,4,3),'M3=[2,2,2,2,2]':(2,2,2,2,2)}
for name,M in traps.items():
    l,a=ell_a(M)
    mins=minimisers(M)
    ch=chain_height(mins) if mins else 0
    theta=a*(l-a)+1
    print(f"{name}: minAdm={minAdm(M)}  ell={l} a={a}  aoyagiTheta=a(l-a)+1={theta}  C(l,a)={comb(l,a)}")
    print(f"    #minimisers over Adm = {len(mins)}   chainHeight(minimiser poset) = {ch}")
    print(f"    minimisers: {sorted(mins)}")

print("\n=== BROAD SWEEP: does |minimisers over Adm| = C(l,a) and chainHeight = a(l-a)+1 ? ===")
def sweep(maxL, maxW):
    card_fail=0; ch_fail=0; total=0; ex=[]
    for L in range(1,maxL+1):
        for M in product(range(1,maxW+1),repeat=L+1):  # positive widths (Aoyagi setting)
            total+=1
            l,a=ell_a(M)
            if l==0: continue
            mins=minimisers(M)
            theta=a*(l-a)+1
            cval=comb(l,a) if 0<=a<=l else -1
            cardok=(len(mins)==cval)
            chok=(chain_height(mins)==theta)
            if not cardok: card_fail+=1
            if not chok: ch_fail+=1
            if (not cardok or not chok) and len(ex)<12:
                ex.append((M,l,a,len(mins),cval,chain_height(mins),theta))
    return total,card_fail,ch_fail,ex

tot,cf,chf,ex=sweep(4,4)
print(f"positive-width M, L<=4, W<=4: total={tot}")
print(f"  cardinality |minimisers| == C(l,a):  {tot-cf}/{tot}  ({cf} fails)")
print(f"  chainHeight == a(l-a)+1:             {tot-chf}/{tot}  ({chf} fails)")
for e in ex: print("   MISMATCH (M,l,a,|min|,C,chH,theta):",e)
