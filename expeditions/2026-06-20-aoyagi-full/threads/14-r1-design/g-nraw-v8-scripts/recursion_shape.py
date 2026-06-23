"""What recursion does minAdm ACTUALLY satisfy?  Two candidate per-node telescopes:

(R1-percluster, cert-104b) blow up ONLY layer 0, n_raw=M_last, child=schurStateRed=(M0-1,M1-1,tail):
       cand = min( M0*M1 ,  M_last + minAdm(M0-1,M1-1,tail) )            [L=2 only, per geom]

(alt-A) the increment is NOT M_last but the TRUE per-node increment d = minAdm(M)-minAdm(child).
        Is there a clean geometric n_raw' with  min(M0*M1, n_raw' + minAdm(child)) = minAdm  for ALL L?
        If so n_raw' = minAdm(M) - minAdm(child)  WHENEVER minAdm < M0*M1 (the binding branch).

We test: does there EXIST any n_raw (>=0) making  min(mk, n_raw + minAdm(child)) = minAdm ?
   - need minAdm <= mk  (else min picks mk and any n_raw>= minAdm-... ; if minAdm>mk it's impossible since
     min(mk, .) <= mk < minAdm).  Check whether minAdm <= mk always.
   - on the binding branch need n_raw = minAdm - minAdm(child) >= 0, i.e. minAdm >= minAdm(child).
"""
from itertools import product
from minadm import min_adm

def child(M):
    M=list(M); M[0]-=1; M[1]-=1; return tuple(M)

print("Q: is minAdm(M) <= M0*M1 always? (needed for min(mk,.) to ever reach minAdm)")
bad=[]
for L in range(1,5):
    for w in product(range(1,6),repeat=L+1):
        M=tuple(w)
        if M[0]<1 or M[1]<1: continue
        if min_adm(M) > M[0]*M[1]:
            bad.append((M,min_adm(M),M[0]*M[1]))
print("  violations minAdm>mk:", bad[:10], "count", len(bad))

print("\nQ: is minAdm(M) >= minAdm(child)? (needed for n_raw = minAdm-minAdm(child) >= 0)")
bad2=[]; eqcap=[]
for L in range(2,5):
    for w in product(range(1,6),repeat=L+1):
        M=tuple(w)
        if M[0]<1 or M[1]<1: continue
        ch=child(M)
        if min_adm(M) < min_adm(ch):
            bad2.append((M, min_adm(M), ch, min_adm(ch)))
print("  violations minAdm(M)<minAdm(child):", bad2[:10], "count", len(bad2))

print("\nThe TRUE increment d = minAdm(M)-minAdm(child) on the binding branch (minAdm<mk):")
print("  is d = M_last only for L=2?  Tabulate d vs M_last by L on binding nodes:")
for L in range(2,5):
    tot=dml=0; ex=[]
    for w in product(range(1,5),repeat=L+1):
        M=tuple(w)
        if M[0]<1 or M[1]<1: continue
        ma=min_adm(M); mk=M[0]*M[1]
        if ma>=mk: continue  # not binding branch (mk caps)
        tot+=1
        d=ma-min_adm(child(M))
        if d==M[-1]: dml+=1
        elif len(ex)<5: ex.append((M, d, M[-1], "d", ma, "ch", min_adm(child(M))))
    print(f"  L={L}: binding nodes {tot}, d==M_last on {dml}; mismatches ex {ex}")
