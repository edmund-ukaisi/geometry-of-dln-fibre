"""Structural facts about minAdm to ground the geometry.

1. L=1:  M=(m,k).  Adm has only T=() (L=0 exponents... actually L=1 means one exponent t0 with t0=0 forced
   since L-1=0).  Mval = (M0 - 0)(M1 - 0) = m*k.  So minAdm = m*k.  Full-rank-drop codim.
2. The 'sort bridge' / weakly-increasing reduction: minAdm is permutation-invariant in M (paper Cor 5.10).
3. Compare minAdm(M) vs minAdm(child) to see the TRUE per-node increment.
"""
from minadm import min_adm, argmin_adm, adm_list, mval
from itertools import product

def child(M):
    M=list(M); M[0]-=1; M[1]-=1; return tuple(M)

# L=1 closed form check
print("L=1:  minAdm(m,k) vs m*k")
for m,k in product(range(1,5),repeat=2):
    print(f"  ({m},{k}) minAdm={min_adm((m,k))}  m*k={m*k}", "OK" if min_adm((m,k))==m*k else "X")

print("\nTRUE per-node increment  minAdm(M) - minAdm(child)  for L>=2 (child=(M0-1,M1-1,tail)):")
for L in range(2,4):
    print(f" L={L}:")
    for widths in product(range(1,5),repeat=L+1):
        M=tuple(widths)
        if M[0]<1 or M[1]<1: continue
        ch=child(M)
        if ch[0]<0 or ch[1]<0: continue
        ma=min_adm(M); mc=min_adm(ch)
        inc = ma - mc
        # report a few
    # just print a representative table for L=2
for M in [(2,2,2),(3,3,3),(2,2,4),(3,3,2),(2,2,1),(4,4,4),(2,3,4),(3,2,5)]:
    ch=child(M)
    print(f"  M={M} minAdm={min_adm(M)} child={ch} minAdm(child)={min_adm(ch)} increment={min_adm(M)-min_adm(ch)} M_last={M[-1]} M0*M1={M[0]*M[1]}")
