"""Verify a closed form for minAdm and derive d = minAdm(M)-minAdm(child) analytically.

The paper's explicit (C,theta): for the zero-product / deepest locus the minimal codim is given by a
QIP whose optimum has a closed form in the SORTED widths.  But the all-zero deepest point is the FULL
zero-product (rank 0 everywhere), codim = the codim of the deepest orbit.

Let me just establish d's dependence: does d depend ONLY on (M0,M1,M_last), or on the whole tail?
Compare M=(3,3,3) [L2] d=3 vs M=(3,3,3,3) [L3] d=2 vs M=(3,3,3,3,3)[L4]:
"""
from itertools import product
from minadm import min_adm

def child(M):
    M=list(M); M[0]-=1; M[1]-=1; return tuple(M)

print("d = minAdm(M) - minAdm(child)  as depth grows, fixed widths:")
for base in [(3,3),(2,2),(4,4),(3,2)]:
    for L in range(2,6):
        M = base + (base[1],)*(L-1)   # (a,b,b,...,b) chain of length L+1? just repeat last
        # build a uniform-ish chain
        M = tuple([base[0]] + [base[1]]*L)
        ma=min_adm(M); ch=child(M); mc=min_adm(ch); d=ma-mc
        print(f"  M={M} (L={L}) minAdm={ma} child={ch} mc={mc} d={d} M_last={M[-1]}")
    print()

print("So d DEPENDS ON DEPTH L, not just (M0,M1,M_last) -> n_raw is NOT a function of the local node alone.")
print("\nKey: is d ALWAYS <= M_last (overshoot direction only)?  And d>=? ")
viol=[]
for L in range(2,5):
    for w in product(range(1,6),repeat=L+1):
        M=tuple(w)
        if M[0]<1 or M[1]<1: continue
        d=min_adm(M)-min_adm(child(M))
        if d>M[-1]: viol.append((M,d,M[-1]))
print("  cases with d > M_last:", viol[:10], "count", len(viol))
