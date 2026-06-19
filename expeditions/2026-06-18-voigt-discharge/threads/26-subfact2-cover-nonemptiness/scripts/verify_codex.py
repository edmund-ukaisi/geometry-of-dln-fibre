"""
Rigorously verify Codex's KEY LEMMA and its consequence.

KEY LEMMA (Codex): For ANY nonnegative triangular array g (g_{ij}>=0 for i<=j, treat out-of-range as 0),
and ANY cell (I,J) with I<J and g_{IJ}>0, define
   A = { [a,e] : a<=I, e>=J, g_{ij}>0 for all a<=i<=I, J<=j<=e }   (rectangle-in-supp intervals)
and  h_{a,e} := g_{a,e} - g_{a,e+1} - g_{a-1,e} + g_{a-1,e+1}  (second diff; out-of-range g = 0).
Then  sum_{[a,e] in A} h_{a,e}  >=  g_{IJ}  >  0.

NOTE: this lemma does NOT reference s, r, m(s), m(r), or extremality. It is purely about g>=0.
But the APPLICATION needs h_{a,e} = m(r)_{[a,e]} - m(s)_{[a,e]} (true by inversion+linearity), and
m(s)>=0, to conclude some m(r)_{[a,e]}>=1.

We test:
 (T1) the KEY LEMMA on RANDOM nonneg triangular arrays g (not just differences of cumulants).
      If it holds for ALL nonneg g, it's stronger than needed (and elementary). Stress hard.
 (T2) the conclusion (some [a,e] in A has m(r)_{[a,e]}>=1) on all our achievable pairs (already known true),
      but now CHECK that A here uses cell (i0,j0) AND that A's defn matches our rectangle defn.
 (T3) does the lemma hold at NON-extremal cells too? (Codex claims yes.)
"""
import random
from itertools import product

def second_diff(g, a, e, N):
    G = lambda i,j: g.get((i,j),0) if (0<=i<=j<=N) else 0
    return G(a,e) - G(a,e+1) - G(a-1,e) + G(a-1,e+1)

def A_set(g, I, J, N):
    """intervals [a,e], a<=I, e>=J, with rectangle [a,I]x[J,e] subset supp(g) (g>0 everywhere)."""
    out=[]
    for a in range(0, I+1):
        for e in range(J, N+1):
            if all(g.get((i,j),0)>0 for i in range(a,I+1) for j in range(J,e+1)):
                out.append((a,e))
    return out

def lemma_lhs(g, I, J, N):
    return sum(second_diff(g,a,e,N) for (a,e) in A_set(g,I,J,N))

def random_nonneg_tri(N, hi=3):
    g={}
    for i in range(N+1):
        for j in range(i,N+1):
            g[(i,j)] = random.randint(0,hi)
    return g

if __name__=="__main__":
    random.seed(1)
    # T1: KEY LEMMA on random nonneg triangular arrays, ALL cells (I,J) with I<J and g>0.
    fails=0; checked=0
    for N in range(1,7):
        for _ in range(20000):
            g=random_nonneg_tri(N, hi=random.choice([1,1,2,3]))
            for I in range(N+1):
                for J in range(I+1,N+1):
                    if g.get((I,J),0)>0:
                        lhs=lemma_lhs(g,I,J,N); checked+=1
                        if not (lhs >= g[(I,J)]):
                            fails+=1
                            if fails<=5:
                                print("LEMMA FAIL N",N,"IJ",(I,J),"lhs",lhs,"gIJ",g[(I,J)])
                                for i in range(N+1): print("   ",[g.get((i,j),0) for j in range(N+1)])
    print(f"T1 KEY LEMMA on random nonneg g: checked={checked} fails={fails}")
