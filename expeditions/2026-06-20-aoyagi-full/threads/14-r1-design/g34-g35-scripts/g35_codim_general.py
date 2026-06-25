import sympy as sp
from itertools import product
# Verify codim S(t) = Mval(t) for NON-square cases (4,3,2),(3,2,3),(2,3,2), via the dim formula.
# General L=2, M=(M1,M2,M3). Stratum S(t1,0): rank(A1)=t1 (A1 is M1xM2), A2 (M2xM3) with cols in
# ker(A1) (dim M2 - t1) so that A1 A2=0. (Need t1 <= min(M1,M2).)
#   dim{rank A1=t1, M1xM2} = t1(M1+M2-t1).
#   dim{A2 M2xM3, cols in (M2-t1)-dim ker} = M3*(M2-t1).
#   dim S = t1(M1+M2-t1) + M3(M2-t1).  N = M1*M2 + M2*M3.  codim = N - dim S.
def Mval(M,t):
    tt=[M[0]]+list(t); L=len(M)-1
    return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))
def codimS(M,t1):
    M1,M2,M3=M
    N=M1*M2+M2*M3
    dimS = t1*(M1+M2-t1) + M3*(M2-t1)
    return N-dimS
print("=== codim S(t1,0) [dim formula] vs Mval(t1,0), non-square cases ===")
for M in [(4,3,2),(3,2,3),(2,3,2),(3,3,3),(2,2,2)]:
    M1,M2,M3=M
    print(f"  M={M}:")
    for t1 in range(min(M1,M2)+1):
        c=codimS(M,t1); mv=Mval(M,(t1,0))
        match = "OK" if c==mv else "*** MISMATCH ***"
        print(f"    S({t1},0): codim={c}, Mval={mv}  {match}")
    print()
print("If codim S(t) = Mval(t) for ALL t (all cases), then:")
print(" - G3.4: strata partition {A1A2=0}, indexed by t1; complete (every fibre pt has a rank).")
print(" - G3.5: binding ratio = ½·min codim = ½·min_Adm Mval = lambdaCore. Generic stratum = achiever.")
print(" - The resolution blows up exactly these strata; every divisor ratio = Mval(t)/2 >= min/2.")
