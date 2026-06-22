"""
Attack (ii) sharpened: when a single exceptional coord u scales SEVERAL factors, ord_u(F)=2k with k>=2.
Does the divisor ratio (h+1)/(2k) UNDERSHOOT lambdaCore?  h = Jacobian exponent of the chart.

The danger divisor: a blow-up of a center cut out by simultaneously scaling several factors. Consider the
DIAGONAL blow-up: blow up the origin of the FULL parameter space (all entries) at once. The chart
  every entry  = u * (new var)
has Jacobian u^{N-1} (N = total #entries) and F -> u^{2L} * unit (scaling all L factors by u scales prod
by u^L, F by u^{2L}). So ord_u F = 2L, k_E = L, h = N-1, ratio = N/(2L).
This is the NAIVE 'blow up everything' divisor. Its ratio N/(2L) vs lambdaCore.

But the FAITHFUL resolution does NOT do this -- it blows up rank strata of ONE partial product at a time.
Still, I must check: is there ANY admissible blow-up the resolution performs that scales >1 factor?

Test the naive full-origin divisor ratio N/(2L) vs lambdaCore for each chain, to SEE the undershoot
magnitude (this divisor is NOT in the faithful atlas, but quantifies the trap).
"""
import sys; sys.path.insert(0,'/tmp/pp3')
from mval import lambdaCore
from fractions import Fraction

def N_entries(M):
    L=len(M)-1
    return sum(M[s]*M[s+1] for s in range(L))   # layer s: M[s-1]xM[s] -> wait indexing

def N_entries_correct(M):
    # layer s (1-indexed s=1..L) has size M[s-1] x M[s]; total entries
    L=len(M)-1
    return sum(M[s-1]*M[s] for s in range(1,L+1))

print(f"{'M':<16}{'N':<5}{'L':<3}{'naiveDivRatio N/(2L)':<22}{'lambdaCore':<12}{'undershoot?'}")
for M in [(2,2,2),(2,1,2),(1,2,1),(3,1,3),(2,3,2),(3,2,1),(1,2,3),
          (3,3,3,3),(2,2,2,2),(4,2,4),(2,4,2),(2,2,2,2,2),(3,2,2,3)]:
    M=list(M); L=len(M)-1
    N=N_entries_correct(M)
    naive=Fraction(N,2*L)
    lc=lambdaCore(M)
    flag = "UNDERSHOOTS" if naive < lc else ("equal" if naive==lc else "above (safe)")
    print(f"{str(tuple(M)):<16}{N:<5}{L:<3}{str(naive):<22}{str(lc):<12}{flag}")
