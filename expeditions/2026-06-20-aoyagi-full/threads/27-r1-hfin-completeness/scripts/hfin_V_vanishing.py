#!/usr/bin/env python3
"""
hfin_V_vanishing.py — does the #135 phi_M chart's unit V vanish within the chart (breaking hfin)?

hdiv (lower bound): needs F o phi = u^2 * V, V >= c0 on a SLICE (one diverging axis). DONE in #135.
hfin (upper bound): needs the charts to COVER routeMBaseNbhd up to null, AND per-chart
   F o phi >= c0 * u^2  (V bounded BELOW on the WHOLE chart neighborhood) so |F|^{-c'} <= C u^{-2c'}.
If V VANISHES on a positive-codim sublocus WITHIN the chart, then F o phi = u^2*V vanishes faster there,
|F|^{-c'} is LARGER, and the single-divisor u^2 model FAILS to upper-bound -- that sublocus is a DEEPER
stratum the chart does NOT resolve (it needs its own sub-chart). THIS is the completeness gap.

Test (3,3,4): V = Uval334 = a^2*||(1,tau)||^2 + ||c*(1,tau)+Delta*S||^2 (the u-free unit). Does V
vanish for (a,c,tau,Delta,S) in the chart box? V=0 requires a=0 AND c(1,tau)+Delta S=0. With a=0 the
first term is 0; the second is a (2,4) determinantal condition -> V vanishes on a POSITIVE-DIMENSIONAL
sublocus {a=0, Delta S = -c(1,tau)} INSIDE the chart. There F o phi vanishes faster than u^2 -> the
u^2 model under-bounds -> hfin per-chart bound FAILS on {a=0}. The {a=0} locus is the DEEPER corank
stratum (rank(Delta) drops further), exactly the determinantal nesting.
"""
import sympy as sp

# Uval334 from the Lean def (RouteMLayerCoverGEL2)
a,c0,c1,t1,t2,t3 = sp.symbols('a c0 c1 t1 t2 t3', real=True)
D00,D01,D10,D11 = sp.symbols('D00 D01 D10 D11', real=True)
S = sp.symbols('S00 S01 S02 S03 S10 S11 S12 S13', real=True)
S00,S01,S02,S03,S10,S11,S12,S13 = S
U = (a**2*(1+t1**2+t2**2+t3**2)
     + ((c0*1+(D00*S00+D01*S10))**2 + (c0*t1+(D00*S01+D01*S11))**2
        + (c0*t2+(D00*S02+D01*S12))**2 + (c0*t3+(D00*S03+D01*S13))**2)
     + ((c1*1+(D10*S00+D11*S10))**2 + (c1*t1+(D10*S01+D11*S11))**2
        + (c1*t2+(D10*S02+D11*S12))**2 + (c1*t3+(D10*S03+D11*S13))**2))
# Does U vanish for a nonzero point in the box? Set a=0, c0=c1=0, Delta=0 -> U=0. That's a positive-
# dim sublocus {a=0,c=0,Delta=0} (S,tau free) INSIDE the chart where U=0.
sub={a:0,c0:0,c1:0,D00:0,D01:0,D10:0,D11:0}  # S,tau free
print("U at {a=0, c=0, Delta=0} (S,tau free) =", U.subs(sub), " => U VANISHES on a positive-dim sublocus.")
# dimension of {U=0} inside the 18-dim chart-unit space (a,c0,c1,t1,t2,t3,D*,S*):
# U is a sum of squares; {U=0} = {a=0, c0(1,tau)+Delta row0 . S=0, c1(1,tau)+Delta row1 . S=0}.
# = {a=0} (1 eqn) AND 8 bilinear eqns. Generically codim 1+? -> positive-dim. So {U=0} is NONEMPTY
# and positive-dimensional within the chart.
print()
print("CONSEQUENCE for hfin: on {U=0} INSIDE the (3,3,4) phi_M chart, F o phi = u^2 * U vanishes to")
print("order > 2 in the (u, transverse) sense -> the single-divisor u^2 model does NOT upper-bound")
print("|F|^{-c'} there. {U=0} is the DEEPER corank stratum (rank Delta drops). The phi_M chart")
print("resolves the GENERIC (top) stratum but NOT this sub-stratum -> the chart family is INCOMPLETE")
print("for the UPPER bound. hdiv didn't care (it used U>=c0 on a slice AVOIDING {U=0}); hfin must")
print("cover {U=0} too, recursively -> the full coupled/iterated resolution (sub-charts on {U=0}).")
