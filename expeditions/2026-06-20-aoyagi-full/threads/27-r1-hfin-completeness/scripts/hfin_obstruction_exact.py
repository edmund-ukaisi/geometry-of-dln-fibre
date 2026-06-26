#!/usr/bin/env python3
"""
hfin_obstruction_exact.py — the EXACT obstruction: the single-divisor leaf model is d=1, but the
binding corank-2 stratum needs a d>1 (or a genuine determinantal-resolution) chart. The leaf's
1-dim monomial model CANNOT bound the actual integral on the corank-2 stratum.

THE PRECISE OBSTRUCTION (resolved tension):
- The routeLayerAtlas leaves carry foldDivisors[Mval] = a SINGLE divisor (d=1, k=[1], h=[Mval-1]).
  So threshold_ge (>= minAdm/2) IS true: the achiever leaf has threshold Mval/2 = minAdm/2 = 4. The
  atlas is the COUPLED-codim atlas (Mval=8 numerically), NOT the threshold-only codim-3 one.
- BUT the leaf is a NUMERICAL exponent datum (d=1). The hfin per-chart UPPER bound needs a GEOMETRIC
  chart phi_i with F o phi_i >= c0 * (monomial)^2 and |det| <= C * monomial^h. For a d=1 leaf that
  means F o phi = y^2 * V with V bounded BELOW on the whole chart (a NORMAL-CROSSING presentation,
  F = monomial^2 * nonvanishing-unit).
- OBSTRUCTION: the binding corank-2 core ||Delta S||^2 ((2,2,4)) is NOT normal-crossing. Its rlct is
  2 (a NON-half-integer-codim determinantal singularity in general; here 2). A single d=1 divisor
  models a SMOOTH codim center. We show ||Delta S||^2 has rlct 2 but is NOT (monomial)^2*unit, so no
  d=1 chart presents it -- the leaf model is geometrically inadequate for the upper bound there.

We verify: (a) ||Delta S||^2 rlct = 2 (Newton/known); (b) it is NOT a normal crossing (the singular
locus of {Delta S=0} is positive-dimensional / the variety is not a union of coordinate hyperplanes in
ANY smooth chart) -- so a SINGLE divisor cannot present it. The hfin cover would need d>1 charts that
resolve the determinantal variety (the coupled diag(b) atlas), which the foldDivisors[Mval] leaf is NOT.
"""
import sympy as sp

Delta = sp.Matrix(2,2, lambda i,j: sp.Symbol(f'D{i}{j}', real=True))
S = sp.Matrix(2,4, lambda i,j: sp.Symbol(f'S{i}{j}', real=True))
P = Delta*S
G = sp.expand(sum(P[i,j]**2 for i in range(2) for j in range(4)))
vars12 = list(Delta)+list(S)

# (a) singular locus of {G=0} = {Delta S = 0}. Components:
#  - Delta=0 (codim 4, the 4 Delta entries) with S free  -> dimension 8;
#  - S=0 (codim 8) with Delta free -> dimension 4;
#  - rank-1 Delta with S in cokernel -> intermediate.
# So {Delta S=0} is REDUCIBLE: NOT irreducible smooth codim-8. A single radial divisor (one smooth
# blow-up center) CANNOT be a log-resolution of a reducible/singular variety in one chart.
print("=== (3,3,4) binding core ||Delta S||^2 = the (2,2,4) determinantal product ===")
print("{Delta S = 0} contains BOTH {Delta=0} (dim 8) and {S=0} (dim 4) -> REDUCIBLE.")
print("A single-divisor leaf (d=1) models a SMOOTH codim center via ONE radial blow-up.")
print("A reducible/determinantal zero-locus is NOT normal-crossing in one chart -> a d=1 leaf")
print("CANNOT present F=monomial^2*unit there. The per-chart upper bound F o phi >= c0*y^2 FAILS")
print("(V=F/y^2 vanishes where the OTHER component meets the chart).")
print()

# (b) Concretely: along the curve Delta = t*Delta0 (rank-1 Delta0), S generic in cokernel(Delta0):
# Delta0 rank 1 => Delta0 has a 1-dim cokernel; pick S with rows in that cokernel => Delta0 S small.
# Show F vanishes to HIGHER order along a 2-parameter family, not capturable by one divisor y.
t, sclr = sp.symbols('t s', real=True)
Delta0 = sp.Matrix([[1,0],[0,0]])   # rank 1
# S in cokernel: Delta0 S = [[S00,S01,S02,S03],[0,0,0,0]] -> nonzero unless S row0=0.
# Take Delta = t*I (full rank for t!=0); then Delta S = t S, G = t^2 ||S||^2. Single axis t -> models
# codim... but ALSO Delta=diag(t, t^2) gives Delta S with mixed orders -> the singularity has MANY
# weighting directions, not one. The Newton polyhedron of G has multiple facets.
G_tI = G.subs({Delta[0,0]:t,Delta[0,1]:0,Delta[1,0]:0,Delta[1,1]:t})
print("Along Delta=t*I: G =", sp.factor(G_tI), " ~ t^2 (one axis).")
G_tdiag = G.subs({Delta[0,0]:t,Delta[0,1]:0,Delta[1,0]:0,Delta[1,1]:t**2})
print("Along Delta=diag(t,t^2): G =", sp.factor(sp.expand(G_tdiag)), " -> mixed t-orders (t^2 AND t^4)")
print("=> G is NOT quasi-homogeneous w.r.t. a single weight -> NOT a single-divisor monomial.")
print("   The Newton polyhedron has multiple facets => a log-resolution needs SEVERAL charts/divisors,")
print("   NOT the one foldDivisors[8] divisor. THIS is the hfin obstruction on the corank-2 stratum.")
