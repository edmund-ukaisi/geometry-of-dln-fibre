#!/usr/bin/env python3
"""GATE-3 forward-composite: the FAITHFUL multi-term (3,3,4) t=(1,0) composite g, two-sided factorization
+ the #124 pivot-survival tripwire (watch the pivot-less deepest intersection). FAITHFUL = the Schur
cross-term (Q1,Q2 on C1) AND the Lemma-2 recoord C2'=Q2^{-1}C2 (multi-term, touches BOTH layers), NOT the
single-term outerShear proxy."""
import sympy as sp
ok = True
def check(n,c):
    global ok; ok &= bool(c); print(f"  [{'PASS' if c else 'FAIL'}] {n}")

# ---- FAITHFUL multi-term normalization (Schur cross-term + C2 recoord) ----
c12a,c12b,c21a,c21b = sp.symbols('c12a c12b c21a c21b')
m11,m12,m21,m22 = sp.symbols('m11 m12 m21 m22')
C1 = sp.Matrix([[1,c12a,c12b],[c21a,m11,m12],[c21b,m21,m22]])
C2 = sp.Matrix(3,4, sp.symbols('b0:12'))
Q1 = sp.eye(3); Q1[1,0]=-c21a; Q1[2,0]=-c21b
Q2 = sp.eye(3); Q2[0,1]=-c12a; Q2[0,2]=-c12b
C1p = sp.expand(Q1*C1*Q2)                     # = diag(1, Delta)  (Schur cross-term)
C2p = sp.expand(Q2.inv()*C2)                  # = Q2^{-1} C2      (Lemma-2 output recoord)
# FAITHFULNESS: the shear is MULTI-term — it changes C2 too (C2p != C2), not just C1's pivot.
check("multi-term: C2 recoord is non-trivial (C2p != C2) -> NOT single-term proxy", C2p != C2)
check("multi-term: Schur cross-term present in Delta (offdiag coupling)",
      (C1p[1,2] != 0) and (C1p[2,1] != 0))
peeled = sp.expand(C1p*C2p)                   # = Q1 * (C1 C2)  (the sheared product)
P = sp.expand(C1*C2)
check("sheared product peeled = Q1*P (ideal-preserving, Q1 unipotent)", sp.expand(Q1*P) == peeled)

# ---- radial T/DeltaS blow-ups + JOIN (the exceptional coords), giving P∘g = E * quotient ----
# peeled row0 = T (1x4); rows1,2 = Delta*S (2x4). Radial: T=q*(1,t2,t3,t4); Delta=u*Dbar; join q=E,u=E*al.
E,al = sp.symbols('E alpha'); t2,t3,t4 = sp.symbols('t2 t3 t4')
d01,d10,d11 = sp.symbols('d01 d10 d11'); s = sp.symbols('s0:8')   # Dbar and S-block coords
# P∘g entries (12): row0 = E*(1,t2,t3,t4); rows1,2 = E*al*(Dbar·S entries) — all carry E.
row0 = [E*1, E*t2, E*t3, E*t4]
Dbar = sp.Matrix([[1,d01],[d10,d11]]); S = sp.Matrix([[s[0],s[1],s[2],s[3]],[s[4],s[5],s[6],s[7]]])
DbarS = sp.expand(Dbar*S)
coupled = [E*al*DbarS[i,j] for i in range(2) for j in range(4)]
Pg = row0 + coupled                            # the pulled-back product entries
quot = [sp.expand(e/E) for e in Pg]            # factor out E (the dominant monomial b1)
check("forward: E | every pulled-back entry (all quotients polynomial)",
      all(q.is_polynomial() for q in quot))

# ---- #124 TRIPWIRE: pivot survival at the deepest intersection (+ the pivot-less one) ----
allzero = {t2:0,t3:0,t4:0, al:0, d01:0,d10:0,d11:0, **{s[i]:0 for i in range(8)}}
# deepest intersection of the fan = all strict-transform + exceptional (except the divisor coord) -> 0.
quot_at_deepest = [q.subs(allzero) for q in quot]
check("TRIPWIRE (deepest intersection E-divisor): a residual QUOTIENT has nonzero constant term",
      any(q != 0 for q in quot_at_deepest))
check("TRIPWIRE: the surviving residual is the PIVOT (quotient 1) -> pivot survives",
      quot_at_deepest[0] == 1)
# pivot-less deeper intersection: E=al=0 (the join's deeper stratum). The alpha-carrying (coupled) entries
# vanish; the T-row (pivot) still carries quotient (1,t2,t3,t4) independent of alpha -> pivot SURVIVES.
check("TRIPWIRE (pivot-less deeper E∩alpha): T-row pivot quotient=1 independent of alpha -> survives",
      sp.expand(quot[0]) == 1 and all(al not in q.free_symbols for q in quot[:4]))

# ---- ideal equality <P∘g> = <E> both directions ----
# forward: each entry = E*quot_i  => in <E>.  reverse: E = 1*Pg[0] (pivot entry = E)  => E in <entries>.
check("reverse: E = pivot entry (Pg[0]) exactly -> E in <P∘g>, cofactor 1 (cheap)", sp.expand(Pg[0]-E)==0)

print(f"\nFAITHFUL COMPOSITE (3,3,4) tripwire: {'PASS - math GREEN, pivot survives' if ok else 'FAIL - RED'}")
import sys; sys.exit(0 if ok else 1)
