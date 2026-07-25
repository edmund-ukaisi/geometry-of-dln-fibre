#!/usr/bin/env python3
"""SUM vs PRODUCT -- the exact crux of Codex's k=2 challenge.
Aoyagi's block-elim gives ||T||^2 + ||Delta S||^2 (a SUM, survivor + residual), NOT a product.
Show: the SUM's join is k=1 (survivor's constant term), and rlct = 1/2*Mval; a PRODUCT would be k=2.
Then a 2-LEVEL-DEEP join to confirm k=1 telescopes."""
import sympy as sp
from fractions import Fraction

# ---- (i) the join of a SUM q^2*U + u^2*G with U(0)=1 is E^2*unit (k=1) ----
q,u,E,al = sp.symbols('q u E alpha'); t2,g1,g2 = sp.symbols('t2 g1 g2')
U = 1 + t2**2                       # survivor: constant term 1
G = g1**2 + g2**2                   # residual core (vanishes at 0)
S_sum = q**2*U + u**2*G             # the SUM (real Aoyagi structure)
S_prod = q**2 * u**2 * (U*G+1)      # a hypothetical PRODUCT (Codex's misreading)
for nm,expr in [("SUM q^2 U + u^2 G", S_sum), ("PRODUCT q^2 u^2 (..)", S_prod)]:
    j = sp.expand(expr.subs({q:E, u:E*al}))           # join q=E,u=E*alpha
    # factor highest power of E dividing j:
    kpow = sp.Poly(j, E).as_dict()
    minE = min(k[0] for k in kpow)                    # lowest E-power = 2k
    unit = sp.simplify(j / E**minE)
    unit0 = unit.subs({al:0,t2:0,g1:0,g2:0})
    print(f"  {nm:24s}: join = E^{minE} * ({sp.factor(unit)}) ;  E-order={minE} => k={Fraction(minE,2)} ; "
          f"unit(0)={unit0} (k=1 iff order=2 & unit(0)!=0)")

# ---- (ii) exact rlct: SUM (survivor present) vs PRODUCT (no survivor), disjoint vars ----
# rlct(f+g)=rlct(f)+rlct(g) [SUM] ; rlct(f*g)=min(rlct f,rlct g) [PRODUCT], disjoint vars.
# survivor ||T||^2 ~ m clean squares (rlct m/2) ; residual sub-core rlct = 1/2*minAdm(sub).
# SUM total = 1/2*(m + minAdm(sub)) = 1/2*Mval(minimizer)  vs  PRODUCT = min(m/2, 1/2*minAdm(sub)).
def demo(m, minadm_sub):
    s = Fraction(m,2)+Fraction(minadm_sub,2)
    p = min(Fraction(m,2), Fraction(minadm_sub,2))
    print(f"  survivor sq={m}, minAdm(sub)={minadm_sub}:  SUM rlct={s} (=1/2*Mval)  |  PRODUCT rlct={p}")
print("(ii) direct-sum(=Aoyagi SUM) keeps 1/2*Mval; a product would collapse to the min:")
demo(4,4)   # (3,3,4)-like: peel 4, sub 4 -> SUM 4 = 1/2*8 ; product would give 2 (Codex's wrong value)
demo(1,3)   # (2,2,2,2)-like: peel 1, sub minAdm 2 ... (illustrative)
demo(3,1)

# ---- (iii) 2-LEVEL deep join: survivor at level1 (const 1) + [survivor level2 (const1) + residual] ----
E2,be = sp.symbols('E2 beta'); r1,r2 = sp.symbols('r1 r2')
# level-2 core G itself = q2^2*U2 + u2^2*G2 with U2(0)=1 ; already joined to E2^2*(U2+beta^2 G2)=E2^2*unit2
# feed that as the residual of level 1:  S = q^2*U + u^2 * (E2**2 * unit2), unit2(0)=1
unit2 = 1 + r1**2 + be**2*(r2**2)          # level-2 joined unit, const 1
S2 = q**2*U + u**2*(E2**2*unit2)
j2 = sp.expand(S2.subs({q:E,u:E*al}))
minE = min(k[0] for k in sp.Poly(j2,E).as_dict()); unit=sp.simplify(j2/E**minE)
print(f"(iii) 2-level: outer join E-order={minE} (k={Fraction(minE,2)}), unit(0)="
      f"{unit.subs({al:0,t2:0,E2:0,r1:0,r2:0,be:0})}  -> k=1 telescopes (survivor const 1 at each level)")
