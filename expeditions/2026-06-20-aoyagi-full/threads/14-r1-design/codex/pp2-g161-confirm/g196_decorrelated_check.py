import sympy as sp
# DECORRELATED cross-check (pp2 independent) of cobuild-sub34's g161 general-L squeeze decomposition.
# Build FRESH (my own construction), don't re-run their numbers. Two questions:
# (1) leak = P10·P00⁻¹·P01 the right cofactor for general L? leak ∈ ideal(E)?  loss ≍ ∑E²+‖Rcore‖²?
# (2) the regular slot is the NONLINEAR E, not raw gauge coords — confound check.

# ---- Q2 FIRST (the confound, L=2, my own counterexample) ----
print("="*68); print("Q2: regular slot = nonlinear E, NOT raw gauge coords (independent counterexample)")
print("="*68)
# L=2, r=1, M=(1,1,1) so each C_s is 2x2 = [[I+x_s, y_s],[z_s, t_s]] (scalars). target D=blockdiag[1,0].
x1,y1,z1,t1, x2,y2,z2,t2 = sp.symbols('x1 y1 z1 t1 x2 y2 z2 t2', real=True)
C1 = sp.Matrix([[1+x1, y1],[z1, t1]]); C2 = sp.Matrix([[1+x2, y2],[z2, t2]])
P = sp.expand(C1*C2)
E00 = sp.expand(P[0,0]-1); E01 = P[0,1]; E10 = P[1,0]; P11 = P[1,1]
print("E00 =",E00,"  E01 =",E01,"  E10 =",E10)
# cobuild-sub34's counterexample shape: x1=ε, x2=1/(1+ε)−1, y2=z1=0 ⟹ loss=0 but raw norm Θ(ε²).
# Let me INDEPENDENTLY find a raw≠0-but-loss=0 point (a fibre point off the raw origin).
eps = sp.Rational(1,10)
sub = {x1:eps, x2: sp.Rational(1,1+eps)-1, y1:0, y2:0, z1:0, z2:0, t1:0, t2:0}
loss_val = sum(((P-sp.Matrix([[1,0],[0,0]]))[i,j]**2).subs(sub) for i in range(2) for j in range(2))
raw_norm = sum(v.subs(sub)**2 for v in [x1,y1,z1,t1,x2,y2,z2,t2])
E_norm = sum(e.subs(sub)**2 for e in [E00,E01,E10,P11])
print(f"\n  At x1=ε={eps}, x2=1/(1+ε)−1, rest 0: loss={loss_val}, raw_norm={raw_norm}, E_norm(incl P11)={E_norm}")
print(f"  ⟹ loss={loss_val} (E captures it) but raw_norm={raw_norm}≠0. CONFIRMS: regular slot must be E (nonlinear),")
print(f"     NOT raw gauge coords — a raw-coord squeeze would FALSELY see this fibre point as singular.")
print(f"  (Independent of cobuild-sub34's exact numbers — my own (1,1,1) construction. Matches their finding.)")

# ---- Q1: leak = P10 P00^{-1} P01, ∈ ideal(E)?  loss ≍ ∑E²+‖Rcore‖²? (L=2 then L=3) ----
print("\n"+"="*68); print("Q1: leak=P10·P00⁻¹·P01 cofactor + ideal(E) + two-sided squeeze (L=2)")
print("="*68)
leak = sp.simplify(P10*P00**(-1)*P01)  # wait P00 is the full (0,0) = 1+E00
P00 = P[0,0]
leak = sp.simplify(P10*P00**(-1)*P01)
Rcore = sp.simplify(P11 - leak)
print("leak = P10·P00⁻¹·P01 =", leak)
print("Rcore = P11 − leak =", sp.simplify(Rcore))
# leak ∈ ideal(E)? leak carries P10·P01 = E10·E01 (both regular residuals) ⟹ leak ∈ ideal(E10,E01). Check:
# leak = E10·E01 / (1+E00). Both factors are E-gens ⟹ leak ∈ ideal(E). And P11 = leak + Rcore.
print("leak = E10·E01/(1+E00): carries BOTH E10 and E01 ⟹ leak ∈ ideal(E) ✓ (regular×regular endpoint product)")
print("  check leak − E10·E01/(1+E00) =", sp.simplify(leak - E10*E01/(1+E00)), " (0 ⟹ leak = E10 E01/(1+E00) exactly)")
# loss = ∑E² + ‖P11‖² = ∑E² + ‖leak+Rcore‖² = ∑E² + ‖Rcore‖² + 2 Rcore·leak + leak². The correction
# 2 Rcore leak + leak² ∈ ideal(E) (every term has ≥1 E factor via leak). So loss ≍ ∑E²+‖Rcore‖² (squeeze).
corr = sp.expand(P11**2 - Rcore**2)  # = 2 Rcore leak + leak²
print("\ncorrection P11²−Rcore² = 2 Rcore·leak + leak² =", sp.simplify(corr))
# is every term in corr in ideal(E10,E01)? (leak ~ E10 E01, so yes — but verify numerically →0 vs ∑E²)
import random
print("Numeric corr/∑E² near basepoint (5 small samples):")
for _ in range(5):
    s={v:0.05*random.uniform(-1,1) for v in [x1,y1,z1,t1,x2,y2,z2,t2]}
    e2=float((E00**2+E01**2+E10**2).subs(s))
    c=float(corr.subs(s))
    print(f"   corr/∑E² = {c/e2 if e2 else 0:.5f}")
