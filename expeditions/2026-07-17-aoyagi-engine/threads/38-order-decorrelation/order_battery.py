#!/usr/bin/env python3
"""
Thread-38 (order-decorrelation) sufficiency battery.  EXACT symbolic algebra (sympy over Q / symbols).

Adjudicates: under the per-step atom composition order DERIVED from Aoyagi pp.16-20
   atom = B ∘ S   (blow-up B OUTERMOST, shear S innermost)
does the structural δ=1 division hold, and does it FAIL under the OTHER order
   atom = S ∘ B   (shear outermost)?

Maps (resolution direction: child coords -> parent coords, parent = atom(child)):
  B = blockBlowupMap center pivot :  x -> y,   y[pivot]=x[pivot];  y[j]=x[pivot]*x[j] (j in center\{pivot});  y[j]=x[j] (spectator)
      (exactly Core.Aoyagi.BlockDivision.blockBlowupMap; see case1_core_exactdiv_killset.py)
  S = shear phi (pivot-keeping: phi[pivot]=0):  x -> x + phi(x)

Checks (from the brief):
  (a) PIVOT-KEEPING shear, B∘S: every parent-frame CENTER coord pulled through the atom is
      divisible by the child pivot coord (delta=1 division structural) -- for ANY pivot-keeping phi.
  (b) phi_bad = Pi.single c (w_s^2) (pivot-keeping, jacDet 1): does NOT break division under B∘S;
      DOES break it under S∘B (reproduce the L4-case1-core witness).
  (c) the real Schur displacement (thread-34 P/Q̂ forms) IS pivot-keeping, and B∘S divides.
  (d) Jacobian bookkeeping: |det D(atom)| = |pivot|^(|center|-1) for a jacDet-1 pivot-keeping shear
      under B∘S.
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    c = bool(cond)
    ok &= c
    print(f"  [{'PASS' if c else 'FAIL'}] {name}")

# ---------------- atom pieces ----------------
def blowup(center, pivot):
    def B(x):
        return [x[pivot] if j == pivot else (x[pivot]*x[j] if j in center else x[j])
                for j in range(len(x))]
    return B

def shear(disp_fn):
    # disp_fn(x) -> list of displacements; pivot-keeping is asserted separately
    def S(x):
        d = disp_fn(x)
        return [sp.expand(x[j] + d[j]) for j in range(len(x))]
    return S

def compose(f, g):          # (f ∘ g)(x) = f(g(x))
    return lambda x: f(g(x))

def divisible_by(expr, piv, gens):
    """EXACT polynomial divisibility of expr by piv (piv a single symbol)."""
    q = sp.cancel(sp.expand(expr) / piv)
    return q.is_polynomial(*gens), q

def jac_det(mapfn, w):
    img = mapfn(list(w))
    Jm = sp.Matrix([[sp.diff(img[i], w[j]) for j in range(len(w))] for i in range(len(w))])
    return sp.factor(sp.expand(Jm.det()))

# =====================================================================
# CONFIG 1 (toy):  D=3, center={0,1}, pivot=0, spectator=2
# =====================================================================
print("=== CONFIG 1 (toy): D=3, center={0,1}, pivot=0, spectator=2 ===")
D, center, pivot, spec = 3, {0, 1}, 0, 2
w = sp.symbols('w0:3')
gens = list(w)
B = blowup(center, pivot)

# --- (a) generic pivot-keeping shear: arbitrary displacement symbols on non-pivot coords ---
#     phi[1], phi[2] arbitrary (independent symbols standing for ANY polynomial), phi[pivot]=0.
phi1, phi2 = sp.symbols('phi1 phi2')
disp_generic = lambda x: [sp.Integer(0), phi1, phi2]   # pivot(0) kept
Sg = shear(disp_generic)
gens_a = gens + [phi1, phi2]
atom_BS_g = compose(B, Sg)(list(w))
a_ok = True
for j in center:
    d, q = divisible_by(atom_BS_g[j], w[pivot], gens_a)
    a_ok &= d
check("(a) B∘S: every center coord divisible by pivot for a GENERIC pivot-keeping shear", a_ok)
# and pivot-keeping is real: atom pivot component carries pivot factor trivially
check("(a') pivot-keeping check phi[pivot]=0", disp_generic(list(w))[pivot] == 0)

# --- (b) phi_bad = Pi.single c (w_s^2), c=1 (center, non-pivot), w_s = spectator w2 ---
c_bad = 1
disp_bad = lambda x: [x[spec]**2 if j == c_bad else sp.Integer(0) for j in range(len(x))]
Sb = shear(disp_bad)
check("(b0) phi_bad is pivot-keeping (phi[pivot]=0)", disp_bad(list(w))[pivot] == 0)
# jacDet of the shear alone = 1
check("(b0') jacDet(shear phi_bad) = 1", jac_det(Sb, w) == 1)

atom_BS_bad = compose(B, Sb)(list(w))      # DERIVED order
atom_SB_bad = compose(Sb, B)(list(w))      # OTHER order
dBS, qBS = divisible_by(atom_BS_bad[c_bad], w[pivot], gens)
dSB, qSB = divisible_by(atom_SB_bad[c_bad], w[pivot], gens)
print(f"       B∘S atom[c]={sp.expand(atom_BS_bad[c_bad])}   /pivot -> {'poly '+str(sp.expand(qBS)) if dBS else 'NON-POLY'}")
print(f"       S∘B atom[c]={sp.expand(atom_SB_bad[c_bad])}   /pivot -> {'poly' if dSB else 'NON-POLY '+str(sp.cancel(atom_SB_bad[c_bad]/w[pivot]))}")
check("(b) phi_bad does NOT break division under DERIVED order B∘S (center coord divisible)", dBS)
check("(b) phi_bad DOES break division under OTHER order S∘B (center coord NOT divisible)", not dSB)

# --- (d) Jacobian: |det D(atom)| = |pivot|^(|center|-1) under B∘S, jacDet-1 shear ---
jd_toy = jac_det(compose(B, Sb), w)
expect_toy = w[pivot]**(len(center)-1)
check(f"(d) toy: |det D(B∘S)| = pivot^(|center|-1) = w0^{len(center)-1}   [got {jd_toy}]",
      sp.simplify(sp.Abs(jd_toy) - sp.Abs(expect_toy)) == 0 or jd_toy == expect_toy)

# =====================================================================
# CONFIG 2 (real Schur displacement, thread-34 P/Q̂ forms):
#   residual block D''=[[1,beta],[gamma,delta]] reduced by P (col op, into g) / Q̂ (cofactor).
#   The shear that enters the atom clears beta/gamma on the d-coords; the PIVOT coord is untouched.
# =====================================================================
print("\n=== CONFIG 2: the real Schur displacement is pivot-keeping (thread-34) ===")
# coords: [u_p(pivot,0), beta(1), gamma(2), delta(3)] -- all four are center (blown-up) d/pivot coords.
# thread-34: child block D_{J+1} = delta - gamma*beta (Schur complement); in the resolution direction
# (child->parent) the col-op P inversion is the shear  delta -> delta + gamma*beta,  pivot/beta/gamma kept.
up, beta, gamma, delta = sp.symbols('u_p beta gamma delta')
wS = [up, beta, gamma, delta]
gensS = list(wS)
centerS, pivotS = {0, 1, 2, 3}, 0
BS_ = blowup(centerS, pivotS)
disp_schur = lambda x: [sp.Integer(0), sp.Integer(0), sp.Integer(0), x[2]*x[1]]   # delta += gamma*beta; pivot kept
S_schur = shear(disp_schur)
check("(c) real Schur displacement is pivot-keeping (phi[pivot]=0)", disp_schur(list(wS))[pivotS] == 0)
check("(c') jacDet(Schur shear) = 1 (unipotent)", jac_det(S_schur, wS) == 1)
atom_schur = compose(BS_, S_schur)(list(wS))
c_ok = all(divisible_by(atom_schur[j], wS[pivotS], gensS)[0] for j in centerS)
check("(c) B∘S with the real Schur displacement: every center coord divisible by pivot", c_ok)

# =====================================================================
# CONFIG 3 ((3,3,4)-shaped Case-1 step, killset modeling): D=4, center={0,1,2}, pivot=0, spectator=3
#   the S=2,J=0 Case-1(1) s-chart: center = the row-1 residual d-entries getting the s-factor.
# =====================================================================
print("\n=== CONFIG 3: (3,3,4) S=2 J=0 Case-1 step; D=4, center={0,1,2}, pivot=0, spectator=3 ===")
D3, center3, pivot3, spec3 = 4, {0, 1, 2}, 0, 3
w3 = sp.symbols('v0:4')
gens3 = list(w3)
B3 = blowup(center3, pivot3)
# phi_bad on this step: c=1 (center non-pivot), spectator = index 3
disp_bad3 = lambda x: [x[spec3]**2 if j == 1 else sp.Integer(0) for j in range(len(x))]
Sb3 = shear(disp_bad3)
atom_BS3 = compose(B3, Sb3)(list(w3))
atom_SB3 = compose(Sb3, B3)(list(w3))
dBS3 = all(divisible_by(atom_BS3[j], w3[pivot3], gens3)[0] for j in center3)
dSB3 = divisible_by(atom_SB3[1], w3[pivot3], gens3)[0]
check("(b/334) B∘S divides all center coords; phi_bad harmless", dBS3)
check("(b/334) S∘B breaks division (center coord 1 not divisible)", not dSB3)
jd3 = jac_det(compose(B3, Sb3), w3)
check(f"(d/334) |det D(B∘S)| = pivot^(|center|-1) = v0^{len(center3)-1}   [got {jd3}]",
      jd3 == w3[pivot3]**(len(center3)-1))

print(f"\nTHREAD-38 SUFFICIENCY BATTERY: {'PASS (EXIT 0)' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
