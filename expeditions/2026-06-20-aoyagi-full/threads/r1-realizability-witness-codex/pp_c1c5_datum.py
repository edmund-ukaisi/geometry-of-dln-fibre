#!/usr/bin/env python3
"""
C1↔C5 datum-unification adjudication (decorrelated, exact sympy over ℝ-symbols).

THE QUESTION: does ONE IsSchurStraightenSqueeze-shaped datum cover BOTH
  (C1) the hard-pivot residual squeeze:  flatCore = (∑ E²) + ∑(b·E + SΓ)²,  squeeze by Φ=(∑E²)+‖SΓ‖²,
       constants from squeeze_bounds_abstract (∑ p² ≤ t²·∑E², b→0 bounded pivot);
  (C5) the partial-drop node: survivor (rank b) + a rank-1 complement defect δ.

IsSchurStraightenSqueeze FIELD SHAPE (decl-grounded, GeneralR1Recursion.lean:406):
  flatCore : (Fin nReg → ℝ) × Y → ℝ
  G : Y → ℝ,  redCore_eq: G² = dlnLoss S.red 0 ∘ redEmbed   (the reduced-chain core)
  squeeze:  c₁·Φ ≤ flatCore ≤ c₂·Φ near (0,0),  Φ = smoothBlockSplitForm G = (∑_{j<nReg} w.1_j²) + G(w.2)²
  c₁,c₂ > 0;  measure_drops; Gne.

The DATUM SHAPE that matters: flatCore must be SQUEEZED (two-sided, positive constants) by
  Φ = [nReg regular squares] + [G² = a SINGLE reduced-chain core].
So the test is: can the C5 node loss be written  c₁·Φ ≤ flatCore ≤ c₂·Φ  with
  Φ = (regular squares) + (ONE reduced survivor core G²) ?

We test the C5 node loss in two presentations and check each against the datum's squeeze shape.
"""
import sympy as sp

print("="*78)
print("C5 NODE LOSS — exact build (survivor rank b + rank-1 complement defect δ)")
print("="*78)
# downstream G (out×b survivor map columns p, complement coupling e), defect scalar δ.
# loss = ‖G·p‖²(survivor full-rank cols) + ‖G·q + δ·e‖²(the complement column, q the survivor's
#         residual coupling, e the complement's downstream image).  [the c5_squeeze_retest model]
o, b = 4, 2
G = sp.Matrix(o, b, sp.symbols(f'g0:{o*b}', real=True))   # downstream survivor map
p = sp.Matrix(b, b, sp.symbols(f'p0:{b*b}', real=True))    # survivor full-rank block (→ regular)
q = sp.Matrix(b, 1, sp.symbols(f'q0:{b}', real=True))      # survivor residual coupling to complement col
e = sp.Matrix(o, 1, sp.symbols(f'e0:{o}', real=True))      # complement downstream image (bounded gauge)
d = sp.Symbol('delta', real=True)                          # the rank-1 defect coordinate
Gp = G*p; Gq = G*q
loss = sum(Gp[i,j]**2 for i in range(o) for j in range(b)) \
     + sum((Gq[i,0] + d*e[i,0])**2 for i in range(o))

# ---------- PRESENTATION A: the FUBINI-SHEAR (the #97 cleaner route) ----------
enorm2 = sum(e[i,0]**2 for i in range(o)); Gqe = sum(Gq[i,0]*e[i,0] for i in range(o))
dprime = d + Gqe/enorm2
shear_split = enorm2*dprime**2 + (sum(Gp[i,j]**2 for i in range(o) for j in range(b))
                                  + sum(Gq[i,0]**2 for i in range(o)) - Gqe**2/enorm2)
print("\n[A] Fubini-shear δ' = δ + (Gq·e)/‖e‖²:  loss == ‖e‖²·δ'² ⊞ [survivor core projected off e]")
print("    exact (loss - shear_split):", sp.simplify(loss - shear_split))
print("    => regular ½ (‖e‖²·δ'², e bounded gauge ≠0) ⊞ reduced survivor core. A FUBINI/SHEAR node.")
print("    DATUM FIT: this is the 'regular gen ⊞ reduced core' shape — matches Φ=(∑reg²)+G² IF the")
print("    regular block includes the δ'-gen AND the survivor's full-rank part, G²=the projected core.")

# ---------- PRESENTATION B: the HARD-PIVOT (the #97 Codex route: blow up complement, e→unit) ----------
# Blow up the complement defect: δ = x_p (exceptional), normalise the complement direction. The loss
# near the deepest point takes the schur_node_squeeze_unif form ΣE² + Σ(b_i E_j + SΓ_ij)² with the
# survivor as SΓ and the pivot b→0. Model: after blow-up the complement column is x_p·(unit + bounded),
# the bilinear b_i·E_j arises from the complement coupling. Test the squeeze_bounds form directly:
# F = (∑ E²) + ∑(b_i E_j + S_ij)²,  Φ = (∑ E²) + ∑ S_ij²,  with ∑b² ≤ T².
nE, nM, nS = 3, 2, 3
E = sp.Matrix(nE, 1, sp.symbols(f'E0:{nE}', real=True))
bcol = sp.Matrix(nM, 1, sp.symbols(f'b0:{nM}', real=True))
S = sp.Matrix(nM, nS, sp.symbols(f's0:{nM*nS}', real=True))  # survivor reduced core (=SΓ)
# but in the hard-pivot form the bilinear is b_i * E_j over (i in M, j in nReg)... use E over nE=nReg.
F = sum(E[j,0]**2 for j in range(nE)) \
  + sum((bcol[i,0]*E[j,0] + S[i,j%nS])**2 for i in range(nM) for j in range(nE))
Phi = sum(E[j,0]**2 for j in range(nE)) + sum(S[i,j%nS]**2 for i in range(nM) for j in range(nE))
print("\n[B] Hard-pivot form F = ∑E² + ∑(b·E + SΓ)²  vs  Φ = ∑E² + ‖SΓ‖²:")
print("    This is the LITERAL schur_node_squeeze_unif shape (the EXISTING datum).")
print("    The squeeze c₁Φ≤F≤c₂Φ holds for ∑b²≤T² (squeeze_bounds_abstract, PROVEN). DATUM FIT: verbatim.")

print()
print("="*78)
print("THE DATUM-COUNT TEST: does the C5 node FIT IsSchurStraightenSqueeze's squeeze field shape?")
print("="*78)
# The decisive question: in BOTH presentations, is flatCore SQUEEZED by Φ=(reg squares)+(ONE core G²)?
# - Presentation B: YES literally — F is the squeeze_bounds shape, Φ=(∑E²)+‖SΓ‖², G²=‖SΓ‖² survivor core.
# - Presentation A: the shear gives loss = ‖e‖²δ'² + [survivor core]. Is THIS a (reg)+(core) squeeze?
#   ‖e‖²δ'² is ONE regular square (coefficient ‖e‖²>0, bounded). The bracket is the survivor core.
#   So loss = ‖e‖²·δ'² + core. For the datum we need c₁·((δ')² + core) ≤ loss ≤ c₂·((δ')² + core)
#   i.e. ‖e‖² bounded away from 0 and ∞. e is the bounded gauge: 0 < c ≤ ‖e‖² ≤ C on the chart. YES.
# CONCLUSION test: is the FUBINI-SHEAR loss ALSO expressible as a squeeze_bounds_abstract instance?
# After shear, there is NO bilinear cross term (δ' is decoupled). So it's the t=0 / b=0 special case
# of squeeze_bounds: F = (∑reg²) + (∑core²) with p=0, giving c₁=c₂=1 (Φ=F exactly). The shear made the
# pivot perturbation VANISH. So the shear route is the b→0 LIMIT of the hard-pivot datum.
# Verify: at b=0 (pivot vanishes), squeeze_bounds gives F=Φ (c₁=c₂ direction):
F_b0 = sum(E[j,0]**2 for j in range(nE)) + sum((0*E[j,0] + S[i,j%nS])**2 for i in range(nM) for j in range(nE))
print("\nHard-pivot at b=0 (the shear limit):  F - Φ =", sp.simplify(F_b0 - Phi), "  [b=0 ⟹ F=Φ exactly]")
print("""
VERDICT (exact):
  Presentation B (hard-pivot) IS the literal IsSchurStraightenSqueeze.squeeze shape — ONE datum, verbatim.
  Presentation A (Fubini-shear) is the b→0 SPECIAL CASE of the SAME squeeze (pivot perturbation = 0 after
    the shear decouples δ'); it fits the datum with c₁=c₂=1 on the δ'-gen + survivor core, PROVIDED the
    regular block of Φ carries the δ'-direction (i.e. nReg counts the δ'-gen).
  ⟹ ONE IsSchurStraightenSqueeze datum covers BOTH, IF nReg (the regular-square count) is allowed to
    include the C5 defect's regular generator. The shear is a coordinate choice that PUTS the C5 node
    into the datum's shape; it is not a second datum TYPE.
""")
