#!/usr/bin/env python3
"""
Off-diagonal contagion in the LOSS (elder charge-2; pairs with pnp-fold cert-fold-regroup §4).

pnp-fold's kill-condition (Jacobian side): a fan-out copy that births a divisor at an
OFF-diagonal pivot cell `z_pivot` accumulates against the state-level divBirthCoord
DIAGONAL cell `z_diag` that descendants reference — discrepancy J_Φ = L·(z_diag/z_pivot)^b.

Question (loss side): does the ∏ z_{divCoord}² loss monomial suffer the SAME contagion?

MECHANISM (chart model, §0 of the fold cert): a max-modulus blow-up with pivot P scales
EVERY other center cell by z_P: z_c → z_P·z_c. So the residual block = z_P·D', and the
product carries z_P once ⟹ frobSq = z_P²·(unit): the loss vanishes order-2 along the
ACTUAL pivot cell z_P. But the ledger's divCoord (state-level) names the DIAGONAL z_D.

(A) CURRENT charts (birth=pivot P, reference=diagonal D, P≠D):
      residualCore = frobSq / z_D²  =  (z_P / z_D)² · unit
    -> vanishes at z_P=0 (z_D≠0): 0<lo FAILS;  unbounded at z_D=0 (z_P≠0): hi FAILS.
    The loss contagion is REAL and breaks BOTH squeeze bounds.

(B) DIAGONAL-NORMALIZED charts (fork-15: source swap pivot<->diagonal, so birth=ref=D):
      frobSq = z_D²·unit,  divCoord = z_D  ->  residualCore = unit.  No contagion.
"""
import sympy as sp

# center block of a case-2 (or case-1 d-block) node: 2x2 residual, cells d00 d01 d10 d11.
# diagonal birth corner D = d00 ; an off-diagonal fan-out pivot P = d01.
d00,d01,d10,d11 = sp.symbols('d00 d01 d10 d11', real=True)
# the rest of the product downstream (a bounded-unit residual matrix U, entries generic)
u1,u2,u3,u4 = sp.symbols('u1 u2 u3 u4', real=True)

# --- max-modulus blow-up with pivot P = d01 (OFF-diagonal): every other center cell ×= z_P ---
zP = d01
D_blown = sp.Matrix([[zP*d00, zP],[zP*d10, zP*d11]])   # pivot d01 free (=zP), others scaled by zP
# the product's frobSq through this block times a downstream bounded unit U (represent as ‖D_blown·Umat‖²)
Umat = sp.Matrix([[1+u1**2, u2],[u3, 1+u4**2]])        # a bounded-invertible unit (spd-ish)
Pmat = D_blown*Umat
frob = sp.expand(sum(Pmat[i,j]**2 for i in range(2) for j in range(2)))
print("=== loss through an OFF-diagonal-pivot blow-up ===")
# factor z_P² (the actual exceptional divisor)
core_P = sp.factor(frob/zP**2)
print("frobSq / z_P²  leaked z_P (=d01)?", core_P.has(d01),
      "  (False => loss vanishes order-2 EXACTLY along the pivot z_P)")

# (A) CURRENT: divCoord names the DIAGONAL D = d00, not the pivot.  residualCore = frob/z_D²
zD = d00
residual_current = sp.simplify(frob/zD**2)
print("\n--- (A) CURRENT charts: monomial = z_D² (diagonal), actual loss ~ z_P² ---")
print("residualCore = frobSq/z_D² = (z_P/z_D)²·unit  =")
print("   ", sp.factor(residual_current))
# leak check: vanishes at z_P=0 (d01=0), d00≠0 ?
val_zP0 = residual_current.subs({d01:0, d00:sp.Rational(1,2), d10:0,d11:0,u1:0,u2:0,u3:0,u4:0})
print("residualCore at z_P=0, z_D=½ :", val_zP0, " (=0 => 0<lo FAILS: divisor trapped, kill-b/c)")
# unbounded at z_D=0 (d00=0), d01≠0 ?
val_zD0 = residual_current.subs({d00:0, d01:sp.Rational(1,2), d10:0,d11:0,u1:0,u2:0,u3:0,u4:0})
print("residualCore at z_D=0, z_P=½ :", val_zD0, " (nonzero over 0 => hi FAILS / undefined: unbounded)")
print("VERDICT (A): the loss suffers the SAME contagion as the Jacobian — residualCore")
print("             carries (z_P/z_D)², breaking BOTH the lower (0<lo) and upper (hi) squeeze.")

# (B) DIAGONAL-NORMALIZED (fork-15): swap so the blow-up pivot IS the diagonal cell D.
zP2 = d00   # now the pivot IS the diagonal
D_blown2 = sp.Matrix([[zP2, zP2*d01],[zP2*d10, zP2*d11]])   # pivot d00 free, others scaled
Pmat2 = D_blown2*Umat
frob2 = sp.expand(sum(Pmat2[i,j]**2 for i in range(2) for j in range(2)))
residual_diag = sp.factor(frob2/zP2**2)          # divCoord = z_D = d00 = pivot: MATCHES
print("\n--- (B) DIAGONAL-NORMALIZED charts (fork-15: pivot = diagonal D) ---")
print("residualCore = frobSq/z_D²  leaked z_D (=d00)?", residual_diag.has(d00),
      "  (False => monomial matches the actual divisor; NO contagion)")
val_B = residual_diag.subs({d01:0,d10:0,d11:0,u1:0,u2:0,u3:0,u4:0})
print("residualCore at the deepest residual point:", val_B, " (a positive unit => squeeze intact)")
print("VERDICT (B): under diagonal-normalization the loss contagion is GONE — birth=reference,")
print("             the monomial z_D² matches the actual exceptional divisor.")

print("\n" + "="*72)
print("KEY: fork-15 (a coordinate SWAP pivot<->diagonal) fixes the CONTAGION, but the")
print("determinantal-residual leak (l3_leak_and_rb §1) is a SEPARATE cross-layer issue")
print("needing the incidence/Q,P SHEAR. The Jacobian is det-1-BLIND to that shear")
print("(ShearReconcile: det Dψ=1), so the Jacobian needs ONLY fork-15; the LOSS needs")
print("BOTH fork-15 AND the Schur/incidence normalization.  'One fix serves both' = NO.")
