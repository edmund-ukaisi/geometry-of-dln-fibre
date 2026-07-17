#!/usr/bin/env python3
# =============================================================================
# WITNESS W1 — JOINT-CENTER SURVIVAL  (executable kill-condition, exact/Groebner)
# =============================================================================
# DISCRIMINATOR (prodcorank-cert.md §1, §4; princ-answer.md Q1):
#   Resolving the FIRST/individual factor-rank strata alone does NOT principalize
#   the product ideal I(P*Z). At the minimal failure n=2, k=2, a SMOOTH codim-3
#   (= C_2) JOINT center survives, carrying a genuinely-new ALIGNMENT coordinate b
#   that no single-factor rank divisor captures.
#
# ENGINE KILL-CONDITION GUARDED:
#   The native resolution engine MUST NOT claim to close the min-corank >= 2
#   product-corank atom by any finite sequence of SINGLE-FACTOR (per-matrix
#   rank-drop) blow-ups. If a peel ships single-factor radial / pivot-Gram
#   blow-ups asserting min-corank >= 2 is principalized, this witness fires:
#   the joint center (x,y,b) is still there.
#
# EXACT INSTRUMENT: sympy Groebner bases over QQ (exact rational coefficients).
#
# EXHIBITS (all exact, no floats):
#   E1. I(P*Z) = (x, y, b)   [both containments via reduced Groebner bases].
#   E2. The two single-factor rank divisors are det(P) = x and det(Z) = y.
#   E3. THE KILL: the alignment coordinate b is NOT in (det P, det Z) = (x, y).
#       => (x,y,b) strictly contains the ideal cut out by the single-factor
#          divisors; b is new data no product of factor-rank divisors reaches.
#   E4. (x,y,b) is a smooth codim-3 complete intersection (Jacobian rank 3 = C_2).
#
# EXPECTED RESULT (checked-in output reproduced verbatim at bottom of file):
#   E1: each entry of P*Z reduces to 0 mod (x,y,b) AND each of x,y,b reduces to
#       0 mod the entries  => I(P*Z) = (x,y,b).
#   E2: det P = x, det Z = y.
#   E3: b reduced mod (x,y) = b  (NONZERO) => b NOT in (det P, det Z). KILL fires.
#   E4: Jacobian of (x,y,b) has rank 3 => smooth codim-3 = C_2.
# =============================================================================

import sympy as sp

def hdr(s): print("\n" + "="*70 + "\n" + s + "\n" + "="*70)

x, y, b, c = sp.symbols('x y b c')
GENS = [x, y, b, c]

# Minimal balanced chart of the n=2,k=2 product-corank locus (princ-answer.md Q1).
# W is invertible so I(P*Z*W) = I(P*Z); we work with P*Z directly.
P = sp.Matrix([[1, 0], [0, x]])
Z = sp.Matrix([[y + b*c, b], [c, 1]])
PZ = P * Z
entries = list(PZ)

hdr("SETUP: n=2, k=2 balanced chart")
print("P  =", P.tolist())
print("Z  =", Z.tolist())
print("P*Z=", PZ.tolist())
print("entries (generators of I(P*Z)) =", entries)

# ---- E1: I(P*Z) = (x, y, b) -------------------------------------------------
hdr("E1: I(P*Z) = (x, y, b)   (Groebner, both containments)")
G_xyb = sp.groebner([x, y, b], *GENS, order='lex')
red_entries = [G_xyb.reduce(e)[1] for e in entries]
fwd = all(r == 0 for r in red_entries)
print("each P*Z entry reduced mod (x,y,b):", red_entries, "=> all zero:", fwd)

G_ent = sp.groebner(entries, *GENS, order='lex')
red_xyb = [G_ent.reduce(g)[1] for g in (x, y, b)]
bwd = all(r == 0 for r in red_xyb)
print("each of x,y,b reduced mod (entries):", red_xyb, "=> all zero:", bwd)
E1 = fwd and bwd
print("E1 VERDICT  I(P*Z) = (x,y,b):", E1)

# ---- E2: single-factor rank divisors are det P = x, det Z = y ---------------
hdr("E2: single-factor rank divisors")
detP = sp.expand(P.det())
detZ = sp.expand(Z.det())
print("det(P) =", detP, "  (P's rank-drop divisor)")
print("det(Z) =", detZ, "  (Z's rank-drop divisor)")
E2 = (detP == x) and (detZ == y)
print("E2 VERDICT  det P = x and det Z = y:", E2)

# ---- E3: THE KILL — b is NOT in (det P, det Z) = (x, y) ---------------------
hdr("E3: KILL — alignment coordinate b NOT in (det P, det Z) = (x, y)")
G_factors = sp.groebner([detP, detZ], *GENS, order='lex')
b_red = G_factors.reduce(b)[1]
print("Groebner basis of (det P, det Z):", list(G_factors.exprs))
print("b reduced mod (det P, det Z) =", b_red, " (nonzero => b NOT in the ideal)")
b_escapes = (b_red != 0)
# Cross-check the other direction: (x,y,b) strictly contains (x,y).
strict = (G_xyb.reduce(x)[1] == 0 and G_xyb.reduce(y)[1] == 0 and b_escapes)
print("(x,y,b) strictly contains (det P, det Z)=(x,y):", strict)
E3 = b_escapes and strict
print("E3 VERDICT  KILL fires (single-factor divisors miss the alignment b):", E3)

# ---- E4: (x,y,b) is a smooth codim-3 complete intersection -----------------
hdr("E4: (x,y,b) smooth, codim 3 = C_2")
J = sp.Matrix([[sp.diff(g, v) for v in GENS] for g in (x, y, b)])  # 3 x 4 Jacobian
rk = J.rank()  # exact rank over QQ(x,y,b,c)
def Ck(k): return k*k - (k*k)//4
print("Jacobian of (x,y,b) =", J.tolist())
print("rank(Jacobian) =", rk, " ; codim of center = 3 ; C_2 =", Ck(2))
E4 = (rk == 3 == Ck(2))
print("E4 VERDICT  smooth codim-3 complete intersection = C_2:", E4)

# ---- overall ---------------------------------------------------------------
hdr("W1 OVERALL")
ok = E1 and E2 and E3 and E4
print("E1 (ideal = (x,y,b)):", E1)
print("E2 (factor divisors x,y):", E2)
print("E3 (KILL: b escapes (x,y)):", E3)
print("E4 (smooth codim-3 = C_2):", E4)
print("W1 PASS:", ok)
assert ok, "W1 FAILED — a load-bearing exhibit did not reproduce"
print("\n[W1] joint center (x,y,b) survives every single-factor blow-up. "
      "min-corank>=2 is NOT single-factor-principalizable.")

# =============================================================================
# CHECKED-IN OUTPUT (verbatim, python3 w1_joint_center_survival.py):
# -----------------------------------------------------------------------------
# (see w1_joint_center_survival.out for the full captured run)
# Key lines:
#   E1 VERDICT  I(P*Z) = (x,y,b): True
#   E2 VERDICT  det P = x and det Z = y: True
#   b reduced mod (det P, det Z) = b  (nonzero => b NOT in the ideal)
#   E3 VERDICT  KILL fires (single-factor divisors miss the alignment b): True
#   E4 VERDICT  smooth codim-3 complete intersection = C_2: True
#   W1 PASS: True
# =============================================================================
