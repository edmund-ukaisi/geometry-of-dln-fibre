#!/usr/bin/env python3
"""EXPLORATORY (not the durable battery): reconstruct Aoyagi's fold residual at an interior
case1(1)-δ=1 boost parent, in TWO ways, and cross-check them:

  (I)  b-chain form  G = diag(b) · [[E_J,O],[O,D_J]] · (deeper layers)  with D_J FRESH generic
       (per fold-recursion-template.md §1.1/§3.2/§3.4 — the faithful support model of foldResid).
  (II) a CONCRETE matrix blow-up + Q-Schur of (2,2,2,2) layer-1, tracking the generator matrix in
       ORIGINAL coordinates, to PIN the transpose (running-min axis <-> flat column axis) empirically.

Then read off the boost center (canonCenterOf case11 = {pivot} ∪ partial block) and the geometric
support (supportAt J=0 = full layer block), and check whether the residual is Deg1SupportedOn the
SMALL center.
"""
import sympy as sp
from itertools import product as iproduct

# ============================================================================
# PART II FIRST — concrete matrix blow-up of (2,2,2,2), pin the transpose.
# ============================================================================
# d=(2,2,2,2), N=3. Lean layer i matrix C_i has size d_{i+1} x d_i (rows d_{i+1}, cols d_i).
# All 2x2 here. Product mult = C_0 C_1 C_2 (d_3 x d_0 = 2x2). coreGen = its 4 entries.
print("="*78)
print("PART II: concrete (2,2,2,2) layer-0 (=template S=1) blow-up + Q-Schur, ORIGINAL coords")
print("="*78)

def mat(name, r, c):
    return sp.Matrix(r, c, lambda i, j: sp.Symbol(f'{name}{i}{j}'))

C0 = mat('a', 2, 2)   # Lean layer 0  (template C^(1)); exceptional pivots born here
C1 = mat('b', 2, 2)   # Lean layer 1  (template C^(2)); the residual D_0 at the boost parent
C2 = mat('c', 2, 2)   # Lean layer 2  (template C^(3)); deeper layer (spectator)
P = sp.expand(C0 * C1 * C2)
print("product P = C0*C1*C2, entry (0,0):", P[0, 0])

# --- resolve layer 0 (C0), radial blow-up at the diagonal corner (0,0) then (1,1) ---
# Aoyagi (template §2): blow up the residual block at its top-left pivot; normalise pivot to 1;
# the exceptional coordinate u carries the whole block's scale; Q clears the pivot ROW; the deeper
# layer's pivot ROW is recoordinatised by Q^{-1}; the SE Schur block δ-γβ continues.
#
# Step (1,0): residual block = C0 (2x2). pivot = C0[0,0] =: u11 (exceptional). In the pivot chart
# C0 = u11 * Cbar with Cbar[0,0]=1. Write Cbar = [[1, β],[γ, δ]] with β=Cbar[0,1], γ=Cbar[1,0],
# δ=Cbar[1,1].  ⟨C0 C1 C2⟩ = u11 · ⟨Cbar C1 C2⟩ (u11 -> Jacobian; δ=1 strict transform).
u11, u12 = sp.symbols('u11 u12')
beta1, gam1, del1 = sp.symbols('beta1 gam1 del1')
Cbar = sp.Matrix([[1, beta1], [gam1, del1]])
Q1 = sp.Matrix([[1, -beta1], [0, 1]])            # clears row 0: Cbar*Q1 = [[1,0],[gam1, del1-gam1 beta1]]
CbarQ = sp.expand(Cbar * Q1)
C1p = sp.expand(Q1.inv() * C1)                   # deeper layer recoordinatised: Q1^{-1} C1
print("\nafter step (1,0): Cbar*Q1 =", CbarQ.tolist(), " (pivot row cleared, SE = Schur s1)")
s1 = sp.expand(del1 - gam1 * beta1)              # the 1x1 Schur complement (fresh residual coord next)
# The invariant now: ⟨C0 C1 C2⟩ = u11 · ⟨ [[1,0],[gam1, s1]] · (Q1^{-1} C1) · C2 ⟩.
# b-chain so far: b_1 = u11 (the pulled-out scale of the whole block via diag).
# Actually the P-step conjugates by diag(b'): the pivot COLUMN gam1 is cleared, leaving the head
# diagonal [[1,0],[0,s1]] and diag(b') = diag(u11, u11) after the WHOLE-tail b-update (Edge A).
# So after step (1,0): b = (u11, u11), residual D_1 = (s1) 1x1, head E_1 = [1].

# Step (1,1): residual block = (s1) 1x1. pivot = s1 =: u12 (2nd exceptional). Whole-tail b-update
# multiplies the tail (index 2..) by u12: b = (u11, u11*u12). residual exhausts (1x1 -> 0x0).
# Rollover to (2,0): residual D_0^{(2)} = C'^(2) = the recoordinatised layer-1 matrix C1p, size 2x2.
b_chain = [u11, u11 * u12]
print("\nb-chain at (S=2,J=0):  b_1 =", b_chain[0], "   b_2 =", b_chain[1],
      "   (b_2/b_1 =", sp.simplify(b_chain[1] / b_chain[0]), "= u12 = the reused pivot)")

# The generator matrix at (2,0): G = diag(b) · C'^(2) · C2  (template: diag(b) on the LEFT, i.e. b_i
# attaches to ROW i of the residual C'^(2)). C'^(2) = C1p (recoordinatised layer 1).
Gcell = sp.diag(*b_chain) * C1p * C2
Gcell = sp.expand(Gcell)
print("\ngenerator G = diag(b)*C1p*C2  (template row = running-min axis):")
for i in range(2):
    for j in range(2):
        print(f"  G[{i},{j}] = {Gcell[i,j]}")

# Which coords are 'exceptional' (u's / born corners)?  u11 = C0[0,0] born-corner (layer0,0,0);
# u12 = s1 (Schur of C0) born-corner (layer0,1,1) = C0[1,1] slot.  In flat coords the boost pivot =
# u12 (born corner (layer0,1,1)).  The residual C1p reads layer-1 coords (b's) + the recoord beta1.
print("\nNOTE: C1p (recoordinatised layer 1) reads beta1 (a layer-0 residual coord) in its pivot row.")
print("      C1p =", C1p.tolist())
