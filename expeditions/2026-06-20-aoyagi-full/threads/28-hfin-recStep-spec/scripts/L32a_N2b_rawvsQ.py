#!/usr/bin/env python3
"""
L32a_N2b_rawvsQ.py — does the Lean statement's RAW Sc·S_bot differ from the cert's natural Sc·Q?

The block-Gauss normal form proof naturally produces  R·S = L⁻¹ · (M11·P ; Sc·Q),  where
  S = U·(P;Q), i.e. P = S_top + M11⁻¹·M12·S_bot,  Q = S_bot   (U=[[I,−M11⁻¹M12],[0,I]], U⁻¹=[[I,+...],[0,I]])
Wait — careful with U vs U⁻¹. We have L·R·U = diag(M11,Sc). So R = L⁻¹·diag(M11,Sc)·U⁻¹, and
  R·S = L⁻¹·diag(M11,Sc)·(U⁻¹·S).  Let (P;Q) := U⁻¹·S.  U⁻¹ = [[I, +M11⁻¹M12],[0,I]] (unitriangular inv).
  So P = S_top + M11⁻¹M12·S_bot,  Q = S_bot.   THUS Q = S_bot EXACTLY (bottom block of U⁻¹·S = S_bot).
  And diag(M11,Sc)·(P;Q) = (M11·P ; Sc·Q) = (M11·P ; Sc·S_bot).

So the NATURAL normal-form gives the SECOND block = Sc·S_bot — EXACTLY the Lean statement's term!
(The first block M11·P = M11·(S_top + M11⁻¹M12 S_bot) = M11·S_top + M12·S_bot = (R·S)_top? Check that too:
 (R·S)_top = M11·S_top + M12·S_bot. And M11·P = M11·S_top + M11·M11⁻¹M12·S_bot = M11·S_top + M12·S_bot. YES.)

So the Lean statement's blocks (R·S)_top and Sc·S_bot are EXACTLY the natural normal-form blocks
M11·P and Sc·Q. The raw-block Lean form IS the cert's natural form — NO extra reconciliation needed.
This script CONFIRMS this numerically across r,j.
"""
import numpy as np
rng = np.random.default_rng(7)

def frobSq(M): return float(np.sum(M**2))

def check(r, j, p, n=2000):
    max_block1 = 0.0   # |(R·S)_top − M11·P|
    max_block2 = 0.0   # |Sc·S_bot − Sc·Q|  (trivially 0 since Q=S_bot, but check the WHOLE identity)
    max_full = 0.0     # |R·S − L⁻¹·(M11·P ; Sc·Q)|
    for _ in range(n):
        R = rng.standard_normal((r, r))
        M11 = R[:j,:j]; M12 = R[:j,j:]; M21 = R[j:,:j]; M22 = R[j:,j:]
        if abs(np.linalg.det(M11)) < 1e-3: continue
        S = rng.standard_normal((r, p))
        M11inv = np.linalg.inv(M11)
        Sc = M22 - M21@M11inv@M12
        L = np.eye(r); L[j:,:j] = -M21@M11inv
        U = np.eye(r); U[:j,j:] = -M11inv@M12
        Uinv = np.linalg.inv(U)
        Linv = np.linalg.inv(L)
        PQ = Uinv @ S
        P = PQ[:j,:]; Q = PQ[j:,:]
        RS = R@S
        RS_top = RS[:j,:]
        S_bot = S[j:,:]
        # block 1: (R·S)_top vs M11·P
        max_block1 = max(max_block1, np.max(np.abs(RS_top - M11@P)))
        # Q vs S_bot
        max_block2 = max(max_block2, np.max(np.abs(Q - S_bot)))
        # full: R·S = L⁻¹·(M11·P ; Sc·S_bot)
        W = np.vstack([M11@P, Sc@S_bot])
        max_full = max(max_full, np.max(np.abs(RS - Linv@W)))
    return max_block1, max_block2, max_full

print("="*78)
print(" Lean RAW (R·S)_top + Sc·S_bot  vs  natural normal-form M11·P + Sc·Q")
print("="*78)
for (r,j,p) in [(2,1,4),(3,1,5),(3,2,5),(4,1,6),(4,2,6),(4,3,6)]:
    b1, b2, full = check(r,j,p)
    print(f"r={r},j={j},p={p}:  |(R·S)_top − M11·P| = {b1:.2e}   |Q − S_bot| = {b2:.2e}   "
          f"|R·S − L⁻¹(M11·P; Sc·S_bot)| = {full:.2e}")
print()
print("VERDICT: if all ≈ 0, the Lean raw-block form IS the natural normal-form (Q = S_bot exactly,")
print("(R·S)_top = M11·P exactly), so NO extra reconciliation step is needed — the comparison")
print("frobSq(R·S) ≍ frobSq((R·S)_top) + frobSq(Sc·S_bot) follows from frobSq(L⁻¹·W) ≍ frobSq(W).")
