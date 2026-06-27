#!/usr/bin/env python3
"""
L32a_N2b_keyident.py — the SINGLE key algebraic identity that collapses N2b's comparison.

CLAIM (no U / column-shear needed):
    (R·S)_bot  =  (M21·M11⁻¹) · (R·S)_top  +  Sc · S_bot
where Sc = M22 − M21·M11⁻¹·M12 and (R·S)_top/bot are the top-j / bottom-(r−j) rows of R·S.

If TRUE, then with A := M21·M11⁻¹ (the row-shear, |A entry| ≤ 1 on the cell):
    R·S = [ (R·S)_top ; A·(R·S)_top + Sc·S_bot ]
    D   = frobSq((R·S)_top) + frobSq(Sc·S_bot)
and the two-sided comparison frobSq(R·S) ≍ D follows from:
  forward:  frobSq(R·S) = frobSq((R·S)_top) + frobSq(A·(R·S)_top + Sc·S_bot)
                        ≤ frobSq((R·S)_top) + 2·frobSq(A·(R·S)_top) + 2·frobSq(Sc·S_bot)
                        ≤ (1+2K)·frobSq((R·S)_top) + 2·frobSq(Sc·S_bot)  ≤ c1·D
            where K = bound on frobSq(A·X)/frobSq(X) from |A entry|≤1 (K = j·(r−j) say).
  reverse:  frobSq(Sc·S_bot) = frobSq((R·S)_bot − A·(R·S)_top)
                             ≤ 2·frobSq((R·S)_bot) + 2·frobSq(A·(R·S)_top)
                             ≤ 2·frobSq((R·S)_bot) + 2K·frobSq((R·S)_top)
            so D = frobSq((R·S)_top)+frobSq(Sc·S_bot) ≤ (1+2K)·frobSq((R·S)_top)+2·frobSq((R·S)_bot)
                 ≤ c·frobSq(R·S)   (both blocks of R·S are ≤ frobSq(R·S)).  ⟹ c0·D ≤ frobSq(R·S).

This is MUCH simpler than the full L⁻¹·diag·U⁻¹ route: it needs ONLY the row-shear bound (already proved
in Lean) + frobSq_add_le + frobSq_mul_entryBound_le. No U, no column-shear, no L⁻¹ inversion in Lean.
"""
import numpy as np
rng = np.random.default_rng(11)

def frobSq(M): return float(np.sum(M**2))

print("="*78)
print(" KEY IDENTITY: (R·S)_bot = (M21·M11⁻¹)·(R·S)_top + Sc·S_bot")
print("="*78)
worst = 0.0
for (r,j,p) in [(2,1,4),(3,1,5),(3,2,5),(4,1,6),(4,2,6),(4,3,6),(5,2,7),(5,3,7)]:
    mx = 0.0
    for _ in range(3000):
        R = rng.standard_normal((r,r))
        M11=R[:j,:j]; M12=R[:j,j:]; M21=R[j:,:j]; M22=R[j:,j:]
        if abs(np.linalg.det(M11))<1e-3: continue
        S = rng.standard_normal((r,p))
        M11inv=np.linalg.inv(M11)
        Sc = M22 - M21@M11inv@M12
        A = M21@M11inv
        RS = R@S
        RS_top = RS[:j,:]; RS_bot = RS[j:,:]; S_bot = S[j:,:]
        lhs = RS_bot
        rhs = A@RS_top + Sc@S_bot
        mx = max(mx, np.max(np.abs(lhs-rhs)))
    worst = max(worst, mx)
    print(f"r={r},j={j},p={p}:  max|(R·S)_bot − (A·(R·S)_top + Sc·S_bot)| = {mx:.2e}")
print()
print(f"WORST residual = {worst:.2e}")
print("VERDICT:", "IDENTITY HOLDS — N2b collapses to row-shear + frobSq_add_le + Cauchy-Schwarz."
      if worst < 1e-9 else "IDENTITY FAILS — re-derive.")
