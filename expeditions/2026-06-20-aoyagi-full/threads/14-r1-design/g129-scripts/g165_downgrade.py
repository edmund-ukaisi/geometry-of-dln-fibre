import sympy as sp
# cobuild-sub34: #54 is a SQUEEZE (c₁=1/2,c₂=2 at w0). My "leak absorbed into ∑E²" overclaimed because
# the absorption COUPLES R and the regular block via the cross term 2⟨R,leak⟩. Verify: is 2⟨R,leak⟩ ≠ 0
# (R NOT ⊥ leak), so the "redefined ∑E²" is NOT a clean regular block?
# Setup (rank-1, (2,2,2)): P11 = T1 T2 + Z1 Y2 (g151). R = the Schur complement (gauge-normalized).
# leak = P11 - R. The Frobenius split loss = ∑E² + ‖P11‖² (EXACT, lemma 3). Then ‖P11‖² = ‖R + leak‖² =
# ‖R‖² + 2⟨R,leak⟩ + ‖leak‖². For "exact ∑E²+‖R‖²" we'd need ‖P11‖² = ‖R‖² i.e. 2⟨R,leak⟩+‖leak‖²=0 OR
# absorbed into ∑E². cobuild-sub34: it's NOT absorbed cleanly (2⟨R,leak⟩ couples). Verify 2⟨R,leak⟩≠0.
a,b,d,G0,G1 = sp.symbols('a b d G0 G1', real=True)  # the (2,2,2) reduced-node coords (g131/g151)
# P11-block reduced core context: from g151, residual core ‖S·Γ‖², S=d-ab, Γ=(G0,G1). The "P11" (1,1)
# block in the 2-layer gauge product. Use the g151 model: P11 (scalar) on {E=0} = T(I-VY)^{-1}S, R = the
# Schur complement. The leak = the E-dependent part. Let me use the FULL P11 = T1 T2 + Z1 Y2 form and
# R = T1 T2 (the "raw" reduced chain), leak = Z1 Y2 (the cross). Check ⟨R,leak⟩ over the reduced entries.
# (rank-1 scalars) R = aT0*bT0 (= T1 T2), leak = aZ0*bY0 (= Z1 Y2). ‖P11‖² = (R+leak)².
R, leak = sp.symbols('R leak', real=True)
# 2⟨R,leak⟩ for scalars = 2 R leak. Is it ≡ 0? Only if R or leak ≡ 0. Generically R,leak ≠ 0, and they
# are INDEPENDENT (R = T1T2 in the T-coords, leak = Z1Y2 in the Z,Y regular coords). So 2 R leak ≠ 0:
print("=== Verify the cross term 2⟨R,leak⟩ ≠ 0 (R not ⊥ leak) — cobuild-sub34's coupling point ===")
# R = aT0 bT0 (reduced T-coords), leak = aZ0 bY0 (Z,Y are REGULAR coords). cross = 2·R·leak =
aT0,bT0,aZ0,bY0 = sp.symbols('aT0 bT0 aZ0 bY0', real=True)
Rexpr = aT0*bT0; leakexpr = aZ0*bY0
cross = sp.expand(2*Rexpr*leakexpr)
print(f"  R = T1 T2 = {Rexpr} (reduced T-coords);  leak = Z1 Y2 = {leakexpr} (Z,Y REGULAR coords)")
print(f"  cross 2⟨R,leak⟩ = {cross}")
print(f"  ≡ 0? {cross == 0}  ⟹ NOT zero generically. R (T-coords) and leak (Z,Y-coords) are INDEPENDENT,")
print(f"  so 2⟨R,leak⟩ = 2 T1 T2 Z1 Y2 ≠ 0 — the cross term COUPLES the reduced core (T) and regular (Z,Y).")
print()
print("⟹ cobuild-sub34 is RIGHT: 'absorb leak into ∑E²' gives ∑E²(redef) = ∑E² + 2⟨R,leak⟩ + ‖leak‖², and")
print("the 2⟨R,leak⟩ = 2 T1T2 Z1Y2 COUPLES core (T) and regular (Z,Y) — NOT a clean regular block. So the")
print("'exact ∑E²+‖R‖²' framing breaks the reg/core separation (sub-6 needs ∑E² clean). The HONEST form")
print("is the SQUEEZE: keep ∑E² and ‖R‖² separate, BOUND the leak (c₁∑E²+‖R‖² ≤ loss ≤ c₂(...), c₁<c₂).")
print()
print("VERDICT: g155 → SQUEEZE. #48's 'exact germ' OVERCLAIMED. The Frobenius split loss=∑E²+‖P11‖² IS")
print("exact (lemma 3); but the P11→R step (‖P11‖² vs ‖R‖²+∑E²) is a genuine SQUEEZE (the leak couples,")
print("c₁<c₂ even at w0 per cobuild-sub34's #54 constants c₁=1/2,c₂=2). Name the FULL comparability SQUEEZE.")
print("Not a soundness issue (loss_squeeze accommodates it); the honest NAME. My downgrade criterion FIRES.")
