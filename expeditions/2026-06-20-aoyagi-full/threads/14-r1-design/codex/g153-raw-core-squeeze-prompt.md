<task>
Lean/Mathlib RLCT proof for deep linear networks. A SIMPLIFICATION I want red-teamed before building.

SETUP. At a rank-r-exact deepest point, each layer is gauge-sliced to C_s = [[I_r+X_s, Y_s],[Z_s,T_s]]
(deviation blocks; T_s = the reduced (H_s−r)×(H_{s+1}−r) block, M_s=H_s−r the reduced widths). The
square-Frobenius loss is ‖∏C_s − D‖²_F where D = blockdiag[I_r, 0] (the deepest product value). Block-
summing the Frobenius norm: loss = ∑(E²) + ‖P11‖², where E = (∏C − D) on the (0,0),(0,1),(1,0) blocks
(the "regular residuals"), and P11 = the (1,1) block of ∏C.

THE KNOWN TRAP (verified). On {E=0}, P11 = T·(I−VY)⁻¹·S (gauge-normalized chain T̃), NOT raw T·S — and
‖T·g·S‖² is NOT two-sided-comparable to ‖T·S‖² (g=(I−VY)⁻¹ between T,S maps a TS=0 dir to TgS≠0, ratio→∞).
So comparing the CORES alone (‖P11‖² vs ‖∏T‖²) fails.

THE SIMPLIFICATION I want to verify. I claim the FULL squeeze holds against the RAW ∏T core:
  ∃ U ∈ 𝓝(w0), ∃ c₁,c₂>0, ∀ pt ∈ U:  c₁·Φ ≤ loss ≤ c₂·Φ,   where Φ := ∑E² + ‖∏T_s‖²  (RAW chain).
Monte-Carlo (r=1, (3,3,3), 500k samples) gives L/Φ → 1 as the deviation scale → 0:
  scale 0.2: [0.77,1.57];  0.1: [0.92,1.10];  0.05: [0.98,1.02];  0.02: [0.996,1.004].
Mechanism I believe: loss − Φ = ‖P11‖² − ‖∏T‖² = (P11−∏T)·(P11+∏T)-ish, and P11 − ∏T ∈ ideal(regular
coords) (vanishes at E=0... NO, at reg-deviation=0). Each term of P11−∏T carries ≥1 regular factor
(Y_s or Z_s or X_s), so ‖P11−∏T‖² ≲ (reg)²·(bounded) ≲ ∑E² near w0 (since E01~Y, E10~Z linearly ⟹
∑E² ≳ ‖reg-linear part‖²). Hence |loss−Φ| ≲ ∑E² ≤ Φ, giving the two-sided bound with c₁,c₂→1.

If TRUE, this AVOIDS the Schur complement (I+E00)⁻¹ entirely — Φ uses the raw ∏T core, which is
literally dlnLoss M 0 of the (T_s) tuple ∈ Params M. Massive Lean simplification.
</task>

<output_contract>
Terse. Answer:
1. Is the full-squeeze-vs-raw-∏T claim TRUE near w0? (yes / no / true-but-with-caveat). One sentence why.
2. Is my mechanism (loss−Φ = ‖P11‖²−‖∏T‖², and ‖P11−∏T‖² ≲ ∑E² because every term of P11−∏T carries a
   regular factor) CORRECT? Identify the single weakest step.
3. THE TRAP CHECK: the known trap is ‖P11‖²/‖∏T‖²→∞ when ∏T→0 with reg≠0. Why does this NOT break the
   FULL squeeze c₁Φ ≤ loss ≤ c₂Φ? (i.e. when ∏T→0, is the excess ‖P11‖² genuinely charged to ∑E² in Φ?)
   Or does it break it — give the exact configuration if so.
4. The cleanest Lean inequality to prove for the UPPER bound (loss ≤ c₂Φ) and LOWER bound (c₁Φ ≤ loss),
   stated in terms of ∑E², ‖P11‖², ‖∏T‖². Is |‖P11‖²−‖∏T‖²| ≤ K·∑E² (on a 𝓝 w0) the right lemma, and
   is K genuinely bounded (not blowing up as reg→0)?
5. The single most likely way this simplification is SUBTLY WRONG.
</output_contract>

<grounding_rules>
Distinguish proven-fact from inference. The Monte-Carlo is evidence not proof. If you can construct an
exact configuration breaking the full squeeze, give it explicitly (matrices). The block algebra is
trusted; reason about the squeeze inequality's truth and its cleanest Lean form.
</grounding_rules>
