<task>
Independent adjudication of a matrix-integral finiteness/domination claim (real log-canonical-threshold work on deep linear networks). Argue whichever direction the algebra supports; my own conclusion is WITHHELD. Distinguish OBSERVED FACT (you derived/verified) from INFERENCE.

SETUP. Fix integers M0,M1,M2,...,M_last (a chain of layer widths), a cut u≥1, and set a=M0-u, b=M1-u. Let:
- z range over a box of "deep" parameters; Q_p = Q_p(z) := prod(redChain u M) z is a u×n matrix (n=M_last); it is a nonzero polynomial in z, full-row-rank u for generic z.
- A_cor range over the box [-1,1]^{b×M2}; Z=Z(z) is an M2×n matrix (deep-tail product) with rank ≥ a+b; Q_b := A_cor·Z is b×n.
- hsQ := [Q_p ; Q_b] (stacked (u+b)×n = M1×n). Its singular values equal those of the full front product.
- x=(P,B12,C) with P u×u INVERTIBLE (IsUnit P), B12 u×b, C a×u, all in [-1,1] boxes; Γ a×b.
- freedSchurLoss = frobSq(P·(Q_p + P^{-1}B12 Q_b)) + frobSq(C·(Q_p + P^{-1}B12 Q_b) + Γ·Q_b).
  Equivalently (shear Γ' = Γ + C P^{-1} B12): = frobSq([P|B12]·hsQ) + frobSq(C·Q_p + Γ'·Q_b).

SHELL-j RESTRICTION (1 ≤ j < r := min(M0-t*,M1-t*)): A_cor restricted to {hsQ ∈ singularShell j} = exactly j singular values of hsQ are < ε, the other min(M1,M2)-j are ≥ ε (a PARTIAL floor: min(M1,M2)-j strong directions floored ≥ ε; j weak directions allowed small).

CLAIM TO ADJUDICATE (∗_T1). For ab/2 < c' < T1 := (1/2)·minAdm(M) [full-chain min over cuts r of (M0-r)(M1-r)+minAdm(redChain r M)], there is a finite constant C_j (allowed → ∞ as c'→T1⁻; NOT uniform in c') with
   ∫_z ∫_{A_cor: shell-j} ∫_{x: P unit, box} ∫_{Γ: shear-box} freedSchurLoss^{-c'}
     ≤ C_j · ∫_z (commonDivisor(z)^2 · frobSq(Q_p(z)))^{-(c'-ab/2)}   [the reduced comparator on the SHORTER chain redChain u M].

KNOWN FACTS (established elsewhere, exact ℚ-Jacobian + decorrelated):
(K1) The OFF-SHELL version (A_cor over the FULL box, IsUnit-P kept, NO shell restriction) is finite only to T1 and is u-INDEPENDENT = ∫‖B·W‖^{-2c'} with RLCT ½minAdm(M); off-shell it is NON-DESCENDING (equals the goal B(M) itself), so unusable as a recursion step.
(K2) The exact Schur identity det(hsQ hsQᵀ)=det(Q_p Q_pᵀ)·det(Q_b (I-Π_p) Q_bᵀ), Π_p=proj onto rowspan(Q_p). The honest weak-determinant is the TRANSVERSE Schur complement det(Q_b(I-Π_p)Q_bᵀ), NOT bare det(Q_b Q_bᵀ).
(K3) A banked lemma gives, for ANY positive weight wf(A_cor)>0 and Ccross:
   ∫_{A_cor box} ∫_Γ (wf(A_cor)+frobSq(Ccross+Γ·Q_b))^{-c'}
     ≤ ∫_{A_cor box} det(Q_b Q_bᵀ)^{-a/2}·Cresid(ab,c')·(wf(A_cor)+frobSq(Ccross·(I-Q_bᵀ(Q_bQ_bᵀ)^{-1}Q_b)))^{-(c'-ab/2)}   [ab/2 charge as Jacobian, exponent shift, residual carries Π_{rowspan Q_b}^⊥, COUPLED].
(K4) Another banked lemma (A_cor-FREE scalar w only): ∫_{A_cor box}∫_Γ (w+frobSq(Ccross+Γ·(A_cor Z)))^{-c'} ≤ Cunif·w^{-(c'-ab/2)}, Cunif free of Z,Ccross,w — provided a DEEP floor ZZᵀ ⪰ ε²·U_s U_sᵀ (U_s orthonormal m-frame, m≥a+b) holds.
(K5) A banked P-radial blow-up: ∫_W φ(frobSq(W·Q)) = ∫_{sphere}∫_{r>0} r^{u·M1-1}·φ(r²·frobSq(reshape(ω)·Q)) (W=[P|B12], the u×M1 front block).
(K6) A banked D-B finiteness: for a rank-ρ linear map L, ∫_{cube} (Σ_j (Lx)_j²)^{-c''} < ⊤ for c'' < ρ/2.
(K7) hpiv: minAdm(redChain u M) ≤ u·ρ where ρ = min of the deep widths (tailMinWidth).

OPEN, UN-ADJUDICATED question (a prior internal recon flagged the shell-j∧IsUnit-P object "soundness-un-adjudicated, candidate wall"): does adding the shell-j PARTIAL floor (+ IsUnit-P) to the off-shell object (K1) restore per-exponent finiteness/domination (∗_T1) up to c'<T1 (in fact up to λ_j ≥ T1), by EXCLUDING the binding low-rank corner that makes (K1) diverge at T1? Or is there a residual divergence (e.g. from the transverse-Schur alignment Q_b rowspace → Q_p rowspace, K2) that the partial floor does NOT exclude?
</task>

<output_contract>
Three sections, terse:
1. SOUNDNESS VERDICT: is (∗_T1) TRUE (per-exponent C_j) on the shell-j partial-floor ∧ IsUnit-P object for 1≤j<r, ab/2<c'<T1? Give the single sharpest reason (or the single sharpest counterexample/divergent corner if FALSE). Label FACT vs INFERENCE.
2. CHEAPEST SOUND ROUTE: the minimal chain of steps from the banked pieces (K3/K4/K5/K6) to (∗_T1). Name the ONE genuinely-new sub-lemma that is not covered by K3-K6, stated precisely. Is the pivot weight wf kept coupled (K3) enough, or must the P-radial blow-up (K5) first DECOUPLE wf to the A_cor-free decLoss form so K4 applies? 
3. THE WALL: the single hardest sub-step, and whether it is LABOUR (mechanism clear, just long) or a genuine WALL (missing math / missing Mathlib primitive). Name the specific missing ingredient.
</output_contract>

<grounding_rules>
State explicitly which claims you VERIFIED by derivation vs INFERRED. If you construct a divergent corner, give the explicit scaling (A_cor=t·A0, z fixed, etc.) and the exponent count. Do not trust K1-K7 blindly if your derivation contradicts one — flag the contradiction.
</grounding_rules>
