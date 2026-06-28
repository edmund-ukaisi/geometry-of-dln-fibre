<task>
Lean 4 / Mathlib. I must prove a general output-width-p corank-2 finiteness:

  theorem schurCoreP_two (p : ℕ) (hp : 0 < p) (c' : ℝ) (hc0 : 0 < c')
    (hc' : c' < schurLambdaP p 2) (T : ℝ) (hT : 0 < T) : SchurCore p 2 c' T

where SchurCore p 2 c' T := `∫_{Δ∈[-T,T]^{2×2}} ∫_{S∈[-T,T]^{2×p}} frobSq(Δ·S)^{-c'} < ⊤`
(frobSq = sum of squared entries of the 2×p matrix Δ·S; Δ is 2×2, S is 2×p, rmatMul = matrix product).

schurLambdaP p 2 = minAdm(![2,2,p])/2 = min(4, 1+p, 2p)/2. For p=1: min(4,2,2)/2 = 1. p=2: min(4,3,4)/2=3/2.
p=3: min(4,4,6)/2=2. p≥4: min(4,1+p,2p)=4 ⟹ =2. So schurLambdaP p 2 = min(4,1+p,2p)/2, in (1/2, 2].

WHAT I HAVE (all sorry-free, general p):
- `schurCoreP_one (p) (hp:0<p) (c') (hc0) (c'<schurLambdaP p 1 = 1/2) (T) (hT) : SchurCore p 1 c' T`
  (the Morse leaf; frobSq(Δ·S)=Δ₀₀²·∑_q S₀q², a 1-D radial divisor × a width-p Morse block).
- `schurCoreP_directMorse (p r) (hr : 3 ≤ r) (c') (hc0) (c'<p/2) (c'<r²/2) (T) (hT) : SchurCore p r c' T`
  — the cap-B finiteness via an r²-chart radial cover, BUT it carries `hr : 3 ≤ r` (the chart-level
  pivot-normalisation `RmatGnorm` and the carve-slot bijection `slotFunR` are stated with hr:3≤r in a
  SEPARATE upstream file I cannot edit; relaxing to 2≤r is not available).
- The full cap-A carve (`schurRatioResidGenP_mid`, `innerSGenCarveP_le`, `schur_matBoxGenP_chart_capA_lt_top`)
  — ALSO carries hr:3≤r (uses the same RmatGnorm / slotFunR machinery). So r=2 cannot use the carve.
- An ABSTRACT lower IH at corank 1: SchurCore p 1 c'' T'' for 0<c''<schurLambdaP p 1=1/2.
- The N2b minor-pivot Schur split is AVAILABLE at any r,p:
  `schur_minorPivot_split (r:=r) (p:=p) (j:=1) (hj:1≤r) : ∃ c₀ c₁, 0<c₀ ∧ 0<c₁ ∧ ∀ R S (bounded cell hyps),
   ∃ Sc:Matrix(Fin(r-1))(Fin(r-1)), Sc = M22-M21·M11⁻¹·M12 ∧ R.det=det M11·det Sc ∧
   c₀·(frobSq(top j rows of R·S) + frobSq(Sc·S_bot)) ≤ frobSq(R·S) ≤ c₁·(same)`.
- A Morse-peel: `core_T_peel_le_aeG (m) (μ) (c') ((m+1)/2<c') (Tw) (w:Ω→ℝ) (Z) (w>0 a.e. on Z) :
   ∫_Z ∫_{T∈morseBox(m+1)Tw}(∑Tᵢ²+w z)^{-c'} ≤ Cresid(m+1)c' · ∫_Z (w z)^{-(c'-(m+1)/2)}`.
- A reusable `Fin p` a.e.-positivity `frobSqGP_ne_zero_ae` / `frobSqShiftGP_ne_zero_ae`.
- The leaf bricks `coreSchurGenValP (r-1) p c'' Kr` + `coreSchurGenValP_lt_top` (needs hr:3≤r!) and
  `schurResidGP_translate_le` (needs hr:3≤r!).
- radial machinery: `radial_morse_dominates_lt_top`, `radial_aAxis_divisor_lt_top` (Δ-axis divisor finite
  for the radial exponent > -1).

THE QUESTION: what is the CHEAPEST way to prove `schurCoreP_two`? The corank is 2, so the angular matrix is
2×2 and there are only 4 charts (max-modulus-entry pivot). I cannot reuse the hr:3≤r chart machinery.
Possible routes:
(R1) A DIRECT 2×2 argument: frobSq(Δ·S) where Δ is 2×2. Is there a clean elementary lower bound /
     factorisation at r=2 that avoids the chart cover entirely? E.g. via Δ = row-reduction or the explicit
     2×2 structure.
(R2) Replicate the r²=4-chart radial cover MANUALLY at r=2 (4 charts), each chart: a-axis radial divisor
     (c' < r²/2 = 2) × a 1×1-residual angular integral. At r=2 the angular residual is over r²-1=3 ratios
     and the N2b j=1 split gives a 1×1 Sc, residual core at corank-1 closed by the corank-1 IH
     (SchurCore p 1). But this is essentially re-deriving the carve at r=2 — is it materially simpler
     because Fin 1 collapses (Sc is a scalar, the M22/g/b carve cube is small)?
(R3) Some monotonicity/domination trick reducing SchurCore p 2 to a product of corank-1 cores?
(R4) Other.

Rank R1–R4 by Lean-effort (lines + risk). For the top route, give a concrete proof skeleton (≤15 lines of
Lean-shaped pseudo-steps): the key lemma calls, the threshold arithmetic (which of min(4,1+p,2p) bounds
feed where), and the single hardest step.
</task>

<output_contract>
Two sections:
A. RANKING of R1–R4 (one line each: effort estimate + the blocking difficulty).
B. SKELETON for the winner (≤15 pseudo-steps), naming the threshold inequalities used and the hardest step.
Mark INFERENCE where you cannot verify a Mathlib lemma exists.
</output_contract>

<grounding_rules>
Reason from the structure described; you cannot see the source. Flag any lemma you assume exists but cannot
confirm as INFERENCE. Be concrete about the r=2 simplifications (Fin 1 collapses, 2×2 determinant).
</grounding_rules>
