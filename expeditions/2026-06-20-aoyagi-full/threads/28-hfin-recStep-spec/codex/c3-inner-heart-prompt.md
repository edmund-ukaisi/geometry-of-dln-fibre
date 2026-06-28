<task>
Lean 4 / Mathlib v4.29. I have BANKED (sorry-free, building) these corank-3 bricks and need the tightest Lean recipe for the SOLE remaining sorry: the JOINT inner heart `schurInner3_ratiofin`. I want a concrete step list, flagging the 1-2 genuinely thrash-prone steps.

BANKED (all sorry-free, in my module RouteMSchurCorank3):
- `schurResid2_translate_le (Sh : Fin 2→Fin 2→ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B) (c'' T : ℝ) :`
    `(∫⁻ Δ in matBox 2 2 T, ∫⁻ S in matBox 2 4 T, ofReal(frobSq(rmatMul (fun i j => Δ i j - Sh i j) S)^(-c''))) ≤ coreSchur2Val c'' (T+B)`
  where `coreSchur2Val c'' Kr := ∫⁻ Δ in matBox 2 2 Kr, ∫⁻ S in matBox 2 4 Kr, ofReal(frobSq(rmatMul Δ S)^(-c''))`, and `coreSchur2Val_lt_top : 0<c''→c''<2→0<Kr→ coreSchur2Val c'' Kr < ⊤`.
- `resolvedShiftR2c3_le (Sh)(B)(hB)(K)(hK:0<K)(c')(hc2:2<c')(hc4:c'<4) :`
    `(∫⁻ Δ in matBox 2 2 K, ∫⁻ S in matBox 2 4 K, ∫⁻ T in morseBox 4 K, ofReal((∑ i, (T i)^2 + frobSq(rmatMul (fun a b => Δ a b - Sh a b) S))^(-c'))) ≤ ofReal(Cresid 4 c') * coreSchur2Val (c'-2) (K+B)`
  (the FULL peel+shifted-residual bundle, uniform in Sh, finite RHS).
- N2b: `schur_minorPivot_split (r:=3)(p:=4) (j:=1) (hj:1≤3)` returns `∃ c₀ c₁, 0<c₀ ∧ 0<c₁ ∧ ∀ (R : Matrix (Fin 3)(Fin 3) ℝ)(S : Fin 3→Fin 4→ℝ), (∀ a b,|R a b|≤1) → (pivot-maxminor hyp) → (det M11 ≠ 0) → ∃ Sc : Matrix (Fin 2)(Fin 2) ℝ, Sc = M22 − M21·M11⁻¹·M12 ∧ R.det = (det M11)·Sc.det ∧ c₀·D ≤ frobSq(rmatMul R S) ∧ frobSq(rmatMul R S) ≤ c₁·D` where `D = frobSq(fun a:Fin 1 => rmatMul R S ⟨a,_⟩) + frobSq(rmatMul (fun a b => Sc a b) (fun a:Fin 2 => S ⟨1+a,_⟩))`. Here M11 = R₀₀ (1×1), M21 a = R⟨1+a⟩⟨0⟩, M12 b = R⟨0⟩⟨1+b⟩, M22 a b = R⟨1+a⟩⟨1+b⟩.
- `schurSplit_lintegral_le (μ)(c₀ c₁)(hc₀)(D F : Ω→ℝ)(Z)(hD≥0)(hF≥0)(hlow:∀z,c₀·D z≤F z)(hupp:∀z,F z≤c₁·D z)(c')(0<c') : ∫_Z F^(-c') ≤ ofReal(c₀^(-c'))·∫_Z D^(-c')`.
- chart helpers: `Rmat3 p y` (3×3, pivot entry e3.symm p = 1, off-pivot = y-components), `Rmat3_pivot`, `Rmat3_entry_le`, `innerS3 c' T p y = ∫_S frobSq(rmatMul (Rmat3 p y) S)^(-c')`, `innerS3_offpivot`, `measurable_innerS3`. Also corank-2 has `frobSq_rmatMul_perm2` (2×2) + `matBox24_rowperm_lintegral` for pivot-swap.
- `radial_morse_residual_power_le`, `core_T_peel_le_ae_c3`, `frobSqShiftR2c3_ne_zero_ae`.

THE SORRY:
`schurInner3_ratiofin (c')(hc0:0<c')(hc':c'<4)(T)(hT:0<T)(p : Fin 9) : ∫⁻ z in (univ.pi (fun _:Fin 8 => Icc (-1) 1)), innerS3 c' T p ((piFinSuccAbove (fun _:Fin 9 => ℝ) p).symm (0, z)) < ⊤`.

MY PLAN:
A. Branch c'≤2 vs 2<c'. For c'≤2: dominate `frobSq(R·S)^(-c') ≤ 1 + frobSq(R·S)^(-3)` pointwise (x^{-c'} ≤ 1+x^{-3} for x>0, c'≤2<3; x=0 gives 0^{neg}=0≤...), reducing to the c''=3∈(2,4) case + a finite-volume `1`-integral over (z-box)×(S-box). So the CORE is the 2<c'<4 case.
B. (2<c'<4 CORE) Bring pivot to (0,0): by perm-invariance, innerS3 c' T p (e.symm(0,z)) = innerS3-at-pivot-(0,0) of a permuted angular matrix. (Or: prove the whole thing at a generic pivot via Rmat3_pivot/Rmat3_entry_le giving R i₀ j₀=1, |R|≤1, and N2b is pivot-agnostic IF I conjugate to (0,0) first — corank-2 did `Equiv.swap` + frobSq_rmatMul_perm2.)
C. Per z, set R := Rmat3 p (e.symm(0,z)) (or its (0,0)-swapped form R'). Apply N2b → c₀,c₁ + Sc(z). Use schurSplit_lintegral_le to get `∫_S frobSq(R·S)^(-c') ≤ ofReal(c₀^(-c'))·∫_S D^(-c')`. Integrate over z: `∫_z innerS3 ≤ ofReal(c₀^(-c'))·∫_z ∫_S D^(-c')`.
   PROBLEM: N2b's c₀ depends on R? NO — c₀,c₁ are quantified BEFORE R,S (uniform), so use `.choose` like corank-2's `c0N2b`. Good, one fixed c₀.
D. `∫_z ∫_S D^(-c')` where D = frobSq(top-row0) + frobSq(Sc(z)·S_bot). The top-row0 = (R·S)_0 = S_0 + R₀₁ S_1 + R₀₂ S_2 (R₀₀=1) — a 4-entry Morse block sheared by S_1,S_2. Need to massage `∫_z ∫_S D^(-c')` into the `resolvedShiftR2c3_le` shape `∫_Δ ∫_S_bot ∫_T (∑T² + frobSq((Δ−Sh)·S_bot))^(-c')` with T = the sheared top block (translate to free Morse), Δ = M22(z), Sh(z) = M21(z)·M12(z), S_bot = (S_1,S_2). Then Tonelli-split z = (M22 4-coords) × (boundary 4-coords); per fixed boundary apply resolvedShiftR2c3_le (≤ const indep of boundary); then ∫_boundary const = const·vol.

QUESTIONS (rank by de-risking):
1. The Fin 8 z-coord bookkeeping in step D: is it cleaner to (a) reindex Fin 8 ≃ (Fin 2×Fin 2) × (Fin 4) via a measurable equiv and Tonelli, recognizing M22 from the {1,2}×{1,2} z-coords, OR (b) AVOID the explicit M22-recognition by NOT integrating z as raw coords but instead: bound `∫_z ∫_S D^(-c')` by first proving a per-z `∫_S D^(-c') ≤ [resolvedShift-shaped thing with Δ ranging over a SINGLE-point... no]`. I think (a) is forced. What is the cleanest measurable equiv `Fin 8 ≃ (Fin 2×Fin 2)⊕(Fin 4)` or `≃ Fin 4 × Fin 4`, and how do I match the M22-coords to the {1,2}×{1,2} entries of `Rmat3 p (e.symm(0,z))` under the e3/piFinSuccAbove parameterization? Is there a SIMPLER route that sidesteps matching exact indices — e.g. bound the angular box `[−1,1]^8` ⊇ enlarge so M22 ranges over matBox 2 2 1 freely and the boundary over [−1,1]^4 freely, via a coordinate SPLIT that doesn't need exact index identification (just that 4 of the 8 coords are the M22 entries and 4 are the M21,M12 entries)?
2. The shear-to-free-Morse + the D-to-resolvedShift massage: D's top block is sheared (T = S_0 + shift(z,S_1,S_2)). resolvedShiftR2c3_le has T FREE over morseBox 4 K. So per (z, S_bot) I translate S_0 ↦ S_0 + shift (MP), box-enlarge S_0 to radius (1 + 2·something). Is it cleaner to (a) do this translate myself and feed resolvedShiftR2c3_le, or (b) is resolvedShiftR2c3_le already the WRONG granularity and I should instead feed `core_T_peel_le_ae_c3` directly (which takes the Morse block + an arbitrary w, no shear assumption)? I.e. should I bypass resolvedShiftR2c3_le and assemble from core_T_peel_le_ae_c3 + schurResid2_translate_le directly, handling the shear translate inline? Which minimizes index friction?
3. Is the perm-to-(0,0) step (B) even needed? N2b's hypotheses fix the pivot minor to the TOP-LEFT j×j block (M11 = R restricted to {0..j-1}). For the chart pivot p (arbitrary Fin 9), Rmat3 p has its 1 at e3.symm p, NOT necessarily (0,0). So I MUST permute to bring the pivot-1 to (0,0) before N2b. Confirm, and give the cleanest perm idiom (the corank-2 schurInner_S_bound_pivot did Equiv.swap + frobSq_rmatMul_perm2 + matBox24_rowperm_lintegral — but that was for the S-box; here the angular R is parameterized by z over a box, and permuting R's rows/cols permutes which z-coords are M22 — does that interact badly with step D's z-split?).

Be concrete + Lean-idiom specific. Give a STEP LIST for the 2<c'<4 core, naming the banked lemma at each step, and RANK the 2 steps most likely to thrash with a mitigation each.
</task>

<output_contract>
1. STEP LIST (2<c'<4 core) — numbered, banked-lemma-per-step, exact Tonelli/reindex/translate move.
2. ANSWERS to Q1, Q2, Q3 — decisive (pick a/b, say why).
3. THRASH RANK — the 2 riskiest steps + a concrete mitigation each. Brief.
</output_contract>

<grounding_rules>
Distinguish VERIFIABLE-from-signatures vs INFERENCE about Mathlib. Flag any lemma you are unsure exists in v4.29; do not invent names (describe + "needs:").
</grounding_rules>
