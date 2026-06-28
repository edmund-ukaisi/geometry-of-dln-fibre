<task>
Lean 4 + Mathlib v4.29. CLOSE the single remaining sorry `schurRatioResidGen_mid` — the firing heart of a
corank-r matrix-integral finiteness. ALL supporting lemmas are PROVEN + banked; I need the exact wiring
(esp. the `zEG` carve reshape + the Sc-readback-via-reshape), to do it right without thrash. Be concrete.

## The goal (the sorry)
```
schurRatioResidGen_mid (r N : ℕ) (hN : r*r = N+1) (hr : 3 ≤ r) (hIH : SchurLowerIH 4 schurLambda r)
  (c' : ℝ) (hc2 : 2 < c') (hc' : c' < schurLambda r) (p : Fin (r*r)) (T : ℝ) (hT : 0 < T) :
  ∫_{z ∈ [-1,1]^N} innerSGen r c' T p ((piRatioG r N hN p).symm (0, z)) < ⊤
```
`innerSGen r c' T p y = ∫_{S∈matBox r 4 T} frobSq(RmatG r p y · S)^{-c'}`.

## PROVEN banked lemmas (all axiom-clean, in-file)
- `innerSGen_eq_norm (r N hN hr c' T p z) : innerSGen r c' T p ((piRatioG …).symm (0,z))
   = ∫_{S∈matBox r 4 T} frobSq(RmatGnorm r N hN hr p z · S)^{-c'}` — pivot-WLOG to (0,0).
- `RmatGnorm … z` : the (0,0)-pivot-normalised r×r angular matrix; `RmatGnorm_pivot : …⟨0⟩⟨0⟩ = 1`;
  `RmatGnorm_offpivot_le : |…a b| ≤ 1` on z∈[-1,1]^N (for (a,b)≠(0,0));
  `RmatGnorm_eq_slot (… a b) (hab : ¬(a=0∧b=0)) : RmatGnorm … z a b = z (slotMatG … a b)` — the cell→z readback.
- `schur_minorPivot_split {r p} (j) (j≤r)` : N2b — ∃ c₀ c₁>0, ∀ R S, [|R|≤1]→[pivot-max minor]→[detM11≠0]
   → ∃ Sc=(M22−M21 M11⁻¹ M12), c₀(frobSq((R·S)_top) + frobSq(Sc·S_bot)) ≤ frobSq(R·S) ≤ c₁(…). (j=1, top=row0.)
- `ofReal_rpow_le_const_mul (X F c₀ c') (0<c')(0<c₀)(0≤X)(0≤F)(c₀ X≤F)(X=0→F=0) :
   ofReal(F^{-c'}) ≤ ofReal(c₀^{-c'})·ofReal(X^{-c'})` — the inverse-power flip.
- `stepShearG (m) (b : Fin m→ℝ)(|b|≤1)(Sc)(T)(0<T)(c') :
   ∫_{S∈matBox(m+1) 4 T} ((∑_q (S 0 q + ∑_a b a·S a.succ q)²) + frobSq(Sc·(S∘succ)))^{-c'}
   ≤ ∫_{S_bot∈matBox m 4 T}∫_{T'∈morseBox 4 ((m+1)T)} ((∑ T'²) + frobSq(Sc·S_bot))^{-c'}` — top-row shear+peel-prep.
- `resolvedShiftRG_le (r)(hr)(Sh : Fin(r-1)→Fin(r-1)→ℝ)(B)(|Sh|≤B)(K)(0<K)(c')(2<c') :
   ∫_{Δ∈matBox(r-1)(r-1) K}∫_{S∈matBox(r-1) 4 K}∫_{T∈morseBox 4 K} ((∑T²)+frobSq((Δ-Sh)·S))^{-c'}
   ≤ ofReal(Cresid 4 c')·coreSchurGenVal (r-1) (c'-2) (K+B)` — the IH-invoking resolved bound.
   `coreSchurGenVal_lt_top` : it's < ⊤ for c'-2 < schurLambda(r-1).
- `cellOfG (m) : (Fin m×Fin m)⊕(Fin m⊕Fin m) → Fin(m+1)×Fin(m+1)` (inl(a,b)↦(a.succ,b.succ);
   inr(inl a)↦(a.succ,0); inr(inr b)↦(0,b.succ)); `cellOfG_injective`, `cellOfG_ne_zero`.
- `bgShiftG (m)(v : Fin m⊕Fin m→ℝ) : Matrix := fun a b => v(inl a)·v(inr b)`; `bgShiftG_entry_le (|v|≤1) : |·|≤1`.
- `schurResidG_translate_le` (Sh-uniform residual ≤ coreSchurGenVal); `frobSqShiftG_ne_zero_ae`,
  `core_T_peel_le_aeG`; the reshape primitives `matToProdG`/`coreJoinG`/`ae_eval_ne_zero_fintype` + their MP.
- `lintegral_translate_leG`, `matBox_rowperm_lintegralG`, `frobSq_rmatMul_permG`, `piRatioG_symm_apply`.

## What's NOT yet built (the gap = the sorry's content)
(i) the `zEG` MP reshape `(Fin N → ℝ) ≃ᵐ ((Fin(r-1)×Fin(r-1)→ℝ) × ((Fin(r-1)⊕Fin(r-1))→ℝ))` carving z
into the M22-cube ⊕ the (g,b)-cube, via the slot bijection from `cellOfG`+`slotMatG` (a `Fin N ≃ (M22⊕(g⊕b))`
through `finCongr hN` + `piFinSuccAbove`-style decode); (ii) the readback `Sc(z) = matOf(M22-cube) −
bgShiftG((g,b)-cube)` connecting the N2b Sc to the carved cubes via `RmatGnorm_eq_slot`; (iii) the assembly
chaining innerSGen_eq_norm → N2b → ofReal_rpow_le_const_mul → stepShearG → carve → resolvedShiftRG_le →
integrate-out-(g,b)-bounded-box.

## QUESTIONS (answer each, concrete Lean-level)
Q1. The `zEG` reshape: cleanest construction at v4.29? The slot bijection `Fin N ≃ (M22⊕(g⊕b))` — build it
    as `(Equiv.ofBijective (fun s => slotMatG-of-cellOf s) hbij).symm` (corank-3 zσ pattern, hbij via
    `Fintype.bijective_iff_injective_and_card` — injective from cellOfG_injective + slotMatG injective; card
    `(r-1)²+2(r-1) = N`)? Then `zEG := piCongrLeft (that) ≫ sumPiEquivProdPi`? Confirm the card step
    `Fintype.card ((Fin(r-1)×Fin(r-1))⊕(Fin(r-1)⊕Fin(r-1))) = N` is `by simp [hN]; ring`/`omega`-closable.
Q2. The readback (ii): I want `∫_z (resolved form at Sc(z)) = ∫_{(M22,gb)} (resolved at matOf M22 − bgShiftG gb)`.
    Is the cleanest route: rewrite `∫_z F(z) = ∫_{(M22,gb)} F(zEG.symm (M22,gb))` via the MP `zEG`, then per
    point show `Sc(zEG.symm(M22,gb)) = matOf M22 − bgShiftG gb` entrywise (using `RmatGnorm_eq_slot` +
    the slot bijection's defining `zEG.symm` readback + the N2b Sc-formula `= M22 − M21·M12` at M11=[1])?
    What's the lowest-friction way to prove that per-point Sc-readback given the N2b Sc is opaque (∃ from
    schur_minorPivot_split)? Should I instead AVOID the N2b ∃-Sc and use the EXPLICIT Sc-formula
    (M22 − M21·M11⁻¹·M12) directly so Sc is a closed expression in RmatGnorm cells, then RmatGnorm_eq_slot
    each cell? (The N2b lemma's first conjunct GIVES Sc = that explicit formula, so I can substitute.)
Q3. The assembly order: confirm the chain ∫_z innerSGen → [innerSGen_eq_norm] → [N2b lower-bound +
    ofReal_rpow_le_const_mul, pointwise under ∫_z∫_S] → [stepShearG turns frobSq(top) into the free T'
    Morse block, leaving ∫_{S_bot}∫_{T'}((∑T'²)+frobSq(Sc·S_bot))^{-c'}] → [carve ∫_z = ∫_{(M22,gb)},
    Sc=matOf M22 − bgShiftG gb] → [resolvedShiftRG_le per fixed gb, B=1, K=max 1 T] → [∫_gb bounded·const].
    Is this the right order, and is the `K = max 1 T` reconciliation (M22 box radius 1 from the ratio box,
    S_bot/T' box radius T) handled by resolvedShiftRG_le taking K and an S-box-enlarge, or do I need an
    extra S-monotone step? Flag the one trickiest gluing point.
Q4. Is closing this sorry from the banked lemmas pure plumbing (~80-120 lines), or is there a hidden gap
    (e.g. the N2b ∃-Sc opacity, the stepShearG top-block matching the N2b top = (R·S) row 0, the K-radius
    mismatch)? yes/no + the smallest sharp statement of any gap.
</task>
<output_contract>
Answer Q1–Q4 concretely (Lean-level, name the lemmas/tactics). For Q2 pick explicit-Sc-formula vs ∃-Sc.
End with: "ASSEMBLY: <PURE-PLUMBING | GAP-AT-<step>>" and "READBACK-VIA: <explicit-formula | ∃-Sc>".
</output_contract>
<grounding_rules>
Mark Mathlib names CONFIRMED only if sure at v4.29, else INFERRED. Distinguish a fact you're confident of
from a tactic guess.
</grounding_rules>
