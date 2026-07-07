<task>
Lean 4 + Mathlib v4.29. I am closing the sole L=2 headline crux `d1ge_L2_hAtV_explicit` by feeding a
banked consumer. All analytic content is banked; the remaining work is a coordinate/measure reindex
("plumbing"). I want your read on the LEANEST construction of the central index-equiv and its
readbacks, plus pitfalls, BEFORE I write ~400 lines.

## The banked germ (given, sorry-free)
`schur_loss_germ_L2_rlct` produces injective pivots `I : Fin r → Fin (H 0)`, `K : Fin r → Fin (H 1)`,
`J : Fin r → Fin (H 2)` and:

    rlctAt H (dlnLoss H B) v = rlctAtOn (schurReadoutF_L2 … C₀ Br₀) (0 : Fin (flatDim H) → ℝ)

where (all in `Fin (flatDim H) → ℝ` = flat parameter space; `b := blockFlatEquiv_L2 H r I K J … : (Fin (flatDim H) → ℝ) ≃L[ℝ] BlockParamsL2 H r`, a CONTINUOUS LINEAR equiv):
- `schurReadoutF_L2 … C Br x = ∑_{a : Fin r ⊕ Fin(H0-r)} ∑_{bb : Fin r ⊕ Fin(H2-r)} ((recoverProduct H r (b x + C) - Br) a bb)^2`
- `recoverProduct H r Q = fromBlocks (Q.2.toBlocks₁₁) (Q.2.toBlocks₁₂) (Q.1.toBlocks₂₁) (Q.1.toBlocks₂₁ * Q.2.toBlocks₁₁⁻¹ * Q.2.toBlocks₁₂ + Q.1.toBlocks₂₂ * Q.2.toBlocks₂₂)`
  i.e. block₁₁=M11, ₁₂=M12, ₂₁=M21, ₂₂ = M21·M11⁻¹·M12 + A0red·A1red.
- `C₀ = schurChartRaw H r (b (paramsEquivFlat H v))`, `Br₀ = B.submatrix (sumSplit I hI)(sumSplit J hJ)`.
- At the base pt x=0: b·0 = 0, recoverProduct(C₀) = (prod v).submatrix(...) = B.submatrix(...) = Br₀ (prod v=B), so F(0)=0.

`blockFlatEquiv_L2` readbacks (proved): `(b x).1 a b = ((paramsEquivFlatLinear H).symm x 0) (sumSplit I hI a) (sumSplit K hK b)` and `(b x).2 a b = ((paramsEquivFlatLinear H).symm x 1) (sumSplit K hK a) (sumSplit J hJ b)`.
Flat structure: `paramsEquivFlat H = piCurry.symm ∘ piCurry.symm ∘ arrowCongr'(Fintype.equivFin (FlatIdx H))`; `FlatIdx H = Σ (⟨s,i⟩ : Σ s:Fin L, Fin(H s.castSucc)), Fin(H s.succ)`; `(paramsEquivFlat H).symm x s i j = x (Fintype.equivFin (FlatIdx H) ⟨⟨s,i⟩,j⟩)`. `sumSplit σ hσ : Fin r ⊕ Fin(n-r) ≃ Fin n`, `sumSplit σ hσ (inl a) = σ a`.

## The banked consumer (given, sorry-free) — I must produce its hypotheses
`d1ge_L2_hAtV_of_explicit_chart {n specDim : ℕ} {Y} [Normed/Measure/Borel/FinDim/Proper/FiniteMeasOnCompacts Y]
    (H r B v) (qₑ : (Fin (nRegL2 H r) → ℝ) × Y → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 1 qₑ) (t0 : Y)
    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn (fun p => (∑ i, p.1 i^2) + (∑ i, qₑ p i^2)) ((0:Fin nReg→ℝ), t0))
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U), (∑ i, qₑ ((0:Fin nReg→ℝ), z) i^2) ≠ 0)
    (e : Y ≃ₜ ((Fin (flatDim (H-r)) → ℝ) × (Fin specDim → ℝ))) (he_mp : MeasurePreserving e) (he_emb : MeasurableEmbedding e)
    (u : Y → ℝ) (hu_meas) (ua ub) (hua : 0<ua) (hu_bnd : ∃ U∈𝓝 t0, ∀ w∈U, ua≤|u w| ∧ |u w|≤ub)
    (hfact : ∀ t:Y, (∑ i, qₑ ((0:Fin nReg→ℝ), t) i^2) = u t * dlnLoss (H-r) 0 ((paramsEquivFlat (H-r)).symm (e t).1))
  : ∃ P, (nRegL2 H r)/2 + rlctAtOn (dlnLoss (H-r) 0) P ≤ rlctAt H (dlnLoss H B) v`
`nRegL2 H r = r*(H0+H2-r)`. `dlnLoss (H-r) 0 A = ‖prod (H-r) A‖² = ∑∑ (prod A)²` (L=2: `prod = A0*A1`).

## The plan (brief-scoped, Option A: e picks up the C-shift, u≡1)
Set Y := (Fin (flatDim (H-r)) → ℝ) × (Fin specDim → ℝ). `specDim := flatDim H - nRegL2 H r - flatDim (H-r)` (need: nReg + flatDim(H-r) + specDim = flatDim H; the coordinate partition proves it).
Central object: an index equiv `e_idx : Fin nReg ⊕ (Fin (flatDim (H-r)) ⊕ Fin specDim) ≃ Fin (flatDim H)` aligned to `b`'s coordinate assignment, feeding `CoreSplitMP.splitOfPartition e_idx : (Fin (flatDim H) → ℝ) ≃ᵐ (Fin nReg → ℝ) × ((Fin (flatDim(H-r))→ℝ) × (Fin specDim→ℝ))` (measure-preserving, banked; readbacks `(split u).1 i = u (e_idx (inl i))`, `.2.1 j = u (e_idx (inr (inl j)))`, `.2.2 k = u (e_idx (inr(inr k)))`).
Coordinate classification per layer/block (sumSplit ₁₁=inl/inl,₁₂=inl/inr,₂₁=inr/inl,₂₂=inr/inr):
- REGULAR (nReg): L0.₂₁ (M21), L1.₁₁ (M11), L1.₁₂ (M12).
- CORE (flatDim(H-r)): L0.₂₂ (W'), L1.₂₂ (V') — these ARE exactly the two (H-r) layers, dims (H0-r)×(H1-r) and (H1-r)×(H2-r).
- SPEC (specDim): L0.₁₁ (X), L0.₁₂ (Y), L1.₂₁ (Uu).
Requirement forcing the alignment: `(split e_idx x).2.1 = paramsEquivFlat (H-r) (W'(x), V'(x))` where W'(x)=(b x).1.toBlocks₂₂, V'(x)=(b x).2.toBlocks₂₂ — so the core block map is `FlatIdx(H-r) → FlatIdx H`, `⟨⟨0,a⟩,b'⟩ ↦ ⟨⟨0, sumSplit I(inr a)⟩, sumSplit K(inr b')⟩`, `⟨⟨1,a⟩,b'⟩ ↦ ⟨⟨1, sumSplit K(inr a)⟩, sumSplit J(inr b')⟩`, conjugated by `Fintype.equivFin`. Then translation on Y's core factor by `coreShift := paramsEquivFlat(H-r)(A0red(P₀),A1red(P₀))` lands `(e t).1` at `(W'+A0red₀, V'+A1red₀)` = the reduced factors (`hfact`), with `qₑ(0,t)` = the ₂₂ residual which on the slice collapses (Schur cplt of Br₀ rank≤r = 0) to A0red·A1red = (W'+c₀)(V'+c₁). `qₑ` global-`ContDiff` uses banked bump-`G` for M11⁻¹.
`hchart`: `rlctAtOn F 0 = rlctAtOn (F ∘ κ.symm) (κ 0)` via `rlctAtOn_comp_homeomorph` (κ = split∘translation, MP+homeo), then `rlctAtOn_congr_germ` to rewrite `F∘κ.symm` into `∑p²+∑qₑ²` near κ 0=(0,t0).
`hRne` from banked `dlnLoss_deepest_core_ae_ne_zero` (a.e.≠0, under hpos ∀s r<H s).
</task>

<output_contract>
Answer these, concisely, in order:
1. Is the coordinate CLASSIFICATION (reg/core/spec block lists) correct, i.e. does F depend on exactly {L0.₂₁, L1.₁₁, L1.₁₂} (reg) ∪ {L0.₂₂, L1.₂₂} (core) and NOT on {L0.₁₁, L0.₁₂, L1.₂₁} (spec)? Any error?
2. LEANEST way to BUILD `e_idx` as an `Equiv` (over Fin (flatDim H)) with the three readbacks provable. Options: (a) build a bijection `FlatIdx H ≃ (regIdx) ⊕ (FlatIdx (H-r)) ⊕ (specIdx)` per-layer/per-block then compose with equivFin's; (b) build three explicit injections `Fin nReg / FlatIdx(H-r) / specIdx ↪ Fin(flatDim H)` with disjoint covering images and glue via a card/`Equiv.ofBijective`; (c) other. Which minimizes Fin/Sigma/equivFin thrash? Give the concrete Mathlib equivs.
3. Do I actually NEED the core-block to equal `paramsEquivFlat(H-r)(W',V')` on the nose, or can I choose `qₑ` to absorb the (H-r) flat decode so `e = refl`-ish and `(e t).1 = t.1` feeds `dlnLoss(H-r) 0 (decode t.1)` directly — sidestepping the FlatIdx(H-r)→FlatIdx H alignment? Concretely: can `qₑ(0,t) := entries of prod(H-r)((paramsEquivFlat(H-r)).symm(t.1 + coreShift))`, decoupled from F's ₂₂ residual, IF I prove `F∘κ.symm =ᶠ ∑p²+∑qₑ²` near base? Which is leaner?
4. The `hchart` germ step: after `rlctAtOn_comp_homeomorph`, I must show `F(κ.symm(p,t)) =ᶠ[𝓝 (0,t0)] (∑ p_i²) + (∑ qₑ(p,t)²)`. Is the cleanest to (i) split F's block sum into reg (3 blocks → ∑p²) + ₂₂ (→∑qₑ²), matching entrywise via the readbacks + translation, with the M11⁻¹→bump-G swap valid only near base (hence `=ᶠ`)? Any trap in Euclidean vs Pi norm for qₑ's `∑ i, qₑ p i^2` codomain `EuclideanSpace ℝ (Fin n)`, n=(H0-r)(H2-r)?
5. Top 3 pitfalls / where I'll thrash, with the pre-emptive fix.
</output_contract>

<grounding_rules>
Flag any step you think is FALSE or where the plan has a real gap (not just Lean-mechanical). Distinguish "mechanical friction" from "mathematical/architectural error". If classification in (1) is wrong the whole plan fails — check it hardest. Do not invent Mathlib lemma names without flagging them as to-verify.
</grounding_rules>
