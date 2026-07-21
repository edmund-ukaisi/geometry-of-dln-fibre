import DLNFibre.Core.Aoyagi.BlockBlowup

/-!
# `Core.Aoyagi.BlockDivision` — exact division by the pivot after a block-center blow-up

The δ-agnostic algebraic heart of the coupled Case-1 witness law `q' = (φ*q)/u_p^δ`
(`Core.Aoyagi.PrincipalInv`, thread-34 certificate; SEAT-L4). After the block-center blow-up
`blockBlowupMap S p` (`Core.Aoyagi.BlockBlowup`), every CENTER coordinate `j ∈ S` pulls back to
`w_p · c_j(w)` with `c_j` a polynomial (`= 1` at the pivot, `= w_j` on the other center members) —
an EXACT division by the pivot coordinate `w ↦ w p`, no localization. SPECTATORS (`j ∉ S`) are
unchanged and do NOT gain the factor (elder W2: the exceptional locus is the pivot hyperplane, and
only center coordinates cross it). Any center-supported combination inherits the factor
(`blockBlowup_center_comb_eq`) — this is the witness-law division at the residual level: a residual
whose entries are center coordinates pulls back with a clean `w_p` factor, so the child quotient
`∑ (q∘σ)·quot` is the EXACT `/u_p` of `q' = (φ*q)/u_p`, no localization, continuous.

Reusable, δ-agnostic (the exponent `δ` is applied downstream in the leaf, per edge-spec — the
DIVISION itself is a single factor, applied `δ`-many times); binds to the banked `blockBlowupMap`.
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D : ℕ}

/-- The exact quotient of a pulled-back CENTER coordinate by the pivot: `1` at the pivot, the bare
coordinate `w ↦ w j` on the other center members. Pins the exact division
`(blockBlowupMap S p w) j = w p * blockBlowupCoordQuot p j w` for `j ∈ S`. -/
def blockBlowupCoordQuot (p : Fin D) (j : Fin D) : (Fin D → ℝ) → ℝ :=
  fun w ↦ if j = p then 1 else w j

/-- **The exact division (center coordinate).** For a center member `j ∈ S`, the pulled-back
coordinate factors as `w_p · quot`, EXACTLY (polynomial quotient, no localization). -/
theorem blockBlowupMap_center_eq (S : Finset (Fin D)) (p : Fin D) {j : Fin D} (hj : j ∈ S)
    (w : Fin D → ℝ) :
    blockBlowupMap S p w j = w p * blockBlowupCoordQuot p j w := by
  unfold blockBlowupMap blockBlowupCoordQuot
  by_cases hjp : j = p
  · simp [hjp]
  · simp [hjp, hj]

/-- **Spectators are unchanged** (elder W2): a non-center coordinate does NOT gain the pivot factor,
so the pivot hyperplane `{w_p = 0}` is exactly the center-block exceptional locus. -/
theorem blockBlowupMap_spectator_eq (S : Finset (Fin D)) {p : Fin D} (hp : p ∈ S) {j : Fin D}
    (hj : j ∉ S) (w : Fin D → ℝ) :
    blockBlowupMap S p w j = w j := by
  have hjp : j ≠ p := fun h ↦ hj (h ▸ hp)
  unfold blockBlowupMap
  simp [hjp, hj]

/-- The exact quotient is continuous. -/
theorem continuous_blockBlowupCoordQuot (p j : Fin D) :
    Continuous (blockBlowupCoordQuot p j) := by
  by_cases hjp : j = p
  · have h : blockBlowupCoordQuot p j = fun _ : Fin D → ℝ ↦ (1 : ℝ) := by
      funext w; simp [blockBlowupCoordQuot, hjp]
    rw [h]; exact continuous_const
  · have h : blockBlowupCoordQuot p j = fun w : Fin D → ℝ ↦ w j := by
      funext w; simp [blockBlowupCoordQuot, hjp]
    rw [h]; exact continuous_apply j

/-- The exact quotient is analytic on the whole space (a coordinate / constant). -/
theorem analyticOnNhd_blockBlowupCoordQuot (p j : Fin D) :
    AnalyticOnNhd ℝ (blockBlowupCoordQuot p j) Set.univ := by
  by_cases hjp : j = p
  · have h : blockBlowupCoordQuot p j = fun _ : Fin D → ℝ ↦ (1 : ℝ) := by
      funext w; simp [blockBlowupCoordQuot, hjp]
    rw [h]; exact analyticOnNhd_const
  · have h : blockBlowupCoordQuot p j = fun w : Fin D → ℝ ↦ w j := by
      funext w; simp [blockBlowupCoordQuot, hjp]
    rw [h]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin D ↦ ℝ) j).analyticOnNhd _

/-- **The witness-law division (center-supported combination — the residual level).** A residual
entry that is a combination `∑ a, cₐ · (center coordinate kₐ)` of center coordinates (`kₐ ∈ S`)
pulls back, after `σ = blockBlowupMap S p`, to `w_p · (∑ a, (cₐ∘σ)·quot(kₐ))` — the EXACT `/u_p`
division of the witness law, no localization. The quotient `∑ a, (cₐ∘σ)·quot(kₐ)` is what the child
`StepInv`'s quotient becomes (continuous when the `cₐ` are). -/
theorem blockBlowup_center_comb_eq {n : ℕ} (S : Finset (Fin D)) (p : Fin D)
    (c : Fin n → (Fin D → ℝ) → ℝ) (k : Fin n → Fin D) (hk : ∀ a, k a ∈ S) (w : Fin D → ℝ) :
    (∑ a, c a (blockBlowupMap S p w) * (blockBlowupMap S p w) (k a))
      = w p * ∑ a, c a (blockBlowupMap S p w) * blockBlowupCoordQuot p (k a) w := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  rw [blockBlowupMap_center_eq S p (hk a)]
  ring

/-- **Continuity of the divided-residual quotient** — the child `StepInv` quotient
`∑ a, (cₐ∘σ)·quot(kₐ)` is `ContinuousOn` the child region when the coefficients `cₐ` are
`ContinuousOn` the parent region `V` and `σ = blockBlowupMap S p` maps the child region into `V`.
This is the continuity half the child `StepInv` needs (`q'` `ContinuousOn`); with
`blockBlowup_center_comb_eq` it delivers the full δ=1 child divisibility for a residual pinned to a
center-coordinate combination. -/
theorem continuousOn_blockBlowup_center_quot {n : ℕ} (S : Finset (Fin D)) (p : Fin D)
    (c : Fin n → (Fin D → ℝ) → ℝ) (k : Fin n → Fin D) {V W : Set (Fin D → ℝ)}
    (hc : ∀ a, ContinuousOn (c a) V) (hmaps : Set.MapsTo (blockBlowupMap S p) W V) :
    ContinuousOn
      (fun w ↦ ∑ a, c a (blockBlowupMap S p w) * blockBlowupCoordQuot p (k a) w) W := by
  refine continuousOn_finset_sum _ (fun a _ ↦ ?_)
  exact ((hc a).comp (continuous_blockBlowupMap S p).continuousOn hmaps).mul
    (continuous_blockBlowupCoordQuot p (k a)).continuousOn

/-! ## FIX-A: blow-up OUTERMOST composed with a pivot-KEEPING shear (elder ruling, 2026-07-21)

The step map is `stepMap = blockBlowupMap S p ∘ sh` (blow-up outermost, thread-34's order), with the
shear `sh` KEEPING the pivot (`sh u p = u p`, `hsh_pivot`). Then the exact `u_p` factor of every
center coordinate is STRUCTURAL — for ANY such shear — since the pivot factor comes from the OUTER
blow-up on the already-sheared point, untouched by the (pivot-keeping) shear. This is the δ-agnostic
enabler of the elder's FIX-A + FIX-RESID: the strict-transform residual `(resid∘stepMap)/u_p` is the
`blockBlowupCoordQuot` combination, continuous, no localization. -/

/-- **FIX-A center division** — blow-up outermost ∘ a pivot-keeping shear: for `j ∈ S`,
`blockBlowupMap S p (sh u) j = u_p · blockBlowupCoordQuot p j (sh u)`, EXACTLY, for ANY `sh` with
`sh u p = u p`. (The pivot factor is structural — one line from `blockBlowupMap_center_eq`.) -/
theorem blockBlowupMap_shear_center_eq (S : Finset (Fin D)) (p : Fin D) {j : Fin D} (hj : j ∈ S)
    (sh : (Fin D → ℝ) → (Fin D → ℝ)) (hsh_pivot : ∀ u, sh u p = u p) (u : Fin D → ℝ) :
    blockBlowupMap S p (sh u) j = u p * blockBlowupCoordQuot p j (sh u) := by
  rw [blockBlowupMap_center_eq S p hj (sh u), hsh_pivot u]

/-- **FIX-A residual division** (the strict transform at the residual level) — a center-supported
residual `∑ a, cₐ·(coord kₐ)` (`kₐ ∈ S`) pulls back through `blockBlowupMap S p ∘ sh` (blow-up
outermost, `sh` pivot-keeping) to `u_p · (∑ a, cₐ·quot(kₐ))∘(sh)` — the EXACT `/u_p` division for
the strict-transform child residual, for ANY pivot-keeping shear (the elder's FIX-A). -/
theorem blockBlowup_shear_center_comb_eq {n : ℕ} (S : Finset (Fin D)) (p : Fin D)
    (c : Fin n → (Fin D → ℝ) → ℝ) (k : Fin n → Fin D) (hk : ∀ a, k a ∈ S)
    (sh : (Fin D → ℝ) → (Fin D → ℝ)) (hsh_pivot : ∀ u, sh u p = u p) (u : Fin D → ℝ) :
    (∑ a, c a (blockBlowupMap S p (sh u)) * blockBlowupMap S p (sh u) (k a))
      = u p * ∑ a, c a (blockBlowupMap S p (sh u)) * blockBlowupCoordQuot p (k a) (sh u) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  rw [blockBlowupMap_shear_center_eq S p (hk a) sh hsh_pivot]
  ring

end DLNFibre.Core.Aoyagi
