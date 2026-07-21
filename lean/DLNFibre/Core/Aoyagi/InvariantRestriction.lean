import DLNFibre.Core.Aoyagi.PrincipalInv
import Meta.Cordon

/-!
# `Core.Aoyagi.InvariantRestriction` — M2: restriction (monotonicity) API for the fold invariants

**API (aoyagi-engine monument wave, SEAT-API / owed-register M2).** The three `.mono` lemmas that
let a consumer restrict a landed invariant from a region `V` to a subregion `V' ⊆ V` without
re-proving it inline. The monument's wiring needs exactly this: `terminal_bezout` produces its
`PrincipalInv` on a SHRUNK open `V' ⊆ V`, and L6 then consumes `StepInv`/`SupportedOn` on that same
shrunk region — so every consumer would otherwise re-derive restriction by hand.

## The weakest hypothesis is `V' ⊆ V` alone

Each of `StepInv`, `PrincipalInv`, `SupportedOn` reads its region `V` only through `ContinuousOn … V`
clauses and `∀ u ∈ V, …` clauses; restriction of both is monotone in the region
(`ContinuousOn.mono`, subset membership). `StepInv` additionally carries the deepest-point vanishing
`(Fᵢ∘g) 0 = 0`, but that clause has **no `V`-dependence at all** — so restriction preserves it
trivially and, in particular, `.mono` needs **no** `0 ∈ V'` side condition. The single hypothesis is
`V' ⊆ V`.
-/

open Set

namespace DLNFibre.Core.Aoyagi

variable {M D : ℕ}

/-- **`StepInv` restricts to a subregion.** For `V' ⊆ V`, the interior step invariant on `V` holds
on `V'`: the quotient continuities restrict (`ContinuousOn.mono`), the pulled-back factorisation
holds on the smaller region, and the deepest-point vanishing `(Fᵢ∘g) 0 = 0` is `V`-independent
(carried unchanged — no `0 ∈ V'` needed). -/
theorem StepInv.mono {F : Fin M → (Fin D → ℝ) → ℝ} {g : (Fin D → ℝ) → (Fin D → ℝ)}
    {b : (Fin D → ℝ) → ℝ} {nR : ℕ} {resid : Fin nR → (Fin D → ℝ) → ℝ}
    {q : Fin M → Fin nR → (Fin D → ℝ) → ℝ} {V V' : Set (Fin D → ℝ)}
    (h : StepInv F g b resid q V) (hsub : V' ⊆ V) :
    StepInv F g b resid q V' := by
  obtain ⟨hq, h0, heq⟩ := h
  exact ⟨fun i j ↦ (hq i j).mono hsub, h0, fun u hu i ↦ heq u (hsub hu) i⟩

/-- **`PrincipalInv` restricts to a subregion.** For `V' ⊆ V`, the terminal principal invariant on
`V` holds on `V'`: both the divisibility quotients `q` and the Bézout coefficients `r` restrict
their continuity (`ContinuousOn.mono`), and both pointwise identities hold on the smaller region.
This is the form `terminal_bezout`'s consumers use — its conclusion lives on a shrunk open
`V' ⊆ V`. -/
theorem PrincipalInv.mono {F : Fin M → (Fin D → ℝ) → ℝ} {g : (Fin D → ℝ) → (Fin D → ℝ)}
    {b : (Fin D → ℝ) → ℝ} {q r : Fin M → (Fin D → ℝ) → ℝ} {V V' : Set (Fin D → ℝ)}
    (h : PrincipalInv F g b q r V) (hsub : V' ⊆ V) :
    PrincipalInv F g b q r V' := by
  obtain ⟨hq, hr, hdiv, hbez⟩ := h
  exact ⟨fun i ↦ (hq i).mono hsub, fun i ↦ (hr i).mono hsub,
    fun u hu i ↦ hdiv u (hsub hu) i, fun u hu ↦ hbez u (hsub hu)⟩

/-- **`SupportedOn` restricts to a subregion.** For `V' ⊆ V`, the center-support (ideal-membership)
witness on `V` holds on `V'`: the same coefficient functions `c` witness the support, their
continuity restricts (`ContinuousOn.mono`), and each residual entry's center-coordinate expansion
holds on the smaller region. -/
theorem SupportedOn.mono {nR : ℕ} {resid : Fin nR → (Fin D → ℝ) → ℝ} {S : Finset (Fin D)}
    {V V' : Set (Fin D → ℝ)} (h : SupportedOn resid S V) (hsub : V' ⊆ V) :
    SupportedOn resid S V' := by
  obtain ⟨c, hc, heq⟩ := h
  exact ⟨c, fun j i ↦ (hc j i).mono hsub, fun j u hu ↦ heq j u (hsub hu)⟩

/-! ## Kill-set — each `.mono` exercised on a concrete non-trivial shrink `ball 0 1 ⊆ univ` -/

/-- `StepInv.mono` on a concrete instance (`F` = the `u₀`-projection, `g = id`, `b ≡ 1`,
`resid = u₀`, `q ≡ 1`) restricted from `univ` to the unit ball. The invariant is non-degenerate: the
factorisation `u₀ = 1·(1·u₀)` and the deepest-point vanishing `(u₀∘id) 0 = 0` both hold. -/
example :
    StepInv (M := 1) (D := 1) (fun _ u ↦ u 0) id (fun _ ↦ 1) (nR := 1) (fun _ u ↦ u 0)
      (fun _ _ _ ↦ (1 : ℝ)) (Metric.ball 0 1) := by
  have h : StepInv (M := 1) (D := 1) (fun _ u ↦ u 0) id (fun _ ↦ 1) (nR := 1) (fun _ u ↦ u 0)
      (fun _ _ _ ↦ (1 : ℝ)) Set.univ :=
    ⟨fun _ _ ↦ continuousOn_const, fun _ ↦ by simp, fun u _ _ ↦ by simp⟩
  exact h.mono (Set.subset_univ _)

/-- `PrincipalInv.mono` on a concrete instance (`F = g = u₀`-projection, `b = u₀`, `q = r ≡ 1`)
restricted from `univ` to the unit ball. Both the divisibility `u₀ = 1·u₀` and the Bézout
`u₀ = ∑ 1·u₀` hold genuinely. -/
example :
    PrincipalInv (M := 1) (D := 1) (fun _ u ↦ u 0) id (fun u ↦ u 0)
      (fun _ _ ↦ 1) (fun _ _ ↦ 1) (Metric.ball 0 1) := by
  have h : PrincipalInv (M := 1) (D := 1) (fun _ u ↦ u 0) id (fun u ↦ u 0)
      (fun _ _ ↦ 1) (fun _ _ ↦ 1) Set.univ :=
    ⟨fun _ ↦ continuousOn_const, fun _ ↦ continuousOn_const,
      fun u _ _ ↦ by simp, fun u _ ↦ by simp⟩
  exact h.mono (Set.subset_univ _)

/-- `SupportedOn.mono` on a concrete instance (`resid = u₀` supported on the center `{0} ⊆ Fin 2` by
`c ≡ 1`) restricted from `univ` to the unit ball. The support expansion `u₀ = ∑_{i∈{0}} 1·uᵢ` holds
genuinely, and `{0}` is a proper (single-coordinate) center of the two-dimensional ambient. -/
example :
    SupportedOn (D := 2) (nR := 1) (fun _ u ↦ u 0) {0} (Metric.ball 0 1) := by
  have h : SupportedOn (D := 2) (nR := 1) (fun _ u ↦ u 0) {0} Set.univ :=
    ⟨fun _ _ _ ↦ 1, fun _ _ ↦ continuousOn_const, fun _ u _ ↦ by simp⟩
  exact h.mono (Set.subset_univ _)

end DLNFibre.Core.Aoyagi
