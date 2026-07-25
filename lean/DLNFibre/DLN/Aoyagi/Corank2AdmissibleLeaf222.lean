import DLNFibre.Core.Aoyagi.PrincipalInv
import DLNFibre.DLN.Aoyagi.LeafCoverTiling

/-!
# `(2,2,2)`-leaf probe — TERMINAL-SHRINK ⋈ COVER (the admissible leaf region)

The pivotal R3 de-risk (reroute R3-derisk, `geometry-invariant-elaboration.md` §Residual R1, ranked
HIGHEST by the seat + Codex independently). `terminal_bezout` (`PrincipalInv.lean:318`) BORNS the
terminal `PrincipalInv` on a **shrunk** open neighbourhood `V' = V ∩ {unit ≠ 0}` (the cleared-pivot
factor must be non-vanishing to invert `b = unit⁻¹·(F i₀∘g)`); the cover fold
(`LeafCoverTiling.Covers`/`covers_subset`) needs each leaf's source box `closedBall 0 R` to sit
*inside* the leaf's certified region. These two must hold **on one chart**: the ideal thread wants a
small `V'`, the cover thread wants a box big enough to tile. The gate: can they conjoin at the
`(2,2,2)` terminal leaf, or does the cover force a radius beyond the non-vanishing region?

**Verdict: GREEN.** The cover box floor is genuine — the block blow-up argmax lift needs source
radius `max R 1 ≥ 1` (ratios in `[-1,1]`), so the leaf box is radius `≥ 1` even to cover an
arbitrarily small target ball (`LeafCoverTiling.closedBall_subset_iUnion_blockBlowup_image_radius`).
The tension it would create with a shrunk `V'` **dissolves** because at the real resolution leaves
the cleared-pivot factor is `unit ≡ 1`: the eliminations are unipotent (`det ≡ 1`) and the blow-ups
exact-monomial, so `|jacDet| = jacWeight` with unit `1` (`chart_of_collapse`'s `unit := fun _ ↦ 1`,
`PrincipalInv.lean`'s `pathMap` docstring, the `(3,3,4)` `cert_334` "pivot strict-transform ≡ 1").
Under `unit ≡ 1`, `terminal_bezout`'s shrink is **vacuous** (`V' = V`), so the cover box of ANY
radius `R` with `closedBall 0 R ⊆ V` sits inside `V'` — conjoined with the `Covers` leaf-clause on
the same region. The `ρ`-compatibility: unit `≡ 1 ⇒ ρ` unconstrained by the shrink (any `R ⊆ V`
works); the merely-continuous case (`unit 0 ≠ 0`) still yields *some* `ρ > 0` but the `≥ 1` cover
floor then needs `unit` non-vanishing on `closedBall 0 1` — which the real-leaf collapse provides.

**API note for R3:** `terminal_bezout` returns `V'` *opaquely* (only `IsOpen V' ∧ 0 ∈ V' ∧ V' ⊆ V`),
so from its current statement one can derive only "∃ ρ > 0, closedBall 0 ρ ⊆ V'"
(`terminal_bezout_cover_ball`) — NOT the full-radius box, even when `unit ≡ 1`. To consume the
collapse the deep build wants the exposed form `terminal_bezout_collapse` below (PrincipalInv on the
FULL `V`), or `terminal_bezout` refined to return `V' = V ∩ {unit ≠ 0}` explicitly.

## Main results
- `exists_cover_ball_of_open` — any open `V' ∋ 0` contains a positive-radius closed cover box.
- `terminal_bezout_cover_ball` — consuming the REAL `terminal_bezout`: its output `V'` always admits
  a cover ball `∃ ρ > 0, closedBall 0 ρ ⊆ V'` (the general "a non-vanishing ball exists").
- `terminal_region_eq_of_collapse` — under `unit ≡ 1` the shrink is vacuous: `V ∩ {unit ≠ 0} = V`.
- `terminal_bezout_collapse` — the API-clean collapse variant: `unit ≡ 1 ⇒ PrincipalInv` on the FULL
  `V` (no shrink), consuming `StepInv`.
- `admissible_leaf_region_222` — THE GATE at the `(2,2,2)` source dimension
  (`flatDim ![2,2,2] = 8`): the terminal region contains the cover box of radius `R` AND satisfies
  the `Covers` leaf-clause, on the same region.
-/

open Metric Set

namespace DLNFibre.DLN.Aoyagi.Corank2AdmissibleLeaf222

open DLNFibre.Core.Aoyagi DLNFibre.DLN.Aoyagi.LeafCoverTiling

variable {D : ℕ}

/-- **An open neighbourhood of `0` contains a positive-radius closed cover box.** The elementary
topological fact behind "a non-vanishing ball exists": `V'` open `∋ 0` gives
`∃ ρ > 0, closedBall 0 ρ ⊆ V'` (take `ρ = ε/2` for the metric ball `ball 0 ε ⊆ V'`). -/
theorem exists_cover_ball_of_open {V' : Set (Fin D → ℝ)}
    (hopen : IsOpen V') (h0 : (0 : Fin D → ℝ) ∈ V') :
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall 0 ρ ⊆ V' := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds h0)
  exact ⟨ε / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩

/-- **The general enabling fact, consuming the REAL `terminal_bezout`.** The terminal principal
invariant is BORN on a shrunk open `V' ∋ 0`; that `V'` therefore always admits a positive-radius
cover box. This is all the *current* (opaque-`V'`) `terminal_bezout` statement can deliver — the `ρ`
is some positive radius, not yet the `≥ 1` the inflate-boxes cover fold wants (see the collapse
variant and the module note). -/
theorem terminal_bezout_cover_ball {M : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ}
    {g : (Fin D → ℝ) → (Fin D → ℝ)} {b : (Fin D → ℝ) → ℝ}
    {q : Fin M → Fin 1 → (Fin D → ℝ) → ℝ} {V : Set (Fin D → ℝ)}
    (hV : IsOpen V) (hV0 : (0 : Fin D → ℝ) ∈ V)
    (hstep : StepInv F g b (fun _ : Fin 1 ↦ 1) q V) (i₀ : Fin M) (unit : (Fin D → ℝ) → ℝ)
    (hc : ContinuousOn unit V) (h0 : unit 0 ≠ 0) (heq : ∀ u ∈ V, (F i₀ ∘ g) u = b u * unit u) :
    ∃ (V' : Set (Fin D → ℝ)) (r : Fin M → (Fin D → ℝ) → ℝ) (ρ : ℝ),
      IsOpen V' ∧ (0 : Fin D → ℝ) ∈ V' ∧ V' ⊆ V ∧ 0 < ρ ∧ closedBall 0 ρ ⊆ V' ∧
        PrincipalInv F g b (fun i ↦ q i 0) r V' := by
  obtain ⟨V', r, hopen, hmem, hsub, hP⟩ := terminal_bezout hV hV0 hstep i₀ unit hc h0 heq
  obtain ⟨ρ, hρ, hball⟩ := exists_cover_ball_of_open hopen hmem
  exact ⟨V', r, ρ, hopen, hmem, hsub, hρ, hball, hP⟩

/-- **The shrink is vacuous under the real-leaf collapse `unit ≡ 1`.** `terminal_bezout` shrinks `V`
to `V ∩ {unit ≠ 0}`; when the cleared-pivot factor is identically `1`, that intersection is `V`
itself. This is the fact that dissolves the terminal-shrink ⋈ cover tension. -/
theorem terminal_region_eq_of_collapse (V : Set (Fin D → ℝ)) (unit : (Fin D → ℝ) → ℝ)
    (hcollapse : ∀ u, unit u = 1) :
    V ∩ {u | unit u ≠ 0} = V := by
  ext u
  simp [hcollapse]

/-- **The API-clean collapse variant of `terminal_bezout`.** Under the real-leaf collapse — the
cleared pivot is `(F i₀∘g) = b` on `V` (i.e. `unit ≡ 1`) — the terminal `PrincipalInv` holds on the
FULL `V`, with NO shrink: divisibility from `StepInv`'s `Fin 1` residual collapse, and Bézout with
the constant coefficient `r = 𝟙[i = i₀]` (continuous everywhere, no `unit⁻¹`). This is the exposed
form the R3 deep build consumes to marry the terminal leaf's certificate region to the cover box. -/
theorem terminal_bezout_collapse {M : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ}
    {g : (Fin D → ℝ) → (Fin D → ℝ)} {b : (Fin D → ℝ) → ℝ}
    {q : Fin M → Fin 1 → (Fin D → ℝ) → ℝ} {V : Set (Fin D → ℝ)}
    (hstep : StepInv F g b (fun _ : Fin 1 ↦ 1) q V) (i₀ : Fin M)
    (hunit : ∀ u ∈ V, (F i₀ ∘ g) u = b u) :
    PrincipalInv F g b (fun i ↦ q i 0) (fun i ↦ fun _ ↦ if i = i₀ then (1 : ℝ) else 0) V := by
  obtain ⟨hqc, _hz, hdiv⟩ := hstep
  refine ⟨fun i ↦ hqc i 0, fun i ↦ ?_, fun u hu i ↦ ?_, fun u hu ↦ ?_⟩
  · -- Bézout coefficients are constants (`1` or `0`) in `u`, continuous on `V`
    exact continuousOn_const
  · -- divisibility: the `Fin 1` residual sum collapses (`resid ≡ 1`)
    have hd := hdiv u hu i
    simpa only [Fin.sum_univ_one, Pi.one_apply, mul_one] using hd
  · -- Bézout `b = ∑ᵢ 𝟙[i=i₀]·(Fᵢ∘g) = (F i₀∘g) = b`
    rw [Finset.sum_eq_single i₀ (fun i _ hi ↦ by simp [hi]) (fun h ↦ absurd (Finset.mem_univ i₀) h)]
    simpa using (hunit u hu).symm

/-- **THE GATE — admissible leaf region at the `(2,2,2)` terminal leaf.** Source dimension
`flatDim ![2,2,2] = 2·2 + 2·2 = 8`. Given the real-leaf collapse `unit ≡ 1` and a cover box radius
`R` whose closed ball sits in the chart region `V` (the inflated tiling radius the fold hands the
leaf, `≥ 1`), the terminal non-vanishing region `V' = V ∩ {unit ≠ 0}` **contains** that cover box
AND the box satisfies the `Covers` leaf-clause — the certificate region and the tiling box conjoined
on one region. No radius conflict: the shrink is vacuous, so any `R` with `closedBall 0 R ⊆ V`
(including `R ≥ 1`) fits. -/
theorem admissible_leaf_region_222
    (V : Set (Fin 8 → ℝ)) (unit : (Fin 8 → ℝ) → ℝ) (hcollapse : ∀ u, unit u = 1)
    (f : ℝ → ℝ) {R : ℝ} (hcover : closedBall (0 : Fin 8 → ℝ) R ⊆ V) :
    closedBall (0 : Fin 8 → ℝ) R ⊆ V ∩ {u | unit u ≠ 0} ∧
      FanTree.Covers f (FanTree.leaf (V ∩ {u | unit u ≠ 0})) R := by
  rw [terminal_region_eq_of_collapse V unit hcollapse]
  exact ⟨hcover, hcover⟩

end DLNFibre.DLN.Aoyagi.Corank2AdmissibleLeaf222
