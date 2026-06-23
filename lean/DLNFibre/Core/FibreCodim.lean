import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.MultComorphism

/-!
# `DLNFibre.Core.FibreCodim` — the fibre-codimension LOWER bound (partial F2 / Lemma 4.6)

**Scope, stated honestly.** Lehalleur–Rimányi Lemma 4.5/4.6 is the *codimension identity*

> `codimRepCanonical (mult⁻¹ B) = codimRepCanonical Σ̄^r + r·(d_0 + d_N − r)`  (`B` rank `r`).

This module proves the **easy half** that is reachable from the committed engine — the inclusion
lower bound

> `codimRepCanonical Σ̄^r ≤ codimRepCanonical (mult⁻¹ B)`

— and **only** that half. The identity itself is **NOT** proved here: its honest proof needs the
fibre-bundle / rank-chart local-trivialization of `mult` over the exact-rank determinantal stratum
`Mat^{rk=r}` (the paper's Lie-group submersion argument), which is **absent from Mathlib v4.29**.
The naïve "two-inequality sandwich" (Krull lower bound + affine-domain upper bound) provably cannot
close the gap: Krull's height theorem bounds height *above* by the generator count `d_N·d_0`, the
wrong direction and far larger than the shift `δ = r(d_0+d_N−r)`; and `mult` is **not flat** — the
fibre dimension *jumps* as the rank drops (witness `(2,2,2)`: the rank-`1` fibre has dimension `4`,
the rank-`0` fibre `mult⁻¹(0) = Σ̄^0` has dimension `5`), so the going-down additivity
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` does not apply to the comorphism at the
closed point `B`. The shift `δ` only materialises after restricting to the exact-rank chart where
the map *is* flat — a substantial new build (explicit pivot charts, the section `D = C A⁻¹ B`, the
product `mult⁻¹(U) ∩ Σ̄^r ≅ U × mult⁻¹(E)`, flatness per top component). The full identity stays
**Cited** (`DLN.BundleShiftInterface.cited_bundle_shift`) until that build lands.

What this lower bound *is*: a rigorous, non-overclaiming piece of bedrock the future chart build can
stand on. Mechanism: `mult⁻¹(B) ⊆ Σ̄^r` (rank of the product on the fibre is `rank B = r ≤ r`), so
`canonicalCoord '' (mult⁻¹ B) ⊆ canonicalCoord '' Σ̄^r`; `vanishingIdeal` is order-reversing and
`Ideal.height` is monotone, giving the codimension inequality. No `[IsAlgClosed]`/`[CharZero]`
needed — this half is pure inclusion monotonicity.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## `codimRepCanonical` is monotone under set inclusion (general lemma) -/

/-- **`codimRepCanonical` is monotone under inclusion.** A subset's geometric codimension is at
least that of any superset: a larger set has a smaller vanishing ideal (`vanishingIdeal_anti_mono`),
and `Ideal.height` is monotone, so `codimRepCanonical Z' ≤ codimRepCanonical Z` when `Z ⊆ Z'`.
Network-free, no field-closure hypothesis. -/
theorem codimRepCanonical_mono {d : Fin (N + 1) → ℕ} {Z Z' : Set (Tuple (k := k) d)}
    (h : Z ⊆ Z') : codimRepCanonical Z' ≤ codimRepCanonical Z := by
  apply Ideal.height_mono
  exact MvPolynomial.vanishingIdeal_anti_mono (Set.image_mono h)

/-! ## The fibre sits inside the closed rank-`≤ r` locus -/

/-- **The fibre over a rank-`r` matrix lies in `Σ̄^r`.** If `mult A = B` and `B.rank = r` then
`(mult A).rank = r ≤ r`, so `A ∈ productRankLocusLE d r`: `mult⁻¹(B) ⊆ Σ̄^r`. -/
theorem fibre_subset_productRankLocusLE {d : Fin (N + 1) → ℕ}
    {B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k} {r : ℕ} (hB : B.rank = r) :
    fibre d B ⊆ productRankLocusLE d r := by
  intro A hA
  rw [mem_productRankLocusLE]
  rw [mem_fibre] at hA
  rw [hA, hB]

/-! ## The fibre-codimension lower bound (the reachable half of Lemma 4.6) -/

/-- **The fibre-codimension lower bound (partial Lemma 4.6).** For `B` of rank `r`, the geometric
codimension of the closed rank-`≤ r` product locus `Σ̄^r` is at most that of the fibre `mult⁻¹(B)`:

> `codimRepCanonical Σ̄^r ≤ codimRepCanonical (mult⁻¹ B)`.

This is the **easy half** of LR Lemma 4.5/4.6 (`codim mult⁻¹ B = codim Σ̄^r + r(d_0+d_N−r)`), the
inequality `C ≤ codim mult⁻¹ B` that follows from `mult⁻¹ B ⊆ Σ̄^r` alone. The full identity — the
shift `+ r(d_0+d_N−r)` — is **Cited** (`DLN.BundleShiftInterface.cited_bundle_shift`); it needs the
exact-rank fibre-bundle structure absent from Mathlib v4.29 (see the module docstring). No closure /
characteristic hypothesis. -/
theorem codimRepCanonical_productRankLocusLE_le_codimRepCanonical_fibre {d : Fin (N + 1) → ℕ}
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) {r : ℕ} (hB : B.rank = r) :
    codimRepCanonical (productRankLocusLE (k := k) d r) ≤ codimRepCanonical (fibre d B) :=
  codimRepCanonical_mono (fibre_subset_productRankLocusLE hB)

/-! ## Non-vacuity witness — `(2,2,2)`, `B = 0`, `r = 0`

The lower bound fires at the cleanest base point `B = 0` (`rank 0 = 0`, `Matrix.rank_zero`): there
`mult⁻¹(0) = Σ̄^0`, so the inequality `codim Σ̄^0 ≤ codim mult⁻¹(0)` is in fact an equality (`0 = 0`
shift) — the lower bound is non-vacuous and tight at `r = 0`, the only case where the full Lemma 4.6
needs no shift (already a LANDED equality in `DLN.RlctPayoff`). -/

section Witness

/-- The fibre-codimension lower bound fires on `(2,2,2)` at `B = 0` (`r = 0`):
`codim Σ̄^0 ≤ codim mult⁻¹(0)`, over `AlgebraicClosure ℚ`. -/
example :
    codimRepCanonical (productRankLocusLE (k := AlgebraicClosure ℚ) dWitness 0)
      ≤ codimRepCanonical (fibre dWitness (0 : Matrix (Fin (dWitness (Fin.last 2)))
          (Fin (dWitness 0)) (AlgebraicClosure ℚ))) :=
  codimRepCanonical_productRankLocusLE_le_codimRepCanonical_fibre _ Matrix.rank_zero

end Witness

end DLNFibre.Core
