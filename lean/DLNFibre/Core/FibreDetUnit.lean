/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.DeepChartRing
import DLNFibre.Core.ChartSection
import DLNFibre.Core.MultComorphism

/-!
# `DLNFibre.Core.FibreDetUnit` — the deep pivot minor is `≡ 1` on the rank-`r` fibre

The **entry lemma** of the fibre-`θ` route (Route A, expedition `theta-components`, thread 04):

> **`ΔPdeep_sub_one_mem_fibreGenIdeal`** — `ΔPdeep d r − 1 ∈ fibreGenIdeal d E`, where
> `E = normalForm (d last) (d 0) r` is the rank-`r` normal form `diag(I_r, 0)`.

Equivalently `ΔPdeep d r ≡ 1` in the fibre coordinate ring `R ⧸ fibreGenIdeal d E`, so the deep
pivot minor `detΔ` is a **unit** on the whole fibre scheme (not merely a non-zero-divisor). This is
the load-bearing definitional fact certified in thread 04: the fibre ideal forces the product
`mult(Ã) = E` in the quotient, so its top-left `r×r` minor is `det (chartΔ E) = det (I_r) = 1`. It
removes the reducedness blocker for the Route-A transport of the `Σ̄^r` component count to the
fibre: `detΔ` a unit on `O(fibre)` ⟹ localizing at `detΔ` changes nothing, so the localized chart
`e` (`Core.ChartLocalizedAlgEquiv`) carries the minimal-prime / top-component structure of the
fibre faithfully.

**Scope (name = content).** General — any dimension vector `d`, any rank `r ≤ d last`, `r ≤ d 0`,
any field `k`. No `IsAlgClosed` / `CharZero`, no radicality / equidimensionality. The `r = 0` case
is `det (0×0) = 1`. This is the clean general restatement of the per-orbit `SourceNoDrop` Fact B
(`chartDsig_not_mem_partitionIdeal`), now an ideal-membership over the *fibre* rather than an orbit
non-vanishing.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The generic product entry is `≡ E` in the fibre coordinate ring.** Each `multPoly d r c` maps
to `C (E r c)` in `R ⧸ fibreGenIdeal d E`: the generator `multPoly d r c − C (E r c)` is in the
ideal. The per-entry input to the `det`-collapse of `ΔPdeep`. -/
theorem multPoly_sub_C_mem_fibreGenIdeal (d : Fin (N + 1) → ℕ)
    (E : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (a : Fin (d (Fin.last N))) (b : Fin (d 0)) :
    multPoly d a b - C (E a b) ∈ fibreGenIdeal d E :=
  Ideal.subset_span ⟨(a, b), rfl⟩

/-- **The chart `Δ`-block of the rank-`r` normal form is the identity** (`det = 1`). The top-left
`r×r` block of `normalForm = diag(I_r, 0)` is `I_r`. (Local restatement of `SourceNoDrop`'s Fact-B
helper, kept here so the entry lemma imports only `ChartSection`.) -/
theorem chartΔ_normalForm (p q r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    chartΔ (normalForm (k := k) p q r hp hq) hp hq = 1 := by
  ext i j
  rw [chartΔ, normalForm, Matrix.submatrix_apply, Matrix.submatrix_apply,
    finSplit_castLE, finSplit_castLE, Matrix.fromBlocks_apply₁₁]

/-- **The deep pivot minor reduces to `det (chartΔ E)` on the fibre.** In the fibre coordinate ring
`R ⧸ fibreGenIdeal d E`, the class of `ΔPdeep d r` equals the class of `C (det (chartΔ E))`: the
determinant commutes with the quotient map, and each generic-product entry reduces to the
corresponding entry of `E` (`multPoly_sub_C_mem_fibreGenIdeal`). -/
theorem mk_ΔPdeep_eq_chartΔ (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0)
    (E : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    Ideal.Quotient.mk (fibreGenIdeal d E) (ΔPdeep d r hp hq)
      = Ideal.Quotient.mk (fibreGenIdeal d E) (C (chartΔ E hp hq).det) := by
  set q := Ideal.Quotient.mk (fibreGenIdeal d E) with hq'
  rw [ΔPdeep, RingHom.map_det q,
    show q (C (chartΔ E hp hq).det) = (q.comp (C : k →+* _)) (chartΔ E hp hq).det from rfl,
    RingHom.map_det (q.comp (C : k →+* _))]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply,
    Matrix.submatrix_apply, Matrix.of_apply, chartΔ, Matrix.submatrix_apply, RingHom.comp_apply,
    ← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (multPoly_sub_C_mem_fibreGenIdeal d E _ _)

/-- **Entry lemma: `detΔ ≡ 1` on the rank-`r` fibre.** The deep pivot minor `ΔPdeep d r` differs
from `1` by an element of `fibreGenIdeal d E`, where `E = normalForm (d last) (d 0) r` is the
rank-`r` normal form `diag(I_r, 0)`. So `detΔ` is a unit in the fibre coordinate ring
`R ⧸ fibreGenIdeal d E` — the load-bearing fact opening the Route-A transport (thread 04). General:
any `d`, any `r`, any field; `r = 0` gives `det (0×0) = 1`. -/
theorem ΔPdeep_sub_one_mem_fibreGenIdeal (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    ΔPdeep d r hp hq - 1
      ∈ fibreGenIdeal d (normalForm (k := k) (d (Fin.last N)) (d 0) r hp hq) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero,
    mk_ΔPdeep_eq_chartΔ d r hp hq, chartΔ_normalForm (d (Fin.last N)) (d 0) r hp hq,
    Matrix.det_one, map_one, map_one]

/-- **`detΔ` is a unit on the rank-`r` fibre.** The class of `ΔPdeep d r` in the fibre coordinate
ring `R ⧸ fibreGenIdeal d E` (`E = normalForm`) is `1`, hence a unit — the form the Route-A
localization transport consumes. -/
theorem isUnit_mk_ΔPdeep_fibreGenIdeal (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    IsUnit (Ideal.Quotient.mk
      (fibreGenIdeal d (normalForm (k := k) (d (Fin.last N)) (d 0) r hp hq))
      (ΔPdeep d r hp hq)) := by
  have h : Ideal.Quotient.mk
      (fibreGenIdeal d (normalForm (k := k) (d (Fin.last N)) (d 0) r hp hq))
      (ΔPdeep d r hp hq) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (ΔPdeep_sub_one_mem_fibreGenIdeal d r hp hq)
  rw [h]; exact isUnit_one

/-! ## The Route-A payoff: localizing the fibre ring at `detΔ` changes nothing

`detΔ` is a unit on `O(fibre)` (`isUnit_mk_ΔPdeep_fibreGenIdeal`), so inverting it is an algebra
isomorphism `O(fibre) ≃ₐ O(fibre)[1/detΔ]` (`IsLocalization.atUnits`, since the powers of a unit are
units). This is the formal statement of thread 04's kill-condition: passing to the pivot chart
`{detΔ ≠ 0}` is invisible on the fibre — no minimal prime / top-dimensional component is lost. It is
the fibre-side endpoint of the Route-A component-count transport. -/

/-- **Localizing the fibre coordinate ring at `detΔ` is an iso.** Since `ΔPdeep d r` is a unit in
`R ⧸ fibreGenIdeal d E` (`E = normalForm`), the away-localization at its class is an algebra
isomorphism `O(fibre) ≃ₐ[O(fibre)] O(fibre)[1/detΔ]`: the pivot chart `{detΔ ≠ 0}` covers the whole
fibre. The reducedness-free Route-A statement (thread 04). -/
noncomputable def fibreLocalizationAwayDetΔ_algEquiv (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    letI Q := MvPolynomial (RepCoord d) k
        ⧸ fibreGenIdeal d (normalForm (k := k) (d (Fin.last N)) (d 0) r hp hq)
    Q ≃ₐ[Q] Localization.Away (Ideal.Quotient.mk
      (fibreGenIdeal d (normalForm (k := k) (d (Fin.last N)) (d 0) r hp hq)) (ΔPdeep d r hp hq)) :=
  IsLocalization.atUnits _ _
    (Submonoid.powers_le.mpr
      ((IsUnit.mem_submonoid_iff _).mpr (isUnit_mk_ΔPdeep_fibreGenIdeal d r hp hq)))

end DLNFibre.Core
