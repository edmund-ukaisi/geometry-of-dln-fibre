import DLNFibre.Core.FibreNormalForm

/-!
# `DLNFibre.Core.EndBaseChangeSweep` — the homogeneous sweep `Σ^r = H·F` (route c scaffolding)

The structural scaffolding of the **equivariant homogeneous sweep** route to Lehalleur–Rimányi Lemma
4.6's fibre dimension (thread 27's certificate). The endpoint group `H = GL_{d_N} × GL_{d_0}` acts on
`Rep_d` through the two end factors (here the full base-change group `BaseChangeGroup`; the inner units
telescope away in `mult`), `mult` is `H`-equivariant (`FibreNormalForm.mult_smul`), and any two rank-`r`
matrices are `H`-equivalent (`exists_baseChange_of_rank_eq`). Hence the **exact-rank locus is one
`H`-sweep of a single fibre**:

> `productRankLocus d r = ⋃_{P} (P • ·) '' (fibre d E)`   for any fixed rank-`r` target `E` (`N ≥ 1`).

This module proves that sweep identity (the reachable structural part of route c). The **dimension
consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` was the *one
genuinely hard rung* — an orbit/quotient-dimension count. It is **NOT** proved in this module; it
is now **discharged** via the route-β localized-chart `AlgEquiv` (`Core.ChartLocalizedAlgEquiv` +
`Core.ChartSweepWiring`) and the closure/density bridge `dim Σ^r = dim Σ̄^r`
(`Core.ClosureBridge`), giving the **unconditional** `codim (fibre d B) = C + δ`
(`Core.FibreCodimFinal`). The downstream assembly
(`codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep`) takes the sweep + closure identities as
**named hypotheses** (the conditional-bank pattern), with everything *around* them machine-checked
here. Nothing in this module itself claims the dimension identity.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## Rank is invariant under the endpoint base change -/

/-- The det of a `BaseChangeGroup` value (a `Units` of the matrix ring) is a unit. -/
theorem isUnit_det_baseChangeGroup (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    (v : Fin (N + 1)) : IsUnit (Units.val (P v)).det :=
  (P v).isUnit.map (Matrix.detMonoidHom)

/-- **Rank of the endpoint-conjugated target is unchanged.** For `P : BaseChangeGroup` and any target
`B`, `rank (P_N · B · P_0⁻¹) = rank B`: left/right multiplication by the invertible end-vertex units
preserves rank (`rank_mul_eq_right_of_isUnit_det` / `rank_mul_eq_left_of_isUnit_det`). -/
theorem rank_endpoint_conj (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    (Units.val (P (Fin.last N)) * B * Units.val ((P 0)⁻¹)).rank = B.rank := by
  rw [Matrix.mul_assoc, Matrix.rank_mul_eq_right_of_isUnit_det _ _
        (isUnit_det_baseChangeGroup d P (Fin.last N)),
      Matrix.rank_mul_eq_left_of_isUnit_det _ _
        (by simpa using isUnit_det_baseChangeGroup d P⁻¹ 0)]

/-! ## The sweep identity `Σ^r = H · F` -/

/-- **The exact-rank locus is the `H`-sweep of one fibre.** For a fixed rank-`r` target `E` and
`N ≥ 1`, the exact-rank locus `productRankLocus d r = {A : rank(mult A) = r}` is exactly the union,
over the endpoint base-change group, of the translates of the fibre `mult⁻¹(E)`:

> `A ∈ productRankLocus d r ↔ ∃ P, A ∈ (P • ·) '' (fibre d E)`.

`(←)` `mult` carries a translate of `fibre E` to `P_N · E · P_0⁻¹`, of rank `= rank E = r`
(`rank_endpoint_conj`). `(→)` `rank(mult A) = r = E.rank`, so `exists_baseChange_of_rank_eq` gives `P`
with `mult A = P_N · E · P_0⁻¹`, and `image_smul_fibre` packages `A` as a translate of `fibre E`. -/
theorem mem_productRankLocus_iff_mem_sweep (d : Fin (N + 1) → ℕ)
    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (E : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) {r : ℕ} (hE : E.rank = r)
    (A : Tuple (k := k) d) :
    A ∈ productRankLocus d r ↔
      ∃ P : BaseChangeGroup (k := k) d, A ∈ (fun A' ↦ P • A') '' (fibre d E) := by
  constructor
  · intro hA
    rw [mem_productRankLocus] at hA
    obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN E (mult d A) (by rw [hE, hA])
    exact ⟨P, by rw [image_smul_fibre, mem_fibre, ← hP]⟩
  · rintro ⟨P, hPA⟩
    rw [image_smul_fibre, mem_fibre] at hPA
    rw [mem_productRankLocus, hPA, rank_endpoint_conj, hE]

/-- **The sweep identity (set form).** `productRankLocus d r = ⋃_P (P • ·) '' (fibre d E)` for a fixed
rank-`r` target `E`. The set-level statement of `mem_productRankLocus_iff_mem_sweep`. -/
theorem productRankLocus_eq_iUnion_smul_fibre (d : Fin (N + 1) → ℕ)
    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (E : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) {r : ℕ} (hE : E.rank = r) :
    productRankLocus d r
      = ⋃ P : BaseChangeGroup (k := k) d, (fun A' ↦ P • A') '' (fibre d E) := by
  ext A
  rw [Set.mem_iUnion, mem_productRankLocus_iff_mem_sweep d hN E hE]

/-! ## Each translate is isomorphic to the fibre `F` (codim-preserving) -/

/-- **All rank-`r` fibres have the same codimension as `mult⁻¹(E)`.** Each `H`-translate of `fibre d
E` is `fibre d (P_N·E·P_0⁻¹)`, a rank-`r` fibre; `G1` (`codimRepCanonical_fibre_eq_of_rank_eq`, the
landed flatness-free homogeneity) makes its codimension equal to that of `mult⁻¹(E)`. The
codim-constancy that lets the sweep reduce to a single fibre. -/
theorem codimRepCanonical_fibre_translate_eq [Infinite k] (d : Fin (N + 1) → ℕ)
    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (E : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (P : BaseChangeGroup (k := k) d) :
    codimRepCanonical (fibre d (Units.val (P (Fin.last N)) * E * Units.val ((P 0)⁻¹)))
      = codimRepCanonical (fibre d E) :=
  codimRepCanonical_fibre_eq_of_rank_eq d hN _ E (rank_endpoint_conj d P E)

end DLNFibre.Core
