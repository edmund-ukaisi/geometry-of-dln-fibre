import DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Deformation
import DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Dimension
import DLNFibre.Core.Dimension.Trdeg

/-!
# `Orbit.Squeeze` — the abstract orbit-dimension squeeze headline

The Phase-2 capstone of the de-`Tuple` refactor: the **abstract orbit-dimension theorem**

> `varietyDim Z = finrank k (range G.δ)`

on the deformation carrier `AffineGVarietyDeformation k` (`Orbit/Deformation.lean`). It assembles
the two-sided differential/transcendence **squeeze**

```
varietyDim Z  =[A4.1]  (trdeg k k[fρ]).toNat
              ≤[Phase-1, DiffIndepCriterion]  genericDifferentialRank k R fρ
              ≤[B1, (H1) + rank-tie]  finrank (range δ)
              ≤[B3, (H2)]  finrank (m.Cotangent)
              =[B4, smooth k-rational point]  varietyDim Z
```

by `le_antisymm`. The variety dimension of the orbit-image closure equals the dimension of the
deformation tangent image `range δ` — the orbit is smooth of the expected dimension.

## name = content — the headline carries its full hypothesis bundle

This is the abstract theorem; the conjunction of hypotheses below is what the DLN matrix-tuple
instance **discharges** (`varietyDim_orbitRankLocus_eq_finrank_range_deformationδ`,
`Core.VoigtDischarge`). Each is an **input**, not a consequence of a bare orbit map:

* the **(H1) factorisation** `DifferentialFactors δAdj L` + the **rank-tie**
  `finrank (range δAdj) = finrank (range δ)` (the transpose Maurer–Cartan carrier; B1's inputs);
* the **differential-independence criterion** `DiffIndepCriterion k G.R` (the A4.2 char-0 content,
  carried as an explicit input — at the *abstract* level this criterion is the only char hypothesis;
  the DLN instance discharges it via `diffIndepCriterion_groupRing`, where `[CharZero k]` is the
  exact line and `[PerfectField]` would be FALSE, banked Phase-1 finding);
* the **(H2) infinitesimal action** `H : G.InfinitesimalAction I` (the dual-number ideal-killing;
  B3's input), with `[FiniteDimensional k (H.basePtIdeal).Cotangent]`;
* the **smooth `k`-rational point** at `m = H.basePtIdeal` — `[Algebra.IsSmoothAt k m]` +
  `hrat : Ideal.ResidueField m ≃ₐ[k] k` — NOT a smooth-point *existence* claim (B4's input; the
  existence is the model's density burden); `[PerfectField k]` for M3 (the only char typeclass the
  abstract headline consumes; no `[CharZero k]` — the char-0 content rides on `hcrit`);
* the **A0 / orbit↔kernel bridges** `hZ : vanishingIdeal Z = I` and
  `hIker : I = ker G.pullback.toRingHom` (the model-specific point set + the ideal-presentation
  linkage); `[Finite G.ρ]`, `[I.IsPrime]`, `[m.IsMaximal]`.

`varietyDim Z : ℕ∞`; the rank `finrank k (range δ) : ℕ` enters cast. B3 lives in `ℕ`, A4.1/B4 in
`ℕ∞`; the casts are explicit (`exact_mod_cast`).

The eventual Mathlib home is `Mathlib.AlgebraicGeometry.Group.Orbit.Squeeze`; the namespace here
mirrors that target (bare `AlgebraicGeometry.Group.Orbit`) so the lift is a file-move.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`. **Monument-free:** no Aoyagi/RLCT
axiom enters the squeeze (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
-/

namespace AlgebraicGeometry.Group.Orbit

open MvPolynomial Module DLNFibre.Core DLNFibre.Core.Dimension
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

/-- **The abstract orbit-dimension squeeze headline (the Phase-2 capstone).** On the deformation
carrier `G : AffineGVarietyDeformation k`, the variety dimension of an orbit-image closure `Z`
equals the dimension of the deformation tangent image:

> `varietyDim Z = finrank k (range G.δ)`.

The hypothesis bundle is the **full honest conjunction** the DLN matrix-tuple instance discharges
(name = content — see the module docstring); none is hidden. The `≤`/`≥` composition
(`le_antisymm`):

* **`≤`** — `varietyDim Z =[A4.1 `varietyDim_eq_trdeg_of_eq_ker`] (trdeg k k[fρ]).toNat`
  `≤[Phase-1 `trdeg_adjoin_le_genericDifferentialRank`, via `DiffIndepCriterion`] genericDiffRank`
  `≤[B1 `genericRankBound`, via (H1) `DifferentialFactors` + rank-tie] finrank (range δ)`;
* **`≥`** — `finrank (range δ) ≤[B3 `finrank_range_δ_le_finrank_cotangent`, via (H2)]`
  `finrank (m.Cotangent) =[B4 `finrank_cotangent_eq_varietyDim`, smooth `k`-point] varietyDim Z`,
  at `m = H.basePtIdeal`.

`varietyDim Z : ℕ∞`, `finrank … : ℕ` cast in; B3's `ℕ` bound and the `ℕ∞` ends are bridged by
`exact_mod_cast`. The char-0 content enters only through the explicit input `hcrit`
(`DiffIndepCriterion`, A4.2); the abstract headline carries no `[CharZero k]`. The smooth side needs
`[PerfectField k]` (M3, no algebraic closedness). Monument-free. -/
theorem varietyDim_eq_finrank_range_δ
    [PerfectField k]
    (G : AffineGVarietyDeformation k) [Finite G.ρ]
    -- the (H1) factorisation + rank-tie inputs (B1)
    (δAdj : G.C1 →ₗ[k] G.C0)
    (L : (FractionRing G.R ⊗[k] G.C0) →ₗ[FractionRing G.R]
        KaehlerDifferential k (FractionRing G.R))
    (hMC : G.DifferentialFactors δAdj L)
    (hRank : finrank k (LinearMap.range δAdj) = finrank k (LinearMap.range G.δ))
    -- the char-0 differential-independence criterion (Phase-1 trdeg bound)
    (hcrit : DiffIndepCriterion k G.R)
    -- the (H2) infinitesimal-action input (B3)
    {I : Ideal (MvPolynomial G.ρ k)}
    (H : G.InfinitesimalAction I)
    [FiniteDimensional k (H.basePtIdeal).Cotangent]
    -- the smooth k-rational point input (B4)
    [hI : I.IsPrime]
    [hm : (H.basePtIdeal).IsMaximal] [Algebra.IsSmoothAt k (H.basePtIdeal)]
    (hrat : Ideal.ResidueField (H.basePtIdeal) ≃ₐ[k] k)
    -- the orbit-as-image / A0 bridges (Z's vanishing ideal, the ideal-ker linkage)
    {Z : Set (G.ρ → k)}
    (hZ : MvPolynomial.vanishingIdeal k Z = I)
    (hIker : I = RingHom.ker G.toAffineGVariety.pullback.toRingHom) :
    varietyDim Z = (finrank k (LinearMap.range G.δ) : ℕ∞) := by
  haveI : Fintype G.ρ := Fintype.ofFinite _
  -- abbreviate the base ideal and the orbit tangent rank
  set m := H.basePtIdeal
  set r : ℕ := finrank k (LinearMap.range G.δ) with hr
  -- (≥) `r ≤ finrank (m.Cotangent) = varietyDim Z`
  have hB3 : r ≤ finrank k (m.Cotangent) := H.finrank_range_δ_le_finrank_cotangent
  have hB4 : (finrank k (m.Cotangent) : ℕ∞) = varietyDim Z :=
    finrank_cotangent_eq_varietyDim I m hrat hZ
  have hge : (r : ℕ∞) ≤ varietyDim Z := by
    rw [← hB4]; exact_mod_cast hB3
  -- (≤) `varietyDim Z = trdeg ≤ genericDifferentialRank ≤ r`
  have hA41 : varietyDim Z
      = ((Algebra.trdeg k G.toAffineGVariety.pullback.range).toNat : ℕ∞) :=
    G.toAffineGVariety.varietyDim_eq_trdeg_of_eq_ker (hZ.trans hIker)
  have htrdeg : (Algebra.trdeg k G.toAffineGVariety.pullback.range).toNat
      ≤ DLNFibre.Core.genericDifferentialRank k G.R G.fρ := by
    rw [G.toAffineGVariety.range_pullback]
    exact trdeg_adjoin_le_genericDifferentialRank k G.R G.fρ hcrit
  have hB1 : DLNFibre.Core.genericDifferentialRank k G.R G.fρ ≤ r :=
    G.genericRankBound δAdj L hMC hRank
  have hle : varietyDim Z ≤ (r : ℕ∞) := by
    rw [hA41]; exact_mod_cast htrdeg.trans hB1
  exact le_antisymm hle hge

end AlgebraicGeometry.Group.Orbit
