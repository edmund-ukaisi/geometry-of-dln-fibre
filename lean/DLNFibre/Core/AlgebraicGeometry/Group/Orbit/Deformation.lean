import DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Basic
import DLNFibre.Core.RingTheory.Kaehler.GenericRank
import DLNFibre.Core.LinearAlgebra.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# `DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Deformation` — deformation carrier + B1 (A4.3)

The deformation extension of the abstract affine-`G`-variety carrier
(`AlgebraicGeometry.Group.Orbit.AffineGVariety`, `Orbit/Basic.lean`) and the **submersion rank bound
B1 (A4.3)** stated against it:

> `genericDifferentialRank k G.R G.fρ ≤ finrank k (range G.δ)`.

`G.δ : C0 →ₗ[k] C1` is the abstract deformation coboundary (the `deformationδ M M` analogue); the
LHS is the field-theoretic generic differential rank of the orbit-coordinate family `G.fρ`
(`Core.RingTheory.Kaehler.GenericRank`).

## The (H1) factorisation hypothesis — name = content

The proof rests on the **Maurer–Cartan factorisation** of the orbit-coordinate differentials. The
genuinely geometric content is carried as a **named hypothesis** the concrete model discharges, NOT
asserted of a bare orbit map. The de-risk (P2.4 GUARD) established the precise dischargeable shape:

* the **forward** factorisation `span_K {D f_x} ≤ range (L ∘ δ.baseChange K)` is NOT dischargeable
  by the matrix-tuple model — its orbit-coordinate differentials pair against **single**
  edge-cochain entries (all of `C1`), not against `range δ` (the image of the coboundary), so a
  single `L` cannot recover them from `range (δ.baseChange K)`;
* the **adjoint/transpose** factorisation IS the model's natural shape and discharges cleanly: it
  carries an abstract **adjoint** `δAdj : C1 →ₗ[k] C0` (the `deltaTᵀ`/`dualMap` analogue) with a
  **rank-tie** `finrank (range δAdj) = finrank (range δ)`, and asserts
  `span_K {D f_x} ≤ range (L ∘ δAdj.baseChange K)` for some `L : K ⊗ C0 → Ω`.

So `DifferentialFactors G δAdj L` is the transpose Maurer–Cartan factorisation. The matrix-tuple
instance discharges it with `δAdj := deltaT M`, `L := (pairMC).liftBaseChange K`, and the rank-tie
`finrank_range_deltaT` (the trace self-duality `finrank (range deltaT) = finrank (range δ⁰)`). The
adjoint and its rank-tie are abstract **inputs**, with the matrix self-duality confined to the model
(name = content; `Core.OrbitDifferentialRank`).

## Hypotheses (name = content)

* `[Finite G.ρ]` / `[Fintype G.ρ]` is carried on the lemmas (the `genericDifferentialRank` needs a
  finite family), NOT on the base carrier (P2.3 discipline).
* `[FiniteDimensional k C0] [FiniteDimensional k C1]` are carrier fields — the deformation spaces
  are finite-dimensional (`finrank` is meaningful, base-change preserves rank).
* No char hypothesis here: B1 is **char-free** (the char-0 A4.2 criterion enters the *trdeg* wrapper
  one layer up, not the rank bound).

The eventual Mathlib home is `Mathlib.AlgebraicGeometry.Group.Orbit.Deformation`; the namespace here
mirrors that target (bare `AlgebraicGeometry.Group.Orbit`) so the lift is a file-move.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace AlgebraicGeometry.Group.Orbit

open scoped TensorProduct
open Module KaehlerDifferential

universe u

/-- **Deformation extension of the abstract affine-`G`-variety carrier.** Adds the deformation data
`(C0, C1, δ : C0 →ₗ[k] C1)` — the cochain-complex analogues `(cochain0 d d, cochain1 d d,
deformationδ M M)` of the DLN instance — to the base carrier `AffineGVariety`. The base carrier
keeps the *minimal* hypotheses (orbit-as-image irreducibility); the deformation/rank bricks consume
this extension. -/
structure AffineGVarietyDeformation (k : Type u) [Field k] extends AffineGVariety k where
  /-- The vertex-cochain space `C⁰` (the `cochain0 d d` analogue), finite-dimensional over `k`. -/
  C0 : Type u
  [C0ab : AddCommGroup C0] [C0mod : Module k C0] [C0fin : FiniteDimensional k C0]
  /-- The edge-cochain space `C¹` (the `cochain1 d d` analogue), finite-dimensional over `k`. -/
  C1 : Type u
  [C1ab : AddCommGroup C1] [C1mod : Module k C1] [C1fin : FiniteDimensional k C1]
  /-- The deformation coboundary `δ⁰ : C⁰ → C¹` (the `deformationδ M M` analogue). Its range is the
  orbit tangent image whose dimension bounds the orbit dimension from above. -/
  δ : C0 →ₗ[k] C1

namespace AffineGVarietyDeformation

variable {k : Type u} [Field k] (G : AffineGVarietyDeformation k)

attribute [instance] AffineGVarietyDeformation.C0ab AffineGVarietyDeformation.C0mod
  AffineGVarietyDeformation.C0fin AffineGVarietyDeformation.C1ab AffineGVarietyDeformation.C1mod
  AffineGVarietyDeformation.C1fin

/-- **(H1) The (transpose) Maurer–Cartan factorisation hypothesis.** Over `K = Frac G.R`, the span
of the orbit-coordinate differentials `{D_k(f_x)}` sits in the base-change image of an **adjoint**
carrier `δAdj : C1 →ₗ[k] C0` composed with a transport `L : K ⊗ C0 → Ω`:
`span_K {D_k(f_x)} ≤ range (L ∘ (δAdj.baseChange K))`.

This is the transpose form the matrix-tuple model discharges (`δAdj := deltaT M`, `L := pairMC`
lift; see the module docstring and the P2.4 GUARD finding). It is an abstract **input**; combined
with the rank-tie `finrank (range δAdj) = finrank (range δ)`, it yields the submersion bound B1.
When `G.fρ` is the coordinate pullback of an orbit map, `δAdj` is the trace-adjoint of the
deformation coboundary and the factorisation is the dual Maurer–Cartan identity. -/
def DifferentialFactors
    (δAdj : G.C1 →ₗ[k] G.C0)
    (L : (FractionRing G.R ⊗[k] G.C0) →ₗ[FractionRing G.R]
        KaehlerDifferential k (FractionRing G.R)) :
    Prop :=
  Submodule.span (FractionRing G.R)
      (Set.range fun x : G.ρ =>
        KaehlerDifferential.D k (FractionRing G.R)
          (algebraMap G.R (FractionRing G.R) (G.fρ x)))
    ≤ LinearMap.range (L.comp (δAdj.baseChange (FractionRing G.R)))

/-- **B1 — the submersion rank bound (A4.3), abstract.** For a finite ambient coordinate index
`G.ρ`, an abstract adjoint `δAdj : C1 → C0` and transport `L : K ⊗ C0 → Ω` satisfying the (H1)
factorisation, with the **rank-tie** `finrank (range δAdj) = finrank (range δ)`, the generic
differential rank of the orbit-coordinate family is at most the dimension of the deformation tangent
image:
`genericDifferentialRank k G.R G.fρ ≤ finrank k (range G.δ)`.

Route (char-free, no further model input): `genericDifferentialRank = finrank_K (span_K {D f_x})
≤[H1, finrank_mono] finrank_K (range (L ∘ δAdj.bc)) ≤[range_comp + finrank_map_le]
finrank_K (range (δAdj.bc)) =[finrank_range_baseChange, V2] finrank_k (range δAdj)
=[rank-tie] finrank_k (range δ)`. The adjoint/rank-tie carry the model's transpose self-duality;
B1 itself uses only `finrank_range_baseChange` and `Submodule.finrank_mono`/`finrank_map_le`. -/
theorem genericRankBound [Fintype G.ρ]
    (δAdj : G.C1 →ₗ[k] G.C0)
    (L : (FractionRing G.R ⊗[k] G.C0) →ₗ[FractionRing G.R]
        KaehlerDifferential k (FractionRing G.R))
    (hMC : G.DifferentialFactors δAdj L)
    (hRank : finrank k (LinearMap.range δAdj) = finrank k (LinearMap.range G.δ)) :
    DLNFibre.Core.genericDifferentialRank k G.R G.fρ
      ≤ finrank k (LinearMap.range G.δ) := by
  set K := FractionRing G.R
  have hfin : Module.Finite K (LinearMap.range (L.comp (δAdj.baseChange K))) :=
    LinearMap.finiteDimensional_range _
  have h1 : DLNFibre.Core.genericDifferentialRank k G.R G.fρ
      ≤ finrank K (LinearMap.range (L.comp (δAdj.baseChange K))) :=
    Submodule.finrank_mono hMC
  have h2 : finrank K (LinearMap.range (L.comp (δAdj.baseChange K)))
      ≤ finrank K (LinearMap.range (δAdj.baseChange K)) := by
    rw [LinearMap.range_comp]
    exact Submodule.finrank_map_le _ _
  have h3 : finrank K (LinearMap.range (δAdj.baseChange K))
      = finrank k (LinearMap.range δAdj) :=
    DLNFibre.Core.finrank_range_baseChange K δAdj
  exact h1.trans ((h2.trans_eq h3).trans_eq hRank)

end AffineGVarietyDeformation

end AlgebraicGeometry.Group.Orbit
