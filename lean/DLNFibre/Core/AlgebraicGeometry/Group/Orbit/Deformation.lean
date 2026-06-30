import DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Basic
import DLNFibre.Core.RingTheory.Kaehler.GenericRank
import DLNFibre.Core.LinearAlgebra.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# `DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Deformation` — deformation carrier + B1, B3

The deformation extension of the abstract affine-`G`-variety carrier
(`AlgebraicGeometry.Group.Orbit.AffineGVariety`, `Orbit/Basic.lean`) and the two abstract rank
bricks stated against it (B1 = A4.3; B3 = A6.1 first half):

* the **submersion rank bound B1 (A4.3)**: `genericDifferentialRank k G.R G.fρ ≤ finrank k (range
  G.δ)`;
* the **cotangent injection B3 (A6.1 first half)**: `finrank k (range G.δ) ≤ finrank k (cotangent
  at the base point)`, from the infinitesimal-action hypothesis (H2).

`G.δ : C0 →ₗ[k] C1` is the abstract deformation coboundary (the `deformationδ M M` analogue); B1's
LHS is the field-theoretic generic differential rank of the orbit-coordinate family `G.fρ`
(`Core.RingTheory.Kaehler.GenericRank`).

## The (H2) infinitesimal-action hypothesis (B3) — name = content

B3 is `finrank (range δ) ≤ finrank (cotangent)` from a **named hypothesis bundle**
`InfinitesimalAction I` over a quotient ideal `I : Ideal (MvPolynomial ρ k)` — the orbit ideal of
the concrete model (for the DLN instance, `I = orbitIdeal M = ker pullback`, equal by theorem). The
P2.5a GUARD (scratch discharge by the matrix-tuple model, body the existing
`dirDeriv`/`dirDeriv_mul`/R2★ lemmas) established that the **forward** shape pins (no transpose
pivot, unlike B1's (H1)): the bundle carries

* `basePt : MvPolynomial ρ k →ₐ[k] k` — evaluation at the base `k`-point (kills `I`);
* `dirDeriv : C0 →ₗ[k] (MvPolynomial ρ k →ₗ[k] k)` — the directional-derivative-at-base-point
  functional, `k`-linear in the direction `φ ∈ C0`, each `dirDeriv φ` killing `I` (R2★);
* `c1coord : C1 →ₗ[k] (ρ → k)`, **injective** — the coordinate map (the `canonicalCoord` analogue);
* Leibniz at the base point and the coordinate test `dirDeriv φ (X x) = c1coord (δ φ) x`.

From this the engine descends `dirDeriv`/`basePt` to `A = MvPolynomial ρ k ⧸ I`, sets the base ideal
`m = ker (basePt descended)`, builds the cotangent-functional pairing
`cotPairing : C0 →ₗ Dual k m.Cotangent`, proves `ker cotPairing ≤ ker δ` (the coordinate-test
injection), and concludes the finrank bound (needing only `[FiniteDimensional k m.Cotangent]` — NOT
a smooth point; that is the B4 input, kept out). The DLN instance discharges (H2) and re-derives
the existing reverse-inequality R5 step definitionally (`m = normalFormIdeal M` by `rfl`).

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

/-! ## B3 — the cotangent injection (A6.1 first half)

The reverse-direction first inequality: `finrank (range δ) ≤ finrank (cotangent at the base point)`,
from the infinitesimal-action hypothesis (H2). See the module docstring for the (H2) shape and the
P2.5a GUARD that pinned the *forward* form. -/

/-- **(H2) The infinitesimal-action hypothesis (B3 input).** Over a quotient ideal
`I : Ideal (MvPolynomial G.ρ k)` (the orbit ideal of the concrete model), the data of a base
`k`-point evaluation `basePt`, a directional-derivative-at-base-point family `dirDeriv` (`k`-linear
in the direction `φ ∈ C0`) killing `I`, and an **injective** coordinate map
`c1coord : C1 → (ρ → k)`, such that each `dirDeriv φ` is a derivation at the base point (Leibniz)
and the coordinate test `dirDeriv φ (X x) = c1coord (δ φ) x` holds.

This is an abstract **input** the concrete model discharges (for the DLN instance, with
`I = orbitIdeal M`, `basePt = orbit-point evaluation`, `dirDeriv = the dual-number directional
derivative`, `c1coord = canonicalCoord`; the discharge body is the existing
`dirDeriv`/`dirDeriv_mul`/R2★ lemmas — `Core.OrbitTangentCotangent`). It is NOT a consequence of a
bare orbit map: the dual-number infinitesimal curve and its ideal-killing are model facts. The
forward shape pins (the P2.5a GUARD), unlike B1's (H1), which needed the transpose. -/
structure InfinitesimalAction (I : Ideal (MvPolynomial G.ρ k)) where
  /-- evaluation at the base `k`-point. -/
  basePt : MvPolynomial G.ρ k →ₐ[k] k
  /-- the directional-derivative-at-base-point functional, `k`-linear in the direction `φ ∈ C0`. -/
  dirDeriv : G.C0 →ₗ[k] (MvPolynomial G.ρ k →ₗ[k] k)
  /-- the coordinate map `C1 → (ρ → k)` (the `canonicalCoord` analogue), injective. -/
  c1coord : G.C1 →ₗ[k] (G.ρ → k)
  /-- `c1coord` is injective (each `δ φ` is recovered from its coordinates). -/
  hc1coord : Function.Injective c1coord
  /-- (R2★) each `dirDeriv φ` kills the orbit ideal `I` to first order. -/
  hkill : ∀ (φ : G.C0) (f : MvPolynomial G.ρ k), f ∈ I → dirDeriv φ f = 0
  /-- `basePt` kills `I` (the base point lies on the orbit closure). -/
  hbase : ∀ f : MvPolynomial G.ρ k, f ∈ I → basePt f = 0
  /-- Leibniz at the base point: `D φ (f g) = basePt f · D φ g + basePt g · D φ f`. -/
  hLeibniz : ∀ (φ : G.C0) (f g : MvPolynomial G.ρ k),
    dirDeriv φ (f * g) = basePt f * dirDeriv φ g + basePt g * dirDeriv φ f
  /-- coordinate test: the directional derivative of `X x` is the `x`-component of `δ φ`. -/
  hcoord : ∀ (φ : G.C0) (x : G.ρ), dirDeriv φ (MvPolynomial.X x) = c1coord (G.δ φ) x

namespace InfinitesimalAction

open MvPolynomial

variable {G} {I : Ideal (MvPolynomial G.ρ k)} (H : G.InfinitesimalAction I)

/-- `basePt` descended to the orbit-image ring `A = MvPolynomial ρ k ⧸ I` (kills `I`). -/
noncomputable def basePtA : (MvPolynomial G.ρ k ⧸ I) →ₐ[k] k :=
  Ideal.Quotient.liftₐ I H.basePt (fun f hf => H.hbase f hf)

/-- The base-point ideal `m = ker (basePtA)` of `A` (the maximal ideal of the base `k`-point). -/
noncomputable def basePtIdeal : Ideal (MvPolynomial G.ρ k ⧸ I) :=
  RingHom.ker H.basePtA.toRingHom

@[simp] theorem basePtA_mk (f : MvPolynomial G.ρ k) :
    H.basePtA (Ideal.Quotient.mk I f) = H.basePt f := rfl

/-- `dirDeriv φ` descended to `A` (kills `I` by R2★); on `mk g` it is `dirDeriv φ g`. -/
noncomputable def dirDerivQuot (φ : G.C0) : (MvPolynomial G.ρ k ⧸ I) →ₗ[k] k :=
  Submodule.liftQ (I.restrictScalars k) (H.dirDeriv φ) (fun x hx => H.hkill φ x hx)

@[simp] theorem dirDerivQuot_mk (φ : G.C0) (g : MvPolynomial G.ρ k) :
    H.dirDerivQuot φ (Ideal.Quotient.mk I g) = H.dirDeriv φ g := rfl

/-- The descended functional is a derivation at the base point. -/
theorem dirDerivQuot_mul (φ : G.C0) (a b : MvPolynomial G.ρ k ⧸ I) :
    H.dirDerivQuot φ (a * b)
      = H.basePtA a * H.dirDerivQuot φ b + H.basePtA b * H.dirDerivQuot φ a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, dirDerivQuot_mk, dirDerivQuot_mk, dirDerivQuot_mk, H.hLeibniz, basePtA_mk,
    basePtA_mk]

/-- The cotangent functional `cot_φ : m.Cotangent →ₗ[k] k`: `dirDerivQuot φ` restricted to `m ⊆ A`
factors through `m ⧸ m²` (vanishes on products, since at the base point `basePtA x = basePtA y = 0`
for `x, y ∈ m`). -/
noncomputable def cotFunctional (φ : G.C0) : (H.basePtIdeal).Cotangent →ₗ[k] k :=
  Ideal.Cotangent.lift
    ((H.dirDerivQuot φ).comp ((H.basePtIdeal).subtype.restrictScalars k))
    (fun x y => by
      have hx : H.basePtA (x : MvPolynomial G.ρ k ⧸ I) = 0 := x.2
      have hy : H.basePtA (y : MvPolynomial G.ρ k ⧸ I) = 0 := y.2
      have hxy : ((x * y : H.basePtIdeal) : MvPolynomial G.ρ k ⧸ I)
          = (x : MvPolynomial G.ρ k ⧸ I) * (y : MvPolynomial G.ρ k ⧸ I) := rfl
      simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, Submodule.coe_subtype, hxy,
        dirDerivQuot_mul, hx, hy, zero_mul, add_zero])

@[simp] theorem cotFunctional_toCotangent (φ : G.C0) (x : H.basePtIdeal) :
    H.cotFunctional φ ((H.basePtIdeal).toCotangent x)
      = H.dirDerivQuot φ (x : MvPolynomial G.ρ k ⧸ I) := rfl

/-- `dirDeriv φ` kills `1`: Leibniz at `f = g = 1` gives `D 1 = 2·(basePt 1)·(D 1) = 2·D 1`. -/
theorem dirDeriv_one (φ : G.C0) : H.dirDeriv φ (1 : MvPolynomial G.ρ k) = 0 := by
  have h := H.hLeibniz φ 1 1
  rw [mul_one, map_one H.basePt, one_mul] at h
  have h2 : H.dirDeriv φ 1 + (0 : k) = H.dirDeriv φ 1 + H.dirDeriv φ 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- `dirDeriv φ` kills constants `C r` (`= r • 1`). -/
theorem dirDeriv_C (φ : G.C0) (r : k) : H.dirDeriv φ (MvPolynomial.C r) = 0 := by
  rw [show (MvPolynomial.C r : MvPolynomial G.ρ k) = r • (1 : MvPolynomial G.ρ k) from by
      rw [smul_eq_C_mul, mul_one], map_smul, dirDeriv_one, smul_zero]

/-- `basePt (C r) = r` (`basePt` is a `k`-algebra hom). -/
theorem basePt_C (r : k) : H.basePt (MvPolynomial.C r) = r := by
  rw [show (MvPolynomial.C r : MvPolynomial G.ρ k) = algebraMap k (MvPolynomial G.ρ k) r from rfl,
    H.basePt.commutes, Algebra.algebraMap_self_apply]

/-- The coordinate-test class `X x − C (basePt (X x))` lies in the base ideal `m` (it evaluates to
`0` at the base point). -/
theorem coordTest_mem (x : G.ρ) :
    Ideal.Quotient.mk I
        (MvPolynomial.X x - MvPolynomial.C (H.basePt (MvPolynomial.X x))) ∈ H.basePtIdeal := by
  show H.basePtA (Ideal.Quotient.mk I
      (MvPolynomial.X x - MvPolynomial.C (H.basePt (MvPolynomial.X x)))) = 0
  rw [basePtA_mk, map_sub, basePt_C, sub_self]

/-- The cotangent-functional pairing `Ψ : C0 →ₗ[k] Dual k m.Cotangent`, `φ ↦ cotFunctional φ`.
Linear in `φ` by linearity of `dirDeriv`. -/
noncomputable def cotPairing : G.C0 →ₗ[k] Module.Dual k (H.basePtIdeal).Cotangent where
  toFun φ := H.cotFunctional φ
  map_add' φ φ' := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨z, rfl⟩ := (H.basePtIdeal).toCotangent_surjective z
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (z : MvPolynomial G.ρ k ⧸ I)
    simp only [LinearMap.add_apply, cotFunctional_toCotangent, ← hg, dirDerivQuot_mk]
    exact congrFun (congrArg DFunLike.coe (map_add H.dirDeriv φ φ')) g
  map_smul' c φ := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨z, rfl⟩ := (H.basePtIdeal).toCotangent_surjective z
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (z : MvPolynomial G.ρ k ⧸ I)
    simp only [LinearMap.smul_apply, RingHom.id_apply, cotFunctional_toCotangent, ← hg,
      dirDerivQuot_mk]
    exact congrFun (congrArg DFunLike.coe (map_smul H.dirDeriv c φ)) g

/-- `cotPairing φ` on the cotangent class of the coordinate test `X x − C (basePt (X x))` is the
`x`-component `c1coord (δ φ) x`. -/
theorem cotPairing_coordTest (φ : G.C0) (x : G.ρ) :
    H.cotPairing φ
        ((H.basePtIdeal).toCotangent
          ⟨Ideal.Quotient.mk I
              (MvPolynomial.X x - MvPolynomial.C (H.basePt (MvPolynomial.X x))),
            H.coordTest_mem x⟩)
      = H.c1coord (G.δ φ) x := by
  show H.cotFunctional φ _ = _
  rw [cotFunctional_toCotangent, dirDerivQuot_mk, map_sub, dirDeriv_C, sub_zero, H.hcoord φ x]

/-- **`ker (cotPairing) ≤ ker δ`.** If the cotangent functional of `φ` vanishes then so does `δ φ`:
testing on the coordinate classes recovers each `c1coord (δ φ) x = 0`, so `c1coord (δ φ) = 0` and
`δ φ = 0` by injectivity of `c1coord`. -/
theorem ker_cotPairing_le_ker_δ :
    LinearMap.ker H.cotPairing ≤ LinearMap.ker G.δ := by
  intro φ hφ
  rw [LinearMap.mem_ker] at hφ ⊢
  have hv : ∀ x : G.ρ, H.c1coord (G.δ φ) x = 0 := fun x => by
    rw [← H.cotPairing_coordTest φ x, hφ, LinearMap.zero_apply]
  have : H.c1coord (G.δ φ) = 0 := by funext x; rw [hv x]; rfl
  exact H.hc1coord (by rw [this, map_zero])

/-- **B3 — the cotangent injection (A6.1 first half).** From the infinitesimal-action hypothesis
(H2), the deformation tangent image `range δ` injects into the Zariski cotangent space at the base
point, so `finrank (range δ) ≤ finrank (m.Cotangent)`. Needs only `[FiniteDimensional k
m.Cotangent]` — the smooth-`k`-point / `= varietyDim` half (B4) is a separate rung. Route:
rank–nullity for `δ` and `cotPairing` (same domain `C0`) with `ker cotPairing ≤ ker δ`, plus
`range cotPairing ⊆ Dual k (m.Cotangent)` and `finrank (Dual k V) = finrank V`
(`Subspace.dual_finrank_eq`). -/
theorem finrank_range_δ_le_finrank_cotangent
    [FiniteDimensional k (H.basePtIdeal).Cotangent] :
    finrank k (LinearMap.range G.δ) ≤ finrank k ((H.basePtIdeal).Cotangent) := by
  have hδ := G.δ.finrank_range_add_finrank_ker
  have hΨ := H.cotPairing.finrank_range_add_finrank_ker
  have hker : finrank k (LinearMap.ker H.cotPairing) ≤ finrank k (LinearMap.ker G.δ) :=
    Submodule.finrank_mono H.ker_cotPairing_le_ker_δ
  have hdual : finrank k (LinearMap.range H.cotPairing)
      ≤ finrank k ((H.basePtIdeal).Cotangent) := by
    calc finrank k (LinearMap.range H.cotPairing)
        ≤ finrank k (Module.Dual k (H.basePtIdeal).Cotangent) := Submodule.finrank_le _
      _ = finrank k ((H.basePtIdeal).Cotangent) := Subspace.dual_finrank_eq
  omega

end InfinitesimalAction

end AffineGVarietyDeformation

end AlgebraicGeometry.Group.Orbit
