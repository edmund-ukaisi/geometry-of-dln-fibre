import DLNFibre.Core.OrbitSmooth
import DLNFibre.Core.OrbitDifferential
import DLNFibre.Core.OrbitDifferentialRank
import DLNFibre.Core.OrbitLinearCodim
import DLNFibre.Core.RingTheory.Ideal.CotangentLocalization
import DLNFibre.Core.Dimension.Regular
import DLNFibre.Core.Dimension.AffineDomain
import DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Dimension
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.DualNumber
import Mathlib.Data.Matrix.DualNumber
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# `DLNFibre.Core.OrbitTangentCotangent` — A6.1: the reverse inequality `finrank(range δ⁰) ≤ varietyDim Z_M`

The **reverse** of the A4 submersion bound: the orbit tangent image `range δ⁰` injects into the
Zariski cotangent space at the normal-form point `M`, whose `k`-dimension is the variety dimension
of the orbit closure `Z_M = canonicalCoord '' orbitRankLocus M`. Combined with A4's `≤`, this squeezes
`varietyDim Z_M = finrank (range δ⁰)`, the geometric heart of Voigt's lemma.

The route is **intrinsic** (thread 38): a directional-derivative pairing against
`I = orbitIdeal M = vanishingIdeal(orbitSet M)` directly — no determinantal minors, no radical. The
one genuinely new content is **R2★** (`mkDerivation_orbitIdeal_eq_zero`): orbit directions `δ⁰ φ`
kill `I` to first order, proved with the landed dual-number certificate `orbitAction_eps_eq_deformationδ`.

**Typeclass.** The reverse inequality is char-free; `[PerfectField k] [Infinite k]` is inherited from
M3 (smooth point: `dense_smoothLocus_of_perfectField` + residue-field formal smoothness over a perfect
field) / L1 (primeness needs only `[Infinite k]`). Algebraic closedness is not used; `ℝ` qualifies
(`CharZero ⟹ PerfectField`). **Dependency rule:** `Core` only.
-/

namespace DLNFibre.Core

open Matrix Module MvPolynomial DualNumber TrivSqZeroExt Dimension

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## GAP 1 — the ambient identity `card (RepCoord d) = finrank C¹` -/

/-- **GAP 1.** `Nat.card (RepCoord d) = finrank k (cochain1 d d)`: both are `∑_i d(i.succ)·d(i.castSucc)`.
The left side reduces via `Nat.card_sigma`/`Fintype.card_prod`/`Fintype.card_fin`; the right is the
landed `finrank_cochain1`. Used in the L7 additive assembly (`card = finrank C¹`). -/
theorem card_repCoord_eq_finrank_cochain1 (d : Fin (N + 1) → ℕ) :
    Nat.card (RepCoord d) = finrank k (cochain1 (k := k) d d) := by
  classical
  rw [finrank_cochain1, Nat.card_eq_fintype_card, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-! ## GAP 2/3 dimension bridges — re-homed to the dimension stack

The DLN-free equidimensionality + κ/k tower facts behind R6 now live in `Core.Dimension.AffineDomain`
(`height_eq_ringKrullDim_of_isMaximal_fintype`, `ringKrullDim_localizationAtPrime_isMaximal_eq_fintype`,
`finrank_eq_finrank_of_residueField_equiv`), consumed here (and by `FibreDimFibration`/`FibreSmoothBlock`)
through the `open DLNFibre.Core.Dimension`. Only the DLN-specific `k`-rationality witness
`residueFieldAtPrimeNormalFormEquiv` stays below. -/

/-- **The orbit residue field is `k`.** `Ideal.ResidueField (normalFormIdeal M) ≃ₐ[k] k`: the
normal-form point `M` is `k`-rational, so the residue field at `m_M` is `k`. The quotient
`orbitRing M ⧸ m_M` is a field (`m_M` maximal); `IsFractionRing.algEquiv` makes it `k`-isomorphic to
its fraction field `κ(m_M)`, and `residueFieldNormalFormEquiv` identifies it with `k`. -/
noncomputable def residueFieldAtPrimeNormalFormEquiv [PerfectField k] [Infinite k]
    {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    Ideal.ResidueField (normalFormIdeal M) ≃ₐ[k] k := by
  haveI : (normalFormIdeal M).IsMaximal := orbitPointIdeal_isMaximal M 1
  have hfield : IsField (orbitRing M ⧸ normalFormIdeal M) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp ‹_›
  haveI : IsScalarTower k (orbitRing M ⧸ normalFormIdeal M)
      (Ideal.ResidueField (normalFormIdeal M)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [show algebraMap k (orbitRing M ⧸ normalFormIdeal M) x
            = algebraMap (orbitRing M) (orbitRing M ⧸ normalFormIdeal M)
              (algebraMap k (orbitRing M) x) from
          IsScalarTower.algebraMap_apply k (orbitRing M) (orbitRing M ⧸ normalFormIdeal M) x,
        ← IsScalarTower.algebraMap_apply (orbitRing M) (orbitRing M ⧸ normalFormIdeal M)
          (Ideal.ResidueField (normalFormIdeal M)),
        ← IsScalarTower.algebraMap_apply k (orbitRing M)
          (Ideal.ResidueField (normalFormIdeal M))]
  -- the structure map of the field `orbitRing M ⧸ m_M` into its residue field is bijective
  have hbij : Function.Bijective
      (algebraMap (orbitRing M ⧸ normalFormIdeal M) (Ideal.ResidueField (normalFormIdeal M))) :=
    ⟨IsFractionRing.injective _ _,
      (IsFractionRing.surjective_iff_isField (R := orbitRing M ⧸ normalFormIdeal M)
        (K := Ideal.ResidueField (normalFormIdeal M))).mpr hfield⟩
  exact (AlgEquiv.restrictScalars k (AlgEquiv.ofBijective
      (Algebra.ofId (orbitRing M ⧸ normalFormIdeal M) (Ideal.ResidueField (normalFormIdeal M)))
      hbij)).symm.trans (residueFieldNormalFormEquiv M)

/-! ## R2★ — orbit directions kill the orbit ideal to first order

The single new content of the reverse inequality. For `f ∈ I = orbitIdeal M` and a tangent direction
`φ : C⁰`, the directional derivative of `f` along `v = δ⁰ φ` (flattened) at the orbit point `M`
vanishes. Discharged with the dual-number group element `P_ε = 1 + ε φ`: evaluating `orbitPullback M f
= 0` at `P_ε` (over `DualNumber k`) and reading the `ε`-coefficient. -/

variable {d : Fin (N + 1) → ℕ}

/-- The dual-number group point of `φ`: at coordinate `⟨v, p, q⟩` the entry `(1 + ε • φ_v)_{pq}`. -/
private noncomputable def groupPointε (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) :
    GroupCoord d → DualNumber k :=
  fun c ↦ (1 + (ε : DualNumber k) • liftMat (φ c.1)) c.2.1 c.2.2

/-- The `k`-algebra hom `MvPolynomial (GroupCoord d) k →ₐ[k] DualNumber k` evaluating the generic
group element at `P_ε = 1 + ε φ`. -/
private noncomputable def aevalGroupε (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) :
    MvPolynomial (GroupCoord d) k →ₐ[k] DualNumber k :=
  MvPolynomial.aeval (groupPointε M φ)

/-- `aevalGroupε` sends the generic matrix at `v` to `1 + ε • φ_v` (entrywise `eval_X`). -/
private theorem aevalGroupε_genericMat (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (v : Fin (N + 1)) :
    (genericMat (k := k) d v).map (aevalGroupε M φ).toRingHom
      = 1 + (ε : DualNumber k) • liftMat (φ v) := by
  funext p q
  simp only [Matrix.map_apply, genericMat, aevalGroupε, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPolynomial.aeval_X, groupPointε]

/-- `1 + ε • φ_v` is invertible over `DualNumber k` (inverse `1 - ε • φ_v`,
`one_add_eps_mul_one_sub_eps`); its determinant is therefore a unit. -/
private theorem isUnit_det_one_add_eps (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (v : Fin (N + 1)) :
    IsUnit (1 + (ε : DualNumber k) • liftMat (φ v)).det :=
  IsUnit.of_mul_eq_one (1 - (ε : DualNumber k) • liftMat (φ v)).det
    (by rw [← Matrix.det_mul, one_add_eps_mul_one_sub_eps, Matrix.det_one])

/-- `aevalGroupε` sends the group denominator `Δ = ∏_v det(generic v)` to a unit (each factor is the
determinant of the invertible `1 + ε • φ_v`). -/
private theorem isUnit_aevalGroupε_groupDenom (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) :
    IsUnit (aevalGroupε M φ (groupDenom (k := k) d)) := by
  rw [groupDenom, map_prod]
  refine IsUnit.prod_iff.mpr fun v _ ↦ ?_
  rw [show (aevalGroupε M φ) (genericMat (k := k) d v).det
      = (aevalGroupε M φ).toRingHom (genericMat (k := k) d v).det from rfl,
    RingHom.map_det, show (aevalGroupε M φ).toRingHom.mapMatrix (genericMat (k := k) d v)
      = 1 + (ε : DualNumber k) • liftMat (φ v) from aevalGroupε_genericMat M φ v]
  exact isUnit_det_one_add_eps M φ v

/-- The dual-number evaluation `ψ : groupRing d →ₐ[k] DualNumber k` at `P_ε = 1 + ε φ`: the
`IsLocalization.liftAlgHom` of `aevalGroupε` through the unit denominator `Δ`. -/
private noncomputable def evalGroupRingε (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) :
    groupRing (k := k) d →ₐ[k] DualNumber k :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (groupDenom (k := k) d))
    (S := groupRing (k := k) d) (f := aevalGroupε M φ)
    (fun y ↦ by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, map_pow]
      exact (isUnit_aevalGroupε_groupDenom M φ).pow n)

/-- `evalGroupRingε` agrees with `aevalGroupε` on `algebraMap`-images. -/
private theorem evalGroupRingε_algebraMap (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (p : MvPolynomial (GroupCoord d) k) :
    evalGroupRingε M φ (groupAlgMap (k := k) d p) = aevalGroupε M φ p := by
  rw [evalGroupRingε, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]; rfl

/-- `evalGroupRingε` fixes the base field `k`. -/
private theorem evalGroupRingε_algebraMap_base (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (a : k) : evalGroupRingε M φ (algebraMap k (groupRing (k := k) d) a)
      = algebraMap k (DualNumber k) a := (evalGroupRingε M φ).commutes a

/-- `evalGroupRingε` sends the generic group element at `v` to `1 + ε • φ_v`. -/
private theorem evalGroupRingε_genericUnit (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (v : Fin (N + 1)) :
    (genericUnit (k := k) d v).map (evalGroupRingε M φ)
      = 1 + (ε : DualNumber k) • liftMat (φ v) := by
  rw [← aevalGroupε_genericMat M φ v]
  funext p q
  simp only [Matrix.map_apply, genericUnit, RingHom.mapMatrix_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, evalGroupRingε_algebraMap]

/-- `evalGroupRingε` sends the constant factor `genericFactor M i` to `liftMat (M i)`. -/
private theorem evalGroupRingε_genericFactor (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (i : Fin N) : (genericFactor M i).map (evalGroupRingε M φ) = liftMat (M i) := by
  funext s t
  simp only [Matrix.map_apply, genericFactor, evalGroupRingε_algebraMap_base, liftMat]

/-- `evalGroupRingε` sends the generic inverse `genericUnitInv v` to `1 − ε • φ_v` (the dual-number
inverse of `1 + ε • φ_v`, `one_add_eps_mul_one_sub_eps` + `Matrix.right_inv_eq_right_inv`). -/
private theorem evalGroupRingε_genericUnitInv (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (v : Fin (N + 1)) :
    (genericUnitInv (k := k) d v).map (evalGroupRingε M φ)
      = 1 - (ε : DualNumber k) • liftMat (φ v) := by
  -- the image of `genericUnit * genericUnitInv = 1` is `(1+εφ) * image(inv) = 1`
  have h1 : (1 + (ε : DualNumber k) • liftMat (φ v))
      * (genericUnitInv (k := k) d v).map (evalGroupRingε M φ) = 1 := by
    rw [← evalGroupRingε_genericUnit M φ v, ← Matrix.map_mul, genericUnit_mul_genericUnitInv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.right_inv_eq_right_inv h1 (one_add_eps_mul_one_sub_eps (φ v))

/-- The **dual-number orbit point** `p_ε : RepCoord d → DualNumber k` at `P_ε = 1 + ε φ`: the entry
`((1 + ε φ_{i.succ}) · M_i · (1 − ε φ_{i.castSucc}))_{st}` of the infinitesimally-deformed orbit element.
By `orbitAction_eps_eq_deformationδ` its `fst` is `(M_i)_{st}` and its `snd` is `(δ⁰ φ i)_{st}`. -/
private noncomputable def orbitPointεMat (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (i : Fin N) : Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) (DualNumber k) :=
  ((1 : Matrix (Fin (d i.succ)) (Fin (d i.succ)) (DualNumber k))
      + (ε : DualNumber k) • liftMat (φ i.succ)) * liftMat (M i)
    * (1 - (ε : DualNumber k) • liftMat (φ i.castSucc))

private noncomputable def orbitPointε (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) :
    RepCoord d → DualNumber k :=
  fun x ↦ orbitPointεMat M φ x.1 x.2.1 x.2.2

/-- **Step A (per-generator).** `evalGroupRingε M φ` sends the generic orbit coordinate to the
dual-number orbit point: `evalGroupRingε M φ (genericOrbitCoord M x) = orbitPointε M φ x`. Pushes
`evalGroupRingε` through the matrix product `genericUnit · genericFactor · genericUnitInv`. -/
private theorem evalGroupRingε_genericOrbitCoord (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (x : RepCoord d) :
    evalGroupRingε M φ (genericOrbitCoord M x) = orbitPointε M φ x := by
  rw [genericOrbitCoord, orbitPointε, orbitPointεMat,
    show evalGroupRingε M φ ((genericUnit (k := k) d x.1.succ * genericFactor M x.1
        * genericUnitInv (k := k) d x.1.castSucc) x.2.1 x.2.2)
      = ((genericUnit (k := k) d x.1.succ * genericFactor M x.1
        * genericUnitInv (k := k) d x.1.castSucc).map (evalGroupRingε M φ)) x.2.1 x.2.2 from rfl,
    Matrix.map_mul, Matrix.map_mul, evalGroupRingε_genericUnit, evalGroupRingε_genericFactor,
    evalGroupRingε_genericUnitInv]

/-- **Step A (assembled).** `evalGroupRingε M φ ∘ orbitPullback M = aeval (orbitPointε M φ)` as
`k`-algebra homs: both send `X x` to `orbitPointε M φ x` (`evalGroupRingε_genericOrbitCoord`) and `C r`
to `algebraMap k _ r`. -/
private theorem evalGroupRingε_comp_orbitPullback (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (g : MvPolynomial (RepCoord d) k) :
    evalGroupRingε M φ (orbitPullback M g) = MvPolynomial.aeval (orbitPointε M φ) g := by
  have hext : (evalGroupRingε M φ).comp (orbitPullback M)
      = MvPolynomial.aeval (orbitPointε M φ) := by
    refine MvPolynomial.algHom_ext (fun x ↦ ?_)
    rw [AlgHom.comp_apply, orbitPullback, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      evalGroupRingε_genericOrbitCoord]
  exact congrFun (congrArg DFunLike.coe hext) g

/-- **Step C.** `orbitPointε M φ x = inl (a_M x) + ε • (v x)`: the dual-number orbit point splits into
its value `a_M x = (M)_x` and its `ε`-coefficient `v x = (δ⁰ φ)_x`, by the landed certificate
`orbitAction_eps_eq_deformationδ`. -/
private theorem orbitPointε_eq (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) (x : RepCoord d) :
    orbitPointε M φ x
      = liftMat (M x.1) x.2.1 x.2.2
        + (ε : DualNumber k) * liftMat (deformationδ M M φ x.1) x.2.1 x.2.2 := by
  rw [orbitPointε, orbitPointεMat, orbitAction_eps_eq_deformationδ M φ x.1, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]

/-- The `liftMat`-entry of a `k`-matrix is `inl` of the entry (constant dual number). -/
private theorem liftMat_apply_eq_inl {a b : ℕ} (A : Matrix (Fin a) (Fin b) k) (p : Fin a)
    (q : Fin b) : liftMat A p q = TrivSqZeroExt.inl (A p q) := by
  rw [liftMat, Matrix.map_apply]; rfl

/-- `fst (orbitPointε M φ x) = a_M x` (the value at the orbit point `M`). -/
private theorem fst_orbitPointε (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) (x : RepCoord d) :
    (orbitPointε M φ x).fst = canonicalCoord d M x := by
  rw [orbitPointε_eq, TrivSqZeroExt.fst_add, liftMat_apply_eq_inl, TrivSqZeroExt.fst_mul, fst_eps,
    zero_mul, add_zero, TrivSqZeroExt.fst_inl, canonicalCoord_apply]

/-- `snd (orbitPointε M φ x) = v x` where `v = canonicalCoord (δ⁰ φ)` (the `ε`-coefficient). -/
private theorem snd_orbitPointε (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) (x : RepCoord d) :
    (orbitPointε M φ x).snd = canonicalCoord d (deformationδ M M φ) x := by
  rw [orbitPointε_eq, TrivSqZeroExt.snd_add, liftMat_apply_eq_inl, TrivSqZeroExt.snd_inl, zero_add,
    TrivSqZeroExt.snd_mul, fst_eps, snd_eps, liftMat_apply_eq_inl, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, canonicalCoord_apply]
  simp

/-! ## The directional-derivative functional and R2★ -/

/-- The **directional-derivative functional** `D_v : R →ₗ[k] k` along `v = δ⁰ φ` at the orbit point
`M`: the `ε`-coefficient of the dual-number evaluation, `D_v f = snd (aeval (orbitPointε M φ) f)`. A
`k`-derivation along `aeval a_M`, with `D_v (X x) = v x`. -/
noncomputable def dirDeriv (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) :
    MvPolynomial (RepCoord d) k →ₗ[k] k :=
  (TrivSqZeroExt.sndHom k k).comp (MvPolynomial.aeval (orbitPointε M φ)).toLinearMap

@[simp] theorem dirDeriv_apply (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (f : MvPolynomial (RepCoord d) k) :
    dirDeriv M φ f = (MvPolynomial.aeval (orbitPointε M φ) f).snd := rfl

/-- `fst ∘ aeval (orbitPointε M φ) = aeval a_M` (the value-part of the dual-number evaluation is plain
evaluation at the orbit point `M`). -/
theorem fst_aeval_orbitPointε (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (f : MvPolynomial (RepCoord d) k) :
    (MvPolynomial.aeval (orbitPointε M φ) f).fst = MvPolynomial.aeval (canonicalCoord d M) f := by
  have h : (TrivSqZeroExt.fstHom k k k).comp (MvPolynomial.aeval (orbitPointε M φ))
      = MvPolynomial.aeval (canonicalCoord d M) := by
    refine MvPolynomial.algHom_ext (fun x ↦ ?_)
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact fst_orbitPointε M φ x
  exact congrFun (congrArg DFunLike.coe h) f

/-- `D_v (X x) = v x` (the directional derivative of a coordinate is its component of `v = δ⁰ φ`). -/
@[simp] theorem dirDeriv_X (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) (x : RepCoord d) :
    dirDeriv M φ (MvPolynomial.X x) = canonicalCoord d (deformationδ M M φ) x := by
  rw [dirDeriv_apply, MvPolynomial.aeval_X, snd_orbitPointε]

/-- **Leibniz at the orbit point.** `D_v (f g) = a_M(f) · D_v g + a_M(g) · D_v f` (the dual-number
`snd_mul`, with `fst ∘ aeval p_ε = aeval a_M`). -/
theorem dirDeriv_mul (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (f g : MvPolynomial (RepCoord d) k) :
    dirDeriv M φ (f * g)
      = MvPolynomial.aeval (canonicalCoord d M) f * dirDeriv M φ g
        + MvPolynomial.aeval (canonicalCoord d M) g * dirDeriv M φ f := by
  rw [dirDeriv_apply, map_mul, TrivSqZeroExt.snd_mul, dirDeriv_apply, dirDeriv_apply,
    fst_aeval_orbitPointε, fst_aeval_orbitPointε]
  simp [mul_comm]

/-- **R2★ — orbit directions kill the orbit ideal to first order.** For `f ∈ orbitIdeal M` and any
`φ : C⁰`, the directional derivative `D_{δ⁰φ} f = 0`. Discharged via the dual-number group element
`P_ε = 1 + ε φ`: `orbitPullback M f = 0` (the kernel identity), so `aeval (orbitPointε M φ) f =
evalGroupRingε M φ (orbitPullback M f) = 0`, hence its `ε`-coefficient vanishes. Needs `[Infinite k]`
(for `I = ker (orbitPullback M)`). -/
theorem dirDeriv_orbitIdeal_eq_zero [Infinite k] (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    {f : MvPolynomial (RepCoord d) k} (hf : f ∈ orbitIdeal M) : dirDeriv M φ f = 0 := by
  -- `f ∈ I = ker (orbitPullback M)`, so `orbitPullback M f = 0`
  have hker : orbitPullback M f = 0 := by
    rw [orbitIdeal, ← range_orbitMap, vanishingIdeal_range_orbitMap_eq_ker M] at hf
    exact hf
  -- `aeval (orbitPointε M φ) f = evalGroupRingε M φ (orbitPullback M f) = 0`
  have h0 : MvPolynomial.aeval (orbitPointε M φ) f = 0 := by
    rw [← evalGroupRingε_comp_orbitPullback M φ f, hker, map_zero]
  rw [dirDeriv_apply, h0, TrivSqZeroExt.snd_zero]

/-! ## R3–R5 — the cotangent injection, now via the abstract engine

`D_v` kills `orbitIdeal M` (R2★), so it descends to `A = orbitRing M`, restricts to `m_M`, and
factors through the cotangent space `m_M.Cotangent`; the resulting pairing
`C⁰ → Dual k (m_M.Cotangent)` has `ker ⊆ ker δ⁰`, giving `finrank (range δ⁰) ≤ finrank
(m_M.Cotangent)`. This whole chain is now the **abstract B3 engine**
(`AffineGVarietyDeformation.InfinitesimalAction`, `Core.AlgebraicGeometry.Group.Orbit.Deformation`);
the matrix tuple discharges its (H2) hypothesis (`dlnInfinitesimalAction`, below) with the
R2★/Leibniz/φ-linearity/coordinate-test lemmas above. R5 is then the abstract bound at that
discharge. -/

variable [Infinite k]

/-! ## R4 — the φ-linearity inputs to the abstract (H2) discharge -/

omit [Infinite k] in
/-- `D_v (C r) = 0` (the directional derivative kills constants). -/
@[simp] theorem dirDeriv_C (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) (r : k) :
    dirDeriv M φ (MvPolynomial.C r) = 0 := by
  rw [dirDeriv_apply, MvPolynomial.aeval_C, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]

omit [Infinite k] in
/-- `canonicalCoord` of a sum of edge maps is the sum of `canonicalCoord`s (entrywise). -/
private theorem canonicalCoord_add (A B : Tuple (k := k) d) (x : RepCoord d) :
    canonicalCoord d (A + B) x = canonicalCoord d A x + canonicalCoord d B x := by
  simp only [canonicalCoord_apply, Pi.add_apply, Matrix.add_apply]

omit [Infinite k] in
/-- `canonicalCoord` of a scalar multiple of an edge map is the scalar multiple (entrywise). -/
private theorem canonicalCoord_smul (c : k) (A : Tuple (k := k) d) (x : RepCoord d) :
    canonicalCoord d (c • A) x = c • canonicalCoord d A x := by
  simp only [canonicalCoord_apply, Pi.smul_apply, Matrix.smul_apply]

omit [Infinite k] in
/-- `D_v` is additive in the direction `φ` (induction on `f`: constants vanish, `X x` gives
`(δ⁰(φ+φ'))_x = (δ⁰φ)_x + (δ⁰φ')_x` by linearity of `δ⁰`, products by Leibniz `dirDeriv_mul`). -/
theorem dirDeriv_add (M : Tuple (k := k) d) (φ φ' : cochain0 (k := k) d d)
    (f : MvPolynomial (RepCoord d) k) :
    dirDeriv M (φ + φ') f = dirDeriv M φ f + dirDeriv M φ' f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp only [dirDeriv_C, add_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]; ring
  | mul_X p x hp =>
    rw [dirDeriv_mul, dirDeriv_mul, dirDeriv_mul, hp, dirDeriv_X, dirDeriv_X, dirDeriv_X,
      show deformationδ M M (φ + φ') = deformationδ M M φ + deformationδ M M φ' from map_add _ _ _,
      canonicalCoord_add]
    ring

omit [Infinite k] in
/-- `D_v` is homogeneous in the direction `φ`. -/
theorem dirDeriv_smul (M : Tuple (k := k) d) (c : k) (φ : cochain0 (k := k) d d)
    (f : MvPolynomial (RepCoord d) k) :
    dirDeriv M (c • φ) f = c • dirDeriv M φ f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp only [dirDeriv_C, smul_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, smul_add]
  | mul_X p x hp =>
    rw [dirDeriv_mul, dirDeriv_mul, hp, dirDeriv_X, dirDeriv_X,
      show deformationδ M M (c • φ) = c • deformationδ M M φ from map_smul _ _ _,
      canonicalCoord_smul]
    simp only [smul_eq_mul]
    ring

/-- The orbit-point cotangent space `m_M.Cotangent` is finite-dimensional over `k`. It is a
finitely-generated `A`-module (`A = orbitRing M` noetherian, `m_M` f.g.), torsion by `m_M`, hence a
finite-dimensional `κ = A/m_M`-vector space; and `κ ≃ₐ[k] k` (the orbit point is `k`-rational), so it
is finite over `k`. Needs only `[PerfectField k]` (this instance does not depend on `[Infinite k]`; the
downstream reverse-inequality theorems do carry `[Infinite k] [PerfectField k]`). -/
instance finiteDimensional_cotangent_normalFormIdeal [PerfectField k] (M : Tuple (k := k) d) :
    FiniteDimensional k ((normalFormIdeal M).Cotangent) := by
  haveI : (normalFormIdeal M).IsMaximal := orbitPointIdeal_isMaximal M 1
  -- `m_M.Cotangent` is a finite `A`-module (`A` noetherian, `m_M` f.g., cotangent a quotient)
  haveI : Module.Finite (orbitRing M) ((normalFormIdeal M).Cotangent) :=
    Module.Finite.of_surjective (normalFormIdeal M).toCotangent
      (normalFormIdeal M).toCotangent_surjective
  -- torsion by `m_M` ⟹ the `κ = A/m_M`-module structure, and it is `Module.Finite κ`
  letI : Module (orbitRing M ⧸ normalFormIdeal M) ((normalFormIdeal M).Cotangent) :=
    Module.IsTorsionBySet.module (Ideal.isTorsionBySet_cotangent (normalFormIdeal M))
  haveI : IsScalarTower (orbitRing M) (orbitRing M ⧸ normalFormIdeal M)
      ((normalFormIdeal M).Cotangent) :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent (normalFormIdeal M))
  haveI : Module.Finite (orbitRing M ⧸ normalFormIdeal M) ((normalFormIdeal M).Cotangent) :=
    Module.Finite.of_restrictScalars_finite (orbitRing M) _ _
  -- `κ = A/m_M` is finite over `k` (`κ ≃ₐ[k] k`), so the cotangent is finite over `k`
  haveI : FiniteDimensional k (orbitRing M ⧸ normalFormIdeal M) :=
    Module.Finite.of_surjective (residueFieldNormalFormEquiv M).symm.toLinearMap
      (residueFieldNormalFormEquiv M).symm.surjective
  haveI : IsScalarTower k (orbitRing M ⧸ normalFormIdeal M) ((normalFormIdeal M).Cotangent) :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent (normalFormIdeal M))
  exact Module.Finite.trans (orbitRing M ⧸ normalFormIdeal M) ((normalFormIdeal M).Cotangent)

/-! ## B3 discharge — the matrix-tuple discharges the abstract (H2) infinitesimal-action

The DLN deformation instance `dlnOrbitDef M` discharges the abstract `InfinitesimalAction`
hypothesis (`Core.AlgebraicGeometry.Group.Orbit.Deformation`) over the orbit ideal `I = orbitIdeal
M`, with: `basePt = aeval (canonicalCoord (1 • M))` (the orbit-point evaluation), `dirDeriv =
dirDeriv M`, `c1coord = canonicalCoord d`. The discharge body is the R2★/Leibniz/coordinate-test
lemmas above. Because `basePt = aeval (canonicalCoord (1 • M))`, the abstract base ideal
`m = ker (basePt descended)` is **definitionally** `normalFormIdeal M = ker (orbitEval M 1)`, so the
abstract B3 re-derives R5 with no transport. -/

open AlgebraicGeometry.Group.Orbit in
/-- **The DLN discharge of the abstract (H2) infinitesimal action.** The matrix-tuple deformation
instance `dlnOrbitDef M` satisfies `AffineGVarietyDeformation.InfinitesimalAction (orbitIdeal M)`:
`basePt = aeval (canonicalCoord (1 • M))`, `dirDeriv = dirDeriv M`, `c1coord = canonicalCoord d`.
The fields are the landed R2★ (`dirDeriv_orbitIdeal_eq_zero`), Leibniz (`dirDeriv_mul`),
φ-linearity (`dirDeriv_add`/`dirDeriv_smul`), and the coordinate test (`dirDeriv_X`). -/
noncomputable def dlnInfinitesimalAction (M : Tuple (k := k) d) :
    (dlnOrbitDef M).InfinitesimalAction (k := k) (orbitIdeal M) where
  basePt := MvPolynomial.aeval (canonicalCoord d ((1 : BaseChangeGroup (k := k) d) • M))
  dirDeriv :=
    { toFun := fun φ ↦ dirDeriv M φ
      map_add' := fun φ φ' ↦ LinearMap.ext fun f ↦ dirDeriv_add M φ φ' f
      map_smul' := fun c φ ↦ LinearMap.ext fun f ↦ dirDeriv_smul M c φ f }
  c1coord :=
    { toFun := fun (φ : cochain1 (k := k) d d) ↦ canonicalCoord d φ
      map_add' := fun A B ↦ by funext x; rfl
      map_smul' := fun c A ↦ by funext x; rfl }
  hc1coord := (canonicalCoord d).injective
  hkill := fun φ f hf ↦ dirDeriv_orbitIdeal_eq_zero M φ hf
  hbase := fun f hf ↦ by
    show MvPolynomial.aeval (canonicalCoord d ((1 : BaseChangeGroup (k := k) d) • M)) f = 0
    rw [MvPolynomial.aeval_eq_eval]
    exact eval_orbitPoint_mem_orbitIdeal M 1 hf
  hLeibniz := fun φ f g ↦ by
    have h := dirDeriv_mul M φ f g
    rw [show ((1 : BaseChangeGroup (k := k) d) • M) = M from one_smul _ _]
    exact h
  hcoord := fun φ x ↦ dirDeriv_X M φ x

/-- **R5 — `finrank (range δ⁰) ≤ finrank (m_M.Cotangent)`.** The injection of the orbit tangent
image into the Zariski cotangent space, in finrank form. Now a transport of the **abstract B3**
(`AffineGVarietyDeformation.InfinitesimalAction.finrank_range_δ_le_finrank_cotangent`,
`Core.AlgebraicGeometry.Group.Orbit.Deformation`) at the DLN discharge `dlnInfinitesimalAction M`:
its base ideal `m` is `normalFormIdeal M` definitionally, and `(dlnOrbitDef M).δ = deformationδ M
M`, so the abstract bound is exactly this statement. The `[PerfectField k]`/`[Infinite k]` feed the
cotangent finite-dimensionality (`finiteDimensional_cotangent_normalFormIdeal`); the injection
itself is char-free (the engine needs only that the cotangent is finite-dimensional). -/
theorem finrank_range_deformationδ_le_finrank_cotangent [PerfectField k] (M : Tuple (k := k) d) :
    finrank k (LinearMap.range (deformationδ M M))
      ≤ finrank k ((normalFormIdeal M).Cotangent) := by
  haveI : FiniteDimensional k ((dlnInfinitesimalAction M).basePtIdeal).Cotangent :=
    finiteDimensional_cotangent_normalFormIdeal M
  exact (dlnInfinitesimalAction M).finrank_range_δ_le_finrank_cotangent

/-! ## R6 — `finrank (m_M.Cotangent) = varietyDim Z_M` via the abstract B4 -/

/-- **R6 — `finrank k (m_M.Cotangent) = varietyDim Z_M`** (the cotangent finrank equals the variety
dimension), now a transport of the **abstract B4**
(`AlgebraicGeometry.Group.Orbit.finrank_cotangent_eq_varietyDim`,
`Core/AlgebraicGeometry/Group/Orbit/Dimension.lean`) at the DLN instance: `σ = RepCoord d`,
`I = orbitIdeal M`, `m = normalFormIdeal M` (a maximal ideal of `orbitRing M = MvPolynomial (RepCoord
d) k ⧸ orbitIdeal M`, definitionally). The abstract B4 chains L2a localization collapse + the κ/k
bridge (GAP2) + M3 (smooth point) + GAP3 + `varietyDim = ringKrullDim`; the DLN instance supplies its
**point** hypotheses — smoothness (`isSmoothAt_normalFormIdeal`, the M3 generic-smoothness density),
`k`-rationality (`residueFieldAtPrimeNormalFormEquiv`, the orbit point is a genuine `k`-point) — and
the A0 bridge `vanishingIdeal Z_M = orbitIdeal M` (`vanishingIdeal_orbitRankLocus_eq_orbitSet`).
Carries `[PerfectField k]` (explicit) `[Infinite k]` (from the section). -/
theorem finrank_cotangent_eq_varietyDim [PerfectField k] (M : Tuple (k := k) d) :
    (finrank k ((normalFormIdeal M).Cotangent) : ℕ∞)
      = varietyDim (canonicalCoord d '' orbitRankLocus M) := by
  haveI : (orbitIdeal M).IsPrime := isPrime_vanishingIdeal_orbitSet M
  haveI : (normalFormIdeal M).IsMaximal := orbitPointIdeal_isMaximal M 1
  haveI : Algebra.IsSmoothAt k (normalFormIdeal M) := isSmoothAt_normalFormIdeal (k := k) M
  exact AlgebraicGeometry.Group.Orbit.finrank_cotangent_eq_varietyDim (orbitIdeal M)
    (normalFormIdeal M) (residueFieldAtPrimeNormalFormEquiv M)
    (vanishingIdeal_orbitRankLocus_eq_orbitSet M)

/-! ## The A6.1 headline — `finrank (range δ⁰) ≤ varietyDim Z_M` -/

/-- **A6.1 (the reverse inequality).** `finrank k (range δ⁰) ≤ varietyDim Z_M`: the orbit tangent
image `range (deformationδ M M)` injects into the Zariski cotangent space at `M` (R2–R5), whose
`k`-dimension is the variety dimension of the orbit closure `Z_M = canonicalCoord '' orbitRankLocus M`
(R6). The char-free reverse of the A4 submersion bound; `[PerfectField k] [Infinite k]` from M3/L1
(no algebraic closedness; `ℝ` qualifies). -/
theorem finrank_range_deformationδ_le_varietyDim [PerfectField k] (M : Tuple (k := k) d) :
    (finrank k (LinearMap.range (deformationδ M M)) : ℕ∞)
      ≤ varietyDim (canonicalCoord d '' orbitRankLocus M) := by
  rw [← finrank_cotangent_eq_varietyDim M]
  exact_mod_cast finrank_range_deformationδ_le_finrank_cotangent M

end DLNFibre.Core
