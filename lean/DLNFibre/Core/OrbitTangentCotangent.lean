import DLNFibre.Core.OrbitSmooth
import DLNFibre.Core.OrbitDifferential
import DLNFibre.Core.OrbitLinearCodim
import DLNFibre.Core.RingTheory.Ideal.CotangentLocalization
import DLNFibre.Core.Dimension.Regular
import DLNFibre.Core.Dimension.AffineDomain
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

/-! ## GAP 3 — L4d over a `Fintype` index (equidimensionality at the orbit point) -/

/-- **GAP 3 — equidimensionality at a closed point, `Fintype`-indexed.** For `A = MvPolynomial σ k ⧸ I`
a finite-type domain over a field (`σ` finite, `I` prime) and `m` a maximal ideal of `A`,
`m.height = ringKrullDim A`. Transported from the `Fin (card σ)` headline
`height_eq_ringKrullDim_of_isMaximal` (L4d) through the `renameEquiv` coordinate relabelling and the
induced quotient algebra equivalence. -/
theorem height_eq_ringKrullDim_of_isMaximal_fintype {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (m : Ideal (MvPolynomial σ k ⧸ I)) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ k ⧸ I) := by
  classical
  haveI : Fintype σ := Fintype.ofFinite _
  -- relabel `σ ≃ Fin (card σ)` and transport `I` to a prime `J`
  set e : MvPolynomial σ k ≃ₐ[k] MvPolynomial (Fin (Fintype.card σ)) k :=
    MvPolynomial.renameEquiv k (Fintype.equivFin σ) with he
  set J : Ideal (MvPolynomial (Fin (Fintype.card σ)) k) :=
    I.map (e : MvPolynomial σ k →+* _) with hJ
  haveI : J.IsPrime := by rw [hJ]; exact Ideal.map_isPrime_of_equiv e
  -- the induced quotient algebra equivalence `A ≃ₐ[k] MvPolynomial (Fin _) k ⧸ J`
  set Φ : (MvPolynomial σ k ⧸ I) ≃ₐ[k] (MvPolynomial (Fin (Fintype.card σ)) k ⧸ J) :=
    Ideal.quotientEquivAlg I J e rfl with hΦ
  -- transport `m` to a maximal ideal `m'` of the `Fin`-indexed quotient
  set m' : Ideal (MvPolynomial (Fin (Fintype.card σ)) k ⧸ J) :=
    m.map (Φ.toRingEquiv : (MvPolynomial σ k ⧸ I) ≃+* _) with hm'
  haveI : m'.IsMaximal := by rw [hm']; infer_instance
  -- L4d on the `Fin`-indexed side, transported back along `Φ` and `e`
  have hL4d := height_eq_ringKrullDim_of_isMaximal k (Fintype.card σ) J m'
  rw [hm', show (m.map (Φ.toRingEquiv : (MvPolynomial σ k ⧸ I) ≃+* _))
      = m.map (Φ : (MvPolynomial σ k ⧸ I) →+* _) from rfl,
    height_map_algEquiv Φ m, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL4d
  exact hL4d

/-- **GAP 3 — local ↔ global dimension at the orbit normal-form point.** For the orbit ring
`A = MvPolynomial σ k ⧸ I` (`σ` finite, `I` prime) and a maximal ideal `m`, the local ring
`Localization.AtPrime m` has Krull dimension equal to `ringKrullDim A`. `Fintype`-indexed companion of
L4d's `ringKrullDim_localizationAtPrime_isMaximal_eq`, via `IsLocalization.AtPrime.ringKrullDim_eq_height`
and the equidimensionality `height_eq_ringKrullDim_of_isMaximal_fintype`. -/
theorem ringKrullDim_localizationAtPrime_isMaximal_eq_fintype {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (m : Ideal (MvPolynomial σ k ⧸ I)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim (MvPolynomial σ k ⧸ I) := by
  haveI : m.IsPrime := inferInstance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
  exact height_eq_ringKrullDim_of_isMaximal_fintype I m

/-! ## GAP 2 — the κ/k base-ring bridge (`finrank k V = finrank κ V` for `κ ≃ₐ[k] k`) -/

/-- **GAP 2 (general tower step).** If a field `κ` is a `k`-algebra with `κ ≃ₐ[k] k` (a `k`-rational
residue field), then for any `κ`-module `V` in a `k → κ → V` scalar tower, `finrank k V = finrank κ V`:
the tower law `finrank k κ · finrank κ V = finrank k V` with `finrank k κ = 1` (from `κ ≃ₐ[k] k`). -/
theorem finrank_eq_finrank_of_residueField_equiv {κ : Type*} [Field κ] [Algebra k κ]
    (e : κ ≃ₐ[k] k) {V : Type*} [AddCommGroup V] [Module κ V] [Module k V] [IsScalarTower k κ V] :
    finrank k V = finrank κ V := by
  haveI : Module.Finite k κ := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  have hκ : finrank k κ = 1 := by
    rw [LinearEquiv.finrank_eq e.toLinearEquiv, finrank_self]
  rw [← Module.finrank_mul_finrank k κ V, hκ, one_mul]

/-- **GAP 2 (the orbit residue field is `k`).** `Ideal.ResidueField (normalFormIdeal M) ≃ₐ[k] k`: the
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

/-! ## R3 — descend `D_v` to `A`, restrict to `m_M`, factor through the cotangent

`D_v` kills `orbitIdeal M` (R2★), so it descends to `Ā_v : A →ₗ[k] k`; restricting to `m_M` and using
the Leibniz vanishing on products gives a functional on the cotangent space `m_M.Cotangent`. -/

variable [Infinite k]

/-- The descended functional `Ā_v : A →ₗ[k] k` (with `A = orbitRing M`): `D_v` factors through the
quotient `R ↠ A` since it kills `orbitIdeal M` (R2★). On a residue class `mk g` it is `D_v g`. -/
noncomputable def dirDerivQuot (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) :
    orbitRing M →ₗ[k] k :=
  Submodule.liftQ ((orbitIdeal M).restrictScalars k) (dirDeriv M φ)
    (fun x hx ↦ dirDeriv_orbitIdeal_eq_zero M φ hx)

@[simp] theorem dirDerivQuot_mk (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (g : MvPolynomial (RepCoord d) k) :
    dirDerivQuot M φ (Ideal.Quotient.mk (orbitIdeal M) g) = dirDeriv M φ g := rfl

/-- `Ā_v` is a derivation at the orbit point: `Ā_v(a b) = a_M(a)·Ā_v(b) + a_M(b)·Ā_v(a)`, where
`a_M(·) = orbitEval M 1`. From `dirDeriv_mul` pushed through the quotient. -/
theorem dirDerivQuot_mul (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) (a b : orbitRing M) :
    dirDerivQuot M φ (a * b)
      = orbitEval M 1 a * dirDerivQuot M φ b + orbitEval M 1 b * dirDerivQuot M φ a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, dirDerivQuot_mk, dirDerivQuot_mk, dirDerivQuot_mk, dirDeriv_mul,
    orbitEval_mk, orbitEval_mk, one_smul, MvPolynomial.aeval_eq_eval]

/-- The cotangent functional `cot_v : m_M.Cotangent →ₗ[k] k` of the tangent direction `v = δ⁰ φ`:
`Ā_v` restricted to `m_M ⊆ A` (`k`-linearly) factors through `m_M ⧸ m_M²` because it vanishes on
products (`x, y ∈ m_M ⟹ a_M(x) = a_M(y) = 0`, so the Leibniz terms drop). -/
noncomputable def cotFunctional (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) :
    (normalFormIdeal M).Cotangent →ₗ[k] k :=
  Ideal.Cotangent.lift
    ((dirDerivQuot M φ).comp ((normalFormIdeal M).subtype.restrictScalars k))
    (fun x y ↦ by
      -- `x, y ∈ m_M` evaluate to `0` at `M`, killing both Leibniz terms
      have hx : orbitEval M 1 (x : orbitRing M) = 0 := x.2
      have hy : orbitEval M 1 (y : orbitRing M) = 0 := y.2
      have hxy : ((x * y : normalFormIdeal M) : orbitRing M)
          = (x : orbitRing M) * (y : orbitRing M) := rfl
      simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, Submodule.coe_subtype, hxy,
        dirDerivQuot_mul, hx, hy, zero_mul, add_zero])

@[simp] theorem cotFunctional_toCotangent (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    (x : normalFormIdeal M) :
    cotFunctional M φ ((normalFormIdeal M).toCotangent x) = dirDerivQuot M φ (x : orbitRing M) :=
  rfl

/-! ## R4 — `cotFunctional` is `k`-linear in `φ`; the coordinate test for injectivity -/

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

/-! ## R4–R5 — the injection `range δ⁰ ↪ Dual k (m_M.Cotangent)` and the finrank bound -/

omit [Infinite k] in
/-- The coordinate test polynomial `X x − C (a_x)` lies in `m_M` (it evaluates to `0` at `M`). -/
theorem coordTest_mem_normalFormIdeal (M : Tuple (k := k) d) (x : RepCoord d) :
    Ideal.Quotient.mk (orbitIdeal M)
        (MvPolynomial.X x - MvPolynomial.C (canonicalCoord d M x)) ∈ normalFormIdeal M := by
  rw [normalFormIdeal, orbitPointIdeal, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    orbitEval_mk, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, one_smul, sub_self]

/-- `Ψ : C⁰ →ₗ[k] Dual k (m_M.Cotangent)`, `φ ↦ cotFunctional M φ`, the cotangent-functional pairing
of the orbit tangent direction `δ⁰ φ`. Linear in `φ` by `dirDeriv_add`/`dirDeriv_smul`. -/
noncomputable def cotPairing (M : Tuple (k := k) d) :
    cochain0 (k := k) d d →ₗ[k] Module.Dual k (normalFormIdeal M).Cotangent where
  toFun φ := cotFunctional M φ
  map_add' φ φ' := by
    refine LinearMap.ext fun z ↦ ?_
    obtain ⟨z, rfl⟩ := (normalFormIdeal M).toCotangent_surjective z
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (z : orbitRing M)
    simp only [LinearMap.add_apply, cotFunctional_toCotangent, ← hg, dirDerivQuot_mk,
      dirDeriv_add]
  map_smul' c φ := by
    refine LinearMap.ext fun z ↦ ?_
    obtain ⟨z, rfl⟩ := (normalFormIdeal M).toCotangent_surjective z
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (z : orbitRing M)
    simp only [LinearMap.smul_apply, RingHom.id_apply, cotFunctional_toCotangent, ← hg,
      dirDerivQuot_mk, dirDeriv_smul, smul_eq_mul]

/-- `cotPairing M φ` evaluated on the cotangent class of the coordinate test `X x − C a_x` is the
component `v x = (δ⁰ φ)_x`: the directional derivative of a coordinate is its `v`-component. -/
theorem cotPairing_coordTest (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d) (x : RepCoord d) :
    cotPairing M φ
        ((normalFormIdeal M).toCotangent
          ⟨Ideal.Quotient.mk (orbitIdeal M)
              (MvPolynomial.X x - MvPolynomial.C (canonicalCoord d M x)),
            coordTest_mem_normalFormIdeal M x⟩)
      = canonicalCoord d (deformationδ M M φ) x := by
  show cotFunctional M φ _ = _
  rw [cotFunctional_toCotangent, dirDerivQuot_mk, map_sub, dirDeriv_X, dirDeriv_C, sub_zero]

/-- **R4 — `ker (cotPairing M) ⊆ ker (deformationδ M M)`.** If the cotangent functional of `φ`
vanishes, then so does `δ⁰ φ`: testing on the coordinate classes recovers each component
`(δ⁰ φ)_x = cotPairing M φ (…) = 0`. -/
theorem ker_cotPairing_le_ker_deformationδ (M : Tuple (k := k) d) :
    LinearMap.ker (cotPairing M) ≤ LinearMap.ker (deformationδ M M) := by
  intro φ hφ
  rw [LinearMap.mem_ker] at hφ ⊢
  -- every coordinate of `δ⁰ φ` is `0`, so `δ⁰ φ = 0`
  have hv : ∀ x : RepCoord d, canonicalCoord d (deformationδ M M φ) x = 0 := by
    intro x
    rw [← cotPairing_coordTest M φ x, hφ, LinearMap.zero_apply]
  have hz : canonicalCoord d (deformationδ M M φ) = canonicalCoord d 0 := by
    funext x; rw [hv x]; simp [canonicalCoord_apply]
  exact (canonicalCoord d).injective hz

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

/-- **R5 — `finrank (range δ⁰) ≤ finrank (m_M.Cotangent)`.** The injection of the orbit tangent
image into the Zariski cotangent space, in finrank form: `ker (cotPairing) ⊆ ker δ⁰` (R4) gives
`finrank (range δ⁰) ≤ finrank (range cotPairing)`, and `range cotPairing ⊆ Dual k (m_M.Cotangent)`
has `finrank ≤ finrank (m_M.Cotangent)` (`Subspace.dual_finrank_eq`). Carries `[PerfectField k]`
(explicit) `[Infinite k]` (from the section). -/
theorem finrank_range_deformationδ_le_finrank_cotangent [PerfectField k] (M : Tuple (k := k) d) :
    finrank k (LinearMap.range (deformationδ M M))
      ≤ finrank k ((normalFormIdeal M).Cotangent) := by
  -- rank–nullity for `δ⁰` and `cotPairing` (same domain `C⁰`), with `ker cotPairing ⊆ ker δ⁰`
  have hδ : finrank k (LinearMap.range (deformationδ M M))
      + finrank k (LinearMap.ker (deformationδ M M)) = finrank k (cochain0 (k := k) d d) :=
    (deformationδ M M).finrank_range_add_finrank_ker
  have hΨ : finrank k (LinearMap.range (cotPairing M))
      + finrank k (LinearMap.ker (cotPairing M)) = finrank k (cochain0 (k := k) d d) :=
    (cotPairing M).finrank_range_add_finrank_ker
  have hker : finrank k (LinearMap.ker (cotPairing M))
      ≤ finrank k (LinearMap.ker (deformationδ M M)) :=
    Submodule.finrank_mono (ker_cotPairing_le_ker_deformationδ M)
  have hdual : finrank k (LinearMap.range (cotPairing M))
      ≤ finrank k ((normalFormIdeal M).Cotangent) := by
    calc finrank k (LinearMap.range (cotPairing M))
        ≤ finrank k (Module.Dual k (normalFormIdeal M).Cotangent) :=
          Submodule.finrank_le _
      _ = finrank k ((normalFormIdeal M).Cotangent) := Subspace.dual_finrank_eq
  omega

/-! ## R6 — chain `finrank (m_M.Cotangent)` to `varietyDim Z_M` -/

/-- `ringKrullDim (orbitRing M)` is a finite natural number `n`, equal to `varietyDim Z_M`:
`A = orbitRing M` is a nontrivial finite-type domain over `k`, with `ringKrullDim` bounded by the
ambient `ringKrullDim (MvPolynomial (RepCoord d) k) = card < ⊤` and `≥ 0` (nontrivial). Carries
`[PerfectField k]` (explicit) `[Infinite k]` (from the section). -/
theorem exists_ringKrullDim_orbitRing_eq [PerfectField k] (M : Tuple (k := k) d) :
    ∃ n : ℕ, ringKrullDim (orbitRing M) = (n : WithBot ℕ∞)
      ∧ varietyDim (canonicalCoord d '' orbitRankLocus M) = (n : ℕ∞) := by
  haveI : Nontrivial (orbitRing M) := inferInstance
  -- `0 ≤ dim A ≤ card` so `dim A` is a finite nat
  have hge : (0 : WithBot ℕ∞) ≤ ringKrullDim (orbitRing M) :=
    ringKrullDim_nonneg_of_nontrivial
  have hle : ringKrullDim (orbitRing M) ≤ (Nat.card (RepCoord d) : WithBot ℕ∞) := by
    refine le_trans (ringKrullDim_quotient_le (orbitIdeal M)) ?_
    rw [ringKrullDim_mvPolynomial_finite]
  -- `varietyDim Z_M = (ringKrullDim (orbitRing M)).unbotD 0` (L6.4 + `varietyDim` def)
  have hvar : varietyDim (canonicalCoord d '' orbitRankLocus M)
      = (ringKrullDim (orbitRing M)).unbotD 0 := by
    rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M]; rfl
  -- extract the nat value `n` of `dim A` (finite: `0 ≤ dim A ≤ card`)
  have hbot : ringKrullDim (orbitRing M) ≠ ⊥ := by
    intro h; rw [h] at hge; simp at hge
  have hcardlt : (Nat.card (RepCoord d) : WithBot ℕ∞) < (⊤ : WithBot ℕ∞) :=
    compareOfLessAndEq_eq_lt.mp rfl
  have htop : ringKrullDim (orbitRing M) ≠ (⊤ : WithBot ℕ∞) :=
    ne_of_lt (lt_of_le_of_lt hle hcardlt)
  -- a `WithBot ℕ∞` that is neither `⊥` nor `⊤` is a finite nat
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hmtop : m ≠ ⊤ := fun h ↦ htop (by rw [← hm, h]; rfl)
  have hmcast : ((m.toNat : ℕ∞) : WithBot ℕ∞) = ringKrullDim (orbitRing M) := by
    rw [ENat.coe_toNat hmtop, hm]
  refine ⟨m.toNat, hmcast.symm, ?_⟩
  rw [hvar, ← hmcast, WithBot.unbotD_coe]

/-- **R6 — `finrank k (m_M.Cotangent) = varietyDim Z_M`.** The cotangent finrank equals the variety
dimension: L2a localization collapse (`m_M.Cotangent ≃ CotangentSpace (AtPrime m_M)` in `k`-finrank),
the κ/k bridge (GAP2), M3 (smooth point: `finrank κ (CotangentSpace) = ringKrullDim (AtPrime m_M)`),
GAP3 (`ringKrullDim (AtPrime m_M) = ringKrullDim (orbitRing M)`), and `varietyDim Z_M =
ringKrullDim (orbitRing M)` (L6.4). Carries `[PerfectField k]` (explicit) `[Infinite k]`
(from the section). -/
theorem finrank_cotangent_eq_varietyDim [PerfectField k] (M : Tuple (k := k) d) :
    (finrank k ((normalFormIdeal M).Cotangent) : ℕ∞)
      = varietyDim (canonicalCoord d '' orbitRankLocus M) := by
  haveI : (normalFormIdeal M).IsMaximal := orbitPointIdeal_isMaximal M 1
  haveI : (orbitIdeal M).IsPrime := isPrime_vanishingIdeal_orbitSet M
  haveI : Algebra.IsSmoothAt k (normalFormIdeal M) := isSmoothAt_normalFormIdeal (k := k) M
  obtain ⟨n, hdimA, hvar⟩ := exists_ringKrullDim_orbitRing_eq M
  -- GAP3: `ringKrullDim (AtPrime m_M) = ringKrullDim (orbitRing M) = n`
  have hdimLoc : ringKrullDim (Localization.AtPrime (normalFormIdeal M)) = (n : WithBot ℕ∞) := by
    rw [ringKrullDim_localizationAtPrime_isMaximal_eq_fintype (orbitIdeal M) (normalFormIdeal M),
      hdimA]
  -- M3: `finrank κ (CotangentSpace (AtPrime m_M)) = n`
  have hM3 : finrank (IsLocalRing.ResidueField (Localization.AtPrime (normalFormIdeal M)))
      (IsLocalRing.CotangentSpace (Localization.AtPrime (normalFormIdeal M))) = n :=
    finrank_cotangentSpace_eq_of_isSmoothAt (k := k) (A := orbitRing M) (normalFormIdeal M) hdimLoc
  -- κ/k bridge (GAP2): `finrank k (CotangentSpace) = finrank κ (CotangentSpace)`
  haveI : IsScalarTower k (IsLocalRing.ResidueField (Localization.AtPrime (normalFormIdeal M)))
      (IsLocalRing.CotangentSpace (Localization.AtPrime (normalFormIdeal M))) := by
    refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
    rw [IsScalarTower.algebraMap_apply k (Localization.AtPrime (normalFormIdeal M))
        (IsLocalRing.ResidueField (Localization.AtPrime (normalFormIdeal M))) r,
      algebraMap_smul, algebraMap_smul]
  have hbridge : finrank k (IsLocalRing.CotangentSpace (Localization.AtPrime (normalFormIdeal M)))
      = finrank (IsLocalRing.ResidueField (Localization.AtPrime (normalFormIdeal M)))
        (IsLocalRing.CotangentSpace (Localization.AtPrime (normalFormIdeal M))) :=
    finrank_eq_finrank_of_residueField_equiv (residueFieldAtPrimeNormalFormEquiv M)
  -- L2a collapse: `finrank k (m_M.Cotangent) = finrank k (CotangentSpace (AtPrime m_M))`
  have hcollapse : finrank k ((normalFormIdeal M).Cotangent)
      = finrank k (IsLocalRing.CotangentSpace (Localization.AtPrime (normalFormIdeal M))) :=
    (Ideal.finrank_cotangentSpace_localization_eq_cotangent (k := k) (normalFormIdeal M)).symm
  rw [hcollapse, hbridge, hM3, hvar]

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
