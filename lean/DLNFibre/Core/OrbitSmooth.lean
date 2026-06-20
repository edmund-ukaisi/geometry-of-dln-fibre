import DLNFibre.Core.OrbitClosure
import DLNFibre.Core.OrbitVariety
import DLNFibre.Core.OrbitPullbackDim
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# `DLNFibre.Core.OrbitSmooth` — smoothness of the orbit closure at the normal-form point (L3)

The orbit-closure variety `Z_M = orbitRankLocus M = Ō_M` is smooth at the orbit normal-form point
`M`: the coordinate ring `A = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(canonicalCoord '' Z_M)`
is formally smooth over `k` at the maximal ideal `m_M = ker(eval at canonicalCoord M)`.

The proof is **homogeneity + Route DENSE** (thread 34/18): the `G_d`-action acts on `Z_M` with a
dense orbit `O_M`; generic smoothness over the perfect (algebraically closed) field `k` produces a
smooth closed point, and the dense orbit guarantees one such smooth point is an orbit point;
transporting it along the `G_d`-action (a `k`-algebra automorphism of `A`) to the normal-form point
`M` gives `IsSmoothAt k m_M`.

**Typeclass.** `[Field k] [IsAlgClosed k]` (⟹ `PerfectField k`, Jacobson, `k`-points = closed
points). **Dependency rule:** `Core` only.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## L3.0 — the `G_d`-action as a `k`-algebra automorphism of the coordinate ring

`baseChangePullback P` (from `OrbitClosure`) is `aeval (baseChangeSub P)`, the coordinate-ring
incarnation of the linear change of variables `A ↦ P • A`. It is invertible: its inverse is the
pullback by `P⁻¹`, witnessed by the composition law `pullback P ∘ pullback Q = pullback (Q * P)`
(pullbacks are contravariant). -/

/-- The pullback composition law (contravariant): `baseChangePullback P (baseChangePullback Q f)
= baseChangePullback (Q * P) f`. Both polynomials evaluate to the same value at every point `x`
(`eval_baseChangePullback`, chasing the `G_d`-shift `shift_Q ∘ shift_P = shift_{Q*P}`), so they are
equal by `MvPolynomial.funext` over the infinite field `k`. -/
theorem baseChangePullback_comp [Infinite k] {d : Fin (N + 1) → ℕ}
    (P Q : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
    baseChangePullback P (baseChangePullback Q f) = baseChangePullback (Q * P) f := by
  refine MvPolynomial.funext (fun x ↦ ?_)
  rw [eval_baseChangePullback, eval_baseChangePullback, eval_baseChangePullback]
  -- `shift_Q (shift_P x) = shift_{Q*P} x`: chase the `G_d`-action through `canonicalCoord`/`symm`
  rw [Equiv.symm_apply_apply, SemigroupAction.mul_smul]

/-- The identity base change pulls back to the identity: `baseChangePullback 1 = id`. The shift by
`1` is the identity (`one_smul`), so `eval x (pullback 1 f) = eval x f` for all `x`. -/
theorem baseChangePullback_one [Infinite k] {d : Fin (N + 1) → ℕ}
    (f : MvPolynomial (RepCoord d) k) :
    baseChangePullback (1 : BaseChangeGroup (k := k) d) f = f := by
  refine MvPolynomial.funext (fun x ↦ ?_)
  rw [eval_baseChangePullback, one_smul, Equiv.apply_symm_apply]

/-- **L3.0 — the `G_d`-action as a `k`-algebra automorphism.** `baseChangeAlgEquiv P` is the
coordinate-ring automorphism `aeval (baseChangeSub P)` (= the change of variables `A ↦ P • A`), with
inverse the pullback by `P⁻¹` (the composition law `pullback P ∘ pullback Q = pullback (Q*P)` and
`pullback 1 = id`). -/
noncomputable def baseChangeAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ}
    (P : BaseChangeGroup (k := k) d) :
    MvPolynomial (RepCoord d) k ≃ₐ[k] MvPolynomial (RepCoord d) k :=
  AlgEquiv.ofAlgHom (baseChangePullback P) (baseChangePullback P⁻¹)
    (by refine AlgHom.ext (fun f ↦ ?_)
        rw [AlgHom.comp_apply, AlgHom.id_apply, baseChangePullback_comp, inv_mul_cancel,
          baseChangePullback_one])
    (by refine AlgHom.ext (fun f ↦ ?_)
        rw [AlgHom.comp_apply, AlgHom.id_apply, baseChangePullback_comp, mul_inv_cancel,
          baseChangePullback_one])

@[simp] theorem baseChangeAlgEquiv_apply [Infinite k] {d : Fin (N + 1) → ℕ}
    (P : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
    baseChangeAlgEquiv P f = baseChangePullback P f := rfl

/-! ## The coordinate ring `A` of the orbit closure and the descended `G_d`-automorphism

`A = MvPolynomial (RepCoord d) k ⧸ I` with `I = vanishingIdeal (orbitSet M)`. By L6.4
(`vanishingIdeal_orbitRankLocus_eq_orbitSet`) this is the coordinate ring of the rank locus
`Z_M = canonicalCoord '' orbitRankLocus M`; by L1 (`isPrime_vanishingIdeal_orbitSet`) it is a
domain. The `G_d`-automorphism `baseChangeAlgEquiv P` stabilises `I`, descending to `A ≃ₐ[k] A`. -/

/-- The vanishing ideal `I = vanishingIdeal (orbitSet M)` we quotient by — the defining ideal of the
orbit closure `Z_M` (L6.4 identifies it with the rank-locus ideal). -/
noncomputable def orbitIdeal {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    Ideal (MvPolynomial (RepCoord d) k) :=
  MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet M)

/-- The coordinate ring `A = MvPolynomial (RepCoord d) k ⧸ I` of the orbit closure `Z_M`. -/
abbrev orbitRing {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) : Type u :=
  MvPolynomial (RepCoord d) k ⧸ orbitIdeal M

/-- `A` is a **domain**: `I = vanishingIdeal (orbitSet M)` is prime (L1, orbit irreducible). -/
instance orbitRing_isDomain [IsAlgClosed k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    IsDomain (orbitRing M) :=
  haveI : (orbitIdeal M).IsPrime := isPrime_vanishingIdeal_orbitSet M
  Ideal.Quotient.isDomain (orbitIdeal M)

/-- The orbit ideal is `G_d`-stable: `baseChangeAlgEquiv P` maps `I` into `I`
(`baseChangePullback_mem_vanishingIdeal_orbitSet`). -/
theorem orbitIdeal_map_le [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) :
    (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _)
      ≤ orbitIdeal M := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap]
  exact baseChangePullback_mem_vanishingIdeal_orbitSet M P hf

/-- The orbit ideal is **invariant** under `baseChangeAlgEquiv P`: `I.map (α_P) = I`. Both `α_P` and
its inverse `α_{P⁻¹}` map `I` into `I`, and `map` of an equiv is monotone with a `map`-inverse. -/
theorem orbitIdeal_map_eq [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) :
    (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _)
      = orbitIdeal M := by
  refine le_antisymm (orbitIdeal_map_le M P) ?_
  -- `I ≤ I.map α_P` ⟸ `I.map α_{P⁻¹} ≤ I` pushed through `α_P` (an equiv)
  have hinv : (orbitIdeal M).map
      (baseChangeAlgEquiv P⁻¹ : MvPolynomial (RepCoord d) k →+* _) ≤ orbitIdeal M :=
    orbitIdeal_map_le M P⁻¹
  calc orbitIdeal M
      = ((orbitIdeal M).map
          (baseChangeAlgEquiv P⁻¹ : MvPolynomial (RepCoord d) k →+* _)).map
          (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _) := by
        rw [Ideal.map_map]
        refine (Ideal.map_id (orbitIdeal M)).symm.trans ?_
        congr 1
        refine RingHom.ext (fun f ↦ ?_)
        rw [RingHom.id_apply, RingHom.comp_apply]
        change f = baseChangePullback P (baseChangePullback P⁻¹ f)
        rw [baseChangePullback_comp, inv_mul_cancel, baseChangePullback_one]
    _ ≤ (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _) :=
        Ideal.map_mono hinv

/-- **The descended `G_d`-automorphism** `α_P : A ≃ₐ[k] A` of the orbit-closure coordinate ring,
from the polynomial-ring automorphism `baseChangeAlgEquiv P` (which stabilises `I`,
`orbitIdeal_map_eq`). -/
noncomputable def orbitRingAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) :
    orbitRing M ≃ₐ[k] orbitRing M :=
  Ideal.quotientEquivAlg (orbitIdeal M) (orbitIdeal M) (baseChangeAlgEquiv P)
    (orbitIdeal_map_eq M P).symm

/-- `α_P` on a residue class is the residue class of the pullback: `α_P (mk f) = mk (pullback P f)`.
-/
@[simp] theorem orbitRingAlgEquiv_mk [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
    orbitRingAlgEquiv M P (Ideal.Quotient.mk (orbitIdeal M) f)
      = Ideal.Quotient.mk (orbitIdeal M) (baseChangePullback P f) :=
  rfl

/-! ## The orbit `k`-points and their point ideals `m_{P•M}` in `A`

For `P : G_d`, the orbit point `canonicalCoord (P • M) ∈ orbitSet M` evaluates every element of
`I = vanishingIdeal (orbitSet M)` to `0`, so `eval (canonicalCoord (P • M)) : R → k` descends to a
`k`-algebra hom `A → k`. Its kernel `m_{P•M}` is a maximal ideal of `A` (residue field `k`), and the
`G_d`-automorphism `α_P` carries `m_{P•M}` to `m_M` (the normal-form point ideal). -/

/-- The orbit point `canonicalCoord (P • M)` lies in `orbitSet M`. -/
theorem canonicalCoord_smul_mem_orbitSet {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) : canonicalCoord d (P • M) ∈ orbitSet M :=
  ⟨P • M, ⟨P, rfl⟩, rfl⟩

/-- Evaluation at the orbit point `canonicalCoord (P • M)` kills the orbit ideal `I`: every `f ∈ I`
vanishes at every orbit point. -/
theorem eval_orbitPoint_mem_orbitIdeal {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) {f : MvPolynomial (RepCoord d) k} (hf : f ∈ orbitIdeal M) :
    MvPolynomial.eval (canonicalCoord d (P • M)) f = 0 := by
  rw [orbitIdeal, MvPolynomial.mem_vanishingIdeal_iff] at hf
  have := hf _ (canonicalCoord_smul_mem_orbitSet M P)
  rwa [MvPolynomial.aeval_eq_eval] at this

/-- The descended **evaluation** `A → k` at the orbit point `canonicalCoord (P • M)`: the
`k`-algebra hom factoring `eval (canonicalCoord (P • M))` through `A = R ⧸ I` (which kills `I`). -/
noncomputable def orbitEval {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) : orbitRing M →ₐ[k] k :=
  Ideal.Quotient.liftₐ (orbitIdeal M)
    (MvPolynomial.aeval (R := k) (canonicalCoord d (P • M)))
    (fun f hf ↦ by rw [MvPolynomial.aeval_eq_eval]; exact eval_orbitPoint_mem_orbitIdeal M P hf)

/-- `orbitEval` on a residue class is evaluation of the representative. -/
@[simp] theorem orbitEval_mk {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
    orbitEval M P (Ideal.Quotient.mk (orbitIdeal M) f)
      = MvPolynomial.eval (canonicalCoord d (P • M)) f := by
  rw [orbitEval, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact congrFun (MvPolynomial.aeval_eq_eval (canonicalCoord d (P • M))) f

/-- The **point ideal** `m_{P•M} = ker (orbitEval M P)` of the orbit `k`-point
`canonicalCoord (P•M)` in `A`. The normal-form point ideal is `m_M = orbitPointIdeal M 1`. -/
noncomputable def orbitPointIdeal {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) : Ideal (orbitRing M) :=
  RingHom.ker (orbitEval M P).toRingHom

/-- The normal-form point ideal `m_M = ker (orbitEval M 1)` (the orbit point `canonicalCoord M`). -/
noncomputable abbrev normalFormIdeal {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    Ideal (orbitRing M) :=
  orbitPointIdeal M 1

/-- `m_{P•M}` is **maximal**: the kernel of the surjective `k`-algebra hom `orbitEval M P : A → k`
onto a field (`orbitEval` is split by `algebraMap k A`). -/
instance orbitPointIdeal_isMaximal {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) : (orbitPointIdeal M P).IsMaximal := by
  have hsurj : Function.Surjective (orbitEval M P).toRingHom := fun y ↦
    ⟨algebraMap k (orbitRing M) y, (orbitEval M P).commutes y⟩
  rw [orbitPointIdeal]
  exact (RingHom.ker_isMaximal_of_surjective _ hsurj)

instance orbitPointIdeal_isPrime {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) : (orbitPointIdeal M P).IsPrime :=
  (orbitPointIdeal_isMaximal M P).isPrime

/-- **L3.0 transport — `orbitEval M 1 ∘ α_P = orbitEval M P`.** The normal-form evaluation
precomposed with the `G_d`-automorphism `α_P` is evaluation at the orbit point `P • M`: chasing
the shift `eval (canonicalCoord M) ∘ pullback P = eval (canonicalCoord (P•M))`. -/
theorem orbitEval_comp_orbitRingAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) :
    (orbitEval M 1).comp (orbitRingAlgEquiv M P).toAlgHom = orbitEval M P := by
  refine AlgHom.ext (fun a ↦ ?_)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [AlgHom.comp_apply]
  change orbitEval M 1 (orbitRingAlgEquiv M P (Ideal.Quotient.mk (orbitIdeal M) f))
    = orbitEval M P (Ideal.Quotient.mk (orbitIdeal M) f)
  rw [orbitRingAlgEquiv_mk, orbitEval_mk, orbitEval_mk, one_smul,
    show MvPolynomial.eval (canonicalCoord d M) (baseChangePullback P f)
      = MvPolynomial.eval (canonicalCoord d (P • (canonicalCoord d).symm (canonicalCoord d M)))
        f from eval_baseChangePullback P (canonicalCoord d M) f,
    Equiv.symm_apply_apply]

/-- **L3.0 transport, ideal form — `m_{P•M} = comap α_P (m_M)`.** The point ideal of the orbit point
`P • M` is the `α_P`-preimage of the normal-form point ideal `m_M`. -/
theorem orbitPointIdeal_eq_comap [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) :
    orbitPointIdeal M P
      = (normalFormIdeal M).comap (orbitRingAlgEquiv M P).toAlgHom.toRingHom := by
  have hcomp : (orbitEval M P).toRingHom
      = (orbitEval M 1).toRingHom.comp (orbitRingAlgEquiv M P).toAlgHom.toRingHom := by
    refine RingHom.ext (fun a ↦ ?_)
    rw [RingHom.comp_apply]
    exact congrFun (congrArg DFunLike.coe (orbitEval_comp_orbitRingAlgEquiv M P).symm) a
  rw [orbitPointIdeal, normalFormIdeal, orbitPointIdeal, hcomp, ← RingHom.comap_ker]

/-! ## L3.1 — smoothness is `G_d`-stable

`m_{P•M} = comap α_P (m_M)` and `α_P : A ≃ₐ[k] A`, so the localizations `AtPrime m_{P•M}` and
`AtPrime m_M` are `k`-algebra isomorphic, and `Algebra.FormallySmooth.iff_of_equiv` transfers
`IsSmoothAt`. -/

/-- The `α_P`-image of `m_{P•M}.primeCompl` is `m_M.primeCompl`: `α_P` carries the complement of
`m_{P•M} = comap α_P m_M` onto the complement of `m_M`. -/
theorem map_orbitPointIdeal_primeCompl [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) :
    (orbitPointIdeal M P).primeCompl.map
        (orbitRingAlgEquiv M P : orbitRing M ≃+* orbitRing M).toMonoidHom
      = (normalFormIdeal M).primeCompl := by
  have hcomap := orbitPointIdeal_eq_comap M P
  -- membership in `m_{P•M}` is membership of the `α_P`-image in `m_M`
  have hmem : ∀ x : orbitRing M,
      x ∈ orbitPointIdeal M P ↔ orbitRingAlgEquiv M P x ∈ normalFormIdeal M := by
    intro x; rw [hcomap, Ideal.mem_comap]; rfl
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- `x ∉ m_{P•M}`, so `α_P x ∉ m_M`
    have : orbitRingAlgEquiv M P x ∉ normalFormIdeal M := fun h ↦ hx ((hmem x).mpr h)
    simpa using this
  · intro hy
    refine ⟨(orbitRingAlgEquiv M P).symm y, ?_, by simp⟩
    -- `α_P⁻¹ y ∉ m_{P•M}`, since `α_P (α_P⁻¹ y) = y ∉ m_M`
    intro h
    exact hy (by simpa [(hmem _).mp h] using (hmem ((orbitRingAlgEquiv M P).symm y)).mp h)

/-- The `k`-algebra equivalence `AtPrime m_{P•M} ≃ₐ[k] AtPrime m_M` induced by `α_P`. -/
noncomputable def localizationAtPrimeAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) (P : BaseChangeGroup (k := k) d) :
    Localization.AtPrime (orbitPointIdeal M P) ≃ₐ[k] Localization.AtPrime (normalFormIdeal M) :=
  AlgEquiv.ofRingEquiv
    (f := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (orbitPointIdeal M P))
      (Localization.AtPrime (normalFormIdeal M))
      (orbitRingAlgEquiv M P : orbitRing M ≃+* orbitRing M) (map_orbitPointIdeal_primeCompl M P))
    (fun r ↦ by
      rw [show (algebraMap k (Localization.AtPrime (orbitPointIdeal M P))) r
          = algebraMap (orbitRing M) (Localization.AtPrime (orbitPointIdeal M P))
            (algebraMap k (orbitRing M) r) from
            (IsScalarTower.algebraMap_apply k (orbitRing M) _ r),
        IsLocalization.ringEquivOfRingEquiv_eq, AlgEquiv.coe_ringEquiv,
        AlgEquiv.commutes,
        ← IsScalarTower.algebraMap_apply k (orbitRing M) _ r])

/-- **L3.1 — smoothness is `G_d`-stable.** `IsSmoothAt k m_{P•M} ↔ IsSmoothAt k m_M`: the
localizations are `k`-algebra isomorphic (`localizationAtPrimeAlgEquiv`), and
`FormallySmooth.iff_of_equiv` transfers formal smoothness. -/
theorem isSmoothAt_orbitPointIdeal_iff [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) :
    Algebra.IsSmoothAt k (orbitPointIdeal M P) ↔ Algebra.IsSmoothAt k (normalFormIdeal M) :=
  Algebra.FormallySmooth.iff_of_equiv (localizationAtPrimeAlgEquiv M P)

/-! ## L3.3 — the orbit's closed points are dense in `Spec A` (Route DENSE)

The orbit `k`-points `canonicalCoord (P • M)` map to the maximal ideals `orbitPointIdeal M P` of
`A`. Their set `orbitSpecSet` is **dense** in `PrimeSpectrum A`: a class `mk g` vanishing at every
orbit point has `g ∈ vanishingIdeal (orbitSet M) = I`, so `mk g = 0`; the vanishing ideal of the
orbit points is `⊥`, and `A` is reduced (domain), so the closure is everything. -/

/-- The set of orbit `k`-points in `Spec A`: the prime spectrum points whose ideal is some
`orbitPointIdeal M P`. -/
def orbitSpecSet {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) : Set (PrimeSpectrum (orbitRing M)) :=
  { p | ∃ P : BaseChangeGroup (k := k) d, p.asIdeal = orbitPointIdeal M P }

/-- **The vanishing ideal of the orbit closed points is `⊥`** (Route DENSE core, a rewrite of L6's
`vanishingIdeal (orbitSet M)`-equality through the quotient). A class `mk g` lying in every orbit
point ideal means `g` vanishes on every orbit point, i.e. `g ∈ I`, i.e. `mk g = 0`. -/
theorem vanishingIdeal_orbitSpecSet_eq_bot [Infinite k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    PrimeSpectrum.vanishingIdeal (orbitSpecSet M) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [PrimeSpectrum.mem_vanishingIdeal] at ha
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  -- `mk g ∈ orbitPointIdeal M P` for all `P`, i.e. `eval (canonicalCoord (P•M)) g = 0` for all `P`
  have hg : ∀ P : BaseChangeGroup (k := k) d,
      MvPolynomial.eval (canonicalCoord d (P • M)) g = 0 := by
    intro P
    have hmem := ha ⟨orbitPointIdeal M P, inferInstance⟩ ⟨P, rfl⟩
    have : orbitEval M P (Ideal.Quotient.mk (orbitIdeal M) g) = 0 := hmem
    rwa [orbitEval_mk] at this
  -- so `g` vanishes on `orbitSet M`, hence `g ∈ I`, hence `mk g = 0`
  have hgI : g ∈ orbitIdeal M := by
    rw [orbitIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro y ⟨A, ⟨P, rfl⟩, rfl⟩
    rw [MvPolynomial.aeval_eq_eval]
    exact hg P
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  exact hgI

/-- **L3.3 — the orbit closed points are dense in `Spec A`.** Their vanishing ideal is `⊥`
(`vanishingIdeal_orbitSpecSet_eq_bot`) and `A` is reduced (a domain), so the closure is `univ`. -/
theorem dense_orbitSpecSet [IsAlgClosed k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    Dense (orbitSpecSet M) := by
  rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    vanishingIdeal_orbitSpecSet_eq_bot M, PrimeSpectrum.zeroLocus_bot]

/-! ## L3.2 — the `Spec` model and its instances

`A = orbitRing M` is a finitely-presented `k`-algebra (Noetherian polynomial quotient), Jacobson
(finite type over a field), reduced (a domain). These feed the generic-smoothness machinery. The
structure morphism `f = Spec.map (algebraMap k A) : Spec(.of A) ⟶ Spec(.of k)` is locally of finite
presentation and finite type; `Spec(.of A)` is reduced and Jacobson. -/

/-- `A = orbitRing M` is a **finitely-presented** `k`-algebra: `MvPolynomial (RepCoord d) k` is
finitely presented over `k`, and the orbit ideal `I` is finitely generated (the polynomial ring is
Noetherian), so the quotient is finitely presented (`FinitePresentation.quotient`). -/
instance orbitRing_finitePresentation {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    Algebra.FinitePresentation k (orbitRing M) :=
  Algebra.FinitePresentation.quotient (IsNoetherian.noetherian (orbitIdeal M))

/-- `A = orbitRing M` is a **Jacobson** ring: a finitely-generated algebra over the field `k`
(`MvPolynomial.isJacobsonRing` for the polynomial ring over the Jacobson field `k`,
`isJacobsonRing_quotient` for the quotient). -/
instance orbitRing_isJacobsonRing {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    IsJacobsonRing (orbitRing M) :=
  isJacobsonRing_quotient (I := orbitIdeal M)

section SpecModel

variable [IsAlgClosed k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)

open AlgebraicGeometry CategoryTheory

/-- The `Spec`-model of the orbit closure: `X = Spec(.of A)`. -/
noncomputable abbrev orbitScheme : Scheme := Spec (.of (orbitRing M))

/-- The structure morphism `f = Spec.map (algebraMap k A) : Spec(.of A) ⟶ Spec(.of k)`. -/
noncomputable abbrev orbitSchemeHom : orbitScheme M ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (orbitRing M)))

/-- The structure morphism is **locally of finite presentation** (`A` finitely presented over
`k`, via `HasRingHomProperty.Spec_iff`). -/
instance orbitSchemeHom_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (orbitSchemeHom M) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  change (algebraMap k (orbitRing M)).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  infer_instance

/-- The structure morphism is **locally of finite type** (from finite presentation). -/
instance orbitSchemeHom_locallyOfFiniteType : LocallyOfFiniteType (orbitSchemeHom M) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap k (orbitRing M)).FiniteType
  rw [RingHom.finiteType_algebraMap]
  infer_instance

/-- **L3.2 skeleton.** Sanity-check (sorry-free) that every instance the generic-smoothness machine
needs resolves on the `Spec` model: `X` reduced + Jacobson, `f` locally of finite presentation +
finite type. -/
example : IsReduced (orbitScheme M) ∧ JacobsonSpace (orbitScheme M)
    ∧ LocallyOfFinitePresentation (orbitSchemeHom M)
    ∧ LocallyOfFiniteType (orbitSchemeHom M) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-! ## L3.4 — assembly: a smooth orbit point exists, transported to the normal-form point

The scheme smooth locus is dense (`dense_smoothLocus_of_perfectField`, perfect `k` + reduced `X`)
and open; the orbit closed points are dense (`dense_orbitSpecSet`); their intersection is nonempty
(`Dense.inter_open_nonempty`) — a smooth orbit `k`-point. The scheme↔ring smooth-point dictionary
(`orbitScheme_mem_smoothLocus_iff_isSmoothAt`) makes it `IsSmoothAt k (orbitPointIdeal M P)`;
the `G_d`-transport (`isSmoothAt_orbitPointIdeal_iff`) carries it to `m_M`. -/

omit [IsAlgClosed k] in
/-- The prime of `k` under the structure map is `⊥` (`k` is a field). -/
theorem comap_algebraMap_eq_bot (p : PrimeSpectrum (orbitRing M)) :
    (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap k (orbitRing M))).hom p).asIdeal = ⊥ := by
  rcases Ideal.eq_bot_or_top (PrimeSpectrum.comap
      (CommRingCat.ofHom (algebraMap k (orbitRing M))).hom p).asIdeal with h | h
  · exact h
  · exact absurd h
      (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap k (orbitRing M))).hom p).2.ne_top

omit [IsAlgClosed k] in
/-- The localized structure map `localRingHom (comap p) p (algebraMap k A)` is formally smooth iff
`A` is formally smooth at `p`. Its source `AtPrime (comap p)` is `k` (the prime is `⊥`, `k` a field;
`IsLocalization.atUnits`), so the localized map is `algebraMap k (AtPrime p)` up to a source iso,
whose `FormallySmooth` is `Algebra.IsSmoothAt k p` (`formallySmooth_algebraMap`). -/
theorem localRingHom_formallySmooth_iff (p : PrimeSpectrum (orbitRing M)) :
    (Localization.localRingHom
        (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap k (orbitRing M))).hom p).asIdeal
        p.asIdeal (algebraMap k (orbitRing M)) rfl).FormallySmooth ↔
      Algebra.IsSmoothAt k p.asIdeal := by
  haveI hqp : (PrimeSpectrum.comap
      (CommRingCat.ofHom (algebraMap k (orbitRing M))).hom p).asIdeal.IsPrime :=
    (PrimeSpectrum.comap _ p).2
  -- `q = comap p = ⊥`; every nonzero element of the field `k` is a unit, so `k ≃ₐ[k] AtPrime q`
  have hunits : (PrimeSpectrum.comap
      (CommRingCat.ofHom (algebraMap k (orbitRing M))).hom p).asIdeal.primeCompl
        ≤ IsUnit.submonoid k := by
    intro x hx
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, comap_algebraMap_eq_bot M p, Ideal.mem_bot] at hx
    simp only [IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.mpr hx
  let e : k ≃ₐ[k] Localization.AtPrime (PrimeSpectrum.comap
      (CommRingCat.ofHom (algebraMap k (orbitRing M))).hom p).asIdeal :=
    IsLocalization.atUnits k _ hunits
  -- the arrow iso: source iso `e.symm`, target identity; square commutes by `localRingHom_to_map`
  have harrow : Arrow.mk (CommRingCat.ofHom (Localization.localRingHom (PrimeSpectrum.comap
        (CommRingCat.ofHom (algebraMap k (orbitRing M))).hom p).asIdeal p.asIdeal
        (algebraMap k (orbitRing M)) rfl))
      ≅ Arrow.mk (CommRingCat.ofHom (algebraMap k (Localization.AtPrime p.asIdeal))) :=
    Arrow.isoMk (e.symm.toRingEquiv.toCommRingCatIso) (Iso.refl _) (by
      refine CommRingCat.hom_ext (RingHom.ext (fun z ↦ ?_))
      -- square at `z = e y` : `algebraMap k (AtPrime p) (e.symm (e y)) = localRingHom (e y)`
      obtain ⟨y, rfl⟩ : ∃ y : k, e y = z := ⟨e.symm z, e.apply_symm_apply z⟩
      change (algebraMap k (Localization.AtPrime p.asIdeal)) (e.symm (e y))
        = Localization.localRingHom _ p.asIdeal (algebraMap k (orbitRing M)) rfl (e y)
      rw [AlgEquiv.symm_apply_apply]
      have hey : e y = algebraMap k (Localization.AtPrime
          (Ideal.comap (algebraMap k (orbitRing M)) p.asIdeal)) y := rfl
      rw [hey, Localization.localRingHom_to_map,
        ← IsScalarTower.algebraMap_apply k (orbitRing M) (Localization.AtPrime p.asIdeal) y])
  have hbridge := RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff harrow
  simp only [CommRingCat.hom_ofHom] at hbridge ⊢
  rw [hbridge, RingHom.formallySmooth_algebraMap]

omit [IsAlgClosed k] in
/-- **The scheme↔ring smooth-point dictionary** (affine bridge via the stalk-map ↔ localized-map
iso). A point `p` of `Spec A` is in the scheme smooth locus of the structure morphism iff `A` is
formally smooth at `p` over `k`. The stalk map of `Spec.map (algebraMap k A)` at `p` is arrow-iso
to `Localization.localRingHom ⊥ p (algebraMap k A)` (`Scheme.arrowStalkMapSpecIso`); since `k` is
a field, the source `AtPrime ⊥` is `k`, so the map is `algebraMap k (AtPrime p)`, whose formal
smoothness is `Algebra.IsSmoothAt k p`. -/
theorem orbitScheme_mem_smoothLocus_iff_isSmoothAt (p : PrimeSpectrum (orbitRing M)) :
    (p : orbitScheme M) ∈ (orbitSchemeHom M).smoothLocus ↔
      Algebra.IsSmoothAt k p.asIdeal := by
  rw [show ((p : orbitScheme M) ∈ (orbitSchemeHom M).smoothLocus)
      = ((orbitSchemeHom M).stalkMap (p : orbitScheme M)).hom.FormallySmooth from
        propext Scheme.Hom.mem_smoothLocus]
  -- the stalk map is arrow-iso to `localRingHom ⊥ p (algebraMap k A)`
  rw [RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap k (orbitRing M))) p)]
  exact localRingHom_formallySmooth_iff M p

/-- **A smooth orbit `k`-point exists.** The (dense, open) scheme smooth locus meets the dense orbit
closed points, giving a smooth point that is an orbit point `orbitPointIdeal M P`. -/
theorem exists_orbitPointIdeal_isSmoothAt :
    ∃ P : BaseChangeGroup (k := k) d, Algebra.IsSmoothAt k (orbitPointIdeal M P) := by
  have hSmDense : Dense ((orbitSchemeHom M).smoothLocus : Set (orbitScheme M)) :=
    Scheme.Hom.dense_smoothLocus_of_perfectField (orbitSchemeHom M)
  obtain ⟨x, hxSmooth, P, hxP⟩ :=
    (dense_orbitSpecSet M).inter_open_nonempty _ (orbitSchemeHom M).smoothLocus.2 hSmDense.nonempty
  refine ⟨P, ?_⟩
  have hring : Algebra.IsSmoothAt k x.asIdeal :=
    (orbitScheme_mem_smoothLocus_iff_isSmoothAt M x).mp hxSmooth
  -- transport `IsSmoothAt` along `x.asIdeal = orbitPointIdeal M P` (`AtPrime` depends only on the
  -- ideal), avoiding the prime-instance motive obstruction
  obtain ⟨x, hxprime⟩ := x
  subst hxP
  exact hring

/-- **L3 headline — `Z_M` is smooth at the orbit normal-form point `M`.** `IsSmoothAt k m_M`: there
is a smooth orbit `k`-point (`exists_orbitPointIdeal_isSmoothAt`), and the `G_d`-action transports
its smoothness to the normal-form point ideal `m_M = orbitPointIdeal M 1`
(`isSmoothAt_orbitPointIdeal_iff`). -/
theorem isSmoothAt_normalFormIdeal : Algebra.IsSmoothAt k (normalFormIdeal M) := by
  obtain ⟨P, hP⟩ := exists_orbitPointIdeal_isSmoothAt M
  exact (isSmoothAt_orbitPointIdeal_iff M P).mp hP

/-- **The residue field at `m_M` is `k`** (`κ(m_M) = k`). The normal-form point `M` is a
`k`-rational point: the evaluation `orbitEval M 1 : A → k` is a surjective `k`-algebra hom with
kernel `m_M`, so the first isomorphism theorem gives `A ⧸ m_M ≃ₐ[k] k`. Consumed by M3/L2a
(cotangent at a `k`-rational point). -/
noncomputable def residueFieldNormalFormEquiv : (orbitRing M ⧸ normalFormIdeal M) ≃ₐ[k] k :=
  Ideal.quotientKerAlgEquivOfSurjective
    (f := orbitEval M 1) (fun y ↦ ⟨algebraMap k (orbitRing M) y, (orbitEval M 1).commutes y⟩)

end SpecModel

section Witness

/-! ## Non-vacuity witness

The `G_d`-action objects (L3.0/L3.1, needing only `[Infinite k]`) are exercised on the concrete
`(2,2,2)/ℚ` tuple `tupleWitnessQ` (`ℚ` is infinite). The smoothness headline itself needs
`[IsAlgClosed k]`, not instantiable at `ℚ`; the algebraic objects it transports along are. -/

/-- The `G_d`-automorphism `α_1 = id` on the orbit ring of the `(2,2,2)/ℚ` witness: the normal-form
evaluation is `G_d`-invariant under the identity base change (`orbitEval_comp_orbitRingAlgEquiv` at
`P = 1`). The L3.0 transport objects are non-vacuous on a real matrix tuple. -/
example : (orbitEval (k := ℚ) tupleWitnessQ 1).comp
    (orbitRingAlgEquiv (k := ℚ) tupleWitnessQ 1).toAlgHom = orbitEval tupleWitnessQ 1 :=
  orbitEval_comp_orbitRingAlgEquiv tupleWitnessQ 1

/-- The normal-form point ideal of the `(2,2,2)/ℚ` witness is maximal: the orbit-ring point ideal
construction is non-vacuous on a concrete tuple. -/
example : (normalFormIdeal (k := ℚ) tupleWitnessQ).IsMaximal :=
  orbitPointIdeal_isMaximal tupleWitnessQ 1

end Witness

end DLNFibre.Core
