import DLNFibre.Core.OrbitCodim
import DLNFibre.Core.Orbit
import DLNFibre.Core.NullstellensatzCodim
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# `DLNFibre.Core.OrbitVariety` — the `G_d`-orbit `O_M` is Zariski-irreducible (L1)

The orbit `O_M = G_d · M` (a point set in `RepCoord d → k`) is **Zariski-irreducible**, i.e. its
vanishing ideal is **prime**: `O_M` is the image of the irreducible group `G_d = ∏_v GL_{d_v}` under
the polynomial orbit map, so `vanishingIdeal O_M = ker μ_M^*` is a kernel into a domain. The
headline is about the orbit *itself* (in general only locally closed); a prime vanishing ideal
certifies that its Zariski *closure* is an irreducible variety. The orbit-closure-equality `closure
O_M =
orbitRankLocus` is the separate L6 box-move sub-ladder, not this module. The foundation L1 that the
pivot chart L3.0, L6, and the codimension bridge L0 stand on.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The orbit `O_M` as a point set, and the orbit map `μ_M` -/

/-- The **orbit** of `M`: the set of all `canonicalCoord`-flattenings of `P • M`, `P` ranging over
`G_d`. A point set in `RepCoord d → k`. -/
def orbitSet {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) : Set (RepCoord d → k) :=
  canonicalCoord d '' { A | ∃ P : BaseChangeGroup (k := k) d, P • M = A }

/-- The **orbit map** `μ_M : G_d → (RepCoord d → k)`, `P ↦ canonicalCoord (P • M)`. -/
noncomputable def orbitMap {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    BaseChangeGroup (k := k) d → (RepCoord d → k) :=
  fun P ↦ canonicalCoord d (P • M)

/-- The orbit is exactly the range of the orbit map. -/
theorem range_orbitMap {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    Set.range (orbitMap M) = orbitSet M := by
  ext y
  simp only [orbitSet, orbitMap, Set.mem_range, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P • M, ⟨P, rfl⟩, rfl⟩
  · rintro ⟨A, ⟨P, rfl⟩, rfl⟩
    exact ⟨P, rfl⟩

/-! ## The coordinate ring `𝒪(G_d)` -/

/-- The coordinate index of `G_d`: one variable per matrix entry of each vertex group element. -/
abbrev GroupCoord (d : Fin (N + 1) → ℕ) : Type :=
  Σ v : Fin (N + 1), Fin (d v) × Fin (d v)

instance (d : Fin (N + 1) → ℕ) : Finite (GroupCoord d) := by
  unfold GroupCoord; infer_instance

/-- The generic matrix at vertex `v`: entry `(i,j)` is the variable `X ⟨v, i, j⟩`. -/
noncomputable def genericMat (d : Fin (N + 1) → ℕ) (v : Fin (N + 1)) :
    Matrix (Fin (d v)) (Fin (d v)) (MvPolynomial (GroupCoord d) k) :=
  fun i j ↦ MvPolynomial.X ⟨v, i, j⟩

/-- The determinant of the generic matrix at `v` is a nonzero polynomial: evaluate every variable
at the identity matrix, where `det` becomes `det 1 = 1 ≠ 0`. -/
theorem det_genericMat_ne_zero (d : Fin (N + 1) → ℕ) (v : Fin (N + 1)) :
    (genericMat (k := k) d v).det ≠ 0 := by
  intro h
  -- evaluate every variable `⟨w, i, j⟩` at `(1 : Matrix) i j` (so the v-block becomes the identity)
  set e : MvPolynomial (GroupCoord d) k →+* k :=
    MvPolynomial.eval (fun c : GroupCoord d ↦
      (1 : Matrix (Fin (d c.1)) (Fin (d c.1)) k) c.2.1 c.2.2)
    with he
  have hmap : e.mapMatrix (genericMat (k := k) d v) = (1 : Matrix (Fin (d v)) (Fin (d v)) k) := by
    funext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, genericMat, he, MvPolynomial.eval_X]
  have hdet : e (genericMat (k := k) d v).det = 1 := by
    rw [RingHom.map_det, hmap, Matrix.det_one]
  rw [h, map_zero] at hdet
  exact one_ne_zero hdet.symm

/-- The **group denominator** `Δ = ∏_v det (generic matrix at v)`. -/
noncomputable def groupDenom (d : Fin (N + 1) → ℕ) : MvPolynomial (GroupCoord d) k :=
  ∏ v : Fin (N + 1), (genericMat (k := k) d v).det

/-- `Δ ≠ 0` (product of nonzero polynomials over a domain). -/
theorem groupDenom_ne_zero (d : Fin (N + 1) → ℕ) : groupDenom (k := k) d ≠ 0 := by
  rw [groupDenom, Finset.prod_ne_zero_iff]
  exact fun v _ ↦ det_genericMat_ne_zero d v

/-- The coordinate ring `𝒪(G_d) := Localization.Away Δ` of `G_d`. -/
abbrev groupRing (d : Fin (N + 1) → ℕ) : Type u :=
  Localization.Away (groupDenom (k := k) d)

/-- `𝒪(G_d)` is a domain (localization of a polynomial domain at a nonzero element). -/
instance groupRing_isDomain (d : Fin (N + 1) → ℕ) : IsDomain (groupRing (k := k) d) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Submonoid.powers (groupDenom (k := k) d)) (groupRing (k := k) d)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (groupDenom_ne_zero d))

/-! ## The generic group element and its inverse in `𝒪(G_d)` -/

/-- The structure map `MvPolynomial (GroupCoord d) k → 𝒪(G_d)`. -/
noncomputable abbrev groupAlgMap (d : Fin (N + 1) → ℕ) :
    MvPolynomial (GroupCoord d) k →+* groupRing (k := k) d :=
  algebraMap (MvPolynomial (GroupCoord d) k) (groupRing (k := k) d)

/-- The generic group element at `v`, pushed into the coordinate ring `𝒪(G_d)`. -/
noncomputable def genericUnit (d : Fin (N + 1) → ℕ) (v : Fin (N + 1)) :
    Matrix (Fin (d v)) (Fin (d v)) (groupRing (k := k) d) :=
  (groupAlgMap (k := k) d).mapMatrix (genericMat d v)

/-- The complementary denominator `∏_{w ≠ v} det (generic matrix at w)`. -/
noncomputable def detCompl (d : Fin (N + 1) → ℕ) (v : Fin (N + 1)) :
    MvPolynomial (GroupCoord d) k :=
  ∏ w ∈ Finset.univ.erase v, (genericMat (k := k) d w).det

/-- `det (generic matrix at v) · detCompl v = Δ`. -/
theorem det_mul_detCompl (d : Fin (N + 1) → ℕ) (v : Fin (N + 1)) :
    (genericMat (k := k) d v).det * detCompl d v = groupDenom (k := k) d := by
  rw [detCompl, groupDenom, ← Finset.prod_erase_mul _ _ (Finset.mem_univ v), mul_comm]

/-- The inverse of `det (generic matrix at v)` in `𝒪(G_d)`: `detCompl v · Δ⁻¹`. -/
noncomputable def genericDetInv (d : Fin (N + 1) → ℕ) (v : Fin (N + 1)) : groupRing (k := k) d :=
  groupAlgMap (k := k) d (detCompl d v) * IsLocalization.Away.invSelf (groupDenom (k := k) d)

/-- `genericDetInv` is a genuine inverse of the determinant in `𝒪(G_d)`. -/
theorem det_genericUnit_mul_genericDetInv (d : Fin (N + 1) → ℕ) (v : Fin (N + 1)) :
    (genericUnit (k := k) d v).det * genericDetInv d v = 1 := by
  have hdet : (genericUnit (k := k) d v).det = groupAlgMap (k := k) d (genericMat d v).det := by
    rw [genericUnit, RingHom.map_det]
  rw [hdet, genericDetInv, ← mul_assoc, ← map_mul, det_mul_detCompl,
    IsLocalization.Away.mul_invSelf]

/-- The generic inverse matrix at `v` in `𝒪(G_d)`: `(det)⁻¹ • adjugate`. -/
noncomputable def genericUnitInv (d : Fin (N + 1) → ℕ) (v : Fin (N + 1)) :
    Matrix (Fin (d v)) (Fin (d v)) (groupRing (k := k) d) :=
  genericDetInv (k := k) d v • (genericUnit (k := k) d v).adjugate

/-- `genericUnit v * genericUnitInv v = 1`: the generic group element is invertible in `𝒪(G_d)`. -/
theorem genericUnit_mul_genericUnitInv (d : Fin (N + 1) → ℕ) (v : Fin (N + 1)) :
    genericUnit (k := k) d v * genericUnitInv d v = 1 := by
  rw [genericUnitInv, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm,
    det_genericUnit_mul_genericDetInv, one_smul]

/-! ## The orbit-map pullback `μ_M^*` -/

/-- `M_i`, pushed entrywise into the coordinate ring `𝒪(G_d)` (constant matrices). -/
noncomputable def genericFactor {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) (i : Fin N) :
    Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) (groupRing (k := k) d) :=
  (M i).map (algebraMap k (groupRing (k := k) d))

/-- The generic orbit-map image of `M` at coordinate `⟨i, r, c⟩`: the `(r,c)` entry of
`Pgen_{i.succ} · M_i · (Pgen_{i.castSucc})⁻¹` in `𝒪(G_d)`. -/
noncomputable def genericOrbitCoord {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    RepCoord d → groupRing (k := k) d :=
  fun x ↦ (genericUnit (k := k) d x.1.succ * genericFactor M x.1
    * genericUnitInv (k := k) d x.1.castSucc) x.2.1 x.2.2

/-- The **orbit-map pullback** `μ_M^* : MvPolynomial (RepCoord d) k → 𝒪(G_d)`, the `k`-algebra hom
sending the coordinate variable `X ⟨i,r,c⟩` to the `(r,c)` entry of the generic orbit element
`Pgen_{i+1} · M_i · Pgen_i⁻¹`. -/
noncomputable def orbitPullback {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    MvPolynomial (RepCoord d) k →ₐ[k] groupRing (k := k) d :=
  MvPolynomial.aeval (genericOrbitCoord M)

/-! ## Evaluation at a group point and the pullback ↔ point-evaluation bridge -/

/-- The group point `xP : GroupCoord d → k` of `P ∈ G_d`: the matrix entries of each `P v`. -/
def groupPoint {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) : GroupCoord d → k :=
  fun c ↦ (P c.1 : Matrix (Fin (d c.1)) (Fin (d c.1)) k) c.2.1 c.2.2

/-- Evaluating the generic matrix at the group point recovers `P v`. -/
theorem eval_genericMat {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) (v : Fin (N + 1)) :
    (genericMat (k := k) d v).map (MvPolynomial.eval (groupPoint P))
      = (P v : Matrix (Fin (d v)) (Fin (d v)) k) := by
  funext i j
  simp only [Matrix.map_apply, genericMat, MvPolynomial.eval_X, groupPoint]

/-- The group denominator evaluates to a unit at any group point (product of nonzero
determinants of invertible matrices). -/
theorem isUnit_eval_groupDenom {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
    IsUnit (MvPolynomial.eval (groupPoint P) (groupDenom (k := k) d)) := by
  rw [groupDenom, map_prod]
  refine IsUnit.prod_iff.mpr fun v _ ↦ ?_
  rw [RingHom.map_det, show (MvPolynomial.eval (groupPoint P)).mapMatrix (genericMat (k := k) d v)
      = (P v : Matrix (Fin (d v)) (Fin (d v)) k) from eval_genericMat P v]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (P v).isUnit

/-- The **point-evaluation** ring hom `𝒪(G_d) → k` at `P ∈ G_d` (lift of `eval (groupPoint P)`
through `Δ`, which is a unit there). -/
noncomputable def evalGroupRing {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
    groupRing (k := k) d →+* k :=
  IsLocalization.Away.lift (groupDenom (k := k) d)
    (g := MvPolynomial.eval (groupPoint P)) (isUnit_eval_groupDenom P)

/-- `evalGroupRing P` agrees with `eval (groupPoint P)` on `algebraMap`-images. -/
@[simp] theorem evalGroupRing_algebraMap {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
    (p : MvPolynomial (GroupCoord d) k) :
    evalGroupRing P (groupAlgMap (k := k) d p) = MvPolynomial.eval (groupPoint P) p :=
  IsLocalization.Away.lift_eq _ _ _

/-- `evalGroupRing P` fixes the base field `k` (it is a `k`-algebra hom). -/
@[simp] theorem evalGroupRing_algebraMap_base {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
    (a : k) : evalGroupRing P (algebraMap k (groupRing (k := k) d) a) = a := by
  rw [show algebraMap k (groupRing (k := k) d) = (groupAlgMap (k := k) d).comp
      (algebraMap k (MvPolynomial (GroupCoord d) k)) from
    IsScalarTower.algebraMap_eq k (MvPolynomial (GroupCoord d) k) (groupRing (k := k) d),
    RingHom.comp_apply, evalGroupRing_algebraMap, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C]

/-- `evalGroupRing P` sends the generic group element `genericUnit v` to the actual matrix `P v`. -/
theorem evalGroupRing_genericUnit {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
    (v : Fin (N + 1)) :
    (genericUnit (k := k) d v).map (evalGroupRing P)
      = (P v : Matrix (Fin (d v)) (Fin (d v)) k) := by
  rw [genericUnit, ← eval_genericMat P v]
  funext i j
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, evalGroupRing_algebraMap]

/-- `evalGroupRing P` sends the constant factor `genericFactor M i` to `M i`. -/
theorem evalGroupRing_genericFactor {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) (i : Fin N) :
    (genericFactor M i).map (evalGroupRing P) = M i := by
  funext r c
  simp only [Matrix.map_apply, genericFactor, evalGroupRing_algebraMap_base]

/-- `evalGroupRing P` sends the generic inverse `genericUnitInv v` to the matrix inverse `(P v)⁻¹`,
which is `↑(P v)⁻¹` (the unit inverse). -/
theorem evalGroupRing_genericUnitInv {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
    (v : Fin (N + 1)) :
    (genericUnitInv (k := k) d v).map (evalGroupRing P)
      = (↑(P v)⁻¹ : Matrix (Fin (d v)) (Fin (d v)) k) := by
  -- the scalar piece: `evalGroupRing P (genericDetInv v) = Ring.inverse (det (P v))`
  have hdet : evalGroupRing P (genericDetInv (k := k) d v)
      = Ring.inverse ((P v : Matrix (Fin (d v)) (Fin (d v)) k)).det := by
    have h2 := congrArg (evalGroupRing P) (det_genericUnit_mul_genericDetInv (k := k) d v)
    rw [map_mul, map_one, RingHom.map_det, RingHom.mapMatrix_apply,
      evalGroupRing_genericUnit] at h2
    -- `det (P v) * evalGroupRing(genericDetInv) = 1` ⟹ the latter is `Ring.inverse (det (P v))`
    set Q := (P v : Matrix (Fin (d v)) (Fin (d v)) k)
    have hu : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp (P v).isUnit
    calc evalGroupRing P (genericDetInv (k := k) d v)
        = Ring.inverse Q.det * Q.det * evalGroupRing P (genericDetInv (k := k) d v) := by
          rw [Ring.inverse_mul_cancel Q.det hu, one_mul]
      _ = Ring.inverse Q.det * (Q.det * evalGroupRing P (genericDetInv (k := k) d v)) := by
          rw [mul_assoc]
      _ = Ring.inverse Q.det := by rw [h2, mul_one]
  -- the matrix piece: `evalGroupRing P` pushes through `adjugate`
  have hadj : (genericUnit (k := k) d v).adjugate.map (evalGroupRing P)
      = ((P v : Matrix (Fin (d v)) (Fin (d v)) k)).adjugate := by
    rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply,
      evalGroupRing_genericUnit]
  rw [Matrix.coe_units_inv, Matrix.inv_def]
  funext i j
  simp only [genericUnitInv, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hdet]
  congr 1
  exact congrFun (congrFun hadj i) j

/-- **The pullback ↔ point-evaluation bridge.** Evaluating the pullback of `g` at `P` recovers the
value of `g` at the orbit point `μ_M P`: `evalGroupRing P (μ_M^* g) = g (μ_M P)`. -/
theorem evalGroupRing_orbitPullback {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) (g : MvPolynomial (RepCoord d) k) :
    evalGroupRing P (orbitPullback M g) = MvPolynomial.eval (orbitMap M P) g := by
  -- per-generator: the pullback coordinate evaluates to the orbit point coordinate
  have hgen : ∀ x : RepCoord d,
      evalGroupRing P (genericOrbitCoord M x) = orbitMap M P x := by
    intro x
    rw [genericOrbitCoord, orbitMap, canonicalCoord_apply, smul_eq_baseChange, baseChange_apply]
    rw [show evalGroupRing P ((genericUnit (k := k) d x.1.succ * genericFactor M x.1
        * genericUnitInv (k := k) d x.1.castSucc) x.2.1 x.2.2)
      = ((genericUnit (k := k) d x.1.succ * genericFactor M x.1
        * genericUnitInv (k := k) d x.1.castSucc).map (evalGroupRing P)) x.2.1 x.2.2 from rfl]
    rw [Matrix.map_mul, Matrix.map_mul, evalGroupRing_genericUnit, evalGroupRing_genericFactor,
      evalGroupRing_genericUnitInv]
  -- assemble: the two ring homs `evalGroupRing P ∘ μ_M^*` and `eval (μ_M P)` agree on `C`, `X`
  have hext : (evalGroupRing P).comp (orbitPullback M).toRingHom
      = MvPolynomial.eval (orbitMap M P) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun x ↦ ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval_C]
      show evalGroupRing P (orbitPullback M (MvPolynomial.C r)) = r
      rw [orbitPullback, MvPolynomial.aeval_C, evalGroupRing_algebraMap_base]
    · rw [RingHom.comp_apply, MvPolynomial.eval_X]
      show evalGroupRing P (orbitPullback M (MvPolynomial.X x)) = orbitMap M P x
      rw [orbitPullback, MvPolynomial.aeval_X, hgen x]
  exact congrFun (congrArg (DFunLike.coe) hext) g

/-! ## The vanishing ideal of the orbit equals the kernel of the pullback -/

/-- **Density of group points.** Any point `x : GroupCoord d → k` at which `Δ` does not vanish
(every vertex block has invertible determinant) is `groupPoint P` for an honest `P ∈ G_d`. -/
theorem exists_baseChange_of_eval_ne_zero {d : Fin (N + 1) → ℕ} {x : GroupCoord d → k}
    (hx : MvPolynomial.eval x (groupDenom (k := k) d) ≠ 0) :
    ∃ P : BaseChangeGroup (k := k) d, groupPoint P = x := by
  -- each vertex block `x_v` has nonzero determinant, hence is invertible
  have hblock : ∀ v : Fin (N + 1),
      (Matrix.of (fun i j ↦ x ⟨v, i, j⟩) : Matrix (Fin (d v)) (Fin (d v)) k).det ≠ 0 := by
    intro v hv
    apply hx
    rw [groupDenom, map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    rw [RingHom.map_det,
      show (MvPolynomial.eval x).mapMatrix (genericMat (k := k) d v)
        = Matrix.of (fun i j ↦ x ⟨v, i, j⟩) from by
        funext i j; simp only [RingHom.mapMatrix_apply, Matrix.map_apply, genericMat,
          MvPolynomial.eval_X, Matrix.of_apply]]
    exact hv
  refine ⟨fun v ↦ ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit (hblock v))).unit, ?_⟩
  funext c
  simp only [groupPoint, IsUnit.unit_spec, Matrix.of_apply]

/-- **The key identity.** A polynomial vanishes on the orbit `O_M = range μ_M` iff its pullback
`μ_M^* g` is zero in the domain `𝒪(G_d)`: `vanishingIdeal (range μ_M) = ker μ_M^*`. The `⊇` is
point-evaluation; the `⊆` is the localization-vanishing-on-the-dense-open argument
(`Away.surj` + `MvPolynomial.funext`, which needs only an infinite integral domain — no algebraic
closure). -/
theorem vanishingIdeal_range_orbitMap_eq_ker [Infinite k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    MvPolynomial.vanishingIdeal k (Set.range (orbitMap M))
      = RingHom.ker (orbitPullback M).toRingHom := by
  ext g
  rw [MvPolynomial.mem_vanishingIdeal_iff, RingHom.mem_ker]
  constructor
  · -- ⊆ : `g` vanishes on the orbit ⟹ `μ_M^* g = 0`
    intro hg
    -- the pullback evaluates to 0 at every group point
    have hzero : ∀ P : BaseChangeGroup (k := k) d, evalGroupRing P (orbitPullback M g) = 0 := by
      intro P
      rw [evalGroupRing_orbitPullback, ← MvPolynomial.aeval_eq_eval]
      exact hg _ ⟨P, rfl⟩
    -- write `μ_M^* g = mk'(h, Δ^n)` and show the numerator `h` vanishes after multiplying by `Δ`
    obtain ⟨n, h, hsurj⟩ := IsLocalization.Away.surj (groupDenom (k := k) d) (orbitPullback M g)
    have hhΔ : h * groupDenom (k := k) d = 0 := by
      refine MvPolynomial.funext fun x ↦ ?_
      rw [map_mul, map_zero]
      by_cases hΔx : MvPolynomial.eval x (groupDenom (k := k) d) = 0
      · rw [hΔx, mul_zero]
      · obtain ⟨P, rfl⟩ := exists_baseChange_of_eval_ne_zero hΔx
        have hev := congrArg (evalGroupRing P) hsurj
        rw [map_mul, map_pow, hzero, zero_mul, evalGroupRing_algebraMap] at hev
        rw [← hev, zero_mul]
    -- domain + `Δ ≠ 0` ⟹ `h = 0`, so `μ_M^* g · (algebraMap Δ)^n = 0`; `algebraMap Δ` is a unit
    have hh : h = 0 := by
      rcases mul_eq_zero.mp hhΔ with h0 | h0
      · exact h0
      · exact absurd h0 (groupDenom_ne_zero d)
    rw [hh, map_zero] at hsurj
    have hΔunit : IsUnit ((algebraMap (MvPolynomial (GroupCoord d) k) (groupRing (k := k) d)
        (groupDenom (k := k) d)) ^ n) :=
      IsUnit.pow n (IsUnit.of_mul_eq_one _
        (IsLocalization.Away.mul_invSelf (groupDenom (k := k) d)))
    show orbitPullback M g = 0
    rw [mul_comm] at hsurj
    exact (hΔunit.mul_right_eq_zero).mp hsurj
  · -- ⊇ : `μ_M^* g = 0` ⟹ `g` vanishes on the orbit
    intro hg y hy
    obtain ⟨P, rfl⟩ := hy
    have hg' : orbitPullback M g = 0 := hg
    show MvPolynomial.aeval (orbitMap M P) g = 0
    rw [MvPolynomial.aeval_eq_eval, ← evalGroupRing_orbitPullback M P g, hg', map_zero]

/-! ## The headline: the orbit `O_M` is Zariski-irreducible (its vanishing ideal is prime) -/

/-- **The orbit is Zariski-irreducible (L1).** The vanishing ideal of the `G_d`-orbit `O_M ⊆
RepCoord d → k` is **prime**: `O_M` is the image of the irreducible group `G_d` under the polynomial
orbit map `μ_M`, so `vanishingIdeal O_M = ker μ_M^*` (`vanishingIdeal_range_orbitMap_eq_ker`) is a
kernel into the domain `𝒪(G_d) = Localization.Away Δ` (`groupRing_isDomain`), hence prime
(`RingHom.ker_isPrime`). The foundation L0/L1/L3/L6 stand on. -/
theorem isPrime_vanishingIdeal_orbitSet [Infinite k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    (MvPolynomial.vanishingIdeal k (orbitSet M) :
      Ideal (MvPolynomial (RepCoord d) k)).IsPrime := by
  rw [← range_orbitMap, vanishingIdeal_range_orbitMap_eq_ker]
  exact RingHom.ker_isPrime (orbitPullback M).toRingHom

/-- **The orbit is Zariski-irreducible (L1, point-space form).** `O_M` is Zariski-irreducible in the
sense of the L0 dictionary (`IsZariskiIrreducible`), i.e. its image in `Spec` is irreducible — the
direct consumer for the L0 codimension bridge. -/
theorem isZariskiIrreducible_orbitSet [Infinite k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    IsZariskiIrreducible (orbitSet M) :=
  (isZariskiIrreducible_iff_isPrime_vanishingIdeal (orbitSet M)).mpr
    (isPrime_vanishingIdeal_orbitSet M)

section Witness

/-! ## Non-vacuity witness

The `(2,2,2)/ℚ` full-rank witness `tupleWitnessQ` (`ℚ` is infinite, so the primeness headline now
fires here — it needs only `[Infinite k]`, not `[IsAlgClosed k]`; the orbit-set and pullback objects
are exercised on the concrete tuple). -/

/-- The orbit set of the `(2,2,2)/ℚ` witness contains the witness's own flattening — the orbit is
inhabited (`P = 1`). The orbit objects are non-vacuous on a concrete matrix tuple. -/
example : canonicalCoord dWitness tupleWitnessQ ∈ orbitSet tupleWitnessQ :=
  ⟨tupleWitnessQ, ⟨1, one_smul _ _⟩, rfl⟩

/-- The primeness headline now fires on the `(2,2,2)/ℚ` witness (`ℚ` is infinite): the orbit's
vanishing ideal is prime, with no algebraic-closedness hypothesis. -/
example : (MvPolynomial.vanishingIdeal ℚ (orbitSet tupleWitnessQ)).IsPrime :=
  isPrime_vanishingIdeal_orbitSet tupleWitnessQ

/-- The orbit map of the witness, evaluated at the identity base change, is the witness's own
flattening. -/
example : orbitMap tupleWitnessQ 1 = canonicalCoord dWitness tupleWitnessQ := by
  rw [orbitMap, one_smul]

end Witness

end DLNFibre.Core
