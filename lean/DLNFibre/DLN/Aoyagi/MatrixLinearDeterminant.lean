import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Bilinear
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.StdBasis

/-!
# Determinants of rectangular matrix multiplication maps

This file records small linear-algebra API needed by the Aoyagi
retained-passive Jacobian calculation.  It is only determinant arithmetic for
left and right multiplication, product maps, and triangular shears on
rectangular matrix spaces.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- A finite product of finite free modules is finite. -/
theorem moduleFinite_prod
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommMonoid N] [Module R N] [Module.Free R N] [Module.Finite R N] :
    Module.Finite R (M × N) :=
  Module.Finite.of_basis
    ((Module.Free.chooseBasis R M).prod (Module.Free.chooseBasis R N))

/-- A finite dependent product of finite free modules is finite. -/
theorem moduleFinite_pi
    {R ι : Type*} {M : ι → Type*} [Semiring R] [Finite ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)] :
    Module.Finite R (∀ i, M i) :=
  let _ : Fintype ι := Fintype.ofFinite ι
  Module.Finite.of_basis
    (Pi.basis fun i => Module.Free.chooseBasis R (M i))

/-- Determinant of a dependent block-diagonal matrix. -/
theorem Matrix.det_blockDiagonal'
    {R ι : Type*} {m : ι → Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (M : ∀ i, Matrix (m i) (m i) R) :
    (Matrix.blockDiagonal' M).det = ∏ i, (M i).det := by
  classical
  have htri :
      Matrix.BlockTriangular (Matrix.blockDiagonal' M) Sigma.fst :=
    Matrix.blockTriangular_blockDiagonal' M
  rw [htri.det_fintype]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  let e : m i ≃ {a : Sigma m // Sigma.fst a = i} :=
    { toFun := fun x => ⟨⟨i, x⟩, rfl⟩
      invFun := fun a => cast (congrArg m (by simpa using a.2)) a.1.2
      left_inv := by
        intro x
        simp
      right_inv := by
        intro a
        rcases a with ⟨⟨j, x⟩, h⟩
        cases h
        simp }
  rw [← Matrix.det_reindex_self e (M i)]
  congr 1
  ext x y
  rcases x with ⟨⟨j, x⟩, hx⟩
  rcases y with ⟨⟨k, y⟩, hy⟩
  cases hx
  cases hy
  simp [Matrix.toSquareBlock_def, Matrix.reindex_apply, e]

/-- Determinant of a product map, with the finite product basis supplied
locally. -/
theorem linearMap_det_prodMap_eq_mul
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    LinearMap.det (f.prodMap g) = LinearMap.det f * LinearMap.det g := by
  haveI : Module.Finite R (M × N) := moduleFinite_prod
  exact LinearMap.det_prodMap f g

/-- Determinant of a product linear equivalence. -/
theorem linearEquiv_prodCongr_det_eq_mul
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (eM : M ≃ₗ[R] M) (eN : N ≃ₗ[R] N) :
    LinearMap.det
        ((eM.prodCongr eN : (M × N) ≃ₗ[R] (M × N)) : (M × N) →ₗ[R] (M × N)) =
      LinearMap.det (eM : M →ₗ[R] M) * LinearMap.det (eN : N →ₗ[R] N) := by
  rw [LinearEquiv.coe_prodCongr, linearMap_det_prodMap_eq_mul]

/-- Absolute determinant of a product linear equivalence whose two factors have
absolute determinant one. -/
theorem linearEquiv_prodCongr_abs_det_eq_one
    {R M N : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (eM : M ≃ₗ[R] M) (eN : N ≃ₗ[R] N)
    (hM : |LinearMap.det (eM : M →ₗ[R] M)| = 1)
    (hN : |LinearMap.det (eN : N →ₗ[R] N)| = 1) :
    |LinearMap.det
        ((eM.prodCongr eN : (M × N) ≃ₗ[R] (M × N)) : (M × N) →ₗ[R] (M × N))| =
      1 := by
  rw [linearEquiv_prodCongr_det_eq_mul, abs_mul, hM, hN, one_mul]

/-- Determinant of a dependent product map. -/
theorem linearMap_det_piMap_eq_prod
    {R ι : Type*} {M : ι → Type*} [CommRing R]
    [Fintype ι] [LinearOrder ι]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
    (f : ∀ i, M i →ₗ[R] M i) :
    LinearMap.det (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)) =
      ∏ i, LinearMap.det (f i) := by
  classical
  haveI : Module.Finite R (∀ i, M i) := moduleFinite_pi
  let b : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex R (M i)) R (M i) :=
    fun i => Module.Free.chooseBasis R (M i)
  let B : Module.Basis (Σ i, Module.Free.ChooseBasisIndex R (M i)) R (∀ i, M i) :=
    Pi.basis b
  simp_rw [← LinearMap.det_toMatrix B, ← LinearMap.det_toMatrix (b _)]
  have hmat :
      LinearMap.toMatrix B B
          (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)) =
        Matrix.blockDiagonal' fun i => LinearMap.toMatrix (b i) (b i) (f i) := by
    ext ⟨i, a⟩ ⟨j, c⟩
    by_cases h : i = j
    · subst j
      simp [B, Matrix.blockDiagonal'_apply, LinearMap.toMatrix_apply',
        LinearMap.pi_apply]
    · simp [B, Matrix.blockDiagonal'_apply, LinearMap.toMatrix_apply',
        LinearMap.pi_apply, h]
  rw [hmat, Matrix.det_blockDiagonal']

/-- Linear equivalence splitting a dependent `Fin (n+1)` family into its last
coordinate and the preceding `castSucc` family. -/
def finSnocLinearEquiv
    {R : Type*} [Semiring R] {n : ℕ} {M : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    (M (Fin.last n) × (∀ i : Fin n, M i.castSucc)) ≃ₗ[R]
      (∀ i : Fin (n + 1), M i) where
  toFun x := Fin.snoc x.2 x.1
  invFun x := (x (Fin.last n), Fin.init x)
  left_inv x := by
    ext i <;> simp
  right_inv x := by
    ext i
    induction i using Fin.lastCases <;> simp [Fin.init_def]
  map_add' x y := by
    ext i
    induction i using Fin.lastCases <;> simp [Fin.snoc_last, Fin.snoc_castSucc]
  map_smul' a x := by
    ext i
    induction i using Fin.lastCases <;> simp [Fin.snoc_last, Fin.snoc_castSucc]

@[simp]
theorem finSnocLinearEquiv_apply_last
    {R : Type*} [Semiring R] {n : ℕ} {M : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (x : M (Fin.last n) × (∀ i : Fin n, M i.castSucc)) :
    finSnocLinearEquiv (R := R) (M := M) x (Fin.last n) = x.1 := by
  simp [finSnocLinearEquiv]

@[simp]
theorem finSnocLinearEquiv_apply_castSucc
    {R : Type*} [Semiring R] {n : ℕ} {M : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (x : M (Fin.last n) × (∀ i : Fin n, M i.castSucc)) (i : Fin n) :
    finSnocLinearEquiv (R := R) (M := M) x i.castSucc = x.2 i := by
  simp [finSnocLinearEquiv]

@[simp]
theorem finSnocLinearEquiv_symm_apply
    {R : Type*} [Semiring R] {n : ℕ} {M : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (x : ∀ i : Fin (n + 1), M i) :
    (finSnocLinearEquiv (R := R) (M := M)).symm x =
      (x (Fin.last n), Fin.init x) :=
  rfl

/-- Successor-unitriangular map on a dependent `Fin` family:
`x_last` is fixed and `x_p` is replaced by `x_p + L_p x_{p+1}`. -/
def finSuccUpperUnitriangularLinearMap
    {R : Type*} [Semiring R] {n : ℕ} {M : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (L : ∀ p : Fin n, M p.succ →ₗ[R] M p.castSucc) :
    (∀ i : Fin (n + 1), M i) →ₗ[R] (∀ i : Fin (n + 1), M i) :=
  LinearMap.pi fun i =>
    Fin.lastCases
      (motive := fun i : Fin (n + 1) =>
        (∀ j : Fin (n + 1), M j) →ₗ[R] M i)
      (LinearMap.proj (Fin.last n))
      (fun p => LinearMap.proj p.castSucc + (L p).comp (LinearMap.proj p.succ))
      i

@[simp]
theorem finSuccUpperUnitriangularLinearMap_last
    {R : Type*} [Semiring R] {n : ℕ} {M : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (L : ∀ p : Fin n, M p.succ →ₗ[R] M p.castSucc)
    (x : ∀ i : Fin (n + 1), M i) :
    finSuccUpperUnitriangularLinearMap (R := R) (M := M) L x (Fin.last n) =
      x (Fin.last n) := by
  simp [finSuccUpperUnitriangularLinearMap]

@[simp]
theorem finSuccUpperUnitriangularLinearMap_castSucc
    {R : Type*} [Semiring R] {n : ℕ} {M : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (L : ∀ p : Fin n, M p.succ →ₗ[R] M p.castSucc)
    (x : ∀ i : Fin (n + 1), M i) (p : Fin n) :
    finSuccUpperUnitriangularLinearMap (R := R) (M := M) L x p.castSucc =
      x p.castSucc + L p (x p.succ) := by
  simp [finSuccUpperUnitriangularLinearMap]

set_option linter.flexible false in
/-- A successor-upper-triangular endomorphism of a dependent `Fin (n+1)` family
has determinant equal to the product of its diagonal block determinants. -/
theorem linearMap_det_finSuccUpperTriangular_eq_prod
    {R : Type*} [CommRing R] {n : ℕ} {M : Fin (n + 1) → Type*}
    [∀ q, AddCommGroup (M q)] [∀ q, Module R (M q)]
    [∀ q, Module.Free R (M q)] [∀ q, Module.Finite R (M q)]
    (T : ((q : Fin (n + 1)) → M q) →ₗ[R] ((q : Fin (n + 1)) → M q))
    (D : ∀ q : Fin (n + 1), M q →ₗ[R] M q)
    (L : ∀ p : Fin n, M p.succ →ₗ[R] M p.castSucc)
    (hlast : ∀ x, T x (Fin.last n) = D (Fin.last n) (x (Fin.last n)))
    (hcastSucc : ∀ (p : Fin n) x,
      T x p.castSucc = D p.castSucc (x p.castSucc) + L p (x p.succ)) :
    LinearMap.det T = ∏ q : Fin (n + 1), LinearMap.det (D q) := by
  classical
  haveI : Module.Finite R ((q : Fin (n + 1)) → M q) := moduleFinite_pi
  let b : ∀ q, Module.Basis (Module.Free.ChooseBasisIndex R (M q)) R (M q) :=
    fun q => Module.Free.chooseBasis R (M q)
  let B : Module.Basis (Σ q, Module.Free.ChooseBasisIndex R (M q)) R
      ((q : Fin (n + 1)) → M q) :=
    Pi.basis b
  let A := LinearMap.toMatrix B B T
  have htri : Matrix.BlockTriangular A Sigma.fst := by
    rintro ⟨i, ai⟩ ⟨j, aj⟩ hji
    dsimp [A] at hji ⊢
    induction i using Fin.lastCases with
    | last =>
        have h_ne_last : j ≠ Fin.last n := ne_of_lt hji
        simp [B, b, LinearMap.toMatrix_apply', hlast, h_ne_last]
    | cast p =>
        have h_ne_cast : j ≠ p.castSucc := ne_of_lt hji
        have h_ne_succ : j ≠ p.succ :=
          ne_of_lt (lt_trans hji p.castSucc_lt_succ)
        simp [B, b, LinearMap.toMatrix_apply', hcastSucc, h_ne_cast, h_ne_succ]
  have hdiag_det :
      ∀ q : Fin (n + 1),
        (A.toSquareBlock Sigma.fst q).det = LinearMap.det (D q) := by
    intro q
    rw [← LinearMap.det_toMatrix (b q)]
    let e :
        Module.Free.ChooseBasisIndex R (M q) ≃
          {a : Sigma fun q => Module.Free.ChooseBasisIndex R (M q) // Sigma.fst a = q} :=
      { toFun := fun a => ⟨⟨q, a⟩, rfl⟩
        invFun := fun a => cast (congrArg (fun q => Module.Free.ChooseBasisIndex R (M q))
          (by simpa using a.2)) a.1.2
        left_inv := by
          intro a
          simp
        right_inv := by
          intro a
          rcases a with ⟨⟨q', a⟩, hq'⟩
          cases hq'
          simp }
    rw [← Matrix.det_reindex_self e (LinearMap.toMatrix (b q) (b q) (D q))]
    congr 1
    ext i j
    rcases i with ⟨⟨qi, ai⟩, hqi⟩
    rcases j with ⟨⟨qj, aj⟩, hqj⟩
    dsimp [A] at hqi hqj ⊢
    cases hqi
    cases hqj
    induction q using Fin.lastCases with
    | last =>
        simp [Matrix.toSquareBlock_def, e, B, b, LinearMap.toMatrix_apply', hlast]
    | cast p =>
        have h_ne : p.succ ≠ p.castSucc := p.castSucc_lt_succ.ne'
        simp [Matrix.toSquareBlock_def, e, B, b, LinearMap.toMatrix_apply',
          hcastSucc, h_ne]
  rw [← LinearMap.det_toMatrix B]
  change A.det = ∏ q : Fin (n + 1), LinearMap.det (D q)
  rw [htri.det_fintype]
  refine Finset.prod_congr rfl ?_
  intro q _hq
  rw [hdiag_det q]

set_option linter.flexible false in
/-- A successor-unitriangular endomorphism of a dependent `Fin (n+1)` family
has determinant one. -/
theorem linearMap_det_finSuccUpperUnitriangular_eq_one
    {R : Type*} [CommRing R] {n : ℕ} {M : Fin (n + 1) → Type*}
    [∀ q, AddCommGroup (M q)] [∀ q, Module R (M q)]
    [∀ q, Module.Free R (M q)] [∀ q, Module.Finite R (M q)]
    (T : ((q : Fin (n + 1)) → M q) →ₗ[R] ((q : Fin (n + 1)) → M q))
    (L : ∀ p : Fin n, M p.succ →ₗ[R] M p.castSucc)
    (hlast : ∀ x, T x (Fin.last n) = x (Fin.last n))
    (hcastSucc : ∀ (p : Fin n) x,
      T x p.castSucc = x p.castSucc + L p (x p.succ)) :
    LinearMap.det T = 1 := by
  classical
  haveI : Module.Finite R ((q : Fin (n + 1)) → M q) := moduleFinite_pi
  let b : ∀ q, Module.Basis (Module.Free.ChooseBasisIndex R (M q)) R (M q) :=
    fun q => Module.Free.chooseBasis R (M q)
  let B : Module.Basis (Σ q, Module.Free.ChooseBasisIndex R (M q)) R
      ((q : Fin (n + 1)) → M q) :=
    Pi.basis b
  let A := LinearMap.toMatrix B B T
  have htri : Matrix.BlockTriangular A Sigma.fst := by
    rintro ⟨i, ai⟩ ⟨j, aj⟩ hji
    dsimp [A] at hji ⊢
    induction i using Fin.lastCases with
    | last =>
        have h_ne_last : j ≠ Fin.last n := ne_of_lt hji
        simp [B, b, LinearMap.toMatrix_apply', hlast, h_ne_last]
    | cast p =>
        have h_ne_cast : j ≠ p.castSucc := ne_of_lt hji
        have h_ne_succ : j ≠ p.succ :=
          ne_of_lt (lt_trans hji p.castSucc_lt_succ)
        simp [B, b, LinearMap.toMatrix_apply', hcastSucc, h_ne_cast, h_ne_succ]
  have hdiag : ∀ q : Fin (n + 1), A.toSquareBlock Sigma.fst q = 1 := by
    intro q
    ext i j
    rcases i with ⟨⟨qi, ai⟩, hqi⟩
    rcases j with ⟨⟨qj, aj⟩, hqj⟩
    dsimp [A] at hqi hqj ⊢
    cases hqi
    cases hqj
    induction q using Fin.lastCases with
    | last =>
        simp [Matrix.toSquareBlock_def, B, b, LinearMap.toMatrix_apply', hlast,
          Matrix.one_apply, Subtype.ext_iff]
        by_cases h : ai = aj
        · subst aj
          rw [Finsupp.single_eq_same, if_pos rfl]
        · rw [Finsupp.single_eq_of_ne h, if_neg h]
    | cast p =>
        have h_ne : p.succ ≠ p.castSucc := p.castSucc_lt_succ.ne'
        simp [Matrix.toSquareBlock_def, B, b, LinearMap.toMatrix_apply', hcastSucc, h_ne,
          Matrix.one_apply, Subtype.ext_iff]
        by_cases h : ai = aj
        · subst aj
          rw [Finsupp.single_eq_same, if_pos rfl]
        · rw [Finsupp.single_eq_of_ne h, if_neg h]
  rw [← LinearMap.det_toMatrix B]
  change A.det = 1
  rw [htri.det_fintype]
  simp [hdiag]

/-- The canonical successor-unitriangular map has determinant one. -/
theorem finSuccUpperUnitriangularLinearMap_det_eq_one
    {R : Type*} [CommRing R] {n : ℕ} {M : Fin (n + 1) → Type*}
    [∀ q, AddCommGroup (M q)] [∀ q, Module R (M q)]
    [∀ q, Module.Free R (M q)] [∀ q, Module.Finite R (M q)]
    (L : ∀ p : Fin n, M p.succ →ₗ[R] M p.castSucc) :
    LinearMap.det (finSuccUpperUnitriangularLinearMap (R := R) (M := M) L) = 1 := by
  exact linearMap_det_finSuccUpperUnitriangular_eq_one
    (finSuccUpperUnitriangularLinearMap (R := R) (M := M) L) L
    (by intro x; simp)
    (by intro p x; simp)

/-- A lower product shear has determinant equal to the product of its diagonal
determinants. -/
theorem linearEquiv_det_skewProd_toLinearMap_eq_mul
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (eM : M ≃ₗ[R] M) (eN : N ≃ₗ[R] N) (f : M →ₗ[R] N) :
    LinearMap.det ((eM.skewProd eN f : M × N →ₗ[R] M × N)) =
      LinearMap.det (eM : M →ₗ[R] M) * LinearMap.det (eN : N →ₗ[R] N) := by
  classical
  let b := Module.Free.chooseBasis R M
  let c := Module.Free.chooseBasis R N
  haveI : Module.Finite R (M × N) := moduleFinite_prod
  rw [← LinearMap.det_toMatrix (b.prod c), ← LinearMap.det_toMatrix b,
    ← LinearMap.det_toMatrix c]
  have hmat :
      LinearMap.toMatrix (b.prod c) (b.prod c)
        ((eM.skewProd eN f : M × N →ₗ[R] M × N)) =
        Matrix.fromBlocks
          (LinearMap.toMatrix b b (eM : M →ₗ[R] M)) 0
          (LinearMap.toMatrix b c f)
          (LinearMap.toMatrix c c (eN : N →ₗ[R] N)) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix, LinearEquiv.skewProd_apply, Pi.single_apply]
  rw [hmat, Matrix.det_fromBlocks_zero₁₂]

/-- A lower product shear with identity diagonal factors has determinant one. -/
theorem linearEquiv_skewProd_refl_refl_det_eq_one
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] N) :
    LinearMap.det
      (((LinearEquiv.refl R M).skewProd
        (LinearEquiv.refl R N) f : M × N →ₗ[R] M × N)) = 1 := by
  rw [linearEquiv_det_skewProd_toLinearMap_eq_mul]
  simp

/-- A lower product shear with identity diagonal factors has absolute
determinant one. -/
theorem linearEquiv_skewProd_refl_refl_abs_det_eq_one
    {R M N : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] N) :
    |LinearMap.det
      (((LinearEquiv.refl R M).skewProd
        (LinearEquiv.refl R N) f : M × N →ₗ[R] M × N))| = 1 := by
  rw [linearEquiv_skewProd_refl_refl_det_eq_one]
  simp

/-- Upper product shear `(x,y) |-> (x + f y, y)`. -/
def linearEquivUpperShear
    {R M N : Type*} [Semiring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) :
    (M × N) ≃ₗ[R] (M × N) where
  toFun x := (x.1 + f x.2, x.2)
  invFun x := (x.1 - f x.2, x.2)
  left_inv := by
    intro x
    ext <;> simp [sub_eq_add_neg, add_assoc]
  right_inv := by
    intro x
    ext <;> simp [sub_eq_add_neg, add_assoc]
  map_add' x y := by
    ext <;> simp [map_add, add_assoc, add_left_comm, add_comm]
  map_smul' a x := by
    ext <;> simp [map_smul, smul_add]

@[simp]
theorem linearEquivUpperShear_apply
    {R M N : Type*} [Semiring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) (x : M × N) :
    (linearEquivUpperShear f) x = (x.1 + f x.2, x.2) :=
  rfl

@[simp]
theorem linearEquivUpperShear_symm_apply
    {R M N : Type*} [Semiring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) (x : M × N) :
    (linearEquivUpperShear f).symm x = (x.1 - f x.2, x.2) :=
  rfl

/-- An upper product shear has determinant one. -/
theorem linearEquivUpperShear_det_eq_one
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (f : N →ₗ[R] M) :
    LinearMap.det ((linearEquivUpperShear f : (M × N) ≃ₗ[R] (M × N)) :
      (M × N) →ₗ[R] (M × N)) = 1 := by
  let e : (M × N) ≃ₗ[R] (N × M) := LinearEquiv.prodComm R M N
  let L : (M × N) ≃ₗ[R] (M × N) := linearEquivUpperShear f
  let S : (N × M) ≃ₗ[R] (N × M) :=
    (LinearEquiv.refl R N).skewProd (LinearEquiv.refl R M) f
  have hconj :
      ((e : (M × N) →ₗ[R] (N × M)).comp
          ((L : (M × N) →ₗ[R] (M × N)).comp
            (e.symm : (N × M) →ₗ[R] (M × N)))) =
        (S : (N × M) →ₗ[R] (N × M)) := by
    apply LinearMap.ext
    intro x
    simp [e, L, S, LinearEquiv.skewProd_apply]
  calc
    LinearMap.det (L : (M × N) →ₗ[R] (M × N)) =
        LinearMap.det
          ((e : (M × N) →ₗ[R] (N × M)).comp
            ((L : (M × N) →ₗ[R] (M × N)).comp
              (e.symm : (N × M) →ₗ[R] (M × N)))) := by
          rw [LinearMap.det_conj (L : (M × N) →ₗ[R] (M × N)) e]
    _ = LinearMap.det (S : (N × M) →ₗ[R] (N × M)) := by
          rw [hconj]
    _ = 1 := by
          rw [linearEquiv_det_skewProd_toLinearMap_eq_mul]
          simp

/-- An upper product shear has absolute determinant one. -/
theorem linearEquivUpperShear_abs_det_eq_one
    {R M N : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (f : N →ₗ[R] M) :
    |LinearMap.det ((linearEquivUpperShear f : (M × N) ≃ₗ[R] (M × N)) :
      (M × N) →ₗ[R] (M × N))| = 1 := by
  rw [linearEquivUpperShear_det_eq_one]
  simp

/-- Upper block-triangular linear map on a product:
`(x,y) ↦ (f x + h y, g y)`. -/
def linearMapUpperTriangular
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : N →ₗ[R] M) :
    (M × N) →ₗ[R] (M × N) where
  toFun x := (f x.1 + h x.2, g x.2)
  map_add' x y := by
    ext <;> simp [map_add, add_assoc, add_left_comm, add_comm]
  map_smul' a x := by
    ext <;> simp [map_smul, smul_add]

@[simp]
theorem linearMapUpperTriangular_apply
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : N →ₗ[R] M)
    (x : M × N) :
    linearMapUpperTriangular f g h x = (f x.1 + h x.2, g x.2) :=
  rfl

/-- Lower block-triangular linear map on a product:
`(x,y) ↦ (f x, h x + g y)`. -/
def linearMapLowerTriangular
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : M →ₗ[R] N) :
    (M × N) →ₗ[R] (M × N) where
  toFun x := (f x.1, h x.1 + g x.2)
  map_add' x y := by
    ext <;> simp [map_add, add_assoc, add_left_comm, add_comm]
  map_smul' a x := by
    ext <;> simp [map_smul, smul_add]

@[simp]
theorem linearMapLowerTriangular_apply
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : M →ₗ[R] N)
    (x : M × N) :
    linearMapLowerTriangular f g h x = (f x.1, h x.1 + g x.2) :=
  rfl

/-- An upper block-triangular linear map has determinant equal to the product
of its diagonal determinants. -/
theorem linearMapUpperTriangular_det_eq_mul
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : N →ₗ[R] M) :
    LinearMap.det (linearMapUpperTriangular f g h) =
      LinearMap.det f * LinearMap.det g := by
  classical
  let b := Module.Free.chooseBasis R M
  let c := Module.Free.chooseBasis R N
  haveI : Module.Finite R (M × N) := moduleFinite_prod
  rw [← LinearMap.det_toMatrix (b.prod c), ← LinearMap.det_toMatrix b,
    ← LinearMap.det_toMatrix c]
  have hmat :
      LinearMap.toMatrix (b.prod c) (b.prod c)
        (linearMapUpperTriangular f g h) =
        Matrix.fromBlocks
          (LinearMap.toMatrix b b f)
          (LinearMap.toMatrix c b h)
          0
          (LinearMap.toMatrix c c g) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix, Pi.single_apply]
  rw [hmat, Matrix.det_fromBlocks_zero₂₁]

/-- A lower block-triangular linear map has determinant equal to the product
of its diagonal determinants. -/
theorem linearMapLowerTriangular_det_eq_mul
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : M →ₗ[R] N) :
    LinearMap.det (linearMapLowerTriangular f g h) =
      LinearMap.det f * LinearMap.det g := by
  classical
  let b := Module.Free.chooseBasis R M
  let c := Module.Free.chooseBasis R N
  haveI : Module.Finite R (M × N) := moduleFinite_prod
  rw [← LinearMap.det_toMatrix (b.prod c), ← LinearMap.det_toMatrix b,
    ← LinearMap.det_toMatrix c]
  have hmat :
      LinearMap.toMatrix (b.prod c) (b.prod c)
        (linearMapLowerTriangular f g h) =
        Matrix.fromBlocks
          (LinearMap.toMatrix b b f)
          0
          (LinearMap.toMatrix b c h)
          (LinearMap.toMatrix c c g) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix, Pi.single_apply]
  rw [hmat, Matrix.det_fromBlocks_zero₁₂]

/-- Read a matrix as a family of columns. -/
def matrixColumnLinearEquiv (R : Type*) [Semiring R] (m n : Type*) :
    Matrix m n R ≃ₗ[R] (n → m → R) where
  toFun X := fun j i => X i j
  invFun f := fun i j => f j i
  left_inv := by
    intro X
    rfl
  right_inv := by
    intro f
    rfl
  map_add' := by
    intro X Y
    rfl
  map_smul' := by
    intro a X
    rfl

/-- The determinant of left multiplication by a square matrix on rectangular
matrices is the determinant of the multiplier to the number of columns. -/
theorem linearMap_det_mulLeftLinearMap
    {R m n : Type*} [CommRing R]
    [Fintype m] [DecidableEq m] [Fintype n]
    (A : Matrix m m R) :
    LinearMap.det (mulLeftLinearMap n R A :
      Matrix m n R →ₗ[R] Matrix m n R) =
        A.det ^ Fintype.card n := by
  let e := matrixColumnLinearEquiv R m n
  let L : Matrix m n R →ₗ[R] Matrix m n R := mulLeftLinearMap n R A
  let P : (n → m → R) →ₗ[R] (n → m → R) :=
    LinearMap.pi (fun j : n => (Matrix.toLin' A).comp (LinearMap.proj j))
  have hconj :
      ((e : Matrix m n R →ₗ[R] (n → m → R)).comp
          (L.comp (e.symm : (n → m → R) →ₗ[R] Matrix m n R))) = P := by
    apply LinearMap.ext
    intro v
    funext j i
    simp [e, matrixColumnLinearEquiv, L, P, mulLeftLinearMap, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Matrix.mul_apply]
  calc
    LinearMap.det L =
        LinearMap.det
          ((e : Matrix m n R →ₗ[R] (n → m → R)).comp
            (L.comp (e.symm : (n → m → R) →ₗ[R] Matrix m n R))) := by
          rw [LinearMap.det_conj L e]
    _ = LinearMap.det P := by rw [hconj]
    _ = ∏ _j : n, LinearMap.det (Matrix.toLin' A) := by
          simpa [P] using
            (LinearMap.det_pi (R := R) (ι := n) (M := m → R)
              (fun _j : n => Matrix.toLin' A))
    _ = A.det ^ Fintype.card n := by
          simp

/-- The determinant of right multiplication by a square matrix on rectangular
matrices is the determinant of the multiplier to the number of rows. -/
theorem linearMap_det_mulRightLinearMap
    {R m n : Type*} [CommRing R]
    [Fintype m] [Fintype n] [DecidableEq n]
    (B : Matrix n n R) :
    LinearMap.det (mulRightLinearMap m R B :
      Matrix m n R →ₗ[R] Matrix m n R) =
        B.det ^ Fintype.card m := by
  let e := Matrix.transposeLinearEquiv m n R R
  let L : Matrix m n R →ₗ[R] Matrix m n R := mulRightLinearMap m R B
  let P : Matrix n m R →ₗ[R] Matrix n m R := mulLeftLinearMap m R Bᵀ
  have hconj :
      ((e : Matrix m n R →ₗ[R] Matrix n m R).comp
          (L.comp (e.symm : Matrix n m R →ₗ[R] Matrix m n R))) = P := by
    apply LinearMap.ext
    intro X
    ext i j
    simp [e, L, P, Matrix.transposeLinearEquiv, mulRightLinearMap, mulLeftLinearMap,
      Matrix.mul_apply, mul_comm]
  calc
    LinearMap.det L =
        LinearMap.det
          ((e : Matrix m n R →ₗ[R] Matrix n m R).comp
            (L.comp (e.symm : Matrix n m R →ₗ[R] Matrix m n R))) := by
          rw [LinearMap.det_conj L e]
    _ = LinearMap.det P := by rw [hconj]
    _ = (Bᵀ).det ^ Fintype.card m := by
          exact linearMap_det_mulLeftLinearMap (R := R) (m := n) (n := m) Bᵀ
    _ = B.det ^ Fintype.card m := by
          rw [Matrix.det_transpose]

section EdgeLocalFCPair

variable {ρ μ κ K : Type*} [CommRing K]
variable [Fintype ρ] [DecidableEq ρ] [Fintype μ] [Fintype κ]

/-- Tangent space for the edge-local pair variables `(F,C)`. -/
abbrev EdgeLocalFCPairTangent :=
  Matrix ρ κ K × Matrix μ κ K

/-- Lower shear `(F,C) |-> (F, C - G*F)`. -/
def edgeLocalFCPairLowerShear
    (G : Matrix μ ρ K) :
    EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) ≃ₗ[K]
      EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) :=
  (LinearEquiv.refl K (Matrix ρ κ K)).skewProd
    (LinearEquiv.refl K (Matrix μ κ K))
    (mulLeftLinearMap κ K (-G))

/-- Diagonal map `(F,C) |-> (-A*F, C)`. -/
def edgeLocalFCPairDiagonal
    (A : Matrix ρ ρ K) :
    EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) →ₗ[K]
      EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) :=
  (mulLeftLinearMap κ K (-A)).prodMap
    (LinearMap.id : Matrix μ κ K →ₗ[K] Matrix μ κ K)

/-- Upper shear `(F,C) |-> (F + H*C, C)`. -/
def edgeLocalFCPairUpperShear
    (H : Matrix ρ μ K) :
    EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) ≃ₗ[K]
      EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) :=
  linearEquivUpperShear (mulLeftLinearMap κ K H)

/-- The edge-local pair map
`(F,C) |-> (-(A + H*G)*F + H*C, -G*F + C)`. -/
def edgeLocalFCPairLinearMap
    (A : Matrix ρ ρ K) (H : Matrix ρ μ K) (G : Matrix μ ρ K) :
    EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) →ₗ[K]
      EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) :=
  (edgeLocalFCPairUpperShear
      (ρ := ρ) (μ := μ) (κ := κ) (K := K) H).toLinearMap.comp
    ((edgeLocalFCPairDiagonal
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) A).comp
      (edgeLocalFCPairLowerShear
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) G).toLinearMap)

omit [DecidableEq ρ] [Fintype κ] in
/-- Formula for the edge-local pair map in `(F,C)` order. -/
theorem edgeLocalFCPairLinearMap_apply
    (A : Matrix ρ ρ K) (H : Matrix ρ μ K) (G : Matrix μ ρ K)
    (v : EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K)) :
    edgeLocalFCPairLinearMap
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) A H G v =
      (-(A + H * G) * v.1 + H * v.2, -G * v.1 + v.2) := by
  rcases v with ⟨F, C⟩
  ext i j <;>
    simp [edgeLocalFCPairLinearMap, edgeLocalFCPairLowerShear,
      edgeLocalFCPairDiagonal, edgeLocalFCPairUpperShear,
      LinearEquiv.skewProd_apply, Matrix.add_mul, Matrix.mul_add,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_left_comm, add_comm]

/-- Inverse formula for the edge-local pair map on the determinant chart
`IsUnit A.det`.

For target coordinates `(U,V)`, this recovers
`F = A⁻¹ * (H*V - U)` and then `C = V + G*F`. -/
def edgeLocalFCPairLinearMapInverse
    (A : Matrix ρ ρ K) (H : Matrix ρ μ K) (G : Matrix μ ρ K) :
    EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) →ₗ[K]
      EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) :=
  let fstL :
      EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) →ₗ[K]
        Matrix ρ κ K :=
    LinearMap.fst K (Matrix ρ κ K) (Matrix μ κ K)
  let sndL :
      EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) →ₗ[K]
        Matrix μ κ K :=
    LinearMap.snd K (Matrix ρ κ K) (Matrix μ κ K)
  let preF :
      EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) →ₗ[K]
        Matrix ρ κ K :=
    (mulLeftLinearMap κ K H).comp sndL - fstL
  let recF :
      EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) →ₗ[K]
        Matrix ρ κ K :=
    (mulLeftLinearMap κ K A⁻¹).comp preF
  recF.prod (sndL + (mulLeftLinearMap κ K G).comp recF)

omit [Fintype κ] in
/-- Apply formula for the inverse edge-local pair map. -/
theorem edgeLocalFCPairLinearMapInverse_apply
    (A : Matrix ρ ρ K) (H : Matrix ρ μ K) (G : Matrix μ ρ K)
    (v : EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K)) :
    edgeLocalFCPairLinearMapInverse
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) A H G v =
      (A⁻¹ * (H * v.2 - v.1),
        v.2 + G * (A⁻¹ * (H * v.2 - v.1))) :=
  rfl

/-- On the determinant chart `IsUnit A.det`, the edge-local pair map is a
linear equivalence with inverse `edgeLocalFCPairLinearMapInverse`. -/
def edgeLocalFCPairLinearEquiv
    (A : Matrix ρ ρ K) (H : Matrix ρ μ K) (G : Matrix μ ρ K)
    (hA : IsUnit A.det) :
    EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) ≃ₗ[K]
      EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K) :=
  LinearEquiv.ofLinear
    (edgeLocalFCPairLinearMap
      (ρ := ρ) (μ := μ) (κ := κ) (K := K) A H G)
    (edgeLocalFCPairLinearMapInverse
      (ρ := ρ) (μ := μ) (κ := κ) (K := K) A H G)
    (by
      apply LinearMap.ext
      intro v
      rcases v with ⟨U, V⟩
      have hx :
          A * (A⁻¹ * (H * V - U)) = H * V - U :=
        Matrix.mul_nonsing_inv_cancel_left A (H * V - U) hA
      apply Prod.ext
      · rw [LinearMap.comp_apply, edgeLocalFCPairLinearMapInverse_apply,
          edgeLocalFCPairLinearMap_apply]
        change
          -(A + H * G) * (A⁻¹ * (H * V - U)) +
              H * (V + G * (A⁻¹ * (H * V - U))) =
            U
        calc
          -(A + H * G) * (A⁻¹ * (H * V - U)) +
              H * (V + G * (A⁻¹ * (H * V - U))) =
            H * V - A * (A⁻¹ * (H * V - U)) := by
              simp [Matrix.mul_add, Matrix.neg_mul, Matrix.add_mul,
                Matrix.mul_assoc, sub_eq_add_neg]
              abel
          _ = H * V - (H * V - U) := by rw [hx]
          _ = U := by abel
      · rw [LinearMap.comp_apply, edgeLocalFCPairLinearMapInverse_apply,
          edgeLocalFCPairLinearMap_apply]
        change
          -G * (A⁻¹ * (H * V - U)) +
              (V + G * (A⁻¹ * (H * V - U))) =
            V
        ext i j
        simp)
    (by
      apply LinearMap.ext
      intro v
      rcases v with ⟨F, C⟩
      have hpre :
          H * (-G * F + C) - (-(A + H * G) * F + H * C) = A * F := by
        simp [Matrix.mul_add, Matrix.neg_mul, Matrix.add_mul,
          Matrix.mul_assoc, sub_eq_add_neg]
        abel
      apply Prod.ext
      · rw [LinearMap.comp_apply, edgeLocalFCPairLinearMap_apply,
          edgeLocalFCPairLinearMapInverse_apply]
        change
          A⁻¹ * (H * (-G * F + C) - (-(A + H * G) * F + H * C)) =
            F
        rw [hpre]
        exact Matrix.nonsing_inv_mul_cancel_left A F hA
      · rw [LinearMap.comp_apply, edgeLocalFCPairLinearMap_apply,
          edgeLocalFCPairLinearMapInverse_apply]
        change
          (-G * F + C) +
              G * (A⁻¹ * (H * (-G * F + C) - (-(A + H * G) * F + H * C))) =
            C
        rw [hpre]
        rw [Matrix.nonsing_inv_mul_cancel_left A F hA]
        ext i j
        simp)

omit [Fintype κ] in
@[simp]
theorem edgeLocalFCPairLinearEquiv_apply
    (A : Matrix ρ ρ K) (H : Matrix ρ μ K) (G : Matrix μ ρ K)
    (hA : IsUnit A.det)
    (v : EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K)) :
    edgeLocalFCPairLinearEquiv
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) A H G hA v =
      edgeLocalFCPairLinearMap
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) A H G v :=
  rfl

omit [Fintype κ] in
@[simp]
theorem edgeLocalFCPairLinearEquiv_symm_apply
    (A : Matrix ρ ρ K) (H : Matrix ρ μ K) (G : Matrix μ ρ K)
    (hA : IsUnit A.det)
    (v : EdgeLocalFCPairTangent (ρ := ρ) (μ := μ) (κ := κ) (K := K)) :
    (edgeLocalFCPairLinearEquiv
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) A H G hA).symm v =
      edgeLocalFCPairLinearMapInverse
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) A H G v :=
  rfl

omit [DecidableEq ρ] [Fintype μ] [Fintype κ] in
/-- The edge-local lower shear has determinant one. -/
theorem edgeLocalFCPairLowerShear_det_eq_one
    [Finite μ] [Finite κ]
    (G : Matrix μ ρ K) :
    LinearMap.det
      (edgeLocalFCPairLowerShear
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) G).toLinearMap = 1 := by
  unfold edgeLocalFCPairLowerShear
  rw [linearEquiv_det_skewProd_toLinearMap_eq_mul]
  simp

omit [DecidableEq ρ] [Fintype ρ] [Fintype κ] in
/-- The edge-local upper shear has determinant one. -/
theorem edgeLocalFCPairUpperShear_det_eq_one
    [Finite ρ] [Finite κ]
    (H : Matrix ρ μ K) :
    LinearMap.det
      (edgeLocalFCPairUpperShear
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) H).toLinearMap = 1 := by
  unfold edgeLocalFCPairUpperShear
  rw [linearEquivUpperShear_det_eq_one]

omit [Fintype μ] in
/-- The edge-local diagonal map contributes only left multiplication by `-A`
on the `F` coordinate. -/
theorem edgeLocalFCPairDiagonal_det_eq
    [Finite μ]
    (A : Matrix ρ ρ K) :
    LinearMap.det
      (edgeLocalFCPairDiagonal
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) A) =
      (-A).det ^ Fintype.card κ := by
  unfold edgeLocalFCPairDiagonal
  rw [linearMap_det_prodMap_eq_mul, linearMap_det_mulLeftLinearMap,
    LinearMap.det_id]
  simp

/-- Exact determinant of the edge-local `(F,C)` pair map. -/
theorem edgeLocalFCPairLinearMap_det_eq
    (A : Matrix ρ ρ K) (H : Matrix ρ μ K) (G : Matrix μ ρ K) :
    LinearMap.det
      (edgeLocalFCPairLinearMap
        (ρ := ρ) (μ := μ) (κ := κ) (K := K) A H G) =
      (-A).det ^ Fintype.card κ := by
  rw [edgeLocalFCPairLinearMap]
  rw [LinearMap.det_comp, LinearMap.det_comp]
  rw [edgeLocalFCPairUpperShear_det_eq_one,
    edgeLocalFCPairDiagonal_det_eq, edgeLocalFCPairLowerShear_det_eq_one]
  simp

end EdgeLocalFCPair

end Aoyagi
end DLN
end DLNFibre
