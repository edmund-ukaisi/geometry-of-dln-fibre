import DLNFibre.DLN.RLCT.Validate.RouteMSmearedContract
import DLNFibre.DLN.RLCT.Foundations.CoreSplitMP

/-!
# `RouteMSmearedPerFamily` — the ∀M (L = 2 first) smeared per-family `ψ_M` / `U` / `subBox` build

Discharges the per-family ingredients behind `routeMCore_box_diverges_smearedContract` (#159), over
OPAQUE widths, starting with **L = 2** (the worked `(2,3,1)`/`(1,2,1)` classes have `L = 2`: `front = A⁰`
a single factor, no prefix product). The L ≥ 3 front-prefix-product (`P = A⁰···A^{L−2}` telescoping) is a
SEPARATE gated sub-tide (controller, 2026-06-28) — surfaced when reached; not built here.

Design (`design.md` thread 59, from `certificate-genM-smeared.md` §2, validated 46/46): a single uniform
reparametrization (front | z-pivot + H̄-angular | S_bot), `ψ_M = paramsEquivFlat ∘ packM ∘ shearM` where
`shearM` is the `coreShear` skew-product (the rational `Λ₀` top-row shift, MP for any widths via the GENERAL
brick `measurePreserving_coreShear_measurable`), `R_M = pivotBlowupOn` (the sole Jacobian `|z|^{minAdm−1}`),
`U_M = ‖P₁H̄‖²` a genuine polynomial (`Λ₀` cancels). FLAG-1 (the `packM` opaque-width cast) handled via the
`Equiv.apply_symm_apply` / flat-index readback pattern (the `paramsEquivFlat` `FlatIdx` ordering align).

## Pre-staged API contracts (the bricks this build consumes — pinned as `example`s)

The durable contracts (skill: pre-stage uncertain API). These confirm the brick signatures compile at the
shapes the L = 2 build needs, BEFORE the cast-heavy fill.
-/

open MeasureTheory
open scoped ENNReal BigOperators Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ### Brick 1 — the general `coreShear` skew-product is measure-preserving (any widths) -/

example (a b c : ℕ) (shift : (Fin a → ℝ) × (Fin c → ℝ) → (Fin b → ℝ)) (hsh : Measurable shift) :
    MeasurePreserving
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) =>
        (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))
      volume volume :=
  measurePreserving_coreShear_measurable a b c shift hsh

/-! ### Brick 2 — `paramsEquivFlat M` is a measure-preserving `MeasurableEquiv` (the outer reshape) -/

example (M : Fin (L + 1) → ℕ) :
    MeasurePreserving (paramsEquivFlat M) (volume : Measure (Params M)) volume :=
  measurePreserving_paramsEquivFlat M

-- the inverse reshape `(paramsEquivFlat M).symm` is the generic `packM` (a `MeasurableEquiv`, MP);
-- its MP is `(measurePreserving_paramsEquivFlat M).symm …` — pinned at build time, not here.

/-! ### Brick 3 — the contract this build feeds (`routeMCore_box_diverges_smearedContract`) -/

example (M : Fin (L + 1) → ℕ)
    (ψ R : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (D : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ))
    (p : Fin (routeMAmbient M)) (h : ℕ)
    (hmp : MeasurePreserving ψ (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume)
    (hemb : MeasurableEmbedding ψ) (c' : ℝ) (ε : ℝ)
    (S : Set (Fin (routeMAmbient M) → ℝ)) (hSmeas : MeasurableSet S)
    (hSpre : S ⊆ (fun u => ψ (R u)) ⁻¹' (cubeBox (routeMAmbient M) ε))
    (hRderiv : ∀ u ∈ S, HasFDerivWithinAt R (D u) S u) (hRinj : Set.InjOn R S)
    (hRdet : ∀ u ∈ S, |(D u).det| = |u p| ^ h)
    (hSdiv : (∫⁻ u in S, ENNReal.ofReal (|u p| ^ h)
      * ENNReal.ofReal (|routeMCore M (ψ (R u))| ^ (-c'))) = ⊤) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-c')) = ⊤ :=
  routeMCore_box_diverges_smearedContract M ψ R D p h hmp hemb c' ε S hSmeas hSpre hRderiv hRinj hRdet
    hSdiv

/-! ### Sub-tide 1 — general matrix-inverse entrywise measurability (the `shiftM`/Λ₀ foundation)

The (2,3,1) `lam231_measurable` uses an explicit `2×2` cofactor inverse (no transport to opaque widths).
The GENERAL route, valid at any width: `A⁻¹ i j = (det A)⁻¹ • adjugate A i j` (`Matrix.inv_def`), with
`adjugate`/`det` continuous (hence measurable) in the entries and `(·)⁻¹` measurable. This unblocks the
opaque-width `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` shift measurability (FLAG-1, resolved). -/

/-- **General matrix-`det` entrywise measurability.** For a matrix-valued map with measurable ENTRIES,
`det (A x)` is measurable in `x`. Via `det_apply'` (`det = ∑_σ ε σ · ∏_i A (σ i) i`) + `Finset` sum/prod
measurability — avoids the `Matrix` `MeasurableSpace` instance (works entrywise, like `lam231`). -/
theorem measurable_matrixDet {X : Type*} [MeasurableSpace X] {n : ℕ}
    (A : X → Fin n → Fin n → ℝ) (hA : ∀ i j, Measurable (fun x => A x i j)) :
    Measurable (fun x => (Matrix.of (A x)).det) := by
  simp only [Matrix.det_apply']
  refine Finset.measurable_sum _ (fun σ _ => ?_)
  refine (measurable_const).mul (Finset.measurable_prod _ (fun i _ => ?_))
  exact hA (σ i) i

/-- **General matrix-`adjugate` entrywise measurability.** Each `adjugate (A x) i j = (updateRow j (e i)).det`
(`adjugate_apply`), a `det` of an entry-measurable matrix — measurable by `measurable_matrixDet`. -/
theorem measurable_matrixAdjugate {X : Type*} [MeasurableSpace X] {n : ℕ}
    (A : X → Fin n → Fin n → ℝ) (hA : ∀ i j, Measurable (fun x => A x i j)) (i j : Fin n) :
    Measurable (fun x => (Matrix.of (A x)).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  -- (updateRow (A x) j (Pi.single i 1)).det — entries measurable (updateRow swaps row j for a constant)
  refine measurable_matrixDet (fun x => (Matrix.of (A x)).updateRow j (Pi.single i 1)) (fun a b => ?_)
  by_cases haj : a = j
  · subst haj
    simp only [Matrix.updateRow_self]
    exact measurable_const
  · simp only [Matrix.updateRow_ne haj, Matrix.of_apply]
    exact hA a b

/-- **General matrix-inverse entrywise measurability (the `shiftM`/Λ₀ foundation).** For a matrix-valued
map with measurable ENTRIES, each inverse entry `(A x)⁻¹ i j` is measurable. Via `Matrix.inv_def`
(`A⁻¹ = (det A)⁻¹ • adjugate A`) + `measurable_matrixDet`/`measurable_matrixAdjugate` + `Measurable.inv`.
The opaque-width replacement for the `(2,3,1)` explicit-`2×2`-cofactor `lam231_measurable` (FLAG-1). -/
theorem measurable_matrixInv_entry {X : Type*} [MeasurableSpace X] {n : ℕ}
    (A : X → Fin n → Fin n → ℝ) (hA : ∀ i j, Measurable (fun x => A x i j)) (i j : Fin n) :
    Measurable (fun x => (Matrix.of (A x))⁻¹ i j) := by
  have hentry : ∀ x, (Matrix.of (A x))⁻¹ i j
      = (Matrix.of (A x)).det⁻¹ * (Matrix.of (A x)).adjugate i j := by
    intro x; rw [Matrix.inv_def]; simp [Matrix.smul_apply, smul_eq_mul]
  simp only [hentry]
  exact (measurable_matrixDet A hA).inv.mul (measurable_matrixAdjugate A hA i j)

/-- **Matrix-product entrywise measurability.** `(A·B) i j = ∑_k A i k · B k j` (`mul_apply`); a finite
sum of products of entry-measurable maps. The other reusable `Λ₀`-building block (`Λ₀ = (P₁ᵀP₁)⁻¹·P₁ᵀ·P₂`
is a chain of these + `measurable_matrixInv_entry`). -/
theorem measurable_matrixMul_entry {X : Type*} [MeasurableSpace X] {n m k : ℕ}
    (A : X → Fin n → Fin m → ℝ) (B : X → Fin m → Fin k → ℝ)
    (hA : ∀ i j, Measurable (fun x => A x i j)) (hB : ∀ i j, Measurable (fun x => B x i j))
    (i : Fin n) (j : Fin k) :
    Measurable (fun x => (Matrix.of (A x) * Matrix.of (B x)) i j) := by
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact Finset.measurable_sum _ (fun l _ => (hA i l).mul (hB l j))

/-- **Matrix-transpose entrywise measurability** (`Aᵀ i j = A j i`). -/
theorem measurable_matrixTranspose_entry {X : Type*} [MeasurableSpace X] {n m : ℕ}
    (A : X → Fin n → Fin m → ℝ) (hA : ∀ i j, Measurable (fun x => A x i j)) (i : Fin m) (j : Fin n) :
    Measurable (fun x => (Matrix.of (A x)).transpose i j) := by
  simp only [Matrix.transpose_apply, Matrix.of_apply]; exact hA j i

/-! ### Sub-tide 2 — the rational `Λ₀` shift entrywise measurability (the `shiftM` content) -/

/-- **The `Λ₀ = (P₁ᵀP₁)⁻¹·P₁ᵀ·P₂` entrywise measurability** — the rational smeared-chart routing, at OPAQUE
widths. Given entry-measurable `P₁ : n×r` and `P₂ : n×c`, each entry of `Λ₀ : r×c` is measurable. Composes
the toolkit: `Gram = P₁ᵀ·P₁` (`r×r`, mul∘transpose), `Gram⁻¹` (`measurable_matrixInv_entry`), then
`Gram⁻¹·(P₁ᵀ·P₂)` (two muls). The opaque-width replacement for `(2,3,1)`'s explicit-`2×2`-cofactor
`lam231_measurable` — the `Λ₀` pole is invisible (`(·)⁻¹` totalized, `a⁻¹ = 0` at the pole). -/
theorem measurable_lamEntry {X : Type*} [MeasurableSpace X] {n r c : ℕ}
    (P₁ : X → Fin n → Fin r → ℝ) (P₂ : X → Fin n → Fin c → ℝ)
    (hP₁ : ∀ i j, Measurable (fun x => P₁ x i j)) (hP₂ : ∀ i j, Measurable (fun x => P₂ x i j))
    (i : Fin r) (j : Fin c) :
    Measurable (fun x =>
      (((Matrix.of (P₁ x))ᵀ * Matrix.of (P₁ x))⁻¹ * (Matrix.of (P₁ x))ᵀ * Matrix.of (P₂ x)) i j) := by
  -- thread BARE entry-functions through the toolkit (Matrix.of f = f definitionally), so each step's
  -- output entry-function feeds the next lemma's `∀ a b, Measurable (fun x => A x a b)` hypothesis.
  -- P₁ᵀ as an entry-function
  set p1t : X → Fin r → Fin n → ℝ := fun x a b => P₁ x b a with hp1t
  have hp1t_meas : ∀ a b, Measurable (fun x => p1t x a b) := fun a b => hP₁ b a
  -- Gram = P₁ᵀ·P₁ as an entry-function (∑_l P₁ x l a · P₁ x l b)
  set gram : X → Fin r → Fin r → ℝ := fun x a b => (Matrix.of (p1t x) * Matrix.of (P₁ x)) a b with hgram
  have hgram_meas : ∀ a b, Measurable (fun x => gram x a b) :=
    fun a b => measurable_matrixMul_entry p1t P₁ hp1t_meas hP₁ a b
  -- Gram⁻¹ as an entry-function
  set ginv : X → Fin r → Fin r → ℝ := fun x a b => (Matrix.of (gram x))⁻¹ a b with hginv
  have hginv_meas : ∀ a b, Measurable (fun x => ginv x a b) :=
    fun a b => measurable_matrixInv_entry gram hgram_meas a b
  -- Gram⁻¹·P₁ᵀ as an entry-function
  set gp : X → Fin r → Fin n → ℝ := fun x a b => (Matrix.of (ginv x) * Matrix.of (p1t x)) a b with hgp
  have hgp_meas : ∀ a b, Measurable (fun x => gp x a b) :=
    fun a b => measurable_matrixMul_entry ginv p1t hginv_meas hp1t_meas a b
  -- the final product (Gram⁻¹·P₁ᵀ)·P₂ — entry (i,j) measurable; defeq to the goal
  have hfin := measurable_matrixMul_entry gp P₂ hgp_meas hP₂ i j
  exact hfin

/-! ### Sub-tide 3 — the general `shearM` is measure-preserving (conjugate of `coreShear` by `splitOfCoreSet`)

`shearM := splitOfCoreSet.symm ∘ coreShear ∘ splitOfCoreSet` — the smeared shear in flat coordinates,
conjugating the abstract `coreShear` skew-product (which adds `shift(Reg, Spec)` to the Core block) by the
`coreSet`-driven block split (Reg = ∅, Core = `coreSet`, Spec = `coreSetᶜ`, genm-splitm's
`CoreSplitMP`). MP for ANY `coreSet` + ANY measurable `shift`, hence a total `MeasurableEquiv` (no pole
obstruction — the rational `Λ₀` enters only the measurable `shift`). The per-family instance (`shearM_conj`)
supplies `coreSet` = the kept-row flat-indices + `shift` = `−Λ₀·S_bot` (measurable by `measurable_lamEntry`). -/

/-- **The general smeared shear `shearM` is measure-preserving.** For any `coreSet : Finset (Fin N)` and any
measurable `shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ)`, the conjugate
`splitOfCoreSet.symm ∘ coreShear[shift] ∘ splitOfCoreSet` is measure-preserving on `Fin N → ℝ`. The
composition of `measurePreserving_splitOfCoreSet`, the `coreShear` skew-product brick, and the symm. -/
theorem measurePreserving_shearM {N : ℕ} (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ))
    (hshift : Measurable shift) :
    MeasurePreserving
      (fun u : Fin N → ℝ =>
        (splitOfCoreSet coreSet).symm
          (let q := splitOfCoreSet coreSet u; (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2))))
      (volume : Measure (Fin N → ℝ)) volume := by
  have hsplit : MeasurePreserving (splitOfCoreSet coreSet)
      (volume : Measure (Fin N → ℝ)) volume := measurePreserving_splitOfCoreSet coreSet
  have hcore : MeasurePreserving
      (fun q : (Fin 0 → ℝ) × ((Fin coreSet.card → ℝ) × (Fin coreSetᶜ.card → ℝ)) =>
        (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))
      volume volume :=
    measurePreserving_coreShear_measurable 0 coreSet.card coreSetᶜ.card shift hshift
  -- shearM = symm ∘ coreShear ∘ split  (MP composition; symm is MP since splitOfCoreSet is a MeasurableEquiv)
  have hsymm : MeasurePreserving (splitOfCoreSet coreSet).symm volume
      (volume : Measure (Fin N → ℝ)) :=
    hsplit.symm (splitOfCoreSet coreSet)
  exact hsymm.comp (hcore.comp hsplit)

/-! ### Sub-tide 4 — the general smeared source box `smearedSubBox` (the contract's `S`)

The achiever source set, ∀M: pin the radial pivot coord `p` into `Ioo 0 δ` (so `|u p| > 0`, the radial
det non-degenerate + the box image small) and ALL other coords into `Icc (−δ) δ`. The general analog of
`(2,3,1)`'s `subBox231` (which pins `u 6 ∈ Ioo 0 δ` + the rest in small `Icc`s). Used as the contract's
measurable source `S` (its `measurableSet` here; the containment + divergence consume the chart). -/

/-- **The general smeared source box.** `smearedSubBox p δ = {u | u p ∈ Ioo 0 δ ∧ ∀ k ≠ p, u k ∈ Icc −δ δ}`
— the pivot coord positive-and-small, the rest small. -/
def smearedSubBox {N : ℕ} (p : Fin N) (δ : ℝ) : Set (Fin N → ℝ) :=
  {u | u p ∈ Set.Ioo (0 : ℝ) δ ∧ ∀ k, k ≠ p → u k ∈ Set.Icc (-δ) δ}

/-- `smearedSubBox p δ` is measurable (a finite intersection of coordinate-preimages of `Ioo`/`Icc`). -/
theorem measurableSet_smearedSubBox {N : ℕ} (p : Fin N) (δ : ℝ) :
    MeasurableSet (smearedSubBox p δ) := by
  have hpiv : MeasurableSet {u : Fin N → ℝ | u p ∈ Set.Ioo (0 : ℝ) δ} :=
    measurableSet_preimage (measurable_pi_apply p) measurableSet_Ioo
  have hrest : MeasurableSet {u : Fin N → ℝ | ∀ k, k ≠ p → u k ∈ Set.Icc (-δ) δ} := by
    have heq : {u : Fin N → ℝ | ∀ k, k ≠ p → u k ∈ Set.Icc (-δ) δ}
        = ⋂ k ∈ (Finset.univ.erase p), {u : Fin N → ℝ | u k ∈ Set.Icc (-δ) δ} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_erase, Finset.mem_univ, and_true]
    rw [heq]
    exact Finset.measurableSet_biInter _ (fun k _ =>
      measurableSet_preimage (measurable_pi_apply k) measurableSet_Icc)
  exact hpiv.inter hrest

end DLNFibre.DLN.RLCT
