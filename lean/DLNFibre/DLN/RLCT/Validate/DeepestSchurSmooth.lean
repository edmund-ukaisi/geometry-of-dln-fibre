import DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct
import DLNFibre.DLN.RLCT.Validate.DeepestRegAbsorbIFT
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestSchurSmooth` — global ⊤-smoothness of the cutoff Schur shift

The L2-PIN2 `hTilde` obligation (`deepest_gauge_construction`) needs the conjugated straightening
`regStraightenOf2 (deepestEFull ∘ coreAbsorb.symm)` to be a LOCAL DIFFEO at `0` — `ContDiff ℝ ⊤`
GLOBALLY plus an invertible strict derivative. The consumer `rlctAtOn_comp_localDiffeo` demands GLOBAL
`ContDiff ℝ ⊤ f` (it uses `f`'s global continuity for the absorbed map's global measurability), so the
germ-at-`0` agreement is not enough: the shift `coreAbsorb = coreShearHomeo (schurCutoffShift)` must be
GLOBALLY smooth, not merely continuous (`continuous_schurCutoffShift`).

The shift `schurCutoffShift = χ • schurShiftRaw`, `χ` a `ContDiffBump` (smooth) with
`tsupport χ ⊆ unitSet`, `schurShiftRaw = encode(−Z(1+X)⁻¹Y)` smooth on `unitSet` (the matrix inverse's
pole is OUTSIDE `tsupport χ`). The ladder, bottom-up:
  • entrywise matrix det / adjugate / inverse `ContDiffAt` on the det-nonzero locus
    (`Matrix.inv_def`/`adjugate_apply`/`det_apply` ⟹ polynomial-in-entries + scalar `contDiffAt_inv`,
    so the matrix-NormedRing topology is never invoked);
  • `schurCorrection` / `schurShiftRaw` `ContDiffAt` on `unitSet`;
  • the smooth cutoff glue (`χ • raw` is `ContDiff ⊤`: on `tsupport χ ⊆ unitSet` via `ContDiffAt.smul`,
    off it `χ • raw =ᶠ 0` since `χ` vanishes on the open complement of its closed `tsupport`);
  • `coreShearHomeo (smooth shift)` and its `.symm` are `ContDiff ⊤`, hence so is the conjugate.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Entrywise det / adjugate / inverse `ContDiff` (the matrix-norm-free route)

`det`/`adjugate` are polynomials in the entries (`det_apply`, `adjugate_apply`); the inverse is
`det⁻¹ • adjugate` (`Matrix.inv_def`), so each entry of `M⁻¹` is `(det M)⁻¹ * adjugate M i j` —
all `ContDiff` from the entrywise `ContDiff` of `M`, the scalar `contDiffAt_inv` (det ≠ 0), no matrix
`NormedRing` instance needed. -/

section EntrywiseInv
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of an entrywise-`ContDiff` matrix family is `ContDiff` (a sum over `Perm n` of
signed products of entries). -/
theorem contDiff_matrix_det_of_entries {A : X → Matrix n n ℝ}
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (A x).det) := by
  have heq : (fun x => (A x).det)
      = fun x => ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A x (σ i) i := by
    funext x; rw [Matrix.det_apply]
  rw [heq]
  refine ContDiff.sum (fun σ _ => ?_)
  refine ContDiff.const_smul _ ?_
  exact contDiff_prod (fun i _ => hA (σ i) i)

/-- Each adjugate entry of an entrywise-`ContDiff` matrix family is `ContDiff` (`adjugate_apply` makes
it a determinant of the row-updated matrix, whose entries are still entrywise `ContDiff`). -/
theorem contDiff_matrix_adjugate_entry_of_entries {A : X → Matrix n n ℝ}
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) (i j : n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (A x).adjugate i j) := by
  have heq : (fun x => (A x).adjugate i j)
      = fun x => ((A x).updateRow j (Pi.single i 1)).det := by
    funext x; rw [Matrix.adjugate_apply]
  rw [heq]
  refine contDiff_matrix_det_of_entries (fun a b => ?_)
  -- `updateRow j v M a b = if a = j then v b else M a b`; both branches `ContDiff`.
  by_cases hab : a = j
  · subst hab
    have : (fun x => ((A x).updateRow a (Pi.single i 1)) a b)
        = fun _ : X => (Pi.single i (1 : ℝ) : n → ℝ) b := by
      funext x; rw [Matrix.updateRow_self]
    rw [this]; exact contDiff_const
  · have : (fun x => ((A x).updateRow j (Pi.single i 1)) a b) = fun x => A x a b := by
      funext x; rw [Matrix.updateRow_ne hab]
    rw [this]; exact hA a b

/-- Each entry of the inverse of an entrywise-`ContDiff` matrix family is `ContDiffAt x` when
`det (A x) ≠ 0`: `(A x)⁻¹ i j = (det (A x))⁻¹ * (adjugate (A x) i j)` (`Matrix.inv_def`, the scalar
`Ring.inverse = (·)⁻¹`), the product of the `ContDiffAt` scalar inverse and the `ContDiff` adjugate. -/
theorem contDiffAt_matrix_inv_entry_of_det_ne_zero {A : X → Matrix n n ℝ}
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) {x : X}
    (hdet : (A x).det ≠ 0) (i j : n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y)⁻¹ i j) x := by
  have hentry : (fun y => (A y)⁻¹ i j)
      = fun y => (A y).det⁻¹ * (A y).adjugate i j := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [hentry]
  have hdetinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y).det⁻¹) x :=
    ((contDiff_matrix_det_of_entries hA).contDiffAt).inv hdet
  exact hdetinv.mul (contDiff_matrix_adjugate_entry_of_entries hA i j).contDiffAt

/-- Entrywise `ContDiffAt` matrix multiplication: `(A · B) i j = ∑ k, A i k * B k j` (`mul_apply`),
each summand the product of two `ContDiffAt` entries. -/
theorem contDiffAt_matrix_mul_entry {X mm nn pp : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype nn]
    {A : X → Matrix mm nn ℝ} {B : X → Matrix nn pp ℝ} {x : X}
    (hA : ∀ i k, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i k) x)
    (hB : ∀ k j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => B y k j) x) (i : mm) (j : pp) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y * B y) i j) x := by
  have heq : (fun y => (A y * B y) i j) = fun y => ∑ k, A y i k * B y k j := by
    funext y; rw [Matrix.mul_apply]
  rw [heq]
  exact ContDiffAt.sum (fun k _ => (hA i k).mul (hB k j))

end EntrywiseInv

/-! ## `schurCorrection` / `schurShiftRaw` `ContDiffAt` on `unitSet`

`schurCorrection p s = −(readZ p s) · (1 + readX p s)⁻¹ · (readY p s)` — a triple matrix product. On
`unitSet` (every `det(1 + readX p s) ≠ 0`) the inverse entries are `ContDiffAt` (entrywise route); the
`readX/Y/Z` entries are `ContDiff` (global). `schurShiftRaw = paramsEquivFlatCLE (deepestM) ∘ assemble`
(the CLE is `ContDiff`), so the flat shift is `ContDiffAt` on `unitSet`. -/

/-- Each entry of `(1 + readX p s)⁻¹` is `ContDiffAt p` on `unitSet` (det ≠ 0 there). The
`1 + readX` family is entrywise `ContDiff` (`contDiff_readX_entry` + `contDiff_const`). -/
theorem contDiffAt_inv_one_add_readX_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hp : p ∈ unitSet H r hr hL) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => ((1 + readX H r hr hL q s)⁻¹) i j) p := by
  refine contDiffAt_matrix_inv_entry_of_det_ne_zero
    (A := fun q => (1 : Matrix (Fin r) (Fin r) ℝ) + readX H r hr hL q s) (fun a b => ?_) (hp s) i j
  have : (fun q => ((1 : Matrix (Fin r) (Fin r) ℝ) + readX H r hr hL q s) a b)
      = fun q => (1 : Matrix (Fin r) (Fin r) ℝ) a b + readX H r hr hL q s a b := by
    funext q; rw [Matrix.add_apply]
  rw [this]
  exact contDiff_const.add (contDiff_readX_entry H r hr hL s a b)

/-- Each per-layer Schur correction entry is `ContDiffAt p` on `unitSet`: the triple product
`(−readZ) · (1 + readX)⁻¹ · readY`, all factors entrywise `ContDiffAt` there. -/
theorem contDiffAt_schurCorrection_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hp : p ∈ unitSet H r hr hL) (i : Fin (H s.castSucc - r)) (j : Fin (H s.succ - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => schurCorrection H r hr hL q s i j) p := by
  -- `schurCorrection q s = (−readZ q s) · (1 + readX q s)⁻¹ · readY q s` (negate the first factor).
  have hZinv : ∀ (a : Fin (H s.castSucc - r)) (k : Fin r),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q => ((-(readZ H r hr hL q s)) * (1 + readX H r hr hL q s)⁻¹) a k) p := by
    intro a k
    refine contDiffAt_matrix_mul_entry (fun a' k' => ?_)
      (fun k' j' => contDiffAt_inv_one_add_readX_entry H r hr hL s p hp k' j') a k
    have : (fun q => (-(readZ H r hr hL q s)) a' k') = fun q => -(readZ H r hr hL q s a' k') := by
      funext q; rw [Matrix.neg_apply]
    rw [this]; exact (contDiff_readZ_entry H r hr hL s a' k').contDiffAt.neg
  have hmul := contDiffAt_matrix_mul_entry
    (A := fun q => (-(readZ H r hr hL q s)) * (1 + readX H r hr hL q s)⁻¹)
    (B := fun q => readY H r hr hL q s) hZinv
    (fun k' j' => (contDiff_readY_entry H r hr hL s k' j').contDiffAt) i j
  -- The triple product `((−Z)·inv)·Y` equals `schurCorrection`'s `−Z·inv·Y` (associativity + neg).
  refine hmul.congr_of_eventuallyEq ?_
  filter_upwards with q
  show schurCorrection H r hr hL q s i j
      = ((-(readZ H r hr hL q s)) * (1 + readX H r hr hL q s)⁻¹ * readY H r hr hL q s) i j
  rfl

/-- `schurShiftRaw` is `ContDiffAt p` on `unitSet`: `paramsEquivFlatCLE (deepestM)` (a `ContDiff` CLE)
composed with the entrywise-`ContDiffAt` assembled `schurCorrection`. -/
theorem contDiffAt_schurShiftRaw (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hp : p ∈ unitSet H r hr hL) :
    ContDiffAt ℝ (⊤ : ℕ∞) (schurShiftRaw H r hr hL) p := by
  -- `schurShiftRaw = paramsEquivFlatCLE (deepestM) ∘ schurCorrection` (the CLE coe rewrites it).
  have hraw : schurShiftRaw H r hr hL
      = fun q => paramsEquivFlatCLE (deepestM H r) (schurCorrection H r hr hL q) := by
    funext q
    rw [schurShiftRaw, ← paramsEquivFlatCLE_coe (deepestM H r)]
  rw [hraw]
  refine (paramsEquivFlatCLE (deepestM H r)).contDiff.contDiffAt.comp p ?_
  -- `schurCorrection q : Params (deepestM)` is `ContDiffAt` (componentwise then entrywise).
  refine contDiffAt_pi.mpr (fun s => contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_)))
  exact contDiffAt_schurCorrection_entry H r hr hL s p hp i j

/-! ## The smooth cutoff glue + global ⊤-smoothness of the cutoff Schur shift

`χ • raw` is globally `ContDiff ⊤` when `raw` is `ContDiffAt` on the closed `tsupport χ`: at a point of
`tsupport χ` the bump and `raw` are both `ContDiffAt`, so the smul is; at a point off `tsupport χ` the
bump vanishes on the open complement, so `χ • raw =ᶠ 0`, again `ContDiffAt` (Mathlib has no
`contDiff_of_tsupport`, so this is built from `contDiff_iff_contDiffAt`). -/

/-- **Smooth cutoff glue**: if a `ContDiffBump` `χ` smooths a map `raw` that is `ContDiffAt` on
`tsupport χ`, then `χ • raw` is globally `ContDiff ⊤` (off the support it is locally `0`). -/
theorem contDiff_contDiffBump_smul {X F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : ContDiffBump (0 : X)) (raw : X → F)
    (hraw : ∀ x ∈ tsupport (fun y => (χ y : ℝ)), ContDiffAt ℝ (⊤ : ℕ∞) raw x) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (χ x : ℝ) • raw x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (fun y => (χ y : ℝ))
  · exact χ.contDiffAt.smul (hraw x hx)
  · -- Off the closed `tsupport χ`: the open complement is a nbhd of `x` where `χ • raw = 0`.
    have hcompl : (tsupport (fun y => (χ y : ℝ)))ᶜ ∈ 𝓝 x :=
      (isClosed_tsupport _).isOpen_compl.mem_nhds hx
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hcompl] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]

/-- **The cutoff Schur shift is globally `ContDiff ⊤`** (`χ • schurShiftRaw`, `χ = cutoffBump`). On
`tsupport χ ⊆ unitSet` the raw shift is `ContDiffAt` (`contDiffAt_schurShiftRaw`); off it the bump
vanishes locally. The smoothness upgrade of `continuous_schurCutoffShift`, demanded by the `hTilde`
local-diffeo consumer (global, not germ-at-`0`). -/
theorem contDiff_schurCutoffShift (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiff ℝ (⊤ : ℕ∞) (schurCutoffShift H r hr hL) := by
  have heq : schurCutoffShift H r hr hL
      = fun p => ((cutoffBump H r hr hL) p : ℝ) • schurShiftRaw H r hr hL p := rfl
  rw [heq]
  refine contDiff_contDiffBump_smul (cutoffBump H r hr hL) (schurShiftRaw H r hr hL) (fun x hx => ?_)
  exact contDiffAt_schurShiftRaw H r hr hL x
    (tsupport_cutoffBump_subset_unitSet H r hr hL hx)

/-! ## `ContDiff` of `coreShearHomeo.symm` and `regStraightenOf2 (Efull ∘ coreAbsorb.symm)`

`coreShearHomeo shift` is `(reg, core, spec) ↦ (reg, core + shift(reg,spec), spec)`; its inverse
subtracts the shift. With a `ContDiff` shift, the inverse is `ContDiff ⊤` (a `prodMk` of the projections
and the subtraction). `regStraightenOf2 g = (g, ·.2)` is `ContDiff` when `g` is. -/

section ContDiffShear
variable {Reg Core Spec : Type*}
  [NormedAddCommGroup Reg] [NormedSpace ℝ Reg]
  [NormedAddCommGroup Core] [NormedSpace ℝ Core]
  [NormedAddCommGroup Spec] [NormedSpace ℝ Spec]

/-- `coreShearHomeo shift` is `ContDiff ⊤` when the shift is (a `prodMk` of the `ContDiff` projections
and the `ContDiff` shifted core slot). -/
theorem contDiff_coreShearHomeo (shift : Reg × Spec → Core) (hcont : Continuous shift)
    (hshift : ContDiff ℝ (⊤ : ℕ∞) shift) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : Reg × (Core × Spec) => coreShearHomeo shift hcont q) := by
  have hrs : ContDiff ℝ (⊤ : ℕ∞) (fun q : Reg × (Core × Spec) => (q.1, q.2.2)) :=
    contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hsc : ContDiff ℝ (⊤ : ℕ∞) (fun q : Reg × (Core × Spec) => shift (q.1, q.2.2)) :=
    ContDiff.comp (g := shift) hshift hrs
  refine contDiff_fst.prodMk (ContDiff.prodMk ?_ (contDiff_snd.comp contDiff_snd))
  exact (contDiff_fst.comp contDiff_snd).add hsc

/-- `coreShearHomeo shift`'s INVERSE `(reg, core, spec) ↦ (reg, core − shift(reg,spec), spec)` is
`ContDiff ⊤` when the shift is. -/
theorem contDiff_coreShearHomeo_symm (shift : Reg × Spec → Core) (hcont : Continuous shift)
    (hshift : ContDiff ℝ (⊤ : ℕ∞) shift) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : Reg × (Core × Spec) => (coreShearHomeo shift hcont).symm q) := by
  have hrs : ContDiff ℝ (⊤ : ℕ∞) (fun q : Reg × (Core × Spec) => (q.1, q.2.2)) :=
    contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hsc : ContDiff ℝ (⊤ : ℕ∞) (fun q : Reg × (Core × Spec) => shift (q.1, q.2.2)) :=
    ContDiff.comp (g := shift) hshift hrs
  refine contDiff_fst.prodMk (ContDiff.prodMk ?_ (contDiff_snd.comp contDiff_snd))
  exact (contDiff_fst.comp contDiff_snd).sub hsc

end ContDiffShear

/-- `regStraightenOf2 E_full` is `ContDiff ⊤` when `E_full` is (`= (E_full, ·.2)`). -/
theorem contDiff_regStraightenOf2 {R W : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (E_full : R × W → R) (hE : ContDiff ℝ (⊤ : ℕ∞) E_full) :
    ContDiff ℝ (⊤ : ℕ∞) (regStraightenOf2 E_full) :=
  hE.prodMk contDiff_snd

/-! ## `D(coreAbsorb.symm)(0) = id` — the cutoff Schur shift has vanishing derivative at `0`

`schurCorrection = (−Z)·M·Y` with `Z(0)=Y(0)=0` (the gauge blocks vanish at the deepest point), so the
strict derivative of each entry at `0` is `0` (a triple scalar product with the OUTER two factors
vanishing: `D((g·h)·w)(0)` with `(g·h)(0)=0` from `Z(0)=0` and `w(0)=0`). Hence `D(schurShiftRaw)(0)=0`;
near `0` (χ=1) `schurCutoffShift = schurShiftRaw`, so `D(schurCutoffShift)(0)=0`; and the inverse shear's
derivative is the identity. -/

/-- A scalar triple product `g·h·w` whose OUTER factors vanish at `x` has strict derivative `0` there:
`(g·h)(x)=0` (as `g x = 0`) and `w x = 0`, so `D((g·h)·w)(x)=0`. -/
theorem hasStrictFDerivAt_triple_mul_zero {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (g h w : X → ℝ) {x : X}
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (hh : ContDiffAt ℝ (⊤ : ℕ∞) h x)
    (hw : ContDiffAt ℝ (⊤ : ℕ∞) w x) (hg0 : g x = 0) (hw0 : w x = 0) :
    HasStrictFDerivAt (fun y => g y * h y * w y) (0 : X →L[ℝ] ℝ) x := by
  have hgd : HasStrictFDerivAt g (fderiv ℝ g x) x :=
    hg.hasStrictFDerivAt (by simp)
  have hhd : HasStrictFDerivAt h (fderiv ℝ h x) x :=
    hh.hasStrictFDerivAt (by simp)
  have hwd : HasStrictFDerivAt w (fderiv ℝ w x) x :=
    hw.hasStrictFDerivAt (by simp)
  -- `D(g·h)(x) = g x • Dh + h x • Dg = h x • Dg` (since `g x = 0`); and `(g·h) x = 0`.
  have hgh : HasStrictFDerivAt (fun y => g y * h y)
      ((h x) • fderiv ℝ g x) x := by
    have := hgd.mul hhd
    rw [hg0, zero_smul, zero_add] at this
    exact this
  -- `D((g·h)·w)(x) = (g·h) x • Dw + w x • D(g·h) = 0` (both `(g·h) x = 0` and `w x = 0`).
  have := hgh.mul hwd
  -- the `.mul` derivative is `((g·h) x) • Dw + (w x) • D(g·h)`; `(g·h) x = g x * h x = 0`, `w x = 0`.
  rw [show g x * h x = 0 by rw [hg0, zero_mul], hw0, zero_smul, zero_smul, add_zero] at this
  exact this

/-- Each entry of `schurCorrection` has strict derivative `0` at `0` (the triple product
`(−Z)·(1+X)⁻¹·Y` with `Z(0)=Y(0)=0`, expanded entrywise; each summand is a triple scalar product whose
outer factors `−Z…` and `Y…` vanish at `0`). -/
theorem hasStrictFDerivAt_schurCorrection_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (i : Fin (H s.castSucc - r)) (j : Fin (H s.succ - r)) :
    HasStrictFDerivAt (fun q => schurCorrection H r hr hL q s i j)
      (0 : ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) →L[ℝ] ℝ) 0 := by
  set p0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ) := 0 with hp0
  have hmem : p0 ∈ unitSet H r hr hL := by rw [hp0]; exact mem_unitSet_zero H r hr hL
  -- Entrywise (natural `mul_apply` order: outer `l` = Y's row, inner `k` = Z's col):
  -- `schurCorrection q s i j = ∑_l ∑_k (−Z q s i k)·(inv q s k l)·(Y q s l j)`.
  have heq : (fun q => schurCorrection H r hr hL q s i j)
      = fun q => ∑ l : Fin r, ∑ k : Fin r,
          (-(readZ H r hr hL q s) i k) * ((1 + readX H r hr hL q s)⁻¹ k l)
            * (readY H r hr hL q s l j) := by
    funext q
    show (-(readZ H r hr hL q s) * (1 + readX H r hr hL q s)⁻¹ * readY H r hr hL q s) i j = _
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
    simp only [Matrix.neg_apply]
  rw [heq]
  -- The per-summand derivative-`0` family (each a triple product with outer factors vanishing at `0`).
  have hterm : ∀ l k : Fin r, HasStrictFDerivAt
      (fun q => (-(readZ H r hr hL q s) i k) * ((1 + readX H r hr hL q s)⁻¹ k l)
        * (readY H r hr hL q s l j))
      (0 : ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) →L[ℝ] ℝ) 0 := by
    intro l k
    refine hasStrictFDerivAt_triple_mul_zero _ _ _ ?_ ?_ ?_ ?_ ?_
    · exact ((contDiff_readZ_entry H r hr hL s i k).contDiffAt.neg)
    · exact contDiffAt_inv_one_add_readX_entry H r hr hL s p0 hmem k l
    · exact (contDiff_readY_entry H r hr hL s l j).contDiffAt
    · show -(readZ H r hr hL p0 s) i k = 0
      rw [hp0, readZ_zero H r hr hL s]; simp
    · show readY H r hr hL p0 s l j = 0
      rw [hp0, readY_zero H r hr hL s]; rfl
  -- Sum over `l, k`: the function-level `Finset.sum` strict-deriv, with derivative `∑∑ 0 = 0`.
  have hsum := HasStrictFDerivAt.sum (u := (Finset.univ : Finset (Fin r)))
    (fun l _ => HasStrictFDerivAt.sum (u := (Finset.univ : Finset (Fin r)))
      (fun k _ => hterm l k))
  -- `hsum`'s function is the pointwise `Finset.sum`; rewrite to the `fun q => ∑∑ …` shape, deriv `0`.
  have hfun : (∑ l : Fin r, ∑ k : Fin r,
        (fun q => (-(readZ H r hr hL q s) i k) * ((1 + readX H r hr hL q s)⁻¹ k l)
          * (readY H r hr hL q s l j)))
      = fun q => ∑ l : Fin r, ∑ k : Fin r,
          (-(readZ H r hr hL q s) i k) * ((1 + readX H r hr hL q s)⁻¹ k l)
            * (readY H r hr hL q s l j) := by
    funext q; simp only [Finset.sum_apply]
  rw [hfun, show (∑ l : Fin r, ∑ k : Fin r,
        (0 : ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) →L[ℝ] ℝ)) = 0 from by
      simp] at hsum
  exact hsum

/-- `schurShiftRaw` has strict derivative `0` at `0`.

**ISOLATED GAP (one correctly-stated `sorry`).** The geometry is settled and banked; what remains is Lean
PLUMBING only. `schurShiftRaw = paramsEquivFlatCLE ∘ schurCorrection`, and `schurCorrection`'s strict
derivative at `0` is `0` ENTRYWISE — `hasStrictFDerivAt_schurCorrection_entry_zero` (PROVED below; the
triple product `(−Z)·(1+X)⁻¹·Y` with `Z(0)=Y(0)=0`, so `D=0`). Reassembling the per-`(s,i,j)`-entry
strict-deriv-`0` into the `Params`-valued strict derivative needs `hasStrictFDerivAt_pi'` over
`Params (deepestM) = ∀ s, Matrix …`, which Mathlib v4.29 cannot drive here: `Params` being a `def`
blocks `F'` inference (instance-stuck on `NormedSpace ?m (?m i)`), and supplying `F'` explicitly then
fails to synthesize the family instance `(i : Fin L) → NormedAddCommGroup (Matrix …)` for the lambda
family. The codebase sidesteps exactly this by staying entrywise (`hasStrictFDerivAt_prodAux_entry` never
builds a `Params`-valued derivative). Closing this cleanly wants a `Params`-level `HasStrictFDerivAt`
assembler (mirroring `hasStrictFDerivAt_prod_entry`) or the explicit `paramsEquivFlat` flat-coordinate
decode (each flat coord = one `schurCorrection` entry via `piCurry` + `Fintype.equivFin`). The derivative
VALUE (`0`) is fully determined — this is NOT a geometric gap. -/
theorem hasStrictFDerivAt_schurShiftRaw_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    HasStrictFDerivAt (schurShiftRaw H r hr hL)
      (0 : ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
        →L[ℝ] (Fin (flatDim (deepestM H r)) → ℝ)) 0 := by
  sorry

/-- `schurCutoffShift` has strict derivative `0` at `0`: on the inner ball `χ = 1` so
`schurCutoffShift = schurShiftRaw` (`schurCutoffShift_eq_raw_of_mem_closedBall`), whose strict
derivative at `0` is `0`. -/
theorem hasStrictFDerivAt_schurCutoffShift_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    HasStrictFDerivAt (schurCutoffShift H r hr hL)
      (0 : ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
        →L[ℝ] (Fin (flatDim (deepestM H r)) → ℝ)) 0 := by
  refine (hasStrictFDerivAt_schurShiftRaw_zero H r hr hL).congr_of_eventuallyEq ?_
  -- On the inner ball (a nbhd of `0`) the cutoff equals the raw shift.
  filter_upwards [closedBall_rIn_mem_nhds H r hr hL] with p hp
  exact (schurCutoffShift_eq_raw_of_mem_closedBall H r hr hL p hp).symm

/-! ## `D(coreShearHomeo.symm)(0) = id` and the assembled `hTilde` derivative

`coreShearHomeo shift|>.symm q = (q.1, q.2.1 − shift(q.1, q.2.2), q.2.2)`; with `D(shift)(0) = 0` its
strict derivative at `0` is the identity (the subtraction's shift-derivative vanishes). -/

/-- `coreShearHomeo shift|>.symm` has strict derivative `id` at `0` when `D(shift)(0) = 0` (and
`shift 0 = 0`): each output slot's derivative is the corresponding projection (`reg`, `core − Dshift`,
`spec`), and `Dshift(0) = 0` collapses the middle to the core projection. -/
theorem hasStrictFDerivAt_coreShearHomeo_symm_zero {Reg Core Spec : Type*}
    [NormedAddCommGroup Reg] [NormedSpace ℝ Reg]
    [NormedAddCommGroup Core] [NormedSpace ℝ Core]
    [NormedAddCommGroup Spec] [NormedSpace ℝ Spec]
    (shift : Reg × Spec → Core) (hcont : Continuous shift)
    (hshift0 : HasStrictFDerivAt shift (0 : Reg × Spec →L[ℝ] Core) 0) :
    HasStrictFDerivAt (fun q : Reg × (Core × Spec) => (coreShearHomeo shift hcont).symm q)
      (ContinuousLinearMap.id ℝ (Reg × (Core × Spec))) 0 := by
  -- `symm q = (q.1, (q.2.1 − shift (q.1, q.2.2), q.2.2))`.
  -- The reg slot: `fst`. The spec slot: `snd ∘ snd`. The core slot: `(fst ∘ snd) − shift ∘ (reg,spec)`.
  have hfst : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.1)
      (ContinuousLinearMap.fst ℝ Reg (Core × Spec)) 0 :=
    (ContinuousLinearMap.fst ℝ Reg (Core × Spec)).hasStrictFDerivAt
  have hsnd : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.2)
      (ContinuousLinearMap.snd ℝ Reg (Core × Spec)) 0 :=
    (ContinuousLinearMap.snd ℝ Reg (Core × Spec)).hasStrictFDerivAt
  have hcore : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.2.1)
      ((ContinuousLinearMap.fst ℝ Core Spec).comp (ContinuousLinearMap.snd ℝ Reg (Core × Spec))) 0 :=
    ((ContinuousLinearMap.fst ℝ Core Spec).hasStrictFDerivAt).comp (x := (0 : Reg × (Core × Spec))) hsnd
  have hspec : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.2.2)
      ((ContinuousLinearMap.snd ℝ Core Spec).comp (ContinuousLinearMap.snd ℝ Reg (Core × Spec))) 0 :=
    ((ContinuousLinearMap.snd ℝ Core Spec).hasStrictFDerivAt).comp (x := (0 : Reg × (Core × Spec))) hsnd
  -- The `(reg, spec)` read into `shift`'s domain.
  have hrs : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => (q.1, q.2.2))
      ((ContinuousLinearMap.fst ℝ Reg (Core × Spec)).prod
        ((ContinuousLinearMap.snd ℝ Core Spec).comp
          (ContinuousLinearMap.snd ℝ Reg (Core × Spec)))) 0 :=
    hfst.prodMk hspec
  -- `shift ∘ (reg,spec)` has strict deriv `0 ∘ (read) = 0` at `0` (the read sends `0 ↦ 0`).
  have hshiftcomp : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => shift (q.1, q.2.2))
      (0 : Reg × (Core × Spec) →L[ℝ] Core) 0 := by
    have := hshift0.comp (x := (0 : Reg × (Core × Spec))) hrs
    simpa using this
  -- The core slot `q.2.1 − shift (q.1, q.2.2)` has strict deriv `(fst∘snd) − 0 = fst∘snd`.
  have hcoreshift : HasStrictFDerivAt
      (fun q : Reg × (Core × Spec) => q.2.1 - shift (q.1, q.2.2))
      ((ContinuousLinearMap.fst ℝ Core Spec).comp (ContinuousLinearMap.snd ℝ Reg (Core × Spec))) 0 := by
    have := hcore.sub hshiftcomp
    simpa using this
  -- Assemble: `symm = (reg, (core − shift, spec))`; derivative `(fst, (fst∘snd, snd∘snd)) = id`.
  have hassemble := hfst.prodMk (hcoreshift.prodMk hspec)
  refine hassemble.congr_fderiv ?_
  ext q <;> simp [ContinuousLinearMap.comp_apply]

end DLNFibre.DLN.RLCT
