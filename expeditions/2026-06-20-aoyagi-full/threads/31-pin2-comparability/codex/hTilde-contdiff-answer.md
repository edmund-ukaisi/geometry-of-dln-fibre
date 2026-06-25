**Q1**

**Yes.** Decisive reason: `ContDiffBump.contDiff` is genuinely `C^n` for arbitrary `n`, including `⊤`, and `Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension` provides `HasContDiffBump E` for finite-dimensional real normed spaces, not only inner-product norms. Since `tsupport χ ⊆ unitSet`, raw smoothness is only needed on the pole-free locus; off `tsupport χ`, the cutoff is locally zero.

**Q2**

1. **Cheapest if you allow changing local RLCT glue:** weaken `rlctAtOn_comp_localDiffeo` from global `ContDiff ℝ ⊤ f` to `ContDiffAt ℝ ⊤ f wstar`.  
   Blocking risk: medium. The file comment says this suffices, and the proof uses global smoothness only to get local continuity/differentiability near `wstar`; replace those by `ContDiffAt.eventually`. This avoids global cutoff smoothness entirely.

2. **Derivative-only shortcut inside current `hTilde`:** yes, `eTilde` from `deepestEFull_deriv` should work verbatim.  
   Blocking risk: low for math, medium in Lean. You still need `HasStrictFDerivAt coreAbsorb.symm id 0`, via `D shift(0)=0`. But this only solves (B); current (A) still blocks.

3. **Discharge current statement as-is:** prove global `ContDiff` of `schurCutoffShift`, then smoothness of `coreAbsorb.symm`, then compose.  
   Blocking risk: highest. This is straightforward but longer, especially because matrix inverse smoothness should be proved entrywise under the existing Pi/sup norm.

4. **Hope `Efull ∘ coreAbsorb.symm` is smooth without proving shift smooth:** not a good shortcut.  
   Blocking risk: high. Unless you prove a special cancellation theorem for `Efull`, you are just hiding the same pole/cutoff smoothness problem.

**Q3**

1. **Entrywise determinant smoothness**  
   ```lean
   theorem contDiffAt_matrix_det_of_entries
       {X n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
       [Fintype n] [DecidableEq n]
       {A : X → Matrix n n ℝ} {x : X}
       (hA : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i j) x) :
       ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y).det) x
   ```
   Load-bearing API: `Matrix.det_apply`, `ContDiffAt.sum`, `contDiffAt_prod`, `ContDiffAt.const_smul`. Risk: low.

2. **Entrywise adjugate smoothness**  
   ```lean
   theorem contDiffAt_matrix_adjugate_entry_of_entries
       {X n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
       [Fintype n] [DecidableEq n]
       {A : X → Matrix n n ℝ} {x : X}
       (hA : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i j) x)
       (i j : n) :
       ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y).adjugate i j) x
   ```
   Load-bearing API: `Matrix.adjugate_apply`, previous determinant lemma. Risk: medium-low.

3. **Entrywise matrix inverse smoothness on det-nonzero locus**  
   ```lean
   theorem contDiffAt_matrix_inv_entry_of_det_ne_zero
       {X n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
       [Fintype n] [DecidableEq n]
       {A : X → Matrix n n ℝ} {x : X}
       (hA : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i j) x)
       (hdet : (A x).det ≠ 0) (i j : n) :
       ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y)⁻¹ i j) x
   ```
   Load-bearing API: `Matrix.inv_def`, `Ring.inverse_eq_inv`, `contDiffAt_inv`, `ContDiffAt.mul`. Risk: medium. Prefer this over `contDiffAt_ringInverse` on matrices because the default matrix norm is Pi/sup-style.

4. **Inverse of `1 + readX`**  
   ```lean
   theorem contDiffAt_inv_one_add_readX_entry
       (H : Fin (L + 1) → ℕ) (r : ℕ)
       (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
       (s : Fin L)
       (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
       (hdet : (1 + readX H r hr hL p s).det ≠ 0)
       (i j : Fin r) :
       ContDiffAt ℝ (⊤ : ℕ∞)
         (fun q => ((1 + readX H r hr hL q s)⁻¹) i j) p
   ```
   Load-bearing API: previous inverse lemma plus existing `contDiff_readX_entry`. Risk: medium.

5. **Raw Schur correction smooth on `unitSet`**  
   ```lean
   theorem contDiffAt_schurCorrection_entry_of_mem_unitSet
       (H : Fin (L + 1) → ℕ) (r : ℕ)
       (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
       (s : Fin L)
       (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
       (hp : p ∈ unitSet H r hr hL)
       (i : Fin (deepestM H r s.castSucc)) (j : Fin (deepestM H r s.succ)) :
       ContDiffAt ℝ (⊤ : ℕ∞)
         (fun q => schurCorrection H r hr hL q s i j) p
   ```
   Load-bearing API: `Matrix.mul_apply`, `ContDiffAt.sum`, `ContDiffAt.mul`, `ContDiffAt.neg`, existing `contDiff_readY_entry`/`contDiff_readZ_entry`. Risk: medium.

6. **Raw flat shift smooth on `unitSet`**  
   ```lean
   theorem contDiffAt_schurShiftRaw_of_mem_unitSet
       (H : Fin (L + 1) → ℕ) (r : ℕ)
       (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
       (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
       (hp : p ∈ unitSet H r hr hL) :
       ContDiffAt ℝ (⊤ : ℕ∞) (schurShiftRaw H r hr hL) p
   ```
   Load-bearing API: `paramsEquivFlatCLE`, `paramsEquivFlatCLE_coe`, `ContinuousLinearEquiv.contDiff`, `contDiffAt_pi'`. Risk: medium.

7. **Smooth support cutoff lemma**  
   ```lean
   theorem contDiff_smul_of_contDiffAt_on_tsupport
       {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
       [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump X]
       (χ : ContDiffBump (0 : X)) (raw : X → E)
       (hraw : ∀ x ∈ tsupport (χ : X → ℝ),
         ContDiffAt ℝ (⊤ : ℕ∞) raw x) :
       ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x • raw x)
   ```
   Load-bearing API: `contDiff_iff_contDiffAt`, `ContDiffBump.contDiffAt`, `ContDiffAt.smul`, `ContDiffAt.congr_of_eventuallyEq`. Risk: medium-high only because Mathlib lacks a ready `contDiff_of_tsupport`.

8. **Global cutoff Schur shift smoothness**  
   ```lean
   theorem contDiff_schurCutoffShift
       (H : Fin (L + 1) → ℕ) (r : ℕ)
       (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
       ContDiff ℝ (⊤ : ℕ∞) (schurCutoffShift H r hr hL)
   ```
   Load-bearing API: previous cutoff lemma, `tsupport_cutoffBump_subset_unitSet`. Risk: medium.

9. **Smoothness of core shear inverse and `regStraightenOf2`**  
   ```lean
   theorem contDiff_coreShearSymm
       {Reg Core Spec : Type*}
       [NormedAddCommGroup Reg] [NormedSpace ℝ Reg]
       [NormedAddCommGroup Core] [NormedSpace ℝ Core]
       [NormedAddCommGroup Spec] [NormedSpace ℝ Spec]
       (shift : Reg × Spec → Core)
       (hshift : ContDiff ℝ (⊤ : ℕ∞) shift) :
       ContDiff ℝ (⊤ : ℕ∞)
         (fun q : Reg × (Core × Spec) =>
           (q.1, (q.2.1 - shift (q.1, q.2.2), q.2.2)))
   ```
   ```lean
   theorem contDiff_regStraightenOf2
       {R W : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
       [NormedAddCommGroup W] [NormedSpace ℝ W]
       (E_full : R × W → R)
       (hE : ContDiff ℝ (⊤ : ℕ∞) E_full) :
       ContDiff ℝ (⊤ : ℕ∞) (regStraightenOf2 E_full)
   ```
   Load-bearing API: `ContDiff.comp`, `ContDiff.prodMk`, `ContDiff.sub`, `contDiff_fst`, `contDiff_snd`. Risk: low.

10. **Derivative-zero and identity derivative lemmas**  
   ```lean
   theorem hasStrictFDerivAt_schurShiftRaw_zero
       (H : Fin (L + 1) → ℕ) (r : ℕ)
       (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
       HasStrictFDerivAt (schurShiftRaw H r hr hL) 0 0
   ```
   ```lean
   theorem hasStrictFDerivAt_schurCutoffShift_zero
       (H : Fin (L + 1) → ℕ) (r : ℕ)
       (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
       HasStrictFDerivAt (schurCutoffShift H r hr hL) 0 0
   ```
   ```lean
   theorem hasStrictFDerivAt_coreShearSymm_zero
       {Reg Core Spec : Type*}
       [NormedAddCommGroup Reg] [NormedSpace ℝ Reg]
       [NormedAddCommGroup Core] [NormedSpace ℝ Core]
       [NormedAddCommGroup Spec] [NormedSpace ℝ Spec]
       (shift : Reg × Spec → Core)
       (h0 : shift 0 = 0)
       (hderiv : HasStrictFDerivAt shift 0 0) :
       HasStrictFDerivAt
         (fun q : Reg × (Core × Spec) =>
           (q.1, (q.2.1 - shift (q.1, q.2.2), q.2.2)))
         (1 : Reg × (Core × Spec) →L[ℝ] Reg × (Core × Spec)) 0
   ```
   Load-bearing API: `HasStrictFDerivAt.mul'`, `HasStrictFDerivAt.comp`, `HasStrictFDerivAt.sub`, `hasStrictFDerivAt_id`, `HasStrictFDerivAt.congr_of_eventuallyEq`, `schurCutoffShift_eq_raw_of_mem_closedBall`. Risk: medium.

**Q4**

Confirm, mathematically. `coreAbsorb.symm q = (reg, core - shift(reg,spec), spec)`, and `D shift(0)=0` because `raw = -Z(1+X)⁻¹Y` has `Z(0)=Y(0)=0` and is degree at least two; the cutoff equals raw near `0`. Therefore `D(coreAbsorb.symm)(0)=id`, so `D(Efull ∘ coreAbsorb.symm)(0)=D(Efull)(0)`, and the `e` from `deepestEFull_deriv` should be the correct `eTilde`.