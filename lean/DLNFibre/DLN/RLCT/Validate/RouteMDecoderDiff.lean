import DLNFibre.DLN.RLCT.Validate.RouteMChainDiff
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# `RouteMDecoderDiff` — b-FrameM-2 assembly (3): the decoder block-constructor differentiability atoms

The decoder block-constructor differentiability atoms for b-FrameM-2 (`item3-frameM-buildspec.md`): the
Schur-frame kept block `bmatStack = [K ; X·K]` and the `u`-carrier `rmatPad = [[0,0],[0,E]]` are
`DifferentiableAt` in their matrix arguments. With `RouteMChainDiff`'s `chainQ`/`chainA` atoms, these
discharge the per-layer `Cgen`/`Agen` differentiability (the residual of
`RouteMChartDiff.phiFlatLiveR1_differentiableAt_of_Agen`).

**The same cast-avoiding route** (Sum-indexed intermediates → per-entry): `bmatStack`/`rmatPad` assemble
over `Fin _ ⊕ Fin _` SUM-indexed spaces (no norm instance), so differentiate PER-ENTRY — decompose the
row/col index via `finSumFinEquiv`, then the banked entry laws (`bmatStack_top`/`_bot`,
`rmatPad_*Add_*Add`) reduce each entry to `K`/`X·K`/`E`/`0`, each differentiable.

* `rmatPad_castAdd_castAdd` / `rmatPad_castAdd_natAdd` — the two missing top-row (`= 0`) entry laws of
  `rmatPad` (the codebase had only the bottom-row `_natAdd_*` laws); derived here for the full 4-way
  `fromBlocks` per-entry case split.
* `diffAt_bmatStack` — `x ↦ bmatStack M t k hdesc (K x) (X x)` differentiable (`[K ; X·K]`, the kept
  block; `X·K` via `DifferentiableAt.matMul`).
* `diffAt_rmatPad` — `x ↦ rmatPad M t s h1 h2 (E x)` differentiable (`[[0,0],[0,E]]`, the `u`-carrier).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (Mathlib calculus + the banked matrix fderiv).
-/

open scoped BigOperators
open Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The two missing `rmatPad` top-row (`= 0`) entry laws -/

section RmatZero
variable {𝕜 : Type} [CommRing 𝕜]

/-- **`rmatPad` kept×kept law**: the top (kept) row, kept column entry is `0` (the `fromBlocks` `₁₁`
zero block). -/
theorem rmatPad_castAdd_castAdd {M t : Fin (L + 1) → ℕ} {s : ℕ}
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) 𝕜)
    (i : Fin (Text M t (s + 1))) (j : Fin (Text M t (s + 1))) :
    rmatPad M t s h1 h2 E
        (Fin.cast (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by omega)
          (Fin.castAdd (Text M t s - Text M t (s + 1)) i))
        (Fin.cast (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)
          (Fin.castAdd (Wext M s - Text M t (s + 1)) j))
      = 0 := by
  simp only [rmatPad, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply,
    finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]

/-- **`rmatPad` kept×residual law**: the top (kept) row, residual column entry is `0` (the `fromBlocks`
`₁₂` zero block). -/
theorem rmatPad_castAdd_natAdd {M t : Fin (L + 1) → ℕ} {s : ℕ}
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) 𝕜)
    (i : Fin (Text M t (s + 1))) (j : Fin (Wext M s - Text M t (s + 1))) :
    rmatPad M t s h1 h2 E
        (Fin.cast (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by omega)
          (Fin.castAdd (Text M t s - Text M t (s + 1)) i))
        (Fin.cast (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)
          (Fin.natAdd (Text M t (s + 1)) j))
      = 0 := by
  simp only [rmatPad, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply,
    finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

end RmatZero

/-! ## The decoder block-constructor differentiability atoms -/

/-- **`bmatStack` is differentiable in its `(K, X)` arguments.** `bmatStack = [K ; X·K]`; per-row
(`finSumFinEquiv`): the top rows are `K` (differentiable), the bottom rows are `X·K`
(`DifferentiableAt.matMul`). The Schur-frame kept block `Bmat` differentiability. -/
theorem diffAt_bmatStack (M t : Fin (L + 1) → ℕ) (k : ℕ) (hdesc : Text M t (k + 1) ≤ Text M t k)
    {N' : ℕ} (Kf : (Fin N' → ℝ) → Matrix (Fin (Text M t (k + 1))) (Fin (Text M t (k + 1))) ℝ)
    (Xf : (Fin N' → ℝ) → Matrix (Fin (Text M t k - Text M t (k + 1))) (Fin (Text M t (k + 1))) ℝ)
    (u : Fin N' → ℝ) (hK : DifferentiableAt ℝ Kf u) (hX : DifferentiableAt ℝ Xf u) :
    DifferentiableAt ℝ (fun x => bmatStack M t k hdesc (Kf x) (Xf x)) u := by
  apply differentiableAt_pi.mpr; intro r
  apply differentiableAt_pi.mpr; intro j
  set hsum : Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k := by omega
  rw [show r = Fin.cast hsum (finSumFinEquiv (finSumFinEquiv.symm (Fin.cast hsum.symm r))) from by
    simp]
  set s := finSumFinEquiv.symm (Fin.cast hsum.symm r) with hs
  clear_value s
  cases s with
  | inl a =>
    rw [show (fun x => bmatStack M t k hdesc (Kf x) (Xf x)
        (Fin.cast hsum (finSumFinEquiv (Sum.inl a))) j) = fun x => Kf x a j from by
      funext x; rw [show finSumFinEquiv (Sum.inl a) = Fin.castAdd _ a from rfl, bmatStack_top]]
    exact differentiableAt_pi.mp (differentiableAt_pi.mp hK a) j
  | inr b =>
    -- rewrite the (X·K) entry to its explicit sum form, so the matMul-whnf is avoided.
    rw [show (fun x => bmatStack M t k hdesc (Kf x) (Xf x)
        (Fin.cast hsum (finSumFinEquiv (Sum.inr b))) j)
          = fun x => ∑ kk, Xf x b kk * Kf x kk j from by
      funext x
      rw [show finSumFinEquiv (Sum.inr b) = Fin.natAdd _ b from rfl, bmatStack_bot, Matrix.mul_apply]]
    apply DifferentiableAt.fun_sum; intro kk _
    exact (differentiableAt_pi.mp (differentiableAt_pi.mp hX b) kk).mul
      (differentiableAt_pi.mp (differentiableAt_pi.mp hK kk) j)

/-- **`rmatPad` is differentiable in its `E` argument.** `rmatPad = [[0,0],[0,E]]`; per-entry, both
indices `finSumFinEquiv`-decomposed (the 4-way `fromBlocks` split): the bottom-right block is `E`
(differentiable), the other three blocks are `0` (`differentiableAt_const`). The `u`-carrier `Rmat`
differentiability. -/
theorem diffAt_rmatPad (M t : Fin (L + 1) → ℕ) (s : ℕ) (h1 : Text M t (s + 1) ≤ Text M t s)
    (h2 : Text M t (s + 1) ≤ Wext M s) {N' : ℕ}
    (Ef : (Fin N' → ℝ) →
      Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (u : Fin N' → ℝ) (hE : DifferentiableAt ℝ Ef u) :
    DifferentiableAt ℝ (fun x => rmatPad M t s h1 h2 (Ef x)) u := by
  apply differentiableAt_pi.mpr; intro r
  apply differentiableAt_pi.mpr; intro col
  set hsr : Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s := by omega
  set hsc : Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s := by omega
  rw [show r = Fin.cast hsr (finSumFinEquiv (finSumFinEquiv.symm (Fin.cast hsr.symm r))) from by simp,
      show col = Fin.cast hsc (finSumFinEquiv (finSumFinEquiv.symm (Fin.cast hsc.symm col))) from by
        simp]
  set sr := finSumFinEquiv.symm (Fin.cast hsr.symm r) with hsrr; clear_value sr
  set sc := finSumFinEquiv.symm (Fin.cast hsc.symm col) with hscc; clear_value sc
  cases sr with
  | inl i =>
    cases sc with
    | inl j =>
      rw [show (fun x => rmatPad M t s h1 h2 (Ef x)
          (Fin.cast hsr (finSumFinEquiv (Sum.inl i))) (Fin.cast hsc (finSumFinEquiv (Sum.inl j))))
          = fun _ => (0 : ℝ) from by
        funext x
        rw [show finSumFinEquiv (Sum.inl i) = Fin.castAdd _ i from rfl,
            show finSumFinEquiv (Sum.inl j) = Fin.castAdd _ j from rfl, rmatPad_castAdd_castAdd]]
      exact differentiableAt_const _
    | inr j =>
      rw [show (fun x => rmatPad M t s h1 h2 (Ef x)
          (Fin.cast hsr (finSumFinEquiv (Sum.inl i))) (Fin.cast hsc (finSumFinEquiv (Sum.inr j))))
          = fun _ => (0 : ℝ) from by
        funext x
        rw [show finSumFinEquiv (Sum.inl i) = Fin.castAdd _ i from rfl,
            show finSumFinEquiv (Sum.inr j) = Fin.natAdd _ j from rfl, rmatPad_castAdd_natAdd]]
      exact differentiableAt_const _
  | inr i =>
    cases sc with
    | inl j =>
      rw [show (fun x => rmatPad M t s h1 h2 (Ef x)
          (Fin.cast hsr (finSumFinEquiv (Sum.inr i))) (Fin.cast hsc (finSumFinEquiv (Sum.inl j))))
          = fun _ => (0 : ℝ) from by
        funext x
        rw [show finSumFinEquiv (Sum.inr i) = Fin.natAdd _ i from rfl,
            show finSumFinEquiv (Sum.inl j) = Fin.castAdd _ j from rfl, rmatPad_natAdd_castAdd]]
      exact differentiableAt_const _
    | inr j =>
      rw [show (fun x => rmatPad M t s h1 h2 (Ef x)
          (Fin.cast hsr (finSumFinEquiv (Sum.inr i))) (Fin.cast hsc (finSumFinEquiv (Sum.inr j))))
          = fun x => Ef x i j from by
        funext x
        rw [show finSumFinEquiv (Sum.inr i) = Fin.natAdd _ i from rfl,
            show finSumFinEquiv (Sum.inr j) = Fin.natAdd _ j from rfl, rmatPad_natAdd_natAdd]]
      exact differentiableAt_pi.mp (differentiableAt_pi.mp hE i) j

end DLNFibre.DLN.RLCT
