import DLNFibre.DLN.RLCT.Validate.RouteMFlatLDU
import DLNFibre.DLN.RLCT.Validate.RouteMFactorMaps

/-!
# `RouteMKLens` — the K-slot LDU reparametrization `kLDU` (∀M, sub-tide 2a)

The LDU lens that turns the FREE-K structured decoder into an LDU-coordinatized one, so the per-boundary
K-core determinant becomes a MONOMIAL (the `RouteMFlatLDU` wall-check fix; the opaque-width generalization
of the `(3,3,3,3)` `Kparam3333`). `kLDU x` rewrites, per boundary `k`, the K-slot block from its raw free
coordinates `Kraw = readK x k` to the LDU matrix `kLens Kraw = (1 + lowMatL l)·diag q·(1 + upMatL u)` where
`(l,q,u) = matrixSplit Kraw` (so `det (kLens Kraw) = ∏_i q_i` and the LDU-pivot exponents are monomial),
leaving every non-K coordinate (X/N/E/lift, and the radial pivot) UNTOUCHED.

* `kLens` — the matrix LDU lens `K ↦ matrixSplit.symm (lduCoreMap (matrixSplit K))`, i.e.
  `(1 + lowMatL l)·diag q·(1 + upMatL u)` reading `(l,q,u)` off `K`'s strict-lower/diag/strict-upper.
* `kLDU` — the flat reparam: rebuild the vector through `chartIdxEquiv`, mapping each K-slot coordinate
  `⟨k, inl (K-branch (i,j))⟩` to `(kLens (readK x k)) i j`, identity on all other slots.
* `readK_kLDU` / `readX_kLDU` / `readN_kLDU` / `readE_kLDU` / `readW_kLDU` — the reader values at `kLDU x`:
  K reads the LDU matrix, the others pass through (via `Equiv.apply_symm_apply` cancellation — the
  `readK_wInt` pattern; NO `chartIdxEquiv` literal indices).

The rate of `phiFlatLDU M t ha hN kLDU` is already banked decoder-agnostically (`routeMCore_phiFlatLDU`,
sub-tide 1) — and the rate reads the radial scalar from the ORIGINAL `x (structPivot)` (the decoder argument
`kLDU x` is the K-lens; the radial axis is read separately, so it survives whatever `kLDU` does to the K
slots). This module supplies the SPECIFIC lens whose K is LDU-coordinatized; the monomial determinant
(sub-tide 2b) and the LDU-decoder interior witness (2e) build on these reader values.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences + matrix algebra).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The matrix LDU lens -/

/-- **The matrix LDU lens** `kLens K := (1 + lowMatL l)·diag q·(1 + upMatL u)`, reading the LDU params
`(l,q,u) = matrixSplit K` (strict-lower / diagonal / strict-upper of `K`). Equivalently
`matrixSplit.symm (lduCoreMap (matrixSplit K))`. Turns the free K-block into an LDU matrix whose
determinant is the monomial `∏_i (matrixSplit K).2.1 i` (the diagonal pivots). -/
noncomputable def kLens {t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) : Matrix (Fin t) (Fin t) ℝ :=
  matrixSplit.symm (lduCoreMap (matrixSplit K))

/-- `kLens K = (1 + lowMatL l)·diag q·(1 + upMatL u)` unfolded (the LDU matrix from `K`'s params). -/
theorem kLens_eq {t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    kLens K
      = (1 + lowMatL (matrixSplit K).1) * Matrix.diagonal (matrixSplit K).2.1
          * (1 + upMatL (matrixSplit K).2.2) := by
  rw [kLens, lduCoreMap, LinearEquiv.symm_apply_apply]

/-- **`det (kLens K) = ∏_i q_i`** (the LDU diagonal pivots `q = (matrixSplit K).2.1` of `K`) — the unit-
triangular factors `1 + lowMatL l`, `1 + upMatL u` are det-1, so the LDU matrix's det is the product of its
diagonal pivots. The MONOMIAL the free-K `det K` is replaced by. -/
theorem kLens_det {t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    (kLens K).det = ∏ i, (matrixSplit K).2.1 i := by
  rw [kLens_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    unitLow_det, unitUp_det, one_mul, mul_one]

/-! ## The flat K-slot reparametrization `kLDU` -/

/-- **The K-slot LDU reparametrization** `kLDU x` — rebuild the flat vector through `chartIdxEquiv`,
mapping each frame-slot K-branch coordinate at boundary `k`, matrix index `(i,j)`, to `(kLens (readK x k)) i j`;
identity on the X/N/E roles, the lift slot, and (since the pivot is a non-K coordinate) the radial axis. -/
noncomputable def kLDU (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ := fun q =>
  match chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL q with
  | ⟨k, Sum.inl s⟩ =>
    match frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>
      let ij := finProdFinEquiv.symm qK
      kLens (readK M t ha x k) ij.1 ij.2
    | _ => x q
  | ⟨_, Sum.inr _⟩ => x q

/-! ## The reader values at `kLDU x` (the `readK_wInt`-pattern cancellation) -/

/-- **`readK (kLDU x) = kLens (readK x)`** — the K-block reads the LDU matrix. The `chartIdxEquiv` round-trip
cancels (`apply_symm_apply`), then `wOnIdx`-style forward-decode of the K-branch + `finProdFinEquiv` round-trip
(the `readK_wInt` pattern; NO literal `chartIdxEquiv` indices). -/
theorem readK_kLDU (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (i j : Fin (Text M t (k.val + 2))) :
    readK M t ha (kLDU M t ha x) k i j = kLens (readK M t ha x k) i j := by
  rw [readK, kLDU]
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- **`readX (kLDU x) = readX x`** — the X-role passes through. -/
theorem readX_kLDU (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (i : Fin (Text M t (k.val + 1) - Text M t (k.val + 2)))
    (j : Fin (Text M t (k.val + 2))) :
    readX M t ha (kLDU M t ha x) k i j = readX M t ha x k i j := by
  rw [readX, kLDU, readX]
  simp only [Equiv.apply_symm_apply]

/-- **`readN (kLDU x) = readN x`** — the N-role passes through. -/
theorem readN_kLDU (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (i : Fin (Text M t (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) :
    readN M t ha (kLDU M t ha x) k i j = readN M t ha x k i j := by
  rw [readN, kLDU, readN]
  simp only [Equiv.apply_symm_apply]

/-- **`readE (kLDU x) = readE x`** — the E-role passes through. -/
theorem readE_kLDU (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (i : Fin (Text M t (k.val + 1) - Text M t (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) :
    readE M t ha (kLDU M t ha x) k i j = readE M t ha x k i j := by
  rw [readE, kLDU, readE]
  simp only [Equiv.apply_symm_apply]

/-- **`readW (kLDU x) = readW x`** — the lift-role passes through (the `Sum.inr` branch is identity). -/
theorem readW_kLDU (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) (j : Fin (Wext M (k.val + 2))) :
    readW M t ha (kLDU M t ha x) k hk i j = readW M t ha x k hk i j := by
  rw [readW, kLDU, readW]
  simp only [Equiv.apply_symm_apply]

/-! ## Non-vacuity: the LDU-lensed K-core determinant is the diagonal-pivot monomial -/

/-- **The LDU-lensed K-core has MONOMIAL determinant** `det (readK (kLDU x) k) = ∏_i q_{k,i}` (the diagonal
pivots `q_k = (matrixSplit (readK x k)).2.1`). This is the whole point of `kLDU`: the free-K `det K`
(a degree-`t` polynomial) is replaced by a monomial in the per-boundary LDU pivots — what sub-tide 2b's
within-layer determinant consumes. Non-vacuity that the lens performs the LDU coordinatization. -/
theorem readK_kLDU_det (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) :
    (Matrix.of (readK M t ha (kLDU M t ha x) k)).det
      = ∏ i, (matrixSplit (Matrix.of (readK M t ha x k))).2.1 i := by
  rw [show Matrix.of (readK M t ha (kLDU M t ha x) k) = kLens (Matrix.of (readK M t ha x k)) from by
    ext i j; exact readK_kLDU M t ha x k i j, kLens_det]

end DLNFibre.DLN.RLCT
