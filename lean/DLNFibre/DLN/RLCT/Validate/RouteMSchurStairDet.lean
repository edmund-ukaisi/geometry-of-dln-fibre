import DLNFibre.DLN.RLCT.Validate.RouteMSchurFrameDet
import DLNFibre.DLN.RLCT.Validate.RouteMStairTwoSided

/-!
# `RouteMSchurStairDet` — the general-`n` per-boundary Schur-frame staircase determinant

The network-free, ∀`n` determinant spine for the general-`L` `Dtot_abs_det_free` (`RouteMEihdFreePoint`,
which is `StairProd (eihdV M) 2`-pinned via `Fin.prod_univ_two`). The L=2 boundary-factor det is one
Schur frame (boundary `0`) + a det-`1` chain unit (boundary `1`), assembled by
`stairMap_abs_det_twoConj` at `n = 2`. The general-`L` boundary factor is a per-boundary Schur
STAIRCASE: each interior boundary `s` carries a Schur frame `schurFrameDeriv (X s) (K s) (N s)` with
abs-det `|det (K s)|^{r_s + c_s}`, and the staircase couplings (the head-into-tail chain feed) are
det-irrelevant.

This module builds that spine ABSTRACTLY over the increment product
`StairProd (fun s => SchurInc (t s) (r s) (c s)) n`, parametric in the per-boundary block data
`(X s, K s, N s)`, so the ∀`L` `Dtot` lift consumes it without re-deriving a new headline:

  `|det (schurStairMap …)| = ∏_{s : Fin n} |det (K s)|^{r_s + c_s}`.

* `schurStairV` — the per-boundary increment space family `s ↦ SchurInc (t s) (r s) (c s)`.
* `schurStairDiag` — the diagonal blocks `s ↦ schurFrameDeriv (X s) (K s) (N s)`.
* `schurStairMap` — the length-`n` staircase with those diagonal Schur frames + a coupling datum.
* `schurStairMap_det` / `schurStairMap_abs_det` — the headline: `det = ∏_s (det (K s))^{r_s + c_s}` /
  `|det| = ∏_s |det (K s)|^{r_s + c_s}`.
* `schurStairMap_abs_det_conj` — the single-`e` conjugate form (`e ∘ D ∘ e.symm = schurStairMap`).
* `schurStairMap_abs_det_twoConj` — the two-sided conjugate form (the shape the `eIn`/`eOut` regauge
  `Dtot` lift consumes), gated on the regauge abs-det-`1`.

At `n = 2` this recovers exactly the `Dtot_abs_det_free` block structure (Schur frame at boundary `0`,
`schurFrameDeriv X K N` with `|det K|^{r+c}`; a second Schur frame or det-`1` unit at boundary `1`);
see `schurStairMap_abs_det_two`. Non-vacuity: `schurStairMap_det_n3_example` fires the length-`3`
staircase on genuine `2×2 / 1×1 / 1×1` boundary blocks. The interior-deepest L=3 anchor
`(2, 4, 3, 2)` is instantiated in `schurStairMap_abs_det_2432` (K-blocks `2×2 / 1×1 / 0×0`, exponents
`(2, 3, 3)`) with the `0×0` leaf collapse `schurStairMap_abs_det_2432_leaf_trivial`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (determinant of a conjugation + the generic
`schurFrame_abs_det`; no analysis). De-risks task (a) of `genm-glinterior` — the staircase-length lift
of the boundary-factor det, at the linear-map level, WITHOUT re-plumbing the concrete `eihd`.
-/

open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

/-! ## The per-boundary Schur-increment staircase -/

/-- **The per-boundary increment space family** `s ↦ SchurInc (t s) (r s) (c s)` — the domain of the
boundary-`s` Schur frame. `StairProd schurStairV n` is the length-`n` nested increment product. -/
abbrev schurStairV (t r c : ℕ → ℕ) : ℕ → Type := fun s => SchurInc (t s) (r s) (c s)

/-- **The diagonal Schur-frame blocks** `s ↦ schurFrameDeriv (X s) (K s) (N s)` — the per-boundary
Schur-frame differential, abs-det `|det (K s)|^{r_s + c_s}` (`schurFrame_abs_det`). -/
def schurStairDiag (t r c : ℕ → ℕ)
    (X : ∀ s, Matrix (Fin (r s)) (Fin (t s)) ℝ) (K : ∀ s, Matrix (Fin (t s)) (Fin (t s)) ℝ)
    (N : ∀ s, Matrix (Fin (t s)) (Fin (c s)) ℝ) :
    (s : ℕ) → schurStairV t r c s →ₗ[ℝ] schurStairV t r c s :=
  fun s => schurFrameDeriv (X s) (K s) (N s)

/-- **The length-`n` per-boundary Schur staircase** — the staircase endomorphism of
`StairProd (schurStairV t r c) n` whose diagonal blocks are the per-boundary Schur frames
`schurStairDiag` and whose head-into-tail couplings are the supplied datum `co` (the inter-layer
chain feed; det-irrelevant). -/
def schurStairMap (t r c : ℕ → ℕ)
    (X : ∀ s, Matrix (Fin (r s)) (Fin (t s)) ℝ) (K : ∀ s, Matrix (Fin (t s)) (Fin (t s)) ℝ)
    (N : ∀ s, Matrix (Fin (t s)) (Fin (c s)) ℝ) (n : ℕ)
    (co : StairCoupling (schurStairV t r c) n) :
    StairProd (schurStairV t r c) n →ₗ[ℝ] StairProd (schurStairV t r c) n :=
  stairMap (schurStairV t r c) n (schurStairDiag t r c X K N) co

/-! ## The staircase determinant `= ∏_s |det (K s)|^{r_s + c_s}` -/

/-- **The per-boundary Schur-staircase determinant** — `det (schurStairMap …) = ∏_s (det (K s))^{r_s + c_s}`.
The general-`n` staircase det `stairMap_det` (couplings drop out), with each diagonal block's det the
generic `schurFrameDeriv_det = (det (K s))^{r_s + c_s}`. -/
theorem schurStairMap_det (t r c : ℕ → ℕ)
    (X : ∀ s, Matrix (Fin (r s)) (Fin (t s)) ℝ) (K : ∀ s, Matrix (Fin (t s)) (Fin (t s)) ℝ)
    (N : ∀ s, Matrix (Fin (t s)) (Fin (c s)) ℝ) (n : ℕ)
    (co : StairCoupling (schurStairV t r c) n) :
    LinearMap.det (schurStairMap t r c X K N n co)
      = ∏ s : Fin n, (K s.val).det ^ (r s.val + c s.val) := by
  rw [schurStairMap, stairMap_det]
  exact Finset.prod_congr rfl (fun s _ => by
    rw [schurStairDiag, schurFrameDeriv_det])

/-- **The per-boundary Schur-staircase abs-det** — `|det (schurStairMap …)| = ∏_s |det (K s)|^{r_s + c_s}`,
the `|·|` form the boundary-factor det headline consumes. -/
theorem schurStairMap_abs_det (t r c : ℕ → ℕ)
    (X : ∀ s, Matrix (Fin (r s)) (Fin (t s)) ℝ) (K : ∀ s, Matrix (Fin (t s)) (Fin (t s)) ℝ)
    (N : ∀ s, Matrix (Fin (t s)) (Fin (c s)) ℝ) (n : ℕ)
    (co : StairCoupling (schurStairV t r c) n) :
    |LinearMap.det (schurStairMap t r c X K N n co)|
      = ∏ s : Fin n, |(K s.val).det| ^ (r s.val + c s.val) := by
  rw [schurStairMap_det, Finset.abs_prod]
  exact Finset.prod_congr rfl (fun s _ => abs_pow _ _)

/-! ## The conjugate forms (the shape the flat-`Dtot` lift consumes) -/

/-- **The Schur-staircase abs-det on a single-conjugate endomorphism.** If a flat endomorphism `D` of
a f.d. space `E` is conjugate to the per-boundary Schur staircase through a layer-collecting equiv `e`
(`e ∘ D ∘ e.symm = schurStairMap`), then `|det D| = ∏_s |det (K s)|^{r_s + c_s}`. -/
theorem schurStairMap_abs_det_conj {E : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (t r c : ℕ → ℕ)
    (X : ∀ s, Matrix (Fin (r s)) (Fin (t s)) ℝ) (K : ∀ s, Matrix (Fin (t s)) (Fin (t s)) ℝ)
    (N : ∀ s, Matrix (Fin (t s)) (Fin (c s)) ℝ) (n : ℕ)
    (co : StairCoupling (schurStairV t r c) n)
    (e : E ≃ₗ[ℝ] StairProd (schurStairV t r c) n) (D : E →ₗ[ℝ] E)
    (hD : (e : E →ₗ[ℝ] StairProd (schurStairV t r c) n) ∘ₗ D
        ∘ₗ (e.symm : StairProd (schurStairV t r c) n →ₗ[ℝ] E)
        = schurStairMap t r c X K N n co) :
    |LinearMap.det D| = ∏ s : Fin n, |(K s.val).det| ^ (r s.val + c s.val) := by
  have hdet : LinearMap.det D = LinearMap.det (schurStairMap t r c X K N n co) := by
    have hDeq : D = (e.symm : StairProd (schurStairV t r c) n →ₗ[ℝ] E)
        ∘ₗ schurStairMap t r c X K N n co ∘ₗ (e : E →ₗ[ℝ] StairProd (schurStairV t r c) n) := by
      rw [← hD]; ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have hconj := LinearMap.det_conj (schurStairMap t r c X K N n co) e.symm
    rw [LinearEquiv.symm_symm] at hconj
    rw [hDeq, hconj]
  rw [hdet]
  exact schurStairMap_abs_det t r c X K N n co

/-- **The Schur-staircase abs-det on a two-sided conjugate endomorphism** (the `eIn`/`eOut` regauge
shape the general-`L` `Dtot` lift consumes). Given the staircase `eOut ∘ D ∘ eIn.symm = schurStairMap`
and the regauge factor `eOut.symm ∘ eIn` abs-det-`1`, `|det D| = ∏_s |det (K s)|^{r_s + c_s}`. -/
theorem schurStairMap_abs_det_twoConj {E : Type} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (t r c : ℕ → ℕ)
    (X : ∀ s, Matrix (Fin (r s)) (Fin (t s)) ℝ) (K : ∀ s, Matrix (Fin (t s)) (Fin (t s)) ℝ)
    (N : ∀ s, Matrix (Fin (t s)) (Fin (c s)) ℝ) (n : ℕ)
    (co : StairCoupling (schurStairV t r c) n)
    (eIn eOut : E ≃ₗ[ℝ] StairProd (schurStairV t r c) n) (D : E →ₗ[ℝ] E)
    (hD : (eOut : E →ₗ[ℝ] StairProd (schurStairV t r c) n) ∘ₗ D
        ∘ₗ (eIn.symm : StairProd (schurStairV t r c) n →ₗ[ℝ] E)
        = schurStairMap t r c X K N n co)
    (hreg : |LinearMap.det ((eOut.symm : StairProd (schurStairV t r c) n →ₗ[ℝ] E)
        ∘ₗ (eIn : E →ₗ[ℝ] StairProd (schurStairV t r c) n))| = 1) :
    |LinearMap.det D| = ∏ s : Fin n, |(K s.val).det| ^ (r s.val + c s.val) := by
  have hstair : (eOut : E →ₗ[ℝ] StairProd (schurStairV t r c) n) ∘ₗ D
      ∘ₗ (eIn.symm : StairProd (schurStairV t r c) n →ₗ[ℝ] E)
      = stairMap (schurStairV t r c) n (schurStairDiag t r c X K N) co := hD
  have hbase := stairMap_abs_det_twoConj (schurStairV t r c) n (schurStairDiag t r c X K N) co
    eIn eOut D hstair hreg
  rw [hbase]
  exact Finset.prod_congr rfl (fun s _ => by
    rw [schurStairDiag, schurFrame_abs_det])

/-! ## `n = 2` recovery + non-vacuity -/

/-- **`n = 2` recovery** — the length-`2` Schur staircase abs-det is `|det (K 0)|^{r_0+c_0} ·
|det (K 1)|^{r_1+c_1}`, the two-boundary product `Dtot_abs_det_free` assembles at `L = 2` (boundary `0`
the live Schur frame; boundary `1` the leaf/chain frame — det `1` when `K 1` is `0×0` or unit). -/
theorem schurStairMap_abs_det_two (t r c : ℕ → ℕ)
    (X : ∀ s, Matrix (Fin (r s)) (Fin (t s)) ℝ) (K : ∀ s, Matrix (Fin (t s)) (Fin (t s)) ℝ)
    (N : ∀ s, Matrix (Fin (t s)) (Fin (c s)) ℝ)
    (co : StairCoupling (schurStairV t r c) 2) :
    |LinearMap.det (schurStairMap t r c X K N 2 co)|
      = |(K 0).det| ^ (r 0 + c 0) * |(K 1).det| ^ (r 1 + c 1) := by
  rw [schurStairMap_abs_det, Fin.prod_univ_two]
  rfl

/-- The `(3,3,3,3)`-shaped example block widths as genuine `ℕ → ℕ` functions: `t = (2,1,1)`,
`r = (1,1,1)`, `c = (1,2,2)` on `s = 0,1,2` (and irrelevant beyond). -/
def schurStairExT3 : ℕ → ℕ := fun s => if s = 0 then 2 else 1
def schurStairExR3 : ℕ → ℕ := fun _ => 1
def schurStairExC3 : ℕ → ℕ := fun s => if s = 0 then 1 else 2

/-- **Non-vacuity (`n = 3`, genuine boundary blocks).** The length-`3` Schur staircase on the
`(3,3,3,3)`-shaped boundaries (`s = 0,1,2` carry `SchurInc` blocks of sizes `2×2 / 1×1 / 1×1`) has
abs-det `∏_s |det (K s)|^{r_s+c_s}` — the couplings drop out and the staircase fires on genuine
(non-trivial) frames, not a hollow generalization. -/
theorem schurStairMap_det_n3_example
    (X : ∀ s, Matrix (Fin (schurStairExR3 s)) (Fin (schurStairExT3 s)) ℝ)
    (K : ∀ s, Matrix (Fin (schurStairExT3 s)) (Fin (schurStairExT3 s)) ℝ)
    (N : ∀ s, Matrix (Fin (schurStairExT3 s)) (Fin (schurStairExC3 s)) ℝ)
    (co : StairCoupling (schurStairV schurStairExT3 schurStairExR3 schurStairExC3) 3) :
    |LinearMap.det (schurStairMap schurStairExT3 schurStairExR3 schurStairExC3 X K N 3 co)|
      = |(K 0).det| ^ 2 * (|(K 1).det| ^ 3 * |(K 2).det| ^ 3) := by
  rw [schurStairMap_abs_det, Fin.prod_univ_three]
  show |(K 0).det| ^ (schurStairExR3 0 + schurStairExC3 0) * |(K 1).det| ^ (schurStairExR3 1 + schurStairExC3 1)
      * |(K 2).det| ^ (schurStairExR3 2 + schurStairExC3 2)
    = |(K 0).det| ^ 2 * (|(K 1).det| ^ 3 * |(K 2).det| ^ 3)
  norm_num [schurStairExR3, schurStairExC3]
  ring

/-! ## The interior-deepest `(2, 4, 3, 2)` staircase instance (the L=3 de-risk anchor)

The pen-and-paper `genm-l3interior` anchor tuple `(2, 4, 3, 2)` (achiever `tStar = (2, 1, 0)`,
`minAdm = 4`) is the interior-deepest L=3 node: the rank drop is split across the interior boundary
`s = 1` (`rBlock·cBlock = 2`) and the leaf `s = 2` (`rBlock·cBlock = 2`), NOT concentrated at one
factor (unlike the leaf-only `(4, 4, 2, 2)`). Its per-boundary Schur K-blocks (along the achiever
path `Text = (·, 2, 2, 1, 0)`) have dimensions `(t 0, t 1, t 2) = (2, 1, 0)` and frame exponents
`(r_s + c_s) = (2, 3, 3)`. This module's abstract spine computes the multi-boundary staircase det on
exactly these shapes — the concrete confirmation that the staircase INDEXING (a genuine `2×2` interior
K-block at `s = 0`, a `1×1` at `s = 1`, a `0×0` leaf at `s = 2`) folds to a single monomial with NO
double-count. -/

/-- The `(2, 4, 3, 2)` achiever-path block widths: `t = (2, 1, 0)`, `r = (0, 1, 1)`, `c = (2, 2, 2)`
(frame exponents `r + c = (2, 3, 3)`), on `s = 0, 1, 2`. -/
def T2432 : ℕ → ℕ := fun s => if s = 0 then 2 else if s = 1 then 1 else 0
def R2432 : ℕ → ℕ := fun s => if s = 0 then 0 else 1
def C2432 : ℕ → ℕ := fun _ => 2

/-- **The `(2, 4, 3, 2)` interior-deepest staircase determinant.** The length-`3` per-boundary Schur
staircase on the achiever-path K-blocks (`2×2 / 1×1 / 0×0`) has abs-det
`|det (K 0)|^2 · |det (K 1)|^3 · |det (K 2)|^3`. The leaf `K 2` is `0×0` (`det = 1`), so its factor is
`1`. The genuine `2×2` interior K-block at `s = 0` and the `1×1` at `s = 1` fold to a single monomial —
the concrete de-risk that the multi-boundary staircase indexing at an interior-deepest L=3 tuple
computes with NO double-count (the disjoint E/K summands guarantee it). -/
theorem schurStairMap_abs_det_2432
    (X : ∀ s, Matrix (Fin (R2432 s)) (Fin (T2432 s)) ℝ)
    (K : ∀ s, Matrix (Fin (T2432 s)) (Fin (T2432 s)) ℝ)
    (N : ∀ s, Matrix (Fin (T2432 s)) (Fin (C2432 s)) ℝ)
    (co : StairCoupling (schurStairV T2432 R2432 C2432) 3) :
    |LinearMap.det (schurStairMap T2432 R2432 C2432 X K N 3 co)|
      = |(K 0).det| ^ 2 * (|(K 1).det| ^ 3 * |(K 2).det| ^ 3) := by
  rw [schurStairMap_abs_det, Fin.prod_univ_three]
  show |(K 0).det| ^ (R2432 0 + C2432 0) * |(K 1).det| ^ (R2432 1 + C2432 1)
      * |(K 2).det| ^ (R2432 2 + C2432 2)
    = |(K 0).det| ^ 2 * (|(K 1).det| ^ 3 * |(K 2).det| ^ 3)
  norm_num [R2432, C2432]
  ring

/-- **The `(2, 4, 3, 2)` leaf K-block is `0×0`, so its Schur factor is `1`.** `T2432 2 = 0`, so
`K 2 : Matrix (Fin 0) (Fin 0) ℝ` has `det = 1` (`Matrix.det_isEmpty`), hence `|det (K 2)|^3 = 1`. The
staircase det collapses to the two live interior/leaf blocks `|det (K 0)|^2 · |det (K 1)|^3`. -/
theorem schurStairMap_abs_det_2432_leaf_trivial
    (X : ∀ s, Matrix (Fin (R2432 s)) (Fin (T2432 s)) ℝ)
    (K : ∀ s, Matrix (Fin (T2432 s)) (Fin (T2432 s)) ℝ)
    (N : ∀ s, Matrix (Fin (T2432 s)) (Fin (C2432 s)) ℝ)
    (co : StairCoupling (schurStairV T2432 R2432 C2432) 3) :
    |LinearMap.det (schurStairMap T2432 R2432 C2432 X K N 3 co)|
      = |(K 0).det| ^ 2 * |(K 1).det| ^ 3 := by
  rw [schurStairMap_abs_det_2432]
  have hK2 : (K 2).det = 1 := by
    have : IsEmpty (Fin (T2432 2)) := by rw [show T2432 2 = 0 from rfl]; exact Fin.isEmpty
    exact Matrix.det_isEmpty
  rw [hK2]
  norm_num

end DLNFibre.DLN.RLCT

end
