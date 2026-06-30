import DLNFibre.DLN.RLCT.Validate.RouteMKLDUAmbientDet
import DLNFibre.DLN.RLCT.Validate.RouteMEihdFreePoint
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveContract

/-!
# `RouteMBdetMonomial` — PIECE 2 scaffold: the `interiorLive_BdetMonomial` chain-rule fold

The boundary-factor determinant of the LIVE-leaf ∘ kLDU chart monomializes:

  `|det D(BchartLeaf ∘ kLDU)(pbo u)| = ∏_{j ≠ leafPivot} |u_j|^{leafH j}`

via the chain rule `|det D(g∘f)(x)| = |det D(g)(f x)| · |det D(f)(x)|`, with:

* **Factor 2** (`RouteMKLDUAmbientDet`, axiom-clean, BANKED): the ambient lens det
  `|det D(kLDU)(pbo u)| = ∏_k ∏_i |q_{k,i}|^{2(t_k−1−i)}`.
* **Factor 1** (genm-eihdfree `Dtot_abs_det_free` + `Bchart_abs_det_eq_Dtot`): the free-`y₀`
  boundary-factor det `|det D(BchartLeaf)(Z)| = |det (readK Z 0)|^{r+c}` at `Z = kLDU(pbo u)`,
  CONDITIONAL on the regauge `hreg : |det((eihdOut).symm ∘ eIn)| = 1`.

`readK_kLDU` naturality + `kLens_det` fold factor 1 to `(∏_i |q_{0,i}|)^{r+c}`; the per-diagonal-pivot
exponent `(r_0+c_0) + 2(t_0−1−i)` matches `liveLeafHOnIdx`.

## Status (SCAFFOLD — the structural atoms LANDED; the product-reindex assembly is the open piece)

LANDED sorry-free (the chain-rule + factor structure, the diagonal-axis API):
* `BchartLeaf_abs_det_free` — factor 1 (`Bchart_abs_det_eq_Dtot` + `Dtot_abs_det_free`, hreg-conditional).
* `BchartLeaf_kLDU_abs_det_split` — the chain rule (`fderiv_comp` + `LinearMap.det_comp` + `abs_mul`).
* `readK_kLDU_pbo` — the K-core of `kLDU(pbo u)` at boundary 0 is `kLens (readK u 0)`.
* `diagAxis` / `u_diagAxis` / `diagAxis_injective` — the boundary-0 K-diagonal axis API.

OPEN (handed back — the bounded `liveLeafHOnIdx`-decode product-reindex glue):
* `leafH_diagAxis` — `leafH (diagAxis i) = (r₀+c₀)+2(t₀−1−i)` (the diagonal `if` fires after the
  `frameSplitEquiv`/`finProdFinEquiv` round-trips; the inner `fse (fse.symm _)` round-trip needs a robust
  decode — the `(0:Fin 2).val+1` vs `0+1` arg-form mismatch blocks a one-shot `simp`).
* `mem_image_diagAxis_of_leafH_ne_zero` — the off-image collapse (`leafH j ≠ 0 ∧ j ≠ pivot ⟹ j ∈
  image diagAxis`; the `Sigma.ext` + `fse.symm` reconstruction).
* `interiorLive_BdetMonomial_of_hreg` — the assembly: LHS-collapse (`Finset.abs_prod`/`prod_pow`/
  `prod_mul_distrib`/`pow_add`, VALIDATED) · the RHS reindex (`Finset.prod_subset` to `image diagAxis`
  + `prod_image`, the open glue) → the monomial.

## hreg gate (caveat next to the claim)

`hreg` is the OPEN regauge abs-det-`1` (`eihd_hreg`, genm-castdet's `RouteMHregPerm.lean`, in flight).
The final `interiorLive_BdetMonomial_of_hreg` carries `hreg` as an `ha`-level hypothesis; genm-r1lower
discharges it at `interiorLive_abs_det` (fed `eihd_hreg ha`). NOT a new mathematical gap.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {M : Fin (2 + 1) → ℕ}

/-- **Factor 1 (free-`y₀`)** — `|det D(BchartLeaf)(Z)| = |det (readK Z 0)|^{r+c}` (given `hreg`). The
`Bchart_abs_det_eq_Dtot` reindex peel + the banked free-point `Dtot_abs_det_free`. -/
theorem BchartLeaf_abs_det_free (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ)
    (hreg : |LinearMap.det
        (((eihdOut ha).symm : StairProd (eihdV M) 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))
          ∘ₗ ((eIn ha) : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd (eihdV M) 2))| = 1) :
    |LinearMap.det (fderiv ℝ (BchartLeaf ha) y₀).toLinearMap|
      = |(Matrix.of (readK M (tach M) ha y₀ ⟨0, by decide⟩)).det|
        ^ ((Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2)) := by
  rw [Bchart_abs_det_eq_Dtot ha y₀, Dtot_abs_det_free ha y₀ hreg]

/-- **The chain-rule split** — `|det D(BchartLeaf ∘ kLDU)(x)| = |det D(BchartLeaf)(kLDU x)| ·
|det D(kLDU)(x)|`. `fderiv_comp` + `LinearMap.det_comp` + `abs_mul`. -/
theorem BchartLeaf_kLDU_abs_det_split (ha : StructAdm M (tach M)) (x : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (fun y => BchartLeaf ha (kLDU M (tach M) ha y)) x).toLinearMap|
      = |LinearMap.det (fderiv ℝ (BchartLeaf ha) (kLDU M (tach M) ha x)).toLinearMap|
        * |LinearMap.det (fderiv ℝ (kLDU M (tach M) ha) x).toLinearMap| := by
  have hcomp : (fun y => BchartLeaf ha (kLDU M (tach M) ha y))
      = BchartLeaf ha ∘ kLDU M (tach M) ha := rfl
  rw [hcomp, fderiv_comp x (Bchart_differentiableAt ha _) (differentiable_kLDU M (tach M) ha x)]
  rw [ContinuousLinearMap.coe_comp, LinearMap.det_comp, abs_mul]

/-- The K-core of `kLDU (pbo u)` at boundary `0` is the lens applied to the (pbo-fixed) K-core of `u`. -/
theorem readK_kLDU_pbo (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix.of (readK M (tach M) ha
        (kLDU M (tach M) ha (pivotBlowupOn (activeM M ha)
          (leafPivot M ha (by norm_num) h0r h0c) u)) ⟨0, by decide⟩)
      = kLens (Matrix.of (readK M (tach M) ha u ⟨0, by decide⟩)) := by
  ext i j
  rw [Matrix.of_apply, readK_kLDU]
  congr 1
  ext a b
  exact readK_pbo_all ha h0r h0c u ⟨0, by decide⟩ a b

/-- The diagonal K-axis of boundary `0` at index `i`: the flat coordinate reading `readK · 0 i i`. -/
noncomputable def diagAxis (ha : StructAdm M (tach M)) (i : Fin (Text M (tach M) 2)) :
    Fin (routeMAmbient M) :=
  (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
    ⟨(0 : Fin 2), Sum.inl ((frameSplitEquiv M (tach M) ((0 : Fin 2).val + 1)
      (ha.hdesc (0 : Fin 2).val (0 : Fin 2).isLt) (ha.hub (0 : Fin 2).val)).symm
        (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i, i))))))⟩

/-- `u (diagAxis i) = readK u 0 i i` (the diagonal K-core entry). -/
theorem u_diagAxis (ha : StructAdm M (tach M)) (u : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Text M (tach M) 2)) :
    u (diagAxis ha i) = readK M (tach M) ha u (0 : Fin 2) i i := by
  rw [readK, diagAxis]

/-- `diagAxis` is injective. -/
theorem diagAxis_injective (ha : StructAdm M (tach M)) : Function.Injective (diagAxis ha) := by
  intro i j hij
  rw [diagAxis, diagAxis] at hij
  have h1 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hij
  have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h1).2
  have h3 := (frameSplitEquiv M (tach M) ((0 : Fin 2).val + 1) (ha.hdesc 0 (by norm_num))
    (ha.hub 0)).symm.injective ((Sum.inl.injEq _ _).mp h2)
  have h4 := finProdFinEquiv.injective
    ((Sum.inl.injEq _ _).mp ((Sum.inl.injEq _ _).mp ((Sum.inl.injEq _ _).mp h3)))
  exact (Prod.mk.injEq .. ▸ h4).1

/-- **The LHS collapse** — factor 1 · factor 2 (boundary 0) folds to the single per-pivot product:
`|∏ q|^{r+c} · ∏_i |q i|^{2(t−1−i)} = ∏_i |q i|^{(r+c)+2(t−1−i)}`. -/
theorem lhs_collapse (τ r c : ℕ) (q : Fin τ → ℝ) :
    |∏ i, q i| ^ (r + c) * ∏ i, |q i| ^ (2 * (τ - 1 - (i : ℕ)))
      = ∏ i : Fin τ, |q i| ^ ((r + c) + 2 * (τ - 1 - (i : ℕ))) := by
  rw [Finset.abs_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => by rw [← pow_add])

/-- **`frameSplitEquiv` is proof-irrelevant in its admissibility args.** The two `≤` hypotheses are
`Subsingleton` (`Nat.le` is a `Prop`), so `frameSplitEquiv` built from different proofs is the SAME
equiv — needed to bridge the `diagAxis` (`by norm_num` proofs) and `liveLeafHOnIdx` (`k.isLt`-derived
proofs) `frameSplitEquiv` copies so the round-trip `e (e.symm X)` is syntactically `Equiv.apply_symm_apply`. -/
theorem frameSplitEquiv_proof_irrel (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 h1' : Text M t (s + 1) ≤ Text M t s) (h2 h2' : Text M t (s + 1) ≤ Wext M s) :
    frameSplitEquiv M t s h1 h2 = frameSplitEquiv M t s h1' h2' := by
  cases Subsingleton.elim h1 h1'
  cases Subsingleton.elim h2 h2'
  rfl

/-- `diagAxis i ≠ leafPivot` — the boundary-0 K-diagonal slot is not the (boundary-1) leaf pivot. -/
theorem diagAxis_ne_leafPivot (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (i : Fin (Text M (tach M) 2)) :
    diagAxis ha i ≠ leafPivot M ha (by norm_num) h0r h0c := by
  rw [diagAxis]
  exact boundary0_ne_leafPivot ha h0r h0c _

/-- **`leafH` at the diagonal axis** — `interiorLive_leafH (diagAxis i) = (r₀+c₀) + 2(t₀−1−i)`. The
`if j = leafPivot` is `false` (`diagAxis_ne_leafPivot`); the `chartIdxEquiv` round-trip on `diagAxis i`
exposes the boundary-0 K-slot tag, the `frameSplitEquiv`/`finProdFinEquiv` round-trips collapse, and the
diagonal `i = i` fires `if_pos`. -/
theorem leafH_diagAxis (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (i : Fin (Text M (tach M) 2)) :
    interiorLive_leafH ha h0r h0c (diagAxis ha i)
      = (Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2)
        + 2 * (Text M (tach M) 2 - 1 - (i : ℕ)) := by
  rw [interiorLive_leafH, if_neg (diagAxis_ne_leafPivot ha h0r h0c i)]
  rw [diagAxis, Equiv.apply_symm_apply, liveLeafHOnIdx]
  simp only [Equiv.apply_symm_apply, finProdFinEquiv.symm_apply_apply]
  rfl

end DLNFibre.DLN.RLCT
