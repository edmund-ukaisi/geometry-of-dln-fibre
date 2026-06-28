import DLNFibre.DLN.RLCT.Validate.RouteMFrontBottleneck
import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanRate
import DLNFibre.DLN.RLCT.Validate.Case222Lemma2
import DLNFibre.DLN.RLCT.Validate.RouteM121Smeared

/-!
# `RouteMSmearedGenChart` — the ∀M-(1,1)-smeared Option-A chart (rate leg)

The generic flat→flat SMEARED chart for the `(1,1)` family (`minAdm = 1`, `r = 1`, deepest column-count
`c = 1`, `m1 = M_{L-1} ≥ 2`). Architecture (Codex `genm11-chart`, hybrid C): the chart is a SINGLE
`Function.update` shear at the canonical deepest-`(0,0)` flat coordinate, NOT routed through
`cleanPhi`/`scaleLayer` (the smeared deepest layer is not a whole-layer scalar multiple). The rate is
proved DIRECTLY through the landed front fact `prodAux_frontScalarShear_cancel`.

The deepest layer `A^{L-1}` has size `m1 × 1` (a single column). The chart's smear shifts the pivot
ROW (row 0) of that column by `−smearShift = −∑ᵣ Λ₀ 0 r · S r`, leaving the residual rows free. The
product telescopes: `P · A^{L-1} = u_p · P₁ + (P₂ − P₁·Λ₀)·S = u_p · P₁` (front fact, off the pole),
so `routeMCore (phiSm u) = u_p² · ‖P₁‖² = u_p² · U`.

This file is the RATE leg; the MP leg + subBox/divergence assembly are the remaining build.
-/

open Matrix MeasureTheory
open scoped BigOperators ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The front product is unaffected by a change in later layers

`prodAux M A (L-1)` (the front product, layers `0..L-2`) reads only the first `L-1` layers, so changing
the DEEPEST layer `L-1` does not change it. This is the brick that licenses "smear only the deepest
layer" — the front coords the routing `Λ₀` reads stay fixed under the chart. -/

/-- **`prodAux` reads only the layers below its index.** If `A` and `B` agree on every layer `s < k`
(as `Fin L` indices), then `prodAux M A k = prodAux M B k`. Induction on `k`. -/
theorem prodAux_congr_of_eqOn_prefix (M : Fin (L + 1) → ℕ) (A B : Params M) :
    ∀ (k : ℕ) (hk : k < L + 1),
      (∀ (s : Fin L), (s : ℕ) < k → A s = B s) →
      prodAux M A k hk = prodAux M B k hk := by
  intro k
  induction k with
  | zero => intro hk _; rfl
  | succ k ih =>
      intro hk hpre
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have e1 : M (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))
          = M ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc) := rfl
      have e2 : M (⟨k + 1, hk⟩ : Fin (L + 1))
          = M ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ) := rfl
      rw [prodAux_succ M A k hk e1 e2, prodAux_succ M B k hk e1 e2]
      rw [ih hk' (fun s hs => hpre s (Nat.lt_succ_of_lt hs))]
      rw [hpre ⟨k, Nat.lt_of_succ_lt_succ hk⟩ (Nat.lt_succ_self k)]

/-! ## The chart data (the `(1,1)` family: `M_{deepLayer.succ} = M_L = 1`, `m1 = M_{deepLayer.castSucc} ≥ 2`)

For the `(1,1)`-smeared family the deepest layer `A^{L-1}` has size `m1 × 1` (`m1 = M_{L-1} ≥ 2`,
`c = M_L = 1`). We abbreviate `dl := deepLayer M hL`; the deepest layer's row-type is `Fin (M dl.castSucc) = Fin m1`,
its column-type `Fin (M dl.succ) = Fin 1`. The front product `P := prodAux M (baseParams u) (L-1)` is
`M_0 × m1`. Hypotheses `hrow : 2 ≤ M dl.castSucc` (so `m1 ≥ 2`, a nonempty residual), `hcol : M dl.succ = 1`. -/

variable (M : Fin (L + 1) → ℕ) (hL : 0 < L)

/-- The base Params tuple decoded from a flat point. -/
noncomputable def baseParams (u : Fin (routeMAmbient M) → ℝ) : Params M :=
  (paramsEquivFlat M).symm u

/-- The front product `P = prodAux M (baseParams u) (L-1)` (layers `0..L-2`), size `M_0 × M_{L-1}`. -/
noncomputable def frontMat (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (M 0)) (Fin (M ⟨L - 1, by omega⟩)) ℝ :=
  prodAux M (baseParams M u) (L - 1) (by omega)

/-- The pivot column `P₁ = frontMat[:, 0]` (a single column), `M_0 × 1`. The deepest-layer row-type is
`Fin (M ⟨L-1,_⟩) = Fin m1`; the pivot is column/row `0`. -/
noncomputable def pivotCol (u : Fin (routeMAmbient M) → ℝ) (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    Matrix (Fin (M 0)) (Fin 1) ℝ :=
  fun i _ => frontMat M hL u i ⟨0, hm1⟩

/-- The residual selector `σ : Fin (m1 − 1) → Fin m1`, `r ↦ r.succ` (rows/cols `1..m1−1`, all except
the pivot `0`). Built as `Fin.succ` (into `Fin ((m1−1)+1)`) recast to `Fin m1` via `m1 = (m1−1)+1`. -/
noncomputable def residSel (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    Fin (M ⟨L - 1, by omega⟩ - 1) → Fin (M ⟨L - 1, by omega⟩) :=
  fun r => Fin.cast (by omega) r.succ

/-- The residual block `P₂` of `frontMat`: columns selected by `residSel` (all columns except the
pivot column `0`), `M_0 × (m1 − 1)`. -/
noncomputable def residCols (u : Fin (routeMAmbient M) → ℝ) (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    Matrix (Fin (M 0)) (Fin (M ⟨L - 1, by omega⟩ - 1)) ℝ :=
  fun i r => frontMat M hL u i (residSel M hL hm1 r)

/-- The scalar-Gram routing `Λ₀ = (P₁ᵀP₁)⁻¹ P₁ᵀ P₂` (a `1 × (m1−1)` matrix). -/
noncomputable def routing (u : Fin (routeMAmbient M) → ℝ) (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    Matrix (Fin 1) (Fin (M ⟨L - 1, by omega⟩ - 1)) ℝ :=
  ((pivotCol M hL u hm1).transpose * pivotCol M hL u hm1)⁻¹
    * (pivotCol M hL u hm1).transpose * residCols M hL u hm1

/-- The deepest-layer column entries (the base, pre-smear): `S i := (baseParams u)^{L-1} i 0`
(the single column of the `m1 × 1` deepest layer). -/
noncomputable def deepCol (u : Fin (routeMAmbient M) → ℝ)
    (hcol : 0 < M (deepLayer M hL).succ) (i : Fin (M (deepLayer M hL).castSucc)) : ℝ :=
  (baseParams M u) (deepLayer M hL) i ⟨0, hcol⟩

/-- The smear shift `∑ᵣ Λ₀ 0 r · S(σ r)`: the routing applied to the residual rows of the deepest
column (`S(σ r)` the residual-row entries `1..m1−1`). The deepest pivot row `0` is shifted by `−` this. -/
noncomputable def smearShift (u : Fin (routeMAmbient M) → ℝ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) (hcol : 0 < M (deepLayer M hL).succ) : ℝ :=
  ∑ r : Fin (M ⟨L - 1, by omega⟩ - 1),
    routing M hL u hm1 0 r * deepCol M hL u hcol (residSel M hL hm1 r)

/-- The smeared deepest layer: `updateRow` of `(baseParams u)^{L-1}` at the pivot row `0`, replacing it
by `(u_p − smearShift)` (the single-entry row, `M_L = 1`). Residual rows `1..m1−1` are untouched. -/
noncomputable def smearedDeepLayer (u : Fin (routeMAmbient M) → ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    Matrix (Fin (M (deepLayer M hL).castSucc)) (Fin (M (deepLayer M hL).succ)) ℝ :=
  Matrix.updateRow ((baseParams M u) (deepLayer M hL)) ⟨0, hrow⟩
    (fun _ => deepCol M hL u hcol ⟨0, hrow⟩ - smearShift M hL u hm1 hcol)

/-- The smeared Params tuple: `baseParams` with the deepest layer replaced by `smearedDeepLayer`. -/
noncomputable def smParams (u : Fin (routeMAmbient M) → ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) : Params M :=
  Function.update (baseParams M u) (deepLayer M hL) (smearedDeepLayer M hL u hrow hcol hm1)

/-! ## The telescope rate (the keystone — consumes the front fact) -/

/-- **The front product is unchanged by the smear.** `smParams` differs from `baseParams` only at the
deepest layer `L−1`, so the front product `prodAux … (L−1)` (layers `0..L−2`) is unaffected:
`prodAux M (smParams u) (L−1) = frontMat u`. -/
theorem prodAux_smParams_front_eq (u : Fin (routeMAmbient M) → ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    prodAux M (smParams M hL u hrow hcol hm1) (L - 1) (by omega) = frontMat M hL u := by
  rw [frontMat]
  refine prodAux_congr_of_eqOn_prefix M (smParams M hL u hrow hcol hm1) (baseParams M u)
    (L - 1) (by omega) (fun s hs => ?_)
  -- `s < L−1` ⟹ `s ≠ deepLayer M hL = ⟨L−1,_⟩`, so the `Function.update` does not fire.
  have hsne : s ≠ deepLayer M hL := by
    intro h; rw [h, deepLayer] at hs; simp only [Fin.val_mk] at hs; omega
  rw [smParams, Function.update_of_ne hsne]

/-- **The deepest-layer matrix of `smParams` is `smearedDeepLayer`.** -/
theorem smParams_deepLayer (u : Fin (routeMAmbient M) → ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    smParams M hL u hrow hcol hm1 (deepLayer M hL) = smearedDeepLayer M hL u hrow hcol hm1 := by
  rw [smParams, Function.update_self]

/-- **The front-fact entry relation** (the shear cancellation, entrywise). Off the pole, with a width-1
layer at `p` (`M ⟨p,_⟩ = 1`, `p ≤ L−1`), the routing applied to the pivot column reproduces each
residual column entrywise: `frontMat i ⟨0,_⟩ · routing 0 r = frontMat i (residSel r)`. This is the
`(i,r)` entry of the landed `prodAux_frontScalarShear_cancel` (`P₁·Λ₀ = P₂`). -/
theorem frontMat_routing_eq_resid (u : Fin (routeMAmbient M) → ℝ)
    (p : ℕ) (hp : p < L + 1) (hp1 : M ⟨p, hp⟩ = 1) (hple : p ≤ L - 1)
    (hm1 : 0 < M ⟨L - 1, by omega⟩)
    (hc : (∑ i, (frontMat M hL u i ⟨0, hm1⟩) ^ 2) ≠ 0)
    (i : Fin (M 0)) (r : Fin (M ⟨L - 1, by omega⟩ - 1)) :
    frontMat M hL u i ⟨0, hm1⟩ * routing M hL u hm1 0 r
      = frontMat M hL u i (residSel M hL hm1 r) := by
  -- `P₁ = pivotCol`, `P₂ = residCols`, `Λ₀ = routing`; the cancellation `P₁·Λ₀ = P₂` from §3.
  have hcancel := prodAux_frontScalarShear_cancel M (baseParams M u) p hp hp1
    (L - 1) hple (by omega) hm1 (by rw [← frontMat]; exact hc) (residSel M hL hm1)
    (pivotCol M hL u hm1) (residCols M hL u hm1)
    (fun i => rfl) (fun i r => rfl)
  -- `routing = (P₁ᵀP₁)⁻¹P₁ᵀP₂`, so `hcancel : P₁ * routing = residCols`. Read entry `(i, r)`.
  have hr : (pivotCol M hL u hm1 * routing M hL u hm1) i r = residCols M hL u hm1 i r := by
    rw [routing]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at hcancel ⊢; rw [hcancel]
  rw [Matrix.mul_apply, Fin.sum_univ_one, pivotCol, residCols] at hr
  exact hr

/-- **The smeared-column sum collapse** (generic, the sum-arithmetic core). With the front-fact relation
`f 0 · lam r = f (r.succ)`, the pivot-row shear `−∑ lam·d` cancels the residual sum, leaving the pivot
term: `∑ⱼ f j · (if j = 0 then d 0 − ∑ᵣ lam r · d (r.succ) else d j) = d 0 · f 0`. Pure `Fin (w+1)`
sum-arithmetic (`Fin.sum_univ_succAbove` at the pivot `0` + `Fin.succAbove_zero`). -/
theorem sum_smearedCol_collapse {w : ℕ} (f d : Fin (w + 1) → ℝ) (lam : Fin w → ℝ)
    (hfront : ∀ r : Fin w, f 0 * lam r = f (Fin.succ r)) :
    (∑ j, f j * (if j = 0 then d 0 - (∑ r, lam r * d (Fin.succ r)) else d j)) = d 0 * f 0 := by
  rw [Fin.sum_univ_succAbove _ (0 : Fin (w + 1))]
  simp only [Fin.succAbove_zero, if_true]
  have hres : ∀ r : Fin w,
      f (Fin.succ r) * (if (Fin.succ r) = 0 then d 0 - (∑ r, lam r * d (Fin.succ r))
        else d (Fin.succ r)) = f (Fin.succ r) * d (Fin.succ r) :=
    fun r => by rw [if_neg (Fin.succ_ne_zero r)]
  rw [Finset.sum_congr rfl (fun r _ => hres r), mul_sub, Finset.mul_sum]
  have hh : ∀ r : Fin w, f 0 * (lam r * d (Fin.succ r)) = f (Fin.succ r) * d (Fin.succ r) :=
    fun r => by rw [← mul_assoc, hfront r]
  rw [Finset.sum_congr rfl (fun r _ => hh r)]; ring

/-- **The smeared-column sum collapse at an opaque positive width** (the chart-shaped instance of
`sum_smearedCol_collapse`). For `0 < n`, pivot `⟨0,hn⟩`, residual selector `Fin.cast _ ∘ Fin.succ`
(matching `residSel`), and the front-fact relation `f ⟨0,hn⟩ · lam r = f (cast (r.succ))`, the shear
cancels: `∑ⱼ f j · (if j = ⟨0,hn⟩ then d ⟨0,hn⟩ − ∑ᵣ lam r · d (cast r.succ) else d j) = d ⟨0,hn⟩ · f ⟨0,hn⟩`.
Destructures `n = w+1` and reduces to `sum_smearedCol_collapse`. -/
theorem sum_smearedCol_collapse_opaque {n : ℕ} (hn : 0 < n) (f d : Fin n → ℝ) (lam : Fin (n - 1) → ℝ)
    (hf : ∀ r : Fin (n - 1), f ⟨0, hn⟩ * lam r = f (Fin.cast (by omega) r.succ)) :
    (∑ j, f j * (if j = ⟨0, hn⟩ then d ⟨0, hn⟩ - (∑ r, lam r * d (Fin.cast (by omega) r.succ))
        else d j)) = d ⟨0, hn⟩ * f ⟨0, hn⟩ := by
  obtain ⟨w, rfl⟩ : ∃ w, n = w + 1 := ⟨n - 1, by omega⟩
  have key := sum_smearedCol_collapse (w := w) f d (fun r => lam (Fin.cast (by omega) r)) ?_
  · convert key using 2 <;> simp
  · intro r; have := hf (Fin.cast (by omega) r); simpa using this

/-- **The telescope (the keystone): the chart product is `u_p`-scaled column 0 of the front product.**
Off the pole `‖col 0‖² ≠ 0`, the deepest-layer shear cancels via the front fact, leaving
`prod M (smParams u) i ⟨0,_⟩ = u_p · frontMat u i ⟨0,_⟩` (with `u_p = deepCol u ⟨0,_⟩` the pivot row
entry). `c = M_L = 1` (the single deepest column), so the product is a single column. -/
theorem prod_smParams_eq_smul_pivotCol (u : Fin (routeMAmbient M) → ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hc1 : M (deepLayer M hL).succ = 1)
    (p : ℕ) (hp : p < L + 1) (hp1 : M ⟨p, hp⟩ = 1) (hple : p ≤ L - 1)
    (hm1 : 0 < M ⟨L - 1, by omega⟩)
    (hc : (∑ i, (frontMat M hL u i ⟨0, hm1⟩) ^ 2) ≠ 0)
    (i : Fin (M 0)) (jc : Fin (M (Fin.last L))) :
    prod M (smParams M hL u hrow hcol hm1) i jc
      = deepCol M hL u hcol ⟨0, hrow⟩ * frontMat M hL u i ⟨0, hm1⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  set A := smParams M hL u hrow hcol hm1 with hAdef
  -- Peel the last (deepest) layer via `prodAux_succ`: `prod = prodAux m * reindex(A_m)`.
  have e1 : M (⟨m, Nat.lt_of_succ_lt (Nat.lt_succ_self (m + 1))⟩ : Fin (m + 1 + 1))
      = M ((⟨m, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (m + 1))⟩ : Fin (m + 1)).castSucc) := rfl
  have e2 : M (⟨m + 1, Nat.lt_succ_self (m + 1)⟩ : Fin (m + 1 + 1))
      = M ((⟨m, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (m + 1))⟩ : Fin (m + 1)).succ) := rfl
  show prodAux M A (m + 1) (Nat.lt_succ_self (m + 1)) i jc = _
  rw [prodAux_succ M A m (Nat.lt_succ_self (m + 1)) e1 e2]
  -- Expand the entry FIRST (before any rewrite that mangles the syntactic product form).
  rw [Matrix.mul_apply]
  -- The first-`m` product is the front product; the last layer is `smearedDeepLayer` (reindex collapses).
  have hfront : prodAux M A m (Nat.lt_of_succ_lt (Nat.lt_succ_self (m + 1)))
      = frontMat M hL u := by
    have := prodAux_smParams_front_eq M hL u hrow hcol hm1
    simpa [hAdef, Nat.add_sub_cancel] using this
  have hlayer : A (⟨m, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (m + 1))⟩ : Fin (m + 1))
      = smearedDeepLayer M hL u hrow hcol hm1 := by
    have h := smParams_deepLayer M hL u hrow hcol hm1
    rw [hAdef]; exact h
  -- The reindexed deepest layer at `(t, jc)` is `smearedDeepLayer t jc` (reindex by rfl-true widths).
  rw [show (finCongr e1.symm) = Equiv.refl _ from finCongr_refl _,
      show (finCongr e2.symm) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl]
  rw [hfront, hlayer]
  -- Goal: `∑ j, frontMat i j * smearedDeepLayer j jc = deepCol ⟨0,hrow⟩ * frontMat i ⟨0,hm1⟩`.
  -- The front-fact relation in the `cast∘succ` residual form (LANDED `frontMat_routing_eq_resid`).
  have hfr : ∀ r, frontMat M hL u i ⟨0, hrow⟩ * routing M hL u hm1 0 r
      = frontMat M hL u i (Fin.cast (by omega) r.succ) := fun r => by
    have h := frontMat_routing_eq_resid M hL u p hp hp1 hple hm1 hc i r
    rw [residSel] at h; convert h using 3
  -- The opaque-width collapse (LANDED): `f=frontMat i, d=deepCol, lam=routing 0` closes the `if`-form sum.
  have hfin := sum_smearedCol_collapse_opaque (L := m + 1) (n := M (deepLayer M hL).castSucc) hrow
    (frontMat M hL u i) (deepCol M hL u hcol) (routing M hL u hm1 0) hfr
  -- Per-term readout (term-mode, column kept as `jc`; `hjc : jc = ⟨0,hcol⟩` recovers `deepCol`). Dodges
  -- the `rw`/`simp` pattern-fail by building the per-term `Eq` and feeding `Finset.sum_congr`.
  have hjc : jc = ⟨0, hcol⟩ := Fin.ext (by have := jc.isLt; have : M (Fin.last (m + 1)) = 1 := hc1; omega)
  have hbody : ∀ j, frontMat M hL u i j * smearedDeepLayer M hL u hrow hcol hm1 j jc
      = frontMat M hL u i j * (if j = ⟨0, hrow⟩
          then deepCol M hL u hcol ⟨0, hrow⟩ - smearShift M hL u hm1 hcol else deepCol M hL u hcol j) :=
    fun j => congrArg (frontMat M hL u i j * ·) (by
      rw [smearedDeepLayer, Matrix.updateRow_apply, hjc]
      simp only [deepCol]
      rfl)
  calc (∑ j, frontMat M hL u i j * smearedDeepLayer M hL u hrow hcol hm1 j jc)
      = ∑ j, frontMat M hL u i j * (if j = ⟨0, hrow⟩
          then deepCol M hL u hcol ⟨0, hrow⟩ - smearShift M hL u hm1 hcol else deepCol M hL u hcol j) :=
        Finset.sum_congr rfl (fun j _ => hbody j)
    _ = deepCol M hL u hcol ⟨0, hrow⟩ * frontMat M hL u i ⟨0, hrow⟩ := hfin
    _ = deepCol M hL u hcol ⟨0, hrow⟩ * frontMat M hL u i ⟨0, hm1⟩ := rfl

/-! ## The MP leg (the flat chart `phiSm` + measure-preservation + measurable embedding) -/

/-- **Width-free single-coordinate subtractive shear is measure-preserving** (the generic wrapper around
`measurePreserving_shearAt`). For a pivot `p : Fin N` and a function `f` invariant under updating coord
`p` (`hinv : f (update u p a) = f u`), the map `u ↦ update u p (u p − f u)` preserves volume. Destructures
`N = n+1` once; `g y := −f ((@Fin.insertNth n (fun _ => ℝ) p 0 y))`, and `g (fun k => u (p.succAbove k)) = −f u` by `hinv`
(reconstructing `u` from `insertNth p (u p) (removeNth)`). -/
theorem measurePreserving_updateSub_of_coordInvariant {N : ℕ} (p : Fin N)
    (f : (Fin N → ℝ) → ℝ) (hf : Measurable f)
    (hinv : ∀ (u : Fin N → ℝ) (a : ℝ), f (Function.update u p a) = f u) :
    MeasurePreserving (fun u : Fin N → ℝ => Function.update u p (u p - f u))
      (volume : Measure (Fin N → ℝ)) volume := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := p.pos; omega⟩
  -- `g y := − f (insertNth p 0 y)`; `measurePreserving_shearAt p g` adds `g (fun k => u (succAbove k))`.
  have hins : Measurable (fun y : Fin n → ℝ => (@Fin.insertNth n (fun _ => ℝ) p (0 : ℝ) y)) := by
    rw [measurable_pi_iff]
    intro j
    rcases Fin.eq_self_or_eq_succAbove p j with rfl | ⟨k, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact measurable_const
    · simp only [Fin.insertNth_apply_succAbove]; exact measurable_pi_apply k
  have hg : Measurable (fun y : Fin n → ℝ => -f ((@Fin.insertNth n (fun _ => ℝ) p 0 y))) := (hf.comp hins).neg
  have hsh := measurePreserving_shearAt p (fun y : Fin n → ℝ => -f ((@Fin.insertNth n (fun _ => ℝ) p 0 y))) hg
  -- the two maps are literally equal, so transport `hsh` along a `funext`.
  have hmap : (fun u : Fin (n + 1) → ℝ =>
        Function.update u p (u p + -f ((@Fin.insertNth n (fun _ => ℝ) p 0 (fun k => u (p.succAbove k))))))
      = fun u : Fin (n + 1) → ℝ => Function.update u p (u p - f u) := by
    funext u
    have hrec : (@Fin.insertNth n (fun _ => ℝ) p (0 : ℝ) (fun k => u (p.succAbove k))) = Function.update u p 0 := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove p j with rfl | ⟨k, rfl⟩
      · rw [Fin.insertNth_apply_same, Function.update_self]
      · rw [Fin.insertNth_apply_succAbove, Function.update_of_ne (Fin.succAbove_ne p k)]
    rw [hrec, hinv u 0, sub_eq_add_neg]
  rw [← hmap]; exact hsh

/-- **The single-coordinate subtractive shear as a `MeasurableEquiv`** (for a coord-`p`-invariant `f`).
The inverse is the additive shear `v ↦ update v p (v p + f v)`. Used to get `MeasurableEmbedding` (MP
alone does not). -/
noncomputable def updateSubME {N : ℕ} (p : Fin N) (f : (Fin N → ℝ) → ℝ) (hf : Measurable f)
    (hinv : ∀ (u : Fin N → ℝ) (a : ℝ), f (Function.update u p a) = f u) :
    (Fin N → ℝ) ≃ᵐ (Fin N → ℝ) where
  toFun u := Function.update u p (u p - f u)
  invFun v := Function.update v p (v p + f v)
  left_inv u := by
    have hfu : f (Function.update u p (u p - f u)) = f u := hinv u _
    funext k
    by_cases hk : k = p
    · subst hk; simp only [Function.update_self, hfu]; ring
    · simp only [Function.update_of_ne hk]
  right_inv v := by
    have hfv : f (Function.update v p (v p + f v)) = f v := hinv v _
    funext k
    by_cases hk : k = p
    · subst hk; simp only [Function.update_self, hfv]; ring
    · simp only [Function.update_of_ne hk]
  measurable_toFun :=
    measurable_update'.comp (measurable_id.prodMk ((measurable_pi_apply p).sub hf))
  measurable_invFun :=
    measurable_update'.comp (measurable_id.prodMk ((measurable_pi_apply p).add hf))

/-- The deepest-`(0,0)` flat coordinate: `flatCoordOf` of the `FlatIdx` slot `(deepLayer, row 0, col 0)`.
The single coord the smear shears. -/
noncomputable def smPivotCoord (hrow : 0 < M (deepLayer M hL).castSucc)
    (hcol : 0 < M (deepLayer M hL).succ) : Fin (routeMAmbient M) :=
  flatCoordOf M ⟨⟨deepLayer M hL, ⟨0, hrow⟩⟩, ⟨0, hcol⟩⟩

/-- **`flatCoordOf` is injective** (`Fin.cast` ∘ `Fintype.equivFin`, both injective). -/
theorem flatCoordOf_injective : Function.Injective (flatCoordOf M) := by
  intro a b hab
  rw [flatCoordOf, flatCoordOf] at hab
  exact (Fintype.equivFin (FlatIdx M)).injective (Fin.cast_injective _ hab)

/-- **The base-params decode at a non-pivot slot is unchanged by the pivot-coord update.** For a slot
`q ≠ (deepLayer, 0, 0)`, `baseParams (Function.update u smPivotCoord a)` agrees with `baseParams u`. -/
theorem baseParams_update_pivot_apply (u : Fin (routeMAmbient M) → ℝ) (a : ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (q : FlatIdx M) (hq : q ≠ ⟨⟨deepLayer M hL, ⟨0, hrow⟩⟩, ⟨0, hcol⟩⟩) :
    (baseParams M (Function.update u (smPivotCoord M hL hrow hcol) a)) q.1.1 q.1.2 q.2
      = (baseParams M u) q.1.1 q.1.2 q.2 := by
  rw [baseParams, baseParams, paramsEquivFlat_symm_decode, paramsEquivFlat_symm_decode,
    Function.update_of_ne]
  exact fun h => hq (flatCoordOf_injective M h)

/-- **The front product is unchanged by the pivot-coord update** (it reads only layers `0..L−2`, none
the deepest). Via `prodAux_congr_of_eqOn_prefix` + `baseParams_update_pivot_apply` (a non-deepest layer
slot differs from the deepest `(0,0)` slot in its layer index). -/
theorem frontMat_update_pivot (u : Fin (routeMAmbient M) → ℝ) (a : ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ) :
    frontMat M hL (Function.update u (smPivotCoord M hL hrow hcol) a) = frontMat M hL u := by
  rw [frontMat, frontMat]
  refine prodAux_congr_of_eqOn_prefix M _ _ (L - 1) (by omega) (fun s hs => ?_)
  funext i j
  refine baseParams_update_pivot_apply M hL u a hrow hcol ⟨⟨s, i⟩, j⟩ (fun h => ?_)
  -- the slot's layer `s` is `< L−1` so `s ≠ deepLayer = ⟨L−1,_⟩`; the FlatIdx equality forces it.
  have : (s : Fin L) = deepLayer M hL := congrArg (fun q : FlatIdx M => q.1.1) h
  rw [this, deepLayer] at hs; simp only [Fin.val_mk] at hs; omega

/-- **The residual deepest-column reads are unchanged by the pivot-coord update** (they read rows
`1..m1−1`, never the pivot row `0`). -/
theorem deepCol_update_pivot_resid (u : Fin (routeMAmbient M) → ℝ) (a : ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) (r : Fin (M ⟨L - 1, by omega⟩ - 1)) :
    deepCol M hL (Function.update u (smPivotCoord M hL hrow hcol) a) hcol (residSel M hL hm1 r)
      = deepCol M hL u hcol (residSel M hL hm1 r) := by
  rw [deepCol, deepCol]
  refine baseParams_update_pivot_apply M hL u a hrow hcol
    ⟨⟨deepLayer M hL, residSel M hL hm1 r⟩, ⟨0, hcol⟩⟩ (fun h => ?_)
  -- `q = q*` forces the FlatRowIdx parts equal; same layer ⟹ rows equal, but `residSel r`'s val ≥ 1 ≠ 0.
  have hrow_eq : (⟨deepLayer M hL, residSel M hL hm1 r⟩ : FlatRowIdx M)
      = ⟨deepLayer M hL, ⟨0, hrow⟩⟩ := congrArg Sigma.fst h
  have hval : (residSel M hL hm1 r) = (⟨0, hrow⟩ : Fin (M (deepLayer M hL).castSucc)) :=
    eq_of_heq (Sigma.ext_iff.1 hrow_eq).2
  rw [residSel] at hval
  have := congrArg Fin.val hval
  simp only [Fin.val_cast, Fin.val_succ] at this; omega

/-- **The routing is unchanged by the pivot-coord update** (it is built from `pivotCol`/`residCols`,
both reading only `frontMat`). -/
theorem routing_update_pivot (u : Fin (routeMAmbient M) → ℝ) (a : ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    routing M hL (Function.update u (smPivotCoord M hL hrow hcol) a) hm1
      = routing M hL u hm1 := by
  have hp : pivotCol M hL (Function.update u (smPivotCoord M hL hrow hcol) a) hm1
      = pivotCol M hL u hm1 := by
    funext i j; rw [pivotCol, pivotCol, frontMat_update_pivot M hL u a hrow hcol]
  have hr : residCols M hL (Function.update u (smPivotCoord M hL hrow hcol) a) hm1
      = residCols M hL u hm1 := by
    funext i r; rw [residCols, residCols, frontMat_update_pivot M hL u a hrow hcol]
  rw [routing, routing, hp, hr]

/-- **`smearShift` is invariant under the pivot-coord update** (Codex's flagged risk, now discharged):
the front coords (`routing`) and the residual rows (`deepCol (residSel r)`) are all unchanged. -/
theorem smearShift_update_pivot (u : Fin (routeMAmbient M) → ℝ) (a : ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    smearShift M hL (Function.update u (smPivotCoord M hL hrow hcol) a) hm1 hcol
      = smearShift M hL u hm1 hcol := by
  rw [smearShift, smearShift]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [routing_update_pivot M hL u a hrow hcol hm1, deepCol_update_pivot_resid M hL u a hrow hcol hm1 r]

/-- The flat chart `phiSm`: a single subtractive shear at the deepest-`(0,0)` coord `smPivotCoord`, by
`smearShift` (the front-coords routing × residual deepest-rows). -/
noncomputable def phiSm (u : Fin (routeMAmbient M) → ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) : Fin (routeMAmbient M) → ℝ :=
  Function.update u (smPivotCoord M hL hrow hcol)
    (u (smPivotCoord M hL hrow hcol) - smearShift M hL u hm1 hcol)

/-- **`smearShift` (as a function of the flat point) is measurable.** `frontMat`/`routing`/`deepCol`
are continuous polynomial/rational-away-from-pole reads of `u` (the `1×1` Gram inverse is `(·)⁻¹`,
measurable everywhere). -/
theorem smearShiftFlat_measurable (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    Measurable (fun u : Fin (routeMAmbient M) → ℝ => smearShift M hL u hm1 hcol) := by
  -- `baseParams u` is a measurable function of `u` (a measurable equiv); every entry is `measurable_pi_apply`
  -- composed with it. `frontMat`/`pivotCol`/`residCols`/`deepCol` are finite sums/products of such entries;
  -- `routing` adds the `1×1` Gram inverse `(·)⁻¹` (measurable everywhere on ℝ).
  -- `frontMat u i j` and `deepCol u i` are CONTINUOUS in `u` (continuous_prodAux ∘ continuous_symm),
  -- hence measurable. `routing 0 r` adds the `1×1` Gram inverse — `(‖col0‖²)⁻¹`, measurable on ℝ.
  have hsymm : Continuous (fun u : Fin (routeMAmbient M) → ℝ => baseParams M u) :=
    continuous_paramsEquivFlat_symm M
  have hfront : ∀ (i : Fin (M 0)) (j : Fin (M ⟨L - 1, by omega⟩)),
      Measurable (fun u : Fin (routeMAmbient M) → ℝ => frontMat M hL u i j) := by
    intro i j
    have : Continuous (fun u : Fin (routeMAmbient M) → ℝ => frontMat M hL u i j) :=
      ((continuous_prodAux M (L - 1) (by omega)).comp hsymm).matrix_elem i j
    exact this.measurable
  have hdeep : ∀ (i : Fin (M (deepLayer M hL).castSucc)),
      Measurable (fun u : Fin (routeMAmbient M) → ℝ => deepCol M hL u hcol i) := by
    intro i
    have : Continuous (fun u : Fin (routeMAmbient M) → ℝ => deepCol M hL u hcol i) := by
      have hc : Continuous (fun u : Fin (routeMAmbient M) → ℝ =>
          (baseParams M u) (deepLayer M hL) i ⟨0, hcol⟩) :=
        (((continuous_apply (deepLayer M hL)).comp hsymm).matrix_elem i ⟨0, hcol⟩)
      exact hc
    exact this.measurable
  -- `routing 0 r = (∑ᵢ frontMat i ⟨0⟩²)⁻¹ · (∑ᵢ frontMat i ⟨0⟩ · frontMat i (residSel r))` (the landed
  -- `scalarGram` `1×1`-Gram closed form), measurable via `measurable_inv` + sums of `hfront` products.
  have hroutingForm : ∀ (u : Fin (routeMAmbient M) → ℝ) (r),
      routing M hL u hm1 0 r
        = (∑ i, (frontMat M hL u i ⟨0, hm1⟩) ^ 2)⁻¹
          * (∑ i, frontMat M hL u i ⟨0, hm1⟩ * frontMat M hL u i (residSel M hL hm1 r)) := by
    intro u r
    have hinv : (((pivotCol M hL u hm1).transpose * pivotCol M hL u hm1)⁻¹ : Matrix (Fin 1) (Fin 1) ℝ) 0 0
        = (∑ i, (frontMat M hL u i ⟨0, hm1⟩) ^ 2)⁻¹ := by
      rw [Matrix.inv_def, Matrix.det_fin_one, Matrix.adjugate_fin_one]
      simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Ring.inverse_eq_inv', Matrix.mul_apply, Matrix.transpose_apply, pivotCol, Fin.sum_univ_one]
      exact congrArg _ (Finset.sum_congr rfl (fun i _ => by rw [sq]))
    rw [routing, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.mul_apply, Fin.sum_univ_one, hinv]
    simp only [Matrix.transpose_apply, pivotCol, residCols]; ring
  have hrouting : ∀ r, Measurable (fun u : Fin (routeMAmbient M) → ℝ => routing M hL u hm1 0 r) := by
    intro r
    have heq : (fun u : Fin (routeMAmbient M) → ℝ => routing M hL u hm1 0 r)
        = fun u => (∑ i, (frontMat M hL u i ⟨0, hm1⟩) ^ 2)⁻¹
          * (∑ i, frontMat M hL u i ⟨0, hm1⟩ * frontMat M hL u i (residSel M hL hm1 r)) :=
      funext (fun u => hroutingForm u r)
    rw [heq]
    refine ((Finset.measurable_sum _ (fun i _ => (hfront i ⟨0, hm1⟩).pow_const 2)).inv).mul ?_
    exact Finset.measurable_sum _ (fun i _ => (hfront i ⟨0, hm1⟩).mul (hfront i (residSel M hL hm1 r)))
  -- `smearShift = ∑ r, routing 0 r · deepCol (residSel r)`.
  refine Finset.measurable_sum _ (fun r _ => ?_)
  exact (hrouting r).mul (hdeep (residSel M hL hm1 r))

/-- **`phiSm` is measure-preserving** — the subtractive shear at `smPivotCoord` by the pivot-coord-
invariant `smearShift` (the landed `measurePreserving_updateSub_of_coordInvariant`). -/
theorem measurePreserving_phiSm (hrow : 0 < M (deepLayer M hL).castSucc)
    (hcol : 0 < M (deepLayer M hL).succ) (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    MeasurePreserving (fun u => phiSm M hL u hrow hcol hm1)
      (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume := by
  exact measurePreserving_updateSub_of_coordInvariant (smPivotCoord M hL hrow hcol)
    (fun u => smearShift M hL u hm1 hcol) (smearShiftFlat_measurable M hL hcol hm1)
    (fun u a => smearShift_update_pivot M hL u a hrow hcol hm1)

/-! ## The connection `(paramsEquivFlat).symm (phiSm u) = smParams u` -/

/-- **`smParams` at a non-pivot slot equals `baseParams`.** For `q ≠ (deepLayer, 0, 0)` with `M_L = 1`:
off the deepest layer `Function.update_of_ne`; on the deepest layer the row `i ≠ ⟨0,hrow⟩` (else, the
column being forced `0` by `M_L = 1`, `q = q*`), so `Matrix.updateRow_ne`. -/
theorem smParams_apply_ne_pivot (u : Fin (routeMAmbient M) → ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) (hc1 : M (deepLayer M hL).succ = 1)
    (q : FlatIdx M) (hq : q ≠ ⟨⟨deepLayer M hL, ⟨0, hrow⟩⟩, ⟨0, hcol⟩⟩) :
    (smParams M hL u hrow hcol hm1) q.1.1 q.1.2 q.2 = (baseParams M u) q.1.1 q.1.2 q.2 := by
  obtain ⟨⟨s, i⟩, j⟩ := q
  rw [smParams]
  by_cases hs : s = deepLayer M hL
  · subst hs
    rw [Function.update_self, smearedDeepLayer, Matrix.updateRow_apply, if_neg]
    -- `i ≠ ⟨0,hrow⟩`: else, `j = ⟨0,hcol⟩` (subsingleton col, `M_L = 1`), giving `q = q*`.
    intro hi; subst hi
    apply hq
    have hjsub : Subsingleton (Fin (M (deepLayer M hL).succ)) := by rw [hc1]; infer_instance
    rw [hjsub.elim j ⟨0, hcol⟩]
  · rw [Function.update_of_ne hs]

/-- **The connection: `(paramsEquivFlat).symm (phiSm u) = smParams u`.** The flat chart `phiSm`
(single-coord shear at `smPivotCoord`) decodes to the Params-level `smParams` (deepest-row-0 shear).
Per-slot: at the pivot `q*` both give `u_p − smearShift`; off it, `phiSm` is `u` (unchanged coord) and
`smParams` is `baseParams` (the `smParams_apply_ne_pivot` helper, using `M_L = 1`). -/
theorem paramsEquivFlat_symm_phiSm_eq_smParams (u : Fin (routeMAmbient M) → ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) (hc1 : M (deepLayer M hL).succ = 1) :
    (paramsEquivFlat M).symm (phiSm M hL u hrow hcol hm1) = smParams M hL u hrow hcol hm1 := by
  funext s i j
  set q : FlatIdx M := ⟨⟨s, i⟩, j⟩ with hq
  -- LHS decodes to `phiSm u (flatCoordOf q)`.
  rw [show ((paramsEquivFlat M).symm (phiSm M hL u hrow hcol hm1)) s i j
      = phiSm M hL u hrow hcol hm1 (flatCoordOf M q) from
    paramsEquivFlat_symm_decode M (phiSm M hL u hrow hcol hm1) q]
  by_cases hqp : q = ⟨⟨deepLayer M hL, ⟨0, hrow⟩⟩, ⟨0, hcol⟩⟩
  · -- pivot slot: both sides are `u_p − smearShift`.
    have hcoord : flatCoordOf M q = smPivotCoord M hL hrow hcol := by rw [hqp]; rfl
    rw [phiSm, hcoord, Function.update_self]
    -- RHS: `smParams q* = smearedDeepLayer ... ⟨0,hrow⟩ ⟨0,hcol⟩ = u_p − smearShift`.
    have hrhs : (smParams M hL u hrow hcol hm1) q.1.1 q.1.2 q.2
        = deepCol M hL u hcol ⟨0, hrow⟩ - smearShift M hL u hm1 hcol := by
      rw [hqp, smParams, Function.update_self, smearedDeepLayer, Matrix.updateRow_self]
    rw [hrhs]
    -- `u smPivotCoord = deepCol ⟨0,hrow⟩` (the pivot coord decodes to the deepest (0,0) entry).
    have hup : u (smPivotCoord M hL hrow hcol) = deepCol M hL u hcol ⟨0, hrow⟩ :=
      (paramsEquivFlat_symm_decode M u ⟨⟨deepLayer M hL, ⟨0, hrow⟩⟩, ⟨0, hcol⟩⟩).symm
    rw [hup]
  · -- non-pivot slot: `phiSm` unchanged (= `u (flatCoordOf q) = baseParams ...`), `smParams = baseParams`.
    have hne : flatCoordOf M q ≠ smPivotCoord M hL hrow hcol :=
      fun h => hqp (flatCoordOf_injective M h)
    rw [phiSm, Function.update_of_ne hne]
    rw [smParams_apply_ne_pivot M hL u hrow hcol hm1 hc1 q hqp]
    rw [baseParams, paramsEquivFlat_symm_decode]

/-- **`phiSm` is a measurable embedding** (it is the `updateSubME` shear, a measurable equivalence). -/
theorem measurableEmbedding_phiSm (hrow : 0 < M (deepLayer M hL).castSucc)
    (hcol : 0 < M (deepLayer M hL).succ) (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    MeasurableEmbedding (fun u => phiSm M hL u hrow hcol hm1) := by
  have h : (fun u => phiSm M hL u hrow hcol hm1)
      = updateSubME (smPivotCoord M hL hrow hcol) (fun u => smearShift M hL u hm1 hcol)
        (smearShiftFlat_measurable M hL hcol hm1)
        (fun u a => smearShift_update_pivot M hL u a hrow hcol hm1) := by
    funext u; rfl
  rw [h]
  exact (updateSubME _ _ _ _).measurableEmbedding

/-! ## The rate in flat coordinates + the (1,1) atom -/

/-- **The flat-chart rate** `routeMCore M (phiSm u) = (u_p)² · U` off the pole, where
`u_p = u (smPivotCoord)` and `U = ∑ᵢ (frontMat u i ⟨0,_⟩)² = ‖P₁‖²`. Composes the connection
(`routeMCore (phiSm u) = dlnLoss (smParams u)`) with the rate keystone (deepest product `= u_p · P₁`,
`M_L = 1` single column). -/
theorem routeMCore_phiSm_offpole (u : Fin (routeMAmbient M) → ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hc1 : M (deepLayer M hL).succ = 1)
    (p : ℕ) (hp : p < L + 1) (hp1 : M ⟨p, hp⟩ = 1) (hple : p ≤ L - 1)
    (hm1 : 0 < M ⟨L - 1, by omega⟩)
    (hc : (∑ i, (frontMat M hL u i ⟨0, hm1⟩) ^ 2) ≠ 0) :
    routeMCore M (phiSm M hL u hrow hcol hm1)
      = (u (smPivotCoord M hL hrow hcol)) ^ 2 * (∑ i, (frontMat M hL u i ⟨0, hm1⟩) ^ 2) := by
  rw [routeMCore, paramsEquivFlat_symm_phiSm_eq_smParams M hL u hrow hcol hm1 hc1, dlnLoss]
  -- `∑ i, ∑ j, (prod (smParams u) i j)²`; `M_L = 1` ⟹ single column `j`; the keystone gives `u_p · frontMat`.
  have hsucc : (deepLayer M hL).succ = Fin.last L := by
    rw [deepLayer]; apply Fin.ext; simp only [Fin.succ_mk, Fin.val_last]; omega
  have hlast1 : M (Fin.last L) = 1 := by rw [← hsucc]; exact hc1
  have hup : u (smPivotCoord M hL hrow hcol) = deepCol M hL u hcol ⟨0, hrow⟩ :=
    (paramsEquivFlat_symm_decode M u ⟨⟨deepLayer M hL, ⟨0, hrow⟩⟩, ⟨0, hcol⟩⟩).symm
  rw [hup, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- inner sum over `Fin (M (last L))` is a single term (`M_L = 1`), value `(u_p · frontMat i ⟨0⟩)²`.
  have hcard : ∀ j : Fin (M (Fin.last L)), (prod M (smParams M hL u hrow hcol hm1) - 0) i j
      = deepCol M hL u hcol ⟨0, hrow⟩ * frontMat M hL u i ⟨0, hm1⟩ := by
    intro j
    rw [Matrix.sub_apply, Matrix.zero_apply, sub_zero,
      prod_smParams_eq_smul_pivotCol M hL u hrow hcol hc1 p hp hp1 hple hm1 hc i j]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hcard j])]
  rw [Finset.sum_const, show (Finset.univ : Finset (Fin (M (Fin.last L)))).card = 1 from by
    rw [Finset.card_univ, Fintype.card_fin, hlast1]]
  rw [one_smul]; ring

/-! ## The unit factor `U` and its properties (toward the subBox) -/

/-- The unit factor `U = ‖P₁‖² = ∑ᵢ (frontMat u i ⟨0,_⟩)²` (the `u_p`-free factor of the rate). -/
noncomputable def frontU (u : Fin (routeMAmbient M) → ℝ) (hm1 : 0 < M ⟨L - 1, by omega⟩) : ℝ :=
  ∑ i, (frontMat M hL u i ⟨0, hm1⟩) ^ 2

/-- **`frontU` is nonnegative.** -/
theorem frontU_nonneg (u : Fin (routeMAmbient M) → ℝ) (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    0 ≤ frontU M hL u hm1 :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- **`frontU` is continuous** (a finite sum of squares of `frontMat` entries). -/
theorem continuous_frontU (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    Continuous (fun u : Fin (routeMAmbient M) → ℝ => frontU M hL u hm1) := by
  refine continuous_finset_sum _ (fun i _ => ?_)
  exact ((((continuous_prodAux M (L - 1) (by omega)).comp
    (continuous_paramsEquivFlat_symm M)).matrix_elem i ⟨0, hm1⟩).pow 2)

/-- **`frontU` is unchanged by the pivot-coord update** (it reads only the front layers). -/
theorem frontU_update_pivot (u : Fin (routeMAmbient M) → ℝ) (a : ℝ)
    (hrow : 0 < M (deepLayer M hL).castSucc) (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    frontU M hL (Function.update u (smPivotCoord M hL hrow hcol) a) hm1 = frontU M hL u hm1 := by
  rw [frontU, frontU, frontMat_update_pivot M hL u a hrow hcol]

/-! ## The off-pole witness (`frontU > 0` somewhere): the `e₀₀` chain

`frontU` is a polynomial in the front coords; it is non-degenerate exactly when every width `M_s ≥ 1`
(else the front product is identically zero — the chart is vacuous). The witness is the `e₀₀` chain
(every layer `= 1` at `(0,0)`): its front product's `(0,0)` entry is `1`, so `frontU ≥ 1 > 0` there.
These three are a local copy of `DeepestCoreNonvanishing.{e00Witness, cast_e00_entry,
prodAux_e00Witness_zero}` (renamed `…Gen` — that module clashes with this file's import closure on
`continuous_dlnLoss`, so it cannot be imported here). -/

/-- The `e₀₀`-chain witness parameter (local copy, see `DeepestCoreNonvanishing.e00Witness`). -/
noncomputable def e00WitnessGen (M : Fin (L + 1) → ℕ) : Params M :=
  fun _ => Matrix.of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℝ) else 0

/-- A matrix-type cast pushes through entries of an `e₀₀`-style `of` matrix (local copy). -/
private theorem cast_e00_entryGen {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    (h : Matrix (Fin a) (Fin b) ℝ = Matrix (Fin a') (Fin b') ℝ)
    (f : Fin a → Fin b → ℝ) (i : Fin a') (j : Fin b') :
    (cast h (Matrix.of f)) i j = f (Fin.cast ha.symm i) (Fin.cast hb.symm j) := by
  subst ha; subst hb; rfl

/-- The `(0,0)` entry of the `e₀₀`-witness partial product is `1` (local copy, see
`DeepestCoreNonvanishing.prodAux_e00Witness_zero`). -/
theorem prodAux_e00WitnessGen_zero (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 1 ≤ M s)
    (k : ℕ) (hk : k < L + 1) :
    prodAux M (e00WitnessGen M) k hk ⟨0, hpos 0⟩ ⟨0, hpos ⟨k, hk⟩⟩ = 1 := by
  induction k with
  | zero => simp [prodAux, Matrix.one_apply]
  | succ k ih =>
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      set Lyr : Matrix (Fin (M ⟨k, hk'⟩)) (Fin (M ⟨k + 1, hk⟩)) ℝ :=
        (by rw [e1, e2]; exact e00WitnessGen M ⟨k, hkL⟩) with hLyr
      have hLyr_entry : ∀ (i : Fin (M ⟨k, hk'⟩)) (j : Fin (M ⟨k + 1, hk⟩)),
          Lyr i j = if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℝ) else 0 := by
        intro i j
        simp only [hLyr, e00WitnessGen, eq_mpr_eq_cast, cast_cast]
        exact (cast_e00_entryGen (congrArg M e1) (congrArg M e2) (by rw [e1, e2]) _ i j).trans (by
          simp [Fin.coe_cast])
      show (prodAux M (e00WitnessGen M) k hk' * Lyr) ⟨0, hpos 0⟩ ⟨0, hpos ⟨k + 1, hk⟩⟩ = 1
      rw [Matrix.mul_apply,
        Finset.sum_eq_single (⟨0, hpos ⟨k, hk'⟩⟩ : Fin (M ⟨k, hk'⟩))]
      · rw [ih hk', hLyr_entry]; simp
      · intro l _ hl
        have hl0 : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext h)
        rw [hLyr_entry]; simp [hl0]
      · intro h; exact absurd (Finset.mem_univ _) h

/-- The off-pole flat witness point: the `e₀₀` chain encoded to flat coords. -/
noncomputable def offPoleWitness : Fin (routeMAmbient M) → ℝ :=
  paramsEquivFlat M (e00WitnessGen M)

/-- **`baseParams (offPoleWitness) = e00WitnessGen`** (the encode/decode round-trip). -/
theorem baseParams_offPoleWitness :
    baseParams M (offPoleWitness M) = e00WitnessGen M := by
  rw [baseParams, offPoleWitness, MeasurableEquiv.symm_apply_apply]

/-- **`frontU > 0` at the off-pole witness** (the front product's `(0,0)` entry is `1`), when all
widths `M_s ≥ 1`. The `(0,0)` summand of `frontU = ∑ᵢ (frontMat i ⟨0⟩)²` is `1 > 0`. -/
theorem frontU_offPoleWitness_pos (hpos : ∀ s, 1 ≤ M s) (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    0 < frontU M hL (offPoleWitness M) hm1 := by
  -- the front product's `(0,0)` entry is `1`, so the `i = ⟨0⟩` summand is `1`.
  have hentry : frontMat M hL (offPoleWitness M) ⟨0, hpos 0⟩ ⟨0, hm1⟩ = 1 := by
    rw [frontMat, baseParams_offPoleWitness]
    exact prodAux_e00WitnessGen_zero M hpos (L - 1) (by omega)
  rw [frontU]
  refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨⟨0, hpos 0⟩, Finset.mem_univ _, ?_⟩
  rw [hentry]; norm_num

/-- **`smearShift = 0` at the off-pole witness** (the deepest residual rows of the `e₀₀` chain are all
`0`, so every term of the shift sum vanishes). -/
theorem smearShift_offPoleWitness (hcol : 0 < M (deepLayer M hL).succ)
    (hm1 : 0 < M ⟨L - 1, by omega⟩) :
    smearShift M hL (offPoleWitness M) hm1 hcol = 0 := by
  rw [smearShift]
  refine Finset.sum_eq_zero (fun r _ => ?_)
  -- `deepCol (residSel r) = e00WitnessGen deepLayer (residSel r) ⟨0⟩ = 0` (residSel r has val ≥ 1).
  have hdeep : deepCol M hL (offPoleWitness M) hcol (residSel M hL hm1 r) = 0 := by
    rw [deepCol, baseParams_offPoleWitness, e00WitnessGen]
    simp only [Matrix.of_apply]
    rw [if_neg]
    intro h
    -- `residSel r` has `val = (r.succ : ℕ) ≥ 1`, contradicting `↑(residSel r) = 0`.
    have hr0 : ((residSel M hL hm1 r : Fin (M ⟨L - 1, by omega⟩)) : ℕ) = 0 := h.1
    rw [residSel] at hr0
    simp only [Fin.val_cast, Fin.val_succ] at hr0; omega
  rw [hdeep, mul_zero]

/-! ## The abstract pivot-peel (the reusable Tonelli measure-theory primitive)

The subBox divergence factors as a Tonelli peel at the (opaque) pivot coordinate: on a source set
`S = ee⁻¹(Ioo 0 α ×ˢ R)` (`ee = piFinSuccAbove p`), an integrand `|u_p|^s · U(u)^{−c'}` with `U`
pivot-independent and `> 0` on the rest box `R` integrates to `(∫_{(0,α)} |x|^s)·(∫_R U^{−c'}) = ⊤·(>0)`.
This lemma is the network-free core; everything chart-specific feeds it through its hypotheses. -/

/-- **The abstract pivot Tonelli peel `= ⊤`.** For a pivot `p : Fin (n+1)`, a pivot-independent
`U` (`hUindep`), `c'` with the 1-D divergence `htop` (`∫_{(0,α)} |x|^s = ⊤`, supplied by the caller as
the `s ≤ −1` rpow atom), and a positive-measure rest box `R` on which `U > 0`, the source-box integral
of `|u_p|^s · U(u)^{−c'}` is `⊤`. The c-o-v is `piFinSuccAbove p` (volume-preserving) + `setLIntegral_prod`;
the pivot factor is `⊤`, the rest factor `∫_R U^{−c'} > 0` (`setLIntegral_pos_iff` + the witness box). -/
theorem subBox_pivot_peel_diverges {n : ℕ} (p : Fin (n + 1)) (α : ℝ) (hα : 0 < α) (s c' : ℝ)
    (U : (Fin (n + 1) → ℝ) → ℝ) (hUmeas : Measurable U)
    (hUindep : ∀ (x : ℝ) (y : Fin n → ℝ), U (Fin.insertNth p x y) = U (Fin.insertNth p 0 y))
    (R : Set (Fin n → ℝ)) (hRmeas : MeasurableSet R) (hRpos : 0 < (volume : Measure (Fin n → ℝ)) R)
    (hRU : ∀ y ∈ R, 0 < U (Fin.insertNth p 0 y))
    (integ : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (hinteg : ∀ u, integ u = ENNReal.ofReal (|u p| ^ s) * ENNReal.ofReal (U u ^ (-c')))
    (htop : (∫⁻ x in Set.Ioo (0 : ℝ) α, ENNReal.ofReal (|x| ^ s)) = ⊤) :
    ∫⁻ u in (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p) ⁻¹'
        (Set.Ioo (0 : ℝ) α ×ˢ R), integ u = ⊤ := by
  set ee := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p with hee
  have hmp : MeasurePreserving ee (volume : Measure (Fin (n + 1) → ℝ)) volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p
  have hsymapp : ∀ x (y : Fin n → ℝ), ee.symm (x, y) = Fin.insertNth p x y :=
    fun x y => by rw [hee, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
  -- `integ = (integ ∘ ee.symm) ∘ ee` pointwise (valid everywhere; rewrite on the source set), then peel.
  rw [setLIntegral_congr_fun (ee.measurable (measurableSet_Ioo.prod hRmeas))
    (fun u _ => by rw [show integ u = integ (ee.symm (ee u)) from by
      rw [MeasurableEquiv.symm_apply_apply]])]
  rw [hmp.setLIntegral_comp_preimage_emb ee.measurableEmbedding
    (fun q : ℝ × (Fin n → ℝ) => integ (ee.symm q)) (Set.Ioo (0 : ℝ) α ×ˢ R)]
  -- under `ee.symm`, the integrand is `|x|^s · U(insertNth p 0 y)^{−c'}` (pivot = first prod factor).
  have hfac : ∀ (q : ℝ × (Fin n → ℝ)),
      integ (ee.symm q)
        = ENNReal.ofReal (|q.1| ^ s) * ENNReal.ofReal (U (Fin.insertNth p 0 q.2) ^ (-c')) := by
    rintro ⟨x, y⟩
    rw [hinteg]
    have ep : ee.symm (x, y) p = x := by rw [hsymapp, Fin.insertNth_apply_same]
    rw [ep, hsymapp, hUindep]
  simp_rw [hfac]
  rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
    Measure.volume_eq_prod _ _]
  -- the rest factor `U(insertNth p 0 y)^{−c'}` is measurable in `y`.
  have hins : Measurable (fun y : Fin n → ℝ => (@Fin.insertNth n (fun _ => ℝ) p (0 : ℝ) y)) := by
    rw [measurable_pi_iff]; intro j
    rcases Fin.eq_self_or_eq_succAbove p j with rfl | ⟨k, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact measurable_const
    · simp only [Fin.insertNth_apply_succAbove]; exact measurable_pi_apply k
  have hUcomp : Measurable (fun y : Fin n → ℝ => U (Fin.insertNth p 0 y)) := hUmeas.comp hins
  have hUm2 : Measurable (fun y : Fin n → ℝ => ENNReal.ofReal (U (Fin.insertNth p 0 y) ^ (-c'))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [setLIntegral_prod _ (by
    apply Measurable.aemeasurable
    exact (by fun_prop : Measurable (fun q : ℝ × (Fin n → ℝ) => ENNReal.ofReal (|q.1| ^ s))).mul
      (hUm2.comp measurable_snd))]
  have hinner : ∀ x, (∫⁻ y in R, ENNReal.ofReal (|x| ^ s)
      * ENNReal.ofReal (U (Fin.insertNth p 0 y) ^ (-c')) ∂(volume : Measure (Fin n → ℝ)))
      = ENNReal.ofReal (|x| ^ s) * (∫⁻ y in R,
        ENNReal.ofReal (U (Fin.insertNth p 0 y) ^ (-c')) ∂(volume : Measure (Fin n → ℝ))) :=
    fun x => lintegral_const_mul _ hUm2
  simp only [hinner]
  rw [lintegral_mul_const _ (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ s)))]
  rw [htop]
  refine ENNReal.top_mul (ne_of_gt ?_)
  rw [setLIntegral_pos_iff hUm2]
  apply lt_of_lt_of_le hRpos
  apply measure_mono
  intro y hy
  refine ⟨?_, hy⟩
  rw [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact Real.rpow_pos_of_pos (hRU y hy) _

end DLNFibre.DLN.RLCT
