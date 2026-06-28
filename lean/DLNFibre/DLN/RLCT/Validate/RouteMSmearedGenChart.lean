import DLNFibre.DLN.RLCT.Validate.RouteMFrontBottleneck
import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanRate
import DLNFibre.DLN.RLCT.Validate.Case222Lemma2

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
open scoped BigOperators

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

end DLNFibre.DLN.RLCT
