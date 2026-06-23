import DLNFibre.DLN.RLCT.Skeleton
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# `DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion` — the general-M resolution recursion (det-1 phase)

The sound det-1 half of the general-M resolution (C2 = det-1 GL-straighten THEN blow-up). The crux
deliverables, all PROVEN (0 sorry):

- `schur_recursion_step_sound` — the **measure-preserving straightening phase** RLCT split: given a
  measure-preserving chart `χ` factoring the loss near the deepest point as `u·((∑ xᵢ²) + G²)`, the
  RLCT splits as `nReg/2 + rlctAtOn(G²)`. (Transport `rlctAtOn_comp_homeomorph` + germ-rewrite
  `rlctAtOn_germ_local` + unit-strip `rlctAtOn_unit_invariant_aux` + smooth-block `S1.5`.)
- `rlctAtOn_germ_local` — general-domain `rlctAtOn` germ-locality (reusable bedrock).
- `ChainDimSplit` — the additive width split (`drop + red = M`, the reduced chain).
- `prod_one_layer` / `dlnLoss_one_layer_deepest` — the L=1 smooth-block leaf (recursion terminator).

SOUNDNESS NOTE (the (C2) finding): the *clean* `rlctAtOn(dlnLoss M 0) 0 = nReg/2 + rlctAtOn(Mred) 0`
WITHOUT a measure-preserving chart hypothesis is **FALSE** (a measure-preserving recursion conserves
dimension ⟹ telescopes to ambient/2 = 4 for (2,2,2) ≠ the verified 3/2). The general-M chart is the
det-1 straightening (here) THEN a blow-up (monomial Jacobian → `⨅ monomialThreshold`, fm's cover
lane, applied to the residual `G`). The measure-preserving hypothesis on `χ` is load-bearing and
confines this lemma to the det-1 straightening phase; the blow-up's monomial weights live downstream.
Artifacts: `expeditions/.../14-r1-design/codex/g32-chart-structure-{prompt,answer}.md`.
-/

open MeasureTheory
open scoped ENNReal
namespace DLNFibre.DLN.RLCT

/-! The general-domain `rlctAtOn` unit-invariance (the prereq) now lives in `Foundations/S1Local.lean`
as `rlctAtOn_unit_invariant_aux` (beside `rlct_unit_invariant_aux`), reachable transitively via the
`Skeleton` import. Removed from this scratch file to avoid duplication. -/

/-- **The chain dimension split** (Codex Q4): an ADDITIVE split of the width vector `M` into a dropped
part (the resolved pivot dims `δ_s`) and a reduced part (the residual chain widths `M^s − δ_s`),
carried as `drop s + red s = M s` to avoid `Fin (M s − δ)` underflow. `splitEquiv` is the per-vertex
`Fin (drop s) ⊕ Fin (red s) ≃ Fin (M s)` that all the casts route through. -/
structure ChainDimSplit {L : ℕ} (M : Fin (L + 1) → ℕ) where
  drop : Fin (L + 1) → ℕ
  red : Fin (L + 1) → ℕ
  hsum : ∀ s, drop s + red s = M s
  hdrops : 0 < ∑ s, drop s   -- the termination condition: ΣM strictly drops on recursion

/-- The reduced width vector of a split (the residual chain's dimensions). -/
def ChainDimSplit.redM {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M) : Fin (L + 1) → ℕ :=
  S.red

/-- The per-vertex split equivalence `Fin (drop s) ⊕ Fin (red s) ≃ Fin (M s)`. -/
def ChainDimSplit.splitEquiv {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M) (s : Fin (L + 1)) :
    (Fin (S.drop s) ⊕ Fin (S.red s)) ≃ Fin (M s) :=
  (finSumFinEquiv).trans (finCongr (S.hsum s))

/-! ## The G3.2 det-1 Schur straightening — `IsSchurStraighten` (the (A) sub-step, SPECIFY)

> **SUPERSEDED (2026-06-22, pp2 #129/#130, controller-blessed).** This `IsSchurStraighten` datum and
> `schur_straighten_of_data` encode the CLEAN measure-preserving-chart route (`flatCore ∘ χ =ᶠ u · Φ` via
> a homeomorphism `χ`). pp2 #129 (decorrelated) RETRACTED that route: the per-node transvection is det-1 /
> measure-preserving (`mp_schur_transvection_vec`) but the LOSS is NOT invariant under it (`L` unipotent
> ⇏ orthogonal), so the clean factor through a c-o-v is unreachable. The CORRECTED datum is
> `IsSchurStraightenSqueeze` (below): the two-sided SQUEEZE `c₁·Φ ≤ flatCore ≤ c₂·Φ` at the deepest point
> (NO chart, NO Jacobian), consumed by `schur_recursion_step_squeeze`. The decls here are retained as a
> TRUE-but-off-path record: `schur_straighten_of_data` is a true conditional (it packages the datum given
> the clean factor as a hypothesis), but the clean-factor hypothesis is not satisfiable by the actual loss.
> Do NOT build the recursion on these; use the squeeze datum.

The (C2) node is **(B) blow-up THEN (A) det-1 Schur** (pp-hall g118/g121). The lanes split it:
**fm's (B) lane** is the coordinate-subspace blow-up (`pivotBlowupOn`, Jacobian `|u|^{Mval−1}`, the
monomial weight `(k,h)` → `monomialThreshold`). **My (A) lane** is the det-1 Schur straightening
WITHIN each blow-up chart: once the blow-up has made a leading pivot a UNIT, a unit-pivot row/col
clear (Lemma-2-general / the `(uᵢ,ψᵢ)` adapted basis) reduces the residual to a strictly-smaller
zero-core `‖∏C'‖²` and STRAIGHTENS the bilinear rank-defect center `{r−pq=0}` to a coordinate center
`{w=0}` (the det-1 change `w := r−pq`). **Jacobian = 1 (measure-preserving) — NO monomial weight;**
the monomial comes only from fm's (B) blow-up. This is the `resolvedForm` the controller named: the
det-1 normal form handed to fm's blow-up cover.

This is exactly the chart `schur_recursion_step_sound` consumes (a MEASURE-PRESERVING `χ` factoring
`dlnLoss M 0` as `u·((∑ regular²) + dlnLoss M' 0)`). The det-1 Schur is the (A) sub-step; it requires
a UNIT pivot (the hypothesis fm's blow-up supplies — at the bare singular origin the pivot is `0` and
this fails, which is WHY the blow-up runs first). `#109`'s substitution algebra (all diff=0) is the
SOUND core of this step. -/

/-- **The det-1 Schur straightening datum (the (A) sub-step) — SPECIFY, fm's 5-point contract.** A
measure-preserving chart `χ` (Jacobian 1, the det-1 Schur / Lemma-2-general) factoring `dlnLoss M 0`
near the deepest point as a unit `u` times `(regular smooth block) + (reduced-chain core dlnLoss M' 0)`,
with `M' = S.red` strictly smaller, AND exposing the explicit coordinate-center index set the blow-up
fires on. NO monomial weight (that is fm's blow-up). This is the `resolvedForm`. Fields carry fm's
5-point ask:
- (1 TYPE) `χ : (Fin nReg → ℝ) × (Fin N' → ℝ) ≃ₜ (Fin N → ℝ)`, `N'` the reduced ambient.
- (2 MP/det-1) `measurePreserving` — fm's glue composes through with NO Jacobian weight.
- (3 COORD-CENTER) `active : Finset (Fin N')` + pivot `p` + `centerCoord`: the rank-defect center is the
  coordinate subspace `{x | ∀ i ∈ active, x i = 0}` (the index set `g5_pivotNode` blows up).
- (4 REDUCED-CHAIN) `S.red` = M' + `flatRedCore`'s reduced-core component + `measure_drops`.
- (5 STRICT-TRANSFORM) `factor` — `flatCore ∘ χ = u · flatRedCore` near `0` (the rewrite fm's integrand
  transport uses; with the analytic unit `u`, MP-transported, no new proof). -/
structure IsSchurStraighten {L : ℕ} {N N' : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
    (nReg : ℕ)
    (flatCore : (Fin N → ℝ) → ℝ)             -- `dlnLoss M 0` in the post-blow-up flat coords
    (flatRedCore : (Fin nReg → ℝ) × ((Fin N' → ℝ)) → ℝ)  -- split target (reg block + reduced core on N')
    (redEmbed : (Fin N' → ℝ) → Params S.red)  -- the flat-embed of the reduced coords into Params M'
    (χ : ((Fin nReg → ℝ) × (Fin N' → ℝ)) ≃ₜ (Fin N → ℝ))  -- the det-1 Schur straightening chart
    (u : (Fin nReg → ℝ) × (Fin N' → ℝ) → ℝ)
    (active : Finset (Fin N')) (p : Fin N') : Prop where
  /-- (2) The straightening is MEASURE-PRESERVING (det-1, the (A) sub-step contributes no weight). -/
  measurePreserving : MeasurePreserving χ volume volume
  /-- `u` is measurable (the analytic unit). -/
  umeas : Measurable u
  /-- (4) REDUCED-CHAIN (explicit): the split target is the regular block plus the EXPLICIT reduced
  core `dlnLoss M' 0` (`M' = S.red`) on the embedded reduced coords — so fm's structural recursion
  descends on the smaller chain `S.red`, not an abstract residual. -/
  redCore_eq : ∀ q, flatRedCore q = (∑ i, q.1 i ^ 2) + dlnLoss S.red 0 (redEmbed q.2)
  /-- (5) STRICT-TRANSFORM: the det-1 normal form near the deepest point —
  `core ∘ χ = unit · (reg block + reduced core)`. -/
  factor : (fun q => flatCore (χ q)) =ᶠ[nhds 0] (fun q => u q * flatRedCore q)
  /-- (3) COORDINATE-CENTER: the pivot lies in the active set (the blow-up's center coords), so the
  rank-defect center `{q | ∀ i ∈ active, q.2 i = 0}` is a coordinate subspace `g5_pivotNode` can fire
  on. (`active`/`p` match `pivotBlowupOn`'s `(active : Finset) (p)` signature, S1G5Charts:384.) -/
  pivot_active : p ∈ active
  /-- (3) the active set is the blow-up codimension `Mval`-many center coords (nonempty: a real drop). -/
  active_nonempty : active.Nonempty
  /-- (4) Well-foundedness (pp #123 field-6): the reduced chain is strictly smaller. -/
  measure_drops : ∑ s, S.red s < ∑ s, M s

/-! ## Body sub-lemma (1): the hard-1-pivot Schur block-identity (the `(L,R)` transvections)

The #127 witness's `(L,R)` transvection pair, at the hard-1 pivot: `L = fromBlocks 1 0 (−c) 1`
(clear col 0), `R = fromBlocks 1 (−b) 0 1` (clear row 0), both UNIPOTENT (det 1), with
`L · (fromBlocks 1 b c D) · R = fromBlocks 1 0 0 (D − c·b)` — block-diagonalizing to the `1×1` regular
pivot ⊕ the reduced Schur factor `S = D − c·b`. Specializes Mathlib's `fromBlocks_eq_of_invertible₁₁`
(the LDU/Schur factorization) to `A = 1` (`⅟1 = 1`). -/
theorem hardPivot_schur_blockId {m n l : ℕ}
    (b : Matrix (Fin m) (Fin n) ℝ) (c : Matrix (Fin l) (Fin m) ℝ) (D : Matrix (Fin l) (Fin n) ℝ) :
    (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ) 0 (-c) 1)
        * (Matrix.fromBlocks 1 b c D)
        * (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ) (-b) 0 1)
      = Matrix.fromBlocks 1 0 0 (D - c * b) := by
  -- Direct double `fromBlocks_multiply`. L·A first (clear col 0), then ·R (clear row 0).
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  -- Discharge the four resulting blocks by ring/matrix algebra.
  congr 1 <;>
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.neg_mul, Matrix.mul_neg, add_zero, zero_add, Matrix.add_mul, Matrix.mul_add] <;>
    abel_nf <;>
    ring_nf

/-- **G3.2 crux — the det-1 Schur straightening, HONEST packaging form (GREEN, mine).**

The unconditional existence `∃ χ u …, IsSchurStraighten M S nReg flatCore …` for an *arbitrary*
`flatCore` is **false** (two independent obstructions, decorrelated pp/Codex 2026-06-22, controller
Decision (A) 2026-06-22 — dropped):
- (i) DIMENSION — a homeomorphism `(Fin nReg → ℝ) × (Fin N' → ℝ) ≃ₜ (Fin N → ℝ)` needs
  `N = nReg + N'` (invariance of domain); quantifying the three dims independently makes it impossible
  when `N ≠ nReg + N'`.
- (ii) CLEAN-FACTOR — `redCore_eq` pins `flatRedCore 0 = 0`, so `factor` forces `flatCore (χ 0) = 0`
  *and* a clean product factorisation `flatCore∘χ = u·(∑Eᵢ²+core)`; the design finding
  `g128-L2-seam-squeeze-bridge.md` shows that exact clean form is **NOT** reachable by a measure-
  preserving change of variables (the honest route is the two-sided SQUEEZE), so even with
  `flatCore = dlnLoss M 0` the unconditional form fails.

So the deliverable is the **packaging**: the heavy *existence* of the measure-preserving chart `χ`
realising the clean factor `flatCore∘χ =ᶠ u·(∑Eᵢ²+core)` is a separate downstream obligation (the chart-
existence content — disputed clean-MP-c-o-v vs #127 squeeze, controller reconciling); supplied here as a
hypothesis, this lemma assembles the `IsSchurStraighten` package, discharging the bookkeeping fields
(`umeas`, `redCore_eq`, `pivot_active`, `active_nonempty`, `measure_drops`) from the `ChainDimSplit` +
the supplied data. The locked `IsSchurStraighten` interface is intact; the statement is exactly what is
true. -/
theorem schur_straighten_of_data {L : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
    (nReg N N' : ℕ) (flatCore : (Fin N → ℝ) → ℝ)
    (redEmbed : (Fin N' → ℝ) → Params S.red)
    (χ : ((Fin nReg → ℝ) × (Fin N' → ℝ)) ≃ₜ (Fin N → ℝ))
    (hχmp : MeasurePreserving χ volume volume)
    (u : (Fin nReg → ℝ) × (Fin N' → ℝ) → ℝ) (humeas : Measurable u)
    (active : Finset (Fin N')) (p : Fin N') (hp : p ∈ active)
    -- the supplied clean germ-factorisation (the g128 straightening content, downstream):
    (hfactor : (fun q => flatCore (χ q)) =ᶠ[nhds 0]
        (fun q => u q * ((∑ i, q.1 i ^ 2) + dlnLoss S.red 0 (redEmbed q.2)))) :
    ∃ (flatRedCore : (Fin nReg → ℝ) × (Fin N' → ℝ) → ℝ)
      (redEmbed' : (Fin N' → ℝ) → Params S.red)
      (χ' : ((Fin nReg → ℝ) × (Fin N' → ℝ)) ≃ₜ (Fin N → ℝ))
      (u' : (Fin nReg → ℝ) × (Fin N' → ℝ) → ℝ) (active' : Finset (Fin N')) (p' : Fin N'),
      IsSchurStraighten M S nReg flatCore flatRedCore redEmbed' χ' u' active' p' := by
  refine ⟨fun q => (∑ i, q.1 i ^ 2) + dlnLoss S.red 0 (redEmbed q.2),
    redEmbed, χ, u, active, p, ?_⟩
  refine
    { measurePreserving := hχmp
      umeas := humeas
      redCore_eq := fun q => rfl
      factor := hfactor
      pivot_active := hp
      active_nonempty := ⟨p, hp⟩
      measure_drops := ?_ }
  -- ∑ S.red < ∑ M from drop + red = M with 0 < ∑ drop (the ChainDimSplit termination measure).
  have hle : ∑ s, S.red s ≤ ∑ s, M s :=
    Finset.sum_le_sum fun s _ => by have := S.hsum s; omega
  have hne : ∑ s, S.red s ≠ ∑ s, M s := by
    intro hEq
    have hdrop0 : ∑ s, S.drop s = 0 := by
      have hadd : ∑ s, S.drop s + ∑ s, S.red s = ∑ s, M s := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun s _ => S.hsum s
      omega
    exact absurd hdrop0 (by have := S.hdrops; omega)
  omega

/-! ## The G3.2 recursion step (SOUND conditional form — PROVEN)

The clean `rlctAtOn(dlnLoss M 0) 0 = nReg/2 + rlctAtOn(dlnLoss Mred 0) 0` (no chart hypothesis) is
**FALSE**: a measure-preserving recursion conserves dimension, so it would telescope to `ambient/2`
(= 4 for (2,2,2)), contradicting the verified `3/2`. (Codex-decorrelated + the dimension count;
artifacts `g32-chart-structure-answer.md`.) The general-M chart is **(C2)**: det-1 GL-straighten (=
Aoyagi's Lemma 2, measure-preserving) THEN blow-up (monomial Jacobian — the `⨅ monomialThreshold`
content). The blow-up is NOT measure-preserving, so the clean nReg/2-chain has no sound realization.

What IS sound and provable is the **CONDITIONAL recursion step on the measure-preserving STRAIGHTENING
phase**: given a measure-preserving chart `χ : (Fin nReg → ℝ) × Y ≃ₜ Params M` that factors the loss
near the deepest point as `u · ((∑ xᵢ²) + G(y)²)` (the regular smooth block + the residual `G`), the
RLCT splits as `nReg/2 + rlctAtOn(G²)`. The unit `u` is stripped by `rlctAtOn_unit_invariant_aux`; the
smooth block by `rlct_additive_smooth_block` (S1.5); the chart transport by `rlctAtOn_comp_homeomorph`
(needs the chart MEASURE-PRESERVING — the load-bearing hypothesis the straightening phase supplies).
This is the det-1 half of (C2); the blow-up half (the monomial Jacobian → `⨅ monomialThreshold`) is
fm's cover lane, applied to the residual `G`. -/

/-- **`rlctAtOn` germ-locality (general domain).** The RLCT threshold depends only on the germ of the
integrand at the base point: `F =ᶠ[𝓝 w0] G ⟹ rlctAtOn F w0 = rlctAtOn G w0`. The general-domain twin
of `rlct_germ_local` — lets the chart's `factor` germ-equality rewrite the integrand. (Controller:
home is `S1Local.lean` beside `rlctAtOn_unit_invariant_aux`.) -/
theorem rlctAtOn_germ_local {N : Type*} [MeasureSpace N] [TopologicalSpace N]
    [OpensMeasurableSpace N] (F G : N → ℝ) (w0 : N) (hFG : F =ᶠ[nhds w0] G) :
    rlctAtOn F w0 = rlctAtOn G w0 := by
  obtain ⟨U₀, hU₀mem, hU₀⟩ := Filter.eventually_iff_exists_mem.1 hFG
  unfold rlctAtOn weightedThreshold
  have key : ∀ (P Q : N → ℝ), (∀ w ∈ U₀, P w = Q w) →
      ∀ c : ENNReal, (∃ c' : NNReal, c = (c':ENNReal) ∧ ∃ Ω, IsOpen Ω ∧ {w0} ⊆ Ω ∧
          IntegrableOn (fun w => |P w| ^ (-(c':ℝ)) * (fun _ => (1:ℝ)) w) Ω volume) →
        (∃ c' : NNReal, c = (c':ENNReal) ∧ ∃ Ω, IsOpen Ω ∧ {w0} ⊆ Ω ∧
          IntegrableOn (fun w => |Q w| ^ (-(c':ℝ)) * (fun _ => (1:ℝ)) w) Ω volume) := by
    rintro P Q hPQ c ⟨c', rfl, Ω, hΩopen, hKΩ, hint⟩
    have hw0 : w0 ∈ Ω := hKΩ rfl
    obtain ⟨V, hVsub, hVopen, hwV⟩ := mem_nhds_iff.1 (Filter.inter_mem (hΩopen.mem_nhds hw0) hU₀mem)
    refine ⟨c', rfl, V, hVopen, Set.singleton_subset_iff.2 hwV, ?_⟩
    have hVΩ : V ⊆ Ω := fun x hx => (hVsub hx).1
    have hVU₀ : V ⊆ U₀ := fun x hx => (hVsub hx).2
    apply (hint.mono_set hVΩ).congr
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with w hw
    rw [hPQ w (hVU₀ hw)]
  congr 1; ext c
  exact ⟨key F G hU₀ c, key G F (fun w hw => (hU₀ w hw).symm) c⟩

/-! ## The SQUEEZE chain (pp2 #129/#130 — the CORRECTED per-node route)

pp2 #129 (decorrelated) RETRACTED the clean measure-preserving-chart route: the per-node transvection
`A ↦ L·A·R` IS det-1 / measure-preserving (`mp_schur_transvection_vec`), but the LOSS is NOT invariant
under it (`L` unipotent ⇏ orthogonal, `‖Â·A2‖² ≠ ‖L·Â·A2‖²`). #127's "clean decoupling" was a MATRIX
identity misread as a loss-VALUE identity. So the per-node `rlctAtOn` does NOT resolve by
`rlctAtOn_comp_homeomorph` (a change of variables); it resolves by the SQUEEZE (same as L2/g128): the
loss `F` is sandwiched `c₁·Φ ≤ F ≤ c₂·Φ` (c₁>0) by the smooth-block normal form `Φ`, comparing `F` and
`Φ` at the SAME point — NO chart, NO measure Jacobian. `mp_schur_transvection_vec` stays true reusable
bedrock but is OFF this path. -/

/-- **General-domain RLCT monotonicity** (the flat-domain twin of `rlctAt_mono`): if near `wstar`
`|G| ≤ |F|` and `G` vanishes only where `F` does, then `rlctAtOn G wstar ≤ rlctAtOn F wstar` — a
smaller `|·|` makes `|·|^{−c'}` larger (harder to integrate), so fewer exponents qualify. The
`G=0→F=0` clause makes the domination pointwise (no a.e./null-set); `Measurable F` is the one analytic
hypothesis. Ports `rlctAt_mono`'s `sSup_le_sSup` argument to a general `MeasureSpace`. -/
theorem rlctAtOn_mono {M : Type*} [MeasureSpace M] [TopologicalSpace M] [OpensMeasurableSpace M]
    (F G : M → ℝ) (wstar : M) (hFmeas : Measurable F)
    (hdom : ∃ U ∈ nhds wstar, ∀ w ∈ U, |G w| ≤ |F w| ∧ (G w = 0 → F w = 0)) :
    rlctAtOn G wstar ≤ rlctAtOn F wstar := by
  unfold rlctAtOn weightedThreshold
  apply sSup_le_sSup
  rintro c ⟨c', rfl, Ω, hΩopen, hKΩ, hint⟩
  obtain ⟨V, hV, hVdom⟩ := hdom
  obtain ⟨W, hWV, hWopen, hwW⟩ := mem_nhds_iff.mp hV
  have hwΩ : wstar ∈ Ω := hKΩ rfl
  refine ⟨c', rfl, Ω ∩ W, hΩopen.inter hWopen, Set.singleton_subset_iff.2 ⟨hwΩ, hwW⟩, ?_⟩
  have hmeasF : AEStronglyMeasurable (fun w => |F w| ^ (-(c' : ℝ)) * (1 : ℝ))
      (volume.restrict (Ω ∩ W)) :=
    ((((continuous_abs.measurable).comp hFmeas).pow_const _).mul_const _).aestronglyMeasurable
  apply MeasureTheory.Integrable.mono (hint.mono_set Set.inter_subset_left) hmeasF
  have hΩW_meas : MeasurableSet (Ω ∩ W) := (hΩopen.inter hWopen).measurableSet
  refine (ae_restrict_iff' hΩW_meas).mpr ?_
  filter_upwards with w hw
  have hd := hVdom w (hWV hw.2)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_one, mul_one, mul_one,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact abs_rpow_neg_mono (F w) (G w) c' c'.2 hd.1 hd.2

/-- **The SQUEEZE RLCT-equality** (the g128 chain front): if `F, Φ ≥ 0` near `wstar`, both measurable,
and `c₁·Φ ≤ F ≤ c₂·Φ` with `0 < c₁`, `0 < c₂`, then `rlctAtOn F wstar = rlctAtOn Φ wstar`. The
constant multiples `c₁, c₂` are positive units stripped by `rlctAtOn_unit_invariant_aux`; the two
inequalities give `rlctAtOn_mono` both ways (the `F=0 ⟺ Φ=0` vanishing from the two-sided bound with
`c₁,c₂>0`). NO change of variables, NO measure Jacobian — `F` and `Φ` compared at the SAME point. -/
theorem rlctAtOn_squeeze {M : Type*} [MeasureSpace M] [TopologicalSpace M] [OpensMeasurableSpace M]
    (F Φ : M → ℝ) (wstar : M) (hFmeas : Measurable F) (hΦmeas : Measurable Φ)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hsq : ∃ U ∈ nhds wstar, ∀ w ∈ U, 0 ≤ Φ w ∧ c₁ * Φ w ≤ F w ∧ F w ≤ c₂ * Φ w) :
    rlctAtOn F wstar = rlctAtOn Φ wstar := by
  obtain ⟨U, hU, hbnd⟩ := hsq
  refine le_antisymm ?_ ?_
  · rw [show rlctAtOn Φ wstar = rlctAtOn (fun w => c₂ * Φ w) wstar from
      (rlctAtOn_unit_invariant_aux Φ (fun _ => c₂) wstar c₂ c₂ hc₂ (by fun_prop)
        ⟨U, hU, fun w _ => by rw [abs_of_pos hc₂]; exact ⟨le_refl _, le_refl _⟩⟩).symm]
    refine rlctAtOn_mono (fun w => c₂ * Φ w) F wstar (by fun_prop) ⟨U, hU, fun w hw => ?_⟩
    obtain ⟨hΦ, hlo, hhi⟩ := hbnd w hw
    have hF0 : 0 ≤ F w := le_trans (mul_nonneg hc₁.le hΦ) hlo
    refine ⟨?_, fun hFeq => ?_⟩
    · rw [abs_of_nonneg hF0, abs_of_nonneg (mul_nonneg hc₂.le hΦ)]; exact hhi
    · show c₂ * Φ w = 0
      have hΦ0 : Φ w = 0 := le_antisymm (by nlinarith [hFeq ▸ hlo]) hΦ
      rw [hΦ0, mul_zero]
  · rw [show rlctAtOn Φ wstar = rlctAtOn (fun w => c₁ * Φ w) wstar from
      (rlctAtOn_unit_invariant_aux Φ (fun _ => c₁) wstar c₁ c₁ hc₁ (by fun_prop)
        ⟨U, hU, fun w _ => by rw [abs_of_pos hc₁]; exact ⟨le_refl _, le_refl _⟩⟩).symm]
    refine rlctAtOn_mono F (fun w => c₁ * Φ w) wstar hFmeas ⟨U, hU, fun w hw => ?_⟩
    obtain ⟨hΦ, hlo, hhi⟩ := hbnd w hw
    have hF0 : 0 ≤ F w := le_trans (mul_nonneg hc₁.le hΦ) hlo
    refine ⟨?_, fun hcF0 => ?_⟩
    · rw [abs_of_nonneg (mul_nonneg hc₁.le hΦ), abs_of_nonneg hF0]; exact hlo
    · have hΦ0 : Φ w = 0 := by
        rcases mul_eq_zero.1 hcF0 with h | h
        · exact absurd h (ne_of_gt hc₁)
        · exact h
      nlinarith [hhi, hΦ0]

/-- The smooth-block normal form on the chart source: `(∑ regular coords²) + G(residual)²`. -/
noncomputable def smoothBlockSplitForm {nReg : ℕ} {Y : Type*} (G : Y → ℝ) :
    (Fin nReg → ℝ) × Y → ℝ := fun p => (∑ i, p.1 i ^ 2) + G p.2 ^ 2

/-- **G3.2 recursion step (SOUND conditional, PROVEN).** On the measure-preserving STRAIGHTENING
phase: given a measure-preserving chart `χ` factoring the loss near the deepest point as
`u · ((∑ xᵢ²) + G²)` (`hfactor`), with `u` a measurable unit bounded in `[a,b]` (`a>0`, `hu`) and `G`
measurable + germ-nonvanishing (`hGne`, the `≠0`-a.e. discipline; holds at NON-LEAF nodes — the leaf
is `dlnLoss_one_layer_deepest`, not this step), the RLCT splits:
`rlctAtOn (dlnLoss M 0) (χ 0) = nReg/2 + rlctAtOn (G²) 0`. Transport (`rlctAtOn_comp_homeomorph`,
needs `χ` measure-preserving) → germ-rewrite (`rlctAtOn_germ_local`) → unit-strip
(`rlctAtOn_unit_invariant_aux`) → smooth-block split (`rlct_additive_smooth_block`, S1.5). The det-1
half of (C2); the blow-up half (residual `G` → `⨅ monomialThreshold`) is fm's cover lane. -/
theorem schur_recursion_step_sound {L : ℕ} (M : Fin (L + 1) → ℕ) (nReg : ℕ)
    {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y] [OpensMeasurableSpace Y]
    [Zero Y]
    (chart : ((Fin nReg → ℝ) × Y) ≃ₜ Params M)
    (hmp : MeasurePreserving chart volume volume) (hemb : MeasurableEmbedding chart)
    (u : (Fin nReg → ℝ) × Y → ℝ) (humeas : Measurable u)
    (G : Y → ℝ) (hGmeas : Measurable G)
    (hGne : ∃ U ∈ nhds (0 : Y), ∀ᵐ z ∂(volume.restrict U), G z ≠ 0)
    (a b : ℝ) (ha : 0 < a)
    (hu : ∃ U ∈ nhds ((0, 0) : (Fin nReg → ℝ) × Y), ∀ w ∈ U, a ≤ |u w| ∧ |u w| ≤ b)
    (hfactor : (fun p => dlnLoss M 0 (chart p)) =ᶠ[nhds ((0, 0) : (Fin nReg → ℝ) × Y)]
        (fun p => u p * smoothBlockSplitForm G p)) :
    rlctAtOn (dlnLoss M 0) (chart (0, 0))
      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) := by
  rw [← rlctAtOn_comp_homeomorph chart hmp hemb (dlnLoss M 0) (0, 0)]
  rw [rlctAtOn_germ_local _ (fun p => u p * smoothBlockSplitForm G p) _ hfactor]
  rw [rlctAtOn_unit_invariant_aux (smoothBlockSplitForm G) u (0, 0) a b ha humeas hu]
  exact rlct_additive_smooth_block G 0 hGmeas hGne

/-- **G3.2 recursion step — the SQUEEZE form (PROVEN, the CORRECTED per-node route, pp2 #129/#130).**
At the deepest point `(0,0)`, the per-node core `flatCore` is SQUEEZED by the smooth-block normal form
`Φ = (∑ Eᵢ²) + G²`: `c₁·Φ ≤ flatCore ≤ c₂·Φ` near `(0,0)` with `0 < c₁`, `0 < c₂` (`hsq`), with `G`
measurable + germ-nonvanishing (`hGne`). Then the RLCT splits:
`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0`. Chain: `rlctAtOn_squeeze` (the two-sided
`rlctAtOn_mono` + positive-unit strip — NO chart, NO measure Jacobian) → `rlct_additive_smooth_block`
(S1.5). This REPLACES `schur_recursion_step_sound`'s measure-preserving-chart front (retracted: the
transvection is MP but the loss is not invariant under it); the tail (S1.5 split) is shared. The
squeeze inequality `hsq` rests on `flatCore − Φ ∈ ideal(regular gens)` (the Schur identity as
ideal-membership; pp2 certifies the general `m×k` node — supplied to `hsq`'s producer downstream). -/
theorem schur_recursion_step_squeeze {nReg : ℕ}
    {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y] [OpensMeasurableSpace Y]
    [Zero Y]
    (flatCore : (Fin nReg → ℝ) × Y → ℝ) (hFmeas : Measurable flatCore)
    (G : Y → ℝ) (hGmeas : Measurable G)
    (hGne : ∃ U ∈ nhds (0 : Y), ∀ᵐ z ∂(volume.restrict U), G z ≠ 0)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hsq : ∃ U ∈ nhds ((0, 0) : (Fin nReg → ℝ) × Y), ∀ w ∈ U,
        0 ≤ smoothBlockSplitForm G w ∧ c₁ * smoothBlockSplitForm G w ≤ flatCore w
          ∧ flatCore w ≤ c₂ * smoothBlockSplitForm G w) :
    rlctAtOn flatCore ((0, 0) : (Fin nReg → ℝ) × Y)
      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) := by
  have hΦmeas : Measurable (smoothBlockSplitForm (nReg := nReg) G) := by
    unfold smoothBlockSplitForm
    exact (Finset.measurable_sum _ (fun i _ =>
      (measurable_pi_apply i |>.comp measurable_fst).pow_const _)).add
        ((hGmeas.comp measurable_snd).pow_const _)
  rw [rlctAtOn_squeeze flatCore (smoothBlockSplitForm G) _ hFmeas hΦmeas c₁ c₂ hc₁ hc₂ hsq]
  exact rlct_additive_smooth_block G 0 hGmeas hGne

/-! ## The CORRECTED per-node datum — `IsSchurStraightenSqueeze` (pp2 #129/#130, controller-blessed)

The faithful per-node straightening datum, replacing the retracted `IsSchurStraighten` (clean MP factor).
pp2 #129 retracted the clean change-of-variables route (the transvection is det-1/MP but the loss is not
invariant under it); pp2 #130 read off the two transport pins the faithful datum needs. In the SQUEEZE
form both pins are met by construction:
- **(i) anchor at the deepest point** (`χ 0 = 0` in #130's chart language): the squeeze compares
  `flatCore` and `Φ` at the SAME point, and the rlct is taken AT that point `(0,0)` — so the basepoint IS
  the deepest point. No chart map; the anchor is the basepoint of `rlctAtOn … (0,0)`.
- **(ii) genuine unit, bounded away from 0**: the unit role is played by the positive squeeze constants
  `c₁, c₂` (`0 < c₁`, `0 < c₂`) — bounded away from `0` by construction, exactly what
  `rlctAtOn_unit_invariant_aux`'s `a > 0` needs. NOT an abstract `Measurable u` (which could vanish).
- **Φ** `= (nReg unit-coeff regular squares) + dlnLoss S.red 0` (the reduced-chain core), via
  `G² = dlnLoss S.red 0` (`G = √`, valid by `dlnLoss_nonneg`).
- The squeeze inequality rests on `flatCore − Φ ∈ ideal(regular gens)` (the Schur identity as
  ideal-membership) — the EXISTENCE-proof obligation (pp2 #11), NOT a field: the datum carries the
  squeeze inequality the recursion step consumes. -/
structure IsSchurStraightenSqueeze {L : ℕ} {nReg : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
    {Y : Type*} [MeasureSpace Y] [TopologicalSpace Y] [Zero Y]
    (flatCore : (Fin nReg → ℝ) × Y → ℝ)       -- the post-blow-up per-node core at the deepest point
    (G : Y → ℝ)                                -- the reduced-chain core (`G² = dlnLoss S.red 0`)
    (redEmbed : Y → Params S.red)              -- the reduced coords ↪ `Params S.red`
    (c₁ c₂ : ℝ) : Prop where
  /-- The per-node core is measurable (polynomial loss). -/
  Fmeas : Measurable flatCore
  /-- The reduced core `G` is measurable. -/
  Gmeas : Measurable G
  /-- (Φ) The reduced part of `Φ` is the reduced-chain loss: `G² = dlnLoss S.red 0` on the embedded
  reduced coords — so the structural recursion descends on the smaller chain `S.red`. -/
  redCore_eq : ∀ y, G y ^ 2 = dlnLoss S.red 0 (redEmbed y)
  /-- Germ-nonvanishing of `G` at the reduced origin (the S1.5 hygiene; the non-leaf node). -/
  Gne : ∃ U ∈ nhds (0 : Y), ∀ᵐ z ∂(volume.restrict U), G z ≠ 0
  /-- (ii) lower squeeze constant is a genuine unit (`> 0`): bounds the loss away from `0·Φ`. -/
  c₁pos : 0 < c₁
  /-- (ii) upper squeeze constant is positive. -/
  c₂pos : 0 < c₂
  /-- (i)+(ii) THE SQUEEZE at the deepest point `(0,0)`: `c₁·Φ ≤ flatCore ≤ c₂·Φ` near `(0,0)`,
  `Φ = smoothBlockSplitForm G = (∑ Eᵢ²) + G²`. The anchor `(0,0)` is the deepest point (#130 (i)); the
  constants `c₁,c₂` are the genuine units (#130 (ii)). NO change of variables, NO measure Jacobian. -/
  squeeze : ∃ U ∈ nhds ((0, 0) : (Fin nReg → ℝ) × Y), ∀ w ∈ U,
      0 ≤ smoothBlockSplitForm G w ∧ c₁ * smoothBlockSplitForm G w ≤ flatCore w
        ∧ flatCore w ≤ c₂ * smoothBlockSplitForm G w
  /-- Well-foundedness (pp #123): the reduced chain is strictly smaller. -/
  measure_drops : ∑ s, S.red s < ∑ s, M s

/-- **The CORRECTED per-node rlct split (PROVEN), from the squeeze datum.** Given the
`IsSchurStraightenSqueeze` datum, the per-node RLCT at the deepest point splits as
`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0` — the regular smooth block plus the reduced-chain
core. Consumes the datum's squeeze + measurability + germ-nonvanishing via `schur_recursion_step_squeeze`
(the g128/L2 chain: `rlctAtOn_squeeze` + `rlct_additive_smooth_block`). The recursion step the structural
recursion descends on; the reduced core `G² = dlnLoss S.red 0` is the smaller-chain loss. -/
theorem schur_straighten_squeeze_of_data {L : ℕ} {nReg : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
    {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y] [OpensMeasurableSpace Y] [Zero Y]
    (flatCore : (Fin nReg → ℝ) × Y → ℝ) (G : Y → ℝ) (redEmbed : Y → Params S.red) (c₁ c₂ : ℝ)
    (h : IsSchurStraightenSqueeze M S flatCore G redEmbed c₁ c₂) :
    rlctAtOn flatCore ((0, 0) : (Fin nReg → ℝ) × Y)
      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) :=
  schur_recursion_step_squeeze flatCore h.Fmeas G h.Gmeas h.Gne c₁ c₂ h.c₁pos h.c₂pos h.squeeze

/-! ## The g131 existence-proof content — `flatCore − Φ ∈ ideal(E)` (the squeeze's WHY, pp2 #131)

The per-node squeeze `c₁·Φ ≤ flatCore ≤ c₂·Φ` (the `squeeze` field) is PRODUCED by the structural fact
`flatCore − Φ ∈ ideal(E)` (the regular pivot-row generators), certified dimension-free in pp2 #131
(decorrelated, Codex-confirmed). The math is a single hard-pivot Schur elimination — read NOT as a
loss-value identity (false, #129) but as the **row decomposition** of the product matrix. The two
algebraic cores, formalised here as reusable matrix-level bedrock:

(1) `schur_row_decomp` — the Schur row-decomposition: with the post-blow-up hard pivot (pivot block `= 1`),
    the lower rows of `Â·A2` are `lower = b·E_row + S·A2red`, `S = D − b·a` the Schur complement,
    `E_row` the pivot-row product, `b = Â[1:,0]`.
(2) `schur_lossDiff_mem_ideal` — hence the Frobenius-loss difference `‖lower‖² − ‖S·A2red‖²` is a
    cofactor sum `Σⱼ Eⱼ·gⱼ`, so `flatCore − Φ ∈ Ideal.span (range E)`.

Together these are the certified existence content #131 hands the squeeze: the same-zero-set + the
structural `c₁>0` (bounded-linear-perturbation) then give the `squeeze` field. The remaining analytic
constant-existence (`c₁>0` on shrinking balls) and the `dlnLoss M 0` blow-up-coordinate assembly are the
producer that feeds `IsSchurStraightenSqueeze.squeeze`. -/

/-- **(1) The g131 Schur row-decomposition** (the `L·A·R = blockdiag` content as a ROW identity, #131).
With the post-blow-up hard pivot (pivot block `= 1`), the lower rows of the product `Â·A2` decompose as
`b·E_row + S·A2red`: `E_row = 1·β + a·Γ` the pivot-row product, `b = Â[1:,0]` the pivot column,
`S = D − b·a` the Schur complement, `A2red = Γ`. A pure `CommRing` matrix identity (block algebra). -/
theorem schur_row_decomp {p m k n : Type*} [Fintype p] [Fintype k] [Fintype m] [DecidableEq p]
    {R : Type*} [CommRing R] (a : Matrix p k R) (b : Matrix m p R) (D : Matrix m k R)
    (β : Matrix p n R) (Γ : Matrix k n R) :
    b * β + D * Γ = b * ((1 : Matrix p p R) * β + a * Γ) + (D - b * a) * Γ := by
  rw [Matrix.one_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- **(2) The g131 loss-difference is a cofactor sum** (entrywise Frobenius, #131). The
sum-of-squares difference `‖lower‖² − ‖S·A2red‖²`, with `lower = bErow + SΓ` (the row decomposition),
equals `Σᵢⱼ (bErow)ᵢⱼ·((bErow)ᵢⱼ + 2(SΓ)ᵢⱼ)` — every term carries a pivot-row factor `bErow`, the
algebraic root of `flatCore − Φ ∈ ideal(E)`. -/
theorem schur_lossDiff_eq_cofactor {m n : Type*} [Fintype m] [Fintype n] {R : Type*} [CommRing R]
    (bErow SΓ : Matrix m n R) :
    (∑ i, ∑ j, (bErow i j + SΓ i j) ^ 2) - (∑ i, ∑ j, (SΓ i j) ^ 2)
      = ∑ i, ∑ j, (bErow i j) * (bErow i j + 2 * SΓ i j) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **(3) Ideal-membership from a cofactor sum** (#131). If `flatCore − Φ = Σⱼ Eⱼ·gⱼ` (the cofactors
`gⱼ` exposed by `schur_lossDiff_eq_cofactor` after regrouping by the pivot-row generator `Eⱼ`), then
`flatCore − Φ ∈ Ideal.span (range E)`. The structural fact that PRODUCES the squeeze (#129/#131). -/
theorem schur_lossDiff_mem_ideal {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]
    (flatCore Φ : R) (E g : ι → R) (hFΦ : flatCore - Φ = ∑ j, E j * g j) :
    flatCore - Φ ∈ Ideal.span (Set.range E) := by
  rw [hFΦ]
  exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- **(4) The squeeze-constant bounds** (the analytic core of the squeeze, #131, blow-up-coord-free).
`F = (∑ Eᵢ²) + ∑ⱼ (pⱼ + sⱼ)²` is squeezed by `Φ = (∑ Eᵢ²) + ∑ⱼ sⱼ²` whenever the linear perturbation
`p` (`= b·E_row`) is small relative to `E`: `∑ pⱼ² ≤ t²·∑ Eᵢ²`. Then `Φ ≤ 2(1+t²)·F` (⟹ the lower
squeeze constant `c₁ = (2(1+t²))⁻¹ > 0`, the STRUCTURAL `c₁>0`) and `F ≤ (2+2t²)·Φ` (⟹ `c₂ = 2+2t²`).
Summed Young inequalities; `t = sup‖b‖ → 0` at the deepest point gives `c₁ → ½`, `c₂ → 2`. This is the
bounded-linear-perturbation estimate that PRODUCES the `IsSchurStraightenSqueeze.squeeze` field; the
`dlnLoss M 0` ⟹ block-`(Â,A2)` blow-up-coordinate assembly (with `p = b·E_row`, `t = ‖b‖`) is the
remaining producer step (couples to the blow-up lane). -/
theorem squeeze_bounds_abstract {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → ℝ) (p s : κ → ℝ) (t : ℝ)
    (hp : (∑ j, (p j) ^ 2) ≤ t ^ 2 * (∑ i, (E i) ^ 2)) :
    ((∑ i, (E i) ^ 2) + (∑ j, (s j) ^ 2))
        ≤ (2 * (1 + t ^ 2)) * ((∑ i, (E i) ^ 2) + (∑ j, (p j + s j) ^ 2))
    ∧ ((∑ i, (E i) ^ 2) + (∑ j, (p j + s j) ^ 2))
        ≤ (2 + 2 * t ^ 2) * ((∑ i, (E i) ^ 2) + (∑ j, (s j) ^ 2)) := by
  set A := ∑ i, (E i) ^ 2
  set P := ∑ j, (p j) ^ 2
  set C := ∑ j, (s j) ^ 2
  set B := ∑ j, (p j + s j) ^ 2
  have hAnn : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hCnn : 0 ≤ C := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have htsq : 0 ≤ t ^ 2 := sq_nonneg t
  have hBup : B ≤ 2 * P + 2 * C := by
    show (∑ j, (p j + s j) ^ 2) ≤ 2 * (∑ j, (p j) ^ 2) + 2 * (∑ j, (s j) ^ 2)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => by nlinarith [sq_nonneg (p j - s j)])
  have hCup : C ≤ 2 * B + 2 * P := by
    show (∑ j, (s j) ^ 2) ≤ 2 * (∑ j, (p j + s j) ^ 2) + 2 * (∑ j, (p j) ^ 2)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => by nlinarith [sq_nonneg (s j + 2 * (p j))])
  refine ⟨?_, ?_⟩
  · have h1 : A + C ≤ (1 + 2 * t ^ 2) * A + 2 * B := by nlinarith [hCup, hp]
    nlinarith [h1, hAnn, hBnn, htsq, mul_nonneg htsq hBnn]
  · have h2 : A + B ≤ (1 + 2 * t ^ 2) * A + 2 * C := by nlinarith [hBup, hp]
    nlinarith [h2, hAnn, htsq, mul_nonneg htsq hCnn]

/-- **The node-level squeeze** (g131, the per-node existence core). The hard-pivot Schur node loss
`F = (∑ⱼ Erowⱼ²) + ∑ᵢⱼ (bᵢ·Erowⱼ + (S·Γ)ᵢⱼ)²` (`Erow` = pivot-row product, `lower = b·Erow + S·Γ` by
`schur_row_decomp`) is squeezed by `Φ = (∑ⱼ Erowⱼ²) + ‖S·Γ‖²` with `t = ‖b‖` (`b` = pivot column):
`Φ ≤ 2(1+t²)·F` and `F ≤ (2+2t²)·Φ`. The `hp` bound is an EQUALITY `∑ᵢⱼ (bᵢ Erowⱼ)² = ‖b‖²·∑ⱼ Erowⱼ²`
(reindexed over `M × n`), so `squeeze_bounds_abstract` applies directly. The squeeze constants
`c₁ = (2(1+t²))⁻¹ > 0`, `c₂ = 2+2t²`. This is the pointwise content of the
`IsSchurStraightenSqueeze.squeeze` field; `t = ‖b‖ → 0` at the deepest point gives `c₁ → ½`. -/
theorem schur_node_squeeze {M n : Type*} [Fintype M] [Fintype n]
    (Erow : n → ℝ) (b : M → ℝ) (SΓ : M → n → ℝ) :
    ((∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (SΓ i j) ^ 2))
        ≤ (2 * (1 + (Real.sqrt (∑ i, (b i) ^ 2)) ^ 2))
            * ((∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (b i * Erow j + SΓ i j) ^ 2))
    ∧ ((∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (b i * Erow j + SΓ i j) ^ 2))
        ≤ (2 + 2 * (Real.sqrt (∑ i, (b i) ^ 2)) ^ 2)
            * ((∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (SΓ i j) ^ 2)) := by
  set t := Real.sqrt (∑ i, (b i) ^ 2) with ht
  have key := squeeze_bounds_abstract (ι := n) (κ := M × n) Erow
    (fun p => b p.1 * Erow p.2) (fun p => SΓ p.1 p.2) t ?_
  · have hΦ : (∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (SΓ i j) ^ 2)
        = (∑ j, (Erow j) ^ 2) + (∑ p : M × n, (SΓ p.1 p.2) ^ 2) := by
      rw [Fintype.sum_prod_type]
    have hF : (∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (b i * Erow j + SΓ i j) ^ 2)
        = (∑ j, (Erow j) ^ 2) + (∑ p : M × n, (b p.1 * Erow p.2 + SΓ p.1 p.2) ^ 2) := by
      rw [Fintype.sum_prod_type]
    rw [hΦ, hF]; exact key
  · have ht2 : t ^ 2 = ∑ i, (b i) ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    rw [ht2, Fintype.sum_prod_type, Finset.sum_mul]
    refine le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **The node squeeze with UNIFORM constants** (the datum-usable form). If the pivot column is bounded
`∑ᵢ bᵢ² ≤ T²` (which holds on a neighborhood of the deepest point, where `b → 0`), the node squeeze
holds with FIXED constants `c₁ = (2(1+T²))⁻¹ > 0`, `c₂ = 2+2T²` — independent of the point, as the
`IsSchurStraightenSqueeze.squeeze` field demands. Monotone-in-`t` strengthening of `schur_node_squeeze`
(`t² = ‖b‖² ≤ T²`). At the deepest point `T → 0` gives `c₁ → ½`, `c₂ → 2`. -/
theorem schur_node_squeeze_unif {M n : Type*} [Fintype M] [Fintype n]
    (Erow : n → ℝ) (b : M → ℝ) (SΓ : M → n → ℝ) (T : ℝ) (hT : (∑ i, (b i) ^ 2) ≤ T ^ 2) :
    (1 / (2 * (1 + T ^ 2))) * ((∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (SΓ i j) ^ 2))
        ≤ (∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (b i * Erow j + SΓ i j) ^ 2)
    ∧ (∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (b i * Erow j + SΓ i j) ^ 2)
        ≤ (2 + 2 * T ^ 2) * ((∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (SΓ i j) ^ 2)) := by
  obtain ⟨hlo, hhi⟩ := schur_node_squeeze Erow b SΓ
  set Φ := (∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (SΓ i j) ^ 2) with hΦdef
  set F := (∑ j, (Erow j) ^ 2) + (∑ i, ∑ j, (b i * Erow j + SΓ i j) ^ 2) with hFdef
  set t := Real.sqrt (∑ i, (b i) ^ 2) with ht
  have ht2 : t ^ 2 = ∑ i, (b i) ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have htT : t ^ 2 ≤ T ^ 2 := ht2 ▸ hT
  have hΦnn : 0 ≤ Φ := by
    rw [hΦdef]; exact add_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  have hFnn : 0 ≤ F := by
    rw [hFdef]; exact add_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  have hden : (0 : ℝ) < 2 * (1 + T ^ 2) := by positivity
  refine ⟨?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [hlo, hFnn, htT]
  · calc F ≤ (2 + 2 * t ^ 2) * Φ := hhi
      _ ≤ (2 + 2 * T ^ 2) * Φ := by nlinarith [hΦnn, htT]

/-- **The per-node existence — `schur_straighten_squeeze_exists` (PROVEN, closes the per-node lane).**
At the post-blow-up 2-factor Schur node, the `IsSchurStraightenSqueeze` datum EXISTS (with explicit
constants `c₁ = (2(1+T²))⁻¹ > 0`, `c₂ = 2+2T²`). The blow-up lane's job — presenting the node loss in
Schur form near the deepest point with a bounded pivot column — enters as the EXPLICIT interface
hypothesis `hnode` (per Codex g132: the `flatCore = ‖Â·A2‖²` coordinate layout is the blow-up (B)-lane
contract, supplied here as a hypothesis, NOT asserted as `dlnLoss M 0 coords = ‖Â·A2‖²` which would
smuggle guessed plumbing). Given that presentation (`flatCore w = ∑ Erowⱼ² + ‖b·Erow + S·Γ‖²`,
`G(w.2)² = ‖S·Γ‖²`, `‖b‖² ≤ T²` on a nbhd), the datum's `squeeze` field is `schur_node_squeeze_unif`;
the rest are the supplied measurability / reduced-core / germ / well-foundedness contracts. This is the
g131-certified existence content transcribed to Lean — the squeeze, not a clean MP factor (#129). -/
theorem schur_straighten_squeeze_exists {L nReg : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
    {Y : Type*} [MeasureSpace Y] [TopologicalSpace Y] [Zero Y]
    {Mblk : Type*} [Fintype Mblk]
    (flatCore : (Fin nReg → ℝ) × Y → ℝ) (G : Y → ℝ) (redEmbed : Y → Params S.red) (T : ℝ)
    (bcol : (Fin nReg → ℝ) × Y → Mblk → ℝ)
    (SΓ : (Fin nReg → ℝ) × Y → Mblk → Fin nReg → ℝ)
    (hFmeas : Measurable flatCore) (hGmeas : Measurable G)
    (hredCore : ∀ y, G y ^ 2 = dlnLoss S.red 0 (redEmbed y))
    (hGne : ∃ U ∈ nhds (0 : Y), ∀ᵐ z ∂(volume.restrict U), G z ≠ 0)
    (hdrop : ∑ s, S.red s < ∑ s, M s)
    (hnode : ∃ U ∈ nhds ((0, 0) : (Fin nReg → ℝ) × Y), ∀ w ∈ U,
        flatCore w = (∑ j, (w.1 j) ^ 2) + (∑ i, ∑ j, (bcol w i * w.1 j + SΓ w i j) ^ 2)
        ∧ G w.2 ^ 2 = (∑ i, ∑ j, (SΓ w i j) ^ 2)
        ∧ (∑ i, (bcol w i) ^ 2) ≤ T ^ 2) :
    ∃ c₁ c₂, IsSchurStraightenSqueeze M S flatCore G redEmbed c₁ c₂ := by
  refine ⟨1 / (2 * (1 + T ^ 2)), 2 + 2 * T ^ 2, ?_⟩
  obtain ⟨U, hU, hpres⟩ := hnode
  refine
    { Fmeas := hFmeas
      Gmeas := hGmeas
      redCore_eq := hredCore
      Gne := hGne
      c₁pos := by positivity
      c₂pos := by positivity
      measure_drops := hdrop
      squeeze := ⟨U, hU, fun w hw => ?_⟩ }
  obtain ⟨hflat, hGsq, hbT⟩ := hpres w hw
  have hΦ : smoothBlockSplitForm G w = (∑ j, (w.1 j) ^ 2) + (∑ i, ∑ j, (SΓ w i j) ^ 2) := by
    simp only [smoothBlockSplitForm]; rw [hGsq]
  obtain ⟨hlo, hhi⟩ := schur_node_squeeze_unif (w.1) (bcol w) (SΓ w) T hbT
  exact ⟨by rw [hΦ]; positivity, by rw [hΦ, hflat]; exact hlo, by rw [hΦ, hflat]; exact hhi⟩

/-- **The reduced-chain RLCT-transport** (closes rv3's FLAG-A — the recursion-CLOSING link). The datum's
`redCore_eq` is a POINTWISE pullback `G y² = dlnLoss S.red 0 (redEmbed y)`; alone it does NOT give
`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) …`. This supplies the transport: if `redEmbed` is a
measure-preserving homeomorphism `Y ≃ₜ Params S.red` anchored (`redEmbed 0 = redZero`), then
`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) redZero` (`rlctAtOn_comp_homeomorph`). The basepoint
`redZero` is passed EXPLICITLY (`Params` has no canonical `Zero`; the reduced deepest point is named by
the producer). The recursion-assembly step discharges this with the datum to descend the RLCT. -/
theorem rlctAtOn_reduced_transport {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M)
    {Y : Type*} [MeasureSpace Y] [TopologicalSpace Y] [Zero Y]
    (G : Y → ℝ) (redEmbed : Y ≃ₜ Params S.red)
    (hmp : MeasurePreserving redEmbed volume volume) (hemb : MeasurableEmbedding redEmbed)
    (redZero : Params S.red) (hzero : redEmbed 0 = redZero)
    (hredCore : ∀ y, G y ^ 2 = dlnLoss S.red 0 (redEmbed y)) :
    rlctAtOn (fun y => G y ^ 2) (0 : Y) = rlctAtOn (dlnLoss S.red 0) redZero := by
  have hpull : (fun y => G y ^ 2) = (fun y => dlnLoss S.red 0 (redEmbed y)) := by
    funext y; exact hredCore y
  rw [hpull, rlctAtOn_comp_homeomorph redEmbed hmp hemb (dlnLoss S.red 0) 0, hzero]

/-- **The bundled per-cell reduced-transport datum** (fm3's `RouteStep.branch` field; sibling to the
value-side `PivotWitness`). Carries the det-1 MP reindex from a post-blow-up reduced ambient `Y` to
`Params S.red`, with the node core presented as `G²`. The recursion's RLCT-descent link: the consuming
`ReducedTransport.transport` (below) gives `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) redZero`, so the
fold descends to the child `S.red`. `Type`-valued (it carries `Y` + instances); the transport content is
the `Prop` extracted by `.transport`. The producer (the blow-up chart) names `Y`/`redEmbed`/`redZero`;
when the blow-up lands the reduced core ON `Params S.red` directly, take `Y = Params S.red`,
`redEmbed = Homeomorph.refl`, `redZero = 0` (the `ofRefl` smart-ctor below). -/
structure ReducedTransport {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M) : Type 1 where
  /-- The post-blow-up reduced ambient (a measurable topological space with a basepoint). -/
  Y : Type
  [meas : MeasureSpace Y]
  [top : TopologicalSpace Y]
  [zero : Zero Y]
  /-- The node core presented on `Y` (the residual whose square is the reduced loss). -/
  G : Y → ℝ
  /-- The det-1 MP homeomorphic reindex `Y ≃ₜ Params S.red`. -/
  redEmbed : Y ≃ₜ Params S.red
  /-- `redEmbed` is measure-preserving (det = 1 — no Jacobian weight). -/
  hmp : MeasurePreserving redEmbed volume volume
  /-- `redEmbed` is a measurable embedding (for the change-of-variables). -/
  hemb : MeasurableEmbedding redEmbed
  /-- The child recursion's basepoint in `Params S.red` (named explicitly — `Params` has no canonical
  `Zero`; the dispatcher READS this as the child's deepest point). -/
  redZero : Params S.red
  /-- `redEmbed` is anchored at the basepoints. -/
  hzero : redEmbed 0 = redZero
  /-- The node core pulls back to the reduced-chain loss: `G y² = dlnLoss S.red 0 (redEmbed y)`. -/
  hredCore : ∀ y, G y ^ 2 = dlnLoss S.red 0 (redEmbed y)

attribute [instance] ReducedTransport.meas ReducedTransport.top ReducedTransport.zero

/-- **The RLCT-descent link from a `ReducedTransport`** (the consuming lemma — the `Prop` content).
`rlctAtOn (rt.G ·²) 0 = rlctAtOn (dlnLoss S.red 0) rt.redZero` — the per-cell transport that closes the
recursion onto the child `S.red`. Just `rlctAtOn_reduced_transport` applied to the bundle's fields. -/
theorem ReducedTransport.transport {L : ℕ} {M : Fin (L + 1) → ℕ} {S : ChainDimSplit M}
    (rt : ReducedTransport S) :
    rlctAtOn (fun y => rt.G y ^ 2) (0 : rt.Y) = rlctAtOn (dlnLoss S.red 0) rt.redZero :=
  rlctAtOn_reduced_transport S rt.G rt.redEmbed rt.hmp rt.hemb rt.redZero rt.hzero rt.hredCore

/-! **Collapse case (fm3's design-Q (i)).** When the post-blow-up reduced ambient IS `Params S.red`
(no genuine reindex), instantiate `ReducedTransport` directly with `Y := Params S.red`,
`redEmbed := Homeomorph.refl _`, `redZero := (0 : Params S.red)` (the Pi-zero), `hmp`/`hemb` from the
identity, leaving only `hredCore : G y² = dlnLoss S.red 0 y`. (No smart-constructor is shipped: the
`Params` Pi-instances are heavy to elaborate through the structure's instance-fields — the SAME friction
that makes the general bundle carry `Y` + instances explicitly. The producer supplies them at the
instantiation site, where `Y` is concrete.) The GENERAL bundle (Y a field) is the answer to (i): keep `Y`
general — the blow-up chart is not `Params S.red` definitionally; `redEmbed` is the genuine MP reindex. -/

/-! ## The L=1 base (the `block_elimination` prototype)

The recursion's leaf. At `L = 1` a `Params` is a SINGLE matrix `A : Matrix (Fin (M 0)) (Fin (M 1)) ℝ`
and `prod M A = A` (a one-term product), so at the deepest point `B = 0` the loss is ALREADY the pure
smooth block `dlnLoss M 0 A = ∑ᵢⱼ (A i j)² = ‖A‖²_F` — no chart, no unit, the reduced chain is empty.
This is what terminates the recursion (the `nReg = M0·M1` regular generators, `red = 0`). The genuine
Schur content (a NONTRIVIAL target `B` of rank `r`) is the `block_elimination` prototype: regular
row/column ops carry `B` to `diag(E_r, 0)`, exposing the `r×r` regular block — but at the deepest
point `B = 0` (`rank 0 = 0`), `block_elimination` degenerates to the all-smooth case, confirming the
leaf. Below: the L=1 deepest-point loss is the entrywise sum of squares (the smooth-block leaf form),
proved directly from `prod` at `L = 1`. -/

/-- `prod` at `L = 1`, entrywise: the single layer matrix `A 0` (a one-term product `1 · A 0`). The
index types match definitionally at `L = 1` (`(0 : Fin 1).castSucc = (0 : Fin 2)`,
`(0 : Fin 1).succ = Fin.last 1`), so `A 0` indexes by `i, j` directly. Mirrors `prod_two_layer`'s
`convert …one_mul…using 2` cast-discharge. -/
theorem prod_one_layer (M : Fin 2 → ℕ) (A : Params M)
    (i : Fin (M 0)) (j : Fin (M (Fin.last 1))) :
    prod M A i j = A 0 i j := by
  unfold prod
  simp only [prodAux, eq_mpr_eq_cast]
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) j using 2

/-- **L=1 base — the smooth-block leaf.** At `L = 1` and the deepest point `B = 0`, the loss is
the pure entrywise sum of squares of the single layer matrix `A 0` — already the smooth-block
normal form (`nReg = M0·M1` regular generators, empty reduced chain). This terminates the Schur
recursion: there is nothing left to pivot. (The genuine Schur split is for `B ≠ 0` of rank `r` via
`block_elimination`; at the deepest point `rank 0 = 0`, the regular `E_r` block is empty, the whole
loss is smooth.) -/
theorem dlnLoss_one_layer_deepest (M : Fin 2 → ℕ) (A : Params M) :
    dlnLoss M 0 A = ∑ i, ∑ j, (A 0 i j) ^ 2 := by
  unfold dlnLoss
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Matrix.sub_apply, Matrix.zero_apply, sub_zero, prod_one_layer]

/-! `dlnLoss_nonneg` now lives in `Foundations/Loss.lean` (reusable bedrock), reachable via the
`Skeleton` import. Removed from this scratch file to avoid duplication. -/

end DLNFibre.DLN.RLCT

