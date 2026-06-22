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
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) j using 2 <;>
    simp [Fin.cast]

/-- **L=1 base — the smooth-block leaf.** At `L = 1` and the deepest point `B = 0`, the loss is the
pure entrywise sum of squares of the single layer matrix `A 0` — already the smooth-block normal form
(`nReg = M0·M1` regular generators, empty reduced chain). This terminates the Schur recursion: there
is nothing left to pivot. (The genuine Schur split is for `B ≠ 0` of rank `r` via `block_elimination`;
at the deepest point `rank 0 = 0`, the regular `E_r` block is empty, the whole loss is smooth.) -/
theorem dlnLoss_one_layer_deepest (M : Fin 2 → ℕ) (A : Params M) :
    dlnLoss M 0 A = ∑ i, ∑ j, (A 0 i j) ^ 2 := by
  unfold dlnLoss
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Matrix.sub_apply, Matrix.zero_apply, sub_zero, prod_one_layer]

/-! `dlnLoss_nonneg` now lives in `Foundations/Loss.lean` (reusable bedrock), reachable via the
`Skeleton` import. Removed from this scratch file to avoid duplication. -/

end DLNFibre.DLN.RLCT

