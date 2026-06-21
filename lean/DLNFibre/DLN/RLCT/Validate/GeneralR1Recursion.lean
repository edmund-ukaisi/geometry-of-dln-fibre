import DLNFibre.DLN.RLCT.Skeleton

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

/-! ## The G3.2 per-node strict-transform datum — `IsSchurNode` (I3, blow-up form, SPECIFY)

The (C)-sound per-node contract (controller-relayed from fm's interface; replaces the incomplete
scalar `IsSchurChart`). The I3 strict-transform identity in **blow-up form**: pulling the core
`dlnLoss M 0` back along the per-node blow-up chart `φ` re-identifies it as the **exceptional
monomial Jacobian-weight** `∏ x^{h}` (NOT a unit — the `(x_p)^{card−1}`-type weight `pivotBlowupOn`
produces) times the **reduced-chain core** `dlnLoss M' 0` on the strictly-smaller chain `M' = S.red`
(via the coordinate embedding `ι`). fm's `g5_pivotNode` glue composes these nodes → `resolution_charts`
(`⨅ monomialThreshold`), descending on the reduced core, reading `(k,h)` at the leaves.

`φ`, the node's chart, is kept ABSTRACT here (a chart function `(Fin N → ℝ) → (Fin N → ℝ)` on the
flat coords + the reduced-chain map): the exact composition — pure `pivotBlowupOn` (C1) vs a det-1
GL-straightening THEN `pivotBlowupOn` (C2) — is pinned by pp-hall's #109 reconcile (the (2,2,2) Lean
anchor exhibits C2: `lemma2Fwd` det-1 then `pivotBlowupOn`). The I3 SHAPE (monomial × reduced-core)
is settled regardless; only the `φ` field's construction differs. `monExp` is the exceptional
exponent vector `h_{n,p}` (the Jacobian-induced monomial), `active`/`p` the blow-up's index data
(matching `pivotBlowupOn`'s `(active : Finset) (p)` signature, pp-hall #123 field-3). -/

/-- **The per-node strict-transform datum (I3, blow-up form) — SPECIFY.** Carries fm's
`ResolutionNode` fields on the flat coords (`Fin N → ℝ` via `paramsEquivFlat`): the active index set +
pivot (blow-up data), the reduced chain `M' = S.red`, the exceptional monomial exponent, and the I3
strict-transform identity `(dlnLoss M 0 ∘ paramsEquivFlat.symm) ∘ φ = (∏ exceptional monomial) ·
((dlnLoss M' 0 ∘ paramsEquivFlat.symm) ∘ reduced-embed)`. The monomial is the BLOW-UP Jacobian weight,
NOT a unit (the (C) correction). `φ` abstract pending pp-hall #109's exact composition. -/
structure IsSchurNode {L : ℕ} {N : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
    (flatCore : (Fin N → ℝ) → ℝ)            -- `dlnLoss M 0` in flat coords
    (flatRedCore : (Fin N → ℝ) → ℝ)         -- `dlnLoss M' 0` (M' = S.red) in flat coords
    (φ : (Fin N → ℝ) → (Fin N → ℝ))          -- the node's blow-up chart (abstract pending pp #109)
    (active : Finset (Fin N)) (p : Fin N)    -- blow-up index data (matches pivotBlowupOn sig)
    (monExp : (Fin N → ℝ) → ℝ)               -- the exceptional monomial Jacobian-weight ∏ x^h
    (ι : (Fin N → ℝ) → (Fin N → ℝ)) : Prop where
  /-- I3 strict-transform (blow-up form): pulled-back core = monomial-weight × reduced core. -/
  strictTransform : ∀ x, flatCore (φ x) = monExp x * flatRedCore (ι x)
  /-- The exceptional weight is the blow-up Jacobian monomial (nonneg; vanishes on the center). -/
  monExp_nonneg : ∀ x, 0 ≤ monExp x
  /-- Well-foundedness (pp #123 field-6): the reduced chain is strictly smaller. -/
  measure_drops : ∑ s, S.red s < ∑ s, M s

/-- **G3.2 crux — the per-node strict-transform existence (SPECIFY, body `sorry`; mine).** There
exists a blow-up node realising the I3 datum: the per-node chart `φ` + index data + monomial exponent
+ reduced chain, with the strict-transform identity. The heavy Schur-construction crux (the
`(uᵢ, ψᵢ)` adapted-basis substitution; pp-hall spells the sub-steps). `φ`'s exact composition
(C1/C2) pinned by pp #109; the I3 shape is settled. A sorry'd existence ⟹ vacuous recursion. -/
theorem schur_node_exists {L : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
    {N : ℕ} (flatCore flatRedCore : (Fin N → ℝ) → ℝ) :
    ∃ (φ : (Fin N → ℝ) → (Fin N → ℝ)) (active : Finset (Fin N)) (p : Fin N)
      (monExp : (Fin N → ℝ) → ℝ) (ι : (Fin N → ℝ) → (Fin N → ℝ)),
      IsSchurNode M S flatCore flatRedCore φ active p monExp ι := by
  sorry

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
at the deepest point `rank 0 = 0`, the regular `E_r` block is empty and the whole loss is smooth.) -/
theorem dlnLoss_one_layer_deepest (M : Fin 2 → ℕ) (A : Params M) :
    dlnLoss M 0 A = ∑ i, ∑ j, (A 0 i j) ^ 2 := by
  unfold dlnLoss
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Matrix.sub_apply, Matrix.zero_apply, sub_zero, prod_one_layer]

/-! `dlnLoss_nonneg` now lives in `Foundations/Loss.lean` (reusable bedrock), reachable via the
`Skeleton` import. Removed from this scratch file to avoid duplication. -/

end DLNFibre.DLN.RLCT

