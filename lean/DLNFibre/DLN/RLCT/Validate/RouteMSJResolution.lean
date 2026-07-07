import DLNFibre.DLN.RLCT.Validate.RouteMBoxThresholdRRP
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotChart
import DLNFibre.DLN.RLCT.Validate.RouteMSJChartAlgebra
import DLNFibre.DLN.RLCT.Foundations.LossContinuity

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJResolution` — the general-`L` R1-UPPER `(S,J)` resolution SKELETON

The **statements-first skeleton** of Aoyagi's simultaneous rank-flag `(S,J)` resolution for the
general-`L` box-finiteness `RouteMBoxThresholdFinite M` (`= rlct ≥ ½·minAdm`, the R1-UPPER long pole).
This is the FIRST tide of a multi-tide mountain: it lays the honest 7-piece contract, CLOSES the
pieces that reuse banked machinery, and leaves the genuinely-new analytic pieces as clearly-named
sorries for subsequent tides.

Grounded design certificate:
`expeditions/2026-06-20-aoyagi-full/threads/genm-r1upper-design/design-cert.md` (3 decorrelated passes
+ Codex xhigh). Its final section is a 7-piece build spec in dependency order; this file's declarations
ARE those pieces.

## The recursion spine (sorry-free wrapper + two contracts)

`RouteMBoxThresholdFinite` is proved by **strong induction on the chain arity** (like `minAdmRec`):
`routeMBoxThresholdFinite_of_step` is the **sorry-free, axiom-clean WRAPPER** — it consumes the two
analytic contracts

* `SJStepHyp` — the `(S,J)` inductive STEP: for a `≥ 3`-width chain `M`, GIVEN box-finiteness for
  every one-shorter chain (the strong IH), box-finiteness holds for `M`;
* `SJBaseHyp` — the `L = 1` (single free matrix) Morse base.

and yields box-finiteness for ALL `M`. The wrapper carries NO analytic content (mirrors
`core_schurGen_lt_top`); the deferred content is confined to the two contracts.

`sjResolutionStep_proof : SJStepHyp` is NOT a bare sorry — it **genuinely composes** piece 3 (the
per-`(t,ρ,κ)` boundary peel `sjBoundaryPeel`) with pieces 4/5/7 (the joint resolution
`sjJointResolution`): the peel bounds the `M` box integral by the finite sum over `t = 1..min` and pivot
charts `(ρ,κ)` of the per-chart peeled integrals (`gammaPeelIntegral M t ρ κ c'`), each finite by the
joint resolution. Piece 3's OUTER measure-preserving reduction is CLOSED (reusable, clean-three):
`routeMLayerBoxIntegral_front_split` (the general-`L` front-split `eFront` + the `prod_front_peel`
integrand identity `frobSq_prod_front`) reduces the `M` box integral to the tail-outer iterated
front-factor fibre integral `∫_{A'∈box(tail)} ∫_{A₀∈box} frobSq(A₀·prod(tailChain M)A')^{−c'}`, and the
finite pivot-chart cover `pivotChartCover_lintegral_le_sum` (CLOSED here, reusing banked
`pivotLocus_eq_iUnion`) splits the inner `A₀`-integral over the pivot charts.

**RE-SCOPE (2026-07-07, triple-confirmed fix + decorrelated Codex).** The prior `(S,J)`-peel contract
was FLAWED: `gammaPeelIntegral M t c'` (a) summed over `t ∈ range(min+1)`, so the `t = 0` term (a `0×0`
pivot) was the WHOLE box integral, making the peel vacuous AND `sjJointResolution M _ 0` CIRCULAR (its
`t=0` instance is the induction goal); (b) was indexed by `t` only, not the chart `(ρ,κ)`; (c) used an
UNFAITHFUL integrand (dropped the `C·Q̃_p` cross-term, replaced `‖A·Q̃_p‖²` by `‖Q_p‖²`, used a clean box
for `Γ`). The fix re-scopes `gammaPeelIntegral` to the FAITHFUL per-`(t,ρ,κ)`-chart RAW contribution
`∫_{A'} ∫_{A₀∈box ∩ pivotChart ρ κ} frobSq(A₀·Q)^{−c'}` (Candidate B), summed over `t = 1..min` — no
dropped term, no clean-box distortion, `t = 0` excluded (killing the circularity). This makes
`sjBoundaryPeel` a PURE cover inequality (`front_split` + `pivotLocus_eq_iUnion` at `t=1`; `{A₀=0}` null),
constant `1`. The faithful cross-coupled Schur form `(‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{−c'}` is the banked
EXACT identity `frobSq_schur_block_split` (`RouteMSJChartAlgebra`), which — with the MP shear `D ↦ Γ` —
is the honest bridge `sjJointResolution` (finiteness) consumes, NOT baked into the def. So the two sorries
feeding `routeMBoxThresholdFinite_sjResolution` are `sjBoundaryPeel` (3, the cover+shear plumbing WALL)
and `sjJointResolution` (4/5/7, per-chart finiteness); the `L = 1` Morse base (`sjBase1_freeMatrix`), the
recursion spine, and the pivot-chart cover are CLOSED.

## The 7 pieces (dependency order; CLOSED vs named-sorry)

1. **Local comparability / units** — `sjLocalComparability`, `paramsBoxM_volume_lt_top`. CLOSED (pure
   measure theory + compactness). The banked L=2 fibre engine is `MatMulFibre.fibre_lintegral_mul_le`.
2. **Pivot–Schur chart** — `sjPivotSchurChart_rrp` (the L=2 `(r,r,p)` instance, CLOSED via the banked
   `routeMBoxThresholdFinite_rrp`). The general-`L` chart is the internal change of variables of piece 3
   (`sjBoundaryPeel`), stated there — not duplicated as a standalone claim.
3. **Boundary peel** (`sjBoundaryPeel`, named sorry — the cover+shear measure-plumbing WALL). Re-scoped
   to the PURE cover inequality `box ≤ ∑_{t=1..min} ∑_{ρ,κ} gammaPeelIntegral M t ρ κ c'` (constant `1`).
   The pieces are banked/closable: `routeMLayerBoxIntegral_front_split` (+ `eFront` + `frobSq_prod_front`,
   clean-three) reduces the `M` box integral to the tail-outer front-factor fibre integral;
   `pivotLocus_eq_iUnion` (`{1 ≤ rank} = ⋃_{ρ,κ} pivotChart ρ κ`) + `lintegral_iUnion_le` cover the inner
   `A₀`-box (the `{A₀=0}` rank-0 point is null). The residual is the block-reindex of `matBox` through
   arbitrary `(ρ,κ)` embeddings + complements measure-preservingly (a multi-hundred-line plumbing wall).
4. **`(S,J)` normal-form invariant** — the block-dimension consequence `sjRunMin_antitone` (running-min
   corank `M(S)` monotone) is CLOSED; the full matrix-valued invariant needs the `[E_J|D_J]` carrier
   (`SJState`/`sjRunMin` stubs), folded into `sjJointResolution`, deferred to the mountain build.
5. **Jacobian / charge-update** — `sjChargeUpdate_accum` (the additive `Mval` charge, CLOSED via banked
   `Mval_decompose`) + the exponent bookkeeping folded into `sjJointResolution`.
6. **Charge-budget inequality** (combinatorial core) — `sjChargeBudget_recursion`/`_le`/`_binding`,
   `sjSubordination`. CLOSED, reusing `LayerSplit_value_eq_minAdm` / `minAdmRec_eq_minAdm`; the residual
   leading-width monotonicity `minAdm_leadWidth_mono` is now PROVED (arity induction on the layer-peeling
   recursion via `minAdm_cons_eq`), so all of piece 6 is sorry-free.
7. **Monomial integrability assembly** (analytic endpoint) — `sjJointResolution` (bundles the
   monomialised finiteness). Named sorry. The generic monomial finiteness it consumes is banked
   (`Case222Cover.monomialIntegrand_integrable_of_lt`); the monomialisation is the new content.

## S2 / axiom hygiene
The wrapper introduces NO measure-theoretic content of its own and NO new axiom. The deferred content
sits in the named contracts; `#print axioms routeMBoxThresholdFinite_of_step` is clean-three. The final
`routeMBoxThresholdFinite_sjResolution` carries exactly the two remaining LOAD-BEARING analytic sorries
(`sjBoundaryPeel`, `sjJointResolution`). The outer front-split plumbing
(`routeMLayerBoxIntegral_front_split`, `eFront`, `frobSq_prod_front`, `measurable_frontIntegrand`) and the
finite pivot-chart cover (`pivotChartCover_lintegral_le_sum`) are CLOSED clean-three
`[propext, Classical.choice, Quot.sound]` and reusable for the eventual `sjBoundaryPeel` discharge.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## `Params` measurability/topology instances (Pi structure through the `Params` def)

`Params H = ∀ s, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ` inherits `TopologicalSpace` /
`MeasurableSpace` / `MeasureSpace` by `inferInstanceAs`, but instance search does NOT unfold the `def`
to find the Pi-level `BorelSpace` / `SecondCountableTopology` / `SigmaFinite volume`. We expose them
here (so `Continuous.measurable` and the product-measure Tonelli lemmas fire on `Params`). -/

instance instSecondCountableParams {L : ℕ} (H : Fin (L + 1) → ℕ) :
    SecondCountableTopology (Params H) :=
  inferInstanceAs (SecondCountableTopology
    (∀ s : Fin L, Fin (H s.castSucc) → Fin (H s.succ) → ℝ))

instance instBorelSpaceParams {L : ℕ} (H : Fin (L + 1) → ℕ) : BorelSpace (Params H) :=
  inferInstanceAs (BorelSpace (∀ s : Fin L, Fin (H s.castSucc) → Fin (H s.succ) → ℝ))

instance instSigmaFiniteParams {L : ℕ} (H : Fin (L + 1) → ℕ) :
    SigmaFinite (volume : Measure (Params H)) :=
  inferInstanceAs (SigmaFinite
    (volume : Measure (∀ s : Fin L, Fin (H s.castSucc) → Fin (H s.succ) → ℝ)))

/-- The `Matrix (Fin m) (Fin n) ℝ` measure space, inherited from the underlying `Fin m → Fin n → ℝ`
Pi structure (`Matrix` is a `def` synonym, so instance search does not unfold it on its own). Exposed
so the pivot-chart cover integral (`pivotChartCover_lintegral_le_sum`, over `pivotChart : Set (Matrix
…)`) elaborates its `∫⁻` against the matrix front factor. Defeq to the Pi volume — no new content. -/
noncomputable instance instMeasureSpaceMatrixFinFin {m n : ℕ} :
    MeasureSpace (Matrix (Fin m) (Fin n) ℝ) :=
  inferInstanceAs (MeasureSpace (Fin m → Fin n → ℝ))

/-! ## Piece 1 — local comparability / units (CLOSED, pure measure theory) -/

/-- **Piece 1 — the L¹ comparability lemma.** If, on a set `s`, the integrand `f` is dominated a.e. by
a finite constant `C` times an integrable `g`, then `∫_s f < ⊤`. The measure-theoretic heart of
Aoyagi's Lemma 1 (bounded units / comparable integrands preserve local `L¹` finiteness). Reusable
bedrock for every chart bound. -/
theorem sjLocalComparability {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f g : α → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hfg : ∀ᵐ a ∂(μ.restrict s), f a ≤ C * g a) (hg : (∫⁻ a in s, g a ∂μ) ≠ ⊤) :
    (∫⁻ a in s, f a ∂μ) < ⊤ := by
  calc (∫⁻ a in s, f a ∂μ)
      ≤ ∫⁻ a in s, C * g a ∂μ := lintegral_mono_ae hfg
    _ = C * ∫⁻ a in s, g a ∂μ := lintegral_const_mul' C _ hC
    _ < ⊤ := ENNReal.mul_lt_top hC.lt_top hg.lt_top

/-- **Piece 1 — the parameter box has finite volume.** `volume (paramsBoxM M T) < ⊤`. The box is the
`paramsEquivFlat`-preimage of the compact flat cube; the flattening is measure-preserving. Reusable in
every chart's `c' = 0` / dominating-constant bound. -/
theorem paramsBoxM_volume_lt_top (M : Fin (L + 1) → ℕ) (T : ℝ) :
    volume (paramsBoxM M T) < ⊤ := by
  rw [← paramsEquivFlat_preimage_paramsBoxM M T,
    (measurePreserving_paramsEquivFlat M).measure_preimage
      (by
        rw [cubeBox]
        exact (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).nullMeasurableSet),
    cubeBox]
  exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top

/-! ## Piece 6 — the charge-budget recursion + subordination (CLOSED via `minAdmRec`)

The combinatorial core: the accumulated per-boundary charge composes as the layer-peeling recursion,
bottoming out at `minAdm M`. All banked in `RouteMLayerSplit` (`LayerSplit_value_eq_minAdm`,
`minAdmRec_eq_minAdm`); the leading-width monotonicity `minAdm_leadWidth_mono` (the former residual) is
now PROVED here (arity induction on `minAdm_cons_eq`), so the whole piece is sorry-free. -/

/-- **The full remaining product chain `(M₁, M₂, …, M_L)`** — the coupling factor `P_full`'s chain
(one fewer layer than `M`, but keeping the ORIGINAL leading width `M₁`, unlike `redChain t` which
replaces it by the pivot rank `t`). Definitionally `tailChain M = redChain (M 1) M`. -/
def tailChain (M : Fin (L + 1 + 1 + 1) → ℕ) : Fin (L + 1 + 1) → ℕ := fun i => M i.succ

@[simp] theorem tailChain_zero (M : Fin (L + 1 + 1 + 1) → ℕ) : tailChain M 0 = M 1 := by
  simp [tailChain, Fin.succ_zero_eq_one]

theorem tailChain_succ (M : Fin (L + 1 + 1 + 1) → ℕ) (i : Fin (L + 1)) :
    tailChain M i.succ = M i.succ.succ := rfl

/-- `tailChain M = redChain (M 1) M` — the full remaining chain is the reduced chain at pivot `M₁`
(the no-rank-drop cut at boundary 0). -/
theorem tailChain_eq_redChain (M : Fin (L + 1 + 1 + 1) → ℕ) :
    tailChain M = redChain (M 1) M := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [tailChain_zero, redChain_zero]
  · rw [tailChain_succ, redChain_succ]

/-- **The peel exponent `a = (M₀ − t)(M₁ − t)`** — the boundary-0 blow-up Jacobian exponent
(`z^{a−1}`), the codim of the corank block `Γ : (M₀−t)×(M₁−t)`. -/
def peelExp (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) : ℕ := (M 0 - t) * (M 1 - t)

/-- **Piece 6 (core) — the charge-budget recursion.** `minAdm M` is the min over admissible pivot
ranks `t` of `(M₀−t)(M₁−t) + minAdm (redChain t M)` — the accumulated per-boundary charge bottoms out
at `minAdm M`. Literally the banked `LayerSplit_value_eq_minAdm`. -/
theorem sjChargeBudget_recursion (M : Fin (L + 1 + 1 + 1) → ℕ) :
    (Finset.range (min (M 0) (M 1) + 1)).inf' (by simp)
        (fun t => (M 0 - t) * (M 1 - t) + minAdm (redChain t M)) = minAdm M :=
  LayerSplit_value_eq_minAdm M

/-- **Piece 6 — the per-chart charge lower bound.** For every admissible pivot `t ≤ min(M₀,M₁)`, the
chart charge `(M₀−t)(M₁−t) + minAdm (redChain t M)` is at least `minAdm M`. -/
theorem sjChargeBudget_le (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (ht : t ≤ min (M 0) (M 1)) :
    minAdm M ≤ (M 0 - t) * (M 1 - t) + minAdm (redChain t M) := by
  rw [← sjChargeBudget_recursion M]
  exact Finset.inf'_le _ (by rw [Finset.mem_range]; omega)

/-- **Piece 6 — the binding cut.** There is a pivot `t*` realising the charge budget:
`(M₀−t*)(M₁−t*) + minAdm (redChain t* M) = minAdm M`. -/
theorem sjChargeBudget_binding (M : Fin (L + 1 + 1 + 1) → ℕ) :
    ∃ t, t ≤ min (M 0) (M 1) ∧
      (M 0 - t) * (M 1 - t) + minAdm (redChain t M) = minAdm M := by
  obtain ⟨t, htmem, hteq⟩ := Finset.exists_mem_eq_inf'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
    (fun t => (M 0 - t) * (M 1 - t) + minAdm (redChain t M))
  rw [Finset.mem_range] at htmem
  exact ⟨t, by omega, hteq.symm.trans (sjChargeBudget_recursion M)⟩

/-- **Piece 6 — `minAdm M ≤ minAdm (redChain (min M₀ M₁) M)`** (unconditional). The cut at
`t = min(M₀,M₁)` has zero block charge (`(M₀−t)(M₁−t) = 0` since one factor vanishes), so the budget
is carried entirely by the reduced chain. -/
theorem minAdm_le_minAdm_redChain_min (M : Fin (L + 1 + 1 + 1) → ℕ) :
    minAdm M ≤ minAdm (redChain (min (M 0) (M 1)) M) := by
  have h := sjChargeBudget_le M (min (M 0) (M 1)) le_rfl
  have ha : (M 0 - min (M 0) (M 1)) * (M 1 - min (M 0) (M 1)) = 0 := by
    rcases le_total (M 0) (M 1) with h01 | h10
    · rw [min_eq_left h01, Nat.sub_self, zero_mul]
    · rw [min_eq_right h10, Nat.sub_self, mul_zero]
  rw [ha, zero_add] at h; exact h

/-- `minAdm` of a two-width chain is the pivot-width product `M 0 · M 1` (the `minAdmRec` leaf). -/
theorem minAdm_two_eq (M : Fin 2 → ℕ) : minAdm M = M 0 * M 1 := by
  rw [← minAdmRec_eq_minAdm, minAdmRec_leaf]

/-- `(Fin.cons p rest) 1 = rest 0` (the second entry of a cons is the head of the tail). -/
theorem cons_one_eq {n : ℕ} (p : ℕ) (rest : Fin (n + 1) → ℕ) :
    (Fin.cons p rest : Fin (n + 2) → ℕ) 1 = rest 0 := by
  rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl, Fin.cons_succ]

/-- `redChain t (Fin.cons p rest) = Fin.cons t (Fin.tail rest)` — the reduced chain of a cons is
independent of the leading width `p` (it drops `p`, installs the pivot `t`, keeps `Fin.tail rest`). -/
theorem redChain_cons (t p : ℕ) (rest : Fin (L + 1 + 1) → ℕ) :
    redChain t (Fin.cons p rest) = Fin.cons t (Fin.tail rest) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [redChain_zero, Fin.cons_zero]
  · simp only [redChain_succ, Fin.cons_succ, Fin.tail]

/-- **The leading-width recursion for `minAdm`** (arity `≥ 3`), with the reduced chain written in the
`Fin.cons` form: `minAdm (cons p rest) = min_{t ≤ min(p, rest₀)} [(p−t)(rest₀−t) + minAdm (cons t
(tail rest))]`. The `sjChargeBudget_recursion` (= banked `LayerSplit_value_eq_minAdm`) specialised at a
cons chain, with `redChain t (cons p rest) = cons t (tail rest)` (`redChain_cons`). Both the pivot range
and the block term depend on `p`; only the reduced chain is `p`-independent. -/
theorem minAdm_cons_eq (p : ℕ) (rest : Fin (L + 1 + 1) → ℕ) :
    minAdm (Fin.cons p rest)
      = (Finset.range (min p (rest 0) + 1)).inf' (by simp)
          (fun t => (p - t) * (rest 0 - t) + minAdm (Fin.cons t (Fin.tail rest))) := by
  rw [← sjChargeBudget_recursion (Fin.cons p rest)]
  simp only [Fin.cons_zero, cons_one_eq, redChain_cons]

/-- **`minAdm` of a chain led by a zero width is `0`.** A chain `Fin.cons 0 rest` has the zero product
(rank forced to `0` through the width-`0` vertex), so its generic fibre is everything — codim `0`. Proved
by arity induction via the leading-width recursion `minAdm_cons_eq`: the pivot range `t ≤ min(0, rest₀) =
0` forces the single cut `t = 0` (block charge `0`), descending to `cons 0 (tail rest)`. Used for the
`min(M₀,M₁) = 0` edge of `sjBoundaryPeel` (there `minAdm M = 0`, so the threshold is unsatisfiable). -/
theorem minAdm_cons_zero {L : ℕ} (rest : Fin (L + 1) → ℕ) :
    minAdm (Fin.cons 0 rest) = 0 := by
  induction L with
  | zero => simp [minAdm_two_eq, Fin.cons_zero]
  | succ L IH =>
    rw [minAdm_cons_eq 0 rest]
    refine Nat.le_antisymm ?_ (Nat.zero_le _)
    refine le_trans (Finset.inf'_le _
      (show (0 : ℕ) ∈ Finset.range (min 0 (rest 0) + 1) by rw [Finset.mem_range]; omega)) ?_
    simp only [Nat.zero_sub, Nat.zero_mul, Nat.zero_add]
    exact le_of_eq (IH (Fin.tail rest))

/-- **Piece 6 — leading-width monotonicity of `minAdm` (PROVED).** Increasing the leading width of a
chain (all else fixed) does not decrease `minAdm`:
`p ≤ q → minAdm (Fin.cons p rest) ≤ minAdm (Fin.cons q rest)`. Proven by induction on the chain arity via
the leading-width recursion (`minAdm_cons_eq`): the reduced chains `cons t (tail rest)` are shared between
the `p`- and `q`-sides (`redChain_cons`), so the two `inf'`s differ only in the pivot range and the block
factor. It is NOT termwise (the larger leading width both raises the block terms and widens the pivot
range `min(·, rest₀)`); the range-widening is handled by selecting the cut `t = p` (block charge `0`) and
descending via the induction hypothesis on `tail rest` when the `q`-cut `t` exceeds `min(p, rest₀)`.
Numerically corroborated (0 violations, `sj_check.py`). -/
theorem minAdm_leadWidth_mono {L : ℕ} (p q : ℕ) (hpq : p ≤ q) (rest : Fin (L + 1) → ℕ) :
    minAdm (Fin.cons p rest) ≤ minAdm (Fin.cons q rest) := by
  induction L generalizing p q with
  | zero =>
    rw [minAdm_two_eq, minAdm_two_eq, Fin.cons_zero, Fin.cons_zero, cons_one_eq, cons_one_eq]
    gcongr
  | succ L IH =>
    rw [minAdm_cons_eq p rest, minAdm_cons_eq q rest]
    refine Finset.le_inf' _ _ (fun t htmem => ?_)
    rw [Finset.mem_range, Nat.lt_succ_iff] at htmem
    have ht_rest : t ≤ rest 0 := le_trans htmem (min_le_right _ _)
    by_cases hcaseA : t ≤ min p (rest 0)
    · -- `t` lies in the `p`-pivot range: the shared cell is monotone in the leading width.
      have hmemp : t ∈ Finset.range (min p (rest 0) + 1) := by rw [Finset.mem_range]; omega
      refine le_trans (Finset.inf'_le _ hmemp) ?_
      have hblk : (p - t) * (rest 0 - t) ≤ (q - t) * (rest 0 - t) := by gcongr
      omega
    · -- `min(p, rest₀) < t ≤ rest₀` forces `min(p, rest₀) = p` and `p < t`: cut at `t = p`
      -- (block charge `0`), then descend by the IH on `tail rest`.
      have hminp : min p (rest 0) = p := by omega
      have hpt : p < t := by omega
      have hmemp : p ∈ Finset.range (min p (rest 0) + 1) := by rw [Finset.mem_range]; omega
      refine le_trans (Finset.inf'_le _ hmemp) ?_
      have hmm : minAdm (Fin.cons p (Fin.tail rest)) ≤ minAdm (Fin.cons t (Fin.tail rest)) :=
        IH p t (le_of_lt hpt) (Fin.tail rest)
      have hz : (p - p) * (rest 0 - p) = 0 := by rw [Nat.sub_self, Nat.zero_mul]
      rw [hz, Nat.zero_add]
      exact le_trans hmm (Nat.le_add_left _ _)

/-- **Piece 6 — `minAdm M ≤ minAdm (tailChain M)`** (the coupling chain dominates). If `M₁ ≤ M₀` the
`t = M₁` cut gives it directly (`redChain M₁ M = tailChain M`, zero block charge); otherwise the
`t = M₀` cut plus leading-width monotonicity (`M₀ ≤ M₁`) does. -/
theorem minAdm_le_minAdm_tailChain (M : Fin (L + 1 + 1 + 1) → ℕ) :
    minAdm M ≤ minAdm (tailChain M) := by
  rcases le_total (M 1) (M 0) with h10 | h01
  · have h := minAdm_le_minAdm_redChain_min M
    rwa [min_eq_right h10, ← tailChain_eq_redChain] at h
  · have h := minAdm_le_minAdm_redChain_min M
    rw [min_eq_left h01] at h
    refine le_trans h ?_
    -- `redChain (M 0) M = Fin.cons (M 0) rest`, `tailChain M = redChain (M 1) M = Fin.cons (M 1) rest`
    have hlift : minAdm (redChain (M 0) M) ≤ minAdm (redChain (M 1) M) :=
      minAdm_leadWidth_mono (M 0) (M 1) h01 (fun i => M i.succ.succ)
    rwa [← tailChain_eq_redChain] at hlift

/-- **Piece 6 — subordination.** At the binding cut `t*`, the coupling exponent `a = (M₀−t*)(M₁−t*)`
is subordinate to the coupling chain's RLCT budget: `a ≤ minAdm M ≤ minAdm (tailChain M)`, i.e.
`a/2 ≤ ½·minAdm(M₁,…,M_L)` — the fact keeping the coupling factor `P_full^{−a/2}` at or below the tail's
RLCT in the joint resolution. **Non-strict is the sharp form**: the design cert's "strict for `a > 0`"
is FALSE at some binding cuts (e.g. `M = (1,1,1)`, cut `t = 0`: `a = 1 = minAdm(1,1)`), so the joint
resolution CANNOT rely on strict slack from this — it must select a favorable (minimal-`a`, "gentle")
binding cut, not the arbitrary minimiser `sjChargeBudget_binding` returns, or exhibit slack elsewhere. -/
theorem sjSubordination (M : Fin (L + 1 + 1 + 1) → ℕ) :
    ∃ t, t ≤ min (M 0) (M 1) ∧
      (M 0 - t) * (M 1 - t) + minAdm (redChain t M) = minAdm M ∧
      (M 0 - t) * (M 1 - t) ≤ minAdm (tailChain M) := by
  obtain ⟨t, ht, heq⟩ := sjChargeBudget_binding M
  refine ⟨t, ht, heq, ?_⟩
  have h1 : (M 0 - t) * (M 1 - t) ≤ minAdm M := by omega
  exact le_trans h1 (minAdm_le_minAdm_tailChain M)

/-- **Piece 5 (charge accounting, CLOSED) — the additive `Mval` charge update.** The exceptional
codim charge accumulates additively down a resolution path: peeling boundary 0 at pivot `T₀` splits
`Mval M T` into the block term `(M₀−T₀)(M₁−T₀)` plus the reduced-chain charge `Mval (redChain T₀ M)
(tail T)`. Banked as `Mval_decompose` — the charge-update side of piece 5 (the Jacobian-exponent side
is analytic, folded into `sjJointResolution`). -/
theorem sjChargeUpdate_accum (M : Fin (L + 1 + 1 + 1) → ℕ) (T : Fin (L + 1 + 1) → ℕ) :
    Mval M T
      = ((M 0 : ℤ) - T 0) * ((M 1 : ℤ) - T 0)
        + Mval (redChain (T 0) M) (Fin.tail T) :=
  Mval_decompose M T

/-! ## Piece 3 (plumbing, CLOSED) — the measure-preserving front-split of the box integral

The `M`-box integral factors through peeling the leftmost layer `A₀ : M₀×M₁` off the product
(`prod M A = A₀ · prod(tailChain M)(tail A)`, `prod_front_peel`), reducing to the iterated
front-factor fibre integral over the tail box (outer) and the `A₀`-box (inner). Pure measure-preserving
plumbing — the general-`L` analog of `eParamsRRP` — the reusable OUTER half of `sjBoundaryPeel`; the
genuinely-new analytic content (the per-tail-parameter inner fibre bound) stays inside `sjBoundaryPeel`. -/

/-- **The front-split measurable equivalence** `Params M ≃ᵐ (M₀×M₁ matrix) × Params(tailChain M)`,
peeling layer `0`. Definitionally `piFinSuccAbove` at index `0`: `Fin.succAbove 0 = Fin.succ` and the
tail widths `tailChain M i = M i.succ` make the `succAbove 0`-reindexed factor family defeq to
`Params (tailChain M)`. -/
noncomputable def eFront (M : Fin (L + 1 + 1 + 1) → ℕ) :
    Params M ≃ᵐ (Fin (M 0) → Fin (M 1) → ℝ) × Params (tailChain M) :=
  MeasurableEquiv.piFinSuccAbove
    (fun s : Fin (L + 1 + 1) => Fin (M s.castSucc) → Fin (M s.succ) → ℝ) 0

/-- `eFront` is measure-preserving (it is `piFinSuccAbove`, banked MP). -/
theorem measurePreserving_eFront (M : Fin (L + 1 + 1 + 1) → ℕ) :
    MeasurePreserving (eFront M) (volume : Measure (Params M)) volume :=
  volume_preserving_piFinSuccAbove
    (fun s : Fin (L + 1 + 1) => Fin (M s.castSucc) → Fin (M s.succ) → ℝ) 0

/-- The first component of `eFront A` is the leading layer `A 0`. -/
theorem eFront_fst (M : Fin (L + 1 + 1 + 1) → ℕ) (A : Params M) : (eFront M A).1 = A 0 := rfl

/-- The second component of `eFront A` is the layer tuple `s ↦ A s.succ` (the tail chain). -/
theorem eFront_snd_apply (M : Fin (L + 1 + 1 + 1) → ℕ) (A : Params M) (s : Fin (L + 1)) :
    (eFront M A).2 s = A s.succ := rfl

/-- The tail component of `eFront A` is `Atail M A` (the `prod_front_peel` tail). -/
theorem eFront_snd_eq_Atail (M : Fin (L + 1 + 1 + 1) → ℕ) (A : Params M) :
    (eFront M A).2 = Atail M A := by
  funext s
  have eA : M ((s.succ : Fin (L + 1 + 1)).castSucc) = Mtail M (s.castSucc) := rfl
  have eB : M ((s.succ : Fin (L + 1 + 1)).succ) = Mtail M (s.succ) := rfl
  rw [eFront_snd_apply, Atail_apply M A s eA eB,
    show (finCongr eA) = Equiv.refl _ from finCongr_refl _,
    show (finCongr eB) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl]

/-- **The box preimage** `eFront ⁻¹' (matBox M₀ M₁ 1 ×ˢ box(tail)) = paramsBoxM M 1`: the `M`-box is
exactly the product of the leading-layer box and the tail box (`Fin.cases` on the layer index). -/
theorem eFront_preimage_box (M : Fin (L + 1 + 1 + 1) → ℕ) :
    eFront M ⁻¹' (matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (tailChain M) 1) = paramsBoxM M 1 := by
  ext A
  simp only [Set.mem_preimage, Set.mem_prod, matBox, paramsBoxM, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, htail⟩ s
    refine Fin.cases (fun i j => ?_) (fun s' i j => ?_) s
    · exact h0 i j
    · exact htail s' i j
  · intro h
    exact ⟨fun i j => h 0 i j, fun s' i j => h s'.succ i j⟩

/-- **The front-peel integrand identity** `frobSq (prod M A) = frobSq (A₀ · prod(tailChain M)(tail A))`
in raw-product (`rmatMul`) form. `prod_front_peel` peels `A 0` off; the reindex over the `rfl`-true
widths collapses (`finCongr_refl` + `reindex_refl_refl`); `Matrix.mul_apply` matches the `Matrix`
product to `rmatMul`, and `Mtail M = tailChain M`, `(eFront M A).2 = Atail M A` bridge the tail. -/
theorem frobSq_prod_front (M : Fin (L + 1 + 1 + 1) → ℕ) (A : Params M) :
    frobSq (prod M A)
      = frobSq (rmatMul (eFront M A).1 (prod (tailChain M) (eFront M A).2)) := by
  have emid : Mtail M (0 : Fin (L + 1 + 1)) = M ((0 : Fin (L + 1 + 1)).succ) := rfl
  have ecol : Mtail M (Fin.last (L + 1)) = M (Fin.last (L + 1 + 1)) := rfl
  rw [prod_front_peel M A emid ecol, eFront_fst, eFront_snd_eq_Atail,
    show (finCongr emid) = Equiv.refl _ from finCongr_refl _,
    show (finCongr ecol) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl]
  congr 1

/-- **Continuity of the front-factor Frobenius loss** `q ↦ frobSq (q.1 · prod(tailChain M) q.2)` (the
tail product is continuous, `continuous_prod`; matrix product + sum of squares preserve continuity). -/
theorem continuous_frontLoss (M : Fin (L + 1 + 1 + 1) → ℕ) :
    Continuous (fun q : (Fin (M 0) → Fin (M 1) → ℝ) × Params (tailChain M) =>
      frobSq (rmatMul q.1 (prod (tailChain M) q.2))) := by
  have hP : Continuous (fun q : (Fin (M 0) → Fin (M 1) → ℝ) × Params (tailChain M) =>
      prod (tailChain M) q.2) := (continuous_prod (tailChain M)).comp continuous_snd
  have hR : Continuous (fun q : (Fin (M 0) → Fin (M 1) → ℝ) × Params (tailChain M) =>
      rmatMul q.1 (prod (tailChain M) q.2)) := by
    unfold rmatMul
    refine continuous_pi (fun i => continuous_pi (fun j => ?_))
    refine continuous_finset_sum _ (fun k _ => Continuous.mul ?_ (hP.matrix_elem k j))
    exact show Continuous (fun q : (Fin (M 0) → Fin (M 1) → ℝ) × Params (tailChain M) =>
        q.1 i k) from (continuous_apply k).comp ((continuous_apply i).comp continuous_fst)
  unfold frobSq
  exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _
    (fun j _ => (hR.matrix_elem i j).pow 2))

/-- **The measurability of the front-factor integrand** (`frobSq` loss through a fixed-exponent
`rpow`, `ofReal`). -/
theorem measurable_frontIntegrand (M : Fin (L + 1 + 1 + 1) → ℕ) (c' : ℝ) :
    Measurable (fun q : (Fin (M 0) → Fin (M 1) → ℝ) × Params (tailChain M) =>
      ENNReal.ofReal ((frobSq (rmatMul q.1 (prod (tailChain M) q.2))) ^ (-c'))) := by
  apply ENNReal.measurable_ofReal.comp
  exact (Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    (continuous_frontLoss M).measurable)

/-- **The front-split of the box integral (CLOSED plumbing).** The `M`-box integral equals the tail-outer
iterated integral of the front-factor fibre integrand `frobSq(A₀ · prod(tailChain M) A')^{−c'}` over the
tail box (outer) and the leading-layer box (inner). Assembly: transport `∫_{paramsBoxM M}` via `eFront`
(MP) + `eFront_preimage_box` + `frobSq_prod_front` onto the product box `matBox ×ˢ box(tail)`, then
`setLIntegral_prod_symm` (Tonelli, reverse order) puts the tail integral outermost. -/
theorem routeMLayerBoxIntegral_front_split (M : Fin (L + 1 + 1 + 1) → ℕ) (c' : ℝ) :
    routeMLayerBoxIntegral M (c' : ℝ) 1
      = ∫⁻ A' in paramsBoxM (tailChain M) 1, ∫⁻ A0 in matBox (M 0) (M 1) 1,
          ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c')) := by
  rw [routeMLayerBoxIntegral]
  have hmp := measurePreserving_eFront M
  have hpre := hmp.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.measurableEmbedding (eFront M))
    (fun q : (Fin (M 0) → Fin (M 1) → ℝ) × Params (tailChain M) =>
      ENNReal.ofReal ((frobSq (rmatMul q.1 (prod (tailChain M) q.2))) ^ (-c')))
    (matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (tailChain M) 1)
  have hprodint : ∫⁻ A in paramsBoxM M 1, ENNReal.ofReal ((frobSq (prod M A)) ^ (-c'))
      = ∫⁻ q in (matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (tailChain M) 1),
          ENNReal.ofReal ((frobSq (rmatMul q.1 (prod (tailChain M) q.2))) ^ (-c')) := by
    calc ∫⁻ A in paramsBoxM M 1, ENNReal.ofReal ((frobSq (prod M A)) ^ (-c'))
        = ∫⁻ A in eFront M ⁻¹' (matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (tailChain M) 1),
            ENNReal.ofReal
              ((frobSq (rmatMul (eFront M A).1 (prod (tailChain M) (eFront M A).2))) ^ (-c')) := by
          rw [eFront_preimage_box]
          refine setLIntegral_congr_fun (measurableSet_paramsBoxM M 1) (fun A _ => ?_)
          rw [frobSq_prod_front M A]
      _ = ∫⁻ q in (matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (tailChain M) 1),
            ENNReal.ofReal ((frobSq (rmatMul q.1 (prod (tailChain M) q.2))) ^ (-c')) := hpre
  rw [hprodint, Measure.volume_eq_prod,
    setLIntegral_prod_symm _ (measurable_frontIntegrand M c').aemeasurable]

/-! ## Piece 3 — the boundary peel (the per-`(t,ρ,κ)` peeled integral, LOAD-BEARING)

Re-scoped 2026-07-07 (triple-confirmed fix). The OLD `gammaPeelIntegral M t c'` was FLAWED on three
counts (see the module header): (1) it summed over `t ∈ range(min+1)`, so the `t = 0` term (a `0×0`
pivot) degenerated to the WHOLE box integral, making the peel vacuous AND the finiteness sorry
`sjJointResolution M _ 0` circular (its `t=0` instance IS the induction goal); (2) it was indexed by
`t` only, but a chart genuinely selects an arbitrary `(ρ,κ)` row/column subset → a different integral;
(3) its integrand was UNFAITHFUL — it dropped the cross-term `C·Q̃_p`, replaced the true top-block
energy `‖A·Q̃_p‖²` by `‖Q_p‖²`, and integrated `Γ` over a CLEAN box instead of the shear-image domain.

The faithful replacement below is the RAW per-`(t,ρ,κ)`-chart contribution — no dropped term, no
clean-box distortion — and the sum is over `t = 1..min(M₀,M₁)` (the `t = 0` whole-box term excluded,
killing the circularity; `{rank = 0} = {A₀ = 0}` is null so `{rank ≥ 1}` = box a.e.). -/

/-- **The per-chart peeled box integral at pivot cut `(t, ρ, κ)`, exponent `c'`** (re-scoped
2026-07-07, faithful). The tail-outer front-factor fibre integral of the front-split integrand
`frobSq(A₀ · prod(tailChain M) A')^{−c'}`, with the inner front factor `A₀` restricted to the pivot
chart `matBox (M₀) (M₁) 1 ∩ pivotChart ρ κ` — the box matrices whose `t×t` `(ρ,κ)`-minor is a unit
(there `A₀` has a rank-`≥ t` pivot). This is EXACTLY the `(t,ρ,κ)`-chart's contribution to the box
integral: no dropped cross-term, no clean-box distortion — the raw `frobSq(A₀·Q)^{−c'}` on the chart.

**Faithful cross-coupled form (banked, consumed by `sjJointResolution`, NOT baked in here).** By the
EXACT block identity `frobSq_schur_block_split` (`RouteMSJChartAlgebra`), on this chart — where the
pivot block `A` is invertible — the integrand equals the cross-coupled Schur form
`(‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{−c'}`, `Q̃_p = Q_p + A⁻¹B·Q_b`, `Γ = D − C A⁻¹ B` the corank block; the
measure-preserving shear `D ↦ Γ` (`measurePreserving_shearSub`) then exposes `Γ` as a free variable over
its shear-image domain `{Γ | Γ + C A⁻¹ B ∈ box}`. That reformulation is the analytic content of
`sjJointResolution` (finiteness), NOT of this definition — keeping the def as the raw chart contribution
makes `sjBoundaryPeel` a pure cover inequality, and `frobSq_schur_block_split` is the honest bridge the
finiteness proof consumes (design decision 2026-07-07, decorrelated Codex-confirmed: Candidate B). -/
noncomputable def gammaPeelIntegral (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ A' in paramsBoxM (tailChain M) 1,
    ∫⁻ A0 in matBox (M 0) (M 1) 1 ∩ pivotChart ρ κ,
      ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c'))

/-- **Piece 3 (sub-lemma 1) — the finite pivot-chart cover subadditivity (CLOSED, banked plumbing).**
For any `ℝ≥0∞`-valued integrand `f` on the front factor `A₀ : Matrix (Fin m) (Fin n) ℝ`, the integral
over the rank-`≥ t` locus is bounded by the finite sum, over all `t`-element row/column pivot selections
`(ρ, κ)`, of the per-chart integrals. Pure measure theory: the banked cover `pivotLocus_eq_iUnion`
(`{t ≤ rank} = ⋃_{ρ,κ} pivotChart ρ κ`, over a field) rewrites the domain to the finite union, then
`lintegral_iUnion_le` (countable subadditivity) + `tsum_fintype` (the embedding types
`Fin t ↪ Fin m/n` are finite) collapse the two `tsum`s to `Finset.sum`s. No disjointness needed (the
charts overlap; subadditivity is the right tool). Reusable bedrock for the peel's inner `A₀`-fibre
stratification. -/
theorem pivotChartCover_lintegral_le_sum {m n : ℕ} (t : ℕ)
    (f : Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞) :
    ∫⁻ A in {A : Matrix (Fin m) (Fin n) ℝ | t ≤ A.rank}, f A
      ≤ ∑ ρ : Fin t ↪ Fin m, ∑ κ : Fin t ↪ Fin n, ∫⁻ A in pivotChart ρ κ, f A := by
  rw [pivotLocus_eq_iUnion t]
  calc ∫⁻ A in ⋃ ρ : Fin t ↪ Fin m, ⋃ κ : Fin t ↪ Fin n, pivotChart ρ κ, f A
      ≤ ∑' ρ : Fin t ↪ Fin m, ∫⁻ A in ⋃ κ : Fin t ↪ Fin n, pivotChart ρ κ, f A :=
        lintegral_iUnion_le _ _
    _ = ∑ ρ : Fin t ↪ Fin m, ∫⁻ A in ⋃ κ : Fin t ↪ Fin n, pivotChart ρ κ, f A := tsum_fintype _
    _ ≤ ∑ ρ : Fin t ↪ Fin m, ∑' κ : Fin t ↪ Fin n, ∫⁻ A in pivotChart ρ κ, f A :=
        Finset.sum_le_sum (fun ρ _ => lintegral_iUnion_le _ _)
    _ = ∑ ρ : Fin t ↪ Fin m, ∑ κ : Fin t ↪ Fin n, ∫⁻ A in pivotChart ρ κ, f A :=
        Finset.sum_congr rfl (fun ρ _ => tsum_fintype _)

/-- **Piece 3 (sub-lemma 1′) — the `matBox`-restricted pivot-chart cover (CLOSED, banked plumbing).**
The `matBox ∩`-restricted analog of `pivotChartCover_lintegral_le_sum`: the box integral over the
rank-`≥ t` locus is bounded by the finite sum, over pivot charts `(ρ, κ)`, of the per-chart box integrals
`∫_{matBox ∩ pivotChart ρ κ} f` — exactly the domains `gammaPeelIntegral` integrates. Same proof:
distribute `matBox ∩` over the finite union (`pivotLocus_eq_iUnion` + `Set.inter_iUnion`), then
`lintegral_iUnion_le` + `tsum_fintype`. -/
theorem pivotChartCover_matBox_le_sum {m n : ℕ} (t : ℕ) (T : ℝ)
    (f : Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞) :
    ∫⁻ A in matBox m n T ∩ {A : Matrix (Fin m) (Fin n) ℝ | t ≤ A.rank}, f A
      ≤ ∑ ρ : Fin t ↪ Fin m, ∑ κ : Fin t ↪ Fin n,
          ∫⁻ A in matBox m n T ∩ pivotChart ρ κ, f A := by
  have hcov : {A : Matrix (Fin m) (Fin n) ℝ | t ≤ A.rank}
      = ⋃ (ρ : Fin t ↪ Fin m) (κ : Fin t ↪ Fin n), pivotChart ρ κ := pivotLocus_eq_iUnion t
  have hdist : (⋃ (ρ : Fin t ↪ Fin m) (κ : Fin t ↪ Fin n), matBox m n T ∩ pivotChart ρ κ)
      = matBox m n T ∩ ⋃ (ρ : Fin t ↪ Fin m) (κ : Fin t ↪ Fin n), pivotChart ρ κ := by
    simp only [Set.inter_iUnion]
  have hset : matBox m n T ∩ {A : Matrix (Fin m) (Fin n) ℝ | t ≤ A.rank}
      = ⋃ (ρ : Fin t ↪ Fin m) (κ : Fin t ↪ Fin n), matBox m n T ∩ pivotChart ρ κ :=
    (congrArg (fun s => matBox m n T ∩ s) hcov).trans hdist.symm
  rw [hset]
  calc ∫⁻ A in ⋃ ρ : Fin t ↪ Fin m, ⋃ κ : Fin t ↪ Fin n, matBox m n T ∩ pivotChart ρ κ, f A
      ≤ ∑' ρ : Fin t ↪ Fin m, ∫⁻ A in ⋃ κ : Fin t ↪ Fin n, matBox m n T ∩ pivotChart ρ κ, f A :=
        lintegral_iUnion_le _ _
    _ = ∑ ρ : Fin t ↪ Fin m, ∫⁻ A in ⋃ κ : Fin t ↪ Fin n, matBox m n T ∩ pivotChart ρ κ, f A :=
        tsum_fintype _
    _ ≤ ∑ ρ : Fin t ↪ Fin m, ∑' κ : Fin t ↪ Fin n, ∫⁻ A in matBox m n T ∩ pivotChart ρ κ, f A :=
        Finset.sum_le_sum (fun ρ _ => lintegral_iUnion_le _ _)
    _ = ∑ ρ : Fin t ↪ Fin m, ∑ κ : Fin t ↪ Fin n, ∫⁻ A in matBox m n T ∩ pivotChart ρ κ, f A :=
        Finset.sum_congr rfl (fun ρ _ => tsum_fintype _)

/-- **Piece 3 (sub-lemma 1″) — the PRODUCT-level `t = 1` pivot-chart cover (CLOSED, banked plumbing).**
For the front-factor `A₀ : Matrix (Fin m) (Fin n) ℝ` (with `m, n ≥ 1`) times a tail set `s ⊆ β`, the
`matBox ×ˢ s` product integral is bounded by the finite sum, over the `t = 1` pivot charts `(ρ, κ)`, of
the `(matBox ∩ pivotChart ρ κ) ×ˢ s` integrals. Two measure-theoretic hearts: (i) the `{rank = 0} =
{A₀ = 0}` locus is a single volume-null point (`NoAtoms` on the matrix `volume`, needing `Nonempty`
both `Fin m`, `Fin n`), so `matBox ×ˢ s =ᵐ (matBox ∩ {1 ≤ rank}) ×ˢ s`; (ii) `{1 ≤ rank} = ⋃_{ρ,κ}
pivotChart ρ κ` (`pivotLocus_eq_iUnion 1`), distributed over `×ˢ s` (`Set.iUnion_prod_const`) and bounded
by subadditivity (`lintegral_iUnion_le` + `tsum_fintype`). The `A₀.rank = 0 → A₀ = 0` step is proved
locally (Mathlib v4.29 has only the converse `Matrix.rank_zero`): `finrank (range mulVecLin) = 0 ⟹
range = ⊥` (`Submodule.finrank_eq_zero`) `⟹ mulVecLin = 0` (`LinearMap.range_eq_bot`) `⟹ A₀ = 0`
(`Matrix.toLin'` is a `LinearEquiv`, hence injective). Reusable bedrock for the boundary peel's
front-factor stratification at the product level. -/
theorem frontBox_pivotCover_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {β : Type*} [MeasureSpace β] [SigmaFinite (volume : Measure β)]
    (T : ℝ) (s : Set β)
    (f : (Fin m → Fin n → ℝ) × β → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q in matBox m n T ×ˢ s, f q
      ≤ ∑ ρ : Fin 1 ↪ Fin m, ∑ κ : Fin 1 ↪ Fin n,
          ∫⁻ q in (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- `A.rank = 0 → A = 0` over `ℝ` (v4.29 ships only the converse `Matrix.rank_zero`).
  have hrank0 : ∀ A : Matrix (Fin m) (Fin n) ℝ, A.rank = 0 → A = 0 := by
    intro A hA
    have hbot : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hA
    have hml : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hbot
    have hlin : Matrix.toLin' A = Matrix.toLin' (0 : Matrix (Fin m) (Fin n) ℝ) := by
      rw [Matrix.toLin'_apply', Matrix.toLin'_apply', hml, Matrix.mulVecLin_zero]
    exact Matrix.toLin'.injective hlin
  -- (i) the `{rank = 0} = {0}` point is null, so the box integral is the `{1 ≤ rank}` integral.
  have hae : (matBox m n T ×ˢ s)
      =ᵐ[volume] ((matBox m n T ∩ {A : Matrix (Fin m) (Fin n) ℝ | 1 ≤ A.rank}) ×ˢ s) := by
    rw [ae_eq_set]
    refine ⟨?_, ?_⟩
    · -- `(matBox ×ˢ s) \ ((matBox ∩ {1 ≤ rank}) ×ˢ s) ⊆ {0} ×ˢ s`, which is null.
      have hsub : (matBox m n T ×ˢ s)
          \ ((matBox m n T ∩ {A : Matrix (Fin m) (Fin n) ℝ | 1 ≤ A.rank}) ×ˢ s)
          ⊆ ({(0 : Fin m → Fin n → ℝ)} : Set _) ×ˢ s := by
        rintro ⟨A0, b⟩ hq
        rw [Set.mem_diff, Set.mem_prod, Set.mem_prod, Set.mem_inter_iff] at hq
        obtain ⟨⟨hA0, hb⟩, hnot⟩ := hq
        have hr0 : Matrix.rank A0 = 0 := by
          by_contra hne
          exact hnot ⟨⟨hA0, Nat.one_le_iff_ne_zero.mpr hne⟩, hb⟩
        have hz : A0 = 0 := hrank0 A0 hr0
        rw [Set.mem_prod]
        exact ⟨by rw [hz]; exact Set.mem_singleton _, hb⟩
      have hnull : volume (({(0 : Fin m → Fin n → ℝ)} : Set _) ×ˢ s) = 0 := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
      exact measure_mono_null hsub hnull
    · -- `((matBox ∩ {1 ≤ rank}) ×ˢ s) \ (matBox ×ˢ s) = ∅`.
      rw [Set.diff_eq_empty.mpr (Set.prod_mono Set.inter_subset_left (subset_refl s))]
      exact measure_empty
  -- (ii) cover `{1 ≤ rank}` by the `t = 1` pivot charts, distributed over `×ˢ s`.
  -- (`congrArg` under `matBox ∩ ·`, as in `pivotChartCover_matBox_le_sum`, to sidestep the
  -- `rw`-under-binder matching failure on `{A | 1 ≤ A.rank}`.)
  have hcov : {A : Matrix (Fin m) (Fin n) ℝ | 1 ≤ A.rank}
      = ⋃ (ρ : Fin 1 ↪ Fin m) (κ : Fin 1 ↪ Fin n), pivotChart ρ κ := pivotLocus_eq_iUnion 1
  have hdist : (⋃ (ρ : Fin 1 ↪ Fin m) (κ : Fin 1 ↪ Fin n), matBox m n T ∩ pivotChart ρ κ)
      = matBox m n T ∩ ⋃ (ρ : Fin 1 ↪ Fin m) (κ : Fin 1 ↪ Fin n), pivotChart ρ κ := by
    simp only [Set.inter_iUnion]
  have hset : matBox m n T ∩ {A : Matrix (Fin m) (Fin n) ℝ | 1 ≤ A.rank}
      = ⋃ (ρ : Fin 1 ↪ Fin m) (κ : Fin 1 ↪ Fin n), matBox m n T ∩ pivotChart ρ κ :=
    (congrArg (fun st => matBox m n T ∩ st) hcov).trans hdist.symm
  have hcover : (matBox m n T ∩ {A : Matrix (Fin m) (Fin n) ℝ | 1 ≤ A.rank}) ×ˢ s
      = ⋃ (ρ : Fin 1 ↪ Fin m) (κ : Fin 1 ↪ Fin n), (matBox m n T ∩ pivotChart ρ κ) ×ˢ s := by
    rw [hset]; simp only [Set.iUnion_prod_const]
  rw [setLIntegral_congr hae, hcover]
  calc ∫⁻ q in ⋃ (ρ : Fin 1 ↪ Fin m) (κ : Fin 1 ↪ Fin n), (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q
      ≤ ∑' ρ : Fin 1 ↪ Fin m,
          ∫⁻ q in ⋃ κ : Fin 1 ↪ Fin n, (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q :=
        lintegral_iUnion_le _ _
    _ = ∑ ρ : Fin 1 ↪ Fin m,
          ∫⁻ q in ⋃ κ : Fin 1 ↪ Fin n, (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q := tsum_fintype _
    _ ≤ ∑ ρ : Fin 1 ↪ Fin m, ∑' κ : Fin 1 ↪ Fin n,
          ∫⁻ q in (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q :=
        Finset.sum_le_sum (fun ρ _ => lintegral_iUnion_le _ _)
    _ = ∑ ρ : Fin 1 ↪ Fin m, ∑ κ : Fin 1 ↪ Fin n,
          ∫⁻ q in (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q :=
        Finset.sum_congr rfl (fun ρ _ => tsum_fintype _)

/-- **Piece 3 — the per-`(t,ρ,κ)` boundary peel (re-scoped 2026-07-07; a pure COVER inequality).** The
`M` box integral is bounded by the finite sum, over pivot cuts `t = 1..min(M₀,M₁)` and pivot charts
`(ρ,κ)`, of the per-chart peeled integrals `gammaPeelIntegral M t ρ κ c'` (constant `1`: the raw chart
cover needs no analytic factor — decorrelated Codex-confirmed).

**The reduction (all measure theory, no genuinely-new analytic content).**
`routeMLayerBoxIntegral_front_split` (MP front-split `eFront` + integrand identity `frobSq_prod_front`,
clean-three) reduces the LHS to the tail-outer iterated front-factor fibre integral
`∫_{A'∈box(tail)} ∫_{A₀∈box} frobSq(A₀·prod(tailChain M)A')^{−c'}`. The inner `A₀`-box integral is then
covered by the pivot charts at `t = 1`: `{A₀ = 0}` (rank `0`) is a single null point, so `∫_{box}` =
`∫_{box ∩ {1 ≤ rank}}`, and `pivotLocus_eq_iUnion` (`{1 ≤ rank} = ⋃_{ρ,κ} pivotChart ρ κ`) + subadditivity
(`lintegral_iUnion_le`) bound it by `∑_{ρ,κ:t=1} ∫_{box ∩ pivotChart ρ κ} = ∑ gammaPeelIntegral M 1 ρ κ`;
the higher `t = 2..min` terms are extra nonnegative slack. The `t = 0` whole-box term is EXCLUDED — that
is the fix for the circularity (its `sjJointResolution` instance was the induction goal). The faithful
cross-coupled Schur form (`frobSq_schur_block_split`) and the shear are NOT needed here — they live in
`sjJointResolution` (finiteness), which the raw chart integrand feeds.

**RESIDUAL (this named sorry) — the measure-plumbing assembly.** The two mathematical hearts are BANKED:
`pivotChartCover_matBox_le_sum` (the `t = 1` cover of the inner `A₀`-box, above) and `minAdm_cons_zero`
(the `min(M₀,M₁) = 0` edge: there `minAdm M ≤ minAdm (redChain 0 M) = minAdm (Fin.cons 0 _) = 0`, so `hc'`
is unsatisfiable). What remains is standard measure plumbing, cleanest via the PRODUCT route (avoids
per-`A'` integral measurability): (1) `routeMLayerBoxIntegral_front_split`, then
`setLIntegral_prod_symm` to `∫_{matBox ×ˢ box(tail)} frontIntegrand`; (2) the null rank-`0` point — needs
`A.rank = 0 → A = 0` (Mathlib v4.29 has only `Matrix.rank_zero`, the converse; provable via
`rank_eq_finrank_span_cols` + `finrank = 0 → span = ⊥` + `Submodule.mem_bot`) and `NoAtoms` on the matrix
`volume` (nested-Pi instance, needs `Nonempty (Fin M₀)`, `Nonempty (Fin M₁)` from `min ≥ 1`), giving
`volume ((matBox ∩ {rank < 1}) ×ˢ box) = 0`; (3) `iUnion_prod_const` + `lintegral_iUnion_le` at the
product level → `∑_{ρ,κ:t=1} ∫_{(matBox ∩ pivotChart) ×ˢ box}`; (4) `setLIntegral_prod_symm` back =
`∑ gammaPeelIntegral M 1 ρ κ`; (5) `Finset.single_le_sum` embeds the `t = 1` term into the `Icc 1 min`
sum (`1 ∈ Icc 1 min` from `min ≥ 1`). Left a sorry here to avoid an unfinished-plumbing broken build;
the statement is faithful and the path is closed to the two banked lemmas. -/
theorem sjBoundaryPeel (M : Fin (L + 1 + 1 + 1) → ℕ) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    routeMLayerBoxIntegral M (c' : ℝ) 1
      ≤ ∑ t ∈ Finset.Icc 1 (min (M 0) (M 1)),
          ∑ ρ : Fin t ↪ Fin (M 0), ∑ κ : Fin t ↪ Fin (M 1),
            gammaPeelIntegral M t ρ κ (c' : ℝ) := by
  rcases Nat.eq_zero_or_pos (min (M 0) (M 1)) with hmin0 | hminpos
  · -- `min(M₀,M₁) = 0` ⟹ `minAdm M = 0`, so the threshold `hc'` is unsatisfiable.
    exfalso
    have hred : redChain 0 M = Fin.cons (0 : ℕ) (Fin.tail (Fin.tail M)) := by
      conv_lhs => rw [← Fin.cons_self_tail M]
      rw [redChain_cons]
    have hMz : minAdm M = 0 := by
      have hle := minAdm_le_minAdm_redChain_min M
      rw [hmin0, hred, minAdm_cons_zero] at hle
      exact Nat.le_zero.mp hle
    rw [hMz] at hc'
    simp only [Nat.cast_zero, zero_div] at hc'
    exact absurd hc' (not_lt.mpr c'.coe_nonneg)
  · -- `min(M₀,M₁) ≥ 1`: the pure product-level cover inequality.
    have hM0 : 0 < M 0 := lt_of_lt_of_le hminpos (min_le_left _ _)
    have hM1 : 0 < M 1 := lt_of_lt_of_le hminpos (min_le_right _ _)
    -- The `M` box integral IS the product integral over `matBox ×ˢ box(tail)` (MP front-split).
    have hLHS : routeMLayerBoxIntegral M (c' : ℝ) 1
        = ∫⁻ q in matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (tailChain M) 1,
            ENNReal.ofReal ((frobSq (rmatMul q.1 (prod (tailChain M) q.2))) ^ (-(c' : ℝ))) := by
      rw [routeMLayerBoxIntegral]
      have hpre := (measurePreserving_eFront M).setLIntegral_comp_preimage_emb
        (MeasurableEquiv.measurableEmbedding (eFront M))
        (fun q : (Fin (M 0) → Fin (M 1) → ℝ) × Params (tailChain M) =>
          ENNReal.ofReal ((frobSq (rmatMul q.1 (prod (tailChain M) q.2))) ^ (-(c' : ℝ))))
        (matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (tailChain M) 1)
      calc ∫⁻ A in paramsBoxM M 1, ENNReal.ofReal ((frobSq (prod M A)) ^ (-(c' : ℝ)))
          = ∫⁻ A in eFront M ⁻¹' (matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (tailChain M) 1),
              ENNReal.ofReal ((frobSq (rmatMul (eFront M A).1
                (prod (tailChain M) (eFront M A).2))) ^ (-(c' : ℝ))) := by
            rw [eFront_preimage_box]
            refine setLIntegral_congr_fun (measurableSet_paramsBoxM M 1) (fun A _ => ?_)
            rw [frobSq_prod_front M A]
        _ = ∫⁻ q in matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (tailChain M) 1,
              ENNReal.ofReal ((frobSq (rmatMul q.1 (prod (tailChain M) q.2))) ^ (-(c' : ℝ))) := hpre
    -- Each `t = 1` product-chart integral IS `gammaPeelIntegral M 1 ρ κ` (`setLIntegral_prod_symm`).
    have hgamma : ∀ (ρ : Fin 1 ↪ Fin (M 0)) (κ : Fin 1 ↪ Fin (M 1)),
        ∫⁻ q in (matBox (M 0) (M 1) 1 ∩ pivotChart ρ κ) ×ˢ paramsBoxM (tailChain M) 1,
            ENNReal.ofReal ((frobSq (rmatMul q.1 (prod (tailChain M) q.2))) ^ (-(c' : ℝ)))
          = gammaPeelIntegral M 1 ρ κ (c' : ℝ) := by
      intro ρ κ
      unfold gammaPeelIntegral
      rw [Measure.volume_eq_prod (Fin (M 0) → Fin (M 1) → ℝ) (Params (tailChain M)),
        setLIntegral_prod_symm _ (measurable_frontIntegrand M (c' : ℝ)).aemeasurable]
    rw [hLHS]
    refine le_trans (frontBox_pivotCover_le hM0 hM1 1 (paramsBoxM (tailChain M) 1)
      _ (measurable_frontIntegrand M (c' : ℝ))) ?_
    simp only [hgamma]
    exact Finset.single_le_sum
      (f := fun t => ∑ ρ : Fin t ↪ Fin (M 0), ∑ κ : Fin t ↪ Fin (M 1), gammaPeelIntegral M t ρ κ (c' : ℝ))
      (fun t _ => zero_le _) (Finset.mem_Icc.mpr ⟨le_refl 1, hminpos⟩)

/-! ## Pieces 4/5/7 — the joint resolution (finiteness of the joint peeled integral; named sorry) -/

/-- **Aoyagi's `(S,J)` resolution state** (the carrier the invariant is stated over): running layer
index `S` reached, within-layer rank-drop counter `J`, and running-minimum corank
`M(S) = min{M^{(s)} : s ≤ S}`. A minimal stub for the normal-form invariant contract (piece 4); the
full carrier `diag(b)·[E_J|D_J]·∏_{s>S}C^{(s)}` is the mountain's core definitional work, deferred. -/
structure SJState (M : Fin (L + 1) → ℕ) where
  /-- Layers resolved so far. -/
  S : ℕ
  /-- Within-layer rank-drop counter. -/
  J : ℕ
  /-- Running-minimum corank `M(S) = min{M^{(s)} : s ≤ S}`. -/
  runMin : ℕ

/-- The running-minimum corank `M(S) = min{M^{(s)} : 0 ≤ s ≤ S}` — the invariant's block dimension. -/
def sjRunMin (M : Fin (L + 1) → ℕ) (S : ℕ) : ℕ :=
  (Finset.range (S + 1)).inf' (by simp) (fun s => M ⟨min s L, by omega⟩)

/-- **Piece 4 — running-min corank monotonicity (CLOSED, the coarse dimensional consequence).** The
running-minimum corank `M(S)` is monotone non-increasing in `S` (`M(S+1) ≤ M(S)`) — the block
dimension of Aoyagi's `(S,J)` normal-form invariant `⟨∏_{s=1}^L C^{(s)}⟩ = ⟨diag(b₁,…,b_{M(S)})·[E_J |
D_J]·∏_{s>S} C^{(s)}⟩` (§5, p.15) can only shrink as more layers are resolved. This is the honest
dimensional shadow the full carrier refines; the matrix-valued invariant itself (the `[E_J|D_J]`
carrier, preserved across `(S,J)→(S,J+1)` and `S→S+1`) needs the carrier type, deferred to the mountain
build and represented here by the `SJState` / `sjRunMin` stubs. -/
theorem sjRunMin_antitone (M : Fin (L + 1) → ℕ) (S : ℕ) :
    sjRunMin M (S + 1) ≤ sjRunMin M S := by
  unfold sjRunMin
  refine Finset.le_inf' _ _ (fun s hs => ?_)
  exact Finset.inf'_le _ (by rw [Finset.mem_range] at hs ⊢; omega)

/-- **Pieces 4/5/7 — the joint resolution (finiteness of the per-chart peeled integral; named sorry).**
GIVEN box-finiteness for every one-shorter chain (the strong IH — in particular for `redChain t M` and
`tailChain M`), `1 ≤ t ≤ min(M₀,M₁)`, and `c' < ½·minAdm M`, the per-`(t,ρ,κ)`-chart peeled integral
`gammaPeelIntegral M t ρ κ c'` is finite.

**Content (the deferred analytic core; `t ≥ 1` makes it non-circular).** On the chart, the `t×t`
`(ρ,κ)`-pivot minor of `A₀` is a UNIT, so the banked block identity `frobSq_schur_block_split`
(`RouteMSJChartAlgebra`) rewrites the raw integrand `frobSq(A₀·Q)^{−c'}` to the cross-coupled Schur form
`(‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{−c'}`, and the MP shear `D ↦ Γ = D − C A⁻¹ B` (`measurePreserving_shearSub`)
exposes `Γ` as a free variable. The inner `Γ`-integral is then done by the Gram change of variables
`Γ ↦ Γ·Q_b` + the isotropic corank atom `matBox_corank_residual_le` (banked, `origin/genm-sjpeel-blow`),
producing — a.e. in `A'` — the Gram residual `det(Q_b Q_bᵀ)^{−(M₀−t)/2}·P_tail^{−(c'−a/2)}`,
`a=(M₀−t)(M₁−t)` (the exponent shift). The remaining OUTER `A'`-integral is the `(S,J)` double induction
(piece 4 invariant, block dimension `sjRunMin_antitone`; piece 5 charge-update `sjChargeUpdate_accum`),
monomialised on a common resolution; the subordination `sjSubordination` (`a/2 ≤ ½·minAdm(tailChain M)`)
keeps the coupling exponents at or below threshold; the monomial endpoint (piece 7) gives finiteness
(banked `monomialIntegrand_integrable_of_lt`). Because `t ≥ 1` the pivot has positive rank, so the chart
integral genuinely reduces to STRICTLY-shorter chains (`redChain t M`, `tailChain M`) via the IH — unlike
the excluded `t = 0` whole-box term. The standing L≥3 wall (750/5440 charts with `M₁−t > min(deeper
widths)` force `Q_b` rank-deficient, recursing to a deeper boundary) is localised to this statement. -/
theorem sjJointResolution (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (t : ℕ) (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1))
    (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1)) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    gammaPeelIntegral M t ρ κ (c' : ℝ) < ⊤ := by
  sorry

/-! ## Piece 2 — the pivot–Schur chart (L=2 instance CLOSED via banked `rrp`) -/

/-- **Piece 2 — the pivot–Schur chart, L=2 `(r,r,p)` instance (CLOSED).** The unit-triangular
Jacobian-1 reduction `Q₁ C Q₂ = diag(pivot, Γ)` (Aoyagi Lemma 2 / Thm 3) closes the box-finiteness for
the depth-2 `(r,r,p)` family — the banked `routeMBoxThresholdFinite_rrp`, which reshapes the box to the
`SchurCore p r` two-matrix core and fires `core_schurGen_lt_top`. The witness that piece 2's chart
reduction is inhabited at the base of the recursion. The general-`L` pivot-Schur chart (the
correct-block-dimension `Q₁ C^{(s)} Q₂ = diag(pivot, Γ)` for each `s`) is NOT a standalone
box-finiteness claim — it is the internal change of variables inside `sjBoundaryPeel` (piece 3); it is
stated there rather than duplicated as a redundant restatement of the inductive step. -/
theorem sjPivotSchurChart_rrp (r p : ℕ) :
    RouteMBoxThresholdFinite (![r, r, p] : Fin 3 → ℕ) :=
  routeMBoxThresholdFinite_rrp r p

/-! ## The recursion spine — the two contracts + the sorry-free wrapper -/

/-- **The `(S,J)` inductive STEP contract.** For a `≥ 3`-width chain `M`, GIVEN box-finiteness for
every one-shorter chain (the strong IH), box-finiteness holds for `M`. Discharged by
`sjResolutionStep_proof` (peel + joint resolution). -/
def SJStepHyp : Prop :=
  ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ),
    (∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') → RouteMBoxThresholdFinite M

/-- **The `L = 1` (single free matrix) base contract.** Box-finiteness for every two-width chain. -/
def SJBaseHyp : Prop := ∀ M : Fin 2 → ℕ, RouteMBoxThresholdFinite M

/-- **The `L = 0` vacuous base (CLOSED).** For a one-width chain `minAdm M = 0`, so the threshold
`c' < ½·minAdm M = 0` is unsatisfiable for `c' : NNReal` — `RouteMBoxThresholdFinite M` holds
vacuously. -/
theorem routeMBoxThresholdFinite_base0 (M : Fin (0 + 1) → ℕ) : RouteMBoxThresholdFinite M := by
  intro c' hc'
  have h0 : minAdm M = 0 := by
    have hz : ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat = 0 := by
      obtain ⟨T, _, hT⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
      rw [hT]; simp [Mval]
    unfold minAdm; exact hz
  rw [h0] at hc'
  simp only [Nat.cast_zero, zero_div] at hc'
  exact absurd hc' (not_lt.mpr c'.coe_nonneg)

/-- **The `(S,J)` inductive step, DISCHARGED (composes piece 3 + pieces 4/5/7).** The peel
(`sjBoundaryPeel`) bounds the `M` box integral by a finite sum of per-chart joint peeled integrals; each
is finite by the joint resolution (`sjJointResolution`); a finite sum of finite terms is finite. NOT a
bare sorry — the analytic content lives entirely in the two named pieces it composes. -/
theorem sjResolutionStep_proof : SJStepHyp := by
  intro L M hIH c' hc'
  -- goal: routeMLayerBoxIntegral M c' 1 < ⊤
  refine lt_of_le_of_lt (sjBoundaryPeel M c' hc') ?_
  refine ENNReal.sum_lt_top.mpr (fun t ht => ?_)
  rw [Finset.mem_Icc] at ht
  refine ENNReal.sum_lt_top.mpr (fun ρ _ => ?_)
  refine ENNReal.sum_lt_top.mpr (fun κ _ => ?_)
  exact sjJointResolution M hIH t ρ κ ht.1 ht.2 c' hc'

/-- **The sorry-free, axiom-clean WRAPPER.** Strong induction on the chain arity: `L = 0` vacuous
(`routeMBoxThresholdFinite_base0`), `L = 1` the base contract, `L ≥ 2` the step contract (its strong IH
is the induction hypothesis at the one-lower arity). Carries NO analytic content of its own — mirrors
`core_schurGen_lt_top`. -/
theorem routeMBoxThresholdFinite_of_step (hstep : SJStepHyp) (hbase1 : SJBaseHyp) :
    ∀ {L : ℕ} (M : Fin (L + 1) → ℕ), RouteMBoxThresholdFinite M := by
  have key : ∀ n : ℕ, ∀ M : Fin (n + 1) → ℕ, RouteMBoxThresholdFinite M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | _ | k
      · intro M; exact routeMBoxThresholdFinite_base0 M
      · intro M; exact hbase1 M
      · intro M; exact hstep M (fun M' => ih (k + 1) (by omega) M')
  intro L M; exact key L M

/-! ## `L = 1` base (single free matrix; the free-matrix Morse integral, PROVED) -/

/-- **The single free matrix loss is the sum of squares of its flat coordinates.** For a two-width chain
`M : Fin 2`, `prod M A = A₀` (`prod_one_layer`), and the entries of `A₀` are exactly the flat coordinates
`paramsEquivFlat M A` (`FlatIdx M` collapses to the single layer `s = 0`), so
`frobSq (prod M A) = ∑ k, (paramsEquivFlat M A k)²`. -/
theorem frobSq_prod_eq_flatSum (M : Fin 2 → ℕ) (A : Params M) :
    frobSq (prod M A) = ∑ k, (paramsEquivFlat M A k) ^ 2 := by
  have hflat : ∑ k, (paramsEquivFlat M A k) ^ 2
      = ∑ idx : FlatIdx M, (A idx.1.1 idx.1.2 idx.2) ^ 2 := by
    refine (Fintype.sum_equiv (Fintype.equivFin (FlatIdx M))
      (fun idx => (A idx.1.1 idx.1.2 idx.2) ^ 2)
      (fun k => (paramsEquivFlat M A k) ^ 2) (fun idx => ?_)).symm
    dsimp only; rw [paramsEquivFlat_decodeM]
  have hsig : ∑ idx : FlatIdx M, (A idx.1.1 idx.1.2 idx.2) ^ 2
      = ∑ i : Fin (M 0), ∑ j : Fin (M (Fin.last 1)), (A 0 i j) ^ 2 := by
    rw [Fintype.sum_sigma, Fintype.sum_sigma, Fin.sum_univ_one]; rfl
  rw [hflat, hsig]
  unfold frobSq
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
    rw [prod_one_layer M A i j]))

/-- **The Morse box integral is finite in any positive dimension below `N/2`.** The `Fin N`-form of the
banked `sumSqND_box_lt_top` (which is stated at `Fin (m+1)`): `∫_{[−1,1]^N} (∑ᵢ xᵢ²)^{−c'} < ⊤` whenever
`0 < N` and `c' < N/2`. Peels `N = m+1` (`0 < N`) and applies `sumSqND_box_lt_top`. -/
theorem morseBox_sumSq_lt_top (N : ℕ) (hN : 0 < N) (c' : ℝ) (hc' : c' < (N : ℝ) / 2) :
    ∫⁻ x in morseBox N 1, ENNReal.ofReal ((∑ i, (x i) ^ 2) ^ (-c')) < ⊤ := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact sumSqND_box_lt_top m 1 one_pos c' (by push_cast at hc' ⊢; linarith)

/-- **The `L = 1` (single free matrix) Morse base (PROVED).** For every two-width chain `M : Fin 2`,
`RouteMBoxThresholdFinite M` holds: the box integral `∫_{A∈paramsBoxM M 1} frobSq(prod M A)^{−c'}` is
finite for `c' < ½·minAdm M = ½·M₀M₁`. Since `prod M A = A₀`, the integrand is the free-matrix Morse
integral `∫_{[−1,1]^{M₀M₁}} (∑ x²)^{−c'}`: transport the `Params M` box through the measure-preserving
flattening `paramsEquivFlat M` (`frobSq_prod_eq_flatSum`, `flatDim M = M₀M₁`) to the `Fin (M₀M₁)` Morse
box, finite by `morseBox_sumSq_lt_top` (threshold `M₀M₁/2`). The degenerate `M₀M₁ = 0` case is vacuous
(the threshold `c' < 0` is unsatisfiable for `c' : NNReal`). -/
theorem sjBase1_freeMatrix : SJBaseHyp := by
  intro M c' hc'
  rw [minAdm_two_eq] at hc'
  rcases Nat.eq_zero_or_pos (M 0 * M 1) with hz | hpos
  · rw [hz] at hc'; simp only [Nat.cast_zero, zero_div] at hc'
    exact absurd hc' (not_lt.mpr c'.coe_nonneg)
  rw [routeMLayerBoxIntegral]
  have hmpF := measurePreserving_paramsEquivFlat M
  have hpre := hmpF.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.measurableEmbedding (paramsEquivFlat M))
    (fun x => ENNReal.ofReal ((∑ k, (x k) ^ 2) ^ (-(c' : ℝ))))
    (morseBox (flatDim M) 1)
  have hbox : (paramsEquivFlat M) ⁻¹' (morseBox (flatDim M) 1) = paramsBoxM M 1 :=
    paramsEquivFlat_preimage_paramsBoxM M 1
  have hrw : ∫⁻ A in paramsBoxM M 1, ENNReal.ofReal ((frobSq (prod M A)) ^ (-(c' : ℝ)))
      = ∫⁻ x in morseBox (flatDim M) 1, ENNReal.ofReal ((∑ k, (x k) ^ 2) ^ (-(c' : ℝ))) := by
    calc ∫⁻ A in paramsBoxM M 1, ENNReal.ofReal ((frobSq (prod M A)) ^ (-(c' : ℝ)))
        = ∫⁻ A in (paramsEquivFlat M) ⁻¹' (morseBox (flatDim M) 1),
            ENNReal.ofReal ((∑ k, (paramsEquivFlat M A k) ^ 2) ^ (-(c' : ℝ))) := by
          rw [hbox]
          refine setLIntegral_congr_fun (measurableSet_paramsBoxM M 1) (fun A _ => ?_)
          rw [frobSq_prod_eq_flatSum M A]
      _ = ∫⁻ x in morseBox (flatDim M) 1, ENNReal.ofReal ((∑ k, (x k) ^ 2) ^ (-(c' : ℝ))) := hpre
  rw [hrw]
  have hfd : flatDim M = M 0 * M 1 := by rw [flatDim_eq, Fin.sum_univ_one]; rfl
  refine morseBox_sumSq_lt_top (flatDim M) (by rw [hfd]; exact hpos) (c' : ℝ) ?_
  rw [hfd]; exact hc'

/-! ## The final assembly -/

/-- **The general-`L` R1-UPPER box-finiteness `RouteMBoxThresholdFinite M`, ∀L.** The final target the
7-piece `(S,J)` resolution discharges: the layer-product box integral is finite below the geometric
threshold `½·minAdm M`, for an arbitrary width vector `M`. Assembled from the sorry-free wrapper applied
to the step (`sjResolutionStep_proof`, = piece 3 ∘ pieces 4/5/7) and the `L = 1` base
(`sjBase1_freeMatrix`, CLOSED). Carries exactly the two remaining genuinely-new analytic sorries:
`sjBoundaryPeel` (3, whose CLOSED outer front-split `routeMLayerBoxIntegral_front_split` leaves only the
per-tail-parameter fibre bound) and `sjJointResolution` (4/5/7). Once these land, this discharges the
bare sorry `routeMCore_threshold_lt_top` (`RouteMSchur.lean`) via `routeMCore_threshold_lt_top_of_box`. -/
theorem routeMBoxThresholdFinite_sjResolution (M : Fin (L + 1) → ℕ) :
    RouteMBoxThresholdFinite M :=
  routeMBoxThresholdFinite_of_step sjResolutionStep_proof sjBase1_freeMatrix M

/-! ## API pins (durable contracts for the banked machinery the mountain consumes) -/

section APIPins

-- Piece 1 fibre engine (L=2 corank-family fibre integral bound).
example {p n q : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) (hq : 1 ≤ q) (T : ℝ) (hT : 0 < T)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < p / 2) (Y : Fin n → Fin q → ℝ) :
    ∫⁻ X in matBox p n T, ENNReal.ofReal ((frobSq (rmatMul X Y)) ^ (-c'))
      ≤ fibreConst p n q T c' * ENNReal.ofReal ((frobSq Y) ^ (-c')) :=
  fibre_lintegral_mul_le hp hn hq T hT c' hc0 hc' Y

-- Piece 2 corank recursion wrapper (the abstract `SchurRecStep` ⟹ `SchurCore` finiteness).
example (p : ℕ) (lam : ℕ → ℝ) (hlam : SchurThreshold p lam) (hstep : SchurRecStep p lam)
    (r : ℕ) (c' : ℝ) (hc0 : 0 < c') (hc' : c' < lam r) (T : ℝ) (hT : 0 < T) :
    SchurCore p r c' T :=
  core_schurGen_lt_top p lam hlam hstep r c' hc0 hc' T hT

-- Piece 6 charge-budget recursion (the layer-peeling `minAdm` recursion, banked).
example (M : Fin (L + 1) → ℕ) : minAdmRec M = minAdm M := minAdmRec_eq_minAdm M

-- Piece 7 free-matrix Morse endpoint (the `n`-dim sum-of-squares box integral, banked).
example (m : ℕ) (T : ℝ) (hT : 0 < T) (c' : ℝ) (hc' : c' < (m + 1) / 2) :
    ∫⁻ x in morseBox (m + 1) T, ENNReal.ofReal ((∑ i, (x i) ^ 2) ^ (-c')) < ⊤ :=
  sumSqND_box_lt_top m T hT c' hc'

end APIPins

end DLNFibre.DLN.RLCT
