import DLNFibre.DLN.RLCT.Validate.RouteMBoxThresholdRRP
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit

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
boundary peel `sjBoundaryPeel`) with pieces 4/5/7 (the joint resolution `sjJointResolution`): the peel
bounds the `M` box integral by a finite sum of per-chart joint peeled integrals, each finite by the
joint resolution. So the only sorries feeding the final `routeMBoxThresholdFinite_sjResolution` are the
genuinely-new analytic pieces `sjBoundaryPeel` (3), `sjJointResolution` (4/5/7), and `sjBase1_freeMatrix`
(the `L = 1` Morse base).

## The 7 pieces (dependency order; CLOSED vs named-sorry)

1. **Local comparability / units** — `sjLocalComparability`, `paramsBoxM_volume_lt_top`. CLOSED (pure
   measure theory + compactness). The banked L=2 fibre engine is `MatMulFibre.fibre_lintegral_mul_le`.
2. **Pivot–Schur chart** — `sjPivotSchurChart_rrp` (the L=2 `(r,r,p)` instance, CLOSED via the banked
   `routeMBoxThresholdFinite_rrp`). The general-`L` chart is the internal change of variables of piece 3
   (`sjBoundaryPeel`), stated there — not duplicated as a standalone claim.
3. **Boundary blow-up / peel** (LOAD-BEARING analytic core) — `sjBoundaryPeel`. Named sorry. The cert's
   exact per-step identity `J ≍ P_tail^{−(c'−a/2)}·P_full^{−a/2}` at cut `t`, `a = (M₀−t)(M₁−t)`.
4. **`(S,J)` normal-form invariant** — the block-dimension consequence `sjRunMin_antitone` (running-min
   corank `M(S)` monotone) is CLOSED; the full matrix-valued invariant needs the `[E_J|D_J]` carrier
   (`SJState`/`sjRunMin` stubs), folded into `sjJointResolution`, deferred to the mountain build.
5. **Jacobian / charge-update** — `sjChargeUpdate_accum` (the additive `Mval` charge, CLOSED via banked
   `Mval_decompose`) + the exponent bookkeeping folded into `sjJointResolution`.
6. **Charge-budget inequality** (combinatorial core) — `sjChargeBudget_recursion`/`_le`/`_binding`,
   `sjSubordination`. CLOSED, reusing `LayerSplit_value_eq_minAdm` / `minAdmRec_eq_minAdm`, modulo the
   ONE named residual `minAdm_leadWidth_mono` (leading-width monotonicity; a clean combinatorial fact,
   numerically verified, deferred to a later tide).
7. **Monomial integrability assembly** (analytic endpoint) — `sjJointResolution` (bundles the
   monomialised finiteness). Named sorry. The generic monomial finiteness it consumes is banked
   (`Case222Cover.monomialIntegrand_integrable_of_lt`); the monomialisation is the new content.

## S2 / axiom hygiene
The wrapper introduces NO measure-theoretic content of its own and NO new axiom. The deferred content
sits in the named contracts; `#print axioms routeMBoxThresholdFinite_of_step` is clean-three. The final
`routeMBoxThresholdFinite_sjResolution` carries exactly the three genuinely-new analytic sorries.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

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
`minAdmRec_eq_minAdm`); the ONE residual is the leading-width monotonicity `minAdm_leadWidth_mono`. -/

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

/-- **Piece 6 — leading-width monotonicity of `minAdm` (the ONE named residual).** Increasing the
leading width of a chain (all else fixed) does not decrease `minAdm`:
`p ≤ q → minAdm (Fin.cons p rest) ≤ minAdm (Fin.cons q rest)`. Numerically verified (0 violations,
`sj_check.py`); the recursion is NOT termwise (a larger leading width both raises the block terms and
widens the admissible pivot range), so this is genuine — if modest — combinatorial work, deferred to a
later tide. Everything else in piece 6 is banked. -/
theorem minAdm_leadWidth_mono {L : ℕ} (p q : ℕ) (hpq : p ≤ q) (rest : Fin (L + 1) → ℕ) :
    minAdm (Fin.cons p rest) ≤ minAdm (Fin.cons q rest) := by
  sorry

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

/-! ## Piece 3 — the boundary blow-up / peel (the joint peeled integral, LOAD-BEARING) -/

/-- **The top-`t`-rows squared-Frobenius norm** `∑_{i<t} ∑_j Pᵢⱼ²`. For the tail product
`P = A₁·A₂···A_{L−1}`, its top `t` rows are `(top t rows of A₁)·A₂···`, so `frobSqTopRows t P` is the
reduced-chain loss `P_tail = ‖(t,M₂,…,M_L)-product‖²`. -/
noncomputable def frobSqTopRows (t : ℕ) {m n : ℕ} (P : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, (if (i : ℕ) < t then (P i j) ^ 2 else 0)

theorem frobSqTopRows_nonneg (t : ℕ) {m n : ℕ} (P : Fin m → Fin n → ℝ) :
    0 ≤ frobSqTopRows t P := by
  unfold frobSqTopRows
  refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
  split <;> positivity

/-- **The joint peeled box integral at cut `t`, exponent `c'`** — the cert's exact per-step object.
Over the tail parameters `A ∈ paramsBoxM (tailChain M) 1`, the JOINT integrand

    P_tail^{−(c'−a/2)} · P_full^{−a/2},   a = (M₀−t)(M₁−t),

with `P_tail = frobSqTopRows t (prod (tailChain M) A)` the reduced tail-chain loss (top `t` rows of the
tail product) and `P_full = frobSq (prod (tailChain M) A)` the FULL remaining product loss (the coupling
factor). Crucially the two factors read the SAME parameters `A` — the object is JOINT, NOT the (unsound)
product of independent single-chain integrals (design-cert §3, §ADDENDUM). -/
noncomputable def jointPeelIntegral (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ A in paramsBoxM (tailChain M) 1,
    ENNReal.ofReal
      ((frobSqTopRows t (prod (tailChain M) A)) ^ (-(c' - (peelExp M t : ℝ) / 2))
        * (frobSq (prod (tailChain M) A)) ^ (-((peelExp M t : ℝ) / 2)))

/-- **Piece 3 — the boundary peel (LOAD-BEARING analytic core; named sorry).** The `M` box integral is
bounded by a FINITE constant times the finite sum, over pivot charts `t ≤ min(M₀,M₁)`, of the joint
peeled integral. Content: on the pivot chart with a `t×t` invertible front block, Aoyagi's Lemma-2
Jacobian-1 reduction `Q₁A₀Q₂ = diag(A₀^{[t]}, Γ)` exposes the corank block `Γ : (M₀−t)×(M₁−t)`; radial
blow-up `Γ = zV` (Jacobian `z^{a−1}`) integrates out the front factor `A₀` and, using
`g²+h² = ‖A₁·A₂···‖²`, collapses to `P_tail^{−(c'−a/2)}·P_full^{−a/2}` (`r1u_identity.py`, exact). The
finite chart cover + the Beta constant `½·B(a/2,c'−a/2)` supply the finite `C`. The internal chart step
is piece 2 (`sjPivotSchurChart`). -/
theorem sjBoundaryPeel (M : Fin (L + 1 + 1 + 1) → ℕ) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      routeMLayerBoxIntegral M (c' : ℝ) 1
        ≤ ∑ t ∈ Finset.range (min (M 0) (M 1) + 1), C * jointPeelIntegral M t (c' : ℝ) := by
  sorry

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

/-- **Pieces 4/5/7 — the joint resolution (finiteness of the joint peeled integral; named sorry).**
GIVEN box-finiteness for every one-shorter chain (the strong IH — in particular for `redChain t M` and
`tailChain M`) and `c' < ½·minAdm M`, the joint peeled integral is finite. Content: the simultaneous
rank-flag `(S,J)` double induction (piece 4 invariant, whose block dimension is `sjRunMin_antitone`;
piece 5 charge-update `sjChargeUpdate_accum`) monomialises `P_tail^{−(c'−a/2)}·P_full^{−a/2}` on a
common resolution; the
subordination `sjSubordination` (`a/2 ≤ ½·minAdm(tailChain M)`, non-strict — see its caveat: strict
fails at some `a>0` cuts, so a gentle minimal-`a` cut must be chosen) keeps the coupling exponents at or
below threshold on the shared divisors; the monomial integrability endpoint (piece 7) then gives finiteness
(`∫∏|uᵢ|^{αᵢ} < ∞ ⟺ αᵢ > −1`, banked as `monomialIntegrand_integrable_of_lt`). This is the standing
L≥3 wall, now localised to this single statement. -/
theorem sjJointResolution (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (t : ℕ) (ht : t ≤ min (M 0) (M 1)) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    jointPeelIntegral M t (c' : ℝ) < ⊤ := by
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
  obtain ⟨C, hCne, hbound⟩ := sjBoundaryPeel M c' hc'
  refine lt_of_le_of_lt hbound ?_
  refine ENNReal.sum_lt_top.mpr (fun t ht => ?_)
  rw [Finset.mem_range] at ht
  exact ENNReal.mul_lt_top hCne.lt_top (sjJointResolution M hIH t (by omega) c' hc')

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

/-! ## `L = 1` base (single free matrix; named sorry — the free-matrix Morse integral) -/

/-- **The `L = 1` (single free matrix) Morse base (named sorry).** For a two-width chain `M : Fin 2`,
`prod M A = A₀` and the box integral is `∫_{A₀∈box} ‖A₀‖^{−2c'}` — finite for `c' < ½·M₀M₁ = ½·minAdm M`
(the free-matrix Morse integral, `∫_{[−1,1]^d} |x|^{−2c'} < ∞ ⟺ 2c' < d = M₀M₁`). Reducible to the
banked `sumSqND_box_lt_top` via a general `matBox M₀ M₁ ≃ᵐ morseBox (M₀·M₁)` reindex; the 2×2 template
is `MatMulFibre.frobSq22_box_lt_top`. Clean bounded plumbing, deferred. -/
theorem sjBase1_freeMatrix : SJBaseHyp := by
  sorry

/-! ## The final assembly -/

/-- **The general-`L` R1-UPPER box-finiteness `RouteMBoxThresholdFinite M`, ∀L.** The final target the
7-piece `(S,J)` resolution discharges: the layer-product box integral is finite below the geometric
threshold `½·minAdm M`, for an arbitrary width vector `M`. Assembled from the sorry-free wrapper applied
to the step (`sjResolutionStep_proof`, = piece 3 ∘ pieces 4/5/7) and the `L = 1` base
(`sjBase1_freeMatrix`). Carries exactly the three genuinely-new analytic sorries: `sjBoundaryPeel` (3),
`sjJointResolution` (4/5/7), `sjBase1_freeMatrix` (`L = 1` Morse). Once these land, this discharges the
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
