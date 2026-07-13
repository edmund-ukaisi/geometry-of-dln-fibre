import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec
import DLNFibre.DLN.RLCT.Validate.RouteMSJAdm
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagCore
import DLNFibre.DLN.RLCT.Validate.MinAdmPermInvariance
import DLNFibre.DLN.RLCT.Validate.RouteMSJBaseHyp
import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplit

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedStep` — the `DecoratedStepHyp` assembly skeleton (#5)

**Thread `genm-sj5-stepasm` (aoyagi-full Stage 2), CONTRACT-FIRST assembly.** This module wires the
outer shape of the `(S,J)` decorated descent STEP — a term of `DecoratedStepHyp adm` for the concrete
admissibility predicate `adm` (`RouteMSJAdm`) — leaving the three analytic branches (and the cover
connector) as PRECISELY-STATED, NAMED `sorry`-holes whose content is built on other lanes. It is a
SPECIFY/audit artifact: the deliverable is a TYPECHECKING skeleton + a seam report, NOT filled proofs.

## The dispatch structure (what this skeleton makes explicit)

`DecoratedStepHyp adm` obligation: for a `≥ 3`-width chain `M`, GIVEN the decorated strong IH (box
finiteness for every `adm`-admissible decoration of every one-shorter chain), every `adm`-admissible
`D : SJDecoration M` is finite below `carrierThreshold M = ½·minAdm M`.

The dispatch is NOT a flat 3-way case on `D`. It is a **2-way split on the decide-checkable Nat key
`M 1 < deepTailMin M`** (waist) vs `≥` (good), where `deepTailMin M = ⨅_{i≥2} M i = min (M₂,…,M_last)`.
This key — NOT the binding-cut hpiv — is the SOUND gate (waistpin #172, decide-checked, 1188
counterexamples): keying on `minAdm (redChain (bindingCut M) M) ≤ bindingCut M · tailMinWidth M` is BUGGY,
because when `bindingCut M = 0` (356 waist chains, e.g. `(1,1,2),(1,2,3)`) it reads `≤ 0` trivially and
routes WAIST chains into the GOOD branch, where the head-split DIVERGES. The "good" half further
decomposes over the deeper-flag singular shells (a per-shell split, INSIDE the outer tail integral, NOT a
per-`D` case):

* **good** (`hgood : deepTailMin M ≤ M 1`) — the per-cut pivot bound `minAdm (redChain u M) ≤
  u · deepTailMin M` (∀ u, the banked `minAdm_redChain_le_deepTailMin`, proved by permuting the argmin
  tail width to position 1 via `minAdm_comp_perm` then `minAdm_le_mul_head`) DERIVES the per-cut hpiv
  `minAdm (redChain (t+j) M) ≤ (t+j) · tailMinWidth M` each shell needs — because on the good side
  `tailMinWidth M = deepTailMin M` — so there is NO per-cut/binding-cut gap. `D.integral c'` peels at the
  binding cut and covers the outer tail by the singular shells `singularShell ε r jf`, `jf : Fin (r+1)`,
  `r = min (M₀−t★) (M₁−t★)` (`singularShell_iUnion` exhaustive). Each shell contribution
  `shellSpineIntegrand M t★ κ ε r jf c'` is bounded:
  - **strict** `jf < r` → hole (a) `deeperFlagStrictShell_finite` (the head-split domination
    `deeperFlag_shell_le` → `cornerComparator … .integral`, finite by the DECORATED IH via
    `cornerComparator_adm`);
  - **saturated** `jf = r` → hole (b) `deeperFlagSaturatedShell_finite` (the lumped full-flag shell,
    discharged via the arity IH at reduced arity — NOT the head-split, whose off-sector block
    degenerates at `jf = r`, see seam note below).
  Summing the finitely-many shells (`lintegral_le_sum_finCover` + `ENNReal.sum_lt_top`) and the peel
  is the **cover connector**, hole (d) `deeperFlagGood_finite`.
* **waist** (`hwaist : M 1 < deepTailMin M`, the deep-tail product has full row rank) —
  `deeperFlag_shell_le` is inapplicable (its per-cut hpiv fails). The chain does NOT reduce to
  the 3-width box finiteness `routeMBoxThresholdFinite_mnp` — that is a PROVEN NO-GO for `L ≥ 1` (witness
  `minAdm (4,2,3,3) = 5` but `minAdm (4,2,3) = 6`, so `I(4,2,3,3)` diverges on `c' ∈ (5/2, 3)` while the
  3-width `I(4,2,3)` is finite there; no `c'`-uniform 3-width domination can hold — the deep charge is
  higher-dimensional). 3-width is only the BASE, never a step target. The waist fires WITH nontrivial
  decoration (front-good + deep pinch → decorated waist), in two sub-cases:
  - **`M₁ ≥ 2`** — hole (c) `deeperFlagWaist_finite`, ROUTE-A **SVD-qPeel + REORIENTATION** (O2 verdict):
    deep-layer SVD → the banked `qPeelIntegral` (`#156` = its `L = 0` base), consuming the decoration
    BEFORE a plain REORIENTATION to a good end (every `≥ 4`-width chain has one; reversal CoV
    `I(M) = I(rev M)`, `minAdm` half-banked via `minAdm_comp_perm`) — the SVD-qPeel consuming the
    decoration first sidesteps waistpin's decoration-transport obstruction. Route-(b) drop-front is DEAD:
    its eigenvalue-profile weight `J_c` is NON-admissible (Hölder `β < 3/4 < 1` needed), a red herring.
    New labour: one deep-layer Gram-spectral/Weyl-Jacobian CoV brick + the reversal-CoV lemma (bounded,
    no wall); NO new decorated-IH predicate (a simplification vs route-(b)).
  - **`M₁ = 1`** (any `L`) — hole (e) `deeperFlagWaistM1_finite`, reversal-FREE and UNCONDITIONAL: the
    loss factorizes `frobSq (Γ · Q) = ‖Γ‖² · ‖Q‖²` for ANY `D`, so the integral splits as a front Morse
    integral × the dropHead-tail IH. A standalone lemma.

The main `decoratedStepHyp_dispatch : DecoratedStepHyp adm` is itself `sorry`-free — the exhaustive
`by_cases (M 1 < deepTailMin M)` (waist/good) with a further `by_cases (M 1 = 1)` inside waist,
dispatching to holes (e), (c), (d). All analytic content lives in the five holes; the banked
`deepTailMin` + `minAdm_redChain_le_deepTailMin` (the per-cut pivot bound) are sorry-free.

## The j ≤ r vs j < r seam (report point i)

`deeperFlag_shell_le` (`RouteMSJDeeperFlagCore`) is typed with `hj : j ≤ min (M₀−t) (M₁−t)` — the
`≤` ALREADY admits `j = r`, so at the STATEMENT level there is NO quantifier gap between strict and
saturated. The two are separated for a PROOF-CONTENT reason, not a typing reason: at `j = r` the peeled
off-sector block has a zero dimension (`M₀−(t+r) = 0` or `M₁−(t+r) = 0` when `r = min(M₀−t,M₁−t)`), so
the head-split domination (Bricks F, D) is degenerate there; the saturated shell is instead closed by
the arity IH. Hence hole (b) is a SEPARATE branch. (This proof-content claim is inherited from the crux
lane's `deeperFlag_spineToCore`; flagged for its confirmation, not verified here.)

## Status

CONTRACT-FIRST skeleton, partially filled: hole (e) `deeperFlagWaistM1_finite` (waist-`M₁=1`) is
FILLED sorry-free (axiom-clean `[propext, Classical.choice, Quot.sound]`), leaving 4 named `sorry`-holes
(a=strict, b=saturated, d=good-connector, c=waist-reversal); main dispatch sorry-free. Hole (b) carries a
newly-added `hcT : c' < carrierThreshold M` (threaded from the dispatch at final wiring). UNTRACKED, NOT
wired into `DLNFibre.lean`/`AxCheck` — the canonical library stays 0-sorry. The remaining sorries are the
explicit deliverable on this tide branch.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## The sound dispatch key + the per-cut pivot bound (banked, sorry-free) -/

/-- **The deep-tail width minimum** `deepTailMin M = ⨅_{i≥2} M i = min (M₂,…,M_last)` — the tail widths
STRICTLY past the pivot layer `M₁` (excludes `M₁`, unlike `tailMinWidth = min (M₁,…,M_last)`). The
decide-checkable SOUND waist key is `M 1 < deepTailMin M` (waistpin #172): keying on the binding-cut
hpiv is buggy (`bindingCut M = 0` routes waist chains to the good branch). -/
def deepTailMin (M : Fin (L + 1 + 1 + 1) → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin (L + 1))).inf' ⟨0, Finset.mem_univ 0⟩ (fun i => M i.succ.succ)

/-- **The head-times-tail-minimum bound `minAdm N ≤ N₀ · ⨅_{i≥1} Nᵢ`**, via permutation invariance:
move the argmin tail width to position 1 (`minAdm_comp_perm` at `Equiv.swap 1 i★.succ`, fixing `0`),
then apply the head bound `minAdm_le_mul_head`. -/
theorem minAdm_le_head_mul_tailInf {k : ℕ} (N : Fin (k + 1 + 1) → ℕ) :
    minAdm N ≤ N 0 * (Finset.univ : Finset (Fin (k + 1))).inf'
      ⟨0, Finset.mem_univ 0⟩ (fun i => N i.succ) := by
  classical
  obtain ⟨istar, -, histar⟩ := Finset.exists_mem_eq_inf'
    (⟨0, Finset.mem_univ 0⟩ : (Finset.univ : Finset (Fin (k + 1))).Nonempty)
    (fun i => N i.succ)
  rw [histar]
  calc minAdm N = minAdm (N ∘ Equiv.swap (1 : Fin (k + 1 + 1)) istar.succ) :=
        (minAdm_comp_perm _ N).symm
    _ ≤ (N ∘ Equiv.swap (1 : Fin (k + 1 + 1)) istar.succ) 0
          * (N ∘ Equiv.swap (1 : Fin (k + 1 + 1)) istar.succ) 1 := minAdm_le_mul_head _
    _ = N 0 * N istar.succ := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne Fin.zero_ne_one (Fin.succ_ne_zero istar).symm,
          Equiv.swap_apply_left]

/-- **The per-cut pivot bound `minAdm (redChain u M) ≤ u · deepTailMin M`** (∀ u) — the GOOD-branch
per-cut hpiv source. `redChain u M = (u, M₂,…,M_last)`, so its position-0 width is `u` and its
tail minimum (indices `≥ 1`) is `deepTailMin M`; `minAdm_le_head_mul_tailInf` gives the bound. On the
good side (`deepTailMin M ≤ M 1`) `tailMinWidth M = deepTailMin M`, so this is exactly the per-cut hpiv
`minAdm (redChain (t+j) M) ≤ (t+j) · tailMinWidth M` that `deeperFlag_shell_le` requires. -/
theorem minAdm_redChain_le_deepTailMin (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) :
    minAdm (redChain u M) ≤ u * deepTailMin M := by
  have h := minAdm_le_head_mul_tailInf (redChain u M)
  rw [redChain_zero] at h
  have hfun : (fun i : Fin (L + 1) => (redChain u M) i.succ) = (fun i => M i.succ.succ) := by
    funext i; exact redChain_succ u M i
  rw [hfun] at h
  exact h

/-! ## The two clean bricks for hole (e) (`M₁ = 1`), sorry-free -/

/-- **Rank-1 Frobenius factorization at a width-1 middle** `frobSq (rmatMul Γ Z) = frobSq Γ · frobSq Z`
when the shared index is `Fin 1`. `Γ · Z` is the outer product `(Γ ·₀) ⊗ (Z ₀·)`, whose squared Frobenius
norm factors. The loss-factorization brick for the `M₁ = 1` waist sub-case (`Γ · prod (dropHead M)` is
rank-1 through the width-1 bottleneck). -/
theorem frobSq_rmatMul_mid_one {a q : ℕ} (Γ : Fin a → Fin 1 → ℝ) (Z : Fin 1 → Fin q → ℝ) :
    frobSq (rmatMul Γ Z) = frobSq Γ * frobSq Z := by
  simp only [frobSq, rmatMul, Fin.sum_univ_one]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- **`minAdm M ≤ minAdm (dropHead M)` when `M₁ = 1`** — the `M₁ = 1` waist-tail threshold brick. Via the
`minAdmRec` layer-peeling recursion: the `t = 1` cut has block charge `(M₀−1)(M₁−1) = 0` (`M₁ = 1`) and
reduced chain `redChain 1 M = dropHead M` (they agree at `0`: both `= M 1 = 1`), so `minAdm M` is a min
over cuts that includes the `t = 1` term `= minAdm (dropHead M)`. Hence the tail IH on `dropHead M`
(threshold `½·minAdm (dropHead M) ≥ ½·minAdm M`) covers the waist-tail factor. -/
theorem minAdm_le_minAdm_dropHead_of_mid_one (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hM0 : 1 ≤ M 0) (hM1 : M 1 = 1) :
    minAdm M ≤ minAdm (dropHead M) := by
  have hrd : redChain 1 M = dropHead M := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [redChain_zero, dropHead, Fin.succ_zero_eq_one, hM1]
    · simp only [redChain_succ, dropHead]
  have h1mem : (1 : ℕ) ∈ Finset.range (min (M 0) (M 1) + 1) := by
    rw [Finset.mem_range, hM1]; omega
  rw [← minAdmRec_eq_minAdm M, ← minAdmRec_eq_minAdm (dropHead M), minAdmRec_succ_succ M]
  refine le_trans (Finset.inf'_le _ h1mem) (le_of_eq ?_)
  rw [hM1, hrd]; simp

/-- **Rank-1 Frobenius factorization at a middle width `w = 1`** (generalized over the width via a
`w = 1` hypothesis so it applies to the opaque `M 1` without an entrywise cast). `frobSq (Γ · Z) =
frobSq Γ · frobSq Z` when the shared index type has one element. -/
theorem frobSq_rmatMul_mid_one' {a w q : ℕ} (hw : w = 1)
    (Γ : Fin a → Fin w → ℝ) (Z : Fin w → Fin q → ℝ) :
    frobSq (rmatMul Γ Z) = frobSq Γ * frobSq Z := by
  subst hw
  exact frobSq_rmatMul_mid_one Γ Z

/-- **The layer-product loss factors at a width-1 waist** `frobSq (prod M A) = frobSq (A 0) ·
frobSq (prod (dropHead M) (A ∘ succ))` when `M 1 = 1`, stated in the `paramsHeadSplit` form (so the
head-split CoV matches syntactically). The head split `prod_headSplit` composed with the rank-1
factorization; the `exact` bridges the opaque middle width `M 1 ≡ dropHead M 0` by defeq. -/
theorem frobSq_prod_mid_one (M : Fin (L + 1 + 1 + 1) → ℕ) (hM1 : M 1 = 1) (A : Params M) :
    frobSq (prod M A)
      = frobSq (paramsHeadSplit M A).1 * frobSq (prod (dropHead M) (paramsHeadSplit M A).2) := by
  rw [prod_headSplit M A]
  exact frobSq_rmatMul_mid_one' hM1 (A 0) (prod (dropHead M) (fun j => A j.succ))

/-- **The front-block × tail-product box integral is finite.** Over the product box `matBox a w 1 ×ˢ
paramsBoxM Mt 1`, the integrand `(frobSq Γ · frobSq (prod Mt B))^{−c'}` Tonelli-separates into a free
`Fin a × Fin w` Morse factor (finite below `½·(a·w)`, `frobSq_matBox_rpow_lt_top`) times the tail
integral (given finite by `hTail`). The `M₁ = 1` waist's shared shape (`Γ` the front block over the
head-dropped tail). -/
theorem frontTail_prod_lt_top {L : ℕ} (a w : ℕ) (Mt : Fin (L + 1 + 1) → ℕ)
    (c' : ℝ) (haw : 0 < a * w) (hcaw : c' < (a * w : ℝ) / 2)
    (hTail : (∫⁻ B in paramsBoxM Mt 1,
        ENNReal.ofReal ((frobSq (prod Mt B)) ^ (-c'))) < ⊤) :
    (∫⁻ p in matBox a w 1 ×ˢ paramsBoxM Mt 1,
        ENNReal.ofReal ((frobSq p.1 * frobSq (prod Mt p.2)) ^ (-c'))) < ⊤ := by
  have hfront : (∫⁻ Γ in matBox a w 1, ENNReal.ofReal ((frobSq Γ) ^ (-c'))) < ⊤ :=
    frobSq_matBox_rpow_lt_top haw c' hcaw 1 one_pos
  have hsplit : ∀ p : (Fin a → Fin w → ℝ) × Params Mt,
      ENNReal.ofReal ((frobSq p.1 * frobSq (prod Mt p.2)) ^ (-c'))
        = ENNReal.ofReal ((frobSq p.1) ^ (-c'))
          * ENNReal.ofReal ((frobSq (prod Mt p.2)) ^ (-c')) := by
    intro p
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (frobSq_nonneg _) _),
      ← Real.mul_rpow (frobSq_nonneg _) (frobSq_nonneg _)]
  rw [lintegral_congr hsplit, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine lt_of_le_of_lt (lintegral_prod_le _) ?_
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_mul_const' _ _ hTail.ne]
  exact ENNReal.mul_lt_top hfront hTail

/-- **The layer-product box integral is finite at a width-1 waist (`M₁ = 1`), given the tail IH.**
The head split (`prod_headSplit` + `frobSq_rmatMul_mid_one'` at `M₁ = 1`) factors
`frobSq (prod M A) = frobSq (A 0) · frobSq (prod (dropHead M) (A ∘ succ))`; the front `Fin (M 0) ×
Fin (M 1)` block is Morse-finite below `½·(M₀·M₁)`, and the head-dropped tail integral is `hTail`.
Change of variables along the measure-preserving `paramsHeadSplit`. -/
theorem routeMLayerBoxIntegral_mid_one_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ) (hM1 : M 1 = 1)
    (c' : ℝ) (haw : 0 < M 0 * M 1) (hcfront : c' < (M 0 * M 1 : ℝ) / 2)
    (hTail : (∫⁻ B in paramsBoxM (dropHead M) 1,
        ENNReal.ofReal ((frobSq (prod (dropHead M) B)) ^ (-c'))) < ⊤) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  rw [routeMLayerBoxIntegral, ← paramsHeadSplit_preimage_box M]
  have hpt : ∀ A : Params M,
      ENNReal.ofReal ((frobSq (prod M A)) ^ (-c'))
        = ENNReal.ofReal ((frobSq (paramsHeadSplit M A).1
            * frobSq (prod (dropHead M) (paramsHeadSplit M A).2)) ^ (-c')) := by
    intro A
    rw [frobSq_prod_mid_one M hM1 A]
  rw [lintegral_congr hpt,
    (paramsHeadSplit_mp M).setLIntegral_comp_preimage_emb (paramsHeadSplit M).measurableEmbedding
      (fun p => ENNReal.ofReal ((frobSq p.1
          * frobSq (prod (dropHead M) p.2)) ^ (-c')))
      (matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (dropHead M) 1)]
  exact frontTail_prod_lt_top (M 0) (M 1) (dropHead M) c' haw hcfront hTail

/-! ## Hole (a) — the strict deeper-flag shell `jf < r` (head-split domination) -/

/-- **HOLE (a) — the strict-shell contribution is finite.** For a GOOD chain (`hpiv`) and a strict shell
`j < r = min (M₀−t) (M₁−t)`, the per-shell spine integrand at the binding cut `t` is finite below the
shifted threshold. Its eventual proof is the head-split domination `deeperFlag_shell_le` — bounding
`shellSpineIntegrand` by `C · (cornerComparator (redChain (t+j) M) k jc).integral (c' − ½·peelCharge)`
with `C < ⊤` — followed by the DECORATED IH `hIH` applied to that reduced comparator (admissible by
`cornerComparator_adm`, whose β-threshold `deeperFlag_shell_le` supplies). This is the `j < r` branch;
filled on the crux lane. The hypotheses mirror `deeperFlag_shell_le` exactly (plus the strict `hjr` and
the decorated IH). -/
theorem deeperFlagStrictShell_finite
    (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M)
    (hcvg : (M 0 - (t + j)) + (M 1 - (t + j))
        ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    (hc' : (((M 0 - (t + j)) * (M 1 - (t + j)) : ℕ) : ℝ) / 2 < c')
    (hjr : j < min (M 0 - t) (M 1 - t))
    (hIH : ∀ (M' : Fin (L + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (L + 1) M' D' → DecoratedBoxThresholdFinite D') :
    shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t))
        ⟨j, Nat.lt_succ_of_le hj⟩ c' < ⊤ := by
  sorry

/-! ## Hole (b) — the saturated deeper-flag shell `jf = r` (arity IH) -/

/-- **HOLE (b) — the saturated (full-flag) shell contribution is finite.** For a GOOD chain and the
LUMPED top shell `j = r = min (M₀−t) (M₁−t)`, the per-shell spine integrand is finite. This is a SEPARATE
branch from (a): at `j = r` the head-split off-sector block degenerates (`M₀−(t+r) = 0` or
`M₁−(t+r) = 0`), so the domination of (a) is not available; the saturated shell is discharged via the
arity IH at reduced arity (`deeperFlag_shell_le`'s `j = r` case fed to `hIH`). Statement mirrors (a) with
`hjeq : j = r` in place of the strict `hjr`. Filled on the crux lane. -/
theorem deeperFlagSaturatedShell_finite
    (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M)
    (hcvg : (M 0 - (t + j)) + (M 1 - (t + j))
        ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    (hc' : (((M 0 - (t + j)) * (M 1 - (t + j)) : ℕ) : ℝ) / 2 < c')
    (hcT : c' < carrierThreshold M)
    (hjeq : j = min (M 0 - t) (M 1 - t))
    (hIH : ∀ (M' : Fin (L + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (L + 1) M' D' → DecoratedBoxThresholdFinite D') :
    shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t))
        ⟨j, Nat.lt_succ_of_le hj⟩ c' < ⊤ := by
  -- HOLE (b), SD-7 (flagged): the OUTER `(A', x)` pivot-radial resolution of the freed Schur-loss spine
  -- to `C · (cornerComparator (redChain (t+j) M) ![1] ![minAdm − 1]).integral (…) < ⊤`, closed by
  -- `hIH` + `cornerComparator_adm` via `hcT` (at j=r: `minAdm M ≤ minAdm (redChain (t+j) M)`, so
  -- `c' < ½·minAdm M ≤ ½·minAdm (redChain (t+j) M)`). The `j=r` degeneracy (min(a,b)=0) drops the corank
  -- corner (S3) but NOT the pivot radial blow-up (`pivotBlock_radial_blowup`) + angular-integrability
  -- reduction to `cornerComparator.integral` — the SAME unbuilt outer double induction the team's open
  -- `RouteMSJPivotDom.pivotDom_finiteness` / `RouteMSJInnerDescent.innerCorankDescent_lt_top` carry.
  -- Beyond a bounded fill on this tide; `hcT` added per coordinator SNAG-C for the eventual close.
  sorry

/-! ## Hole (d) — the GOOD-case cover connector (assembly of the strict + saturated shells) -/

/-- **HOLE (d) — the good-case cover connector.** For a GOOD chain (`hgood : deepTailMin M ≤ M 1`, the
SOUND key) and an `adm`-admissible `D`, GIVEN the decorated IH, `D` is finite below its carrier
threshold. Its eventual proof is the ASSEMBLY: peel `D.integral c'` at the binding cut `t★ = bindingCut M`
into the shell-spine integrands (the decorated analogue of `sjBoundaryPeel` +
`gammaPeelIntegral_schurShearFree_eq`), cover the outer tail by the singular shells
(`singularShell_iUnion` exhaustive), bound each shell by hole (a) if `jf < r` and hole (b) if `jf = r`,
and sum the finitely-many shells (`lintegral_le_sum_finCover` + `ENNReal.sum_lt_top`). Each shell's
per-cut hpiv is DERIVED from `hgood` via the banked `minAdm_redChain_le_deepTailMin` (on good,
`tailMinWidth M = deepTailMin M`). This connector — the peel-to-shell-sum reduction for an ARBITRARY
admissible `D` (not just the trivial decoration) — is the seam being pinned on the cover lane. It
consumes holes (a), (b). -/
theorem deeperFlagGood_finite
    (M : Fin (L + 1 + 1 + 1) → ℕ) (D : SJDecoration M)
    (hD : adm (L + 1 + 1) M D)
    (hgood : deepTailMin M ≤ M 1)
    (hIH : ∀ (M' : Fin (L + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (L + 1) M' D' → DecoratedBoxThresholdFinite D') :
    DecoratedBoxThresholdFinite D := by
  sorry

/-! ## Hole (c) — the WAIST branch, `M₁ ≥ 2` (route-A SVD-qPeel + reorientation) -/

/-- **HOLE (c) — the waist branch, `M₁ ≠ 1` (route-A SVD-qPeel + reorientation).** In the waist regime
(`hwaist : M 1 < deepTailMin M`, i.e. `M₁ < min(M₂,…,M_last)`, the deep-tail product full-row-rank case)
with `M₁ ≠ 1`, `deeperFlag_shell_le` is inapplicable (its per-cut hpiv fails).

**Fill route-A — SVD-qPeel + REORIENTATION** (O2 scout verdict, decorrelated Codex): a deep-layer SVD
sends `D.integral` to the banked `qPeelIntegral` (`#156` is its `L = 0` base), CONSUMING the decoration
first; then a plain REORIENTATION to a good end (every `≥ 4`-width chain has one; reversal CoV
`I(M) = I(rev M)`, `minAdm` half-banked via `minAdm_comp_perm`) lands the head-split/IH. Consuming the
decoration in the SVD-qPeel BEFORE the plain reversal sidesteps waistpin's decoration-transport
obstruction. The earlier route-(b) drop-front is DEAD: its eigenvalue-profile weight `J_c` is
NON-admissible (Hölder `β < 3/4`, below the `β < 1` a sharp domination needs — a red herring). New
labour: one deep-layer Gram-spectral / Weyl-Jacobian CoV brick + the reversal-CoV lemma (bounded, no
wall) — and NO new decorated-IH predicate (a simplification over route-(b)). The hole STATEMENT below is
route-agnostic (hyps → finiteness, with `hIH`). HELD pending the admfix `adm` repair. NOT filled here. -/
theorem deeperFlagWaist_finite
    (M : Fin (L + 1 + 1 + 1) → ℕ) (D : SJDecoration M)
    (hD : adm (L + 1 + 1) M D)
    (hwaist : M 1 < deepTailMin M)
    (hM1 : M 1 ≠ 1)
    (hIH : ∀ (M' : Fin (L + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (L + 1) M' D' → DecoratedBoxThresholdFinite D') :
    DecoratedBoxThresholdFinite D := by
  sorry

/-! ## Hole (e) — the WAIST sub-case `M₁ = 1` (reversal-FREE rank-1 factorization) -/

/-- **HOLE (e) — the waist sub-case `M₁ = 1` (FILLED, sorry-free, axiom-clean).** At `M₁ = 1` the loss
factors through the width-1 bottleneck: `frobSq (rmatMul Γ Z) = frobSq Γ · frobSq Z`
(`frobSq_rmatMul_mid_one'`, the `w = 1` wrapper of the banked `frobSq_rmatMul_mid_one`), so the decorated
box integral splits into a FRONT Morse factor × a `dropHead M`-TAIL IH factor. UNCONDITIONAL in the waist
(no `hwaist` hypothesis needed) — the factorization holds for any `M₁ = 1`; the dispatch only invokes it
inside the waist branch.

The fill: `intro c' hc'`, then the vacuous `minAdm M = 0` branch (threshold `0`, no `c' ≥ 0` below it).
Otherwise `minAdm M ≥ 1` gives `1 ≤ M 0` (via `minAdm_le_mul_head`, `minAdm M ≤ M₀·M₁ = M₀`); the tail
finiteness is `hIH (dropHead M) (SJDecoration.trivial _) (adm_trivial (L+1) _)` +
`decoratedBoxThresholdFinite_trivial_iff` (→ `RouteMBoxThresholdFinite (dropHead M)`, i.e. the finite tail
integral at `c'`). Threshold bookkeeping: `c' < ½·minAdm M ≤ min(½·(M₀·M₁), ½·minAdm (dropHead M))` via
`minAdm_le_mul_head` (front budget) and `minAdm_le_minAdm_dropHead_of_mid_one` (tail budget). Then the
`adm = genuineCarrier ∧ FaithfulSJAt` disjunction is dispatched
`obtain ⟨hgen, hf⟩ := hD; obtain ⟨hζ, hν, e, hmpe, hdome, hctx⟩ := hgen;
rcases hf with ⟨hd0, hobs⟩ | ⟨_hd1, i₀, _halpha, hbeta, hdelta0, hgamma⟩`:
- **d=0** (`hobs : carrier.loss u z x = ∑ v, (x v)²`): `decLoss u z = frobSq (prod M (e z))` (the eqRec
  transport `hν`/`hctx`/`eqRec_fun_apply_eqRec`, as in `decoratedBase_d0_of_lossEq`); the `d = 0` integral
  collapses (empty monomial, unit-box measure `1`) and the measure-preserving CoV along `e` reduces it to
  `routeMLayerBoxIntegral M c' 1`, closed by the banked `routeMLayerBoxIntegral_mid_one_lt_top` (head-split
  CoV → front-Morse `frobSq_matBox_rpow_lt_top` × tail-IH).
- **d≥1**: `decLoss_clean_of_uniformResidualSupport D i₀ hdelta0` + `gammaPrimeClause` provenance give
  `decLoss u z = commonDivisor² · frobSq (rmatMul (eΓ z).1 (prod (dropHead M) (eΓ z).2))`; Tonelli splits
  `D.integral` into `(∫ monomialIntegrand)` (finite below `monomialThreshold`, from `hbeta`, via
  `monomialIntegrand_lintegral_unitBox_lt_top`) × `(∫ frobSq(rmatMul Γ Z_tail)^{−c'})` (CoV along `eΓ`,
  rank-1 split `frobSq_rmatMul_mid_one'`, then the banked `frontTail_prod_lt_top`).

Bricks banked sorry-free (this file): `frobSq_rmatMul_mid_one'`, `frobSq_prod_mid_one`,
`frontTail_prod_lt_top`, `routeMLayerBoxIntegral_mid_one_lt_top` (+ the reused
`frobSq_rmatMul_mid_one`, `minAdm_le_minAdm_dropHead_of_mid_one`). Concludes `DecoratedBoxThresholdFinite
D`; `#print axioms` = `[propext, Classical.choice, Quot.sound]`. -/
theorem deeperFlagWaistM1_finite
    (M : Fin (L + 1 + 1 + 1) → ℕ) (D : SJDecoration M)
    (hD : adm (L + 1 + 1) M D)
    (hM1 : M 1 = 1)
    (hIH : ∀ (M' : Fin (L + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (L + 1) M' D' → DecoratedBoxThresholdFinite D') :
    DecoratedBoxThresholdFinite D := by
  classical
  intro c' hc'
  rw [carrierThreshold] at hc'
  -- vacuous when `minAdm M = 0` (threshold `0`, no `c' ≥ 0` below it).
  rcases Nat.eq_zero_or_pos (minAdm M) with hm0 | hmpos_nat
  · exfalso
    rw [hm0] at hc'; simp only [Nat.cast_zero, zero_div] at hc'
    exact absurd hc' (not_lt.mpr c'.coe_nonneg)
  -- `minAdm M ≥ 1`; derive `1 ≤ M 0` from `minAdm M ≤ M 0 · M 1 = M 0`.
  have hmle_head : minAdm M ≤ M 0 * M 1 := minAdm_le_mul_head M
  have hM0 : 1 ≤ M 0 := by
    rcases Nat.eq_zero_or_pos (M 0) with h | h
    · exfalso; rw [h, Nat.zero_mul] at hmle_head; omega
    · exact h
  have hc'0 : (0 : ℝ) ≤ (c' : ℝ) := c'.coe_nonneg
  -- front budget `c' < ½·(M₀·M₁)` (from `minAdm M ≤ M₀·M₁`), and `0 < M₀·M₁`.
  have hcfront : (c' : ℝ) < (M 0 * M 1 : ℝ) / 2 := by
    have h1 : (minAdm M : ℝ) ≤ (M 0 * M 1 : ℝ) := by exact_mod_cast hmle_head
    have h2 : (c' : ℝ) < (minAdm M : ℝ) / 2 := hc'
    push_cast at h1 ⊢; linarith
  have haw : 0 < M 0 * M 1 := lt_of_lt_of_le hmpos_nat hmle_head
  -- tail budget `c' < ½·minAdm (dropHead M)` (from `minAdm M ≤ minAdm (dropHead M)`).
  have hmle_tail : minAdm M ≤ minAdm (dropHead M) :=
    minAdm_le_minAdm_dropHead_of_mid_one M hM0 hM1
  have hctail : (c' : ℝ) < (minAdm (dropHead M) : ℝ) / 2 := by
    have h1 : (minAdm M : ℝ) ≤ (minAdm (dropHead M) : ℝ) := by exact_mod_cast hmle_tail
    have h2 : (c' : ℝ) < (minAdm M : ℝ) / 2 := hc'
    linarith
  -- the finite tail integral, via the trivial-decoration IH on `dropHead M`.
  have hTail : (∫⁻ B in paramsBoxM (dropHead M) 1,
      ENNReal.ofReal ((frobSq (prod (dropHead M) B)) ^ (-(c' : ℝ)))) < ⊤ := by
    have hTailBox : RouteMBoxThresholdFinite (dropHead M) :=
      (decoratedBoxThresholdFinite_trivial_iff (dropHead M)).mp
        (hIH (dropHead M) (SJDecoration.trivial (dropHead M)) (adm_trivial (L + 1) (dropHead M)))
    have := hTailBox c' hctail
    rwa [routeMLayerBoxIntegral] at this
  -- dispatch the `FaithfulSJAt` disjunction (`adm := genuineCarrier ∧ FaithfulSJAt`).
  obtain ⟨hgen, hf⟩ := hD
  obtain ⟨hζ, hν, e, hmpe, hdome, hctx⟩ := hgen
  rcases hf with ⟨hd0, hobs⟩ | ⟨_hd1, i₀, _halpha, hbeta, hdelta0, hgamma⟩
  · -- (ii) `d = 0` free-block leaf: `decLoss = frobSq (prod M (e z))`; integral collapses & CoV.
    letI := D.mZ
    have hloss : ∀ (u : Fin D.d → ℝ) (z : D.Z), D.decLoss u z = frobSq (prod M (e z)) := by
      intro u z
      letI := D.fν; letI := D.fι
      rw [SJDecoration.decLoss, hobs (D.ctx z).1 (D.ctx z).2 u]
      have hfrob : frobSq (prod M (e z))
          = ∑ ik : (Fin (M 0) × Fin (M (Fin.last (L + 1 + 1)))), (prod M (e z) ik.1 ik.2) ^ 2 := by
        rw [frobSq, Fintype.sum_prod_type]
      rw [hfrob]
      refine Fintype.sum_equiv (Equiv.cast hν) _ _ (fun v => ?_)
      have hEq : (D.ctx z).2 v = prod M (e z) (Equiv.cast hν v).1 (Equiv.cast hν v).2 := by
        rw [← eqRec_fun_apply_eqRec hν (D.ctx z).2 v]
        exact congrFun (hctx z) (Equiv.cast hν v)
      rw [hEq]
    haveI hEmpty : IsEmpty (Fin D.d) := by rw [hd0]; infer_instance
    have hprod1 : ∀ u : Fin D.d → ℝ, (∏ ℓ, |u ℓ| ^ (D.jac ℓ)) = 1 := fun u => by
      rw [Finset.univ_eq_empty, Finset.prod_empty]
    have hvol : (volume : Measure (Fin D.d → ℝ)) (unitBox D.d) = 1 := by
      rw [unitBox, volume_pi_pi]; simp
    have hdommeas : MeasurableSet D.dom := by
      rw [hdome]; exact (measurableSet_paramsBoxM M 1).preimage e.measurable
    have hkey : D.integral (c' : ℝ)
        = ∫⁻ z in D.dom, ENNReal.ofReal ((frobSq (prod M (e z))) ^ (-(c' : ℝ))) := by
      unfold SJDecoration.integral
      refine setLIntegral_congr_fun hdommeas (fun z _ => ?_)
      have hpt : ∀ u : Fin D.d → ℝ,
          ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ D.jac ℓ) * D.decLoss u z ^ (-(c' : ℝ)))
            = ENNReal.ofReal ((frobSq (prod M (e z))) ^ (-(c' : ℝ))) :=
        fun u => by rw [hprod1 u, one_mul, hloss u z]
      rw [lintegral_congr hpt, setLIntegral_const, hvol, mul_one]
    rw [hkey, hdome,
      hmpe.setLIntegral_comp_preimage_emb e.measurableEmbedding
        (fun A => ENNReal.ofReal ((frobSq (prod M A)) ^ (-(c' : ℝ)))) (paramsBoxM M 1)]
    exact routeMLayerBoxIntegral_mid_one_lt_top M hM1 (c' : ℝ) haw hcfront hTail
  · -- (iii) `d ≥ 1` resolved corner (units-free Γ×tail split, `M₁ = 1` factorization).
    letI := D.mZ; letI := D.fν; letI := D.fι; haveI : Nonempty D.ι := ⟨i₀⟩
    obtain ⟨a, eΓ, ρ, hmpΓ, hdomΓ, hdim, hprov⟩ := hgamma
    set k := sharedDivisorExp D.carrier.supp with hk
    -- the clean rank-1-factored loss: `decLoss = commonDivisor² · frobSq (Γ · Z_tail)`.
    have hdec : ∀ (u : Fin D.d → ℝ) (z : D.Z),
        D.decLoss u z = commonDivisor D.carrier.supp u ^ 2
          * frobSq (rmatMul (eΓ z).1 (prod (dropHead M) (eΓ z).2)) := by
      intro u z
      rw [decLoss_clean_of_uniformResidualSupport D i₀ hdelta0 u z]
      congr 1
      have hsc : ∀ i, (D.carrier.residual (D.ctx z).1 (D.ctx z).2 i) ^ 2
          = (rmatMul (eΓ z).1 (prod (dropHead M) (eΓ z).2) (ρ i).1 (ρ i).2) ^ 2 :=
        fun i => by rw [hprov z i]
      rw [Finset.sum_congr rfl (fun i _ => hsc i),
        Equiv.sum_comp ρ (fun pq => (rmatMul (eΓ z).1 (prod (dropHead M) (eΓ z).2) pq.1 pq.2) ^ 2),
        frobSq]
      exact Fintype.sum_prod_type
        (fun pq => (rmatMul (eΓ z).1 (prod (dropHead M) (eΓ z).2) pq.1 pq.2) ^ 2)
    -- threshold plumbing for the monomial (β) factor.
    have hmpos : (0 : ℝ) < (minAdm M : ℝ) := by exact_mod_cast hmpos_nat
    have hden : ENNReal.ofReal ((minAdm M : ℝ) / 2) = (minAdm M : ℝ≥0∞) / 2 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_natCast,
        ENNReal.ofReal_ofNat]
    have hc'enn : (c' : ℝ≥0∞) < (minAdm M : ℝ≥0∞) / 2 := by
      rw [← hden, ← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hmpos (by norm_num))).mpr hc'
    have hax : ∀ j, (c' : ℝ≥0∞) < axisRatio (D.jac j) (k j) := by
      intro j
      have hle : monomialThreshold D.d k D.jac ≤ axisRatio (D.jac j) (k j) := by
        rw [monomialThreshold_eq_iInf_axisRatio]; exact iInf_le _ j
      exact lt_of_lt_of_le (lt_of_lt_of_le hc'enn hbeta) hle
    have hIu : (∫⁻ u in unitBox D.d,
        ENNReal.ofReal (monomialIntegrand D.d k D.jac (c' : ℝ) u)) < ⊤ :=
      monomialIntegrand_lintegral_unitBox_lt_top D.d k D.jac (c' : ℝ)
        (fun j => axisRatio_lt_exp (hax j))
    -- the Γ·tail integral: CoV along `eΓ`, rank-1 split, then `frontTail_prod_lt_top`.
    have hIΓ : (∫⁻ z in D.dom,
        ENNReal.ofReal ((frobSq (rmatMul (eΓ z).1 (prod (dropHead M) (eΓ z).2)))
            ^ (-(c' : ℝ)))) < ⊤ := by
      rw [hdomΓ, hmpΓ.setLIntegral_comp_preimage_emb eΓ.measurableEmbedding
        (fun p => ENNReal.ofReal ((frobSq (rmatMul p.1 (prod (dropHead M) p.2))) ^ (-(c' : ℝ))))
        (matBox a (M 1) 1 ×ˢ paramsBoxM (dropHead M) 1),
        setLIntegral_congr_fun
          ((matBox_measurableSet a (M 1) 1).prod (measurableSet_paramsBoxM (dropHead M) 1))
          (fun p _ => by rw [frobSq_rmatMul_mid_one' hM1 p.1 (prod (dropHead M) p.2)])]
      refine frontTail_prod_lt_top a (M 1) (dropHead M) (c' : ℝ) ?_ ?_ hTail
      · exact lt_of_lt_of_le hmpos_nat hdim
      · have h1 : (minAdm M : ℝ) ≤ (a * M 1 : ℝ) := by exact_mod_cast hdim
        have h2 : (c' : ℝ) < (minAdm M : ℝ) / 2 := hc'
        push_cast at h1 ⊢; linarith
    -- assemble: `D.integral = (∫ monomial) · (∫ Γ·tail)`.
    have hpt : ∀ (u : Fin D.d → ℝ) (z : D.Z),
        (∏ ℓ, |u ℓ| ^ D.jac ℓ) * D.decLoss u z ^ (-(c' : ℝ))
          = monomialIntegrand D.d k D.jac (c' : ℝ) u
            * (frobSq (rmatMul (eΓ z).1 (prod (dropHead M) (eΓ z).2))) ^ (-(c' : ℝ)) := by
      intro u z
      rw [hdec u z, Real.mul_rpow (by positivity) (frobSq_nonneg _), ← mul_assoc]
      congr 1
      rw [monomialIntegrand, commonDivisor_sq]
    have hkey : D.integral (c' : ℝ)
        = (∫⁻ u in unitBox D.d, ENNReal.ofReal (monomialIntegrand D.d k D.jac (c' : ℝ) u))
          * (∫⁻ z in D.dom, ENNReal.ofReal ((frobSq (rmatMul (eΓ z).1
              (prod (dropHead M) (eΓ z).2))) ^ (-(c' : ℝ)))) := by
      unfold SJDecoration.integral
      rw [← lintegral_const_mul' _ _ hIu.ne]
      refine setLIntegral_congr_fun ?_ (fun z _ => ?_)
      · rw [hdomΓ]
        exact ((matBox_measurableSet a (M 1) 1).prod
          (measurableSet_paramsBoxM (dropHead M) 1)).preimage eΓ.measurable
      · rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr (fun u => ?_)
        rw [hpt u z, ENNReal.ofReal_mul (monomialIntegrand_nonneg' D.d k D.jac (c' : ℝ) u)]
    rw [hkey]
    exact ENNReal.mul_lt_top hIu hIΓ

/-! ## The assembled decorated step — `DecoratedStepHyp adm` (dispatch, sorry-free) -/

/-- **The assembled decorated step `DecoratedStepHyp adm`.** For every `≥ 3`-width chain `M`, GIVEN the
decorated strong IH, every `adm`-admissible `D : SJDecoration M` is finite below its carrier threshold.
The dispatch is exhaustive: `by_cases hpiv` on the pivot-admissibility at the binding cut — `hpiv`
(front-good) routes to the cover connector hole (d) `deeperFlagGood_finite`; `¬hpiv` (waist) splits
further `by_cases M₁ = 1` into the reversal-free sub-case hole (e) `deeperFlagWaistM1_finite` and the
reversal route hole (c) `deeperFlagWaist_finite`. Sorry-free itself — all analytic content is in the
five holes. -/
theorem decoratedStepHyp_dispatch : DecoratedStepHyp adm := by
  intro L M hIH D hD
  by_cases hkey : M 1 < deepTailMin M
  · -- WAIST (`M 1 < deepTailMin M`): route (b) drop-front, split off the `M₁ = 1` sub-case.
    by_cases hM1 : M 1 = 1
    · exact deeperFlagWaistM1_finite M D hD hM1 hIH
    · exact deeperFlagWaist_finite M D hD hkey hM1 hIH
  · -- GOOD (`deepTailMin M ≤ M 1`): the head-split cover connector.
    exact deeperFlagGood_finite M D hD (not_lt.mp hkey) hIH

end DLNFibre.DLN.RLCT
