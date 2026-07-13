import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec
import DLNFibre.DLN.RLCT.Validate.RouteMSJAdm
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagCore
import DLNFibre.DLN.RLCT.Validate.MinAdmPermInvariance

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
  - **`M₁ ≥ 2`** — hole (c) `deeperFlagWaist_finite`, ROUTE (b) DROP-FRONT: integrate out the front
    block `Γ` (KEEPING `M₁`), landing on the `dropHead M` DECORATED IH carrying an eigenvalue-profile
    weight (the deep-pinch spectral weight rides in the reduced decoration's carrier/jac). Reversal route
    (a) is DEAD here: `FaithfulSJAt` is front-oriented, and reversal's endpoint `a ≠ M₀` makes it a
    re-resolution, not a reindex. Calls `hIH (dropHead M) D_w`; the `adm` premise on the weight `D_w` is
    the OPEN gate **O2** (a scout adjudicating admissibility).
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

CONTRACT-FIRST skeleton: 5 named `sorry`-holes (a=strict, b=saturated, d=good-connector,
c=waist-reversal, e=waist-`M₁=1`), main dispatch sorry-free. UNTRACKED, NOT wired into
`DLNFibre.lean`/`AxCheck` — the canonical library stays 0-sorry. Sorries are the explicit deliverable
on this tide branch.
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
    (hjeq : j = min (M 0 - t) (M 1 - t))
    (hIH : ∀ (M' : Fin (L + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (L + 1) M' D' → DecoratedBoxThresholdFinite D') :
    shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t))
        ⟨j, Nat.lt_succ_of_le hj⟩ c' < ⊤ := by
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

/-! ## Hole (c) — the WAIST branch, `M₁ ≥ 2` (route (b) DROP-FRONT → dropHead-decorated IH) -/

/-- **HOLE (c) — the waist branch, `M₁ ≠ 1` (route (b): DROP-FRONT → dropHead-decorated IH).** In the
waist regime (`hwaist : M 1 < deepTailMin M`, i.e. `M₁ < min(M₂,…,M_last)`, the deep-tail product
full-row-rank case) with `M₁ ≠ 1`, `deeperFlag_shell_le` is inapplicable (its per-cut hpiv fails). The
waist fires WITH nontrivial decoration (front-good + deep pinch → decorated waist).

**Fill route (b) — DROP-FRONT** (waistpin's corrected pin; the earlier reversal route (a) is DEAD:
`FaithfulSJAt` is front-oriented, and reversal's endpoint `a ≠ M₀` makes it a re-resolution, not a
reindex — and the waist genuinely fires with nontrivial decoration). Integrate out the FRONT block `Γ`
while KEEPING `M₁`, landing on the `dropHead M` DECORATED IH carrying an eigenvalue-profile weight (the
deep-pinch spectral weight rides in the reduced decoration's carrier/jac). Concretely the fill calls
`hIH (dropHead M) D_w` where `D_w : SJDecoration (dropHead M)` is the eigenvalue-profile-weight
decoration; the `adm (L+1) (dropHead M) D_w` premise `hIH` needs is the OPEN gate **O2** (a scout is
adjudicating whether that weight is admissible). NOT `routeMBoxThresholdFinite_mnp` (proven NO-GO for
`L ≥ 1`; see module header). The hole STATEMENT below is route-agnostic (hyps → finiteness, with `hIH`);
only the documented fill route changed from reversal to (b). Concludes `DecoratedBoxThresholdFinite D`.
NOT filled here. -/
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

/-- **HOLE (e) — the waist sub-case `M₁ = 1` (reversal-free, UNCONDITIONAL).** When `M₁ = 1` (any `L`),
the front block `Γ` is a column and the deep-tail product `Q = prod (dropHead M)` a row, so the loss
FACTORIZES for ANY `D`: `frobSq (Γ · Q) = ‖Γ‖² · ‖Q‖²` (rank-1 outer product; waistpin-confirmed cheap +
unconditional). The decorated box integral therefore splits as a FRONT Morse integral (the radial `‖Γ‖²`
factor, `corankLeaf_rpow_lt_top` at `n = 1`) times the dropHead-tail IH (`Q` = one-shorter chain product,
closed by the DECORATED IH `hIH` on `dropHead M` at the reduced arity). Reversal-free, a standalone
lemma, no open gate. Concludes `DecoratedBoxThresholdFinite D`. NOT filled here. -/
theorem deeperFlagWaistM1_finite
    (M : Fin (L + 1 + 1 + 1) → ℕ) (D : SJDecoration M)
    (hD : adm (L + 1 + 1) M D)
    (hM1 : M 1 = 1)
    (hIH : ∀ (M' : Fin (L + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (L + 1) M' D' → DecoratedBoxThresholdFinite D') :
    DecoratedBoxThresholdFinite D := by
  sorry

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
