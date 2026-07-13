import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec
import DLNFibre.DLN.RLCT.Validate.RouteMSJAdm
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagCore
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCapB

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

The dispatch is NOT a flat 3-way case on `D`. It is a **2-way split on the pivot-admissibility** at the
binding cut `t★ = bindingCut M`, and the "good" half further decomposes over the deeper-flag singular
shells (a per-shell split, INSIDE the outer tail integral, NOT a per-`D` case):

* **good** (`hpiv : minAdm (redChain t★ M) ≤ t★ · tailMinWidth M`) — `D.integral c'` peels at the binding
  cut and covers the outer tail by the singular shells `singularShell ε r jf`, `jf : Fin (r+1)`,
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
* **waist** (`¬hpiv`) — hole (c) `deeperFlagWaist_finite`: `deeperFlag_shell_le` is inapplicable
  (`hpiv` is one of its hypotheses), so the chain reduces to the banked 3-width box finiteness
  `routeMBoxThresholdFinite_mnp`. PROVISIONAL: the exact reduction route is pinned on a parallel
  pen-and-paper; this module states the TARGET the connector must hit.

The main `decoratedStepHyp_dispatch : DecoratedStepHyp adm` is itself `sorry`-free — it is the exhaustive
`by_cases hpiv` dispatch to holes (d) and (c). All analytic content lives in the four holes.

## The j ≤ r vs j < r seam (report point i)

`deeperFlag_shell_le` (`RouteMSJDeeperFlagCore`) is typed with `hj : j ≤ min (M₀−t) (M₁−t)` — the
`≤` ALREADY admits `j = r`, so at the STATEMENT level there is NO quantifier gap between strict and
saturated. The two are separated for a PROOF-CONTENT reason, not a typing reason: at `j = r` the peeled
off-sector block has a zero dimension (`M₀−(t+r) = 0` or `M₁−(t+r) = 0` when `r = min(M₀−t,M₁−t)`), so
the head-split domination (Bricks F, D) is degenerate there; the saturated shell is instead closed by
the arity IH. Hence hole (b) is a SEPARATE branch. (This proof-content claim is inherited from the crux
lane's `deeperFlag_spineToCore`; flagged for its confirmation, not verified here.)

## Status

CONTRACT-FIRST skeleton: 4 named `sorry`-holes (a, b, c=waist, d=connector), main dispatch sorry-free.
UNTRACKED, NOT wired into `DLNFibre.lean`/`AxCheck` — the canonical library stays 0-sorry. Sorries are
the explicit deliverable on this tide branch.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

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

/-- **HOLE (d) — the good-case cover connector.** For a GOOD chain (`hpiv` at the binding cut) and an
`adm`-admissible `D`, GIVEN the decorated IH, `D` is finite below its carrier threshold. Its eventual
proof is the ASSEMBLY: peel `D.integral c'` at the binding cut `t★ = bindingCut M` into the shell-spine
integrands (the decorated analogue of `sjBoundaryPeel` + `gammaPeelIntegral_schurShearFree_eq`), cover
the outer tail by the singular shells (`singularShell_iUnion` exhaustive), bound each shell by hole (a)
if `jf < r` and hole (b) if `jf = r`, and sum the finitely-many shells
(`lintegral_le_sum_finCover` + `ENNReal.sum_lt_top`). This connector — the peel-to-shell-sum reduction
for an ARBITRARY admissible `D` (not just the trivial decoration) — is the seam being pinned on the
cover lane. It consumes holes (a), (b). -/
theorem deeperFlagGood_finite
    (M : Fin (L + 1 + 1 + 1) → ℕ) (D : SJDecoration M)
    (hD : adm (L + 1 + 1) M D)
    (hpiv : minAdm (redChain (bindingCut M) M) ≤ (bindingCut M) * tailMinWidth M)
    (hIH : ∀ (M' : Fin (L + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (L + 1) M' D' → DecoratedBoxThresholdFinite D') :
    DecoratedBoxThresholdFinite D := by
  sorry

/-! ## Hole (c) — the WAIST branch (`hpiv` fails → reduce to `routeMBoxThresholdFinite_mnp`) -/

/-- **HOLE (c) — the waist branch (PROVISIONAL).** When the pivot-admissibility FAILS at the binding cut
(`¬hpiv`), `deeperFlag_shell_le` is inapplicable (`hpiv` is one of its hypotheses), so the head-split
route is unavailable. The chain is a "waist": `D.integral c'` reduces to the banked 3-width box
finiteness `routeMBoxThresholdFinite_mnp (m n p)` (finite for ALL widths).

**The EXACT statement this hole requires of its connector** (the contract to relay to the waist
pen-and-paper): there are widths `m n p : ℕ` (derived from `M` and the waist data) and a threshold-
respecting reduction such that, for every `c' < carrierThreshold M = ½·minAdm M`,
`D.integral c' ≤ (routeMLayerBoxIntegral (![m, n, p] : Fin 3 → ℕ) c' 1)` (or a finite multiple thereof),
with `c' < ½·minAdm (![m,n,p])` guaranteed by the waist inequality `¬hpiv`; the RHS is `< ⊤` by
`routeMBoxThresholdFinite_mnp m n p`. The open content is (i) the choice of `(m,n,p)` and (ii) the
threshold bookkeeping `carrierThreshold M ≤ ½·minAdm (![m,n,p])` that the waist inequality must supply.
NOT filled here. -/
theorem deeperFlagWaist_finite
    (M : Fin (L + 1 + 1 + 1) → ℕ) (D : SJDecoration M)
    (hD : adm (L + 1 + 1) M D)
    (hpiv : ¬ (minAdm (redChain (bindingCut M) M) ≤ (bindingCut M) * tailMinWidth M)) :
    DecoratedBoxThresholdFinite D := by
  sorry

/-! ## The assembled decorated step — `DecoratedStepHyp adm` (dispatch, sorry-free) -/

/-- **The assembled decorated step `DecoratedStepHyp adm`.** For every `≥ 3`-width chain `M`, GIVEN the
decorated strong IH, every `adm`-admissible `D : SJDecoration M` is finite below its carrier threshold.
The dispatch is the exhaustive `by_cases` on the pivot-admissibility at the binding cut: `hpiv` (good)
routes to the cover connector hole (d) `deeperFlagGood_finite`; `¬hpiv` (waist) routes to the waist hole
(c) `deeperFlagWaist_finite`. Sorry-free itself — all analytic content is in the four holes. -/
theorem decoratedStepHyp_dispatch : DecoratedStepHyp adm := by
  intro L M hIH D hD
  by_cases hpiv : minAdm (redChain (bindingCut M) M) ≤ (bindingCut M) * tailMinWidth M
  · exact deeperFlagGood_finite M D hD hpiv hIH
  · exact deeperFlagWaist_finite M D hD hpiv

end DLNFibre.DLN.RLCT
