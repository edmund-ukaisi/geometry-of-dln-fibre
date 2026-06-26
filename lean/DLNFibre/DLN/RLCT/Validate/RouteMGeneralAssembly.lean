import DLNFibre.DLN.RLCT.Validate.RouteMBranchRead

/-!
# `RouteMGeneralAssembly` — the #99 CONSUMER scaffold (fm3, route-first)

The fm3 half of the #99 co-build: the recursion ASSEMBLY + the value-fold, consuming rs-grind's non-leaf
read (a `RouteMBranchRead`, the frozen seam) and the banked `routeM_value_eq`. ROUTE-FIRST: the structure
is green-with-named-sorries against the LOCKED `RouteMBranchRead`; the named sorries are the genuine #99
gaps (the read→codims bridge, riding rs-grind's read body; the achiever-witness, riding #121-(ii)).

This is built against the FROZEN `RouteMBranchRead` (does NOT need rs-grind's read body — only the type),
so it compiles in parallel with rs-grind's read. The seam is `RouteMBranchRead`.
-/

open DLNFibre.DLN.RLCT
open scoped BigOperators ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The general-branch assembly (fm3 CONSUMER).** rs-grind's non-leaf read `r : RouteMBranchRead M₀ M`
assembles into the `routeStep` branch via the banked bridge `r.toRouteStep`. This IS the general branch
arm of `routeStep` (the `else` of the leaf-first dispatch), once the read is supplied. -/
def routeStepGeneralBranch {M₀ M : Fin (L + 1) → ℕ} (r : RouteMBranchRead M₀ M) : RouteStep M₀ M :=
  r.toRouteStep

/-- **The value-fold over the read's chart family (#99 value target, CONSUMER side).** Given the read's
per-leaf codim accumulation (`hdataOf` — the `appendDivisor` fold, threaded by the recursion through the
read's `codim`), the per-leaf root-anchored `PivotWitness M` (`hwitOf`, from the read's `witness`), and the
ACHIEVER leaf `i₀` with `minAdm ∈ codimsOf i₀` (`hbind₀` — the #121-(ii) named hyp: the achiever stratum is
GENUINELY reached, `rankFn (cascadeTuple M T*) = achieverRankPattern M T*`, NOT a vacuous membership), the
`⨅` over `routeMIota M` of the per-leaf `monomialThreshold` is `½·minAdm(M) = lambdaCore`. Reduces to the
banked `routeM_value_eq` — the value rides ONLY the `PivotWitness` codims (no cascade in the value lane). -/
theorem routeMGeneralValue (M : Fin (L + 1) → ℕ) (codimsOf : routeMIota M → List ℕ)
    (hdataOf : ∀ i, (routeAtlas M M).data i = MonoData.foldDivisors (codimsOf i))
    (hm₀ : 1 ≤ ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat)
    (hwitOf : ∀ i, ∀ c ∈ codimsOf i, PivotWitness M c)
    (i₀ : routeMIota M) (hbind₀ : ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat ∈ codimsOf i₀) :
    (⨅ i : routeMIota M, monomialThreshold (routeD M i) (routeK M i) (routeH M i))
      = ((((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat : ℝ≥0∞)) / 2 :=
  routeM_value_eq M codimsOf hdataOf hm₀ hwitOf i₀ hbind₀

/-! ## The #99 NAMED GAPS (route-first; both genuine, NOT faked)

`routeMGeneralValue` is the value-fold LOGIC, CONDITIONAL on its hypotheses — exactly the banked
`routeM_value_eq`. To make it UNCONDITIONAL on the actual `routeMIota M` (the general routeStep body
computing), two named gaps remain, each riding a co-builder's piece:

1. **The read→codims bridge (rs-grind's read body).** The general `routeStep` branch must be the read's
   `toRouteStep` so `routeMIota M` computes; then `codimsOf`/`hdataOf` come from the read's `codim` threaded
   by `appendDivisor` along the recursion. This rides rs-grind's non-leaf read producing a
   `RouteMBranchRead M M` whose `routeAtlas` data folds to its codims. Named gap — rs-grind's lane.

2. **The achiever-witness (`#121-(ii)`).** `i₀`/`hbind₀` (the achiever leaf with `minAdm ∈ codimsOf i₀`,
   GENUINELY reached) is the `#121-(ii)` conclusion (`rankFn (cascadeTuple M T*) = achieverRankPattern M T*`,
   the orbit-stratum = column-constant completion via `Q3` — NOT a weaker `∃ i₀`). Plugs in when `#121`
   merges (`#28`). Named gap — `#121`-(ii)'s lane.

Both are the controller's route-first plan: build the scaffold green against the frozen seam, the two named
gaps fill from the co-builders.

**Axiom honesty (`#print axioms`).** `routeMGeneralValue` has no `sorry` TACTIC (its proof term is exactly
`routeM_value_eq` applied), BUT it depends on `sorryAx` TRANSITIVELY: its statement is over `routeMIota M`,
whose value reduces through `routeAtlas` → `routeStep`, whose general BRANCH is still `sorry`. So the value
lane carries `sorryAx` until #99 fills that branch — the SAME inheritance the committed `routeM_value_eq`
already has (`#print axioms routeM_value_eq` → `[propext, sorryAx, Classical.choice, Quot.sound,
monomial_rlct]`). The PROOF LOGIC is `routeM_value_eq`-clean (no new sorry introduced here); the `sorryAx` is
the inherited #99 `routeStep`-branch gap, NOT a hole in this lemma's reasoning. It clears when #99 lands. -/

end DLNFibre.DLN.RLCT
