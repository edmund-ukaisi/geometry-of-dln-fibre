import DLNFibre.DLN.RLCT.Validate.RouteMRecursion
import DLNFibre.DLN.RLCT.Validate.SchurState

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222RouteStep` — the committed `RouteStep` type, validated on (2,2,2) (fm3)

A non-vacuity / fidelity check on the committed `RouteStep` / `NodeChartFamily` / `PivotWitness` types
(`RouteMRecursion.lean`): the (2,2,2) chain admits a GENUINE root-anchored dispatch whose value folds to
`3/2 = lambdaCore(2,2,2)`. This de-risks the committed type WITHOUT touching the general `routeStep` body
(still `sorry`, gated on §4 realizability) — the (2,2,2) reachability is finite/decidable, so the achiever
witness is constructed directly here, no general coverage theorem needed.

What it exhibits (the (2,2,2) anchor, pp2 g208 / `Case222RouteMCover`):
- the two pivot witnesses `T = (0,0)` (codim `Mval M222 (0,0) = 4`) and `T = (1,0)` (codim `= 3 = minAdm`),
  both admissible (`∈ Adm M222`, by `decide`) — the root-anchored `PivotWitness M222`;
- a one-leaf `NodeChartFamily M222` whose `codimsOf = [4, 3]` (the binding path), folding via the banked
  `foldFamily_iInf_eq_half_minAdm` to `⨅ = ½·3 = 3/2`;
- a concrete `RouteStep M222 M222` BRANCH term (`schurState` splits + the two codims + the two
  root-anchored `PivotWitness`es), confirming the committed inductive's `branch` is inhabited with genuine
  data (NOT vacuous, NOT the smuggling traps fenced in `routeStep`'s docstring).

This is the (2,2,2)-instance VALUE/dispatch deliverable (distinct from crux2's #94 cover wrap). It validates
the type the general fix-body will fill; it does not fill it.
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

/-- The (2,2,2) chain: `M = (2,2,2)` on `Fin 3` (`L = 2`). -/
abbrev M222route : Fin 3 → ℕ := fun _ => 2

/-! ## The two root-anchored pivot witnesses (the (2,2,2) admissible strata) -/

/-- `T = (0,0)` is admissible for `M222`, with `Mval = 4` (the step-1 codim-4 stratum). The
root-anchored `PivotWitness M222route 4`. -/
def pivotWitness222_step1 : PivotWitness M222route 4 where
  T := ![0, 0]
  hAdm := by decide
  hCodim := by decide

/-- `T = (1,0)` is admissible for `M222`, with `Mval = 3 = minAdm` (the binding step-2 stratum). The
root-anchored `PivotWitness M222route 3` — the achiever's binding divisor. -/
def pivotWitness222_step2 : PivotWitness M222route 3 where
  T := ![1, 0]
  hAdm := by decide
  hCodim := by decide

/-- `minAdm(M222) = 3` (so `lambdaCore(2,2,2) = 3/2`). -/
theorem minAdm_M222 :
    ((Adm M222route).inf' (Adm_nonempty M222route) (Mval M222route)).toNat = 3 := by decide

/-! ## The (2,2,2) value folds to `3/2` over the committed family -/

/-- The single binding-path leaf's codim-list `[4, 3]` — the (2,2,2) achiever path (step-1 codim 4,
step-2 codim 3 = minAdm). The `PivotWitness M222route` for each entry: `4 ↦ step1`, `3 ↦ step2`. -/
def codimsOf222 : Unit → List ℕ := fun _ => [4, 3]

/-- Every codim on the (2,2,2) leaf path carries a root-anchored `PivotWitness M222route`. (`PivotWitness`
is a `Type` — data-carrying — so this is a `def`, not a `theorem`; the codim is recovered from the
membership proof, then the matching witness `Type` value is returned. `4 ↦ step1`, `3 ↦ step2`.) -/
def codimsOf222_witnessed :
    ∀ i : Unit, ∀ c ∈ codimsOf222 i, PivotWitness M222route c := by
  intro _ c hc
  refine if h4 : c = 4 then h4 ▸ pivotWitness222_step1
    else if h3 : c = 3 then h3 ▸ pivotWitness222_step2 else ?_
  exfalso
  simp only [codimsOf222, List.mem_cons, List.not_mem_nil, or_false] at hc
  omega

/-- **The (2,2,2) value folds to `3/2`.** Over the one-leaf family with `codimsOf = [4,3]` (the achiever
path, both codims root-anchored-witnessed, `3 = minAdm` binding), the `⨅` of the `foldDivisors` thresholds
is `½·minAdm = 3/2 = lambdaCore(2,2,2)`. Consumes the banked `foldFamily_iInf_eq_half_minAdm` — validating
that the committed `PivotWitness`/`foldDivisors` value-side fires on the anchor. -/
theorem case222_routeStep_value :
    (⨅ i : Unit, monomialThreshold (MonoData.foldDivisors (codimsOf222 i)).d
        (MonoData.foldDivisors (codimsOf222 i)).k (MonoData.foldDivisors (codimsOf222 i)).h)
      = 3 / 2 := by
  have hkey := foldFamily_iInf_eq_half_minAdm M222route codimsOf222
    (by rw [minAdm_M222]; omega) codimsOf222_witnessed ()
    (by rw [minAdm_M222]; simp only [codimsOf222, List.mem_cons]; decide)
  rw [hkey, minAdm_M222]
  norm_num

/-! ## A concrete `RouteStep M222 M222` BRANCH — the committed inductive is inhabited with genuine data

The committed `RouteStep.branch` is exercised with `schurState` splits, the two codims `4`/`3`, and the two
root-anchored `PivotWitness`es. This confirms `RouteStep M₀ M`'s `branch` constructor (root-anchored
`PivotWitness M₀`) admits a genuine (non-vacuous) (2,2,2) term — the type the general `routeStep` body fills.
The two cells use the SAME `schurState M222` split (the width reduction is shared; the pivot CHOICE = the
`codim`/witness, which differs). `hlo` (the `schurState` precondition) holds since `M222 s = 2 ≥ 1`. -/

/-- `M222` satisfies the `schurState` precondition (`1 ≤ M s` at the pivot vertices `s ≤ 1`). -/
theorem M222_hlo : ∀ s : Fin 3, s.val ≤ 1 → 1 ≤ M222route s := fun s _ => by
  simp only [M222route]; omega

/-- **The committed `RouteStep M222 M222` branch is inhabited with genuine root-anchored data.** Two pivot
cells (`Bool`), each with the `schurState M222` split, codims `4`/`3`, and the root-anchored
`PivotWitness M222route` (`step1`/`step2`). Confirms the `branch` constructor's fields (notably
`witness : (c) → PivotWitness M₀ (codim c)`) are jointly inhabitable on the (2,2,2) anchor — the committed
inductive is non-vacuous, root-anchored, and carries the §2-certified codim witnesses. -/
def case222_routeStep_branch : RouteStep M222route M222route :=
  .branch Bool inferInstance ⟨true⟩
    (fun _ => schurState M222route M222_hlo)
    (fun b => if b then 4 else 3)
    (fun b => by
      by_cases hb : b = true
      · simpa [hb] using pivotWitness222_step1
      · simp only [Bool.not_eq_true] at hb
        simpa [hb] using pivotWitness222_step2)

end DLNFibre.DLN.RLCT
