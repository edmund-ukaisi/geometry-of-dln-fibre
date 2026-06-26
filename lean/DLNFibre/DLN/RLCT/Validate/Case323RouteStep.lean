import DLNFibre.DLN.RLCT.Validate.RouteMRecursion
import DLNFibre.DLN.RLCT.Validate.SchurState

/-!
# `DLNFibre.DLN.RLCT.Validate.Case323RouteStep` — the `(3,2,3)` SECOND anchor (fm3, #103 corroboration)

A second decide-checked anchor for the committed `RouteStep` / `PivotWitness` / `foldFamily` value-side,
alongside the `(2,2,2)` anchor (`Case222RouteStep`). Same mechanism on a second, ASYMMETRIC instance
(`M = (3,2,3)`, `L = 2`) — corroboration that the dispatch + value fold is not `(2,2,2)`-special. The
general achiever stays the named gap regardless; this hardens the base.

The `(3,2,3)` chain `(3,2,3) → (2,1,3) → (1,0,3)[leaf]` has 2 branch nodes (decl-confirmed: `#eval` vs
committed `Lambda.lean`). The ROOT-anchored codims (the controller's pinned distinction —
`RouteMState`'s `foldFamily` docstring): `minAdm(3,2,3) = 5` (achiever `T* = (1,0)`, `Mval(M, T*) = 5`); a
second root stratum `T = (0,0)` gives `Mval(M, 0) = 6`. So `codimsOf323 = [6, 5]` (`6` non-binding, `5 =
minAdm` binding), folding via the banked `foldFamily_iInf_eq_half_minAdm` to `⨅ = ½·5 = 5/2`. The 2nd branch
node `(2,1,3)` has REDUCED-state `minAdm = 2`, but its appended codim is the ROOT `Mval = 6 ≥ 5` — using the
reduced `2` would undershoot the (C≥) bound; this anchor makes the root-anchoring necessity concrete.
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

/-- The `(3,2,3)` chain: `M = (3,2,3)` on `Fin 3` (`L = 2`). The asymmetric second anchor. -/
abbrev M323route : Fin 3 → ℕ := ![3, 2, 3]

/-! ## The two root-anchored pivot witnesses (the `(3,2,3)` admissible strata) -/

/-- `T = (0,0)` is admissible for `M323`, with `Mval = 6` (a root stratum, non-binding). The root-anchored
`PivotWitness M323route 6`. -/
def pivotWitness323_root : PivotWitness M323route 6 where
  T := ![0, 0]
  hAdm := by decide
  hCodim := by decide

/-- `T = (1,0)` is admissible for `M323`, with `Mval = 5 = minAdm` (the binding stratum, the achiever). The
root-anchored `PivotWitness M323route 5` — the achiever's binding divisor. -/
def pivotWitness323_achiever : PivotWitness M323route 5 where
  T := ![1, 0]
  hAdm := by decide
  hCodim := by decide

/-- `minAdm(M323) = 5` (so `lambdaCore(3,2,3) = 5/2`). -/
theorem minAdm_M323 :
    ((Adm M323route).inf' (Adm_nonempty M323route) (Mval M323route)).toNat = 5 := by decide

/-! ## The `(3,2,3)` value folds to `5/2` over the committed family -/

/-- The single binding-path leaf's codim-list `[6, 5]` — the `(3,2,3)` achiever path (root codim 6,
achiever codim 5 = minAdm). The `PivotWitness M323route` for each entry: `6 ↦ root`, `5 ↦ achiever`. -/
def codimsOf323 : Unit → List ℕ := fun _ => [6, 5]

/-- Every codim on the `(3,2,3)` leaf path carries a root-anchored `PivotWitness M323route`. (`6 ↦ root`,
`5 ↦ achiever`; the codim is recovered from the membership proof, then the matching witness is returned.) -/
def codimsOf323_witnessed :
    ∀ i : Unit, ∀ c ∈ codimsOf323 i, PivotWitness M323route c := by
  intro _ c hc
  refine if h6 : c = 6 then h6 ▸ pivotWitness323_root
    else if h5 : c = 5 then h5 ▸ pivotWitness323_achiever else ?_
  exfalso
  simp only [codimsOf323, List.mem_cons, List.not_mem_nil, or_false] at hc
  omega

/-- **The `(3,2,3)` value folds to `5/2`.** Over the one-leaf family with `codimsOf = [6, 5]` (the achiever
path, both codims root-anchored-witnessed, `5 = minAdm` binding), the `⨅` of the `foldDivisors` thresholds
is `½·minAdm = 5/2 = lambdaCore(3,2,3)`. The asymmetric SECOND anchor corroborating `case222_routeStep_value`
— the value-side fires identically on a non-`(2,2,2)` instance. -/
theorem case323_routeStep_value :
    (⨅ i : Unit, monomialThreshold (MonoData.foldDivisors (codimsOf323 i)).d
        (MonoData.foldDivisors (codimsOf323 i)).k (MonoData.foldDivisors (codimsOf323 i)).h)
      = 5 / 2 := by
  have hkey := foldFamily_iInf_eq_half_minAdm M323route codimsOf323
    (by rw [minAdm_M323]; omega) codimsOf323_witnessed ()
    (by rw [minAdm_M323]; simp only [codimsOf323, List.mem_cons]; decide)
  rw [hkey, minAdm_M323]
  norm_num

end DLNFibre.DLN.RLCT
