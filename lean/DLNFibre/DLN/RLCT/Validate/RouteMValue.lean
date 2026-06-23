import DLNFibre.DLN.RLCT.Validate.RouteMRecursion

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMValue` — the value fold over `routeMIota` (fm3 #103)

The value-side of the Route-M recursion: the `⨅` over the chart family `routeMIota M` of the per-leaf
`monomialThreshold` equals `½·minAdm(M)` (`= lambdaCore`, the CORE). This is the abstract value-fold
WIRING — it reduces the recursion's output to the banked `RouteMState.foldFamily_iInf_eq_half_minAdm`
(which needs ONLY the per-leaf root-anchored `PivotWitness` + one achiever leaf; NO cascade / NO
`RealizableRank` — the cascade-realizability is the #104 DESCENT's geometric soundness, separate).

The recursion accumulates each leaf's `MonoData` via `MonoData.appendDivisor` down the `Σ`-tree, so a leaf's
`data` is `MonoData.foldDivisors (codimsOf path)` for the path's accumulated codims. This file states the
value fold CONDITIONALLY on that accumulation (`hdata`) + the witness data — both supplied by the dispatcher
(`routeStep`'s branch) once it emits the genuine per-cell codims. The accumulation `hdata` + the
achiever-leaf-existence for general `M` is the named gap (rides the rank-pattern read / #104); here is the
value-fold LOGIC that consumes it, abstract over the family.
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The value fold over `routeMIota` (the #103 value-wiring).** Given the recursion-accumulation
`hdata : (routeAtlas M M).data i = foldDivisors (codimsOf i)` (each leaf's `MonoData` is the
`appendDivisor`-fold of its path's codims) + the `foldFamily_iInf` data (every codim a root-anchored
`PivotWitness M`, an achiever leaf `i₀` with `minAdm ∈ codimsOf i₀`, `minAdm ≥ 1`), the `⨅` over the chart
family of the per-leaf `monomialThreshold` is `½·minAdm(M)`. Reduces to
`RouteMState.foldFamily_iInf_eq_half_minAdm` — the value rides ONLY the `PivotWitness` codims (no cascade).
The hypotheses `hdata`/`hwit`/`hbind₀` are what `routeStep`'s branch supplies (the named gap); this is the
value-fold logic, abstract over the family.

**Root-anchoring (the codims fidelity point, fm3 decl-check).** `hwit` requires each path codim to be a
`PivotWitness M` — i.e. `codim = (Mval M T).toNat` for `T ∈ Adm M` at the FIXED ROOT `M`, NOT the reduced
node's `minAdm`. This is load-bearing for `(C≥)`: a reduced node's `minAdm` UNDERSHOOTS (it can be `< minAdm
M`), which would break the lower bound. Worked anchors (decl-checked): `(2,2,2)` chain `→(1,1,2)→(0,0,2)`
(2 branch nodes), `codimsOf = [Mval(2,2,2)(0,0)=4, Mval(2,2,2)(1,0)=3=minAdm]`, fold `min(2,3/2)=3/2`;
`(3,2,3)` chain `→(2,1,3)→(1,0,3)` (2 branch nodes), `codimsOf = [6, 5]` (BOTH root `Mval(3,2,3) T`:
`Mval(1,0)=5=minAdm` the achiever, `Mval(0,0)=Mval(2,0)=6`; NOT the reduced `minAdm(2,1,3)=2`), fold
`min(3, 5/2)=5/2`. The `PivotWitness M` type enforces the root-anchoring; this lemma consumes it. -/
theorem routeM_value_eq (M : Fin (L + 1) → ℕ) (codimsOf : routeMIota M → List ℕ)
    (hdata : ∀ i, (routeAtlas M M).data i = MonoData.foldDivisors (codimsOf i))
    (hm₀ : 1 ≤ ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat)
    (hwit : ∀ i, ∀ c ∈ codimsOf i, PivotWitness M c)
    (i₀ : routeMIota M) (hbind₀ : ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat ∈ codimsOf i₀) :
    (⨅ i : routeMIota M, monomialThreshold (routeD M i) (routeK M i) (routeH M i))
      = ((((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat : ℝ≥0∞)) / 2 := by
  have hrw : ∀ i : routeMIota M,
      monomialThreshold (routeD M i) (routeK M i) (routeH M i)
        = monomialThreshold (MonoData.foldDivisors (codimsOf i)).d
            (MonoData.foldDivisors (codimsOf i)).k (MonoData.foldDivisors (codimsOf i)).h := by
    intro i
    unfold routeD routeK routeH
    rw [hdata i]
  rw [iInf_congr hrw]
  exact foldFamily_iInf_eq_half_minAdm M codimsOf hm₀ hwit i₀ hbind₀

end DLNFibre.DLN.RLCT
