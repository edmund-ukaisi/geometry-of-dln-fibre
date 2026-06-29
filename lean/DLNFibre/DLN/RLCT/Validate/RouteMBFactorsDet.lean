import DLNFibre.DLN.RLCT.Validate.RouteMChartFactorFold

/-!
# `RouteMBFactorsDet` — per-boundary `[schur, chain, ldu]` telescope (Phase B, obligation 3)

The abs-det of a `composeFold` over `L` per-boundary factor triples `[schur s, chain s, ldu s]`
telescopes to `∏ s : Fin L, eng s`, where `eng s` is the schur·ldu engine value at boundary `s`
and the chain factors contribute det 1.

## Main result

`foldDerivList_abs_det_perBoundary`: given
- `schur chain ldu : Fin L → ChartFactor N` (the per-boundary factor families),
- `eng : Fin L → ℝ` (the engine value at each boundary),
- `BFactors = (List.finRange L).flatMap (fun s => [schur s, chain s, ldu s])`,
- `aS, aC, aL : Fin L → ℝ` (explicit per-factor abs-det values),
- `hfac` tying the `foldDerivList` map to the interleaved triple list,
- `hC : ∀ s, aC s = 1` (chain factors have det 1),
- `hSL : ∀ s, aS s * aL s = eng s` (schur·ldu product = engine),
the composite abs-det equals `∏ s : Fin L, eng s`.

Route: `composeFold_abs_det` reduces to `tripleDetList.prod`; the chain-1 collapse
`tripleDetList_prod_chain_one` then reduces to `∏ s, eng s`.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {N : ℕ}

/-! ## Auxiliary: the interleaved per-triple det list -/

/-- The interleaved det list for `L` boundaries:
`(finRange L).flatMap (fun s => [aS s, aC s, aL s])`.
When all chain entries `aC s = 1`, its product is `∏ s, aS s * aL s`. -/
def tripleDetList (L : ℕ) (aS aC aL : Fin L → ℝ) : List ℝ :=
  (List.finRange L).flatMap (fun s => [aS s, aC s, aL s])

@[simp]
theorem tripleDetList_nil (aS aC aL : Fin 0 → ℝ) :
    tripleDetList 0 aS aC aL = [] := by
  simp [tripleDetList]

theorem tripleDetList_succ (L : ℕ) (aS aC aL : Fin (L + 1) → ℝ) :
    tripleDetList (L + 1) aS aC aL =
      [aS 0, aC 0, aL 0] ++
        tripleDetList L
          (fun s : Fin L => aS s.succ)
          (fun s : Fin L => aC s.succ)
          (fun s : Fin L => aL s.succ) := by
  simp only [tripleDetList, List.finRange_succ, List.flatMap_cons, List.flatMap_map]

/-- When all chain entries equal 1, `(tripleDetList L aS aC aL).prod = ∏ s, aS s * aL s`. -/
theorem tripleDetList_prod_chain_one (L : ℕ) (aS aL : Fin L → ℝ)
    (aC : Fin L → ℝ) (hC : ∀ s : Fin L, aC s = 1) :
    (tripleDetList L aS aC aL).prod = ∏ s : Fin L, (aS s * aL s) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [tripleDetList_succ, List.prod_append]
    rw [Fin.prod_univ_succ]
    simp only [List.prod_cons, List.prod_nil, hC 0, mul_one]
    congr 1
    · ring
    · exact ih (fun s => aS s.succ) (fun s => aL s.succ) (fun s => aC s.succ)
              (fun s => hC s.succ)

/-! ## Main theorem: the per-boundary fold telescopes -/

/-- **The per-boundary telescope**: the abs-det of a `composeFold` over
`(finRange L).flatMap (fun s => [schur s, chain s, ldu s])` equals `∏ s : Fin L, eng s`,
given:
- `hfac`: the `foldDerivList`-map yields the interleaved triple `tripleDetList L aS aC aL`,
- `hC`: every chain abs-det `aC s = 1`,
- `hSL`: `aS s * aL s = eng s` for each boundary.

The parent wires `aS`, `aC`, `aL` to the concrete per-factor det values (from
`schurChartFactor_abs_det`, `chainChartFactor_abs_det`, `lduChartFactor_abs_det`). -/
theorem foldDerivList_abs_det_perBoundary {L : ℕ}
    (schur chain ldu : Fin L → ChartFactor N)
    (eng : Fin L → ℝ)
    (u : Fin N → ℝ)
    (aS aC aL : Fin L → ℝ)
    (hfac : (foldDerivList
        ((List.finRange L).flatMap (fun s => [schur s, chain s, ldu s]))
        u).map (fun D => |LinearMap.det D.toLinearMap|) =
      tripleDetList L aS aC aL)
    (hC : ∀ s : Fin L, aC s = 1)
    (hSL : ∀ s : Fin L, aS s * aL s = eng s) :
    |LinearMap.det
        ((foldDerivList
          ((List.finRange L).flatMap (fun s => [schur s, chain s, ldu s]))
          u).prod).toLinearMap| =
      ∏ s : Fin L, eng s := by
  rw [composeFold_abs_det _ u (tripleDetList L aS aC aL) hfac,
      tripleDetList_prod_chain_one L aS aL aC hC]
  congr 1; ext s; exact hSL s

/-! ## Non-vacuity: `L = 1` instance -/

/-- `L = 1` witness: a single `[F, G, H]` fold with chain `G` having abs-det 1 and
`|det F| * |det H| = eng` telescopes to `eng`. -/
example (F G H : ChartFactor N) (u : Fin N → ℝ) (eng : ℝ)
    (hfac : (foldDerivList [F, G, H] u).map
        (fun D => |LinearMap.det D.toLinearMap|) =
      [eng, 1, 1]) :
    |LinearMap.det ((foldDerivList [F, G, H] u).prod).toLinearMap|
        = ∏ _s : Fin 1, eng := by
  rw [composeFold_abs_det [F, G, H] u [eng, 1, 1] hfac]
  simp

end DLNFibre.DLN.RLCT
