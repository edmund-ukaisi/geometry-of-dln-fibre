import DLNFibre.DLN.Aoyagi.Corank2NativeValue334
import DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

/-!
# `DLN.Aoyagi.Corank2CleanEntryBase334` — the (B) seat scaffolding for the CLEAN-144 `hentry`

Base definitions + light lemmas the per-pivot entry-equalities (`Corank2CleanEntry334`) ride:

- `coreGen_eWrap_entry_ij` — `coreGen dvec eWrap (finProdFinEquiv (i,j)) u = (A1 u · A0 u) i j`
  (the reduction of the abstract `coreGen` index to the concrete `4×3` product entry, via
  `mult_eWrap`).
- `A1_00 … A1_32` — the 12 entries of `A1` as `OfNat`-indexed coordinate reads (so the entry algebra
  `ring`-matches the composite's `OfNat` reads, avoiding a `Fin.mk` vs literal atom mismatch).
- `leafMap` — the whole-conjugate leaf composite `bb S1 p1 ∘ nativeChart1 p1 ∘ bb (σC1 p1) p2 ∘
  bb (σC2 p1) p3`, and `gFin_eq_leafMap` : `gFin c = leafMap (pivot1 c) (pivot2 c) (pivot3 c)`.
- `ijpair` / `k0` — the survivor `coreGen` entry index of each clean leaf, `k0 c = finProdFinEquiv
  (ijpair (pivot1 c) (pivot2 c))` (the column `= A0`-column of `p1`, the row read off the born
  mechanism; the 36 clean `(p1,p2)` pairs, verified by the pnp 288-leaf census).
- `prod_ek₀` — `∏_d (w d)^(ek₀ c d) = w (pivot1 c) · w (pivot2 c)` (pivot-cross monomial collapse,
  `pivots_distinct`).
- `cleanPairs` / `IsClean` — the CLEAN-144 predicate (single-entry pivot-cross survivor leaves).
-/

open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativeValue334
open DLNFibre.DLN.Aoyagi.NativePerm334
open DLNFibre.DLN.Aoyagi.NativeShear334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi.CleanHentry334

/-! ## §1 — the `coreGen`→`(A1·A0)`-entry reduction and the `A1` entry reads -/

/-- **`coreGen` at `eWrap` = the `(A1·A0)` matrix entry** (the `mult_eWrap` product form; the
`coreGen` index `k` reindexed by `finProdFinEquiv.symm`). -/
theorem coreGen_eWrap_entry (k : Fin (dvec (Fin.last 2) * dvec 0)) (u : Fin 21 → ℝ) :
    coreGen dvec eWrap k u
      = (A1 u * A0 u) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp only [coreGen]
  exact congrFun (congrFun (mult_eWrap u) _) _

/-- **`coreGen` at `eWrap` = the `(A1·A0)` matrix entry** indexed by an explicit `(i, j)`. -/
theorem coreGen_eWrap_entry_ij (i : Fin 4) (j : Fin 3) (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (i, j)) u = (A1 u * A0 u) i j := by
  simp only [coreGen, Equiv.symm_apply_apply]
  exact congrFun (congrFun (mult_eWrap u) _) _

theorem A1_00 (u : Fin 21 → ℝ) : A1 u 0 0 = u 8 := rfl
theorem A1_01 (u : Fin 21 → ℝ) : A1 u 0 1 = u 12 := rfl
theorem A1_02 (u : Fin 21 → ℝ) : A1 u 0 2 = u 16 := rfl
theorem A1_10 (u : Fin 21 → ℝ) : A1 u 1 0 = u 9 := rfl
theorem A1_11 (u : Fin 21 → ℝ) : A1 u 1 1 = u 13 := rfl
theorem A1_12 (u : Fin 21 → ℝ) : A1 u 1 2 = u 17 := rfl
theorem A1_20 (u : Fin 21 → ℝ) : A1 u 2 0 = u 10 := rfl
theorem A1_21 (u : Fin 21 → ℝ) : A1 u 2 1 = u 14 := rfl
theorem A1_22 (u : Fin 21 → ℝ) : A1 u 2 2 = u 18 := rfl
theorem A1_30 (u : Fin 21 → ℝ) : A1 u 3 0 = u 11 := rfl
theorem A1_31 (u : Fin 21 → ℝ) : A1 u 3 1 = u 15 := rfl
theorem A1_32 (u : Fin 21 → ℝ) : A1 u 3 2 = u 19 := rfl

/-! ## §2 — the leaf composite and its identification with `gFin` -/

/-- **The whole-conjugate leaf composite** in pivot form: node-1 `bb S1 p1 ∘ nativeChart1 p1`,
node-2 `bb (σC1 p1) p2`, node-3 `bb (σC2 p1) p3` — `= gFin c` at the leaf's pivots. -/
noncomputable def leafMap (p1 p2 p3 : Fin 21) : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  fun w => blockBlowupMap S1 p1 (nativeChart1 p1
    (blockBlowupMap (sigmaC1Fs p1) p2 (blockBlowupMap (sigmaC2Fs p1) p3 w)))

/-- `gFin c = leafMap (pivot1 c) (pivot2 c) (pivot3 c)` — the flat leaf family is the pivot
composite (definitional: `gFlat` unfolds to `leafMap` at `idxEquiv c`'s pivots). -/
theorem gFin_eq_leafMap (c : Fin numCharts) (w : Fin 21 → ℝ) :
    gFin c w = leafMap (pivot1 c) (pivot2 c) (pivot3 c) w := rfl

/-! ## §3 — the survivor entry index `ijpair` / `k0` (pnp 288-leaf census) -/

/-- **The survivor `coreGen` entry position** `(i, j)` of the clean leaf `(p1, p2)`: column `j` is
the `A0`-column of `p1`; row `i` is the born-mechanism survivor row (the 36 clean pairs = CLEAN-144;
off the clean pairs the value is a placeholder). -/
def ijpair (p1 p2 : Fin 21) : Fin 4 × Fin 3 :=
  if p1 = 0 then
    (if p2 = 20 then (0, 0) else if p2 = 4 then (1, 0) else if p2 = 6 then (2, 0) else (3, 0))
  else if p1 = 1 then
    (if p2 = 0 then (0, 0) else if p2 = 5 then (1, 0) else if p2 = 7 then (2, 0) else (3, 0))
  else if p1 = 2 then
    (if p2 = 4 then (0, 1) else if p2 = 20 then (1, 1) else if p2 = 3 then (2, 1) else (3, 1))
  else if p1 = 3 then
    (if p2 = 6 then (0, 2) else if p2 = 2 then (1, 2) else if p2 = 20 then (2, 2) else (3, 2))
  else if p1 = 4 then
    (if p2 = 2 then (0, 1) else if p2 = 0 then (1, 1) else if p2 = 6 then (2, 1) else (3, 1))
  else if p1 = 5 then
    (if p2 = 4 then (0, 1) else if p2 = 1 then (1, 1) else if p2 = 7 then (2, 1) else (3, 1))
  else if p1 = 6 then
    (if p2 = 3 then (0, 2) else if p2 = 4 then (1, 2) else if p2 = 0 then (2, 2) else (3, 2))
  else if p1 = 7 then
    (if p2 = 6 then (0, 2) else if p2 = 5 then (1, 2) else if p2 = 1 then (2, 2) else (3, 2))
  else (if p2 = 0 then (0, 0) else if p2 = 2 then (1, 0) else if p2 = 3 then (2, 0) else (3, 0))

/-- **The survivor `coreGen` index** `k0 c = finProdFinEquiv (ijpair (pivot1 c) (pivot2 c))` — the
entry the CLEAN-144 loss dominates (fed to `rlctAt_coreGen334_ge_four_of_survivor_entries`). -/
noncomputable def k0 (c : Fin numCharts) : Fin (dvec (Fin.last 2) * dvec 0) :=
  finProdFinEquiv (ijpair (pivot1 c) (pivot2 c))

/-! ## §4 — the pivot-cross monomial collapse -/

/-- **`∏_d (w d)^(ek₀ c d) = w (pivot1 c) · w (pivot2 c)`** — the pivot-cross survivor monomial
(`ek₀ = 1@p1 + 1@p2`, `pivots_distinct`). -/
theorem prod_ek₀ (c : Fin numCharts) (w : Fin 21 → ℝ) :
    ∏ d, (w d) ^ (ek₀ c d) = w (pivot1 c) * w (pivot2 c) := by
  have hstep : ∀ d : Fin 21, (w d) ^ (ek₀ c d)
      = if d = pivot1 c ∨ d = pivot2 c then w d else 1 := by
    intro d
    simp only [ek₀]
    split_ifs <;> simp
  simp_rw [hstep]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one,
    show Finset.filter (fun d : Fin 21 => d = pivot1 c ∨ d = pivot2 c) Finset.univ
        = {pivot1 c, pivot2 c} from by
      ext d; simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton],
    Finset.prod_pair (pivots_distinct c)]

/-! ## §5 — the CLEAN-144 predicate -/

/-- The 36 clean `(p1, p2)` pivot pairs (single-entry pivot-cross survivor; the CLEAN-144 leaves are
those with `(pivot1, pivot2)` in this set). -/
def cleanPairs : Finset (Fin 21 × Fin 21) :=
  {(0, 2), (0, 4), (0, 6), (0, 20), (1, 0), (1, 4), (1, 5), (1, 7),
   (2, 0), (2, 3), (2, 4), (2, 20), (3, 2), (3, 4), (3, 6), (3, 20),
   (4, 0), (4, 2), (4, 6), (4, 20), (5, 0), (5, 1), (5, 4), (5, 7),
   (6, 0), (6, 2), (6, 3), (6, 4), (7, 1), (7, 4), (7, 5), (7, 6),
   (20, 0), (20, 2), (20, 3), (20, 4)}

/-- **A leaf is CLEAN** iff its `(pivot1, pivot2)` is a clean pivot-cross pair. -/
def IsClean (c : Fin numCharts) : Prop := (pivot1 c, pivot2 c) ∈ cleanPairs

-- Forced axiom gate: the base scaffolding rests only on `[propext, Classical.choice, Quot.sound]`.
#assert_banked_clean_batch [coreGen_eWrap_entry, coreGen_eWrap_entry_ij, gFin_eq_leafMap, prod_ek₀]

end DLNFibre.DLN.Aoyagi.CleanHentry334
