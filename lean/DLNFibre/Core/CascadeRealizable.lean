import DLNFibre.Core.CascadeRank
import DLNFibre.Core.Submult
import DLNFibre.Core.OrbitKostant

/-!
# `DLNFibre.Core.CascadeRealizable` — the diagonal cascade realizes its rank pattern

Rung 2+ of the cascade-realizability ladder (pp2 g228 / pp-r1realize #107, double-confirmed): the explicit
diagonal cascade `cascadeTuple d t := fun s ↦ partialId (d_{s+1}) (d_s) (t_s)` (Core's left-multiply
orientation) has every interval sub-product a single partial-identity, its rank the running window-min of
the block ranks — `count-the-1s`, no `Matrix.rank_mul_le`, no surjectivity.

`submult (cascadeTuple) i j = partialId (d_j) (d_i) (⨅_{i ≤ s < j} t_s)` (`submult_cascade`), so the rank
pattern `rankFn (cascadeTuple) i j = min over the window of the block ranks` (`rank_submult_cascade`),
capped by the endpoint widths. This is the matrix-level cascade computation; the §4 achiever witness
`T* ∈ RealizableRank` instantiates it with the achiever's running ranks (downstream, with the `embedRank`
2-index matching).
-/

open Matrix
namespace DLNFibre.Core

variable {k : Type*} [Field k] {N : ℕ}

/-- **The diagonal cascade** (Core left-multiply orientation): `A_s = partialId (d_{s+1}) (d_s) (t_s)`, the
rectangular partial-identity block with `t_s` surviving 1s. A genuine `Tuple d` (the block dimensions match
the `Tuple` factor shape `Matrix (Fin (d s.succ)) (Fin (d s.castSucc))`). -/
def cascadeTuple (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) : Tuple (k := k) d :=
  fun s => partialId k (d s.succ) (d s.castSucc) (t s)

/-- **Single-step (the cascade's one-block sub-product).** `submult (cascadeTuple) s.castSucc s.succ` is the
block `A_s = partialId (d_{s+1}) (d_s) (t_s)` itself. The base case of the cascade product iteration
(`submult i (i+1) = A_i`), via `submult_succ` + `submult_self`. -/
theorem submult_cascade_single (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) (s : Fin N) :
    submult d (cascadeTuple (k := k) d t) s.castSucc s.succ (Fin.castSucc_le_succ s)
      = partialId k (d s.succ) (d s.castSucc) (t s) := by
  rw [submult_succ d (cascadeTuple d t) s.castSucc s le_rfl, submult_self, Matrix.mul_one]
  rfl

/-- The surviving-1 count of the cascade sub-product over `[i, j]`: `d_i` at the empty window `i = j`
(the identity), and `min (t_p) (prev)` gaining the block `A_p` at each step. The recursion mirrors
`submult_succ` (left-multiply by `A_p = partialId · t_p`, so `partialId_mul` takes the `min`). The
window-min capped by `d_i` (the base width). -/
def cascadeCount (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) (i : Fin (N + 1)) :
    (j : Fin (N + 1)) → ℕ :=
  Fin.induction (d i) (fun p prev => min (t p) prev)

@[simp] theorem cascadeCount_self (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) (i : Fin (N + 1)) :
    cascadeCount d t i 0 = d i := rfl

@[simp] theorem cascadeCount_succ (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) (i : Fin (N + 1)) (p : Fin N) :
    cascadeCount d t i p.succ = min (t p) (cascadeCount d t i p.castSucc) := by
  simp [cascadeCount]

/-- **Rung 3 — the cascade interval sub-product is a single partial-identity** (the window-min iteration).
`submult (cascadeTuple) 0 j = partialId (d_j) (d_0) (cascadeCount 0 j)`, with `cascadeCount` the running
`min` of the block ranks (capped by `d_0`). By `Fin.induction` on `j` through `submult_succ`, applying the
product law `partialId_mul` at each step (the `t_p ≤ d_{p+1}` middle-dimension bound holds for the cascade's
admissible ranks — supplied as `ht`). The `i = 0` prefix row carries the running ranks `rankFn(0,j)`. -/
theorem submult_cascade_prefix (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ)
    (ht : ∀ p : Fin N, t p ≤ d p.castSucc) (j : Fin (N + 1)) :
    submult d (cascadeTuple (k := k) d t) 0 j (Fin.zero_le j)
      = partialId k (d j) (d 0) (cascadeCount d t 0 j) := by
  induction j using Fin.induction with
  | zero =>
    rw [submult_self, cascadeCount_self]
    -- the identity = the full partial-identity (every diagonal entry survives, `a < d 0` always)
    ext a b
    simp only [partialId, Matrix.of_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp [a.isLt]
    · rw [if_neg hab, if_neg (fun hc => hab (Fin.ext hc.1))]
  | succ p ih =>
    rw [submult_succ d (cascadeTuple d t) 0 p (Fin.zero_le _), ih, cascadeCount_succ,
      show cascadeTuple (k := k) d t p
          = partialId k (d p.succ) (d p.castSucc) (t p) from rfl,
      partialId_mul (k := k) (d p.succ) (d p.castSucc) (d 0) (t p)
        (cascadeCount d t 0 p.castSucc) (ht p)]

/-- **Rung 4a — the cascade's prefix rank pattern.** `rankPattern (cascadeTuple) 0 j` is the surviving-1
count of the prefix sub-product: `survivors (d_j) (d_0) (cascadeCount 0 j) = min (cascadeCount 0 j)
(min (d_j) (d_0))`. Composes `submult_cascade_prefix` (the sub-product is a single partial-identity) with
`rank_partialId` (its rank is the count). The achiever's running-rank row `r_{0j}` of the cascade. -/
theorem rankPattern_cascade_prefix (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ)
    (ht : ∀ p : Fin N, t p ≤ d p.castSucc) (j : Fin (N + 1)) :
    rankPattern d (cascadeTuple (k := k) d t) 0 j (Fin.zero_le j)
      = survivors (d j) (d 0) (cascadeCount d t 0 j) := by
  rw [rankPattern, submult_cascade_prefix d t ht j, rank_partialId]

/-- The cascade tuple's rank pattern is in the range of `rankFn` — `rankFn (cascadeTuple d t) ∈ Set.range
(rankFn d)`. **This statement is a TAUTOLOGY** (`⟨cascadeTuple d t, rfl⟩`: every tuple's pattern is in the
range of `rankFn`); it is **VACUOUS as an achiever-realizability claim** — it says nothing about WHICH pattern
is realized, in particular nothing tying it to the achiever stratum `r*`. Kept ONLY as the trivial
`Set.range` membership; the genuine, non-vacuous content lives elsewhere:

- **The (0, j) row IS computed** (`rankPattern_cascade_prefix`): `rankPattern (cascadeTuple) 0 j = survivors
  (d_j) (d_0) (cascadeCount t 0 j)`. THAT is the substance — the running-rank row of the realized pattern.
- **The achiever-realizability tie `rankFn (cascadeTuple t*) = r*` is NOT proven here** and is NOT this lemma.
  It needs `r*` defined INDEPENDENTLY from `Adm` (the minimising admissible exponent's rank pattern), then the
  equality matching `cascadeCount t*` to `r*`'s running ranks. That is the orbit-side tie #121 (`Adm ↔
  RealizableRank`, the genuine realizability) — a real obligation, NOT the `⟨_, rfl⟩` tautology below.

The general routeStep arm (#103) and the genuine #116-(2) realizability must cite #121, never this membership. -/
theorem cascadeTuple_rankFn_mem_range (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) :
    rankFn d (cascadeTuple (k := k) d t) ∈ Set.range (rankFn (k := k) d) :=
  ⟨cascadeTuple d t, rfl⟩

/-! ## The interior 2-index window (#122, general `i`): `rankPattern (cascadeTuple) i j` for `i > 0`

The general rank-pattern entry of the cascade — the `i`-RELATIVE running-min over the block window `[i, j)`
(NOT the from-`0` `cascadeCount`). `submult d (cascadeTuple) i j` (the partial product `A_{j-1} ⋯ A_i`)
gains a block `A_p` only for `i ≤ p < j`, so the surviving-1 count folds `min (t_p)` over exactly that
window, capped by the base width `d_i`. This is the genuine general rank-pattern computation (Core-native,
non-vacuous — it computes actual `Matrix.rank`s); it feeds the #121-(ii) achiever-realizability tie. -/

/-- The `i`-relative surviving-1 count of `submult (cascadeTuple) i j`: base `d_i` (at `j = i`, the
identity), folding `min (t_p)` for each block `A_p` with `i ≤ p < j` (the `if i ≤ p.castSucc` guard skips the
blocks below `i`, which `submult i` never multiplies). -/
def cascadeWindow (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) (i : Fin (N + 1)) :
    (j : Fin (N + 1)) → ℕ :=
  Fin.induction (d i) (fun p prev => if i ≤ p.castSucc then min (t p) prev else prev)

@[simp] theorem cascadeWindow_zero (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) (i : Fin (N + 1)) :
    cascadeWindow d t i 0 = d i := rfl

@[simp] theorem cascadeWindow_succ (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) (i : Fin (N + 1)) (p : Fin N) :
    cascadeWindow d t i p.succ
      = if i ≤ p.castSucc then min (t p) (cascadeWindow d t i p.castSucc)
        else cascadeWindow d t i p.castSucc := by
  simp [cascadeWindow]

/-- Below/at the base index, the window count is the base width: `cascadeWindow d t i j = d i` for
`j ≤ i` (no block `A_p` with `p ≥ i` is in `[i, j)`, so every fold guard is false). -/
theorem cascadeWindow_le_base (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) (i j : Fin (N + 1)) (hji : j ≤ i) :
    cascadeWindow d t i j = d i := by
  induction j using Fin.induction with
  | zero => rfl
  | succ p ih =>
    have hps : p.castSucc < p.succ := by rw [Fin.lt_def, Fin.val_succ, Fin.val_castSucc]; omega
    rw [cascadeWindow_succ, if_neg (fun hip =>
      absurd (lt_of_le_of_lt hip (lt_of_lt_of_le hps hji)) (lt_irrefl _))]
    exact ih (le_trans (le_of_lt hps) hji)

/-- **#122 — the cascade interval sub-product is a single partial-identity (general `i`).**
`submult (cascadeTuple) i j = partialId (d_j) (d_i) (cascadeWindow i j)` for `i ≤ j`, by `Fin.induction` on
`j` through `submult_succ` + `partialId_mul`. Below `i` (`j ≤ i`) the window count stays `d_i` and the only
reachable case is `j = i` (`submult_self = 1 = partialId (d_i)(d_i)(d_i)`); for `j = p.succ` with `i ≤
p.castSucc` the block `A_p` mins in `t_p` (the `i ≤ p.castSucc` guard matches `submult_succ`'s hypothesis).
Generalizes `submult_cascade_prefix` (the `i = 0` case). -/
theorem submult_cascade (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ)
    (ht : ∀ p : Fin N, t p ≤ d p.castSucc) (i j : Fin (N + 1)) (hij : i ≤ j) :
    submult d (cascadeTuple (k := k) d t) i j hij
      = partialId k (d j) (d i) (cascadeWindow d t i j) := by
  induction j using Fin.induction with
  | zero =>
    -- `i ≤ 0` ⟹ `i = 0`; `submult 0 0 = 1 = partialId (d 0)(d 0)(d 0)`.
    have hi0 : i = 0 := Fin.le_zero_iff.1 hij
    subst hi0
    rw [submult_self, cascadeWindow_zero]
    ext a b
    simp only [partialId, Matrix.of_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp [a.isLt]
    · rw [if_neg hab, if_neg (fun hc => hab (Fin.ext hc.1))]
  | succ p ih =>
    by_cases hip : i ≤ p.castSucc
    · -- the block `A_p` is in the window: `submult i p.succ = A_p * submult i p.castSucc`.
      rw [submult_succ d (cascadeTuple d t) i p hip, ih hip, cascadeWindow_succ, if_pos hip,
        show cascadeTuple (k := k) d t p = partialId k (d p.succ) (d p.castSucc) (t p) from rfl,
        partialId_mul (k := k) (d p.succ) (d p.castSucc) (d i) (t p)
          (cascadeWindow d t i p.castSucc) (ht p)]
    · -- `¬ i ≤ p.castSucc` and `i ≤ p.succ` force `i = p.succ` (the base of the window).
      have hcs : (p.castSucc : Fin (N + 1)).val = p.val := Fin.val_castSucc p
      have hss : (p.succ : Fin (N + 1)).val = p.val + 1 := Fin.val_succ p
      have hisucc : i = p.succ := by
        rcases Nat.lt_or_ge i.val p.succ.val with hlt | hge
        · exact absurd (by rw [Fin.le_def, hcs]; omega : i ≤ p.castSucc) hip
        · exact Fin.ext (le_antisymm (by simpa [Fin.le_def] using hij) hge)
      subst hisucc
      rw [submult_self, cascadeWindow_succ, if_neg hip]
      -- cascadeWindow at p.succ (= i, the base) reduces to d i; and submult_self = identity = full partialId
      rw [cascadeWindow_le_base d t p.succ p.castSucc (Fin.castSucc_le_succ p)]
      ext a b
      simp only [partialId, Matrix.of_apply, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp [a.isLt]
      · rw [if_neg hab, if_neg (fun hc => hab (Fin.ext hc.1))]

/-- **#122 — the cascade's general interior rank pattern.** `rankPattern (cascadeTuple) i j` is the
surviving-1 count of the interval sub-product: `survivors (d_j) (d_i) (cascadeWindow i j) = min
(cascadeWindow i j) (min (d_j) (d_i))` — the `i`-relative window-min of the block ranks, capped by the
endpoint widths. Composes `submult_cascade` (the sub-product is a single partial-identity) with
`rank_partialId`. The full 2-index rank pattern `r_{ij}` of the cascade — the general rank-pattern
computation the #121-(ii) achiever tie consumes (matched, on a fixed achiever `t = t*`, to the
independently-defined `r*`). Generalizes `rankPattern_cascade_prefix` (the `i = 0` row).

**The endpoint-cap form is correct ONLY under `ht`.** The RHS caps the window-min by the ENDPOINT widths
`d_i, d_j` (via `cascadeWindow`'s base `d_i` + `survivors`' `min (d_j)(d_i)`), NOT by the intermediate
widths `d_p` (`i < p < j`). In general (no `ht`) an intermediate `d_p < window-min` PINCHES the true rank
below this endpoint form — the genuine rank is `min(window-min t, min over ALL widths d_i..d_j)` (pp-rstar
#121/#127 cert §2b; e.g. `d=(5,1,3,1), t=(3,3,3)`, cell `(0,2)`: endpoint form `3`, true rank `1`, pinched
by `d_1=1`). The hypothesis `ht : ∀ p, t_p ≤ d_{p.castSucc}` is EXACTLY what kills the pinch: it threads
through `partialId_mul`'s `ha : a ≤ m` at each block, forcing the window-min `≤` every intermediate width,
so the intermediate cap never bites and the endpoint form equals the true rank. Verified exact (sympy over
ℚ): 0 mismatches in 329840 cells under `ht`; the pinch only shows on `t` violating `ht`. So the name =
content holds — but only with `ht`, which every cascade use-site (admissible `t*`, `adm_le_width`) supplies. -/
theorem rankPattern_cascade (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ)
    (ht : ∀ p : Fin N, t p ≤ d p.castSucc) (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern d (cascadeTuple (k := k) d t) i j hij
      = survivors (d j) (d i) (cascadeWindow d t i j) := by
  rw [rankPattern, submult_cascade d t ht i j hij, rank_partialId]

end DLNFibre.Core
