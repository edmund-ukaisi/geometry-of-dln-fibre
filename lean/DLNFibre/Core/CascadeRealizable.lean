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

end DLNFibre.Core
