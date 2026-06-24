import DLNFibre.DLN.RLCT.Validate.RouteMLeaf
import DLNFibre.Core.CascadeRealizable
import DLNFibre.Core.CascadeAchiever

/-!
# `DLNFibre.DLN.RLCT.Validate.CascadeAchiever` — the genuine realizability tie (#121-(ii))

The orbit-side `r*` for an **admissible** exponent vector `T`, defined from `(M, T)` ALONE (no
`cascadeTuple`, no matrix), and the genuine equality

> `rankFn M (cascadeTuple M T) = achieverRankPattern M T`  for `T ∈ Adm M`.

`expSurvivor` is the running rank `ρ` (`ρ_0 = M_0`, `ρ_{j+1} = T_j`); `achieverRankPattern` is the
column-constant completion `ρ_j` above the diagonal, `M_i` on it, `0` below. This is a genuine equality of
two independently-defined `Fin (L+1) → Fin (L+1) → ℕ`-functions — the LHS is `Matrix.rank`s of explicit
cascade products, the RHS a combinatorial `if`-formula in `(M, T)` — NOT the `⟨cascadeTuple, rfl⟩`
tautology (`Core.CascadeRealizable.cascadeTuple_rankFn_mem_range` flags that vacuity).

**Scope (precision).** The proof uses ONLY clauses (i)+(ii) of admissibility (the per-block bound and the
weak-decrease); clause (iii) (last-zero, `admPred.2.2`) is NOT used — the equality holds without it. The
theorem is stated at `T ∈ Adm M` for the downstream consumer (#116-(2), #103 general arm), but the content
is the (i)+(ii) monotonicity chain (pp-rstar CERT §2c/2d, decorrelated codex-confirmed minimal subset).

**The cap correction (CERT §2b).** The general rank of an interval cascade product is
`min(window-min of T over [i,j), min over ALL widths M_i..M_j)` — NOT the endpoint cap `min(M_i, M_j)`
(an intermediate width can pinch: `M=(5,1,3,1), T=(3,3,3)`, cell `(0,2)`: endpoint-cap `3` but true rank
`1`). The committed `Core.rankPattern_cascade` carries the hypothesis `ht : ∀ p, T_p ≤ M_p`, under which the
intermediate pinch never bites (the window-min is already `≤` every intermediate width); so its endpoint
form is SOUND on its `ht` use-site. Here `adm_le_width` discharges `ht` from admissibility, and `H2`+`H3`
push the window-min below every endpoint width — so the collapse to `ρ_j` is forced by the monotonicity
chain, not asserted.
-/

open Matrix
open DLNFibre.Core

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! The achiever defs `expSurvivor` (the running rank `ρ`) and `achieverRankPattern` (the orbit-stratum
pattern `r*`) live network-free in `Core.CascadeAchiever` — shared with fm3's `RouteMBranchRead.realizes_ach`
lock and the geometric-codim identification (#116-(2), #103). Brought into scope here by `open DLNFibre.Core`
above; the simp lemmas `expSurvivor_zero`/`expSurvivor_succ` are likewise Core-side.

## H1 — `ρ = expSurvivor` is weakly decreasing under (i)+(ii) -/

/-- **H1 (ρ antitone).** Under admissibility clauses (i)-at-0 and (ii), `ρ = expSurvivor M T` is weakly
decreasing. By `Fin.antitone_iff_succ_le`, reduce to the per-step `ρ_{p+1} ≤ ρ_p`: at `p = 0`,
`ρ_1 = T_0 ≤ min(M_0, M_1) ≤ M_0 = ρ_0` (clause (i)); at `p ≥ 1`, `ρ_{p+1} = T_p ≤ T_{p-1} = ρ_p`
(clause (ii)). Clause (iii) is unused. -/
theorem expSurvivor_antitone (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : admPred M T) :
    Antitone (expSurvivor M T) := by
  obtain ⟨hbound, hdecr, _⟩ := hT
  rw [Fin.antitone_iff_succ_le]
  intro p
  rw [expSurvivor_succ]
  -- goal: T p ≤ expSurvivor M T p.castSucc
  rcases Nat.eq_zero_or_pos p.val with hp0 | hppos
  · -- p = 0: p.castSucc = 0, so expSurvivor = M 0; T p ≤ min(M 0, M 1) ≤ M 0.
    have hcast : (p.castSucc : Fin (L + 1)) = 0 := by
      apply Fin.ext; rw [Fin.val_castSucc, hp0]; rfl
    rw [hcast, expSurvivor_zero]
    have hb := hbound p
    simp only [admBound, hp0, if_true] at hb
    exact le_trans hb (min_le_left _ _)
  · -- p ≥ 1: p.castSucc = q.succ for q = p-1; expSurvivor = T q; T p ≤ T q by weak-decrease.
    set q : Fin L := ⟨p.val - 1, by omega⟩ with hq
    have hqv : q.val = p.val - 1 := rfl
    have hcast : (p.castSucc : Fin (L + 1)) = q.succ := by
      apply Fin.ext; rw [Fin.val_castSucc, Fin.val_succ, hqv]; omega
    have hqp : q ≤ p := by rw [Fin.le_def, hqv]; omega
    rw [hcast, expSurvivor_succ]
    exact hdecr q p hqp

/-! ## H2 — the window-min collapses to `ρ_j` -/

/-- **H2 (window-min = ρ_j).** Under H1, the `i`-relative window count of the cascade equals `ρ_j` for
`i < j`: `cascadeWindow M T i j = expSurvivor M T j`. The fold `min(T_p)` over `[i,j)` from base `M_i`
collapses to the last entry `T_{j-1} = ρ_j` because `ρ` is weakly decreasing (every `T_p` and the base
`M_i = ρ_i` are `≥ ρ_j`). Uses only clauses (i)+(ii) (through H1). -/
theorem cascadeWindow_eq_expSurvivor (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : admPred M T)
    (i j : Fin (L + 1)) (hij : i < j) :
    cascadeWindow M T i j = expSurvivor M T j := by
  have hanti := expSurvivor_antitone M T hT
  induction j using Fin.induction with
  | zero => exact absurd hij (Fin.not_lt_zero i)
  | succ p ih =>
    -- i < p.succ ⟹ i ≤ p.castSucc, so the fold step takes the `min`.
    have hip : i ≤ p.castSucc := by
      rw [Fin.le_def, Fin.val_castSucc]; rw [Fin.lt_def, Fin.val_succ] at hij; omega
    rw [cascadeWindow_succ, if_pos hip]
    -- the running window count `cascadeWindow i p.castSucc`: either the base `M i` (`i = p`) or IH (`i < p`).
    rcases lt_or_eq_of_le hip with hlt | heq
    · -- i < p.castSucc: IH gives `cascadeWindow i p.castSucc = expSurvivor p.castSucc`;
      -- then `min (T p) (expSurvivor p.castSucc) = expSurvivor p.succ` since `T p = expSurvivor p.succ`
      -- and `expSurvivor p.succ ≤ expSurvivor p.castSucc` (antitone).
      rw [ih hlt, ← expSurvivor_succ M T p]
      exact min_eq_left (hanti (Fin.castSucc_le_succ p))
    · -- i = p.castSucc: the window is at its base `M i`; `min (T p) (M i) = T p = expSurvivor p.succ`
      -- since `T p ≤ M (p.castSucc) = M i` (adm_le_width).
      rw [← heq, cascadeWindow_le_base M T i i le_rfl, expSurvivor_succ]
      have hbw : T p ≤ M p.castSucc := adm_le_width M T hT p
      rw [← heq] at hbw
      exact min_eq_left hbw

/-! ## H3 — the running rank is bounded by its own width

The single width cap `ρ_i ≤ M_i` for every `i` (from clause (i): `ρ_0 = M_0`, and `ρ_{i+1} = T_i ≤
admBound(i) ≤ M_{i+1}`). The two endpoint caps the collapse needs (`ρ_j ≤ M_i` and `ρ_j ≤ M_j` for
`i < j`) both follow: `ρ_j ≤ M_j` is this at `j`; `ρ_j ≤ ρ_i ≤ M_i` uses antitone (H1) for the left cap. -/

/-- **H3 (width cap).** The running rank is bounded by its own width: `ρ_i ≤ M_i` for every `i`. At `i = 0`
this is equality; at `i = p.succ` it is `T_p ≤ admBound(p) ≤ M_{p.succ}` (clause (i), with `admBound(0) =
min(M_0,M_1) ≤ M_1` and `admBound(p) = M_{p.succ}` for `p ≥ 1`). Uses only clause (i). -/
theorem expSurvivor_le_width (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : admPred M T) (i : Fin (L + 1)) :
    expSurvivor M T i ≤ M i := by
  obtain ⟨hbound, _, _⟩ := hT
  induction i using Fin.cases with
  | zero => rw [expSurvivor_zero]
  | succ p =>
    rw [expSurvivor_succ]
    have hb := hbound p
    rcases Nat.eq_zero_or_pos p.val with hp0 | hppos
    · -- p = 0: admBound = min(M_0,M_1); M (p.succ) = M 1.
      simp only [admBound, hp0, if_true] at hb
      have hps : M p.succ = M 1 := by
        apply congrArg M; apply Fin.ext
        rw [Fin.val_succ, hp0, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [hps]; exact le_trans hb (min_le_right _ _)
    · -- p ≥ 1: admBound = M (p.succ) directly.
      have hpne : ¬ p.val = 0 := by omega
      simp only [admBound, hpne, if_false] at hb
      exact hb

/-! ## The tie -/

/-- **#121-(ii) — the genuine realizability tie.** For an admissible exponent vector `T`, the cascade's
rank pattern equals the independently-defined achiever pattern `r*`:
`rankFn M (cascadeTuple M T) = achieverRankPattern M T`. Proof scope: clauses (i)+(ii) of `admPred` only
(clause (iii), last-zero, is unused). Off the triangle `i > j` both sides are `0`; on the diagonal both are
`M_i` (`rankPattern_self` vs the `if i = j` branch); for `i < j` the cascade rank
`survivors (M_j)(M_i)(cascadeWindow i j)` collapses to `ρ_j` via H2 (window = ρ_j) + H3a/H3b (every width
cap `≥ ρ_j`). -/
theorem rankFn_cascadeTuple_eq_achieverRankPattern {k : Type*} [Field k]
    (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    rankFn (k := k) M (cascadeTuple (k := k) M T) = achieverRankPattern M T := by
  have hadm : admPred M T := (Finset.mem_filter.1 hT).2
  have ht : ∀ p : Fin L, T p ≤ M p.castSucc := adm_le_width M T hadm
  have hanti := expSurvivor_antitone M T hadm
  funext i j
  rw [rankFn, achieverRankPattern]
  rcases lt_trichotomy i j with hlt | heq | hgt
  · -- i < j: cascade rank collapses to ρ_j.
    rw [dif_pos (le_of_lt hlt), if_pos hlt,
      rankPattern_cascade (k := k) M T ht i j (le_of_lt hlt),
      survivors, cascadeWindow_eq_expSurvivor M T hadm i j hlt]
    -- min (ρ_j) (min (M j) (M i)) = ρ_j since ρ_j ≤ M_j and ρ_j ≤ M_i.
    have hMj : expSurvivor M T j ≤ M j := expSurvivor_le_width M T hadm j
    have hMi : expSurvivor M T j ≤ M i :=
      le_trans (hanti (le_of_lt hlt)) (expSurvivor_le_width M T hadm i)
    exact min_eq_left (le_min hMj hMi)
  · -- i = j: diagonal, both sides = M i.
    subst heq
    rw [dif_pos le_rfl, if_neg (lt_irrefl i), if_pos rfl,
      rankPattern_self M (cascadeTuple (k := k) M T) i]
  · -- i > j: off the triangle, both sides = 0.
    rw [dif_neg (not_le.2 hgt), if_neg (not_lt.2 (le_of_lt hgt)), if_neg (Fin.ne_of_gt hgt)]

/-! ## Non-vacuity — the tie applies on the property-breaker witnesses (CERT §3)

The tie's `rankFn` side is `noncomputable` (`Matrix.rank`), so the in-file checks split: `decide` that the
witness `T` is genuinely admissible (the theorem's hypothesis is satisfiable — non-vacuous), and `#guard`
the `achieverRankPattern` value the theorem then certifies equals the genuine cascade rank. The cert verified
(sympy, exact ℚ ranks) that `rankFn` agrees with these `achieverRankPattern` values; this theorem is the Lean
proof of that agreement. -/

/-- The CERT §3 property-breaker `M = (1,1,1,2,1)`, `T = (1,1,1,0)` is genuinely admissible: the theorem
applies non-vacuously. (Increasing-width corner `M_2 = 1 < M_3 = 2`; strict pre-final drop `T_2 = 1 > 0`.) -/
example : (![1, 1, 1, 0] : Fin 4 → ℕ) ∈ Adm (![1, 1, 1, 2, 1] : Fin 5 → ℕ) := by decide

/-- The interior rank-2 variant `M = (3,3,3,2,2)`, `T = (3,3,2,0)` is admissible: a substantive
(non-`1×1`) interior cell. -/
example : (![3, 3, 2, 0] : Fin 4 → ℕ) ∈ Adm (![3, 3, 3, 2, 2] : Fin 5 → ℕ) := by decide

/-- The achiever's interior nonzero cell `(1,3)` on the property-breaker is rank `1` (`ρ_3 = T_2 = 1 > 0`):
the equality is content at a genuine interior stratum, not a boundary artefact. -/
example : achieverRankPattern (![1, 1, 1, 2, 1] : Fin 5 → ℕ) (![1, 1, 1, 0]) 1 3 = 1 := by decide

/-- The interior cell `(1,3)` on the rank-2 variant is rank `2` (`ρ_3 = T_2 = 2`): a substantive matrix
rank, not `0/1`. -/
example : achieverRankPattern (![3, 3, 3, 2, 2] : Fin 5 → ℕ) (![3, 3, 2, 0]) 1 3 = 2 := by decide

end DLNFibre.DLN.RLCT
