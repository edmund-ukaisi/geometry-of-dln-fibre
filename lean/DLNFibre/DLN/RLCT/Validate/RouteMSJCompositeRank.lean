import DLNFibre.DLN.RLCT.Validate.MinAdmPermInvariance
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# `RouteMSJCompositeRank` — the composite-rank codim `CRrec` + the (I) deep gate

The Route-B deep-gate obligation (I) of the `(□)` capstone (deepgate cert §1(A) + codex
answer §2). Two deliverables:

* **`CRrec M s`** — the composite-rank codim of the deep tail: the parameter-space codim of
  the locus `{rank(product of M) ≤ s}`, given by the **head-peeling recursion** (the canonical
  CR def; reuses the banked `redChain`). Specialises to `minAdm` at `s = 0`
  (`CRrec_zero_eq_minAdm`).
* **THE (I) THEOREM `minAdm_le_compositeRank_add`** — the deep-rank stratification of the QIP:

      minAdm M ≤ CRrec (deepTail M) s + minAdm (M₀, M₁, s)     (for every s)

  where `deepTail M = (M₂, …, M_last)`. Supplies input (I) — the deep-rank stratification — to the
  deep branch `C_k ≥ minAdm(M) − ab`; the full inequality also needs (II)
  `minAdm(M₀,M₁,s) ≤ ab + us − γ_s` and the γ_s/charge assembly (both stepbuild's).

**Strategy (all head-peel; `minAdm` permutation-invariance is banked, `MinAdmPermInvariance`).**
The genuine content is the KEY lemma `minAdm (Fin.snoc D t) ≤ t·s + CRrec D s` (append a head
width `t` to the deep tail `D`). Head-peeling `Fin.snoc D t` keeps `t` at the tail (untouched)
and reduces `D`'s front — aligning exactly with `CRrec`'s head-peel recursion, so the induction
closes with a 3-chain base case. The (I) theorem head-peels `M`, turns `redChain t M =
Fin.cons t (deepTail M)` into snoc form via the one permutation fact `minAdm (Fin.cons t D) =
minAdm (Fin.snoc D t)` (`Fin.snoc_eq_cons_rotate` + `minAdm_comp_perm`), and applies KEY.

`CRrec`'s head-peel value equals the cert's last-peel CR (reversal agreement, 65k cases 0
fails); it is the canonical CR def (controller decision, 2026-07-15).
-/

open scoped BigOperators
open Finset

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The composite-rank codim `CRrec` (head-peeling recursion) -/

/-- **The composite-rank codim `CRrec M s`** — the parameter-space codim of
`{rank(product of M) ≤ s}`, by head-peeling (the canonical CR def; deepgate cert §1(A)).
- `Fin 1` (vacuous one-width): `0`.
- `Fin 2` (the two-width leaf, a single `M₀×M₁` matrix): `(M₀−s)(M₁−s)` (ℕ-truncated) — the
  determinantal codim of `{rank ≤ s}`.
- `Fin (L+3)` (`≥ 3` widths): min over the leading-pivot rank `t ≤ min(M₀,M₁)` of
  `(M₀−t)(M₁−t) + CRrec (redChain t M) s` (peel the front layer, one fewer width). -/
def CRrec : {L : ℕ} → (M : Fin (L + 1) → ℕ) → (s : ℕ) → ℕ
  | 0, _, _ => 0
  | 1, M, s => (M 0 - s) * (M 1 - s)
  | (_ + 1 + 1), M, s =>
      (Finset.range (min (M 0) (M 1) + 1)).inf' (by simp)
        (fun t => (M 0 - t) * (M 1 - t) + CRrec (redChain t M) s)

/-- `CRrec` on a `≥ 3`-width chain unfolds to the front-peel min. -/
theorem CRrec_succ_succ (M : Fin (L + 1 + 1 + 1) → ℕ) (s : ℕ) :
    CRrec M s = (Finset.range (min (M 0) (M 1) + 1)).inf' (by simp)
        (fun t => (M 0 - t) * (M 1 - t) + CRrec (redChain t M) s) := rfl

/-- `CRrec` on a two-width leaf is the determinantal codim `(M₀−s)(M₁−s)`. -/
theorem CRrec_leaf (M : Fin 2 → ℕ) (s : ℕ) : CRrec M s = (M 0 - s) * (M 1 - s) := rfl

/-- **`CRrec M 0 = minAdmRec M`.** At `s = 0` the leaf is `(M₀−0)(M₁−0) = M₀·M₁` and the recursion
matches `minAdmRec`'s (`{product = 0}` is `{rank ≤ 0}`). By arity induction. -/
theorem CRrec_zero_eq_minAdmRec : {L : ℕ} → (M : Fin (L + 1) → ℕ) →
    CRrec M 0 = minAdmRec M
  | 0, _ => rfl
  | 1, M => by rw [CRrec_leaf, minAdmRec_leaf, Nat.sub_zero, Nat.sub_zero]
  | (_ + 1 + 1), M => by
      rw [CRrec_succ_succ, minAdmRec_succ_succ]
      refine Finset.inf'_congr _ rfl (fun t _ => ?_)
      rw [CRrec_zero_eq_minAdmRec (redChain t M)]

/-- **`CRrec M 0 = minAdm M`** — the `s = 0` specialization recovers the full minimal admissible
codim. -/
theorem CRrec_zero_eq_minAdm (M : Fin (L + 1) → ℕ) : CRrec M 0 = minAdm M := by
  rw [CRrec_zero_eq_minAdmRec, minAdmRec_eq_minAdm]

/-! ## The permutation + peel bridges (prepend `t` ↔ append `t`; peel under the appended tail) -/

/-- **Prepend = append (permutation-invariance).** `minAdm (Fin.cons t D) = minAdm (Fin.snoc D t)`:
moving the head width `t` to the tail is a cyclic permutation (`Fin.snoc_eq_cons_rotate` =
`finRotate`), under which `minAdm` is invariant (`minAdm_comp_perm`). -/
theorem minAdm_cons_eq_snoc (t : ℕ) (D : Fin (L + 1) → ℕ) :
    minAdm (Fin.cons t D) = minAdm (Fin.snoc D t) := by
  rw [Fin.snoc_eq_cons_rotate]
  exact (minAdm_comp_perm (finRotate _) (Fin.cons t D)).symm

/-- **Peel commutes with the appended tail.** `redChain r (Fin.snoc D t) = Fin.snoc (redChain r D)
t`: head-peeling the front layer at `r` leaves the appended tail `t` untouched. -/
theorem redChain_snoc (r t : ℕ) (D : Fin (L + 1 + 1 + 1) → ℕ) :
    redChain r (Fin.snoc D t) = Fin.snoc (redChain r D) t := by
  funext p
  refine Fin.cases ?_ (fun q => ?_) p
  · -- p = 0
    rw [redChain_zero]
    rw [show (0 : Fin (L + 1 + 1 + 1)) = (0 : Fin (L + 1 + 1)).castSucc from rfl,
      Fin.snoc_castSucc, redChain_zero]
  · -- p = q.succ, q : Fin (L + 1 + 1)
    rw [redChain_succ]
    refine Fin.lastCases ?_ (fun j => ?_) q
    · -- q = Fin.last (L + 1) : both sides are `t`
      rw [show ((Fin.last (L + 1)).succ.succ : Fin (L + 1 + 1 + 1 + 1))
            = Fin.last (L + 1 + 1 + 1) from Fin.ext (by simp),
          Fin.snoc_last,
          show ((Fin.last (L + 1)).succ : Fin (L + 1 + 1 + 1))
            = Fin.last (L + 1 + 1) from Fin.ext (by simp),
          Fin.snoc_last]
    · -- q = j.castSucc, j : Fin (L + 1)
      rw [show (j.castSucc.succ.succ : Fin (L + 1 + 1 + 1 + 1)) = (j.succ.succ).castSucc from
            Fin.ext (by simp [Fin.val_succ, Fin.val_castSucc]),
          Fin.snoc_castSucc,
          show (j.castSucc.succ : Fin (L + 1 + 1 + 1)) = (j.succ).castSucc from
            Fin.ext (by simp [Fin.val_succ, Fin.val_castSucc]),
          Fin.snoc_castSucc, redChain_succ]

/-- `Fin.snoc D t` reads its `0`th entry off `D`. -/
theorem snoc_apply_zero {n : ℕ} (D : Fin (n + 1) → ℕ) (t : ℕ) :
    (Fin.snoc (α := fun _ => ℕ) D t) (0 : Fin (n + 1 + 1)) = D 0 := by
  rw [show (0 : Fin (n + 1 + 1)) = Fin.castSucc (0 : Fin (n + 1)) from (Fin.castSucc_zero).symm,
    Fin.snoc_castSucc]

/-- `Fin.snoc D t` reads its `1`st entry off `D`. -/
theorem snoc_apply_one {n : ℕ} (D : Fin (n + 1 + 1) → ℕ) (t : ℕ) :
    (Fin.snoc (α := fun _ => ℕ) D t) (1 : Fin (n + 1 + 1 + 1)) = D 1 := by
  rw [show (1 : Fin (n + 1 + 1 + 1)) = Fin.castSucc (1 : Fin (n + 1 + 1)) from
    Fin.ext (by simp), Fin.snoc_castSucc]

/-! ## THE KEY LEMMA — appending a head width to the deep tail -/

/-- **THE KEY LEMMA.** `minAdm (Fin.snoc D t) ≤ t·s + CRrec D s` for a deep tail `D` (`≥ 2` widths).
Peel the front layer of the chain `(D₀, …, D_last, t)` at each rank `r`: the appended head width `t`
stays at the tail (untouched, `redChain_snoc`), so the recursion aligns with `CRrec`'s head-peel
step-for-step. The base case (`D : Fin 2`, a 3-chain) picks the pivot `min s (min D₀ D₁)` and
case-splits on `s ≤ min(D₀,D₁)`. -/
theorem minAdm_snoc_le : {L : ℕ} → (D : Fin (L + 1 + 1) → ℕ) → (t s : ℕ) →
    minAdm (Fin.snoc D t) ≤ t * s + CRrec D s
  | 0, D, t, s => by
      rw [CRrec_leaf, ← minAdmRec_eq_minAdm, minAdmRec_succ_succ]
      have hs0 := snoc_apply_zero D t
      have hs1 := snoc_apply_one D t
      simp only [hs0, hs1]
      have hcell : ∀ r, minAdmRec (redChain r (Fin.snoc D t)) = r * t := by
        intro r
        have h1 : redChain r (Fin.snoc D t) 1 = t := by
          rw [show (1 : Fin 2) = (0 : Fin 1).succ from Fin.ext (by simp), redChain_succ,
            show ((0 : Fin 1).succ.succ : Fin 3) = Fin.last 2 from Fin.ext (by simp), Fin.snoc_last]
        rw [minAdmRec_leaf, redChain_zero, h1]
      -- witness pivot `w = min s (min D₀ D₁)`.
      have hmem : min s (min (D 0) (D 1)) ∈ Finset.range (min (D 0) (D 1) + 1) :=
        Finset.mem_range.mpr (by omega)
      refine le_trans (Finset.inf'_le _ hmem) ?_
      rw [hcell]
      -- goal: (D₀ − w)(D₁ − w) + w·t ≤ t·s + (D₀ − s)(D₁ − s),  w = min s (min D₀ D₁)
      by_cases hsle : s ≤ min (D 0) (D 1)
      · rw [show min s (min (D 0) (D 1)) = s from by omega, Nat.mul_comm s t]; omega
      · rw [show min s (min (D 0) (D 1)) = min (D 0) (D 1) from by omega]
        have hprod0 : (D 0 - min (D 0) (D 1)) * (D 1 - min (D 0) (D 1)) = 0 := by
          rcases le_total (D 0) (D 1) with h | h
          · rw [show min (D 0) (D 1) = D 0 from by omega]; simp
          · rw [show min (D 0) (D 1) = D 1 from by omega]; simp
        rw [hprod0, Nat.zero_add]
        calc min (D 0) (D 1) * t ≤ s * t := Nat.mul_le_mul_right _ (by omega)
          _ = t * s := Nat.mul_comm _ _
          _ ≤ t * s + (D 0 - s) * (D 1 - s) := Nat.le_add_right _ _
  | (L + 1), D, t, s => by
      rw [CRrec_succ_succ]
      -- achiever `r` of `CRrec D s`.
      obtain ⟨r, hrmem, hreq⟩ := Finset.exists_mem_eq_inf'
        (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
        (fun r => (D 0 - r) * (D 1 - r) + CRrec (redChain r D) s)
      rw [Finset.mem_range] at hrmem
      rw [hreq, ← minAdmRec_eq_minAdm, minAdmRec_succ_succ]
      have hs0 := snoc_apply_zero D t
      have hs1 := snoc_apply_one D t
      simp only [hs0, hs1]
      have hmem : r ∈ Finset.range (min (D 0) (D 1) + 1) := Finset.mem_range.mpr (by omega)
      refine le_trans (Finset.inf'_le _ hmem) ?_
      rw [redChain_snoc, minAdmRec_eq_minAdm]
      have IH := minAdm_snoc_le (redChain r D) t s
      omega

/-! ## THE (I) THEOREM — deep-rank stratification of the QIP -/

/-- The deep tail `(M₂, …, M_last)` of a `≥ 4`-width chain `M`. Definitionally `redChain t M =
`Fin.cons t (deepTail M)`. -/
def deepTail (M : Fin (L + 1 + 1 + 1 + 1) → ℕ) : Fin (L + 1 + 1) → ℕ :=
  fun i => M i.succ.succ

/-- **THE (I) THEOREM.** `minAdm M ≤ CRrec (deepTail M) s + minAdm ![M 0, M 1, s]` — the deep-rank
stratification of the QIP (deepgate cert §6 / codex answer §2): head-peel `M` at pivot `t`; the
reduced chain `redChain t M = Fin.cons t (deepTail M)` is `≤ t·s + CRrec (deepTail M) s` (KEY, via
`minAdm_cons_eq_snoc`); the achiever `t` of the 3-chain `![M 0, M 1, s]` closes it. Holds for every
`s` (stepbuild uses `s = ρ − k`). Supplies input (I) to the deep branch `C_k ≥ minAdm(M) − ab`; the
full branch also needs (II) `minAdm(M₀,M₁,s) ≤ ab + us − γ_s` and the γ_s assembly (stepbuild). -/
theorem minAdm_le_compositeRank_add (M : Fin (L + 1 + 1 + 1 + 1) → ℕ) (s : ℕ) :
    minAdm M ≤ CRrec (deepTail M) s + minAdm ![M 0, M 1, s] := by
  -- the 3-chain `minAdm ![M₀,M₁,s]` is `gCrux M₀ M₁ s` (banked `minAdmRec_three`).
  have h3 : minAdm (![M 0, M 1, s] : Fin 3 → ℕ) = gCrux (M 0) (M 1) s := by
    rw [← minAdmRec_eq_minAdm, minAdmRec_three]
    simp
  -- achiever `t` of the 3-chain min.
  obtain ⟨t, htmem, hteq⟩ := Finset.exists_mem_eq_inf'
    (s := Finset.range (min (M 0) (M 1) + 1)) (by simp)
    (fun t => (M 0 - t) * (M 1 - t) + t * s)
  rw [Finset.mem_range] at htmem
  -- head-peel `minAdm M`, bound by the achiever cell.
  rw [← minAdmRec_eq_minAdm, minAdmRec_succ_succ]
  have hmem : t ∈ Finset.range (min (M 0) (M 1) + 1) := Finset.mem_range.mpr (by omega)
  refine le_trans (Finset.inf'_le _ hmem) ?_
  -- cell at `t`: `(M₀−t)(M₁−t) + minAdm (Fin.cons t (deepTail M))`.
  rw [show redChain t M = Fin.cons t (deepTail M) from rfl, minAdmRec_eq_minAdm,
    minAdm_cons_eq_snoc]
  have hKEY := minAdm_snoc_le (deepTail M) t s
  rw [h3, show gCrux (M 0) (M 1) s = (M 0 - t) * (M 1 - t) + t * s from hteq]
  omega

/-! ## Non-vacuity anchors (canonical `(4,4,4,4)` deep-gate case, cert §2) -/

-- `CRrec (deepTail (4,4,4,4)) 2 + minAdm (4,4,2) = 4 + 7 = 11 = minAdm (4,4,4,4)`: (I) tight here.
example : deepTail (![4, 4, 4, 4] : Fin 4 → ℕ) = ![4, 4] := by decide
example : CRrec (![4, 4] : Fin 2 → ℕ) 2 = 4 := by decide
example : minAdmRec (![4, 4, 2] : Fin 3 → ℕ) = 7 := by decide
example : minAdmRec (![4, 4, 4, 4] : Fin 4 → ℕ) = 11 := by decide

-- `CRrec (·, 0) = minAdm` fires on the `(2,2,2)` anchor.
example : CRrec (![2, 2, 2] : Fin 3 → ℕ) 0 = minAdm (![2, 2, 2] : Fin 3 → ℕ) :=
  CRrec_zero_eq_minAdm _

end DLNFibre.DLN.RLCT
