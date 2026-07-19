import DLNFibre.DLN.RLCT.Engine.GeoAlphaGauge

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoInvVal` — the value invariant `Inv_val` (loss-t15, PHASE 3b)

The prod-diagonalization crux `leafDiagFrob_geoAtlasNorm` closes via Aoyagi's value invariant
`Inv_val(acc, s): prod M (acc w) = diag(b(s))·[[E_J,O],[O,D_J]]` (pnp-fold §7 / `cert-loss-
factorization`). §7 verdict: TWO certs, ONE skeleton — `Inv_val` reuses t14's det-walk skeleton
(tree walk, per-`stepUpdate`-case dispatch, `conRoot` base, `DivBirthInv` threading, the
`geoChartMap_flat_*` reads) with the VALUE payload (residual block `D_J`, the power-1 squarefree
`b`-chain, the α gauge that the det-1-blind Jacobian never sees).

This file builds the **t14-INDEPENDENT consumer side** (team-lead GO, gate 175a86025): the
`frobSq`-of-diagonal lemma and the leaf-discharge bridge `LeafProdDiag → LeafDiagFrob`. When t14's
det-walk lands, the loss lane owes only the four maintenance proofs + the walk instantiation
(mirroring t14's step-case plumbing) — that supplies `LeafProdDiag` at each leaf, and this bridge
finishes to `LeafDiagFrob` (hence `LeafPullback`, via the PROVEN `leafPullback_of_diagFrob`).

The `Inv_val` statement + the four maintenance signatures (DivBirthInv threaded per rider 1, the
`partialDiag` block interface pinned abstractly per rider 2) live in
`design-inv-val-statement-t15.md` and land here once t14's walk fixes the shared plumbing.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **`frobSq` of a rectangular diagonal matrix** (standalone, t14-independent): if `A` vanishes off
the value-diagonal (`A i j = d i` when `(i:ℕ) = (j:ℕ)`, else `0`), then `frobSq A = Σᵢ (dᵢ counted
only where the column exists)²`. Aoyagi's leaf `prod = diag(b)` has `frobSq = Σ bᵢ²` — this is that
read. -/
theorem frobSq_of_diagonal {p q : ℕ} (A : Fin p → Fin q → ℝ) (d : Fin p → ℝ)
    (hA : ∀ i j, A i j = if (i : ℕ) = (j : ℕ) then d i else 0) :
    frobSq A = ∑ i : Fin p, (if (i : ℕ) < q then d i else 0) ^ 2 := by
  unfold frobSq
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hA]
  by_cases hiq : (i : ℕ) < q
  · rw [Finset.sum_eq_single (⟨(i : ℕ), hiq⟩ : Fin q), if_pos hiq]
    · simp
    · intro j _ hj
      have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hiq]
    refine (Finset.sum_eq_zero fun j _ => ?_).trans (by simp)
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hiq (h ▸ j.isLt)
    simp [hne]

/-- **The leaf-discharge bridge** (t14-independent): from Aoyagi's leaf `prod = diagonal(dvec)` (the
value invariant's leaf case) to `LeafDiagFrob`. `dvec` is the `b`-chain read off the fully-cleared
diagonal; `hd` factors each counted diagonal entry as `(∏_k z_{divCoord k}) · ρ` (terminal-product ×
divisibility ratio, `cert-loss-factorization` (a)). Then `frobSq_of_diagonal` + the ratio properties
give `LeafDiagFrob` (hence `LeafPullback` via the PROVEN `leafPullback_of_diagFrob`). When t14's
walk lands, `Inv_val`'s leaf case supplies `hdiag`/`hd`/`hone`/`hbd` (`dvec`/`ρ` from
`bExp`/`bChain`); this bridge is the whole consumer side, pre-built. -/
theorem leafDiagFrob_of_prodDiag (l : LeafData M)
    (dvec ρ : Params M → Fin (M 0) → ℝ) (hi : ℝ)
    (hdiag : ∀ w ∈ l.srcBox, ∀ i j,
      prod M (l.chartMap w) i j = if (i : ℕ) = (j : ℕ) then dvec w i else 0)
    (hd : ∀ w ∈ l.srcBox, ∀ i : Fin (M 0),
      (if (i : ℕ) < M (Fin.last L) then dvec w i else 0)
        = (∏ k : Fin l.numDiv, paramsEquivFlat M w (l.divCoord k)) * ρ w i)
    (hone : ∀ w ∈ l.srcBox, ∃ i : Fin (M 0), ρ w i = 1)
    (hbd : ∀ w ∈ l.srcBox, ∑ i : Fin (M 0), (ρ w i) ^ 2 ≤ hi) :
    LeafDiagFrob l := by
  refine ⟨M 0, ρ, hi, fun w hw => ?_, hone, hbd⟩
  rw [frobSq_of_diagonal (prod M (l.chartMap w)) (dvec w) (hdiag w hw)]
  exact Finset.sum_congr rfl fun i _ => by rw [hd w hw i]

end DLNFibre.DLN.RLCT.Engine
