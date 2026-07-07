import DLNFibre.Core.Analysis.RLCT.Pair
import DLNFibre.Core.Analysis.RLCT.Witness
import DLNFibre.Core.Analysis.RLCT.SumSq

/-!
# `RLCT.CiteCoherence` — B5 (on-cite positivity) + the cite/cite-free coherence on the witness germ

Two corollaries validating that the **cited** zeta-pole machinery agrees with the **cite-free**
canonical value on a concrete germ. These are the only results in the R9 layer that carry the
continuation cite (`cited_local_zeta_pole`); that is correct and honest — they *are* statements
about the cited object — and they sit **off** the DLN payoff's value path (the payoff rides the two
Watanabe/Aoyagi cites on `rlctGlobal`, never this local zeta axiom).

* **B5 — `rlctAt_pos_of_zetaSetup`** (CITED): every `ZetaSetup S` has `0 < rlctAt S.K S.x₀`. One
  line from the cite's `s₀ < 0` (`largestPole_neg`) and the bundled `s₀ = −rlctAt K x₀`.
* **Coherence (i) — `rlctAt_zetaSetupSq`** (cite-free): the witness germ's canonical local RLCT is
  `1/2`, via `zetaSetupSq.K = sumSq 1` and `rlctAt_sumSq` at `C = 1`.
* **Coherence (ii) — `rlctPair_lam_zetaSetupSq`** (CITED): the *cited* pole location
  `(rlctPair zetaSetupSq).lam` equals the *cite-free* canonical value `1/2` (Link 1 + (i)) — the
  cited and cite-free readings agree on the one concrete germ, validating Link 1 non-vacuously.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set

namespace RLCT

variable {n : ℕ}

/-- **B5 — on-cite positivity (CITED): `0 < rlctAt S.K S.x₀`.** From any `ZetaSetup S`, the local
RLCT at the base point is strictly positive: the cite gives a genuine negative largest pole
(`largestPole_neg`, `s₀ < 0`) and the bundled `s₀ = −rlctAt K x₀` (`largestPole_eq_neg_rlctAt`), so
`rlctAt K x₀ = −s₀ > 0`. Carries `cited_local_zeta_pole` (it is a statement about the cited pole);
standalone corollary, off the payoff's value path. -/
theorem rlctAt_pos_of_zetaSetup (S : ZetaSetup n) : 0 < rlctAt S.K S.x₀ := by
  have hlt : largestPole S < 0 := largestPole_neg S
  have heq : largestPole S = -(rlctAt S.K S.x₀) := largestPole_eq_neg_rlctAt S
  linarith [heq ▸ hlt]

/-- The witness germ `zetaSetupSq.K` is the 1-variable sum-of-squares kernel `sumSq 1` (both are
`fun x ↦ (x 0)^2`, the `Fin 1` sum collapsing to its single term). -/
lemma zetaSetupSq_K_eq_sumSq : zetaSetupSq.K = sumSq 1 := by
  funext x
  simp [zetaSetupSq, sqGerm, sumSq]

/-- The witness germ's base point is the origin. -/
lemma zetaSetupSq_x₀_eq_zero : zetaSetupSq.x₀ = 0 := rfl

/-- **Coherence (i) — cite-free: `rlctAt zetaSetupSq.K zetaSetupSq.x₀ = 1/2`.** The canonical local
RLCT of the witness germ `K = (x 0)^2` at `0` is `1/2`: rewrite `zetaSetupSq.K = sumSq 1` and
`zetaSetupSq.x₀ = 0`, then `rlctAt_sumSq` at `C = 1` gives `1/2`. Cite-free (rides `RLCT.SumSq`). -/
theorem rlctAt_zetaSetupSq : rlctAt zetaSetupSq.K zetaSetupSq.x₀ = 1 / 2 := by
  rw [zetaSetupSq_K_eq_sumSq, zetaSetupSq_x₀_eq_zero, rlctAt_sumSq (le_refl 1)]
  norm_num

/-- **Coherence (ii) — CITED: `(rlctPair zetaSetupSq).lam = 1/2`.** The *cited* zeta-pole location
`λ` on the witness germ equals the *cite-free* canonical value `1/2`: Link 1
(`rlctPair_lam_eq_rlctAt`, `λ = rlctAt K x₀`) plus coherence (i) (`rlctAt = 1/2`). This shows the
cited pole location agrees with the cite-free canonical value on the one concrete germ — Link 1 is
validated non-vacuously. Carries `cited_local_zeta_pole` (via Link 1). -/
theorem rlctPair_lam_zetaSetupSq : (rlctPair zetaSetupSq).lam = 1 / 2 := by
  rw [rlctPair_lam_eq_rlctAt, rlctAt_zetaSetupSq]

end RLCT
