/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.DLN.RLCT.Foundations.Loss
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepPivot

set_option linter.style.longLine false

/-!
# `RouteMSJDeepChainPeel` — the concrete↔abstract chain-descent bridge (deep atlas, Tide B)

**Thread `genm-deepatlas`, aoyagi-full Stage 2 (branch β, NATIVE).** The single, clean,
**loss-independent** rank/geometry bridge connecting the concrete DLN chain `prodAux`/`prod`
(`Foundations.Loss`) to the abstract **effective-state** recursion on which the atlas coverage and
gluing are stated. Per the controller's framing (2026-07-15): keep this link a PURE rank lemma in
Tide B — it must NOT bleed into the measure/loss step (the capstone integrand is concrete `prodAux`,
so the "opaque-width cast grind" is *located* here, not deferred).

## The effective state

At recursion level `k`, the state is a right factor `Q` and its represented product `prodAux k · Q`.
Peeling the last layer (`prodAux_succ`) and applying the general-pivot rank reduction
(`generalPivot_reduce_rank`, the tide-B bridge) descends the state from level `k+1` to level `k`:

    rank(prodAux (k+1) · Q)  =  rank(prodAux k · Q'),   Q' = (effLayer·Q)[:,κ] · ((effLayer·Q)[ρ,κ])⁻¹,

the composite-rank recursion realised on the actual chain. The effective last layer at this level is
`effLayer · Q` where `effLayer` is the `k`-th DLN layer reindexed into the running-width type (exactly
the block `prodAux_succ` exposes). This is loss-independent: only ranks and the layer product appear.

## What lands here (sorry-free)

* **`effLayer`** — the `k`-th layer reindexed to the running widths (the block `prodAux_succ` peels).
* **`prodAux_succ_mul`** — `prodAux (k+1) · Q = prodAux k · (effLayer · Q)` (the matrix-level peel of
  the last layer under a right factor; `prodAux_succ` + `mul_assoc`).
* **`prodAux_reduce_rank`** — the chain-descent rank identity: `rank(prodAux (k+1) · Q)` equals the
  composed rank through the reduced level-`k` factor, for any pivot `(ρ, κ)` of `effLayer · Q`.

Standalone (NOT aggregator-wired). Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix

namespace DeepAtlas

variable {L : ℕ}

/-- The `k`-th DLN layer reindexed into the running-width type `Fin (H⟨k⟩) × Fin (H⟨k+1⟩)` — exactly
the block `prodAux_succ` exposes when peeling the last layer of `prodAux (k+1)`. -/
noncomputable def effLayer (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1) :
    Matrix (Fin (H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))))
      (Fin (H (⟨k + 1, hk⟩ : Fin (L + 1)))) ℝ :=
  Matrix.reindex
    (finCongr (rfl : H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))
        = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc)).symm)
    (finCongr (rfl : H (⟨k + 1, hk⟩ : Fin (L + 1))
        = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ)).symm)
    (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

/-- **The last-layer peel under a right factor.** `prodAux (k+1) · Q = prodAux k · (effLayer · Q)` —
the running product with a right factor `Q` peels its last layer into the head `prodAux k` times the
effective last layer `effLayer · Q`. Pure matrix algebra (`prodAux_succ` + `mul_assoc`); the
concrete↔abstract link that keeps the cast grind out of the measure step. -/
theorem prodAux_succ_mul (H : Fin (L + 1) → ℕ) (A : Params H) (k q : ℕ) (hk : k + 1 < L + 1)
    (Q : Matrix (Fin (H (⟨k + 1, hk⟩ : Fin (L + 1)))) (Fin q) ℝ) :
    prodAux H A (k + 1) hk * Q
      = prodAux H A k (Nat.lt_of_succ_lt hk) * (effLayer H A k hk * Q) := by
  rw [prodAux_succ H A k hk rfl rfl]
  exact Matrix.mul_assoc _ _ _

/-- **The chain-descent rank identity (composite-rank recursion on the actual chain).** For a size-`r`
pivot `(ρ, κ)` (`r = (effLayer·Q).rank`) of the effective last layer `effLayer · Q`, the composed rank
through level `k+1` equals the composed rank through the reduced level-`k` factor
`(effLayer·Q)[:,κ] · ((effLayer·Q)[ρ,κ])⁻¹`:

    rank(prodAux (k+1) · Q) = rank(prodAux k · (effLayer·Q)[:,κ] · ((effLayer·Q)[ρ,κ])⁻¹).

The state descends `(k+1, q) → (k, r)`. Composes the peel `prodAux_succ_mul` with the general-pivot
rank reduction `generalPivot_reduce_rank`. Loss-independent. -/
theorem prodAux_reduce_rank (H : Fin (L + 1) → ℕ) (A : Params H) (k q : ℕ) (hk : k + 1 < L + 1)
    (Q : Matrix (Fin (H (⟨k + 1, hk⟩ : Fin (L + 1)))) (Fin q) ℝ)
    (ρ : Fin (effLayer H A k hk * Q).rank ↪ Fin (H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))))
    (κ : Fin (effLayer H A k hk * Q).rank ↪ Fin q)
    (hU : IsUnit ((effLayer H A k hk * Q).submatrix ρ κ)) :
    (prodAux H A (k + 1) hk * Q).rank
      = (prodAux H A k (Nat.lt_of_succ_lt hk) * (effLayer H A k hk * Q).submatrix id κ
          * ((effLayer H A k hk * Q).submatrix ρ κ)⁻¹).rank := by
  rw [prodAux_succ_mul H A k q hk Q]
  exact generalPivot_reduce_rank _ (effLayer H A k hk * Q) ρ κ hU

/-- Non-vacuity: the chain descent applies at level `k` of any chain with `k+2 ≤ L+1`, for any
right factor `Q` and any unit pivot of the effective last layer. -/
example (H : Fin (L + 1) → ℕ) (A : Params H) (k q : ℕ) (hk : k + 1 < L + 1)
    (Q : Matrix (Fin (H (⟨k + 1, hk⟩ : Fin (L + 1)))) (Fin q) ℝ)
    (ρ : Fin (effLayer H A k hk * Q).rank ↪ Fin (H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))))
    (κ : Fin (effLayer H A k hk * Q).rank ↪ Fin q)
    (hU : IsUnit ((effLayer H A k hk * Q).submatrix ρ κ)) : True := by
  have _h := prodAux_reduce_rank H A k q hk Q ρ κ hU
  trivial

end DeepAtlas

end DLNFibre.DLN.RLCT
