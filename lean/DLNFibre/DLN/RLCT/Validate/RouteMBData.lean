import DLNFibre.DLN.RLCT.Validate.RouteMBInterface

/-!
# `RouteMBData` — the radial-scaling core of the B-interface map identity (the `hmap` algebra)

The genuinely-reachable, network-free core of `BData.hmap` (`phiFlatLiveR1 = B ∘ pivotBlowupOn`):
the radial scalar `u` of the achiever chart `phiGen u M t B hle` can be ABSORBED into the block
data, because `phiGen` reads `u` and `B` ONLY through `Cgen u M t B hle = Bmat·chainQ(N) + u•Rmat`
(interior) / `u•Rfin` (leaf) — the `u` multiplies ONLY the residual blocks `Rmat`/`Rfin`. So scaling
those two fields by `u` (keeping `Bmat`/`Nblk`/`Wblk`) and setting the radial to `1` reproduces the
SAME chart:

  `phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u B) hle`.

This is the cast-LIGHT algebraic identity (pure `GenBlk`/`Cgen`/`Agen` matrix algebra, NO
`chartIdxEquiv` slot surgery). It is the lever Codex's gate verdict (`codex/bdata-gate-answer.md`,
V-CONSTRUCTIBLE-HARD) flagged: define the boundary factor with the radial set to `1` reading the
already-scaled residual coordinates; the radial degree comes entirely from `pivotBlowupOn`, not from
`B`.

It does NOT route through the Codex-REFUTED `composeFold fs = φ` disjoint-factor fold (genm-mapeq
@d7e75c8d): the radial is factored out as the genuine `pivotBlowupOn` map, and `B` here is the
radial-`1` chart itself — an arbitrary map, NOT a disjoint fold (so the chain-coupling unsoundness
that killed F1 does not apply; see `codex/bdata-gate-answer.md` Q2).

* `smulRmatRfin` — scale a `GenBlk`'s residual blocks `Rmat`/`Rfin` by a scalar (the
  radial-absorbing reblocking), keeping `Bmat`/`Nblk`/`Wblk`.
* `Cgen_smulRmatRfin` — `Cgen 1 (smulRmatRfin u B) = Cgen u B` (the per-boundary residual identity).
* `Agen_smulRmatRfin` / `chartParamsGen_smulRmatRfin` — the layer / chart-parameter consequences.
* `phiGen_smul_radial` — `phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u B) hle` (chart id).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {L : ℕ}
variable {𝕜 : Type} [CommRing 𝕜]

/-- **The radial-absorbing reblocking.** Scale a `GenBlk`'s residual blocks `Rmat`/`Rfin` by `u`,
keeping the kept/residual/lift blocks `Bmat`/`Nblk`/`Wblk` unchanged. Then
`Cgen 1 (smulRmatRfin u B) = Cgen u B`: the radial `u` is absorbed into the residual coordinates. -/
noncomputable def smulRmatRfin (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜) :
    GenBlk M t 𝕜 where
  Bmat := B.Bmat
  Nblk := B.Nblk
  Wblk := B.Wblk
  Rmat := fun k => u • B.Rmat k
  Rfin := fun k => u • B.Rfin k

/-- **The per-boundary residual identity** `Cgen 1 (smulRmatRfin u B) = Cgen u B` (every `k`).
Interior: `Bmat·chainQ(N) + 1•(u•Rmat) = Bmat·chainQ(N) + u•Rmat`; leaf: `1•(u•Rfin) = u•Rfin`. The
`Bmat`/`Nblk` blocks are shared (`smulRmatRfin` keeps them), so the `chainQ` part is untouched. -/
theorem Cgen_smulRmatRfin (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) (k : ℕ) :
    Cgen 1 M t (smulRmatRfin u M t B) hle k = Cgen u M t B hle k := by
  unfold Cgen smulRmatRfin
  by_cases hk : k < L
  · rw [dif_pos hk, dif_pos hk, one_smul]
  · rw [dif_neg hk, dif_neg hk, one_smul]

/-- **The per-layer identity** `Agen 1 (smulRmatRfin u B) = Agen u B` (every `k`). `Agen u B k =
chainA(N_k, W_k, Cgen u B (k+1))`; the `N_k`/`W_k` blocks are shared (`smulRmatRfin` keeps
`Nblk`/`Wblk`) and the accumulator `Cgen (k+1)` is matched by `Cgen_smulRmatRfin`. -/
theorem Agen_smulRmatRfin (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) (k : ℕ) :
    Agen 1 M t (smulRmatRfin u M t B) hle k = Agen u M t B hle k := by
  unfold Agen
  by_cases hk : k < L
  · rw [dif_pos hk, dif_pos hk]
    show chainA _ ((smulRmatRfin u M t B).Nblk k) ((smulRmatRfin u M t B).Wblk k) _ = _
    rw [Cgen_smulRmatRfin u M t B hle (k + 1)]
    rfl
  · rw [dif_neg hk, dif_neg hk]

/-- **The chart-parameter identity** `chartParamsGen 1 (smulRmatRfin u B) = chartParamsGen u B`.
`chartParamsGen` is the width-reindex of the chain layer `chainOfMt.toChain.A = Agen`, matched
boundary-wise by `Agen_smulRmatRfin`. -/
theorem chartParamsGen_smulRmatRfin (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    chartParamsGen 1 M t (smulRmatRfin u M t B) hle = chartParamsGen u M t B hle := by
  funext s
  unfold chartParamsGen
  congr 1
  exact Agen_smulRmatRfin u M t B hle s.val

/-- **The radial-scaling chart identity** `phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u B)`.
The radial scalar `u` of the achiever chart is absorbed into the residual blocks: `phiGen` reads `u`
only through `Cgen`, which `smulRmatRfin` reproduces at radial `1`. The load-bearing algebra of the
B-interface map identity (the radial degree then comes from `pivotBlowupOn`, not from `B`). -/
theorem phiGen_smul_radial (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u M t B) hle := by
  unfold phiGen
  rw [chartParamsGen_smulRmatRfin u M t B hle]

/-- **Non-vacuity**: at radial `u = 1` the reblocking is invisible (`smulRmatRfin 1 B` has the same
`Cgen` as `B`), so `phiGen 1 B = phiGen 1 (smulRmatRfin 1 B)` — the identity is consistent, and at a
genuine radial it relocates the scalar into the residual blocks. -/
example (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    phiGen 1 M t B hle = phiGen 1 M t (smulRmatRfin 1 M t B) hle :=
  phiGen_smul_radial 1 M t B hle

end DLNFibre.DLN.RLCT
