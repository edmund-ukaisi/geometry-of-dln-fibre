import DLNFibre.DLN.RLCT.Validate.RouteMFactoredChain
import DLNFibre.DLN.RLCT.Validate.RouteMSuffixBridge

/-!
# `RouteMChainRate` — the rate-identity engine `prod M A = u • H` (general-`M` achiever)

Combines the abstract telescope (`RouteMAchieverTelescope`), the factored-data builder
(`RouteMFactoredChain`), and the suffix↔product bridge (`RouteMSuffixBridge`) into the single
M-agnostic rate-identity engine: a `FactoredChain L u` whose `C 0 = 1` (the deepest factor is its own
compressed transition), whose ambient widths match the DLN widths (`hW`) and whose layers reindex to the
DLN layers (`hA`), satisfies

> `prod M A = u • H`,   `H := reindex (c.toChain.Hmat 0)`.

This is the chart identity's RATE factor: the per-`M` achiever construction supplies a `FactoredChain`
(its block matrices + `hC`/`hQA`/`base` + `C 0 = 1` + the matches), and gets `prod = u•H` with NO
per-entry `ring` blow-up — the telescope does the divisibility, the bridge does the product-shape match.

* `FactoredChain.prod_eq_reindex_suffix` — the bridge restated: `prod M A = reindex (suffix 0)`
  (the per-`M` construction simplifies `suffix 0` via its own `C 0 = 1` + `telescope_zero`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

namespace FactoredChain

variable {L : ℕ} {u : ℝ}

/-- **The rate-identity bridge** (`prod M A = reindex (suffix 0)`). The suffix bridge
(`Chain.suffix_zero_reindex_eq_prod`) on the produced chain: with the width match `hW` and the layer
match `hA`, the chain's full suffix product reindexes to the DLN layer product `prod M A`. The per-`M`
construction then simplifies `suffix 0` (via its own `C 0 = 1` fed into `telescope_zero`, which yields
`suffix 0 = u • Hmat 0` once `Twid 0 = Wwid 0`), turning this into `prod M A = u • H`. -/
theorem prod_eq_reindex_suffix (c : FactoredChain L u)
    (M : Fin (L + 1) → ℕ) (A : Params M)
    (hW : ∀ k (hk : k ≤ L), c.toChain.Wwid k = M ⟨k, Nat.lt_succ_of_le hk⟩)
    (hA : ∀ k (hk : k < L),
      Matrix.reindex (finCongr (hW k (le_of_lt hk))) (finCongr (hW (k + 1) hk))
          (c.toChain.A k)
        = (A ⟨k, hk⟩ :
            Matrix (Fin (M (⟨k, Nat.lt_succ_of_le (le_of_lt hk)⟩ : Fin (L + 1))))
              (Fin (M (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (L + 1)))) ℝ)) :
    prod M A
      = Matrix.reindex (finCongr (hW 0 (Nat.zero_le L))) (finCongr (hW L (le_refl L)))
          (c.toChain.suffix 0 (Nat.zero_le L)) :=
  (Chain.suffix_zero_reindex_eq_prod c.toChain M A hW hA).symm

end FactoredChain

end DLNFibre.DLN.RLCT
