import DLNFibre.DLN.RLCT.Validate.RouteMChainFactor

/-!
# `RouteMChainBlockValid` — non-vacuity of the sum-block chaining crux (`chain_block`)

The `chain_block` engine lemma (`[I | N]·[C − N·W ; W] = C`) is the load-bearing block-algebra step in
the per-`M` achiever chain's `hQA` (the cert's unit-triangular `B/C`-chaining). This module exercises it
with GENUINE nonzero `N`, `W` (a `2 → 1`-block split, the `(3,3,3,3)`-shape `r_s = 1` boundary), so the
crux is confirmed to fire non-vacuously — not only on the `N = 0` rank-stay degenerate case.

The witness: `t = Fin 2` (kept), `c = Fin 1` (residual), `m' = Fin 2`; `N : 2×1`, `W : 1×2`, `C : 2×2`
arbitrary. `chain_block` gives `[I₂ | N]·[C − N·W ; W] = C` directly (no per-entry `ring` at the call
site — the engine lemma absorbs the block multiply). -/

namespace DLNFibre.DLN.RLCT

open Matrix

/-- **`chain_block` fires with genuine nonzero blocks** (`t = Fin 2`, `c = Fin 1`, `m' = Fin 2`). For
arbitrary `N : 2×1`, `W : 1×2`, `C : 2×2`, the chaining row `[I₂ | N]` times the lift column
`[C − N·W ; W]` returns `C`. Confirms the sum-block crux is non-vacuous on a genuine `r_s = 1` boundary
(the `(3,3,3,3)` block shape), not just the `N = 0` rank-stay case. -/
theorem chain_block_witness
    (N : Matrix (Fin 2) (Fin 1) ℝ) (W : Matrix (Fin 1) (Fin 2) ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ) :
    (Matrix.of (fun (i : Fin 2) (j : Fin 2 ⊕ Fin 1) =>
        Sum.elim ((1 : Matrix (Fin 2) (Fin 2) ℝ) i) (N i) j))
        * (Matrix.of (fun (i : Fin 2 ⊕ Fin 1) (j : Fin 2) => Sum.elim (C - N * W) W i j))
      = C :=
  chain_block N W C

end DLNFibre.DLN.RLCT
