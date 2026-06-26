import DLNFibre.DLN.RLCT.Validate.RouteMAchieverTelescope
import DLNFibre.DLN.RLCT.Foundations.Loss

/-!
# `RouteMAchieverBridge` — reusable bricks for the `suffix 0 = prod M A` bridge (PARTIAL)

Toward bridging the abstract chained-product telescope (`Chain.suffix`, a right-associated fold) to the
genuine DLN layer product `prod M A` (`prodAux`, a left-associated prefix fold): the general achiever
chart consumes `Chain.chain_telescope_zero` (`C_0 · suffix_0 = u • Hmat_0`); with `C_0 = 1` this gives
`suffix_0 = u • Hmat_0`, so a `suffix_0 = prod M A` bridge would yield the chart identity `prod M A = u • H`.

**STATUS — the two reusable bricks below are BANKED sorry-free; the `prod` front-peel itself is now
LANDED in `RouteMFrontPeel` (`prod_front_peel : prod M A = A_0 · (reindex …) prod (Atail M A)`, axiom-clean
— the deferred `prodAux` reassociation XL-cast, shared with `DeepestTelescoping.endpoint_telescoping`).**
The wall the earlier tides hit (a `prodAux_succ` + `ext` entry-chase through the `Fin (M 0)` vs
`Fin (M ⟨0,_⟩)` square-ness) was dissolved by an INDUCTION-on-prefix-length proof (never `ext`): each step
combines `prodAux_succ` on parent + tail with `reindex_finCongr_mul`, all cast bookkeeping at the equiv
level (`finCongr_refl` → `reindex_refl_refl` via `erw`); the reassociation is closed by `set` + a
fully-applied `Matrix.mul_assoc` term. The REMAINING bridge work (`suffix 0 = prod M A`) is the chain↔`M`
width-embedding induction (a chain-shift matching `Chain.suffix_succ` against `prod_front_peel`); reachable
(the `L=0` base typechecks), it is owned by the achiever-chart assembly that constructs the chain.

* `reindex_finCongr_mul` — `reindex (finCongr …)` distributes over matrix products (the Codex-named
  cast-killer; reusable wherever a width-equality reindex meets a product).
* `Mtail` / `Atail` — the tail width-function / tail layers (drop the first layer), recast into
  `Params (Mtail M)`. The front-peel target's tail chain.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators
open Matrix

variable {L : ℕ}

/-! ## The tail chain and its layers -/

/-- The tail width function `Mtail M k = M (k+1)` (drop the source vertex), as a `Fin (L+1) → ℕ`
chain (one fewer layer than the `Fin (L+1+1)` parent). -/
def Mtail (M : Fin (L + 1 + 1) → ℕ) : Fin (L + 1) → ℕ := fun i => M i.succ

@[simp] theorem Mtail_apply (M : Fin (L + 1 + 1) → ℕ) (i : Fin (L + 1)) :
    Mtail M i = M i.succ := rfl

/-- The tail layers `Atail A s = A s.succ` (drop the first layer), recast into `Params (Mtail M)`. -/
def Atail (M : Fin (L + 1 + 1) → ℕ) (A : Params M) : Params (Mtail M) := fun s =>
  (by
    have e1 : Mtail M s.castSucc = M s.succ.castSucc := by
      simp only [Mtail]; congr 1
    have e2 : Mtail M s.succ = M s.succ.succ := rfl
    rw [e1, e2]; exact A s.succ :
    Matrix (Fin (Mtail M s.castSucc)) (Fin (Mtail M s.succ)) ℝ)

/-! ## The cast-killer: matrix products commute with `reindex (finCongr …)` -/

/-- **`reindex (finCongr …)` distributes over matrix products** (the Codex-named cast-killer). For
width-equalities `a=a'`, `b=b'`, `c=c'`, reindexing a product `X·Y` equals the product of the
reindexed factors. Via `Matrix.reindex_apply` + `Matrix.submatrix_mul_equiv`. -/
theorem reindex_finCongr_mul {a b c a' b' c' : ℕ}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (X : Matrix (Fin a) (Fin b) ℝ) (Y : Matrix (Fin b) (Fin c) ℝ) :
    Matrix.reindex (finCongr ha) (finCongr hc) (X * Y)
      = Matrix.reindex (finCongr ha) (finCongr hb) X
        * Matrix.reindex (finCongr hb) (finCongr hc) Y := by
  simp only [Matrix.reindex_apply]
  exact (Matrix.submatrix_mul_equiv X Y (finCongr ha).symm (finCongr hb).symm
    (finCongr hc).symm).symm

end DLNFibre.DLN.RLCT
