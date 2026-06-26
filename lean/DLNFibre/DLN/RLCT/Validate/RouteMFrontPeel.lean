import DLNFibre.DLN.RLCT.Validate.DeepestTelescoping
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverBridge

/-!
# `RouteMFrontPeel` — the `prod` front-peel (the deferred `prodAux` reassociation XL-cast)

Peeling the FIRST layer off the DLN layer-product:
`prod M A = A 0 · (reindex …) (prod (Mtail M) (Atail M A))` for `M : Fin (L+1+1) → ℕ`, `A : Params M`.

`prodAux`/`prod` are LEFT-associated prefix folds (peel the LAST layer natively, `prodAux_succ`); the
front-peel exposes the LEFTMOST factor, which is a reassociation. This was DEFERRED TWICE — once by
`DeepestTelescoping.endpoint_telescoping`, once by the last R1-lower tide — as the `prodAux` reassociation
XL-cast. It is the lemma needed for:
- R1-lower's `suffix 0 = prod M A` bridge (the abstract telescope `Chain.suffix` recurses by FRONT-peel,
  `suffix_succ : suffix s = A_s · suffix (s+1)`, so the bridge consumes exactly this), and
- L2/D1's `DeepestTelescoping.endpoint_telescoping` (the deferred XL-cast).

**The technique** (the reusable kernel; what the prior tides lacked): induction on the prefix length `k`,
NEVER an entrywise `ext`. Each step combines `prodAux_succ` on the parent and the tail with
`reindex_finCongr_mul` (reindex distributes over products) to push `A 0` leftward past the associativity;
the cast bookkeeping is done at the EQUIV level (`finCongr_refl` collapses each `finCongr (rfl-true)` to
`Equiv.refl`, then `Matrix.reindex_refl_refl` via `erw` collapses `reindex refl refl` to the identity).
The reassociation `(A 0 · X) · Y = A 0 · (X · Y)` — which `rw [Matrix.mul_assoc]` cannot match through the
dependent-dimension `HMul` — is closed by `set`-ting `X, Y` then a `trans` + fully-applied
`Matrix.mul_assoc A0 X Y` term (no `rw` occurrence search).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators
open Matrix

variable {L : ℕ}

/-- **Generic 3-matrix reassociation** `a · b · c = a · (b · c)` over `Type*` Fintypes. Stated
generically so a fully-applied term dodges the dependent-dimension explicit-arg matching that defeats
`rw [Matrix.mul_assoc]` (the `mul_four_reassoc` precedent in `DeepestTelescoping`). -/
theorem mul_three_reassoc {p q r s : Type*} [Fintype p] [Fintype q] [Fintype r]
    (a : Matrix p q ℝ) (b : Matrix q r ℝ) (c : Matrix r s ℝ) :
    a * b * c = a * (b * c) := Matrix.mul_assoc a b c

/-- **The tail-layer rewrite** `(Atail M A) s = reindex (finCongr …) (finCongr …) (A s.succ)`. The
`Atail` def's `Eq.mpr` cast (transporting `A s.succ` across the `rfl`-true width equalities
`Mtail M s.castSucc = M s.succ.castSucc`, `Mtail M s.succ = M s.succ.succ`) is exactly a `finCongr`
reindex; collapsing those `finCongr` to `Equiv.refl` (the widths are `rfl`-equal) then
`reindex_refl_refl` reduces both sides to `A s.succ`. The clean handle the front-peel step needs to
identify the parent layer `A ⟨k+1,_⟩` with the tail layer `(Atail M A) ⟨k,_⟩`. -/
theorem Atail_apply (M : Fin (L + 1 + 1) → ℕ) (A : Params M) (s : Fin L)
    (eA : M ((s.succ : Fin (L + 1)).castSucc) = Mtail M (s.castSucc))
    (eB : M ((s.succ : Fin (L + 1)).succ) = Mtail M (s.succ)) :
    (Atail M A) s = Matrix.reindex (finCongr eA) (finCongr eB) (A s.succ) := by
  rw [show (finCongr eA) = Equiv.refl _ from finCongr_refl _,
      show (finCongr eB) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl]
  unfold Atail
  rfl

/-- **The `prodAux` front-peel** (the deferred XL-cast, generalized over the prefix length `k`). The
prefix product through the first `k+1` parent layers peels its leftmost factor `A 0`:
`prodAux M A (k+1) = A 0 · (reindex …) (prodAux (Mtail M) (Atail M A) k)`. The column cast `ecol`
(at running width `M ⟨k+1,_⟩ = Mtail M ⟨k,_⟩`) and the fixed middle cast `emid` (`M 1 = Mtail M 0`)
are supplied as `rfl`-true hypotheses. Proven by induction on `k`: `prodAux_succ` (parent + tail) +
`reindex_finCongr_mul` + `Atail_apply`, all cast bookkeeping at the equiv level. -/
theorem prodAux_front_peel (M : Fin (L + 1 + 1) → ℕ) (A : Params M)
    (emid : Mtail M (0 : Fin (L + 1)) = M ((0 : Fin (L + 1)).succ)) :
    ∀ (k : ℕ) (hk : k + 1 < L + 1 + 1)
      (ecol : Mtail M (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin (L + 1)) = M (⟨k + 1, hk⟩ : Fin (L + 1 + 1))),
    prodAux M A (k + 1) hk
      = (A 0) * (Matrix.reindex (finCongr emid) (finCongr ecol)
          (prodAux (Mtail M) (Atail M A) k (Nat.lt_of_succ_lt_succ hk))) := by
  intro k
  induction k with
  | zero =>
      intro hk ecol
      have e1 : M (⟨0, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1 + 1))
          = M ((⟨0, Nat.lt_of_succ_lt_succ hk⟩ : Fin (L + 1)).castSucc) := rfl
      have e2 : M (⟨0 + 1, hk⟩ : Fin (L + 1 + 1))
          = M ((⟨0, Nat.lt_of_succ_lt_succ hk⟩ : Fin (L + 1)).succ) := rfl
      rw [prodAux_succ M A 0 hk e1 e2]
      rw [show (finCongr e1.symm) = Equiv.refl _ from finCongr_refl _,
          show (finCongr e2.symm) = Equiv.refl _ from finCongr_refl _,
          show (finCongr emid) = Equiv.refl _ from finCongr_refl _,
          show (finCongr ecol) = Equiv.refl _ from finCongr_refl _]
      erw [Matrix.reindex_refl_refl, Matrix.reindex_refl_refl]
      erw [Matrix.one_mul, Matrix.mul_one]
      rfl
  | succ k ih =>
      intro hk ecol
      -- parent last-peel at index (k+1).
      have eP1 : M (⟨k + 1, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1 + 1))
          = M ((⟨k + 1, Nat.lt_of_succ_lt_succ hk⟩ : Fin (L + 1)).castSucc) := rfl
      have eP2 : M (⟨k + 1 + 1, hk⟩ : Fin (L + 1 + 1))
          = M ((⟨k + 1, Nat.lt_of_succ_lt_succ hk⟩ : Fin (L + 1)).succ) := rfl
      rw [prodAux_succ M A (k + 1) hk eP1 eP2]
      -- apply the IH to the prefix factor (its column cast at index k).
      have ecolk : Mtail M (⟨k, by omega⟩ : Fin (L + 1)) = M (⟨k + 1, by omega⟩ : Fin (L + 1 + 1)) := rfl
      rw [ih (Nat.lt_of_succ_lt hk) ecolk]
      -- tail last-peel at index k (chain `Mtail M` / `Atail M A`, length `L+1`).
      have hktail : k + 1 < L + 1 := by omega
      have eT1 : Mtail M (⟨k, Nat.lt_of_succ_lt hktail⟩ : Fin (L + 1))
          = Mtail M ((⟨k, Nat.lt_of_succ_lt_succ hktail⟩ : Fin L).castSucc) := rfl
      have eT2 : Mtail M (⟨k + 1, hktail⟩ : Fin (L + 1))
          = Mtail M ((⟨k, Nat.lt_of_succ_lt_succ hktail⟩ : Fin L).succ) := rfl
      rw [prodAux_succ (Mtail M) (Atail M A) k hktail eT1 eT2]
      -- distribute the outer reindex over the tail product (middle interface `hb`).
      have hb : Mtail M (⟨k, by omega⟩ : Fin (L + 1)) = M (⟨k + 1, by omega⟩ : Fin (L + 1 + 1)) := rfl
      rw [reindex_finCongr_mul emid hb ecol (prodAux (Mtail M) (Atail M A) k (by omega))
        (Matrix.reindex (finCongr eT1.symm) (finCongr eT2.symm) (Atail M A ⟨k, by omega⟩))]
      -- reassociate `(A0 · X) · Y → A0 · (X · Y)` via `set` + fully-applied `Matrix.mul_assoc`.
      set X := Matrix.reindex (finCongr emid) (finCongr ecolk)
        (prodAux (Mtail M) (Atail M A) k (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt hk))) with hXdef
      set Y := Matrix.reindex (finCongr eP1.symm) (finCongr eP2.symm)
        (A (⟨k + 1, Nat.lt_of_succ_lt_succ hk⟩ : Fin (L + 1))) with hYdef
      -- the layer identification `Y = Z` (parent layer = tail layer, both reindexed).
      have hYZ : Y = (Matrix.reindex (finCongr hb) (finCongr ecol)
          (Matrix.reindex (finCongr eT1.symm) (finCongr eT2.symm)
            (Atail M A (⟨k, by omega⟩ : Fin L)))) := by
        rw [hYdef]
        have eA : M (((⟨k, by omega⟩ : Fin L).succ : Fin (L + 1)).castSucc)
            = Mtail M ((⟨k, by omega⟩ : Fin L).castSucc) := rfl
        have eB : M (((⟨k, by omega⟩ : Fin L).succ : Fin (L + 1)).succ)
            = Mtail M ((⟨k, by omega⟩ : Fin L).succ) := rfl
        rw [Atail_apply M A (⟨k, by omega⟩ : Fin L) eA eB]
        rw [show (finCongr eP1.symm) = Equiv.refl _ from finCongr_refl _,
            show (finCongr eP2.symm) = Equiv.refl _ from finCongr_refl _,
            show (finCongr hb) = Equiv.refl _ from finCongr_refl _,
            show (finCongr ecol) = Equiv.refl _ from finCongr_refl _,
            show (finCongr eT1.symm) = Equiv.refl _ from finCongr_refl _,
            show (finCongr eT2.symm) = Equiv.refl _ from finCongr_refl _,
            show (finCongr eA) = Equiv.refl _ from finCongr_refl _,
            show (finCongr eB) = Equiv.refl _ from finCongr_refl _]
        repeat erw [Matrix.reindex_refl_refl]
      rw [hYZ]
      exact Matrix.mul_assoc (A 0) X _

/-- **The `prod` front-peel** (the `k = L` specialization). The full DLN layer-product peels its
leftmost layer: `prod M A = A 0 · (reindex …) (prod (Mtail M) (Atail M A))`. The endpoint column cast
`ecol` is `Mtail M (last L) = M (last (L+1))` (both `= M (last)`). -/
theorem prod_front_peel (M : Fin (L + 1 + 1) → ℕ) (A : Params M)
    (emid : Mtail M (0 : Fin (L + 1)) = M ((0 : Fin (L + 1)).succ))
    (ecol : Mtail M (Fin.last L) = M (Fin.last (L + 1))) :
    prod M A = (A 0) * (Matrix.reindex (finCongr emid) (finCongr ecol)
        (prod (Mtail M) (Atail M A))) := by
  have hk : L + 1 < L + 1 + 1 := Nat.lt_succ_self _
  have ecol' : Mtail M (⟨L, Nat.lt_of_succ_lt_succ hk⟩ : Fin (L + 1))
      = M (⟨L + 1, hk⟩ : Fin (L + 1 + 1)) := rfl
  show prodAux M A (L + 1) (Nat.lt_succ_self (L + 1)) = _
  rw [prodAux_front_peel M A emid L hk ecol']
  congr 1

end DLNFibre.DLN.RLCT
