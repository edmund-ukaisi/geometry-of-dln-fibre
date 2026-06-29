import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatStruct

/-!
# `RouteMActiveSlots` — the structured residual active-slot embedding (∀M-L2 brick 3 foundation)

The structured residual `active M` for the ∀M interior-det headline is the set of flat coordinates
the radial `u = x p₀` scales: per interior boundary `k`, the `r_k × c_k` E-block (the Schur frame's
`u·E` carrier), plus the leaf residual `rfin` reads. This module banks the E-BLOCK slot embedding
`activeSlotE` (reusing the decoder's `readE` index map: `frameSplitEquiv.symm`'s `E`-summand pulled
through `chartIdxEquiv.symm`) and its injectivity in the matrix index `(i, j)` — the hardest
dependent-`Fin` piece of the structured-active construction (Codex's flagged E-block embedding).

`activeSlotE M t ha k` enumerates the E-block flat slots at boundary `k`; injective in `(i, j)` by
composition of the injective `chartIdxEquiv.symm` / `frameSplitEquiv.symm` / `finProdFinEquiv`. The
full `active M` (the union over boundaries + the leaf slots, `card = minAdm` tied to
`readerComplement_card_add_minAdm`) is assembled on this; the leaf slots are chosen from the
reader-complement (the (2,2,2) `lf0/lf1` pattern, lifted via brick 1).

* `activeSlotE` — the E-block flat slot at boundary `k`, matrix index `(i, j)` (`= readE`'s slot).
* `activeSlotE_inj` — `activeSlotE … i j = activeSlotE … i' j' → i = i' ∧ j = j'` (injectivity).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-- **The E-block active-slot embedding** at interior boundary `k` — the flat coordinate carrying
the Schur-frame `u·E` entry `(i, j)` (`r_k × c_k`). Reuses the decoder's `readE` index map: place
`(i, j)` in the `E`-summand (`Sum.inr`) of `frameSplitEquiv`, pull back to the `schurDim k` slot,
then `chartIdxEquiv.symm ⟨k, Sum.inl ·⟩`. These slots are the additively-`u`-scaled residual. -/
noncomputable def activeSlotE (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    (i : Fin (Text M t (k.val + 1) - Text M t (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) : Fin (routeMAmbient M) :=
  (chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm
    ⟨k, Sum.inl ((frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val)).symm
      (Sum.inr (finProdFinEquiv (i, j))))⟩

/-- **`activeSlotE` is injective in the matrix index `(i, j)`** (at fixed boundary `k`): distinct
E-block entries occupy distinct flat slots. Composition of the injective `chartIdxEquiv.symm`,
`frameSplitEquiv.symm`, `finProdFinEquiv` — the disjointness the `u`-scaled active set needs. -/
theorem activeSlotE_inj (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    {i i' : Fin (Text M t (k.val + 1) - Text M t (k.val + 2))}
    {j j' : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))}
    (h : activeSlotE M t ha k i j = activeSlotE M t ha k i' j') : i = i' ∧ j = j' := by
  unfold activeSlotE at h
  have h2 := (chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm.injective h
  rw [Sigma.mk.inj_iff] at h2
  have h3 := h2.2
  simp only [heq_eq_eq, Sum.inl.injEq] at h3
  have h4 := (frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt)
    (ha.hub k.val)).symm.injective h3
  rw [Sum.inr.injEq] at h4
  have h5 := finProdFinEquiv.injective h4
  rw [Prod.mk.injEq] at h5
  exact h5

end DLNFibre.DLN.RLCT
