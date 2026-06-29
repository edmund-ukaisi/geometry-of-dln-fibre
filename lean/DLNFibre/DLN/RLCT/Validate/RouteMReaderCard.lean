import DLNFibre.DLN.RLCT.Validate.RouteMCardBridge

/-!
# `RouteMReaderCard` — the reader/active cardinality invariant (∀M-L2 brick 1)

The foundational counting brick for the ∀M interior-det headline. The faithful achiever chart
factors as `φ = B ∘ pivotBlowupOn active p₀`, where `active` is the structured RESIDUAL set (the
interior E-blocks + the leaf residual — the `minAdm M` coords the radial `u = x p₀` scales) and the
READERS are the spectator coords `univ \ active` (fixed by `pivotBlowupOn`, read by `B` as ordinary
coords). The design (decorrelated Codex + the (2,2,2) `hmap_222` analysis): `readerSet` is DERIVED
from `active` (`readerSet := univ \ active`), NOT chosen independently — a chosen-active that is not
the residual set breaks the map identity `hmap`.

This module banks the cardinality bookkeeping INDEPENDENT of the structured-active construction
(brick 3): given any `active` of cardinality `minAdm M` in `Fin (routeMAmbient M)` (which exists by
`radialActive_exists`; the structured one is built in brick 3), the reader-complement
`univ \ active` has cardinality `flatDim M − minAdm M`, and the headline invariant
`readerSet.card + minAdm M = flatDim M` holds (equality — `flatDim = routeMAmbient = card univ`).
The `minAdm M ≤ flatDim M` half is the banked `minAdm_le_routeMAmbient` (`routeMAmbient = flatDim`).

* `minAdm_le_flatDim` — `minAdm M ≤ flatDim M` (the codim ≤ ambient-dim bound).
* `readerComplement_card` — `(univ \ active).card = flatDim M − minAdm M`.
* `readerComplement_card_add_minAdm` — `(univ \ active).card + minAdm M = flatDim M` (the invariant,
  as an EQUALITY; the `≤` form is immediate).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite cardinality; no analysis).
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **`minAdm M ≤ flatDim M`** — the achiever-center codimension is at most the ambient parameter
dimension `flatDim M = ∑_s M_s·M_{s+1}`. This is the banked `minAdm_le_routeMAmbient` reread through
the definitional `routeMAmbient M = flatDim M`. The `minAdm` half of the reader/active count. -/
theorem minAdm_le_flatDim (M : Fin (L + 1) → ℕ) : minAdm M ≤ flatDim M :=
  minAdm_le_routeMAmbient M

/-- **The reader-complement count**: with `active.card = minAdm M`, the spectator (reader) coords
`univ \ active` number `flatDim M − minAdm M`. (`Finset.card_sdiff_of_subset` on `active ⊆ univ`;
`card_univ = routeMAmbient = flatDim`.) The reader count for the headline's slot-zone. -/
theorem readerComplement_card (M : Fin (L + 1) → ℕ)
    (active : Finset (Fin (routeMAmbient M))) (hcard : active.card = minAdm M) :
    ((Finset.univ : Finset (Fin (routeMAmbient M))) \ active).card = flatDim M - minAdm M := by
  have huniv : (Finset.univ : Finset (Fin (routeMAmbient M))).card = flatDim M := by
    rw [Finset.card_univ, Fintype.card_fin]; rfl
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ active), huniv, hcard]

/-- **The reader/active cardinality invariant** (as an EQUALITY): with `active.card = minAdm M`, the
readers and the active residual coords partition the `flatDim M` flat coordinates —
`(univ \ active).card + minAdm M = flatDim M`. The `≤` form the slot-zone uses (`readerSet.card +
minAdm ≤ flatDim`) is immediate from this; it certifies the reader-complement has exactly `minAdm`
room for the structured active set (brick 3). -/
theorem readerComplement_card_add_minAdm (M : Fin (L + 1) → ℕ)
    (active : Finset (Fin (routeMAmbient M))) (hcard : active.card = minAdm M) :
    ((Finset.univ : Finset (Fin (routeMAmbient M))) \ active).card + minAdm M = flatDim M := by
  rw [readerComplement_card M active hcard]
  have : minAdm M ≤ flatDim M := minAdm_le_flatDim M
  omega

end DLNFibre.DLN.RLCT
