import DLNFibre.DLN.Aoyagi.StepConstructor
import DLNFibre.DLN.Aoyagi.LeafCoverTiling

/-!
# R2 (cover-side) — the FAMILY-UNION-COVER: the born-siblings tile the parent box

The elder's named R2 obligation, as a THEOREM: the UNION of the born-siblings' images covers the
parent (node) box — the non-redundant thing M1 did NOT test (M1 proved single-leaf shrink ⊇ its own
box; here the FAN of born siblings covers the node box). Cover/geometry-side only (the ideal-side
`RegionRepresents` monomialisation is R3's).

`bornSiblings_union_covers`: at a node with center `Z` and clean node clearing `c`, GIVEN the
clearing
covers the source box (`closedBall 0 (max R 1) ⊆ c.shear '' dom` — the shear box-containment, banked
for the real shears as `GeneralGeoAtlas.blockShear_covers_of_norm_bound` /
`Corank2FanCover334.blockShear_covers_scaled`), the union of the born-siblings' step-maps
(`bornSiblings … p .stepMap = blockBlowupMap Z p ∘ c.shear`) covers `ball 0 R`. Proof: the banked
argmax cover `ball_subset_iUnion_blockBlowup_comp` — a target `x ∈ ball 0 R` lifts to a pivot `p ∈
Z`
and a source point in the box, which the clearing realises. Each sibling is the constructor's own
`PivotStep` (from M2), so this marries the born-siblings (R1) to the block-cover atom.

**Scope (honest).** This is the family-union-cover AT A NODE (the elder's owed obligation). The full
R2 rung — the radius-parameterised REAL-TREE cover fold over `conRel_wf` (marrying
`GeoCoverSpec.flatCube_subset_leafPathImages`'s real BRANCHING fold with `FanTree.Covers`'s GROWING
radius, per-node clause = this theorem, IH at `f (max R 1)`, global `C*`) — is the genuine new fold
the R3-derisk named as "R2's real work"; its shape is pinned below but the `conRel_wf` marriage is
not
yet assembled. Reported as the remaining R2 work.

## Main result
- `bornSiblings_union_covers` — the family-union-cover at a node: the born-siblings' union covers
the
  node ball (given the node clearing covers the source box).
-/

open DLNFibre.Core.Aoyagi Metric Set
open DLNFibre.DLN.Aoyagi.LeafCoverTiling

namespace DLNFibre.DLN.Aoyagi.CoverFold

open DLNFibre.DLN.Aoyagi.StepConstructor

/-- **FAMILY-UNION-COVER (per node).** At a node with nonempty center `Z` and clean node clearing
`c`
(kept at each pivot of `Z`), if the clearing covers the source box (`closedBall 0 (max R 1) ⊆
c.shear '' dom`), then the UNION of the born-siblings' step-maps covers `ball 0 R`. The fan of
siblings
born at the pivots of `Z` tiles the node ball — not a single-leaf fact. -/
theorem bornSiblings_union_covers {N : ℕ} (Z : Finset (Fin N)) (hZ : Z.Nonempty)
    (c : CleanClearing N) (hkeep : ∀ p ∈ Z, c.keep p) (dom : Set (Fin N → ℝ))
    {R : ℝ} (hR : 0 < R) (hshearcov : closedBall 0 (max R 1) ⊆ c.shear '' dom) :
    ball (0 : Fin N → ℝ) R ⊆
      ⋃ p : {p // p ∈ Z}, (bornSiblings Z c hkeep p.1 p.2).stepMap '' dom := by
  have hcov : ∀ p ∈ Z, closedBall (0 : Fin N → ℝ) (max R 1) ⊆
      ⋃ i ∈ {i : {q // q ∈ Z} | i.1 = p}, c.shear '' dom := by
    intro p hp x hx
    exact Set.mem_iUnion₂.mpr ⟨⟨p, hp⟩, rfl, hshearcov hx⟩
  have h := ball_subset_iUnion_blockBlowup_comp (S := Z) hZ hR
    (g := fun _ : {q // q ∈ Z} ↦ c.shear) (A := fun _ ↦ dom) (pv := fun p ↦ p.1) hcov
  -- the atom's union is over the born-siblings' step-maps (definitionally)
  exact h

end DLNFibre.DLN.Aoyagi.CoverFold
