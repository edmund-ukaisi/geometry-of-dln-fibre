# Statement card — L2 scale-join: the (3,3,4) fan cover at GENERAL target radius R

The elder's guardrail (i), bounded: generalize the (3,3,4) `gWrapFan` cover from the hardcoded target
radius `R = 1` (the `903`-inflated leaf domain) to a GENERAL target radius `R`. #188's born-α family
(cover side, P2) needs the cover at a SMALL `R` (the residual-unit radius), not the `R = 1` one. The
engine atoms already carry the scale — this only threads `R`, no re-derivation.

> **Claim (L2 scale-join, cover side / P2).** For every target radius `R`, the shared (3,3,4) cover fan
> `gWrapFan R` (the `fanOfSteps` fan whose canonical leaf is `gWrap = sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘
> bbA1`) covers the closed ball of radius `R` about `0` by its leaf-chart images, under the quadratic
> inflation `f = r ↦ r + 2r²` (which sizes only the leaf boxes, not the covered ball). Hence for `0 < R`
> the leaf-chart images are a neighbourhood of `0`, and choosing `R` small covers a small ball — the
> shape the born-α value side (P1) needs at the residual-unit radius.
>
> - **Lean:** module `DLNFibre.DLN.Aoyagi.Corank2FanCover334`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2FanCover334.lean` @ `1542ee7d452d8067d029e2ff366cd77f85f4bfaa`,
>   branch `expedition/aoyagi-l2scalejoin`).
>   ```
>   theorem gWrapFan_covers (R : ℝ) : Covers (fun r ↦ r + 2 * r ^ 2) (gWrapFan R) R
>
>   theorem ball_subset_gWrapFan_leafImages (R : ℝ) :
>       ball (0 : Fin 21 → ℝ) R ⊆ (gWrapFan R).leafImages
>
>   theorem gWrapFan_leafImages_mem_nhds {R : ℝ} (hR : 0 < R) :
>       (gWrapFan R).leafImages ∈ 𝓝 (0 : Fin 21 → ℝ)
>
>   theorem exists_ball_subset_gWrapFan_leafImages {R : ℝ} (hR : 0 < R) :
>       ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : Fin 21 → ℝ) ρ ⊆ (gWrapFan R).leafImages
>   ```
> - **Gloss.**
>   - `gWrapFan_covers R`: the `FanTree.Covers` fold-condition holds for the fan `gWrapFan R` at target
>     radius `R` (each of the three fan nodes box-contains under `f`, and the leaf boxes are sized by the
>     iterated `f`). It is the general-`R` form of the former `Covers … (gWrapFan 1) 1`.
>   - `ball_subset_gWrapFan_leafImages R`: every point of sup-norm `< R` about `0` lies in the union of
>     the fan's leaf-chart images. The **covered** radius is EXACTLY `R` (no `f`-inflation on this side);
>     the `f = r ↦ r + 2r²` inflation only enlarges the leaf source boxes. For `R ≤ 0` the ball is empty
>     (vacuous). No positivity hypothesis.
>   - `gWrapFan_leafImages_mem_nhds hR`: for `0 < R`, the leaf-chart images form a neighbourhood of `0`.
>     The `U ∈ 𝓝 0` shape the born-α wire (#188) consumes: instantiate at `R` = the residual-unit radius.
>   - `exists_ball_subset_gWrapFan_leafImages hR`: the `∃ ρ > 0` shape (witness `ρ = R`), the general-`R`
>     generalization of the former `R = 1` named theorem.
> - **Proved.** All four, unconditionally in `R` (positivity only where a genuine neighbourhood is
>   asserted). `#print axioms` on all four = `[propext, Classical.choice, Quot.sound]` (forced
>   `#assert_banked_clean_batch` gate in-file + explicit `#print axioms` scratch, sorry-free, no cited
>   axiom).
> - **Assumed.** `gWrapFan_covers` / `ball_subset_gWrapFan_leafImages`: none (`R` free). `mem_nhds` /
>   `exists_…`: `0 < R` (needed for a genuine neighbourhood / nonempty `ρ`). No other hypotheses.
> - **Cited.** none — built on the already-scale-parametric engine: `LeafCoverTiling.FanTree.Covers`,
>   `covers_subset`; `GeneralGeoAtlas.covers_fanOfSteps`; `Corank2FanDef334.gWrapFan`; the per-step
>   box-containment `gWrapFanSteps_boxContain` (unchanged, this file) and its atoms (`shearH_covers`,
>   `permP_image_superset`, `blockShear_covers_scaled`); Mathlib (`ball_subset_closedBall`,
>   `ball_mem_nhds`, `mem_of_superset`).
> - **Deferred.** The **value side (P1)** — the born-α per-leaf value survivors / sandwich — is NOT here;
>   it is a parallel pen-and-paper. Assembly (a later seat) wires this cover (`hcover`) with the value
>   (`hsandwich`) at `R = min leaf sandwich-unit-radius`. NOTE (W1 seam, surfaced by P1 pnp): the value
>   may ride per-leaf NATIVE born-α (a distinct shear per leaf) rather than the fixed `shearH ∘ permP`;
>   the cover/value OBJECT-unification is under elder review. This card is object-specific to the
>   fixed-shear `gWrapFan`; the general-`R` SCALING is object-agnostic (see Route) and transfers to any
>   `fanOfSteps` fan whose steps box-contain.
> - **Route (formaliser, aoyagi-l2scalejoin).** The engine was already scale-parametric — the labour was
>   threading, per the mandate. `gWrapFan R = fanOfSteps f gWrapFanSteps R` (def) and `covers_fanOfSteps`
>   is `∀ R`, with hypothesis `∀ t, closedBall 0 t ⊆ shear '' closedBall 0 (f t)` — which
>   `gWrapFanSteps_boxContain` already proves at every `t`. So `gWrapFan_covers R :=
>   covers_fanOfSteps gWrapFanSteps R gWrapFanSteps_boxContain` (one line, general `R`). Then
>   `covers_subset (gWrapFan R) (gWrapFan_covers R) : closedBall 0 R ⊆ leafImages`, and
>   `ball_subset_closedBall.trans …` gives the open-ball form; `mem_of_superset (ball_mem_nhds 0 hR) …`
>   gives the `𝓝 0` form. No atom was re-derived and no fixed-shear-specific value/survivor claim was
>   made. Added `open Topology` for `𝓝`.
> - **LoC.** `+40 −13` (net `+27`) in `Corank2FanCover334.lean`; the box-containment §0–§2.1 atoms
>   untouched (consumer `NodeCover334.shearH_covers` safe).
> - **Status.** sorry-free (awaiting reviewer fidelity check).
