# Statement card — block-atom cover (Q) (seat-Q)

The per-step cover atom the L7 monument cover fold (salvage option (b)) consumes: the block-center
generalization of `OriginBlowup.ball_subset_iUnion_blowup_image`. SHEAR-FREE, pure Core, network-free.

> **Claim (Q, L7 `fan-design-certificate.md` §2.1).** For a nonempty center `S ⊆ Fin D`, the open unit
> cube around `0` is covered by the union, over pivots `p ∈ S`, of the images of the `S`-center block
> blow-up charts `blockBlowupMap S p` on the closed unit cube, with the off-`S` (spectator) coordinates
> passed through:
> `cubeBox D 1 ⊆ ⋃ (p ∈ S) blockBlowupMap S p '' cubeBox D 1`.
>
> - **Lean (general form):** `DLNFibre.Core.Aoyagi.ball_subset_iUnion_blockBlowup_image_radius`
>   (`lean/DLNFibre/Core/Aoyagi/BlockBlowupCover.lean` @ `d4013880771ecb730a7b9f352d8abf193cefa1e8`)
>   ```
>   theorem ball_subset_iUnion_blockBlowup_image_radius {S : Finset (Fin D)} (hS : S.Nonempty)
>       {R : ℝ} (hR : 0 < R) :
>       Metric.ball (0 : Fin D → ℝ) R ⊆
>         ⋃ p ∈ S, (blockBlowupMap S p) '' (Metric.closedBall 0 (max R 1))
>   ```
> - **Lean (the certificate's `(Q)`, R = 1 corollary):**
>   `DLNFibre.Core.Aoyagi.ball_subset_iUnion_blockBlowup_image`
>   ```
>   theorem ball_subset_iUnion_blockBlowup_image {S : Finset (Fin D)} (hS : S.Nonempty) :
>       Metric.ball (0 : Fin D → ℝ) 1 ⊆
>         ⋃ p ∈ S, (blockBlowupMap S p) '' (Metric.closedBall 0 1)
>   ```
> - **Gloss.** `blockBlowupMap S p w` sends the pivot `p ↦ w_p`, the other center coords
>   `j ∈ S \ {p} ↦ w_p · w_j`, and every spectator `j ∉ S ↦ w_j` (fixed). The theorem: any target `x`
>   in the open ball of radius `R` about the origin (sup-norm on `Fin D → ℝ`, i.e. `|x_j| < R` for all
>   `j`) lies in the image of *some* pivot-`p` chart (`p ∈ S`) applied to the closed box of radius
>   `max R 1`. The witness pivot is the `S`-coordinate of maximal `|x_·|`; the source point is
>   `w_p = x_p`, `w_q = x_q / x_p` (`q ∈ S \ {p}`), `w_j = x_j` (spectators). At `R = 1`, `max 1 1 = 1`
>   gives the certificate's unit-cube `(Q)`.
> - **Proved.** Both statements, unconditionally, for every ambient `D`, every nonempty `S`, and
>   (radius form) every `R > 0`. `#print axioms` on both = `[propext, Classical.choice, Quot.sound]`
>   (forced-recompile, sorry-free, no cited axiom).
> - **Assumed.** `S.Nonempty` (need a pivot to route to; the certificate's `|S| ≥ 1`). Radius form also
>   assumes `R > 0`. No other hypotheses.
> - **Cited.** none — built directly on `Core.Aoyagi.BlockBlowup` (`blockBlowupMap` + structural
>   lemmas) and Mathlib.
> - **Deferred.** The R-parametric *fold* over the monument `TreePath` tree (§2.3–2.4 of the
>   certificate) and its shear box-inflation bookkeeping are NOT here — this is the single per-step
>   cover ATOM the fold consumes, not the fold. The `max R 1` source radius is the honest tight bound
>   for the atom; whether the fold wants exactly this box shape is a fold-lane design choice (flagged to
>   controller). Value/monomialisation leaves (L6/L8/Descent) are explicitly out of scope (the atom is
>   shear-free; the certificate §1.4 documents the cover/value shear coupling separately).
> - **Route (seat-Q).** Mirror the landed `OriginBlowup.ball_subset_iUnion_blowup_image` argmax-cover
>   proof, generalizing the argmax from all of `Fin D` (`S = univ`) to `S` only, with spectators passed
>   through. Two cases on `x_p = 0` (max over `S` is 0 ⟹ every center coord is 0, spectators through)
>   vs `x_p ≠ 0` (the standard argmax lift; `mul_div_cancel₀` closes `x_p · (x_j / x_p) = x_j`, ratios
>   `≤ 1` by maximality). Bounds carry the `max R 1` split (pivot/spectator `< R`, center ratios `≤ 1`).
> - **Status.** sorry-free (awaiting reviewer fidelity check).
