**VERDICT:** No: no fixed finite-intersection neighborhood from `S := h.source`, `T := h.target` gives the literal bi-invariance, and the literal `hmaps`/`hsymmmaps` signature is too strong without extra dynamical hypotheses.

For `A := S ∩ T`, the proposed
```lean
V = A ∩ h ⁻¹' A ∩ h.symm ⁻¹' A
```
does not close. If `w ∈ V`, then `h w ∈ A`; but to prove `h w ∈ V` you also need `h (h w) ∈ A`. That is the next forward-preimage condition. Adding finitely many clauses only moves the missing condition to the next iterate. The infinite intersection of all forward/backward clauses is invariant, but need not be open; for `f x = 2*x` near `0` inside a bounded local source, it collapses to `{0}` in the forward direction.

The downstream lemma should drop global invariance. Use a chart neighborhood such as
```lean
V0 : Set M := h.source ∩ h.target
```
(or a further open shrink for the `C¹` facts), and keep only the inverse identities on `V0`:
```lean
hleft  : ∀ w ∈ V0, h.symm (f w) = w
hright : ∀ w ∈ V0, f (h.symm w) = w
```
Then for each open `Ω`, define the actual forward working set
```lean
s Ω := V0 ∩ f ⁻¹' (Ω ∩ V0)
```
and `MapsTo f (s Ω) (Ω ∩ V0)` is just `fun w hw ↦ hw.2`. Injectivity on `s Ω` follows from `hleft`.

If the reverse branch must land back in the working neighborhood, shrink the target for that step:
```lean
t Ω := Ω ∩ V0 ∩ h.symm ⁻¹' V0
s Ω := V0 ∩ f ⁻¹' t Ω
```
Then `MapsTo h.symm (t Ω) (s Ω)` follows from the `h.symm ⁻¹' V0` clause plus `hright`; no global `hsymmmaps : MapsTo h.symm V0 V0` is needed.

Mathlib v4.29 names:

```lean
h.open_source        : IsOpen h.source
h.open_target        : IsOpen h.target
h.map_source         : w ∈ h.source → h w ∈ h.target
h.map_target         : w ∈ h.target → h.symm w ∈ h.source
h.mapsTo             : MapsTo h h.source h.target
h.symm_mapsTo        : MapsTo h.symm h.target h.source
h.left_inv           : w ∈ h.source → h.symm (h w) = w
h.right_inv          : w ∈ h.target → h (h.symm w) = w
h.leftInvOn          : LeftInvOn h.symm h h.source
h.rightInvOn         : RightInvOn h.symm h h.target
h.continuousOn       : ContinuousOn h h.source
h.continuousOn_symm  : ContinuousOn h.symm h.target
```

For your `ContDiffAt` IFT construction:
```lean
ContDiffAt.toOpenPartialHomeomorph
ContDiffAt.toOpenPartialHomeomorph_coe
ContDiffAt.mem_toOpenPartialHomeomorph_source
ContDiffAt.image_mem_toOpenPartialHomeomorph_target
ContDiffAt.to_localInverse
```
The coercion theorem is stronger than “`h = f` on source”:
```lean
(hf.toOpenPartialHomeomorph f hf' hn : M → M) = f
```
