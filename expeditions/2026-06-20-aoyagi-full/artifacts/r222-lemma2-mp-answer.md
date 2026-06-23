exit=0
1. `x1 ↦ x1 + x0*x5`
2. `x2 ↦ x2 + x0*x6`
3. `x3 ↦ x3 - x0*x4`  (i.e. `x3 + (-(x0*x4))`)

Each shear is exactly the 1‑coordinate lemma with  
`g r = r0 * r5`, `r0 * r6`, `-(r0 * r4)` (after re‑indexing).  
Compose: `shear3 ∘ shear2 ∘ shear1 ∘ perm`.

**About route (B) (Jacobian = 1)**  
You can make it work, but it’s *longer*: you’ll have to use change‑of‑variables lemmas from
`Mathlib/MeasureTheory/Function/Jacobian.lean`, notably
- `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
(or for Bochner integrals, `integral_image_eq_integral_abs_det_fderiv_smul`)
together with `HasFDerivAt`, `measurableEmbedding`/`injOn`, and the det computation.  
There’s no “one‑liner” `MeasurePreserving` lemma for `|det| = 1` in v4.29.

If you want, I can help write the exact Lean proof term for the shear lemma and the concrete permutation for your `Fin 7` indexing.
tokens used
42,852
**Recommendation (fewest steps in v4.29)**  
Use route **(A)**: permutation + three one‑coordinate shears, each proved measure‑preserving via `MeasurePreserving.skew_product` and `measurePreserving_add_right`. There is **no** ready-made “Jacobian = 1 ⇒ MeasurePreserving” lemma, so route (B) is longer.

**1‑coordinate shear lemma (the core reusable step)**  
Let `i : Fin n` and `g : ({j // j ≠ i} → ℝ) → ℝ`. Define
```
shear i g : (Fin n → ℝ) → (Fin n → ℝ)
```
as conjugation by `MeasurableEquiv.piEquivPiSubtypeProd` to split off coordinate `i`:
```
e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun j => j ≠ i)
shear i g := fun x => e.symm ( (e x).1, (e x).2 + g (e x).1 )
```
Then the proof skeleton is:

- `hE : MeasurePreserving e` via  
  `volume_preserving_piEquivPiSubtypeProd (fun _ => ℝ) (fun j => j ≠ i)`.
- `hshear' : MeasurePreserving (fun p : rest × ℝ => (p.1, p.2 + g p.1)) (volume.prod volume) (volume.prod volume)` via  
  `MeasurePreserving.skew_product` with
  - `f := id` and `(MeasurePreserving.id _)`,
  - measurability of `uncurry (fun r x => x + g r)`,
  - `hg : ∀ᵐ r, map (fun x => x + g r) volume = volume`, proved by  
    `ae_of_all _ (fun r => (measurePreserving_add_right (μ := volume) (g r)).map_eq)`.

- Conjugate back:
```
(MeasurePreserving.symm e hE).comp (hshear'.comp hE)
```

Lemma names used:
- `volume_preserving_piEquivPiSubtypeProd`
- `MeasurePreserving.skew_product`
- `measurePreserving_add_right`
- `MeasurePreserving.comp`
- `MeasurePreserving.symm`

This avoids any `volume = Measure.pi` friction; the `volume_preserving_*` lemmas already land in `volume.prod volume`.

**Decomposition for your `lemma2Fwd`**
Let `perm` reorder coordinates to
`(v0, v3, v4, v2, v1, v5, v6)` using  
`MeasurableEquiv.piCongrLeft` and `volume_measurePreserving_piCongrLeft`.

Then define three shears on the reordered coordinates:
1. `x1 ↦ x1 + x0*x5`
2. `x2 ↦ x2 + x0*x6`
3. `x3 ↦ x3 - x0*x4`  (i.e. `x3 + (-(x0*x4))`)

Each shear is exactly the 1‑coordinate lemma with  
`g r = r0 * r5`, `r0 * r6`, `-(r0 * r4)` (after re‑indexing).  
Compose: `shear3 ∘ shear2 ∘ shear1 ∘ perm`.

**About route (B) (Jacobian = 1)**  
You can make it work, but it’s *longer*: you’ll have to use change‑of‑variables lemmas from
`Mathlib/MeasureTheory/Function/Jacobian.lean`, notably
- `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
(or for Bochner integrals, `integral_image_eq_integral_abs_det_fderiv_smul`)
together with `HasFDerivAt`, `measurableEmbedding`/`injOn`, and the det computation.  
There’s no “one‑liner” `MeasurePreserving` lemma for `|det| = 1` in v4.29.

If you want, I can help write the exact Lean proof term for the shear lemma and the concrete permutation for your `Fin 7` indexing.
