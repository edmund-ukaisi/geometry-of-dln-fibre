# Consultation: measure-preservation of a polynomial automorphism (Lean 4 / Mathlib v4.29)

I need to prove (sorry-free, Lean) that an explicit polynomial bijection on `Fin 7 → ℝ` preserves
Lebesgue volume. It's the "Lemma-2" regular change of coordinates in an RLCT resolution.

## The map

```
lemma2Fwd (v : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![ v 0,                 -- slot 0 unchanged
     v 3 + v 0 * v 5,     -- slot 1
     v 4 + v 0 * v 6,     -- slot 2
     v 2 - v 0 * v 1,     -- slot 3
     v 1,                 -- slot 4
     v 5,                 -- slot 5 unchanged
     v 6 ]                -- slot 6 unchanged
```
It has a polynomial inverse (already proven `Equiv`), and the Jacobian determinant is the CONSTANT
`−1` (sympy-verified). I have `lemma2Equiv : (Fin 7 → ℝ) ≃ (Fin 7 → ℝ)`, both directions continuous,
and a `Homeomorph`. I need `MeasurePreserving lemma2Fwd volume volume`.

## The question — cleanest sound route in Mathlib v4.29

It is NOT linear (bilinear terms `v0*v5` etc.), so `Matrix`/`LinearMap` volume lemmas don't apply
directly. Candidate routes:

(A) **Shear decomposition.** Decompose as a composition of (i) a coordinate permutation (slot 1↔4,
slot 2,3 reorder) — measure-preserving via `MeasurableEquiv.piCongrLeft` /
`volume_preserving_piCongrLeft`; and (ii) elementary "transvection" shears `x_i ↦ x_i + f(other
coords)` — each measure-preserving via `measurePreserving_prod_add` (the shear `(x,y)↦(x,x+y)`) after
isolating the sheared coordinate with `MeasurableEquiv.piFinSuccAbove` or `piEquivPiSubtypeProd`. Is
this the cleanest? How many shear steps, and what's the cleanest way to isolate one coordinate as a
`ℝ × (rest)` product for `measurePreserving_prod_add`? Concretely: to prove `x_i ↦ x_i + g(x_{≠i})`
preserves `volume` on `Fin n → ℝ`, what is the shortest Mathlib chain?

(B) **Change of variables with constant unit Jacobian.** Is there a Mathlib lemma "a `C¹`
diffeomorphism with `|det Dφ| = 1` everywhere is measure-preserving" that I can apply with the explicit
constant Jacobian? (e.g. via `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` /
`MeasurePreserving` from `|det| = 1`?) What's the exact lemma name and what do I need to supply
(injectivity, `HasFDerivAt`, the det computation)?

(C) Any cleaner route I'm missing — e.g. a "triangular polynomial map with unit diagonal Jacobian
preserves volume" lemma, or expressing it as `Measure.map` and using `map_eq` via the inverse?

Please recommend the route with the FEWEST Mathlib steps for THIS specific 7-variable map, with
concrete v4.29 lemma names. If (A), give the explicit shear/permutation factorization order and the
one-coordinate-shear measure-preservation chain. Flag any instance/defeq friction (e.g. the
`volume = Measure.pi` vs `Measure.prod` mismatch when isolating a coordinate).
