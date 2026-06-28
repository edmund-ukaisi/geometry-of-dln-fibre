<task>
In Lean 4 + Mathlib (v4.29), give the cleanest proof that a 2-coordinate "triangular shear" on
`Fin 9 → ℝ` is measure-preserving for the product Lebesgue (`volume`) measure. I have the map and its
measurable-equivalence already; I need `MeasurePreserving shear231 volume volume`.
</task>

<context>
The map (each output coord; `lam231 w 0`, `lam231 w 1` are MEASURABLE functions reading ONLY coords
0..5; neither reads coord 6 or 7):

  shear231 w i =
    if i = 6 then w 6 - lam231 w 0 * w 8
    else if i = 7 then w 7 - lam231 w 1 * w 8
    else w i

So it translates coords 6 and 7 by measurable functions of {0,1,2,3,4,5,8} (the shifts do NOT depend
on coords 6 or 7, and not on each other's coord). It is the identity on {0,1,2,3,4,5,8}.

I HAVE already (all sorry-free):
- `shear231_measurable : Measurable shear231`
- `shear231Inv` (adds the shifts back), `shear231_leftInv`, `shear231_rightInv`, `shear231Inv_measurable`
- `shear231ME : (Fin 9 → ℝ) ≃ᵐ (Fin 9 → ℝ)` (the MeasurableEquiv from the above)
- `lam231_measurable (i : Fin 2) : Measurable (fun w => lam231 w i)`

I have a banked single-core skew-product lemma (the (1,2,1) module):
  measurePreserving_coreShear_measurable (a b c : ℕ)
    (shift : (Fin a → ℝ) × (Fin c → ℝ) → (Fin b → ℝ)) (hmshift : Measurable shift) :
    MeasurePreserving
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) =>
        (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))
      volume volume

and the (1,2,1) precedent proved its single-coord shear MP by conjugating this by a measurable-equiv
reindex `split121 : (Fin 4 → ℝ) ≃ᵐ (Fin 1 → ℝ) × ((Fin 1 → ℝ) × (Fin 2 → ℝ))` built from
`MeasurableEquiv.piFinSuccAbove`/`funUnique`/`prodCongr`, with `measurePreserving_split121` from
`volume_preserving_piFinSuccAbove`/`volume_preserving_funUnique`, then
`MeasurePreserving.congr` against the explicit pointwise identity `shear = split.symm ∘ coreShear ∘ split`.

QUESTION: For the 2-coordinate case at Fin 9, what is the cleanest route?
Option A: decompose `shear231 = T6 ∘ T7` (two single-coord shears) and prove each MP by the
  split-conjugation (TWO Fin-9 `piFinSuccAbove` peels). Index bookkeeping.
Option B: a single `split231` pulling out the 2-core {6,7} and ONE `coreShear_measurable` with b=2.
Option C: something simpler — e.g. a Mathlib lemma that a measurable shear `x ↦ x + N(x)` where
  `N i` reads only coords ≠ i is volume-preserving directly; the shifts are NONLINEAR.

Give the most robust concrete tactic-level Lean for whichever option you recommend. Prefer fewest
moving `MeasurableEquiv` reindex parts. Mathlib v4.29 quirks: `MeasurableEquiv.prodCongr_apply`,
`coe_refl`, `symm_trans` do NOT exist.
</context>

<output>
The recommended option + concrete Lean (definitions + the MP theorem proof skeleton), and the precise
index map for the piFinSuccAbove peel(s).
</output>
