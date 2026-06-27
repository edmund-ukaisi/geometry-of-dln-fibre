<task>
Lean 4 + Mathlib v4.29. Route (b): discharge a `cov` change-of-variables field via MeasurePreserving +
MeasurableEmbedding (NO HasFDerivAt/Jacobian). I need the cleanest concrete plumbing for a `Fin 4 → ℝ`
self-map that is a fiberwise translation with a MEASURABLE (not continuous) shift.

THE MAP (a "shear" on `Fin 4 → ℝ`, coords `(a,b,z,sb) = (u 0,u 1,u 2,u 3)`):
  shear121 (u) = ![u 0, u 1, u 2 - (u 1 / u 0) * u 3, u 3]
i.e. coord 2 (`z`) is translated by `f(a,b,sb) = -(b/a)·sb`, a MEASURABLE function of coords {0,1,3}
(rational; NOT continuous at a=0, but a=0 is null).

THE GOAL — discharge this `cov` field (note `leafH ≡ 0`, so the weight `∏|u_j|^{leafH j} = 1`):
  cov : ∀ V, MeasurableSet V → ∀ g : (Fin 4 → ℝ) → ℝ≥0∞,
    ∫⁻ x in phi121sm '' (V \ {x | x 2 = 0}), g x      -- pivot p = z-axis = index 2
      = ∫⁻ u in V \ {x | x 2 = 0}, ENNReal.ofReal (∏ j, |u j| ^ (0:ℕ)) * g (phi121sm u)
where `phi121sm = paramsEquivFlat M121 ∘ chartParams121` and `chartParams121 = pack121 ∘ shear121`
(`pack121` and `paramsEquivFlat` are measure-preserving LINEAR equivs). So
`phi121sm = Q121 ∘ shear121` with `Q121 := paramsEquivFlat ∘ pack121` a measure-preserving linear equiv.

I HAVE (sorry-free, banked):
- `MeasurePreserving.setLIntegral_comp_emb (hg : MeasurePreserving g μ ν) (hge : MeasurableEmbedding g)
   (f) (s) : ∫⁻ a in s, f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν` — this is EXACTLY the cov shape (with
   weight 1, RHS-to-LHS).
- `shear121_injOn : Set.InjOn shear121 {u | u 0 ≠ 0}` (off-pole injective).
- `measurePreserving_coreShear (a b c) (shift : (Fin a→ℝ)×(Fin c→ℝ)→(Fin b→ℝ)) (hshift : Continuous shift)
   : MeasurePreserving (fun q : (Fin a→ℝ)×((Fin b→ℝ)×(Fin c→ℝ)) => (q.1,(q.2.1 + shift(q.1,q.2.2),q.2.2)))
   volume volume` — the banked fiber-shear MP (via skew_product + measurePreserving_add_right). Its proof
   only uses `hshift.measurable`; a MEASURABLE-shift variant should follow by the same proof.

QUESTIONS:
1. The cleanest concrete path to `MeasurePreserving phi121sm volume volume`: should I (a) reindex
   `Fin 4 → ℝ ≃ᵐ (Fin 1→ℝ) × ((Fin 1→ℝ) × (Fin 2→ℝ))` (core=z, the rest) and conjugate
   `measurePreserving_coreShear` (with a MEASURABLE-shift variant), then compose with `Q121` (MP linear
   equiv)? Or (b) prove `MeasurePreserving shear121` more directly (e.g. it's `id` on coords 0,1,3 and a
   `z ↦ z + f(rest)` translation — is there a slicker `Fin`-indexed shear MP lemma than reindexing to a
   binary product)? Give the EXACT lemma chain. Flag the reindex friction (the `Fin 4 → ℝ` vs binary-product
   measure-equiv `volume_eq_prod`/`MeasurableEquiv.piFinSuccAbove`-style adapters).
2. The MEASURABLE-shift variant of `measurePreserving_coreShear`: confirm `MeasurePreserving.skew_product`
   needs only `Measurable (uncurry g)` (not continuity), so replacing `Continuous shift` with
   `Measurable shift` in the banked proof works verbatim. Give the exact `skew_product` hypothesis.
3. `MeasurableEmbedding phi121sm`: `phi121sm` is a bijection on `Fin 4→ℝ` (global, since the inverse
   `(a,b,z',sb)↦(a,b,z'+(b/a)sb,sb)` is measurable even at a=0 where b/a totalizes to 0 — it's still a
   measurable bijection). Is `MeasurableEmbedding` of a measurable bijection-with-measurable-inverse the
   right framing (`MeasurableEquiv.measurableEmbedding` after packaging as a `≃ᵐ`)? Or, since I only need
   the cov on `V\{z=0}` (off the pivot, but the POLE {a=0} is the issue not {z=0}), do I still need the
   image-null `φ_sm''(s∩{a=0})` split, OR does the GLOBAL measurable-bijection framing make `shear121` a
   genuine `MeasurableEquiv` on all of `Fin 4→ℝ` (the pole included, since the translation is a measurable
   bijection there too), so NO split is needed and the cov holds on all of `V\{z=0}` directly? Assess
   carefully: is `shear121` (with b/a totalized to 0 at a=0) a measurable BIJECTION on all of `Fin 4→ℝ`,
   measure-preserving globally? If yes, the whole pole-split disappears.
4. Given Q3: if `shear121` is a global measurable measure-preserving bijection, the cleanest cov proof is
   `(MeasurePreserving phi121sm).setLIntegral_comp_emb (MeasurableEmbedding phi121sm) g (V\{z=0})` +
   rewriting the weight `ofReal(∏|u_j|^0)=1`. Confirm this discharges the field with NO image-null split.
   What's the exact handling of the `∏ j, |u j|^(0:ℕ) = 1` → `ofReal 1 = 1` → `1 * g = g` rewrite?
</task>

<output_contract>
Answer Q1–Q4 in order. For Q1 give the exact lemma chain (reindex equiv name + coreShear conjugation +
Q121 compose). For Q2 confirm measurable-shift suffices + the skew_product hyp. For Q3 give a yes/no on
whether shear121 is a GLOBAL measurable MP bijection (so no pole-split) with the reasoning. For Q4 the exact
weight-rewrite tactic. End with "RECOMMEND:" — the single cleanest lemma sequence to the cov field, and
whether the pole-split is needed. Flag any lemma name you're unsure exists in v4.29.
</output_contract>

<grounding_rules>
Distinguish certain-Mathlib-v4.29-facts from inference. The load-bearing uncertainty is Q3 (is the totalized
shear a GLOBAL measure-preserving measurable bijection, eliminating the pole-split?) and Q1 (the Fin-4 ↔
binary-product reindex friction for conjugating coreShear). Be concrete about measure-equiv reindex lemma
names (`MeasurableEquiv.piFinSuccAbove`, `MeasurableEquiv.funUnique`, `volume_eq_prod`, `Measure.volume_pi`).
