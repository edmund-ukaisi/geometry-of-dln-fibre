<task>
Lean 4 + Mathlib v4.29. I'm building a measure-preserving equivalence `Params(2,2,2) ≃ᵐ (Fin 8 → ℝ)`
and hitting a SPECIFIC elaboration/instance wall when stating/proving the measure-preservation of an
intermediate "append" equiv on binary products. I need the CONCRETE Lean idiom to get past it (exact
syntax/tactic), not a redesign. I write/run the Lean.

## The setup (works)
```lean
noncomputable def finAppend (n m : ℕ) : ((Fin n → ℝ) × (Fin m → ℝ)) ≃ᵐ (Fin (n + m) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr' finSumFinEquiv (MeasurableEquiv.refl ℝ))
```
This DEF elaborates fine.

## The wall: stating its measure-preservation
There is NO `MeasureSpace ((Fin n → ℝ) × (Fin m → ℝ))` instance in Mathlib (confirmed: `inferInstance`
fails). So I must use an explicit product measure for the domain. Every phrasing I've tried fails:

1. `MeasurePreserving (finAppend n m) (volume.prod volume) volume`
   → `failed to synthesize instance` on the `volume`s (can't infer the factor types / product).
2. `MeasurePreserving (finAppend n m) ((volume:Measure (Fin n→ℝ)).prod (volume:Measure (Fin m→ℝ))) (volume:Measure (Fin (n+m)→ℝ))`
   → Type mismatch on the CODOMAIN: `volume has type @Measure ?m MeasureSpace.toMeasurableSpace but
   expected @Measure (Fin (n+m)→ℝ) MeasurableSpace.pi`. (A MeasurableSpace instance diamond:
   `MeasureSpace.toMeasurableSpace` vs `MeasurableSpace.pi` on `Fin k → ℝ` — defeq but the elaborator
   picks different ones for the equiv's codomain vs the `volume` term.)
3. Factors as `Measure.pi (fun _ : Fin n => (volume:Measure ℝ))` → same codomain mismatch.

The available m.p. lemmas (CHECKED to exist, v4.29):
- `measurePreserving_sumPiEquivProdPi_symm (μ) : MeasurePreserving (sumPiEquivProdPi X).symm
   ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) (Measure.pi μ)`
- `measurePreserving_arrowCongr' (μ) (ν) (eα) (eβ) (hm) : MeasurePreserving (arrowCongr' eα eβ)
   (Measure.pi μ) (Measure.pi ν)`
- `volume_pi : (volume : Measure (Π i, α i)) = Measure.pi (fun i => volume)`
- `MeasurePreserving.prod`, `MeasurePreserving.trans`, `MeasurePreserving.comp`.

## The actual goal
I ultimately want `MeasurePreserving e222 (volume : Measure (Params (2,2,2))) (volume : Measure (Fin 8 → ℝ))`
where `Params(2,2,2) = ∀ s:Fin 2, Matrix (Fin 2)(Fin 2) ℝ` (a NESTED pi, HAS a MeasureSpace instance via
the pi/Matrix instances), and `e222` is the explicit flatten (a00↦0,…,b11↦7). The binary-product
`finAppend` was Codex's earlier suggested building block, but the product-MeasureSpace instance gap makes
its m.p. statement fight the elaborator (above).

## The questions (concrete idiom, ranked)
1. THE STATEMENT: what is the EXACT phrasing of `MeasurePreserving finAppend <domain> <codomain>` that
   elaborates? (e.g. `@MeasurePreserving _ _ _ _ (finAppend n m) ((Measure.pi _).prod (Measure.pi _)) volume`
   with explicit MeasurableSpace args? or `(volume.prod volume : Measure _)` with a type ascription on the
   WHOLE prod? or use `Measure.volume_eq_prod`-style? or avoid `volume` on the codomain and write
   `Measure.pi (fun _ => volume)` there to match `MeasurableSpace.pi`?) Give the precise syntax that
   dodges the `MeasureSpace.toMeasurableSpace` vs `MeasurableSpace.pi` diamond.
2. ALTERNATIVELY: should I ABANDON the binary-product `finAppend` building block entirely and build
   `e222` the way `paramsEquivFlat` does — `piCurry`-collapse the nested pi to a single `Σ`-indexed pi,
   then ONE `arrowCongr'`/`piCongrLeft` reindex by an EXPLICIT `Fin 8 ≃ FlatIdx` bijection — which never
   forms a binary product, so never needs `MeasureSpace (α×β)`? I have `measurePreserving_piCurry`
   (proven) + `measurePreserving_paramsEquivFlat` (proven, but uses the noncomputable `Fintype.equivFin`).
   If I just swap `Fintype.equivFin (FlatIdx H)` for my explicit `myEq : Fin 8 ≃ FlatIdx H222` in a
   generalized `paramsEquivFlatWith`, the m.p. proof is identical (arrowCongr' works for any equiv) and
   there are ZERO binary products. Is this strictly cleaner than fighting the product elaboration? What's
   the cost of defining the explicit `Fin 8 ≃ FlatIdx (fun _ => 2)` (= `Σ q:(Σ s:Fin2,Fin2),Fin2`,
   constant bounds so ≃ Fin2×Fin2×Fin2)?
3. For the explicit `Fin 8 ≃ FlatIdx (fun _:Fin 3 => 2)`: cleanest construction (finProdFinEquiv chain?
   Finset.orderIsoOfFin? an explicit ⟨match⟩?) realizing a specific order, and is proving it's an Equiv
   (left/right inv) `decide`-able since everything is concrete `Fin`?

## Output
Q1: the exact elaborating statement syntax (the diamond-dodge). Q2: yes/no abandon binary products for
the piCurry+explicit-reindex route, with the decisive reason. Q3: cleanest explicit `Fin 8 ≃ FlatIdx`
construction + whether the Equiv proof is `decide`-able. Terse; concrete syntax over prose.
</task>

<output_contract>
Three numbered answers. Q1: 1-2 exact Lean statement lines that elaborate (or "not fixable as stated,
use Q2"). Q2: ABANDON/KEEP + one decisive reason. Q3: the construction + decide-ability yes/no.
Confidence flags on any lemma/instance names.
</output_contract>

<grounding_rules>
Be concrete: I need syntax that compiles, not a description. If the binary-product route is genuinely a
dead-end for clean Lean (the diamond can't be dodged cleanly), say so plainly and commit to the
piCurry+explicit-reindex route. Distinguish confident-v4.29 from unverified names.
</grounding_rules>
