**Ranking**
1. **D, with one adjustment.** Best. Keep the MP `split` as the raw coordinate reindex, define the honest `Φ` using a second `coreAbsorb` map, then use one producer-certified RLCT identity to replace the absorbed core by the raw disjoint core before applying `rlct_additive_smooth_block`. If `g` reads regular coordinates, do this absorption identity on the full split space before additivity, not after.

2. **C.** Sound but heavy. It makes the normalized core syntactically disjoint, but every consumer of `split` now pays non-MP transport, Jacobian, properness/null-set, and weight-peel overhead.

3. **A.** Too abstract. Spectator-peel only applies if the core term is independent of spectators; an arbitrary `coreVal` depending on full coordinates bypasses rather than preserves the sub-6 proof.

4. **B.** Bad for sub-6. If `coreEmbed` reads the regular block, the singular term is not disjoint from `∑ reg²`, so `rlct_additive_smooth_block` does not apply.

**Winner: D, formulated as “MP split + producer-certified core absorption RLCT identity”.**

Use abbrevs like this, or expand them inline:

```lean
abbrev deepestM (H : Fin (L + 1) → ℕ) (r : ℕ) : Fin (L + 1) → ℕ :=
  fun s => H s - r

abbrev deepestNReg (H : Fin (L + 1) → ℕ) (r : ℕ) : ℕ :=
  r * (H 0 + H (Fin.last L) - r)

abbrev DeepestSplit (H : Fin (L + 1) → ℕ) (r nGauge : ℕ) : Type :=
  (Fin (deepestNReg H r) → ℝ) ×
    ((Fin (flatDim (deepestM H r)) → ℝ) × (Fin nGauge → ℝ))

noncomputable abbrev deepestCoreF (H : Fin (L + 1) → ℕ) (r : ℕ)
    (y : Fin (flatDim (deepestM H r)) → ℝ) : ℝ :=
  dlnLoss (deepestM H r)
    (0 : Matrix (Fin ((deepestM H r) 0)) (Fin ((deepestM H r) (Fin.last L))) ℝ)
    ((paramsEquivFlat (deepestM H r)).symm y)
```

Changed/new structure fields:

```lean
  split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge

  /-- Raw-core to gauge-normalized-core absorption, on split coordinates.
  It may depend on the other split coordinates, but it changes only the core slot. -/
  coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge

  coreAbsorb_basepoint : coreAbsorb 0 = 0

  coreAbsorb_regular :
    ∀ q : DeepestSplit H r nGauge, (coreAbsorb q).1 = q.1

  coreAbsorb_spectator :
    ∀ q : DeepestSplit H r nGauge, (coreAbsorb q).2.2 = q.2.2

  /-- The producer's unit-Jacobian absorption theorem. -/
  coreAbsorb_rlct :
    rlctAtOn
        (fun q : DeepestSplit H r nGauge =>
          (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
        (0 : DeepestSplit H r nGauge)
      =
    rlctAtOn
        (fun q : DeepestSplit H r nGauge =>
          (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
        (0 : DeepestSplit H r nGauge)
```

Replace the core term in `loss_squeeze` by the absorbed core:

```lean
let q := split w
(∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1
```

Sub-6 skeleton:

1. MP transport by `rlctAtOn_comp_homeomorph Γ.split Γ.split_mp ...`, using `Γ.split_basepoint`, lands on split-space absorbed `Φ`.
2. Rewrite absorbed `Φ` to raw disjoint `Φ` by `Γ.coreAbsorb_rlct`.
3. Apply `rlct_additive_smooth_block` to raw `Φ`, with `G y := Real.sqrt (deepestCoreF H r y.1)`.
4. Rewrite `G y ^ 2 = deepestCoreF H r y.1`, then apply `rlctAtOn_spectator_peel`.
5. Apply sub-7 `deepest_reduced_core_identification`.

The single hard producer field is exactly `coreAbsorb_rlct`. Its intended proof is: `π := coreAbsorb`, show `rawΦ ∘ π = absorbedΦ` using `coreAbsorb_regular`, apply `weightedThreshold_transport`, then peel the bounded-unit Jacobian with `weightedThreshold_weight_unit_invariant`.