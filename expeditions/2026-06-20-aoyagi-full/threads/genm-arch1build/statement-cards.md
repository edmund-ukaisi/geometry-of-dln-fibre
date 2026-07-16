# genm-arch1build — statement cards

Branch `genm-arch1build` off `origin/genm-deepatlas` @323f40776. ARCH-1 mint-path prerequisites for
`deeperFlag_shell_le` via the coupled-incidence route. Each card: the informal claim, the Lean signature,
the English gloss, the load-bearing hypotheses, status.

---

## Card 1 — `deepFactor_rank_ge_deepTailMin_ae` (hZrank, rankgen route (c))

**Claim.** The generic rank of the deep-tail matrix product equals the minimum intermediate width: for a.e.
reduced parameter `z`, `rank (deeperFlagZdeep M u z) ≥ deepTailMin M`.

**Lean** (`RouteMSJDeepRankGen.lean`):
```
theorem deepFactor_rank_ge_deepTailMin_ae (M : Fin (L+1+1+1) → ℕ) (u : ℕ) :
    ∀ᵐ z ∂(volume : Measure (Params (redChain u M))),
      deepTailMin M ≤ (deeperFlagZdeep M u z).rank
```
**Gloss.** `deeperFlagZdeep M u z = prod (dropHead (redChain u M)) ((paramsHeadSplit … z).2)` is the product
of the deep-tail layers of widths `(M₂,…,M_last)`; its generic rank is `deepTailMin M = min(M₂,…,M_last)`.
**Hypotheses.** None beyond the chain shape (full-measure statement over `z`).
**Underlying general lemma.** `prod_minor_rank_ge_ae {N} (H : Fin (N+1)→ℕ) (ρ) (hρ : ∀ i, ρ ≤ H i) :
∀ᵐ A ∂vol, ρ ≤ (prod H A).rank` — generic rank of a chain product = min width (reusable, network-free).
**Method.** rectangular-identity witness ⟹ nonzero top-left `ρ×ρ` minor polynomial ⟹
`MvPolynomial.ae_eval_ne_zero` + `measurePreserving_paramsEquivFlat` ⟹ `rank ≥ ρ`; transfer along the
measure-preserving head split + `Prod.snd`.
**Status.** Proved sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Card 2 — `deepFactor_hZrank_of_le` (the `hGae_from_deepRank` input)

**Lean:**
```
theorem deepFactor_hZrank_of_le (M) (u) (hb : M 1 - u ≤ deepTailMin M) :
    ∀ᵐ z ∂(volume.restrict (paramsBoxM (redChain u M) 1)),
      M 1 - u ≤ (deeperFlagZdeep M u z).rank
```
**Gloss.** Restricts Card 1 to the box and monotonises with the caller's binding-cut Nat fact
`M₁−u ≤ deepTailMin M` (from `tailWidth_le_deepTailMin_of_binding`). Feeds `hGae_from_deepRank` (banked),
which produces exactly `shellSpine_le_frontCharge`'s `hGae`. **Status.** Sorry-free, axiom-clean.

---

## Card 3 — `deepFactor_hEtopae` (the pivot-energy a.e.-positivity, `shellSpine_le_frontCharge`'s `hEtopae`)

**Claim.** The pivot energy `E_top = frobSq(P·Q̃ₚ)` is `> 0` a.e. in the front block `x` on `outerDom`, a.e.
in `p`.

**Lean** (`RouteMSJPivotEnergyPos.lean`):
```
theorem deepFactor_hEtopae (M : Fin (L+1+1+1) → ℕ) (t j : ℕ) (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i) :
    ∀ᵐ p ∂(volume.restrict (paramsBoxM (redChain (t+j) M) 1 ×ˢ matBox (M 1-(t+j)) (M 2) 1)),
      ∀ᵐ x ∂(volume.restrict (outerDom (t+j) (M 0-(t+j)) (M 1-(t+j)) 1)),
        0 < frobSq (Matrix.of x.1.1 * ((hsQ M (t+j) (deeperFlagZdeep M (t+j)) p.1 p.2).submatrix Sum.inl id
          + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2
              * (hsQ M (t+j) (deeperFlagZdeep M (t+j)) p.1 p.2).submatrix Sum.inr id))
```
**Gloss.** Matches `shellSpine_le_frontCharge`'s second a.e. hypothesis verbatim (same measures + `E_top`).
**Hypotheses.** `1 ≤ t` (so `u = t+j ≥ 1`), `∀ i, 1 ≤ M i` (so `prod (redChain u M) z ≠ 0` a.e., i.e.
`Q_p ≠ 0`).
**Underlying general lemma.** `frobSq_stack_pos_ae {u a b n} (hu : 1 ≤ u) (Qp Qb) (hQp : Qp ≠ 0) :
∀ᵐ x ∂vol(SJOuter u a b), 0 < frobSq (of x.1.1 * Qp + of x.1.2 * Qb)` (reusable).
**Method.** `Q_p ≠ 0` (corePoly nonvanishing) ⟹ a nonzero entry of `[P|B₁₂]·hsQ` at `(0,k₀)` is a nonzero
linear form in `P`'s row 0 ⟹ `ae_matrix_eval_ne_zero`; Fubini in `(P,B₁₂,C)` via
`quasiMeasurePreserving_fst` + `measurePreserving_swap` + `ae_prod_iff_ae_ae`; `pivotEnergy_stack_eq` gives
the `P⁻¹`-form on `outerDom` (`IsUnit P`).
**Status.** Proved sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

**Net.** Both a.e.-genericity inputs of `shellSpine_le_frontCharge` are dischargeable, so the step-1+2
reduction `shellSpineIntegrand ≤ ∫_p frontChargeIntegrand` is a fully-dischargeable domino (given the good
binding-cut scope). The remaining gap to `deeperFlag_shell_le` is Brick A (the domination to the
comparator).
