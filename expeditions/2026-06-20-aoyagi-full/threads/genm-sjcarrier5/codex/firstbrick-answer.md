**1. FIRST BRICK**

Bank the **supplied-equiv block-reindex transport for `gammaPeelIntegral`**, not the full `ρ,κ` complement construction.

```lean
theorem gammaPeelIntegral_blockReindex_eq
    (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1))
    (er : Fin (M 0) ≃ Fin t ⊕ Fin (M 0 - t))
    (ec : Fin (M 1) ≃ Fin t ⊕ Fin (M 1 - t))
    (her : ∀ i : Fin t, er.symm (Sum.inl i) = ρ i)
    (hec : ∀ j : Fin t, ec.symm (Sum.inl j) = κ j)
    (c' : ℝ) :
    gammaPeelIntegral M t ρ κ c'
      =
      ∫⁻ A' in paramsBoxM (tailChain M) 1,
        ∫⁻ A0 in
          ((fun A0 :
              Matrix (Fin t ⊕ Fin (M 0 - t)) (Fin t ⊕ Fin (M 1 - t)) ℝ =>
              A0.reindex er.symm ec.symm) ⁻¹' matBox (M 0) (M 1) 1
            ∩ {A0 :
                Matrix (Fin t ⊕ Fin (M 0 - t)) (Fin t ⊕ Fin (M 1 - t)) ℝ |
                IsUnit A0.toBlocks₁₁}),
          ENNReal.ofReal
            ((frobSq
                (A0 * ((prod (tailChain M) A').reindex ec (Equiv.refl _)))) ^ (-c'))
```

Why this first: it is the first integral-level bridge from the raw chart integral to the banked Schur algebra, while avoiding the highest-noise subproblem by taking `er/ec` as inputs. It unlocks the next theorem exactly: an a.e. Schur-split rewrite using `frobSq_schur_toBlocks_split`.

**2. RANK**

1. `gammaPeelIntegral_blockReindex_eq`: best value/buildability. Risk: proving the matrix reindex is MP and the Frobenius product reindex identity.
2. Per-chart Schur-split integrand rewrite: high value. Risk: extracting `[Invertible A0.toBlocks₁₁]` from restricted-domain membership under `lintegral_congr_ae`.
3. Shear `D ↦ Γ` plus block-domain/Fubini plumbing: high value. Risk: product-splitting the block box and managing the shear-image set.
4. Corank-peel→IH on full-rank `Q_b`: not first under verdict A. Risk: it drifts toward the Gram/atom route and misses rank-deficient strata.
5. Abstract `(S,J)` descent skeleton: eventual core, but too much new construction before the CoV bridge is banked.

**3. THE ρ,κ→full-equiv SUBPROBLEM**

Do not make arbitrary `ρ,κ` extension the first integral brick. The cheaper route is: prove the transport theorem with supplied `er/ec`, then instantiate later by the existing `sumSplit` pattern:

```lean
let er : Fin (M 0) ≃ Fin t ⊕ Fin (M 0 - t) :=
  (sumSplit (ρ : Fin t → Fin (M 0)) ρ.injective).symm

have her : ∀ i : Fin t, er.symm (Sum.inl i) = ρ i := by
  intro i
  simpa [er] using sumSplit_inl (ρ : Fin t → Fin (M 0)) ρ.injective i
```

Same for `κ`. The relevant ingredients are `Equiv.ofInjective`, `Fintype.equivOfCardEq`, `Fintype.card_compl_set`, `Equiv.Set.sumCompl`, and the already banked `sumSplit_inl`. Fully avoiding complements is not realistic: Schur blocks and the corank atom need the non-pivot block as an actual index type.

**4. CLOSE-IN-ONE-TIDE?**

No. Closing `sjJointResolution` end-to-end this tide is not realistic. Correct call: bank brick #1 and report.

Ordered multi-tide sequence:

1. `gammaPeelIntegral_blockReindex_eq`.
2. `ρ,κ` wrapper using `sumSplit`.
3. Schur-split integrand rewrite on the reindexed chart.
4. Block Fubini plus `measurePreserving_shearSub`.
5. Pure R-blowup corank peel wired to charge update and `redChain` IH.
6. `(S,J)` descent assembly into `sjJointResolution`, then `SJStepHyp`.