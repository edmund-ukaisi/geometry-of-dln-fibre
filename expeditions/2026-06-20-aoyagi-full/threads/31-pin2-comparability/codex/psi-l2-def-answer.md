1. **Use correction cutoff.** Define the cutoff map as `q + χ q • (psiSplitRawL2 q - q)`, not primarily as `(1 - χ q) • q + χ q • psiSplitRawL2 q`; they are algebraically equal, but the correction form matches your banked `χ • raw` smoothness lemma and makes “derivative = id” reduce to “correction has derivative 0”.

```lean
def psiSplitDeltaL2 q := psiSplitRawL2 q - q

def psiSplitCutL2 q :=
  q + (χ q : ℝ) • psiSplitDeltaL2 q

def psiL2 w :=
  split.symm (psiSplitCutL2 (split w))
```

Keep `psiSplitRawL2` as the honest formula for S6, then prove `psiSplitCutL2 =ᶠ[𝓝 0] psiSplitRawL2` from `χ = 1` near `0`.

2. **Build a fresh full `DeepestSplit` bump.** Do not try to use `cutoffBump ∘ (fun q => (q.1, q.2.2))` as a `ContDiffBump`: its support is cylindrical in the core direction, so it will not have the shape Mathlib’s `ContDiffBump` API expects. Recommended shape:

```lean
def rsProj (q : DeepestSplit H r _) := (q.1, q.2.2)

def jointUnitSetFull : Set (DeepestSplit H r _) :=
  {q | rsProj q ∈ jointUnitSet H r hr hL} -- include A₀,A₁,W,P00 denominators

noncomputable def psiBumpFull : ContDiffBump (0 : DeepestSplit H r _) where
  rIn := ε / 4
  rOut := ε / 2
  ...
```

Choose `ε` using openness of `rsProj ⁻¹' jointUnitSet` at `0`, so `tsupport χ ⊆ jointUnitSetFull`. TRAP: the existing `unitSet` for per-layer `I + readX` is not enough if `W⁻¹` or `⅟P00` has its own determinant condition.

3. **The little-o route is viable but probably not the cleanest Lean route.** For ordinary derivatives, `correction = o(‖q‖)` is exactly the right analytic statement; for strict derivatives you need the corresponding strict/two-point form, and the exact Mathlib bridge lemma availability is something I’d treat as [infer]. A more Lean-friendly path is componentwise strict differentiability: prove each matrix-entry correction has strict derivative `0` by product rules, using that products with at least two vanishing factors kill all first-order terms. Use smoothness of inverse entries on the support/open unit set, but do not need their derivative to be zero. TRAP: `readX`, `readY`, `readZ`, and core reads are linear projections, so their derivative is not zero; only products such as `Z * A⁻¹ * Y`, `K*S1`, etc. lose first order.

4. **S3, S2, and S4 can all land before S6.** Build order I’d use: define `psiSplitRawL2`, `psiSplitDeltaL2`, full bump `χ`, `psiSplitCutL2`, then `psiL2`; prove support and near-zero `χ = 1`; prove S3 fixpoint; prove raw `ContDiffAt` on the support and then S2 via `contDiff_contDiffBump_smul`; prove S4 from `D psiSplitDeltaL2 0 = 0` and conjugate through `split`. S6 should consume only the near-zero equality `psiSplitCutL2 = psiSplitRawL2`, so it can be delayed without blocking the diffeo-side lemmas.

5. **No structural red flag.** The route is sound in shape: raw rational formula locally, correction cutoff globally, affine split conjugation, and eventual equality for the composition identity. The main risks are Lean-engineering risks: determinant support too small, treating projected bump as a full `ContDiffBump`, or accidentally proving derivative-zero for reads instead of for higher-order products. A simpler Ψ may exist algebraically, but I would not discard the certified formula; at most define the deltas directly to make S4 cleaner while keeping the certified `T1'`, `Y1'` formulas for S6 traceability.

**GO** on the proposed def, with the adjustment: define the cutoff as `q + χ • (Ψ_split q - q)` using a fresh full-`DeepestSplit` bump.