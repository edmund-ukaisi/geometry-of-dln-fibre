# Statement card — R1-UPPER `(S,J)` peel, Piece 3 (split A): the Γ-explicit reduction

**Tide:** `genm-sjpeel-p3` (branch `origin/genm-sjpeel-p3`). **File:**
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJResolution.lean`. **Base:** `origin/expedition/aoyagi-full`
@ `da6d88dd`.

## What this tide delivered

1. **Def-refinement (the requested skeleton change).** Replaced `jointPeelIntegral`'s collapsed
   `P_tail^{−(c'−a/2)}·P_full^{−a/2}` by the **Γ-EXPLICIT** per-step object, keeping the corank block
   `Γ` an integration variable:

   > **Def.** `gammaPeelIntegral M t c' = ∫_{A'∈paramsBoxM(tailChain M) 1} ∫_{Γ∈matBox(M₀−t)(M₁−t) 1}
   >   (frobSqTopRows t (prod (tailChain M) A') + frobSq(Γ · gammaTailRows t (prod (tailChain M) A')))^{−c'}`.
   >
   > - **Lean:** `DLNFibre.DLN.RLCT.gammaPeelIntegral` (+ helper `gammaTailRows`).
   > - **Gloss.** Over the tail parameters `A'` and the corank block `Γ`, the integrand is
   >   `(P_tail + ‖Γ·Q_b‖²)^{−c'}` at the UNSHIFTED exponent `−c'`; `P_tail = ‖top t rows of Q‖²`,
   >   `Q_b = bottom (M₁−t) rows of Q`, `Q = prod (tailChain M) A'`. The exponent shift + Gram
   >   determinant emerge only from the inner `Γ`-integral (the finiteness content), not the def.
   > - **Why.** Design-cert ADDENDUM 3: the honest per-chart residual is a Gram determinant
   >   (anisotropic in `Q_b`), NOT `P_full^{−a/2}`; the reduction must keep `Γ` explicit (both
   >   pointwise routes are proven dead).

   `sjBoundaryPeel` re-threaded to conclude `box ≤ ∑_t C · gammaPeelIntegral M t c'`;
   `sjJointResolution` re-threaded to `gammaPeelIntegral M t c' < ⊤`; `sjResolutionStep_proof` and the
   sorry-free wrapper `routeMBoxThresholdFinite_of_step` compose unchanged.

2. **Sub-lemma 1 — the finite pivot-chart cover subadditivity (CLOSED, clean-three).**

   > **Claim.** For any `f : Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞`,
   >   `∫_{A ∈ {rank ≥ t}} f ≤ ∑_{ρ:Fin t↪Fin m} ∑_{κ:Fin t↪Fin n} ∫_{A ∈ pivotChart ρ κ} f`.
   >
   > - **Lean:** `DLNFibre.DLN.RLCT.pivotChartCover_lintegral_le_sum`.
   > - **Proved.** Banked `pivotLocus_eq_iUnion` (`{rank≥t} = ⋃ charts`, over a field) + countable
   >   subadditivity `lintegral_iUnion_le` + `tsum_fintype` (embedding types finite). No disjointness.
   > - **Status.** sorry-free, `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
   > - Support: a `noncomputable instance MeasureSpace (Matrix (Fin m) (Fin n) ℝ)` (defeq to the Pi
   >   volume; no prior instance in the codebase; full `DLNFibre` green-gated).

## Recalibration — the tide's core premise was refuted (KNOWING DECISION for the controller)

The tide brief scoped Piece 3 as "pure plumbing on banked pieces; atom-free" with all 4 sub-lemmas
"clean-three" and `box ≤ ∑ gammaPeelIntegral` sorry-free. **That is not achievable.** Block algebra +
decorrelated Codex xhigh (`codex/piece3-reachability-{prompt,answer}.md`) both return:

- **Sub-lemma 2 (`schurShear_chart_lintegral`) is FALSE as an exact identity.** After the Jacobian-1
  shear `D ↦ Γ = D − C A⁻¹ B`, the EXACT integrand is `(‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{−c'}`,
  `Q̃_p := Q_p + A⁻¹B·Q_b` — NOT `(P_tail + ‖Γ·Q_b‖²)^{−c'}` (the top block carries the invertible-but-
  near-singular `A`; the bottom retains the `C·Q̃_p` cross term). The banked `schur_cov` gives Schur
  block algebra + a unit-Jacobian reparametrisation; it does NOT preserve the Frobenius norm.
- **Sub-lemma 3 (`chartRadialBlock_to_gammaPeel`) is IRREDUCIBLE analytic, not plumbing.** The step to
  `C_κ · gammaPeelIntegral` integrates a NEGATIVE power over the pivot variables `(A,B,C)`; since
  `frobSq(A₀·Q)` vanishes on a positive-codim `(A,B,C)`-locus there is NO uniform pointwise lower bound,
  and the `(A,B,C)`-integration genuinely SHIFTS the exponent `c' ↦ c'−½(M₀−t)(M₁−t)` (radial blow-up /
  Beta), with a Gram-determinant residual. It is even *false* without the shift (`∫_{[-1,1]}|aQ|^{−2c'}`
  diverges for `c'≥½` while the Γ-free target is finite). The design cert's own ADDENDUM-3
  "LOAD-BEARING" tags + "Gram determinant" finding corroborate this; the brief's "banked plumbing"
  relabel was over-optimistic.

**Net.** Sub-lemmas 2/3 are the mountain's pieces 4/5/7 analytic core, not this tide's. `sjBoundaryPeel`
(`box ≤ ∑ gammaPeelIntegral`) stays a NAMED sorry whose residual is precisely that per-chart Γ-bound.

## Remaining sorries in `RouteMSJResolution` (exactly two, both LOAD-BEARING analytic)

- `sjBoundaryPeel` — the per-chart Γ-bound (the exact-post-shear integrand → `gammaPeelIntegral` via the
  radial blow-up / Beta / Gram; NOT plumbing). Its OUTER front-split + the finite pivot-chart cover are
  CLOSED.
- `sjJointResolution` — `gammaPeelIntegral M t c' < ⊤` (the inner Γ-box Gram c.o.v. via the banked
  `matBox_corank_residual_le`, then the `(S,J)` outer resolution + charge budget).

`routeMBoxThresholdFinite_sjResolution` carries `sorryAx` via exactly these two (`#print axioms`
confirmed, force-fresh). Everything else in the file — the wrapper, `sjBase1_freeMatrix`, piece-6 charge
budget, the front-split, and `pivotChartCover_lintegral_le_sum` — is clean-three.

## Next (pieces 5–7, the analytic core; later tides)

Discharge `gammaPeelIntegral`'s finiteness: inner Γ-box Gram change of variables `Γ ↦ Γ·Q_b`
(Jacobian `det(Q_b Q_bᵀ)^{(M₀−t)/2}`) + the banked isotropic corank atom `matBox_corank_residual_le`
(`origin/genm-sjpeel-blow`), a.e. in `A'` (the `{det(Q_b Q_bᵀ)=0}`, `{P_tail=0}` loci null), then the
`(S,J)` charge-budget recursion. The one risk (design-cert `r1u_qb_rank.py`): 750/5440 charts force
`Q_b` rank-deficient (`M₁−t > min(deeper widths)`) → the chart recurses (the `(S,J)` coupling).
