<task>
Lean 4 + Mathlib v4.29 formalisation. I am building the change-of-variables (CoV)
bridge to close a named `sorry` in an Aoyagi-style RLCT box-finiteness proof. This
is an explicitly MULTI-TIDE mountain (a design adjudication estimates ~65-75% new
construction). I need you to pick the SINGLE highest-value, LOWEST-BUILD-RISK first
integral-level brick to bank this tide, and give its exact Lean statement shape.

## The named target (do NOT try to close it this tide; help me pick the first brick)

    theorem sjJointResolution (M : Fin (L+1+1+1) → ℕ)
        (hIH : ∀ M' : Fin (L+1+1) → ℕ, RouteMBoxThresholdFinite M')
        (t : ℕ) (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1))
        (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1)) (c' : NNReal)
        (hc' : (c':ℝ) < (minAdm M:ℝ)/2) :
        gammaPeelIntegral M t ρ κ (c':ℝ) < ⊤

where

    gammaPeelIntegral M t ρ κ c' =
      ∫⁻ A' in paramsBoxM (tailChain M) 1,          -- outer: tail-chain params box
        ∫⁻ A0 in matBox (M 0) (M 1) 1 ∩ pivotChart ρ κ,   -- inner: front factor, chart
          ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c'))

- `A0 : Fin (M 0) → Fin (M 1) → ℝ` (front layer), `Q := prod (tailChain M) A' :
  Fin (M 1) → Fin (M_L) → ℝ` (product of the remaining L+1 layers).
- `pivotChart ρ κ = {A0 | IsUnit (A0.submatrix ρ κ)}` : the (ρ,κ) t×t minor is invertible.
- `rmatMul` is raw matrix mult; `frobSq X = ∑ᵢⱼ Xᵢⱼ²`.
- `RouteMBoxThresholdFinite M' := ∀ c'' : NNReal, (c'':ℝ) < minAdm M'/2 →
    routeMLayerBoxIntegral M' c'' 1 < ⊤` (the box integral of `frobSq(prod M' ·)^{-c''}`).
- `minAdm` is the combinatorial charge (banked recursion `= minAdmRec`); `peelExp M t =
  (M₀−t)(M₁−t)` is the corank-block codim.

## The DESIGN route (adjudicated, verdict A, "pure R-BLOWUP"; do NOT deviate)

On the chart, reindex `A0` to `fromBlocks A B C D` over `Fin t ⊕ Fin(M₀−t)` rows and
`Fin t ⊕ Fin(M₁−t)` cols with `A` the invertible pivot. Schur block split (BANKED,
`frobSq_schur_block_split`):

    frobSq(A0·Q) = frobSq(A·Q̃_p) + frobSq(C·Q̃_p + Γ·Q_b),
    Q̃_p = Q_p + A⁻¹B·Q_b,  Γ = D − C A⁻¹ B  (corank block, (M₀−t)×(M₁−t)),
    Q_p/Q_b = pivot/non-pivot column rows of Q.

Then the MP shear D↦Γ (BANKED `measurePreserving_shearSub`) frees Γ. The corank block
is peeled by a single radial (charge = peelExp), the pivot block A is a Morse direction,
and the coupling reduces to the chain `redChain t M = (t, M₂,…,M_L)` (arity L+2), which
the IH `hIH` covers. Do NOT integrate Γ out against Q_b as a Gram determinant
`det(Q_bQ_bᵀ)^{-p/2}` (the "atom route" — walls on the Q_b rank-deficient / degenerate
strata; this is the res-of-singularities trap the adjudication forbids).

## What is BANKED (reuse; sorry-free, axiom-clean)

- POINTWISE: `frobSq_schur_block_split`, `corankStep` (`frobSq((u•fromBlocks A B C D)·Q)
  = u²·(frobSq(A·Q̃_p)+frobSq(C·Q̃_p+Γ·Q_b))`), `corankStep_prefactor`.
- PIVOT CHART: `pivotLocus_eq_iUnion` (`{t≤rank}=⋃_{ρκ} pivotChart`), `schur_cov`,
  `schur_cov_toBlocks`, `pivotBlock_reindex_eq_submatrix` (top-left block of `A0.reindex
  e₀ e₁` = the (e₀,e₁) minor), `measurePreserving_shearSub` (block shear (x,D)↦(x,D−Kx)).
- CORANK INTEGRAL: `matBox_corank_dominates_absZ_lt_top` (∫_z∫_{Δ∈matBox p q T}
  (frobSq Δ + W z)^{-c'} < ⊤ for c'<pq/2, W≥0, μZ<∞ — Δ enters ISOTROPICALLY via frobSq Δ);
  `matBox_corank_residual_absZ_le` (c'>pq/2, W>0: ≤ Cresid·∫_z (W z)^{-(c'−pq/2)});
  `corankBlock_morsePeel_lt_top` (anisotropic frobSq(Ccross+Γ·Qb), needs Q_bQ_bᵀ PosDef).
- TERMINAL: `sjLoss_terminal_lintegral_lt_top` (∫_{unitBox} (∑bᵢ²)^{-c'}·∏|u_ℓ|^{h_ℓ} < ⊤
  below the monomial threshold, given a dehomogenised generator).
- CARRIER: `SJLinGenState` (supp + linear coeff), `loss_ofMatrix_product`
  (frobSq(A0·Q) = carrier loss of `ofMatrix`), `loss_radialStep`, `gen_rowMix_const`.
- Matrix→flat MP: `eMatFlat p q : (Fin p→Fin q→ℝ) ≃ᵐ (Fin (p*q)→ℝ)`, MP; frobSq↔∑sq.
- MP vector split by a partition/coreSet: `splitOfPartition`, `splitOfCoreSet`
  (`(Fin a ⊕ Fin b ⊕ Fin c) ≃ Fin N`, MP).

## What is MISSING (the gap; no banked lemma does this)

The integral-level CoV connecting `gammaPeelIntegral`'s raw matrix-box `∫⁻` to the
banked bricks. In particular: (1) a MEASURE-PRESERVING block-reindex of the inner `A0`
box `matBox M₀ M₁ 1 ∩ pivotChart ρ κ` into `fromBlocks A B C D` coordinates over
`Fin t ⊕ Fin(M₀−t)` / `Fin t ⊕ Fin(M₁−t)` (extending the ARBITRARY embeddings ρ,κ to
full equivs); (2) per-chart transport applying the Schur split + shear; (3) the
corank-block peel wired to the IH; (4) the descent/assembly.

## Constraints / risks (Lean-idiom, from the repo's own notes)

- Opaque/dependent widths (`Fin (M₀−t)` etc.) make `Matrix.mul_apply`/`reindex`/`simp`
  fire in isolation but "no progress" in-context; the working pattern is fully-applied
  terms + `have`+`exact` at explicit indices. Reindex-extending-arbitrary-ρκ to a full
  `Fin m ≃ Fin t ⊕ Fin (m−t)` is fiddly (complement embedding + `Fintype.card` equiv +
  `Nat.sub` arithmetic). This is the SIZE risk, not a math wall.
- Zero sorry/axiom/native_decide in committed files; must stay axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).

<output_contract>
Four sections, terse, decision-grade:

1. FIRST BRICK. Name the single highest-value, lowest-build-risk integral-level brick
   to bank THIS tide (one of: block-reindex MP equiv; per-chart Schur-split integrand
   rewrite; the corank-peel→IH wiring for the FULL-RANK-Q_b slice; the abstract (S,J)
   descent skeleton; or something better). Give its exact Lean theorem SIGNATURE
   (statement only) at the real opaque widths. Justify why it is both load-bearing and
   low-risk, and what later tides it unblocks.

2. RANK the 3-4 candidate bricks by (value × buildability), one line each, with the
   single dominant build-risk of each.

3. THE ρ,κ→full-equiv SUBPROBLEM. Is extending arbitrary `ρ : Fin t ↪ Fin m` to a
   measure-preserving block-reindex `Fin m ≃ Fin t ⊕ Fin (m−t)` the right first move, or
   is there a lower-risk route that AVOIDS building the complement equiv (e.g. keep A0
   un-reindexed and phrase the Schur split via submatrices at ρ,κ directly; or reindex
   Q's rows only)? Give the concrete cheaper route if one exists, with the Mathlib
   lemma names it would use.

4. CLOSE-IN-ONE-TIDE? Is closing `sjJointResolution` end-to-end this tide realistic, or
   is honest-partial (bank brick #1 + report) the correct call? If multi-tide, give the
   ordered brick sequence (3-6 bricks) so successive tides compose.
</output_contract>
