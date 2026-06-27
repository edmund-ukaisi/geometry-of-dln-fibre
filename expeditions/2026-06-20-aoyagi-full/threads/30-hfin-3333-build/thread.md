# Thread 30 — `(3,3,3,3)` hdiv instance (the decisive multi-pivot LDU+chaining node)

R1 hdiv: the `(3,3,3,3)` instance of `NodeAchieverChart` + the box-divergence atom, on the banked
bundle (`NodeAchieverChart.lean` + the `RouteM4422.lean` template) and the closed-form φ_M certificate
(`threads/26-r1-genM-chart/ §Uniform closed form`). The decisive multi-pivot validation: nonzero
intermediate codims (descent `T* = (2,1,0)`, block codims `1,2,3`), the LDU-core + `B/C`-chaining chart,
NOT just `(4,4,2,2)`'s pure radial blow-up.

File: `lean/DLNFibre/DLN/RLCT/Validate/RouteM3333.lean`.

## What is built (green, sorry-free)

The chart `phi3333 = paramsEquivFlat M3333 ∘ chartParams3333`, `chartParams3333 = (A, B, C)` the three
`3×3` layers of Codex's verified frame (slot map: `x 0=u`, `x 1..8=a,α,γ,δ,λ₁,λ₂,m₁,m₂`,
`x 9..14=b,ℓ,n₁,n₂,η₁,η₂`, `x 15..17=r`, `x 18..23=h₁,h₂`, `x 24..26=ζ`):

    A = [[I₂];[λ]]·K·[I₂|m] + u·E₂₂,  K = !![a, aα; γa, γaα+δ]   (the LDU rank-1+residual core)
    B = [[D − m·r];[r]],  D = [[1];[ℓ]]·b·[1,n₁,n₂] + u·Y,  Y = !![0,0,0; 0,η₁,η₂]
    C = [[u·ζ − n₁·h₁ − n₂·h₂];[h₁];[h₂]]

Proven lemmas (all sorry-free; reviewed SURVIVED, see below):

- `minAdm_M3333 = 6`, `flatDim/routeMAmbient M3333 = 27`. Threshold `½·minAdm = 3`.
- `dlnLoss_chartParams3333 : dlnLoss M3333 0 (chartParams3333 x) = (x 0)² · Vval3333 x` — the
  soundness-critical `F = u²·V` identity (the telescoping `A·B·C = (x 0)·H`, `Hval3333 = (A·B·C)/x₀`,
  `Vval3333 = ‖H‖²` a genuine polynomial, NOT a pure unit — the multi-pivot shape). Proven via 9
  literal-index per-entry `ring` identities (`prod_chartParams3333_entry_ij`) dispatched by `fin_cases`.
- `routeMCore_phi3333 : routeMCore M3333 (phi3333 x) = (x 0)² · Vval3333 x`.
- `Vval3333_ae_pos : ∀ᵐ x, 0 < Vval3333 x` — the genuine-polynomial null-zero-set route
  (`VPoly3333 ≠ 0` at the witness `x 1 = x 9 = x 24 = 1` (a=b=ζ₀=1) where `V = 1`;
  `MvPolynomial.ae_eval_ne_zero`). `Vval3333_le_on_box` (bounded above on `[0,δ]²⁷`).
- `leafH3333 = (5 on axis 0, 4 on axis 1, 2 on axis 4, 3 on axis 9, else 0)` — the EXACT 27×27 Jacobian
  det exponents `u⁵·a⁴·δ²·b³` (u-exp `5 = minAdm − 1`; the LDU/chaining pivots `a, δ, b` as `k = 0`
  spectators). `leafH3333_pivot`, `leafH3333_prod_eq`, `leaf_integrand3333`.
- `continuous_phi3333`, `phi3333_zero` (reaches the deepest point), `phi3333_image_subset_cubeBox`.

## The det soundness check (the degenerate-chart guard)

`|det Dφ3333| = ∏_j |u j|^{leafH3333 j} = |u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³` — VERIFIED two ways:
- sympy `threads/26-r1-genM-chart/scripts/verify_codex_3333.py`: det = `u⁵·a⁴·δ²·b³`, u-exp 5 = minAdm−1,
  27 inputs = flatDim, det ≠ 0 off `{u=0}` (generic `a, δ, b`).
- the reviewer independently re-derived the 27×27 Jacobian det = `x0⁵·x1⁴·x4²·x9³` matching `leafH3333`.

VERIFIED block-triangular ORDERING (the Lean-provable route for the cov field): 9 identity blocks (det
1) + z-block `u·I₃` (u³) + η-block `u·I₂` (u²) + b-block lower-tri diag `(1,b,b,b)` (b³) + the A-block
9×9 (det `a⁴·δ²`, the LDU off-diagonal — the one non-triangular sub-piece). Product = `u⁵·a⁴·δ²·b³`.

## The Jacobian infrastructure (banked green, sorry-free) + the Frame-det wall

Beyond the core, the full Jacobian/composition machinery is banked green (the reusable bricks toward the
general closed-φ_M chaining det):

- `pack3333` + `pack3333CLM` + `fin27EquivFlatIdx3333` + `measurePreserving_pack3333` +
  `measurePreserving_Q3333CLM` + `Q3333CLM_abs_det = 1` (the outer reshape, measure-preserving, via the
  banked `ParamsReshapeMP`).
- `T3333` (the flat structural chart map) + `chartParams3333_eq_pack_T` + `T3333Deriv` (explicit 27×27
  fderiv CLM) + `T3333_hasFDerivAt` (the full chain-rule `HasFDerivAt` — the hard analytic piece).
- The **composition decomposition** `T3333 = Frame3333 ∘ Kparam3333` (`Frame3333_Kparam3333` proven) +
  `Kparam3333Deriv` / `Frame3333Deriv` + their `HasFDerivAt` + **`Kparam3333Deriv_det = (x 1)²`** (PROVEN
  via the abstract-entry `BlockTriangular` pattern — the proof-of-concept that the timeout-free det idiom
  works).

**The Frame-det wall (the one remaining gap).** `Frame3333Deriv_det = x0⁵·x1²·x4²·x9³` did NOT land — a
Lean elaboration COST-ACCUMULATION wall (not a math gap; det fully certified). The abstract-entry
`BlockTriangular` pattern WORKS (Kparam det landed), but Frame's `BlockTriangular.det` reduces to 25
block-values where the two 2×2 K/Kᵀ blocks each need a subtype-`{i // blk i = v} ≃ Fin 2` reindex before
`Matrix.det_fin_two` fires (×2), plus 25-fold `prod_insert` image bookkeeping, on top of an
already-heavy combined file (the 4M-heartbeat Kparam det + the 2×27-row `HasFDerivAt`). The per-cycle
elaboration cost of the combined file exceeds a tractable build. **Fix (roadmapped):** a dedicated small
file with JUST `Frame3333Deriv` + its det (escapes the per-cycle cost), then `phi3333_abs_det`,
`phi3333_injOn` (off the 4-hyperplane locus), `phi3333_cov` (4-puncture + 3 null slices, mirror
`phi334`), `nodeChart3333`, the atom.

### Det-tactic lesson (banked for the redo + the general closed-φ_M chaining)

The timeout-free det idiom (the `pivotBlowupOnDeriv_det` pattern, `Foundations/S1G5Charts.lean`):
- Factor the map: `det(T) = ∏ det(factor)` via `LinearMap.det_comp` (NEVER a single n×n
  `Matrix.mul_apply` product identity — the 729-entry A·B·C product blew 2M heartbeats).
- Per factor: `rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']`, entry
  `M i j = (Deriv)(Pi.single j 1) i`, then `BlockTriangular` proven by `fin_cases i` on the ROW INDEX
  ONLY (27 cases, NOT 729) with `simp only [Deriv, pi_apply, add/smul/proj_apply, Pi.single_apply,
  smul_eq_mul, Fin.ext_iff, Fin.val_zero, Fin.val_one] <;> split_ifs <;> first | rfl | (exfalso; omega)
  | ring_nf`. NEVER unfold to `![…]`.
- Diagonal product: `Finset.prod_congr` to an explicit `![…]` of diagonal entries, then
  `Fin.prod_univ_succ` + `ring`.
- CRUCIAL: define the fderiv CLM with EXPLICIT literal `match ⟨k,_⟩ =>` patterns for all rows (a
  catch-all `| i => P i` whnf-times-out).

## Status

- Core (chart + `F = u²·V` + `V > 0` a.e. + `V` bounded + leaf-integrand + leafH + continuity + image
  containment): **green, sorry-free, reviewed SURVIVED** (fidelity + soundness; the det re-derived).
- Jacobian infra (reshape MP + `T3333_hasFDerivAt` + the composition decomposition +
  `Kparam3333Deriv_det`): **green, sorry-free**.
- `Frame3333Deriv_det` → `phi3333_cov` → `NodeAchieverChart M3333` instance → atom
  `routeMCore_box_diverges_achiever_3333`: **NOT landed** — the Frame-det elaboration-cost wall;
  roadmapped to a dedicated small file. Det fully certified (sympy + reviewer 27×27 re-derivation);
  purely a Lean tactic-cost problem on an OPTIONAL validation instance.

The bundle + assembly are already banked (via `RouteM4422`); `(3,3,3,3)` is the OPTIONAL multi-pivot
validation. NOT closing the general-M atom (needs the general chaining ∀ M). One citation:
`monomial_rlct` (S2, via the assembly).
