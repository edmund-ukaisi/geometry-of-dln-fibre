# Thread `genm-sjjoint` — sjJointResolution staged wins (tide report + statement card)

Branch `origin/genm-sjjoint` @ `375abcf4` (off `origin/genm-sjbpeel` @ 83976c60 + merge of
`origin/genm-sjpeel-blow`). Target: the `sjJointResolution` mountain (last analytic sorry of the
general-`L` R1-UPPER `(S,J)`-peel). Design cert: `genm-sjjoint-design/cert.md`.

## What this tide BANKED (sorry-free, axiom-clean)

### 1. Merge: the isotropic box corank atom into the peel-stack lineage
`origin/genm-sjpeel-blow` carried `RouteMSJCorankResidual.lean` (the box atom
`matBox_corank_residual_le`) but it was NOT in the peel-stack lineage. Merged (one docstring conflict
in `RouteMSJResolution.lean`, resolved in favour of the CLOSED `sjBoundaryPeel` route; the stale
`genm-sjpeel-blow` note described an abandoned pointwise route). `RouteMSJResolution` builds green
(8302 jobs); `sjBoundaryPeel` still sorry-free; only `sjJointResolution` (L803) remains its sorry.

### 2. NEW: the full-space isotropic corank atom (the radial endpoint of step 2's Γ-atom)

> **Claim.** For `pq/2 < c'`, `w > 0`, the corank block `Γ` integrated over ALL of `ℝ^{p×q}` has the
> exact residual-power value `∫_{ℝ^{p×q}}(frobSq Γ + w)^{−c'} = Cresid(pq)c'·w^{−(c'−pq/2)}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.matBox_corank_residual_fullSpace_eq`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankResidual.lean` @ `375abcf4`)
> - **Gloss.** `∫⁻ Γ : Fin p → Fin q → ℝ, ofReal ((frobSq Γ + w)^(-c')) = ofReal (Cresid (p*q) c' *
>   w^(-(c' - (p*q)/2)))`.
> - **Proved.** The exact equality, via `eMatFlat` (matrix ≃ᵐ `Fin(pq)→ℝ`, MP) + `frobSq_eq_flatSum`
>   + `PiLp.volume_preserving_toLp` (`Fin(pq)→ℝ ≃ EuclideanSpace`, MP) + banked full-space radial value
>   `integral_core_full_eq`, bridged Bochner→`∫⁻` by `ofReal_integral_eq_lintegral_ofReal`.
> - **Cited/Deferred.** None. Axiom-clean `[propext, Classical.choice, Quot.sound]` (forced
>   `#print axioms`).
> - **Role.** The `R = I`, `S = 0` special case of the cert's step-2 anisotropic-shifted atom; the
>   radial core the general `∫(w+‖ΓR+S‖²)^{−c'}` reduces to after the Gram change of variables. Also
>   the exact shape step-1's *enlarge-before-shear* needs (the shear is MP only on the full space).

## The isolated GAP (NOT touched — honest, per "don't launder")

`sjJointResolution` remains a single named sorry (`RouteMSJResolution.lean:803`). Its existing docstring
is accurate: it is Aoyagi's `(S,J)` monomial/normal-form DOUBLE INDUCTION, bounded but unbuilt, NOT a
banked-piece composition (the cert's 3-decorrelated-line verdict). I did **not** launder it into a fake
reduction — doing so honestly requires steps 1–2 sorry-free, and those are mountains (below).

## Why the full 4-step reduction is a MULTI-TIDE mountain (evidence-based obstruction)

The team-lead's staged-wins framing (steps 1–4) glosses that each of steps 1–2 is itself a
multi-hundred-line NEW build, and that **even the L=0 base needs them**. Concretely:

- **Step 2 anisotropic Γ-atom — the crux is a Kronecker-determinant linear change of variables.** The
  radial endpoint is now banked (above). The remaining anisotropic content
  `∫_{ℝ^{p×q}}(w+‖ΓR+S‖²)^{−c'} = det(RRᵀ)^{−p/2}·(endpoint at w' = w+‖S(I−P_R)‖²)` needs: (a) `RRᵀ`
  symmetric-posdef → invertible square root (`R` full row-rank q, the non-bottleneck a.e. condition);
  (b) the linear cov `Γ ↦ Γ·G^{−1/2}` on `Matrix (Fin p)(Fin q)`, whose Jacobian is
  `LinearMap.det (right-mult by M) = det M ^ p` — this det (of the `M ⊗ I_p`-type operator) is the
  thrash-prone crux; Mathlib has `map_linearMap_addHaar_eq_smul_addHaar` (general linear cov) but NOT,
  as far as this tide found, the `det(right-mult on p×q matrices) = det^p` identity ready-made;
  (c) the orthogonal projection `I−P_R` and the residual `S(I−P_R)`. Each is a real sub-build; the
  assembly is multi-hundred-line and NOT a comfortable single-tide close.
- **Step 2 second branch (`c' ≤ a/2`, 94/480 charts).** Real and prevalent (`a ≥ minAdm M` ⟹ the atom
  is never applicable). Needs a separate bounded-integrand argument — but it, too, consumes the block
  split (to expose the core `w`).
- **Step 1 bridge.** The block-reindex of `A₀` (arbitrary `(ρ,κ)` → `Fin t ⊕ Fin (M₀−t)` sum-type
  blocks via complement equivs, measure-preservingly) + `frobSq_schur_block_split` pointwise rewrite +
  Fubini to isolate `D` + enlarge `box_D ⊆ ℝ^{pq}` + full-space shear `D↦Γ`
  (`measurePreserving_shearSub`). Banked pieces exist, but the sum-type-block reindex plumbing is
  itself "NEW-but-bounded" multi-hundred-line work.
- **L=0 base is NOT free.** At `L=0` the tail is a single free matrix (decoupled), but connecting
  `gammaPeelIntegral` (chart-restricted 2-matrix integral) to the banked `SchurCore`/`rrp` STILL needs
  the block split + the corank atom (the naive exponent-preserving peel `fibre_lintegral_mul_le` caps
  at `c' < M₀/2`, missing the full `c' < minAdm/2` — the R1-UPPER wall recurs). So the L=0/L≥1 split
  does NOT reduce content without the atom+bridge.
- **Step 3 outer double-induction (the true gap).** At the binding cut the residual exponent EXACTLY
  saturates the reduced-chain IH threshold (0/4000, cert), zero budget for the Gram coupling; the
  Gram divisor and reduced-core divisor share the deeper product `Z = A₂···A_{L−1}` at `L ≥ 3`. Not
  closable by any black-box shorter-chain / Hölder call — the unbuilt `(S,J)` monomial resolution.

## Recommended tide decomposition (for the controller)

1. **Atom tide** — build the anisotropic-shifted Γ-atom `∫(w+‖ΓR+S‖²)^{−c'} ≤ …` on top of the
   now-banked isotropic endpoint (`matBox_corank_residual_fullSpace_eq`). The load-bearing sub-lemma to
   build first: `det (right-mult by M on Matrix (Fin p)(Fin q)) = det M ^ p` (the cov Jacobian). Then
   posdef sqrt + projection + assembly.
2. **Bridge tide** — the block-reindex + Fubini + enlarge + shear, ending at the anisotropic atom, +
   the `c' ≤ a/2` branch. Reduces `sjJointResolution` to the outer-residual finiteness.
3. **Outer (S,J) double-induction tide(s)** — the mountain proper (Aoyagi §5 carrier); the charge-value
   half is banked (`minAdmRec_eq_minAdm`, `sjChargeUpdate_accum`, `sjSubordination`).

The isolation to a single sorry (step 4) is achievable only AFTER tides 1–2 land sorry-free; attempting
it now would be laundering.
