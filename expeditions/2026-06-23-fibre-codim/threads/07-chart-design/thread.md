# thread 07 — chart-build design recon (G0, scout — blueprint for the multi-tide build)

**Type:** explore (scout) · design recon. The operator committed to building the full Lemma 4.6 identity
via the rank-chart local-trivialization (a multi-module AG build). Before sinking formaliser tides into
it, **pin the decomposition and probe the hard crux (G2) for v4.29 reachability** — the same design
discipline that produced the thermometer (N=1) win and the thread-03 reframe. No production Lean required
(probe with throwaway `example` blocks if useful); output is the confirmed rung-ladder + risk map.

## The target + the known route
Core target: `codimRepCanonical (fibre d B) = cCodim d r + r(d_0+d_N−r)` for `B` rank r, r≤min d, 0<N.
LR's proof: `mult : Σ^r → Mat^{rk=r}` is a Zariski-locally-trivial fibre bundle (GL_{d_N}×GL_{d_0}
equivariant); `dim Σ̄^r = dim Mat^{rk=r} + dim(fibre)` ⟹ the shift. The rung-ladder (synthesis): G1
reduce-to-`E=diag(I_r,0)` (a separate tide, thread 08); **G2** the chart trivialization `mult⁻¹(U)∩Σ^r ≅
U × mult⁻¹(E)` (pivot chart U = top-left r×r block invertible) — the crux; **G3** dim-additivity +
Brick A min-over-components → the identity.

## Your questions to answer (the blueprint)
1. **G2 reachability.** Is the product trivialization `mult⁻¹(U)∩Σ^r ≅ U × mult⁻¹(E)` (as varieties /
   coordinate rings) formalizable at Mathlib v4.29 on the engine's `codimRepCanonical`/`varietyDim`
   (`MvPolynomial ⧸ vanishingIdeal`, `Ideal.height`) substrate? What exactly does the explicit section
   (`D = C A⁻¹ B` on the pivot chart) give, and how does it yield a **dimension** statement (product ⟹
   `dim = dim U + dim fibre`) WITHOUT a general morphism-dimension theorem? Does Mathlib have product /
   principal-open dimension lemmas that apply, or must they be built (size?)?
2. **Group-reduction vs inner-quiver route.** Compare two routes for `dim(fibre over E)`:
   (a) the chart trivialization (G2/G3 above);
   (b) the **inner-group route** — `mult⁻¹(E)` is stable under `H = (∏_{0<i<N} GL_{d_i}) × Stab(E)`;
   is `dim mult⁻¹(E)` computable via the engine's orbit/`OrbitImageDim` machinery applied to `H`, or via
   a modified quiver, sidestepping G2's product construction? (The thermometer dodged the feared build by
   an N=1 specialisation — look for the analogous shortcut.)
3. **Reducibility.** `codimRepCanonical = iInf over minimal primes`. How do the fibre's components match
   Σ̄^r's orbit-components (Brick A's `minimalPrimes_sigmaIdeal_eq`) with the `+δ`? Pin the correspondence.
4. **Rung-ladder + risk.** Confirm/revise the G1–G4 ladder; per rung: which engine/Mathlib machinery,
   NEW vs reuse, size, risk; name the single hardest sub-wall and whether it is reachable this build.

## Method
- Exact algebra (the explicit section, the pivot chart, the `(2,2,2),r=1` numerics: `dim Σ̄^1 = 7 = 3 + 4`).
- **Fire a decorrelated `local-codex-consult`** (authenticated, xhigh) on G2 reachability + the
  group-reduction-vs-inner-quiver choice; save under `threads/07-chart-design/codex/`.
- Read: `Core/MultComorphism` (F1), `Core/FibreCodim` (F2 lower bound + NO-GO write-up), `Core/SigmaCodim`
  (Brick A, minimal primes), `Core/OrbitImageDim`/`OrbitPullbackDim`/`JacobianTrdeg` (the thermometer's
  trdeg/Jacobian dim machinery), `Core/DeterminantalStratumDim` (thermometer), `Core/Orbit` (group action),
  `Core/NullstellensatzCodim` (catenary, `height_map_algEquiv`).

## Output (report to controller)
The confirmed rung-ladder (G1–G4, revised if a cleaner route exists), per-rung machinery + size + risk,
the single hardest sub-wall + its reachability verdict, the decorrelated-Codex read, and a clear
recommendation: which route for `dim(fibre over E)` (chart-trivialization vs inner-quiver), and the
order to launch the formaliser tides. **No production Lean / no commits to library files** (design only;
throwaway probes fine). In-repo notes only; never `~/.claude/**/memory/`. Don't touch other worktrees.
