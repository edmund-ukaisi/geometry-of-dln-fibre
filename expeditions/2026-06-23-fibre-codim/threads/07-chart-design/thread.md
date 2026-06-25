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

---

## G0 RECON FINDINGS (scout, 2026-06-23)

### Numerics (anchor, all confirmed exact)
`(2,2,2), r=1`: D=8; `dim Σ̄^1 = 7`; `δ = r(d_0+d_N−r) = 3`; `dim Mat^{rk=1} = 3` (thermometer);
`dim fibre(E) = 4`; `codim fibre = 4 = C(1) + δ(3)`. Chart additivity `7 = 3 + 4` ✓.

### Substrate read (engine, all landed/sorry-free, v4.29)
- `varietyDim Z := (ringKrullDim (MvPol ⧸ vanishingIdeal(coord''Z))).unbotD 0` — reads the **Zariski
  closure** dimension, NOT an open chart's coordinate ring.
- Catenary bridge `codimRep + varietyDim = card` for IRREDUCIBLE `Z` (`vanishingIdeal` prime), additive,
  no flatness (`codimRep_add_varietyDim_eq_card`).
- Affine-domain equidimensionality (no flatness): `height p + dim(A⧸p) = dim A`
  (`affine_domain_height_add_ringKrullDim_quotient_eq`).
- Brick A `codim Σ̄^r = cCodim` general r; minimal primes of `sigmaIdeal` = maximal orbit closures
  (`minimalPrimes_sigmaIdeal_eq`).
- F1 comorphism `multComap`, fibre ideal `= Ideal.map multComap m_B`, globally (CommRing).
- Going-down height-additivity `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` PRESENT in
  Mathlib v4.29 (pinned in `FlatTrivialProductProbe`); flat ⟹ HasGoingDown is an instance.
- Polynomial-extension dim `R[X]: dim = dim R + 1` PRESENT (`ringKrullDim_of_isNoetherianRing`).
- **MISSING in Mathlib v4.29 (verified by grep over KrullDimension/):** any `Localization.Away`
  Krull-dimension-preservation lemma; any tensor-product Krull-dim additivity.

### Codex (xhigh, decorrelated) — convergent + two sharpenings
1. **G2 = real infra build, NOT a chart one-liner.** Schur section gives a genuine `AlgEquiv` only
   AFTER localizing at the pivot minor; the dimension transport (localized polynomial-extension Krull
   dim, reducible/min-prime) is the wall, ~6–9 modules. Hardest sub-wall: **dim of localized
   polynomial extensions over (possibly reducible) affine coordinate rings**.
2. **Substrate objection (independently confirmed):** `varietyDim` sees the closure, not the open
   chart — G2 needs a NEW localized-chart-ring layer. (Mitigant: dense-open ⟹ same dim as closure, so
   the *top-component* dim is recoverable; the *product isomorphism* still lives on the localization.)
3. **Inner-group route (Q2b): NO-GO** — `mult⁻¹(E)` is not a single H-orbit; the rank-pattern orbit
   classification doesn't classify H-orbits with frozen endpoint product; recursion-on-N is a hidden
   stratified-dim theorem. `OrbitImageDim` computes dims of KNOWN orbit closures, doesn't identify the
   fibre as such.
4. **"fibre(E) = Σ⁰_{d−r}" lead (Q2c): LITERALLY FALSE** (verified: `dim fibre(E)=4 ≠ dim Σ⁰_{(1,1,1)}=1`).
   Correct relation: `dim fibre(E) = dim Σ⁰_{d−r} + Σ_{i=1}^{N−1} r(2 d_i − r)` (interior-vertex frame
   terms). Self-consistent on the anchor: `4 = 1 + 3`. Still needs chart/product infra — not a free win.

### My independent addition: the going-down-on-localized-comorphism mechanism
There are TWO additivity mechanisms, not one:
- **(M-tensor)** product-variety dim = sum (Codex's framing) — blocked on the missing tensor/localized
  poly-ext dim lemma.
- **(M-goingdown)** localize F1's `multComap` to the pivot chart (invert pivot minor + rank minors);
  on that chart `mult` IS flat (the bundle), so `HasGoingDown` holds and the LANDED
  `height_eq_height_add_of_liesOver_of_hasGoingDown` gives `height P = height p + height(fibre prime)`
  directly — the engine-native path the prior L1 threads intended. Reuses landed machinery; dodges the
  missing tensor lemma. STILL needs: (i) chart-localized `multComap` as `algebraMap`; (ii) a genuine
  **flatness proof on the chart** (the wall-within-the-wall that stalled thread-04, NOT an API gap —
  ~8–12 modules to construct the localized determinantal-chart algebra map + prove free/flat via the
  Schur section); (iii) `height(fibre prime) = dim mult⁻¹(E)`; (iv) reducibility/min-prime over
  components. So M-goingdown moves the wall from "tensor-dim lemma" to "chart flatness proof", but the
  total build size is comparable (Codex's 6–9 + the flatness construction).

