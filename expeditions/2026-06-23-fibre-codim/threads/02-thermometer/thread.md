# thread 02 — thermometer  (formalisation / tide)

**Type:** formalisation (tide) · `OPENED → SPECIFY → PROVE → AUDIT`.
**Goal:** the first rung of the AG build for Lemma 4.6 — the **determinantal-stratum dimension**

$$
\dim \mathrm{Mat}^{\mathrm{rk}=r}_{d_N \times d_0} \;=\; r\,(d_0 + d_N - r),
$$

the dimension of the variety of $d_N \times d_0$ matrices of rank $\le r$ (equivalently the
rank-exactly-$r$ locus, open dense in it). This is the recon's in-reach geometric brick **and the
thermometer**: its outcome tells us whether the engine's orbit-image dimension route generalises to a
*new* orbit map — the read that gates opening layer 1 (the finite-type-morphism dimension wall).

## Why / context (read first)
- **The recon report** in `expeditions/2026-06-23-fibre-codim/threads/01-recon/thread.md` — the full
  route, the HAVE/MISSING table, and why this brick is in-reach while the full Lemma 4.6 is not.
- This is rung 1 of a committed multi-layer build; subsequent layers (the morphism-dimension theorem,
  the `G_out`-trivialisation, the per-component assembly) are NOT in scope here.

## Route (recon's; verify in SPECIFY)
$\mathrm{Mat}^{\mathrm{rk}=r}$ is a single orbit of $G_{\mathrm{out}} = GL_{d_N} \times GL_{d_0}$ acting
by $(P,Q)\cdot M = P\,M\,Q^{-1}$ (the orbit of the rank-$r$ block $E_r$ is all rank-$r$ matrices). The
`voigt-discharge` library computes an orbit's dimension via the **orbit-map image** (transcendence
degree / generic Jacobian rank): `Core.OrbitImageDim`, `JacobianTrdeg`, `OrbitPullbackDim`,
`OrbitVariety`, `OrbitDifferential*`. **But** that machinery is currently wired to the `GL_d` quiver
orbit map `μ_M` (differential `δ⁰`); this brick needs a **new** `G_out`-on-`Mat` orbit map + its
differential, then the (generic) image-dimension count `= r(d_0+d_N−r)`. Building that new orbit map
cleanly (or finding it does not reuse the existing infra) **is the thermometer reading.** A direct
determinantal parametrisation (rank-$r$ ≅ image of $(d_N\times r)\times(r\times d_0)$ full-rank pairs,
$r d_N + r d_0 - r^2$) is an acceptable alternative route if cleaner — report which you took.

## Process (supervisor checkpoint)
SPECIFY first: pin the exact Lean statement (the engine encoding of "$\dim$ of the rank-$\le r$ matrix
variety" — `varietyDim` of the determinantal ideal, or the orbit dimension) and a proof skeleton;
**report the skeleton + chosen route + any friction to the controller BEFORE grinding the full proof**
(this is rung 1 of a hard build — we checkpoint the route). Then PROVE.

## AUDIT gate
Green (whole library), `scripts/sorries` 0, `#print axioms` `[propext, Classical.choice, Quot.sound]`.
A concrete witness by `decide +kernel` or evaluation (e.g. $2\times2$, $r=1$ → $3$). Reviewer confirms
the Lean statement = "$\dim \mathrm{Mat}^{\mathrm{rk}=r} = r(d_0+d_N−r)$" (name = content).

## Build note
The worktree builds via a **symlinked shared `lean/.lake/packages`** (Uplift A — mathlib rev
`8a178386` matches the main checkout); do NOT run `lake exe cache get` (it would re-clone). `lake build`
from `lean/` works incrementally. New module under `lean/DLNFibre/Core/` (controller aggregates).

## Scope
`Core`-only (network-free; no `DLNFibre.DLN`). `decide +kernel` not `native_decide`. Don't touch other
worktrees or any stash. In-repo memory only.

## Report
The thermometer reading: did the orbit-image route generalise to the new `G_out` map (→ layer 1 likely
feasible), or did it require a different approach / hit friction (→ layer 1 reassessment)? Plus the
usual: final theorem name + signature, witness, green/sorries/axioms.

## Notes / progress
(appended during work)

---

# TIDE OUTPUT (2026-06-23, formaliser) — LANDED, sorry-free, axiom-clean

**THERMOMETER READING: GREEN.** The orbit-image dimension route generalised to the determinantal
variety with **zero new orbit-map build** — the recon's "new `G_out`-on-`Mat` orbit map" turned out
unnecessary. The classical rank-`≤ r` matrix variety is the **`N = 1` specialisation** of the LANDED
quiver engine: for the single-arrow dimension vector `d = ![n, m]`, a `Tuple` is one matrix
`Mat_{m × n}`, `G_d = GL_m × GL_n` is exactly `G_out`, and `productRankLocusLE ![n,m] r` is the
rank-`≤ r` determinantal variety. The entire `voigt-discharge` + `SigmaCodim` stack
(`codimRepCanonical Σ̄^r = cCodim`, unconditional in char 0 + alg-closed) applies by specialisation.
**Implication for layer 1:** the determinantal-stratum *dimension* (recon's layer 2) is now
discharged. The fibre-dimension *wall* (recon's layer 1, `dim total = dim base + dim fibre`) is a
DISTINCT obstruction and is untouched by this — it remains the genuine blocker.

## Route taken (NOT the recon's two candidates)
Neither (a) a new `G_out`-on-`Mat` orbit map + differential, nor (b) the direct `(u,v) ↦ u·v`
determinantal parametrisation (Codex decorrelated-flagged the parametrisation as fighting Mathlib's
rational-function bookkeeping). Instead: the **`N = 1` quiver specialisation** of the landed engine.
Codex independently surfaced this ("for `N = 1`, the existing type-A orbit-closure/codimension engine
specializes exactly to the classical rank-≤r determinantal variety").

## The four pieces (1 LANDED-reuse chain, 3 elementary new bricks)
- **LANDED-reuse:** `codimRepCanonical_productRankLocusLE_eq_cCodim_enat` (codim `= cCodim`,
  unconditional char 0 + alg-closed); `codimRep_add_varietyDim_eq_card` (catenary `codim + dim =
  card`); `isPrime_vanishingIdeal_orbitRankLocus` (primality of an orbit closure).
- **New brick (combinatorial):** `kostantPartitions ![n,m] r = {stratumPartition n m r}` (singleton at
  `N = 1`), so `cCodim ![n,m] r = (n − r)(m − r)` (the single `(0,0)·(1,1)` term of `codimForm 1`).
- **New brick (primality):** `productRankLocusLE ![n,m] r = orbitRankLocus M₀` for the realizer `M₀`
  (only the corner `(0,1)` constraint binds; diagonals are full), giving primality.
- **New brick (ambient):** `Nat.card (RepCoord ![n,m]) = m·n`. Then `m·n − (n−r)(m−r) = r(n+m−r)`.

## Statement card

> **Claim.** The variety of `m × n` matrices of rank `≤ r` (for `r ≤ n`, `r ≤ m`) has dimension
> `r·(d_0 + d_N − r) = r·(n + m − r)` (`d_0 = n`, `d_N = m`). Witness: `2 × 2`, `r = 1` → `3`.
>
> - **Lean:** `DLNFibre.Core.varietyDim_productRankLocusLE_stratum`
>   (`lean/DLNFibre/Core/DeterminantalStratumDim.lean` @ `8cba3dd5160af0158586313674a0c13135b4b71d`)
> - **Gloss.** Over an algebraically closed field of characteristic 0, for `r ≤ n` and `r ≤ m`, the
>   `varietyDim` (Krull dimension of the coordinate ring of the Zariski closure) of the flattened
>   closed product-rank-`≤ r` locus of the single-arrow quiver `d = ![n, m]` — i.e. the rank-`≤ r`
>   determinantal variety `Mat^{rk ≤ r}_{m × n}` — equals `r·(n + m − r)`.
> - **Proved.** The exact equality `varietyDim = r·(n + m − r)`, unconditionally given the hypotheses
>   `[IsAlgClosed k] [CharZero k]`, `r ≤ n`, `r ≤ m`. Axiom-clean `[propext, Classical.choice,
>   Quot.sound]`. Concrete witness `2 × 2, r = 1 → 3` (`example` in-file; also checked over
>   `AlgebraicClosure ℚ`).
> - **Assumed.** `[IsAlgClosed k] [CharZero k]` (the Voigt-discharge scope, where `codim Σ̄^r = C`
>   is the genuine geometric codimension); `r ≤ n`, `r ≤ m` (so `Mat^{rk≤r}` is the full corner-`r`
>   variety — matches the recon target's `∀ k', r ≤ d k'`).
> - **Cited.** none (the whole chain is proved in-engine; the Voigt discharge it stands on is itself
>   proved, not cited).
> - **Deferred.** none for THIS brick. (The fibre-dimension theorem `dim total = dim base + dim
>   fibre` of recon's layer 1 — the genuine blocker — is a separate result, not in scope here.)
> - **Status.** sorry-free + reviewed (reviewer fidelity PASS on all 5 questions, 2026-06-23;
>   decorrelated Codex concurred; build/sorries/axioms independently confirmed from the worktree).

## AUDIT
- `lake build` (whole library): green, 3696 jobs (baseline intact). New module: 3011 jobs, green.
- `scripts/sorries`: `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `#print axioms varietyDim_productRankLocusLE_stratum` → `[propext, Classical.choice, Quot.sound]`.
- Witness `2 × 2, r = 1 → 3` proved in-file and over `AlgebraicClosure ℚ`.

## Aggregator wiring (controller-owned — exact line to append at the end of `lean/DLNFibre.lean`)
```
import DLNFibre.Core.DeterminantalStratumDim
```
(All three dependencies — `SigmaCodim`, `NullstellensatzCodim`, `SigmaStratification` — are already
imported in the aggregator; the new line goes last, after `import DLNFibre.Core.CThetaArbitrary`.)
