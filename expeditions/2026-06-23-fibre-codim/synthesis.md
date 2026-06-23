# synthesis — fibre-codimension bundle-shift (LR Lemma 4.6)  (controller's internal ground)

*Internal integrative read + drift-guard; assumes repo context. Not the deliverable.*

## Current read (2026-06-23, setup)

Opened off `dev` (`8cba3dd`, includes PR #6 + #7) after the `explicit-ctheta` close. The LR engine
(Bundles 1–3) and the `r=0` fibre (`codim mult⁻¹(0) = C`, `DLN.RlctPayoff`) are complete. The **one
remaining geometric gap** is the general-`B` fibre codimension — LR **Lemma 4.6** — currently an
ASSUMED hypothesis `BundleShiftInterface.cited_bundle_shift` in `DLN.RlctPayoffGeneral`:

> for `0 < N`, `B.rank = r`, `r ≤ min d`:
> `codimRepCanonical (fibre d (B.map ι)) = codimRepCanonical (productRankLocusLE d r) + r(d_0+d_N−r)`.

The `rlct = (C + r(d_0+d_N−r))/2` payoff (`rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi`) carries
this as one of two Cited/assumed interfaces (the other = the genuinely-cited Aoyagi rlct bound).
Discharging Lemma 4.6 removes the assumed one.

**Difficulty is real:** the interface docstring says a prior thread (thread 11) hit "the fibre-dimension
wall of Mathlib v4.29." So a from-scratch build is likely (cf. the q-series sub-library; the
`voigt-discharge` AG dimension library — `Ideal.height` codim, orbit dimension,
`dim 𝒪 = dim G − dim Aut`).

**Route (LR):** `mult⁻¹(B)` fibres locally-trivially over the rank-`r` matrix variety
`Mat^{rk=r}` (dim `r(d_0+d_N−r)`) with a zero-product-type fibre; total = base + fibre dimension gives
the shift. `codim Σ̄^r = C` is landed (`Core.SigmaCodim`).

## Plan

**Open with a RECON (thread 01)** — scope reachability before grinding (the difficulty is known). Verdict:
whole-in-reach → propose a rung-ladder for a formalisation tide; obstruction → roadmap with the precise
missing AG. Then either a tide (formaliser) or a roadmap entry. Build baseline warming (fresh worktree).

## Drift guard

LR route only (`Core` geometry + `DLN.RlctPayoff*`). **No collision with the live aoyagi-full** (its
independent λ-via-resolution route, `DLN.RLCT.*`, does not touch this). The analytic
`rlct ≤ ½·codim` stays **Cited**; nothing named `rlct_…` claims it.

## Recon verdict (2026-06-23, thread 01) — GENUINE BLOCKER

Lemma 4.6 is **not whole-in-reach** at Mathlib v4.29. The shift ≡ dimension additivity
`varietyDim Σ^r = varietyDim mult⁻¹(B) + r(d_0+d_N−r)`, which needs a **finite-type-morphism dimension
theorem** (`dim total = dim base + fibre dim`) that Mathlib lacks and the landed AG library does not
supply for *this* map: for `B≠0`, `mult⁻¹(B)` is not `GL_d`-stable (`mult(P•A)=P_N·mult(A)·P_0⁻¹`), so
it is not a union of orbit-rank-loci and the `r=0` orbit-closure machinery does not transfer. Size of a
from-scratch build: **~8–15 modules** (Codex this thread; thread-11 gave 7–10). Decorrelated Codex
(authenticated, xhigh) convergently confirmed + sharpened (the wall is the `ringKrullDim` equality for
finite-type families; the global-trivialisation escape doesn't apply — bundle only locally trivial).
Numerics: `(2,2,2),r=1` fibre codim 4 = 1+3 ✓. **Decision: keep the cited `BundleShiftInterface`;
roadmap the gap.** The one in-reach sub-brick (a thermometer, NOT a standalone deliverable):
`dim Mat^{rk=r} = r(d_0+d_N−r)` via a new `G_out` orbit-image route (~2–3 modules).

**This expedition's central question is answered in the negative (a scoping deliverable): the chunk is
blocked, precisely sized, and roadmapped.** Strategic fork surfaced to the operator.

## Pivot — operator committed to the AG build (2026-06-23)

The operator chose to **take on the from-scratch AG dimension-theory build** to close Lemma 4.6, and
authorised starting with the recon's "thermometer" brick. So this expedition is no longer recon→roadmap;
it now **pursues the build**, in the recon's order:

1. **[thread 02, NOW] Thermometer — `dim Mat^{rk=r} = r(d_0+d_N−r)`.** The determinantal-stratum
   dimension, via a new `G_out = GL_{d_N}×GL_{d_0}` orbit-image route on the existing `voigt-discharge`
   trdeg/Jacobian machinery (`OrbitImageDim`/`JacobianTrdeg`/`OrbitPullbackDim`). The one in-reach
   geometric brick; its outcome is a faithful thermometer for whether **layer 1** (the wall) is worth
   opening.
2. **[then] Layer 1 — the finite-type-morphism dimension theorem** (`dim total = dim base + fibre dim`),
   the actual wall (~5–8 modules). Reassess after the thermometer.
3. **[then] Layer 3** — `G_out`-equivariant trivialisation of `mult : Σ^r → Mat^{rk=r}` (~1–2).
4. **[then] Layer 4** — reducibility / per-component assembly into the `codimRepCanonical` shift (~1–2);
   retire the cited `BundleShiftInterface`.

**Build is workable.** Uplift A applied in practice: symlinked this worktree's `lean/.lake/packages` →
the main checkout's prebuilt copy (mathlib rev `8a178386` matches), so the worktree builds without the
mathlib clone (`Core.Basic` built in 4.2 s). Full baseline build green (3696→3697 with the module).

## Thermometer LANDED (thread 02, 2026-06-23) — green, but layer 1 NOT de-risked

`Core.DeterminantalStratumDim.varietyDim_productRankLocusLE_stratum`: for `[IsAlgClosed k] [CharZero k]`,
`r ≤ n`, `r ≤ m`, `varietyDim (productRankLocusLE ![n,m] r) = r(n+m−r)`. Green (3697 jobs), `scripts/sorries`
0, axiom-clean; reviewer fidelity PASS + Codex + my own independent green-gate + precision/bedrock read.

**Route (not the recon's two candidates):** the **N=1 specialisation** — `productRankLocusLE ![n,m] r`
*is* the rank-`≤r` determinantal variety (single-arrow quiver, `G_d = G_out`), so the LANDED
`voigt-discharge`+`SigmaCodim` stack applies. 1 reuse-chain (`codim=cCodim` enat, catenary `codim+dim=card`,
orbit-closure primality) + 3 elementary new bricks (N=1 Kostant singleton ⇒ `cCodim = (n−r)(m−r)`; the
variety = one orbit closure ⇒ primality; `card = m·n`). Then `m·n − (n−r)(m−r) = r(n+m−r)`.

**THERMOMETER READING (the key deliverable):** GREEN, but **it did NOT touch layer 1.** It rode the
single-variety catenary `codim+dim=card`; recon's **layer 1** — the finite-type-morphism dimension
theorem `dim total = dim base + fibre dim` for `mult⁻¹(B) → Mat^{rk=r}` — is a DISTINCT mechanism, still
the genuine blocker. So the thermometer gives **no positive signal** that layer 1 is easier than the
recon feared (~5–8 modules, missing from Mathlib). **Checkpoint surfaced to the operator** before opening
the layer-1 build.

**Noted future need (layer 3):** the explicit matrix-rank-locus identification
`productRankLocusLE ![n,m] r = {M | M.rank ≤ r}` was dropped (non-load-bearing here, fought `multPrefix`
dependent types); needed when layer 3 uses `Mat^{rk=r}` as the bundle *base*. Tracked.

## Layer-1 design recon LANDED (thread 03, 2026-06-23) — GO, REFRAMED + de-risked

**The wall was mis-scoped.** We do NOT need the general morphism theorem `dim total = dim base + fibre`.
Two of the three dims are already landed (`dim Σ^r = card − cCodim`, `SigmaCodim`+`NullstellensatzCodim`;
`dim Mat^{rk=r} = r(d_0+d_N−r)`, the thermometer). So the only unknown is **`dim fibre`**, and the engine
already carries the lever: the **going-down height-additivity lemma**
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (`@[stacks 00ON]`, present at v4.29), applied
via flatness — *already used* in `Core.AffineDomainDimension` / `FlatQuasiFiniteHeight` /
`PolynomialDimension` (substrate the earlier recon understated). Minimal target: the squeeze
`(★) varietyDim Σ^r = varietyDim Mat^{rk=r} + varietyDim(fibre)`, equivalent to the codim shift via the
catenary. Numeric check `(2,2,2),r=1`: `7 = 3 + 4`. Codex (xhigh, decorrelated) converged identically.

**Scope collapses** ~8–15 → **~5–8 modules** (a fixed-fibre flat-height squeeze). **Rung-ladder:**
L1-0 flatness of `mult` on a rank-`r` chart (NEW, **HIGH** — the wall-within) → L1-1 height-additivity
(Mathlib+landed pattern) → L1-2 fibre-ring id (NEW, MED) → L1-3 base dim on chart (LANDED+transport) →
L1-4 height=dim assembly (LANDED) → L1-5 reducibility/per-component bookkeeping (NEW, MED-HIGH) →
L1-6 output codim bridge (LANDED). **Residual risk concentrates on L1-0 and L1-5.**

**Sequencing (recon's, adopted):** **Tide A** = L1-0 flatness (standalone, gating, thermometer-style) →
**Tide B** = L1-1→4 squeeze (mostly transport) → **Tide C** = L1-5→6 (retire `cited_bundle_shift`).
**L1-0 fallback** if flatness walls: a two-inequality sandwich (lower bound cheap via going-down/up;
upper bound = equidimensionality, the residual hard half); failing that, discharge `r ≤ 1` + roadmap
generality. Tide A opens with a SPECIFY-first probe of the v4.29 `Module.Flat` descent-along-chart API.

## HOLD — VM rotation (2026-06-23 ~14:15 UTC)

Operator is rotating the VM; holding, will resume in the same session. **State at hold:** everything
landed is committed + pushed to `origin/expedition/fibre-codimension` (thermometer module + all
expedition docs incl. the thread-03 design report + thread-04 brief). No live teammates (the Tide A
formaliser died on a **transient API 529 overload**, and the re-launch was blocked by model
unavailability — infra, not a math wall; nothing was lost).

**Tide A ALREADY reached its verdict** (captured in `lean/DLNFibre/Core/FlatTrivialProductProbe.lean` —
builds green, an un-aggregated `example`-block contract artefact) before the overload deaths: the
`Module.Flat` API is fully viable at v4.29 (the `example`-blocks pin free⟹flat, flat-local-on-base
`Module.flat_of_localized_span`, `RingHom.Flat.propertyIsLocal`, the height-additivity lemma). **But the
flat route is unreachable until a from-scratch coordinate-ring algebra map `A →+* B` for `mult` exists** —
the engine has none (`mult` is set-level on `Tuple d`, codim via `vanishingIdeal`/`Ideal.height`; no Spec,
no scheme, no algebra map between base/total coordinate rings). Building that ring map + the determinantal
chart localisation + the section trivialisation is an **~8–12-module affine-AG construction — NOT an API
gap.** This **revises L1-0's cost UP** from the design recon's optimistic read.

**RESUME = an operator re-scope decision (NOT a blind Tide A re-launch):**
(a) commit to the ~8–12-module coordinate-ring-map / Spec construction for `mult` (the honest flat route);
(b) the **fallback two-inequality dimension sandwich** (cheap lower bound via going-down/up; upper bound =
equidimensionality, the residual hard half); or (c) discharge the witness range `r ≤ 1` + roadmap
generality. The probe file pins the verified downstream API so whichever route is chosen stands on
confirmed contracts.

**Build note for resume:** the worktree builds via the symlinked shared `lean/.lake/packages` → main
checkout (mathlib `8a178386`); if the symlink/`.lake` did not survive rotation, re-create it
(`rm -rf lean/.lake && mkdir lean/.lake && ln -s
/home/ubuntu/workspace/geometry-of-dln-fibre/lean/.lake/packages lean/.lake/packages`) — do NOT
`lake exe cache get`.

## Process

Controller in a worktree ⟹ teammate `isolation: worktree` collapses to this shared worktree (serial).
The fresh-worktree baseline build hit the mathlib-clone wall (>10-min bash cap) — Uplift A again;
deferred (no tide pending the fork).

## RESUME — operator: "go straight to the build, ambitious" (2026-06-23, post-rotation)

Re-read the full expedition state. Operator declined the gating recon hedge and committed to the
ambitious build of Lemma 4.6 (route (a)≈(b): the comorphism + fixed-fibre height-squeeze; Codex's
"buildable route", the general bundle theorem stays roadmapped).

**Exact discharge target** (`BundleShiftInterface.cited_bundle_shift`, the only assumed step under the
`rlct = C/2` payoff): for `0<N`, `B.rank=r`, `r≤d k'`,
`codimRepCanonical (fibre d (B.map ι)) = codimRepCanonical (productRankLocusLE d r) + r(d_0+d_N−r)`.
Brick A (landed) gives `codimRepCanonical Σ̄^r = cCodim d r`; via the landed catenary bridge
(`height_vanishingIdeal_add_varietyDim_eq_card`) the target is the **dimension squeeze**
`varietyDim(fibre d B) = varietyDim Σ̄^r − r(d_0+d_N−r)`, i.e. `dim Σ̄^r = dim(fibre) + dim Mat^{rk=r}`
(both RHS dims landed: `SigmaCodim`/`NullstellensatzCodim` + the thermometer `DeterminantalStratumDim`).

**The keystone is constructible — thread-04's "no ring map exists" is "not yet built", not "impossible".**
`mult` is defined over any `CommRing`, so the product-entry polynomials are just `mult` applied to the
GENERIC tuple (entries = `MvPolynomial.X` variables) over `MvPolynomial (RepCoord d) k`. Eval at a point
recovers the actual product (eval is a ring hom, commutes with matrix mult), so:
- `canonicalCoord '' (fibre d B) = zeroLocus {multPoly(r,c) − C(B r c)}`;
- `vanishingIdeal(fibre) = radical(span{multPoly(r,c) − C(B r c)})` (Nullstellensatz, `IsAlgClosed`);
- the comorphism `multComap := aeval multPoly : MvPolynomial(Fin d_N × Fin d_0) k →ₐ MvPolynomial(RepCoord d) k`
  realises the fibre generator-ideal as `Ideal.map multComap (maxIdeal B)`, i.e. the fibre coordinate
  ring is `R_total ⧸ (m_B · R_total)` — the "fibre = B/mB" object the height-squeeze consumes.

**Rung-ladder (committed):**
- **Tide F1 [thread 05, NOW] — the comorphism keystone** (`Core.MultComorphism`): `multPoly`, the
  eval-compatibility bridge, fibre = zero-locus, `vanishingIdeal(fibre) = radical(fibre-gen-ideal)`, and
  `multComap` with the `Ideal.map` identification. Discharges the thread-04 blocker concretely.
- **Tide F2 — the height-squeeze** (`dim(fibre) = dim R_total − dim R_base` on a rank-`r` chart).
  **Route steer (controller, post-F1-launch): the two-inequality SANDWICH, NOT flatness.** The landed
  `AffineDomainDimension.affine_domain_height_add_ringKrullDim_quotient_eq` (`height p + dim(A⧸p) = dim A`
  for a finite-type affine domain `A = MvPolynomial⧸prime`) is **equidimensionality with NO flatness
  hypothesis** — exactly Codex's upper bound. So F2 dodges **L1-0 flatness** (the wall-within-the-wall
  that stalled thread-04): upper bound = this affine-domain formula per top component; lower bound = a
  minimal prime over `m_B` (uses F1's `multComap` + `Ideal.map` identification, NOT flatness). Confirm the
  exact form once F1 lands. Reducibility subtlety: `codimRepCanonical = height(vanishingIdeal) = min` over
  components and Σ̄^r is reducible when θ>1, so the sandwich is per-(top-)component — dovetails into F3.
- **Tide F3 — assembly**: per-component / reducibility bookkeeping → `codimRepCanonical(fibre) = cCodim + shift`;
  retire `cited_bundle_shift`. Witness `(2,2,2), r=1`: fibre codim `4 = 1 + 3`.

## F2 OUTCOME — the sandwich is a NO-GO; my route steer was wrong (2026-06-23)

**Correction to my own steer.** I told the operator the sandwich "dodges L1-0 flatness" and "the two
scariest pieces are dissolved." That was wrong, and Tide F2 + decorrelated Codex caught it:

- **Krull is the wrong direction.** `Ideal.height_le_card_of_mem_minimalPrimes_span` bounds codim
  *above* by the generator count `d_N·d_0` (≫ the shift `δ = r(d_0+d_N−r)`), not below by `C+δ`. The
  "lower bound via Krull" I steered toward does not exist without first building the exact-rank chart.
- **`mult` is genuinely not flat.** Fibre dimension JUMPS as the rank drops — witness `(2,2,2)`: the
  rank-1 fibre has dim 4 (codim 4 = C+δ = 1+3), the rank-0 fibre `mult⁻¹(0)=Σ̄^0` has dim 5 (codim 3).
  So `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` does not apply to `multComap` at the
  closed point `B`. Flatness is NOT dodged; it only holds after restricting to the open exact-rank
  chart — which is exactly the missing build. The landed affine-domain equidimensionality converts
  dim-bounds to height-bounds but does not supply the missing fibre-dimension upper bound.
- **No clean partial identity beyond r=0.** r=1 still needs the chart; r=0 (`fibre(0)=Σ̄^0`, shift 0)
  is the only clean case and is already landed (`DLN.RlctPayoff`).

**LANDED (honest reachable half, bedrock):** `Core.FibreCodim` — `codimRepCanonical Σ̄^r ≤
codimRepCanonical(mult⁻¹ B)` (from `mult⁻¹B ⊆ Σ̄^r`), green/sorry-free/axiom-clean, named honestly as a
one-sided bound, NO-GO documented next to the claim. `[Field k]` only. The future chart build stands on it.

**Corrected roadmap — the genuine remaining content = the rank-chart local-trivialization build** (LR's
Lie-group submersion, the thing thread-01/thread-04 flagged and the sandwich was hoped to dodge but does
not): reduce `B` to `E = diag(I_r,0)`; pivot chart `U = D(Δ)` (top-left r×r block invertible, dim δ);
explicit section `D = C A⁻¹ B`; prove `mult⁻¹(U) ∩ Σ̄^r ≅ U × mult⁻¹(E)` as rings; flat-on-chart ⟹
going-down ⟹ `height_eq_height_add` per top component; minimum over components via Brick A's
minimal-prime machinery (`SigmaCodim.minimalPrimes_sigmaIdeal_eq`). Substantial, multi-rung, but concrete
(explicit charts, not abstract scheme theory). The `BundleShiftInterface` stays Cited until it lands.

**Decision point for the operator** (cost re-calibrated UP from my wrong steer): commit to the chart
build (ambitious completion, several tides) vs. land-the-half + roadmap + keep Cited.

## BUILD COMMITTED — the rank-chart trivialization (operator: "A. Build it!", 2026-06-23)

Operator chose (A): build the full Lemma 4.6 identity via the rank-chart local-trivialization. The
target (Core): `codimRepCanonical (fibre d B) = cCodim d r + r(d_0+d_N−r)` for `B` rank r, r≤min d, 0<N.

**Rung-ladder (the LR submersion, made engine-concrete):**
- **G0 [thread 07, design recon, NOW]** — pin the formalization decomposition + probe the G2 crux
  (product trivialization + dim-additivity) for v4.29 reachability; group-reduction vs inner-quiver
  route; decorrelated Codex; output the confirmed ladder + per-rung risk + go/no-go.
- **G1 [thread 08, formaliser, NOW (parallel, independent)]** — **reduce to normal form.**
  `codimRepCanonical (fibre d B) = codimRepCanonical (fibre d E)` for `B` rank r, `E = diag(I_r,0)`, via
  the `GL_{d_N}×GL_{d_0}` linear action on `Rep_d` (on the end factors A_N, A_1) + mult-equivariance
  `mult(P·A)=P_N·mult(A)·P_0⁻¹` + codim-invariance under the induced coordinate-ring algebra
  automorphism (`NullstellensatzCodim.height_map_algEquiv`) + rank-normal-form transitivity (any rank-r
  `B = P_N·E·P_0⁻¹`). Reduces the whole problem to the SINGLE fibre over `E`. Independent of G2/G3,
  bankable regardless — safe to build now.
- **G2 [the crux]** — chart trivialization: `mult⁻¹(U) ∩ Σ^r ≅ U × mult⁻¹(E)` over the pivot chart
  `U = {top-left r×r block invertible}` via the explicit section; → dim-additivity over the chart.
- **G3 [assembly]** — `dim Σ̄^r = δ + dim(fibre over E)` (chart is dense open in the top stratum) +
  Brick A min-over-components (`SigmaCodim.minimalPrimes_sigmaIdeal_eq`) → `codimRepCanonical(fibre E) =
  cCodim + δ`. With G1 ⟹ the identity for all B of rank r.
- **G4 [DLN wiring]** — discharge `BundleShiftInterface.cited_bundle_shift` (instantiate K, `B.map ι`). Thin.

Substrate in hand: F1 (`MultComorphism`, the comorphism + fibre ideal), the F2 lower bound
(`FibreCodim`), the thermometer (`dim Mat^{rk=r}=δ`), Brick A (`SigmaCodim`), the catenary bridge, the
group/orbit machinery (`Orbit`). Residual risk concentrates on **G2** (the product trivialization) —
hence the G0 recon probes it first.

## G0 RECON VERDICT (thread 07, 2026-06-23) — CONDITIONAL GO; gate the flatness core

Scout + decorrelated Codex: the chart build is buildable but it IS the real Lie-group submersion made
affine-AG-concrete — **~6–12 modules, HIGH-risk core = a chart-flatness proof.** Both shortcut hopes
fail: inner-group route NO-GO (`mult⁻¹(E)` is not a single H-orbit; `OrbitImageDim` can't identify it);
`fibre(E)=Σ⁰_{d−r}` LITERALLY FALSE (`dim fibre(E)=4 ≠ dim Σ⁰_{(1,1,1)}=1`; correct relation
`dim fibre(E)=dim Σ⁰_{d−r}+Σ_{i=1}^{N−1} r(2d_i−r)`, still needs the chart infra).

**Substrate finding:** `varietyDim` reads the Zariski CLOSURE dim, not an open chart's coordinate ring;
G2 lives on the open pivot chart (localize at the pivot minor) ⟹ a NEW localized-chart-ring layer.
Mathlib v4.29 has NO `Localization.Away` Krull-dim-preservation and NO tensor Krull-dim additivity
(grep-verified) — so the product-dim mechanism (M-tensor) must be built. **Recommended route: M-goingdown** —
localize F1's `multComap` to the pivot chart where `mult` IS flat (the bundle), then the LANDED
`height_eq_height_add_of_liesOver_of_hasGoingDown` gives the shift; reuses landed going-down, one fewer
missing Mathlib lemma. Wall moves to: a genuine **flatness proof on the chart via the Schur section**.

**Reducibility (Q3):** Brick A `minimalPrimes_sigmaIdeal_eq` (Σ̄^r components = maximal orbit closures);
the chart trivialization carries components(Σ^r) ↔ components(fibre) with uniform `+δ`, so
`codimRepCanonical = min over components` survives. (Module ~7–9; part of the hard cluster.)

**Launch order (recon's, adopted):** keep G1 running; then a **gating prototype tide (G2a, thread 09)** =
the chart-localized `multComap` + the Schur freeness/flatness on ONE pivot chart (the anchor `(2,2,2),r=1`)
— thermometer-style: if chart flatness walls there, we learn it cheaply before the full G2. Only on a GO
signal: commit full G2 (height-additivity + reducibility) + G3 (assembly) + G4 (DLN wiring). **Worktree
constraint:** formaliser tides run SEQUENTIALLY here (shared `.lake/build`); G1 → G2a → G2 → G3 → G4.

## G2a GATE VERDICT (thread 09, 2026-06-23) — NO-GO this run; G2 buildable but ~8–12 modules

The gating flatness prototype + decorrelated Codex convergently read **NO-GO** for a cheap landing.
Per-sub-step: (1) the chart-localized comorphism `IsLocalization.Away.map (multComap) Δ` is REACHABLE
(compiles); (3) flatness is a one-liner GIVEN the trivialization, via the **tensor** closer `R_t ≃ R_b
⊗[k] F_E` (`F_E` reducible — the `ℓm=0` relation — NOT a polynomial algebra; Codex corrected my initial
model) → `Algebra.TensorProduct.instFree` → flat. **The WALL is (2): the Schur trivializing `AlgEquiv`.**
The engine carries the exact-rank base/total coordinate rings as **opaque `vanishingIdeal`-quotients with
no explicit presentation**, so the `AlgEquiv` cannot be exhibited without first building the
determinantal-quotient presentation from scratch. No API gap blocks it — it is a from-scratch
affine-determinantal-AG build. Codex also refuted the soft-retraction shortcut (section ⊁ going-down;
counterexample `A→A×A/(t)`) and confirmed v4.29 has no miracle/generic-flatness criterion to bypass it.

**Durable artefact:** `Core/ChartFlatnessProbe.lean` (green, zero sorry, un-aggregated like
`FlatTrivialProductProbe`) — pins the localized comorphism, `IsLocalization.flat`, the going-down
consumer, and the corrected tensor Schur closer as compiling `example`s. The future build stands on it.

## ROADMAP — G2 = the determinantal-presentation build (the named wall)
To close the full identity, build (≈8–12 modules, the dominant cost is the presentation layer, NOT the
flatness closer):
1. **Explicit presentation of the exact-rank determinantal coordinate rings** (base `Mat^{rk=r}` and total
   `Σ^r`) — replace the opaque `vanishingIdeal`-quotients with generators/relations usable for an `AlgEquiv`.
2. The localized determinantal quotient algebra map (invert the pivot minor) on the pivot chart `U`.
3. The **Schur `AlgEquiv`** `R_t,loc ≃ R_b,loc ⊗[k] F_E` (the trivialization; the reducible `F_E` model),
   incl. the inverse formulas through quotient+localization → `Module.Flat` → `HasGoingDown`.
4. Height-additivity via the LANDED `height_eq_height_add_of_liesOver_of_hasGoingDown` → the `+δ` shift.
5. Reducibility/min-prime bookkeeping (`F_E` reducible; Brick A `minimalPrimes_sigmaIdeal_eq`) +
   finite-chart-cover for top-dimension → `codimRepCanonical(fibre E) = cCodim + δ`.
6. With G1 (`codimRepCanonical_fibre_eq_of_rank_eq`) ⟹ the identity for all rank-r B; G4 discharges
   `DLN.BundleShiftInterface.cited_bundle_shift`.

**Per the pre-agreed gate contract (NO-GO ⟹ land + roadmap), this expedition's reachable scope is
complete.** Banked: F1 (comorphism keystone, reusable), the F2 lower bound, G1 (reduce-to-E), two
route-pinning probes, this precise roadmap. The determinantal-presentation build is sub-expedition-scale.

## OPERATOR: PUSH UNTIL 4.6 CLOSES (option 2, 2026-06-23)

Operator chose (2): build the determinantal-presentation layer in-place, drive until Lemma 4.6 closes.
Committing. Tide-ladder (controller decomposition of the ~8–12 modules; refine as tiles land):
- **G2-1 [thread 10, NOW]** — pivot-chart explicit presentation of the **base** `Mat^{rk=r}`: the Schur
  parametrization `Mat^{rk=r} ∩ U ≅ GL_r × Mat_{r×(d_0−r)} × Mat_{(d_N−r)×r}` (top-left r×r block `Δ`
  invertible; bottom-right forced `= B_21 Δ⁻¹ B_12`), dim `= δ = r(d_0+d_N−r)`. The explicit handle the
  opaque `vanishingIdeal`-quotient lacked; foundation for the Schur AlgEquiv.
- **G2-2** — explicit presentation of the **total** `Σ^r` on the chart.
- **G2-3** — the Schur `AlgEquiv` `R_t,loc ≃ R_b,loc ⊗[k] F_E` (reducible `F_E`) → `Module.Flat` → going-down.
- **G2-4** — height-additivity (LANDED `height_eq_height_add_of_liesOver_of_hasGoingDown`) → `+δ`.
- **G2-5** — reducibility/min-prime + finite chart-cover → `codimRepCanonical(fibre E) = cCodim + δ`.
- **G3/G4** — assembly with G1 (`codimRepCanonical_fibre_eq_of_rank_eq`) ⟹ identity for all rank-r B;
  discharge `DLN.BundleShiftInterface.cited_bundle_shift`.
Discipline: each tide SPECIFY-first + decorrelated Codex + hard checkpoint; sequential (worktree-shared
build); controller green-gates + reviewer/Codex on the final discharge. Surface only a genuine wall or completion.
