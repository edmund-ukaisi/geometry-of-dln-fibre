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
Aoyagi `rlct = ½·codim` equality stays **Cited**; nothing named `rlct_…` claims it.

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

## RING-LEVEL ARCHITECTURE for G2-2..G2-4 (controller design, 2026-06-23, post-G2-1)

The target `codimRepCanonical(fibre E) = C + δ` decomposes as a height composition (to be Codex-vetted
at the G2-2 checkpoint before committing the chain):

1. **Catenary composition (in `MvPolynomial(RepCoord)`):** `codim_Rep(fibre) = C + codim_{Σ̄^r}(fibre)`,
   for each top component (catenary; `codim_Rep(Σ̄^r) = C` is Brick A). [G2-4]
2. **Height-additivity on the descended comorphism `A = R_base → B = R_total`:** for `P` a minimal prime
   of `m_E·B`, `height P = height(m_E) + height(P / m_E·B)`. With `m_E` the maximal ideal of the closed
   point `E` in the irreducible base `Mat^{rk≤r}`: `height(m_E) = dim R_base = δ` (thermometer), and
   `height(P/m_E·B) = 0` (P minimal over `m_E·B`) ⟹ `codim_{Σ̄^r}(fibre) = δ`. [G2-4]
3. **The `HasGoingDown` for (2) holds only on the chart** (mult is NOT globally flat — fibre dim jumps).
   So localize `A,B` at `det Δ`; on the chart the Schur `AlgEquiv` `B_loc ≅ A_loc ⊗ F_E` gives free ⟹
   flat ⟹ going-down. Localization bookkeeping: primes meeting the chart keep their height. [G2-3, the wall]
4. **Prerequisite (G2-2):** explicit presentation of the **localized base ring** `R_base,loc[det Δ⁻¹]`
   as a polynomial localization in the free Schur coordinates (Δ,B12,B21) — which needs
   `vanishingIdeal(Mat^{rk≤r})` = the `(r+1)`-minor determinantal ideal (prime; is the radical/vanishing
   ideal over alg-closed k). G2-1's Schur relation `B22 = B21Δ⁻¹B12` is what makes it free once det Δ⁻¹.

**Rungs:** G2-2 = localized base presentation (+ Codex-vet the whole composition); G2-3 = total ring +
the Schur AlgEquiv + flat/going-down (the wall); G2-4 = the height-additivity + catenary composition →
codim(fibre E)=C+δ; G2-5 = reducibility/min-prime; G3/G4 = lift via G1 + discharge the interface.

## G2-2 CHECKPOINT — composition NO-GO REFUTED; generator-free base route (2026-06-23)

The G2-2 tide's decorrelated Codex flagged the ring-level composition as NO-GO (claiming the flat-local
height-additivity identity and catenary are both absent from Mathlib v4.29). **Controller override
(grep-verified): the engine's OWN landed AG library dissolves both — Codex assessed bare Mathlib, not the
engine.**
- The additive identity `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` IS present + used
  (`FlatQuasiFiniteHeight:75`, `PolynomialDimension:114` — "the load-bearing additive half", pinned in
  `FlatTrivialProductProbe:104`). Codex confused it with `HasGoingDown.of_flat` (only the inequality). It
  applies on the LOCALIZED flat rings.
- The catenary composition `ht_R(Q)=ht_R(I_X)+ht_{R/I_X}(Q/I_X)` follows from the landed poly-bridge
  (`height_vanishingIdeal_add_varietyDim_eq_card`) + the landed affine-domain equidim
  (`affine_domain_height_add_ringKrullDim_quotient_eq`), per top component.
So the chain stays on the height-additivity architecture. Real remaining work = localization-height
bookkeeping + per-component reducibility (G2-5), NOT absent machinery.

**G2-2 route (GO, generator-free — dodges determinantal-ideal theory, which IS absent at v4.29):** the
**Schur graph ideal** `J = (detΔ·B22 − B21·adj(Δ)·B12)` in the localized poly ring; prove `J ⊆ I_loc` via
"detΔ·g_ab vanishes on all Σ̄^r" (G2-1's Schur relation on the chart, trivially on V(detΔ)); upgrade to
`J = I_loc` by height-comparison (both prime height C; `Ideal.height_strict_mono_of_is_prime`). Base facts
(`R_base` domain, `dim = δ`) re-exported from `DeterminantalStratumDim` (the N=1-orbit-closure route).

**Reserved alternative for G2-4 (Codex's, genuinely good):** the **total-space explicit-coordinate** route
— on the chart the fibre is cut by `C+δ` coordinate equations (C for Σ̄^r + δ for E), so `height = C+δ` by
direct poly/localization transport, no flat-local dimension formula, no catenary. Trades the localization
bookkeeping for a stronger explicit total presentation in G2-3 (built anyway). Decide G2-4's route after G2-3.

## G2-2 D2 progress + a process gotcha (2026-06-24)

**Landed (aggregated, whole-lib green 3706, sorries 0, axiom-clean):** three new reusable modules from the
elimination tide — `MvPolynomialKerAeval` (`ker_aeval_eq_graphIdeal` for arbitrary ι, via the translation
identity — no `Finite`; + `graphIdealQuotientEquiv`, `graphIdeal_isPrime`), `GraphIdealHeight`
(`height_graphIdeal_eq = #eliminated vars`, field catenary), `DeterminantalBaseElimination` (the reindex +
detΔ bridge: `repCoordReindex`, `blockAlgEquiv`, **`blockAlgEquiv_detPivot`** = `detΔ ↦ C detSchurS`).
G2-2 remaining = the final localized transport + `Iad=J` + the equiv `A_loc/Iad ≅ Sd` (thread 13).

**PROCESS GOTCHA (record for future worktree-based expeditions; promote to a policy at close):** a
controller running from a worktree (via `EnterWorktree`) spawns teammates whose **Bash default cwd is the
MAIN checkout**, not the worktree — and the main checkout may be on a *different live session's branch*
(here `expedition/aoyagi-full`). A teammate's first `scripts/lb`/file-write/commit can land in the wrong
tree / collide with another session. **Mitigation (now in tide specs):** every teammate `cd`s into
`…/.claude/worktrees/<wt>/lean` explicitly for EVERY Bash call; never `git add -A`. The G2-2b tide hit this
(a file briefly landed in main), caught + cleaned it, left aoyagi's work untouched; controller verified
read-only — no collateral damage.

## G2-2 COMPLETE (rung 2 of ~6) — the localized base presentation (2026-06-24)

`Core.DeterminantalBasePresentation.basePresentationEquiv [IsAlgClosed k][CharZero k] : A_loc/Iad ≅ₐ[k]
Sd` — the localized determinantal base ring mod its base ideal IS the free Schur localization (regular,
dim δ). Green, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`; reviewer fidelity PASS
+ controller fidelity-read; aggregated. **Correctness guard verified satisfied:** the hard direction
`Iad ⊆ J` is EARNED by the height squeeze (`J ⊆ Ψ(Iad)` easy + `height J = height Ψ(Iad) = C` + both
prime ⟹ `Iad = J` via `height_strict_mono_of_is_prime`), NOT assumed — and the two heights come from
INDEPENDENT engines (`height Iad` from the codim/cCodim engine `height_map_sigmaIdeal_away_eq_cCodim`;
`height J` from the graph-ideal-height engine), so no circularity. The honest discharge.

**Reusable bedrock banked across G2-2** (threads 10–13): `DeterminantalChart` (Schur rank criterion +
block-diag rank additivity), `DeterminantalChartRing` (bordered Schur minor over any CommRing, universal-
coefficient route), `MvPolynomialKerAeval` (`ker_aeval = graphIdeal`, arbitrary ι), `GraphIdealHeight`
(catenary `height_graphIdeal_eq` + the localized transport), `DeterminantalBaseElimination` (reindex +
detΔ bridge + `blockAlgEquiv_detPivot`), `DeterminantalBasePresentation` (the localized Ψ + the (*)
bordered-minor identity + the squeeze + the equiv).

**Process note:** G2-2's elimination half (threads 12/13) saw heavy multi-tide coordination churn (3
collisions, a shutdown, message-crossings) — all from the controller spawning/re-engaging a second tide
on the same residual. **Zero damage** (branch coherent + green throughout, every committed seam axiom-
clean, no lost work — `g2-2c` preserved its work as a committed module). Lesson, now firm: ONE tide per
rung, run to natural completion/checkpoint, never a second tide on the same work until the first is
confirmed terminated. Applied from G2-3 on.

## Build ladder status (the determinantal-presentation route for Lemma 4.6)
- G1 (reduce-to-E) ✓ · G2-1 (chart Schur criterion) ✓ · **G2-2 (localized base presentation `A_loc/Iad ≅
  Sd`) ✓** · **G2-3 NEXT — the TOTAL presentation + flatness (the genuine wall)** · G2-4 (height-additivity
  → codim_{Σ̄^r}(fibre)=δ) · G2-5 (reducibility/min-prime) · G3/G4 (assembly + discharge BundleShiftInterface).

## G2-3 RECON VERDICT (thread 14, 2026-06-24) — REACHABLE, materially harder than G2-2 (~7–10 modules)

Scout + decorrelated Codex converged. No Mathlib gap; the wall is a from-scratch affine-AG construction.

**Route — endpoint normalization (NOT G2-2's graph trick — it doesn't port).** In `Rep_d` the product
entries are degree-N polys and the total rank ideal FACTORS (reducible: e.g. `det(A₂A₁)=detA₁·detA₂` for
(2,2,2)r1) — so the base's B22-graph-elimination fails. Instead: `R := Sd` (G2-2's output, regular dim δ),
`S := O(Σ̄^r ∩ chart)`. Write the chart target `B = L·E·H` (L,H unipotent); normalize ONLY the endpoint
factors `Ã₁ = A₁H⁻¹`, `Ã_N = L⁻¹A_N` (middles unchanged) ⟹ `mult(A)=B ⟺ mult(Ã)=E` ⟹ `S ≅ₐ[R] R ⊗_k F_E`
with `F_E = k[Ã]/(mult(Ã)−E)` (E constant, uniform in N). Free over k ⟹ flat ⟹ HasGoingDown ⟹ the LANDED
`height_eq_height_add_of_liesOver_of_hasGoingDown` ⟹ `codim_{Σ̄^r}(fibre)=δ`. LEH transport verified exact
on the (2,2,2),r=1 anchor; the 5 flatness/going-down closers compile at v4.29 (throwaway probe).

**Single chart covers the whole fibre at E** (pivot=1≠0). The `+C` (to `codim_Rep = C+δ`) is a SEPARATE
assembly rung reusing Brick A `minimalPrimes_sigmaIdeal_eq`; G2-4/G2-5 (reducibility) FOLD into it.

**DEAD route (killed, don't re-explore):** the CI / `d_N·d_0` shortcut is a CONFOUND — `(d_N−r)(d_0−r) =
C_single` (target-matrix codim) ≠ `C = cCodim_Rep(Σ̄^r)` (quiver codim); they differ at r=0 (landed
`codimRepCanonical(fibre d222 0)=3` ≠ `d_N·d_0=4`), so `mult⁻¹(0)` is NOT a CI. Codex independently rejected.

**Rung-ladder (R2-1..R2-6):** R2-1 localized total ring `S` (low) → **R2-2 base-change graph presentation
`S ≅ R[Ã]/(mult(Ã)−B_univ)` (M–L, the swing factor)** → **R2-3 endpoint-normalization AlgEquiv `S ≅ R ⊗_k
F_E` (HIGH — the wall, built on R2-2)** → R2-4 flat/going-down closer (low, one-liner once the AlgEquiv
exists) → R2-5 `height m_B=δ` + minimal-prime relative-height-0 (med) → R2-6 `+C` assembly + reducibility
fold (med). The wall (R2-2/R2-3) is new scheme-free affine scaffolding (the engine carries O(Σ̄^r) only as
a `vanishingIdeal`); everything else reuses landed engines.

**Plan (recon's, adopted):** spec R2-2 FIRST as a SPECIFY-first probe-tide — it decides M (reuses G2-2's
`blockAlgEquivLoc`/`IsLocalization.Away` machinery ⟹ R2-3 solid) vs L (needs new affine presentation ⟹
pen-and-paper certify the R2-3 ideal-transport before any formaliser commits). One write-tide at a time.

## R2-2 = L (thread 15, 2026-06-24) — routing pen-and-paper for the cut-ideal radical certification

R2-2 (swing-factor probe) returned **L** (tide + decorrelated Codex converged; clean STOP, no library
Lean, no sorry). The localized total-ring presentation does NOT cleanly reuse G2-2: the engine carries
`O(Σ̄^r∩chart)` only as the REDUCED `Sred = (MvPol/sigmaIdeal)[1/ΔP]`, but the endpoint-normalization
route wants the CUT presentation `Scut = R[Ã]/(mult(Ã)−B_univ)`. **`Scut = Sred` ⟺ the cut ideal
`(mult(Ã)−B_univ)` is RADICAL** (⟺ `F_E` reduced) — genuinely-new content, no engine/Mathlib lemma. This
reducedness is LOAD-BEARING (if not radical, the trivialization connects to a non-reduced object — a hole).

**Routed to pen-and-paper (thread 16)** to adjudicate the truth-value (is the cut ideal radical / `F_E`
reduced?) via exact algebra (Gröbner on the anchor + general argument) + decorrelated Codex, and certify
the Lean-buildable mechanism (route (a) direct-radical vs (b) deferred-via-F_E-reduced) — BEFORE any
formaliser builds the R2-3 AlgEquiv. Don't build on an unproven reducedness.

## THREAD 16 CERTIFICATE (pen-and-paper, 2026-06-24) — cut ideal RADICAL / F_E REDUCED; route (b)

Clean verdict (no hedge): `I_E = (mult(Ã)−E)` is RADICAL, `F_E = k[Ã]/I_E` REDUCED, for every N≥1 / dim
vector / target (depends only on rank E). Certified: Singular `primdecGTZ`+`radical` over ℚ on 11 cases
(anchor `(2,2,2)r1` + generic-E + N=3 `(2,2,2,2)` + `(3,2,3)`/`(2,3,2)`/`(1,2,1)` + E=I + r=0 + `(3,3,3)r1`)
— ALL radical, NO embedded/nilpotent primes; reducible + non-equidim for low r but always reduced. Component
count = type-A rank-pair rule. Decorrelated xhigh Codex converged + predicted the `(3,3,3)` data.

**Mechanism (load-bearing): reducedness INHERITED from the reduced ambient rank locus `Z_r` (type-A quiver
rank locus, known reduced — Buch–Fulton / Kinser–Rajchgot) via faithfully-flat local triviality.** NOT
smoothness/CM (fibre non-equidim/non-CM for low r — that route is wrong).

**Correction (important):** `sigmaIdeal = sInf(orbitIdeals) = vanishingIdeal` is radical-but-**REDUCIBLE**
on the chain (`Σ̄^1 = {detA₁·detA₂=0}`, 2 comps); prime ONLY on the single-matrix base `dStratum`. The
R2-2 prompt's "sigmaIdeal prime over IsAlgClosed" was wrong; the fix removes the worried tension.

**ROUTE (b), deferred — recommended (don't do route a / up-front primary decomp):**
1. R2-3 AlgEquiv `S ≅ₐ[R] R ⊗_k F_E` (endpoint normalization).
2. `Sred = (P/sigmaIdeal)[1/ΔP]` reduced — engine `vanishingIdeal_isRadical` (`NullstellensatzCodim:69`).
3. `Sred ≅ S` ⟹ `R⊗F_E` reduced ⟹ (k→R faithfully flat, char 0) `F_E` reduced ⟹ `I_E` radical.
So `Scut = Sred` is the CONCLUSION. Cleanest new lemma: the radical-collapse of `MultComorphism` pt 4
(`fibreGenIdeal = radical(fibreGenIdeal) = vanishingIdeal(fibre)` — the `radical(...)` wrapper drops).

**Confirmed engine handles:** `vanishingIdeal_isRadical` (NullstellensatzCodim:69),
`vanishingIdeal(fibre)=radical(fibreGenIdeal)` (MultComorphism pt4), `sigmaIdeal=vanishingIdeal`
(SigmaComponents:130). **One open dependency to pin:** the Mathlib tensor-with-a-field reducedness-descent
`F_E reduced ⟸ R ⊗_k F_E reduced` (char 0 ⟹ standard; `Algebra.TensorProduct` / faithfully-flat IsReduced).

**NEXT: R2-3 (thread 17)** — the endpoint-normalization AlgEquiv + the route-(b) reducedness chain. The
recon's HIGH-risk rung, now DE-RISKED (reducedness certified true; mechanism + handles confirmed). Then
R2-4 (flat/going-down, one-liner) → R2-5 (height) → R2-6 (+C assembly).

## R2-3a LANDED + R2-3b DECOMPOSED (thread 17 → thread 18, 2026-06-24)

**R2-3a — the route-(b) reducedness chain is BANKED, conditionally** (`Core.FibreReducedTrivialization`,
green/sorry-free/axiom-clean `[propext, Classical.choice, Quot.sound]`; aggregated `ef9b78c9`; controller
fidelity-read PASS). Three headlines, ALL wired against the deep product iso `e : S ≃ₐ[k] R ⊗_k F_B` +
`IsReduced S` as **explicit hypotheses** (not sorry, not axiom):
- `isReduced_of_tensor` — the tensor-with-a-field reducedness descent (the one pinned Mathlib dependency
  thread 16 flagged), CLOSED OUTRIGHT via `Algebra.TensorProduct.includeRight_injective` +
  `isReduced_of_injective` (needs only `[Nontrivial R]`, not char 0 / faithful flatness).
- `fibreGenIdeal_isRadical_of_trivialization` — the full chain (S reduced → R⊗F reduced → F reduced →
  `fibreGenIdeal` radical).
- `vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization` — the radical-collapse of MultComorphism pt4.

**Honest current status (the crux):** the ENTIRE bundle-shift `codim(fibre) = cCodim + δ` now rests on
the SINGLE open object `e` — the deep product trivialization. Everything else is banked: G1, G2-1, G2-2,
R2-3a (this conditional chain), and the engine codim `cCodim d r`. `e` is certified TRUE on paper (thread
16). The expedition either (a) builds `e` and fully discharges `BundleShiftInterface`, or (b) closes with
`e` as the single named open hypothesis — a clean honest reduction, recorded for end-of-expedition review.
**No downstream result discharges `BundleShiftInterface` on `e` until R2-3b proves it.**

**R2-3b decomposition** (Codex build order, `threads/17/codex/algequiv-answer.md` — "one tide should not
aim for the full deep iso"):
- **R2-3b-1+2 (thread 18, NEXT/in-flight):** the deep chart ring `Sred = Localization.Away(ΔP) ⧸ IadDeep`
  for general `d` (the engine's `basePresentationEquiv`/`SchurLoc` are N=1 only — genuinely new) + the
  `RepCoord`↔stratum-coord/endpoint bridges + the localized base→total map (`multComap` /
  `IsLocalization.Away.mapₐ` / `Ideal.quotientMapₐ` ∘ `basePresentationEquiv.symm`) giving `Sred` its
  `SchurLoc`-algebra structure. The foundational rungs.
- **R2-3b-3:** the endpoint-normalization AlgEquiv on the UNQUOTIENTED poly ring over arbitrary `R`
  (`aeval` substitution `Ã₁=A₁H⁻¹, Ã_N=L⁻¹A_N` via `AlgEquiv.ofAlgHom` + explicit inverse — avoid
  `baseChangeAlgEquiv`'s `[Infinite k]` baggage).
- **R2-3b-4 (the hard rung):** the normalized product iso DESCENDS to the reduced chart quotient
  (`Sred ≃ₐ[R] R ⊗_k F_E`) — discharges R2-3a's hypothesis `e`. Codex: "that leaves one precise missing
  rung." Walls Codex flagged: `RepCoord (dStratum q p)` ↔ `Fin p × Fin q` bridge; endpoint indexing at
  N≥1; `IsScalarTower`/localization instances around `SchurLoc`; `multComap` maps base `sigmaIdeal` into
  the deep one; avoid the circular `sigmaIdeal ≤ fibreGenIdeal`.
- Then **R2-5/R2-6/G3/G4** as before (height-additivity → +C assembly → lift via G1 → discharge the
  interface). The full reviewer + decorrelated Codex soundness gate lives at the DISCHARGE (G4), not the
  conditional pre-builds.

## EXPEDITION OUTCOME (2026-06-24) — WALL at R2-3b-4; Lemma 4.6 geometry REDUCED to a certified residual

**The planned determinantal-trivialization route does NOT close Lemma 4.6's geometry in Lean at v4.29.**
R2-3b-4 (the deep product iso `e`) walled at the mandatory SPECIFY checkpoint — *before* any grind — on a
**certified, decorrelated-Codex-concurred circularity** (thread 20 + its xhigh Codex + the prior thread-17
Codex all locate the same obstacle; the controller independently verified the logic). This is a negative
deliverable, not a failure: the geometry is reduced to a single, precisely-located, certified-true residual,
with everything else machine-checked.

**The circularity (why `e` cannot be built as a Lean *strategy*).** The iso `e : Sred ≃ₐ SchurLoc ⊗_k
FibreAlg d E` can hold only if `SchurLoc ⊗_k FibreAlg d E` is reduced (it is `≅` the reduced `Sred`), which
forces `FibreAlg d E` reduced ⟺ `fibreGenIdeal d E` radical. So **any genuine `e` proves the radicality as
a byproduct** — `e` is *equivalent* to the radicality, not a path to it. Concretely: the forward map
`Sred → SchurLoc ⊗ FibreAlg` is well-defined only given `sigmaIdeal d r ≤ ker φ` (the rank/pointwise facts
give only `≤ (ker φ).radical`; strengthening = the radicality, = thread-17's `sigmaIdeal ≤ fibreGenIdeal`
circularity); the reverse map's injectivity forces `FibreAlg d E` reduced. Route (b) — "derive `FibreAlg`
reduced *from* `Sred` reduced *via* `e`" — is circular as a Lean construction. (The thread-16 *mechanism*,
"reducedness inherited via faithfully-flat local triviality", is mathematically valid — but that *local
triviality IS* `e`, so it cannot be the Lean route to `e`.) The height-via-radical-insensitivity escape
(`codim(fibre) = height(fibreGenIdeal)` needs no radicality) does **not** dodge `e` either: the
height-additivity `codim_{Σ̄^r}(fibre) = δ` routes through the *same* flat trivialization (going-down).

**THE RESIDUAL (single, named, certified TRUE).** The deep product trivialization `e` ⟺ the radicality of
the deep fibre ideal `fibreGenIdeal d E` (`N ≥ 1`, normal form `E`) ⟺ the **deep flat/smooth
trivialization of `Σ̄^r` over its rank base**. Certified TRUE pen-and-paper (thread 16: Singular
`primdecGTZ` on 11 cases + the type-A rank-locus reducedness mechanism, Buch–Fulton / Kinser–Rajchgot). Its
Lean proof needs a **deep localized flat trivialization** — a ≥2-module from-scratch AG sub-project; the
engine's determinantal machinery (`basePresentationEquiv`, `SchurLoc`) is **`N = 1` only**, and the deep
(`N ≥ 1`) product's rank ideal *factors*, so the N=1 graph/Schur trick does not port. This is the same wall
located progressively by threads 01 (morphism-fibre-dim, ~8–15 modules), 09 (G2a flatness NO-GO), 14/15
(R2-2 = L), 16 (the "one dep" that is in fact this) — now pinned exactly.

**BANKED, unconditional + axiom-clean** (the expedition's positive deliverable — the engine *toward* the
bundle-shift): `Core.DeepChartRing` (the deep chart ring `Sred` for general `d`; `isReduced_Sred`; the
non-circular `deepBaseComap_sigmaIdeal_le`; `schurToSred` + the `SchurLoc`-algebra structure),
`Core.EndpointNormalization` (`gaugeEquiv` + `gaugeEquiv_multPoly`, the `baseChange` gauge over arbitrary
`CommRing`), and `Core.FibreReducedTrivialization` (R2-3a: the route-(b) reducedness chain + radical-collapse
+ `isReduced_of_tensor`), all conditional on `e`. The day a deep-flat-trivialization tide proves `e` (or the
radicality directly), the chain closes with **zero further reducedness work** — every consumer of `e` is
already proved against it, and `hSred` is already discharged (`isReduced_Sred`).

**HONESTY (no overclaim).** `BundleShiftInterface.cited_bundle_shift` in `DLN.RlctPayoffGeneral` remains an
**Assumed/Cited interface — NOT discharged.** Lemma 4.6's geometric content (`codim(fibre) = C + δ`) is
**not proved in Lean**; it is reduced to the named residual above. Nothing is named to suggest otherwise.

**THE FORK (operator decision — surfaced, signal-and-wait).** (a) **Close the expedition here** — bank the
engine + the conditional chain + the precisely-located certified residual as the deliverable; `Lemma 4.6
geometry` stays reduced-to-residual on the ROADMAP. (b) **Authorize a deep-flat-trivialization sub-project**
— a substantial fresh expedition (deep localized flat trivialization / type-A rank-locus reducedness in
Lean; likely needs scaffolding Mathlib v4.29 lacks). **Controller recommendation: (a).** The residual is a
genuine new layer, not "filling the current one"; it deserves its own scoping, not an autonomous launch on
top of a walled route. The current result — a certified, Codex-concurred residual with the entire
surrounding engine machine-checked — is strong and honest.

## PHASE 2 (2026-06-24) — operator authorized the follow-on; RECON-FIRST (map math + Lean-API paths)

Operator chose the AMBITIOUS fork: **build the residual.** Directive: "work out the details, plan both
the math paths AND the lean API pathways; you hold the broader picture, ask teammates to map details."
So Phase 2 is **recon-first**, not a blind tide at the wall.

**Controller's broader-picture hypothesis (the lead candidate to stress-test):** the residual may be best
attacked NOT as the (circular) trivialization, but as the **SMOOTHNESS / SUBMERSION** statement — `mult`
is a submersion onto `Σ̄^r` on the rank-`r` chart (`d(mult) = Σ A_N···(dA_i)···A₁` full-rank onto the
tangent of the rank locus) ⟹ the fibre is **smooth** of dimension `dim Rep − C − δ` ⟹ **reduced + codim
`C + δ`**, potentially **closing the whole thing directly and bypassing the iso `e`**. Crucially the engine
ALREADY built the smoothness/Jacobian/regular-dimension machinery for the ORBIT codim (Voigt discharge):
`Core.MatrixKaehler.derivMatrix_mul_apply` (the derivative of a matrix PRODUCT — literally `d(mult)`),
`Core.SmoothPointRegular` (`smooth_point_isRegularLocalRing`, cotangent finrank), `Core.SmoothLocalRelative
Dimension`, `Core.CotangentJacobian`, `Core.JacobianTrdeg`. The question is whether this ORBIT machinery
ports to the FIBRE of `mult`.

**Recon dispatched (parallel, decorrelated, read-only — no Lean writes):**
- **thread 21 (`scout-residual-math`):** enumerate + RANK the math routes — the submersion/smoothness route
  (evaluate hardest: is `d(mult)` surjective on the chart? does smooth ⟹ reduced + codim, bypassing `e`?
  how does the reducibility of `Σ̄^r` interact?), the type-A rank-locus reducedness route, others.
  Decorrelated Codex.
- **thread 22 (`scout-residual-leanapi`):** map the engine's smoothness/Jacobian machinery (does it port
  orbit→fibre?) + Mathlib v4.29 (Jacobian⟹smooth criterion, regular⟹reduced, flat/going-down) — reusable
  handles, gaps, module-count per route. Decorrelated Codex.

**Next:** synthesize the two findings into a concrete plan (the chosen math route + the Lean-API rung
ladder), present it, then execute via serial formaliser tides (one write-tide; SPECIFY-first + checkpoints).

## PHASE 2 RECON CONVERGED → the HEIGHT-DIRECT route (build it, multi-round)

Both scouts (21 math, 22 Lean-API) + their decorrelated Codices **converge**, and the operator's steer
(2026-06-24) is to stop declaring walls and **break the hard thing into manageable pieces while holding
the big picture — let the sea rise**. The reframe:

**The codim is RADICAL-INSENSITIVE.** `codimRepCanonical(fibre) = height(vanishingIdeal(fibre)) =
height(radical(fibreGenIdeal)) = height(fibreGenIdeal)` — independent of whether `fibreGenIdeal` is
radical. So the **thread-20 wall (the scheme iso `e` / cut-ideal radicality) is OFF the critical path for
the codim** — it was a red herring; the RLCT payoff needs only the codim. The R2-3b-4 "WALL" does not
block the goal.

**The singularity at `E` is dodged by working at GENERIC points.** `d(mult)` rank drops at `E` (the fibre
is reducible + singular there — scout 21's Jacobian), so global smoothness is false. But every variety is
**generically smooth** (char 0): read the dimension at a **generic point of each top component**, where
`d(mult)` has full rank `C + δ` and the tangent space `= ker d(mult)` has dim `card − C − δ`. No global
smoothness, no flatness, no trivialization `e` needed.

**HEIGHT-DIRECT rung ladder (`codimRepCanonical(fibre d E) = C + δ`):**
- **H1 (retarget):** `codimRepCanonical(fibre d B) = height(fibreGenIdeal d B)` unconditionally
  (radical-insensitive; `MultComorphism` pt4 + `height(radical I) = height I`). Banks the decoupling.
- **H2 (differential):** `dmult` via `MatrixKaehler.derivMatrix_mul_apply` (product rule
  `d(A_N···A₁) = Σ A_N···dA_i···A₁`) — the brick (none exists yet).
- **H3 (generic Jacobian rank):** at a generic point of each top component of the fibre, `d(mult)` has
  rank `C + δ` (tangent `= ker d(mult)`, dim `card − C − δ`) — linear-algebra/combinatorial, the engine's
  strength; reuses `CotangentJacobian.finrank_cotangentSpace_eq_finrank_ker_jacobian` (tangent = ker
  Jacobian, NO smoothness needed).
- **H4 (local dim = tangent dim at a generic smooth point):** generic smoothness ⟹ component dim =
  `card − C − δ` (reuse `SmoothPointRegular`/`SmoothLocalRelativeDimension`, both fully generic per scout 22).
- **H5 (assembly):** `dim(fibre) = max_component = card − C − δ` ⟹ `codim = C + δ`; reducibility via Brick A
  (`minimalPrimes_sigmaIdeal_eq`). Combine with H1.

Reusable, LANDED: `MultComorphism`, `SigmaCodim` (`codim Σ̄^r = C`), the thermometer
(`DeterminantalStratumDim`, `dim Mat^{rk=r} = δ`), the going-down/affine-domain height engine, the gauge
(`EndpointNormalization`), `Sred` (`DeepChartRing`). Module estimate (scout 22): ~4–6.

**Discipline (operator steer):** build it, multi-round; explore details per-rung as reached, not as one
upfront gate; break a hard piece smaller rather than declaring a wall. Starting H1+H2 now.

## H3 CERTIFICATE → route REFINED to the FIBRATION dim count (thread 25, 2026-06-24)

H1+H2+H3a LANDED (green, axiom-clean): `codim(fibre)=height(fibreGenIdeal)` (H1, radical-insensitive);
`d(mult)` + Jacobian-entry brick (H2); the fibre Jacobian + `finrank(ker)+rank=card` + tangent=ker (H3a,
`Core.FibreJacobian`). The pen-and-paper (thread 25) then **certified** `dim mult⁻¹(E) = card−C−δ` two
exact ways (Singular Krull dim, 13 cases incl. N=3; sympy Jacobian rank) and **refined the route**:

- **PRIMARY route = the FIBRATION dim count** (not the per-component Jacobian rank): `mult|_{Σ̄^r} : Σ̄^r ↠
  Mat^{≤r}` is dominant, `E` generic (rank-exactly-r), so generic-fibre-dim ⟹ `dim F = dim Σ̄^r − dim
  Mat^{≤r} = (card−C) − δ`. Reuses LANDED `dim Σ̄^r = card−C` (`SigmaCodim`) + `dim Mat^{≤r} = δ`
  (thermometer `DeterminantalStratumDim`). **No flatness** (generic flatness is free) — sidesteps the
  thread-20 wall AND the per-component rank bookkeeping. `+C` = Σ̄^r codim (Kostant/Ext), `+δ` = the target
  rank-locus dim.
- **Scope correction (load-bearing):** the fibre is REDUCIBLE; `rank = C+δ` holds only at a generic point
  of a **TOP** component (lower-dim components carry higher rank, up to `d_N·d_0`). So the Jacobian-rank
  route (H3b/H3c) is dimension-dependent + fiddly — **superseded** for the codim by the fibration. H3a
  stays banked (a clean reusable module; `rank=C+δ` is a corollary via `card−dim`, not the target).
- **Kill-condition:** `r ≤ min_i d_i` (E realizable / dominance). Only **generic-reducedness of the top
  component** needed (NOT global reducedness — thread-20 stays off-path). Decorrelated Codex confirmed the
  fibration count + corrected a false tangent-bound. Certificate: `threads/25-jacobian-rank-cert/certificate.md`.

**REMAINING critical path (H4→H5→discharge):**
- **H4 — `varietyDim(fibre over E) = card − C − δ`** via the fibration (dominant `mult|_{Σ̄^r} ↠ Mat^{≤r}`
  + the engine's dimension toolkit: `AffineNoetherRank` (`ringKrullDim = trdeg`), `AffineDomainDimension`
  (equidim `height p + dim(R/p) = dim R`), the catenary `NullstellensatzCodim`, + landed `dim Σ̄^r`, `dim
  Mat^{≤r}`). The substantive AG rung — break into pieces, build, don't wall.
- **H5 — catenary closer:** `height(fibreGenIdeal) = card − varietyDim(fibre) = C+δ` (min-prime / top-comp
  dim, reducibility via Brick A `minimalPrimes_sigmaIdeal_eq`), combine with H1 ⟹ `codim(fibre)=C+δ`. Then
  G4: discharge `BundleShiftInterface`.

## ROUTE B KILLED (circular) → ROUTE c (homogeneous sweep) is the path (thread 27→28, 2026-06-24)

**H4 landed the engine-side assembly + the conditional capstone** (`codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds` + the G1-transport `..._at_witness`, committed in probe modules; base-δ bricks + equidim + the H5 min-over-components closer in `FibreDimFibration`/probes — all green/axiom-clean), reducing `codim(fibre)=C+δ` to per-component dimension facts. Thread 27 (pen-and-paper, 2 decorrelated Codices, 9-case exact) then **killed route B and certified route c:**

- **Route B (Jacobian rank ≥ C+δ) is CIRCULAR.** At a generic SMOOTH point, `rank(d mult_A) = card − dim F_α`
  is rank-nullity (an IDENTITY), so "`rank ≥ C+δ` on every component" ⟺ "`dim F_α ≤ card−C−δ`" = the
  conclusion. The `+C` has NO independent handle (`rank = δ + codim Ō_M` is EXACTLY refuted); the bound is
  NON-uniform (fails at singular sub-loci). The δ-part (`image ⊇ T_E Mat^{≤r}`, orbit-tangent) is clean but
  insufficient. **Do not build route B.** (The factor-rank strata are NOT the components — the recurring confound.)
- **Route c (the equivariant homogeneous SWEEP) is the clean general argument — BOTH directions at once,
  flatness-free, no Jacobians/smoothness/components.** `H = GL_{d_N}×GL_{d_0}` acts through the end vertices
  (`mult_smul`); `Mat^{=r} = H·E` one orbit (`exists_baseChange_of_rank_eq`) ⟹ `Σ^r = H·F`; the action map
  `H×F → Σ^r` has `Stab_H(E)`-coset fibres (homogeneous ⟹ uniform, NO flatness) ⟹ **`dim Σ^r = δ + dim F`**;
  density `dim Σ^r = dim Σ̄^r` (Step C, Cited LR 4.4/4.5) + landed `dim Σ̄^r = card−C` (`SigmaCodim`) ⟹
  **`codim F = C+δ`**. Reuses landed engine (`mult_smul`, `exists_baseChange_of_rank_eq`, G1, the δ
  thermometer, `SigmaCodim`, the orbit-dim machinery `OrbitImageDim`/`JacobianTrdeg`).
- **The ONE new rung** = Step B (the homogeneous-sweep dim identity, an orbit-dimension count on the engine
  substrate — NOT a general fibre-dim theorem, NOT the flatness wall). **The ONE Cited bridge** = Step C
  (`dim Σ^r = dim Σ̄^r`, density; try to prove it cheaply since `varietyDim` IS closure-dim, else name it).
  So route c reduces `BundleShiftInterface` from FULLY Cited to **proved modulo one standard density fact**.

**NOW (thread 28):** the route-c formaliser tide — Step B (sweep) + Step C + assembly + G1 lift ⟹
`codimRepCanonical(fibre d B) = C+δ` (Core). Then a final DLN tide discharges `BundleShiftInterface` (G4,
full reviewer + Codex gate). The H4 Jacobian capstones are off the proof-path (route B circular) but the
base-δ/equidim/`SigmaCodim`/closer bricks are route c's substrate. Cert: `threads/27-.../certificate.md`.

## VERDICT — route c collapses to `cited_bundle_shift`; the `+δ` is the exhaustively-confirmed residual (thread 28, 2026-06-24)

The route-c "one new rung" (the sweep dim-identity `varietyDim Σ^r = δ + varietyDim F`) is **(b) Mathlib-
absent AND logically equal to `BundleShiftInterface.cited_bundle_shift` itself** — engine-grounded scout
verdict + decorrelated Codex (`threads/28-.../sweepdim-reachability.md`). The engine computes `varietyDim`
exactly ONE way: for a SINGLE `G_d`-orbit, `Z_M = dim G − dim Stab` via `orbitPullback M : R → O(G_d)`
whose range is a DOMAIN (`OrbitPullbackDim:74`→`AffineNoetherRank:81`→`VoigtDischarge:38`). `Σ^r = H·F` is
an **associated bundle** `H ×^Stab F` (a *family* of H-orbits; `F` reducible, `O(F)` not a domain), so
the sweep needs **product-trdeg** `trdeg(O(H)⊗O(F))` — absent from Mathlib v4.29 (the engine has only
tower-additivity). And Step D (`varietyDim Σ̄^r = card−C`) is ALSO not landed (the catenary bridge is
prime-gated, `Σ̄^r` reducible). Both gaps isolated as named hyps `hSweepDim`/`hFcat` in
`Core.FibreCodimSweepAssembly` (the assembly arithmetic machine-checked). Route c **does not shorten the
path** — its rung IS the bundle shift, reframed.

**EXHAUSTIVE finding (5+ routes, 3+ decorrelated Codices):** the `+δ` — the geometric heart of LR Lemma
4.6, `codim(fibre B) = codim Σ̄^r + δ`, = `cited_bundle_shift` — is irreducibly a **~8–12-module from-scratch
AG sub-project**: the exact-rank chart trivialization `R_total ≃ R_base ⊗ F_E` + flatness + going-down (the
threads 09/14/20/R2-3b lineage). It is walled on EVERY route: flatness (mult not globally flat), Jacobian
(circular — `rank = card−dim` at a smooth pt; the `+C` is a generic-lci lemma ≈ the thread-20 radicality
wall), homogeneous-sweep (collapses to itself, product-trdeg absent). A general product/fibre-dim theorem
is ≥ comparable (10–18 modules) and still wouldn't handle the Stab quotient. This is thread-01's original
blocker, now confirmed from every angle. NOT a premature wall-call — a thoroughly-decomposed, multiply-
verified structural fact.

**BANKED (the expedition's positive deliverable — enormous bedrock + the precise reduction):** the
radical-insensitive retarget `codim(fibre)=height(fibreGenIdeal)` (H1); the differential `d(mult)` +
Jacobian (`MultDifferential`/`FibreJacobian`); the per-component→codim assembly + the conditional capstone +
G1-transport; the base-δ/equidim bricks; the sweep structure `Σ^r = H·F` (`EndBaseChangeSweep`); the
decomposition theorem `rank(d mult_A) = δ + dim π_BR(image)` (thread 27 §6b); and `FibreCodimSweepAssembly`
reducing `codim=C+δ` to the two named hyps. So `BundleShiftInterface` is reduced from **fully Cited (the
whole of Lemma 4.6's geometry)** to **one isolated, certified-true dimension interface** with all
surrounding machinery machine-checked.

**FORK (operator decision — surfaced):** (a) accept `cited_bundle_shift` (= `hSweepDim`/`hFcat`) as the
named Cited residual — close with `codim=C+δ` proved modulo one isolated certified interface, a strong
hole-free result; or (b) commit the ~8–12-module exact-rank chart-trivialization + flatness + going-down
build (the stalled lineage, eyes open about cost). The RLCT payoff `rlct = ½·codim` stays Cited (Aoyagi)
regardless; `BundleShiftInterface` stays Assumed until (b) is built.

## ROUTE-C INTEGRATED + operator chose to BUILD hSweep (2026-06-24)

`codimRepCanonical(fibre d B) = C+δ` for rank-r B is now **PROVED IN LEAN modulo exactly TWO named
residuals** (`Core.RouteCAssembly.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep'`, aggregated
`edaa1573`, green/axiom-clean; controller fidelity-read PASS — the conditional bank is honest, no
hypothesis = the conclusion, the thread-27 circularity trap avoided):
- **`hSweep`** = the homogeneous-sweep dim identity `varietyDim Σ^r = δ + varietyDim F` (the `+δ` bundle
  shift = `cited_bundle_shift`).
- **`hClosure`** = `varietyDim Σ^r = varietyDim Σ̄^r` (the ONE Cited density bridge, LR 4.4/4.5).
The reducible-locus catenary hyps are PROVED (`Core.RadicalCatenary`, unconditional in radicality); the
sweep structure `Σ^r = H·F` is proved (`Core.EndBaseChangeSweep`).

**Operator chose (b): BUILD `hSweep` unconditionally.** The non-circular route (thread 29 pen-and-paper +
Codex): **generic freeness** (at a generic flat-locus point — Grothendieck's lemma, standard + reusable,
Mathlib v4.29-ABSENT, ~3–5 modules) + a **relative fibre-dimension formula** (~2–3 modules, reuses the
landed going-down `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`) + **GL×GL homogeneity
transport** (G1, LANDED — generic-point fibre dim ⟹ E's fibre dim). This DODGES the R2-3b-4
reducedness-circularity (only fibre *isomorphism*, no scheme iso `e`) AND the absent product-trdeg. The
flatness-at-E route is circular (re-enters R2-3b-4); generic freeness is the non-circular substitute.

**Build ladder (b):** (1) generic freeness [the load-bearing new rung] → (2) relative fibre-dim → (3)
transport (landed) ⟹ `hSweep` → plug into `..._of_sweep'` ⟹ unconditional `codim F = C+δ` (modulo
`hClosure`) → (4) hClosure (prove via density/openness, or keep Cited) → (5) G4: discharge
`DLN.BundleShiftInterface.cited_bundle_shift` (full reviewer + Codex gate). Next tide: generic freeness,
SPECIFY-first (thorough Mathlib check — confirm it's genuinely absent — + the dévissage/filtration proof).

## CENTRAL RESULT ACHIEVED — codim(fibre)=C+δ PROVED, zero-cite (2026-06-25)

The hSweep build (option b) landed end-to-end. **`codimRepCanonical (fibre d B) = (cCodim d r).toNat +
r·(d_N + d_0 − r)`** for any rank-`r` `B` is **PROVED IN LEAN with no Cited interface for the geometry** —
`Core.FibreCodimFinal.codimRepCanonical_fibre_eq_cCodim_add_shift`, minimal-hyp form (only
`[IsAlgClosed][CharZero]` + `(kostantPartitions d r).Nonempty` + `B.rank = r`), tip `538dea7a`.

**Verified (controller, independent of the tides' green reports):** whole-library `./scripts/lb` green
(3763 jobs); `scripts/sorries` = 0 sorry / 0 axiom / 0 native_decide; `#print axioms
codimRepCanonical_fibre_eq_cCodim_add_shift` = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

**Double-gated by decorrelated, controller-commissioned review** (a builder-spawned review was treated as
supporting evidence, not the gate):
- **#67 — `e` (chartLocalizedAlgEquiv) fidelity:** PASS. Honest, non-vacuous, axiom-clean; both descents
  ride only `vanishingIdeal` — the R2-3b-4 generator-ideal wall structurally avoided.
- **#68 — codim↔paper fidelity:** PASS. Matches LR Lemma 4.6 (`lem:rank_vs_fibers`): `cCodim`=`C` (Cor 3.5
  form), shift=`δ`, `Fin(N+2)` depth correct (no off-by-one), achievability hyp = the paper's `r ≤ min d`,
  `(2,2,2)` checked by hand+`decide`, NO overclaim (codim, not rlct). `reviews/68-codim-final-fidelity.md`.

**How the R2-3b-4 wall fell (route-β).** The residual `e` — the deep flat/smooth trivialization that the
§EXPEDITION OUTCOME left as "certified TRUE but circular as a Lean route, a ≥2-module from-scratch AG
sub-project" — was built directly as the **localized chart `AlgEquiv`** over the rank-=r ring,
**radical-insensitive (vanishingIdeal-side) throughout**, so the "build `e` ⟺ prove the radicality `e`
would establish" circularity never arises. Seams: A (target-side eval + chart-eval lemma), B (principal-open
zero-test), C (Ψ descent → `chartPsiLoc`, incl. the det-assembly `chartPsiAeval ΔPdeep = detSchurS`-image,
a unit), D (Φ descent → `chartPhiLoc`), E (`AlgEquiv.ofAlgHom` glue + gauge-group-law round-trips, the
matrix-inverse wall sidestepped at the units level). Then `Core.SourceNoDrop` (`hsig`) + the wiring → hSweep
→ route-c assembly (`hClosure` in-repo).

**Process notes (banked lessons).** (1) A per-module green build is NOT a whole-library green build —
aggregating `FibreCodimFinal` surfaced a NAME COLLISION (it reused the bare name of the older CONDITIONAL
min-primes theorem); fixed by renaming the conditional one `…_of_height_bounds`. The controller re-verified
every gate (build / sorries / `#print axioms`) itself rather than trusting "green" reports. (2) Push-safety:
a tide's `git push` silently failed for several commits (local-ahead, unpushed) — the controller backed them
up via fetch+push each cycle. (3) The minimal-hyp tightening (#69) dropped `hp/hq/hN` (derived from `h` /
vacuous), a strict strengthening that preserves fidelity.

**Caveats (next to the claim).** `k : Type 0` (the DLN payoff field — ℝ/ℂ; universe lift roadmap-able);
the `kostantPartitions`-nonempty achievability hypothesis is carried (reviewer-confirmed = `r ≤ min d`,
non-vacuous); **`rlct = ½·codim` stays Cited** (Aoyagi/Watanabe) — the geometric codimension is the new
zero-cite content.

**DESTINATION REALIZED (#52 discharged, 2026-06-25).** `DLN.BundleShiftDischarge` proves the bundle shift
from Core (`bundleShift_of_core`, via `FibreCodimFinal` + `SigmaCodim` Brick A); the rewired payoff
`rlct_lossDLN_eq_half_cCodim_add_shift` DROPS the geometric interface and rests on ONLY the Cited Aoyagi
`RlctInterface`. `#print axioms` = `[propext, Classical.choice, Quot.sound]` (geometric half genuinely
Proved); reviewer-g4 PASS (decorrelated + Codex). The full chain — geometry `codim = C+δ` zero-cite, wired
into the RLCT payoff `rlct = C/2` with ONLY the analytic Aoyagi `rlct = ½·codim` equality Cited — is the
destination, realized at `k : Type 0` (the DLN field; covers ℂ). The G1 lift is subsumed by `FibreCodimFinal`.

**Remaining.** #54 — θ-count fidelity for `(3,3,3)` (separate follow-up). Opening/merging PR #10 is
operator-gated.
