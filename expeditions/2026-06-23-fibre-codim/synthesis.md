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

## Process

Controller in a worktree ⟹ teammate `isolation: worktree` collapses to this shared worktree (serial).
The fresh-worktree baseline build hit the mathlib-clone wall (>10-min bash cap) — Uplift A again;
deferred (no tide pending the fork).
