   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019efbd4-ff0e-7391-a56d-0ca4c4904ff1
--------
user
# Codex consult — the radical ideal-split: tractable, or needs absent machinery? (Lean v4.29)

Greenlit to grind the make-or-break radical ideal-split (route (c), thread 31). I need a sharp
read on tractability BEFORE sinking the module budget, and which ring the normalizing gauge lives
over. STOP→fallback (cite `hSweep`) is authorized if it needs a Mathlib-absent sub-theorem.

## The architecture (LANDED in the engine)

- `ΔPdeep` = the top-left r×r minor of `of (multPoly d)` (the TOTAL-ring pivot minor), in
  `MvPolynomial (RepCoord d) k`.
- `Sred = Localization.Away ΔPdeep ⧸ IadDeep`, where `IadDeep = (sigmaIdeal d r).map (algebraMap
  (MvPolynomial (RepCoord d) k) (Localization.Away ΔPdeep))`. `sigmaIdeal` = vanishing ideal of the
  rank-≤r product locus Σ̄^r (radical, alg-closed).
- `SchurLoc = Localization.Away detSchurS` (the BASE chart ring, a localized polynomial ring in δ
  vars, `dim = δ`). `basePresentationEquiv : Localization.Away detPivotPoly ⧸ Iad ≃ₐ[k] SchurLoc`.
- `baseLocMap : Localization.Away detPivotPoly →ₐ[k] Localization.Away ΔPdeep` (the base→total
  localized ring map, `IsLocalization.Away.mapₐ deepBaseComap`).
- `schurToSred : SchurLoc →ₐ[k] Sred` makes `Sred` a `SchurLoc`-algebra.
- I have LANDED `schurComplement_normal_form` (network-free): `L⁻¹·M·H⁻¹ = diag(I_r,0)` for
  `M = [[Δ,B12],[B21,B22]]`, `Δ` invertible, `B22 = B21 Δ⁻¹ B12`. And a gauge `gaugeEquiv` (an
  `AlgEquiv` of `MvPolynomial (RepCoord d) R`) for any coeff ring `R`, with `gaugeEquiv_multPoly`.

## The target (the split)

`ringKrullDim Sred = ringKrullDim SchurLoc + ringKrullDim FibreAlg = δ + ringKrullDim FibreAlg`,
where `FibreAlg = MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E`. Radical-level route:
`((gauge.map IadDeep).radical = splitBaseFibreIdeal.radical)`, then `Ideal.quotientEquivAlg` +
`ringKrullDim_quotient_eq_of_radical_eq` (LANDED) + the poly-extension dim.

## My ring confusion (resolve this first)

The normalizing gauge inverts the PIVOT minor. Two candidates for which ring it lives over:
(a) `SchurLoc` (the base — `detSchurS` is the base pivot), where I built my `endpointGauge`; or
(b) `Localization.Away ΔPdeep` (the total localization — `ΔPdeep` is the total pivot, which is the
    image of `detPivotPoly` under `deepBaseComap`).
`IadDeep` lives over (b). My `endpointGauge` is over (a). To gauge `IadDeep` I seemingly need the
gauge over (b), with blocks = images of the Schur blocks under `baseLocMap`. **Q1: is the gauge over
(b) the right object, and is it just `endpointGauge` transported along `baseLocMap`/`schurToSred`, or
do I rebuild it over (b) from `ΔPdeep`'s own pivot data?**

## The real questions

1. **Which ring for the gauge** (Q1 above) + the cleanest Lean shape to get a gauge that acts on
   `IadDeep`'s ambient ring `Localization.Away ΔPdeep`.
2. **Is the split `(gauge.map IadDeep).radical = splitBaseFibreIdeal.radical` tractable at v4.29, or
   does it need a Mathlib-absent sub-theorem?** Specifically the two containments:
   - `⊆`: the gauged `sigmaIdeal` generators (bordered (r+1)-minors of `multPoly`) become, after the
     Schur normalization, the "fibre" generators + the base δ-coordinate relations. Is this a finite
     explicit generator computation (tractable), or does it need a structural ideal-image theorem?
   - `⊇`: the harder direction (the R2-3b-4 wall was the forward map needing `sigmaIdeal ≤ ker`).
     At the RADICAL/dimension level, does `⊇` reduce to a height/dimension count (both ideals have
     the same height, both prime-ish → equal) that SIDESTEPS the explicit generator containment?
     I have `ringKrullDim_quotient_radical` (radical-insensitivity) landed.
3. **Is there a SHORTER dimension-only path** that avoids the explicit ideal-split entirely — e.g.:
   `Sred` is a `SchurLoc`-algebra (via `schurToSred`); if I can show `Sred` is module-finite or a
   localized-polynomial extension of `SchurLoc ⊗ (something dim 0)`... OR use that
   `Sred ≅ Localization.Away ΔPdeep ⧸ IadDeep` and compute `ringKrullDim` of the localized quotient
   directly via the LANDED determinantal/orbit dimension machinery (the engine already computes
   `dim Σ̄^r = card − C` and `dim Mat^{≤r} = δ`)? Could the chart dimension come from
   `dim Σ̄^r − dim(complement of chart)` or a localization-dim argument, WITHOUT building the split?
4. **Honest verdict**: is the radical ideal-split a ~2-3-module tractable grind, or is it the
   R2-3b-4 wall in disguise (needs the absent localized-quotient-interchange / structural ideal
   theorem)? If the latter, I STOP and cite `hSweep`. Be adversarial — I have a STOP→B authorization
   and would rather take a clean B than grind a wall.

Give me: the right gauge ring, the tractability verdict on each containment (or the height-count
sidestep), any shorter dimension-only path, and a clear "grind it (~N modules)" vs "STOP→B" call.

codex
I’ll read the local project instructions and the relevant Lean/exposition artifacts first, then I’ll give a tractability call grounded in what is actually present in this worktree.
exec
/bin/bash -lc "sed -n '1,220p' README.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 2 in 0ms:
sed: can't read README.md: No such file or directory

exec
/bin/bash -lc "sed -n '1,220p' CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 2 in 0ms:
sed: can't read CLAUDE.md: No such file or directory

exec
/bin/bash -lc "pwd && rg --files -g 'CLAUDE.md' -g 'README.md' -g '*.lean' -g '*.md' | head -200" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
split-tractability-prompt.md
rung2-lighter-path-prompt.md
rung2-regular-section-prompt.md
rung2-regular-section-answer.md
rung2-lighter-path-answer.md
route-choice-prompt.md
split-tractability-answer.md
noncirc-setlevel-prompt.md
noncirc-setlevel-answer.md
route-choice-answer.md

codex
This thread directory is mostly prompt/answer notes, so I’m moving up to the repo root to inspect the actual Lean engine and policy context.
exec
/bin/bash -lc 'git rev-parse --show-toplevel' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
2026-06-24T22:51:52.417439Z ERROR codex_app_server::bespoke_event_handling: request failed with client error: JSONRPCErrorError { code: -32000, data: None, message: "command execution approval is not supported in exec mode for thread `019efbd4-ff0e-7391-a56d-0ca4c4904ff1`" }
 exited 1:
2026-06-24T22:51:52.417739Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc 'git rev-parse --show-toplevel'`: CreateProcess { message: "Rejected(\"rejected by user\")" }
exec
/bin/bash -lc 'find .. -maxdepth 6 -name CLAUDE.md -o -name README.md -o -name lakefile.lean -o -name lake-manifest.json | head -100' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
exec
/bin/bash -lc "sed -n '1,240p' split-tractability-answer.md && sed -n '1,260p' route-choice-answer.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019efbd4-ff0e-7391-a56d-0ca4c4904ff1
--------
user
# Codex consult — the radical ideal-split: tractable, or needs absent machinery? (Lean v4.29)

Greenlit to grind the make-or-break radical ideal-split (route (c), thread 31). I need a sharp
read on tractability BEFORE sinking the module budget, and which ring the normalizing gauge lives
over. STOP→fallback (cite `hSweep`) is authorized if it needs a Mathlib-absent sub-theorem.

## The architecture (LANDED in the engine)

- `ΔPdeep` = the top-left r×r minor of `of (multPoly d)` (the TOTAL-ring pivot minor), in
  `MvPolynomial (RepCoord d) k`.
- `Sred = Localization.Away ΔPdeep ⧸ IadDeep`, where `IadDeep = (sigmaIdeal d r).map (algebraMap
  (MvPolynomial (RepCoord d) k) (Localization.Away ΔPdeep))`. `sigmaIdeal` = vanishing ideal of the
  rank-≤r product locus Σ̄^r (radical, alg-closed).
- `SchurLoc = Localization.Away detSchurS` (the BASE chart ring, a localized polynomial ring in δ
  vars, `dim = δ`). `basePresentationEquiv : Localization.Away detPivotPoly ⧸ Iad ≃ₐ[k] SchurLoc`.
- `baseLocMap : Localization.Away detPivotPoly →ₐ[k] Localization.Away ΔPdeep` (the base→total
  localized ring map, `IsLocalization.Away.mapₐ deepBaseComap`).
- `schurToSred : SchurLoc →ₐ[k] Sred` makes `Sred` a `SchurLoc`-algebra.
- I have LANDED `schurComplement_normal_form` (network-free): `L⁻¹·M·H⁻¹ = diag(I_r,0)` for
  `M = [[Δ,B12],[B21,B22]]`, `Δ` invertible, `B22 = B21 Δ⁻¹ B12`. And a gauge `gaugeEquiv` (an
  `AlgEquiv` of `MvPolynomial (RepCoord d) R`) for any coeff ring `R`, with `gaugeEquiv_multPoly`.

## The target (the split)

`ringKrullDim Sred = ringKrullDim SchurLoc + ringKrullDim FibreAlg = δ + ringKrullDim FibreAlg`,
where `FibreAlg = MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E`. Radical-level route:
`((gauge.map IadDeep).radical = splitBaseFibreIdeal.radical)`, then `Ideal.quotientEquivAlg` +
`ringKrullDim_quotient_eq_of_radical_eq` (LANDED) + the poly-extension dim.

## My ring confusion (resolve this first)

The normalizing gauge inverts the PIVOT minor. Two candidates for which ring it lives over:
(a) `SchurLoc` (the base — `detSchurS` is the base pivot), where I built my `endpointGauge`; or
(b) `Localization.Away ΔPdeep` (the total localization — `ΔPdeep` is the total pivot, which is the
    image of `detPivotPoly` under `deepBaseComap`).
`IadDeep` lives over (b). My `endpointGauge` is over (a). To gauge `IadDeep` I seemingly need the
gauge over (b), with blocks = images of the Schur blocks under `baseLocMap`. **Q1: is the gauge over
(b) the right object, and is it just `endpointGauge` transported along `baseLocMap`/`schurToSred`, or
do I rebuild it over (b) from `ΔPdeep`'s own pivot data?**

## The real questions

1. **Which ring for the gauge** (Q1 above) + the cleanest Lean shape to get a gauge that acts on
   `IadDeep`'s ambient ring `Localization.Away ΔPdeep`.
2. **Is the split `(gauge.map IadDeep).radical = splitBaseFibreIdeal.radical` tractable at v4.29, or
   does it need a Mathlib-absent sub-theorem?** Specifically the two containments:
   - `⊆`: the gauged `sigmaIdeal` generators (bordered (r+1)-minors of `multPoly`) become, after the
     Schur normalization, the "fibre" generators + the base δ-coordinate relations. Is this a finite
     explicit generator computation (tractable), or does it need a structural ideal-image theorem?
   - `⊇`: the harder direction (the R2-3b-4 wall was the forward map needing `sigmaIdeal ≤ ker`).
     At the RADICAL/dimension level, does `⊇` reduce to a height/dimension count (both ideals have
     the same height, both prime-ish → equal) that SIDESTEPS the explicit generator containment?
     I have `ringKrullDim_quotient_radical` (radical-insensitivity) landed.
3. **Is there a SHORTER dimension-only path** that avoids the explicit ideal-split entirely — e.g.:
   `Sred` is a `SchurLoc`-algebra (via `schurToSred`); if I can show `Sred` is module-finite or a
   localized-polynomial extension of `SchurLoc ⊗ (something dim 0)`... OR use that
   `Sred ≅ Localization.Away ΔPdeep ⧸ IadDeep` and compute `ringKrullDim` of the localized quotient
   directly via the LANDED determinantal/orbit dimension machinery (the engine already computes
   `dim Σ̄^r = card − C` and `dim Mat^{≤r} = δ`)? Could the chart dimension come from
   `dim Σ̄^r − dim(complement of chart)` or a localization-dim argument, WITHOUT building the split?
4. **Honest verdict**: is the radical ideal-split a ~2-3-module tractable grind, or is it the
   R2-3b-4 wall in disguise (needs the absent localized-quotient-interchange / structural ideal
   theorem)? If the latter, I STOP and cite `hSweep`. Be adversarial — I have a STOP→B authorization
   and would rather take a clean B than grind a wall.

Give me: the right gauge ring, the tractability verdict on each containment (or the height-count
sidestep), any shorter dimension-only path, and a clear "grind it (~N modules)" vs "STOP→B" call.

codex
I’ll read the local project instructions and the relevant Lean/exposition artifacts first, then I’ll give a tractability call grounded in what is actually present in this worktree.
exec
/bin/bash -lc "sed -n '1,220p' README.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 2 in 0ms:
sed: can't read README.md: No such file or directory

exec
/bin/bash -lc "sed -n '1,220p' CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 2 in 0ms:
sed: can't read CLAUDE.md: No such file or directory

exec
/bin/bash -lc "pwd && rg --files -g 'CLAUDE.md' -g 'README.md' -g '*.lean' -g '*.md' | head -200" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
split-tractability-prompt.md
rung2-lighter-path-prompt.md
rung2-regular-section-prompt.md
rung2-regular-section-answer.md
rung2-lighter-path-answer.md
route-choice-prompt.md
split-tractability-answer.md
noncirc-setlevel-prompt.md
noncirc-setlevel-answer.md
route-choice-answer.md

codex
This thread directory is mostly prompt/answer notes, so I’m moving up to the repo root to inspect the actual Lean engine and policy context.
exec
/bin/bash -lc 'git rev-parse --show-toplevel' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
2026-06-24T22:51:52.417439Z ERROR codex_app_server::bespoke_event_handling: request failed with client error: JSONRPCErrorError { code: -32000, data: None, message: "command execution approval is not supported in exec mode for thread `019efbd4-ff0e-7391-a56d-0ca4c4904ff1`" }
 exited 1:
2026-06-24T22:51:52.417739Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc 'git rev-parse --show-toplevel'`: CreateProcess { message: "Rejected(\"rejected by user\")" }
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019efab0-c1e0-7933-ba10-281ed659d0f8
--------
user
# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)

I am formalising one dimension identity in Lean 4 + Mathlib v4.29 (a research engine for the geometry
of deep-linear-network multiplication-map fibres). I need to pick the cheapest reachable route and
know the TRUE cost. Be adversarial about cost.

## The exact target (`hSweep`)

```
varietyDim (Σ^r)  =  δ  +  varietyDim F
```
where, concretely in the engine (all set-level over an algebraically closed field `k`, char 0):
- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
  Krull dim of the coordinate ring of a subset `Z` of affine space `RepCoord d → k`.
- `Σ^r = productRankLocus d r = {A : rank(mult A) = r}` — the EXACT-rank locus (tuples of composable
  matrices whose product has rank exactly `r`).
- `F = fibre d B = mult⁻¹(B)` for a fixed rank-`r` target `B`.
- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).

## What is already LANDED in the engine (reuse these)

1. **The sweep identity (set form):** `Σ^r = ⋃_{P ∈ H} (P • ·) '' F`, where `H = GL_{d_N} × GL_{d_0}`
   (the endpoint base-change group `BaseChangeGroup`). I.e. `Σ^r = H · F` (one group-sweep of a single
   fibre). PROVED: `productRankLocus_eq_iUnion_smul_fibre`.
2. **Homogeneity (G1):** all rank-`r` fibres are isomorphic; `codimRepCanonical (fibre B') =
   codimRepCanonical (fibre B)` for any rank-`r` `B'`. So every `H`-translate of `F` has the same
   codim/dim. PROVED.
3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
   parametrization pullback (`OrbitPullbackDim`, `AffineNoetherRank`:
   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
   (tower additivity, Stacks 030H) is in Mathlib and the engine uses it.
4. **The comorphism `O(Mat^{=r}) → O(Σ^r)`:** `multComap d := aeval multPoly` IS built
   (`MultComorphism`); the fibre coordinate ring is `R_total ⧸ m_B · R_total` (the comorphism +
   `Ideal.map`). So there IS an abstract ring map `R = O(base) → S = O(total)` at the ideal level.
5. **Generic freeness (module case), JUST LANDED (rung 1):** for a Noetherian domain `R` and a
   FINITE `R`-module `M`, `M[1/r]` is free/flat over `R[1/r]` for some nonzero `r`. The
   algebra-finite-type (relative dim > 0) version is Mathlib-ABSENT.
6. **Determinantal base stratum dim = δ** (LANDED). **Going-down height-additivity**
   `Ideal.height_eq_under_of_flat_quasiFiniteAt` + `Algebra.HasGoingDown.of_flat` (LANDED in
   `FlatQuasiFiniteHeight`).

## The crux

The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
0`), so it is NOT module-finite — rung-1 (module-case generic freeness) does NOT directly apply.

## Two candidate routes — assess reachability + TRUE cost of each at v4.29

**Route (a) — transcendence-degree / tower additivity.** `Σ^r` and `F` are f.g. domains over `k`
(are they? `Σ^r` is the exact-rank locus — irreducible? `F` may be reducible — see below). If I can
show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
the tower `k ⊆ Frac O(Mat^{=r}) ⊆ Frac O(Σ^r)` gives `trdeg_k O(Σ^r) = trdeg_k O(Mat^{=r}) +
trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
`trdeg_{Frac R} Frac S = dim(generic fibre) = dim F` (via homogeneity G1, all fibres iso). Does this
close WITHOUT generic flatness? What is the precise missing lemma — is it "relative trdeg = generic
fibre dim" or "generic fibre dim = special fibre dim (F at B)"? The reducibility of `F`/`Σ^r` (F has
components of dims 10,9,9 on the (3,3,3) r=1 anchor; Σ^r has comps 15,14,14) — does the trdeg/tower
route survive non-irreducibility (trdeg is about a domain = irreducible; for reducible we take the
max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
flatness, given reducibility?

**Route (b) — algebra-case generic freeness (EGA IV 6.9.1).** Relative Noether normalization `R →
R[X_1..X_d] → S` (module-finite generically) + rung-1 (module case on the finite part) + polynomial
flatness + composition ⟹ flatness on a dense-open of `Spec R` ⟹ going-down ⟹ relative-dim formula.
The NEW Mathlib-side piece is **relative Noether normalization** (over a domain `R`, not a field).
Mathlib has Noether normalization over a FIELD. Is the relative/over-a-domain version present at
v4.29? If absent, that is a from-scratch build — how large?

## My questions

1. Which route is cheaper/more reachable at v4.29 given the LANDED pieces, AND given the engine is
   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
   `Spec`-level? The going-down machinery (b) wants `Ideal.height`/`HasGoingDown` on RING MAPS — does
   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
2. Route (a): is "`dim(H·F) = dim(H·E) + dim F`" (sweep/orbit-dimension additivity) provable from
   trdeg tower additivity + homogeneity WITHOUT a flatness/generic-freeness input? Group sweeps `G·F`
   classically have `dim(G·F) = dim F + dim(G·E)` when the map `G × F → G·F` is dominant with generic
   fibre dim `= dim(stabilizer)`. Is there a clean trdeg argument, or does it secretly need fibre-dim
   semicontinuity (a flatness-flavoured input)?
3. Is there a THIRD route I am missing — e.g. directly: `Σ^r → Mat^{=r}` is a `H`-equivariant
   surjection, `Mat^{=r} = H·E` is a single H-orbit (homogeneous space!), so `Σ^r → Mat^{=r}` is a
   FIBRE BUNDLE (locally trivial in the Zariski/étale topology since `H` is a group), hence
   `dim Σ^r = dim Mat^{=r} + dim F` is the bundle dimension formula — no generic flatness needed,
   just local triviality of a `H`-bundle over a homogeneous space. Is THAT reachable at v4.29 (does
   Mathlib have homogeneous-space / principal-bundle dimension)? This feels like the real structure.
4. If ALL routes hit a Mathlib-absent theorem, say so plainly — that is a recalibration point.

Give me: the route ranking, the precise missing lemma(s) for the top route, a module-count estimate,
and whether any route avoids a from-scratch sub-library. Be honest if this rung is genuinely
sub-expedition-scale.

codex
I’ll inspect the local Lean dependency surface first, especially whether Mathlib already has relative Noether normalization, generic flatness beyond finite modules, and the dimension/going-down bridge you mentioned. After that I’ll rank the routes against what is actually available in this worktree.
exec
/bin/bash -lc 'rg -n "Noether( |ian)?[Nn]ormal|normalization|GenericFreeness|generic freeness|FlatQuasiFinite|height_eq_under|trdeg_add_eq|HasGoingDown|relative" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
./route-choice-prompt.md:1:# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)
./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-prompt.md:38:   algebra-finite-type (relative dim > 0) version is Mathlib-ABSENT.
./route-choice-prompt.md:40:   `Ideal.height_eq_under_of_flat_quasiFiniteAt` + `Algebra.HasGoingDown.of_flat` (LANDED in
./route-choice-prompt.md:41:   `FlatQuasiFiniteHeight`).
./route-choice-prompt.md:45:The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
./route-choice-prompt.md:46:0`), so it is NOT module-finite — rung-1 (module-case generic freeness) does NOT directly apply.
./route-choice-prompt.md:54:trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
./route-choice-prompt.md:56:close WITHOUT generic flatness? What is the precise missing lemma — is it "relative trdeg = generic
./route-choice-prompt.md:63:**Route (b) — algebra-case generic freeness (EGA IV 6.9.1).** Relative Noether normalization `R →
./route-choice-prompt.md:65:flatness + composition ⟹ flatness on a dense-open of `Spec R` ⟹ going-down ⟹ relative-dim formula.
./route-choice-prompt.md:66:The NEW Mathlib-side piece is **relative Noether normalization** (over a domain `R`, not a field).
./route-choice-prompt.md:67:Mathlib has Noether normalization over a FIELD. Is the relative/over-a-domain version present at
./route-choice-prompt.md:74:   `Spec`-level? The going-down machinery (b) wants `Ideal.height`/`HasGoingDown` on RING MAPS — does
./route-choice-answer.md:6:workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./route-choice-answer.md:16:# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)
./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:53:   algebra-finite-type (relative dim > 0) version is Mathlib-ABSENT.
./route-choice-answer.md:55:   `Ideal.height_eq_under_of_flat_quasiFiniteAt` + `Algebra.HasGoingDown.of_flat` (LANDED in
./route-choice-answer.md:56:   `FlatQuasiFiniteHeight`).
./route-choice-answer.md:60:The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
./route-choice-answer.md:61:0`), so it is NOT module-finite — rung-1 (module-case generic freeness) does NOT directly apply.
./route-choice-answer.md:69:trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
./route-choice-answer.md:71:close WITHOUT generic flatness? What is the precise missing lemma — is it "relative trdeg = generic
./route-choice-answer.md:78:**Route (b) — algebra-case generic freeness (EGA IV 6.9.1).** Relative Noether normalization `R →
./route-choice-answer.md:80:flatness + composition ⟹ flatness on a dense-open of `Spec R` ⟹ going-down ⟹ relative-dim formula.
./route-choice-answer.md:81:The NEW Mathlib-side piece is **relative Noether normalization** (over a domain `R`, not a field).
./route-choice-answer.md:82:Mathlib has Noether normalization over a FIELD. Is the relative/over-a-domain version present at
./route-choice-answer.md:89:   `Spec`-level? The going-down machinery (b) wants `Ideal.height`/`HasGoingDown` on RING MAPS — does
./route-choice-answer.md:109:I’ll inspect the local Lean dependency surface first, especially whether Mathlib already has relative Noether normalization, generic flatness beyond finite modules, and the dimension/going-down bridge you mentioned. After that I’ll rank the routes against what is actually available in this worktree.

exec
/bin/bash -lc "pwd && rg --files -g 'lakefile.*' -g 'lean-toolchain' -g 'lake-manifest.json' -g 'CLAUDE.md' -g 'README.md'" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 1 in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex

codex
The current thread directory only exposed the prompt artifacts in the first search, so I’m going to look upward for the actual Lake workspace and the vendored Mathlib cache. That matters because this is exactly the kind of question where a near-miss theorem name can change the cost estimate.
exec
/bin/bash -lc "find .. -maxdepth 6 \\( -name lakefile.lean -o -name lakefile.toml -o -name lean-toolchain -o -name lake-manifest.json -o -name Mathlib \\) -print" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
exec
/bin/bash -lc "find /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim -maxdepth 5 \\( -name lakefile.lean -o -name lakefile.toml -o -name lean-toolchain -o -name lake-manifest.json -o -name Mathlib \\) -print" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/lakefile.toml
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/lake-manifest.json
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/lean-toolchain

exec
/bin/bash -lc "sed -n '1,220p' route-choice-answer.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019efab0-c1e0-7933-ba10-281ed659d0f8
--------
user
# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)

I am formalising one dimension identity in Lean 4 + Mathlib v4.29 (a research engine for the geometry
of deep-linear-network multiplication-map fibres). I need to pick the cheapest reachable route and
know the TRUE cost. Be adversarial about cost.

## The exact target (`hSweep`)

```
varietyDim (Σ^r)  =  δ  +  varietyDim F
```
where, concretely in the engine (all set-level over an algebraically closed field `k`, char 0):
- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
  Krull dim of the coordinate ring of a subset `Z` of affine space `RepCoord d → k`.
- `Σ^r = productRankLocus d r = {A : rank(mult A) = r}` — the EXACT-rank locus (tuples of composable
  matrices whose product has rank exactly `r`).
- `F = fibre d B = mult⁻¹(B)` for a fixed rank-`r` target `B`.
- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).

## What is already LANDED in the engine (reuse these)

1. **The sweep identity (set form):** `Σ^r = ⋃_{P ∈ H} (P • ·) '' F`, where `H = GL_{d_N} × GL_{d_0}`
   (the endpoint base-change group `BaseChangeGroup`). I.e. `Σ^r = H · F` (one group-sweep of a single
   fibre). PROVED: `productRankLocus_eq_iUnion_smul_fibre`.
2. **Homogeneity (G1):** all rank-`r` fibres are isomorphic; `codimRepCanonical (fibre B') =
   codimRepCanonical (fibre B)` for any rank-`r` `B'`. So every `H`-translate of `F` has the same
   codim/dim. PROVED.
3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
   parametrization pullback (`OrbitPullbackDim`, `AffineNoetherRank`:
   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
   (tower additivity, Stacks 030H) is in Mathlib and the engine uses it.
4. **The comorphism `O(Mat^{=r}) → O(Σ^r)`:** `multComap d := aeval multPoly` IS built
   (`MultComorphism`); the fibre coordinate ring is `R_total ⧸ m_B · R_total` (the comorphism +
   `Ideal.map`). So there IS an abstract ring map `R = O(base) → S = O(total)` at the ideal level.
5. **Generic freeness (module case), JUST LANDED (rung 1):** for a Noetherian domain `R` and a
   FINITE `R`-module `M`, `M[1/r]` is free/flat over `R[1/r]` for some nonzero `r`. The
   algebra-finite-type (relative dim > 0) version is Mathlib-ABSENT.
6. **Determinantal base stratum dim = δ** (LANDED). **Going-down height-additivity**
   `Ideal.height_eq_under_of_flat_quasiFiniteAt` + `Algebra.HasGoingDown.of_flat` (LANDED in
   `FlatQuasiFiniteHeight`).

## The crux

The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
0`), so it is NOT module-finite — rung-1 (module-case generic freeness) does NOT directly apply.

## Two candidate routes — assess reachability + TRUE cost of each at v4.29

**Route (a) — transcendence-degree / tower additivity.** `Σ^r` and `F` are f.g. domains over `k`
(are they? `Σ^r` is the exact-rank locus — irreducible? `F` may be reducible — see below). If I can
show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
the tower `k ⊆ Frac O(Mat^{=r}) ⊆ Frac O(Σ^r)` gives `trdeg_k O(Σ^r) = trdeg_k O(Mat^{=r}) +
trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
`trdeg_{Frac R} Frac S = dim(generic fibre) = dim F` (via homogeneity G1, all fibres iso). Does this
close WITHOUT generic flatness? What is the precise missing lemma — is it "relative trdeg = generic
fibre dim" or "generic fibre dim = special fibre dim (F at B)"? The reducibility of `F`/`Σ^r` (F has
components of dims 10,9,9 on the (3,3,3) r=1 anchor; Σ^r has comps 15,14,14) — does the trdeg/tower
route survive non-irreducibility (trdeg is about a domain = irreducible; for reducible we take the
max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
flatness, given reducibility?

**Route (b) — algebra-case generic freeness (EGA IV 6.9.1).** Relative Noether normalization `R →
R[X_1..X_d] → S` (module-finite generically) + rung-1 (module case on the finite part) + polynomial
flatness + composition ⟹ flatness on a dense-open of `Spec R` ⟹ going-down ⟹ relative-dim formula.
The NEW Mathlib-side piece is **relative Noether normalization** (over a domain `R`, not a field).
Mathlib has Noether normalization over a FIELD. Is the relative/over-a-domain version present at
v4.29? If absent, that is a from-scratch build — how large?

## My questions

1. Which route is cheaper/more reachable at v4.29 given the LANDED pieces, AND given the engine is
   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
   `Spec`-level? The going-down machinery (b) wants `Ideal.height`/`HasGoingDown` on RING MAPS — does
   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
2. Route (a): is "`dim(H·F) = dim(H·E) + dim F`" (sweep/orbit-dimension additivity) provable from
   trdeg tower additivity + homogeneity WITHOUT a flatness/generic-freeness input? Group sweeps `G·F`
   classically have `dim(G·F) = dim F + dim(G·E)` when the map `G × F → G·F` is dominant with generic
   fibre dim `= dim(stabilizer)`. Is there a clean trdeg argument, or does it secretly need fibre-dim
   semicontinuity (a flatness-flavoured input)?
3. Is there a THIRD route I am missing — e.g. directly: `Σ^r → Mat^{=r}` is a `H`-equivariant
   surjection, `Mat^{=r} = H·E` is a single H-orbit (homogeneous space!), so `Σ^r → Mat^{=r}` is a

codex
There is already a prior consult transcript in this thread, and the Lean workspace is at `.../fibre-codim/lean`. I’m reading both: the transcript gives continuity, while the Lean files tell me whether the proposed split has enough local infrastructure.
exec
/bin/bash -lc "sed -n '220,520p' route-choice-answer.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:

## The crux

The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
0`), so it is NOT module-finite — rung-1 (module-case generic freeness) does NOT directly apply.

## Two candidate routes — assess reachability + TRUE cost of each at v4.29

**Route (a) — transcendence-degree / tower additivity.** `Σ^r` and `F` are f.g. domains over `k`
(are they? `Σ^r` is the exact-rank locus — irreducible? `F` may be reducible — see below). If I can
show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
the tower `k ⊆ Frac O(Mat^{=r}) ⊆ Frac O(Σ^r)` gives `trdeg_k O(Σ^r) = trdeg_k O(Mat^{=r}) +
trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
`trdeg_{Frac R} Frac S = dim(generic fibre) = dim F` (via homogeneity G1, all fibres iso). Does this
close WITHOUT generic flatness? What is the precise missing lemma — is it "relative trdeg = generic
fibre dim" or "generic fibre dim = special fibre dim (F at B)"? The reducibility of `F`/`Σ^r` (F has
components of dims 10,9,9 on the (3,3,3) r=1 anchor; Σ^r has comps 15,14,14) — does the trdeg/tower
route survive non-irreducibility (trdeg is about a domain = irreducible; for reducible we take the
max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
flatness, given reducibility?

**Route (b) — algebra-case generic freeness (EGA IV 6.9.1).** Relative Noether normalization `R →
R[X_1..X_d] → S` (module-finite generically) + rung-1 (module case on the finite part) + polynomial
flatness + composition ⟹ flatness on a dense-open of `Spec R` ⟹ going-down ⟹ relative-dim formula.
The NEW Mathlib-side piece is **relative Noether normalization** (over a domain `R`, not a field).
Mathlib has Noether normalization over a FIELD. Is the relative/over-a-domain version present at
v4.29? If absent, that is a from-scratch build — how large?

## My questions

1. Which route is cheaper/more reachable at v4.29 given the LANDED pieces, AND given the engine is
   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
   `Spec`-level? The going-down machinery (b) wants `Ideal.height`/`HasGoingDown` on RING MAPS — does
   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
2. Route (a): is "`dim(H·F) = dim(H·E) + dim F`" (sweep/orbit-dimension additivity) provable from
   trdeg tower additivity + homogeneity WITHOUT a flatness/generic-freeness input? Group sweeps `G·F`
   classically have `dim(G·F) = dim F + dim(G·E)` when the map `G × F → G·F` is dominant with generic
   fibre dim `= dim(stabilizer)`. Is there a clean trdeg argument, or does it secretly need fibre-dim
   semicontinuity (a flatness-flavoured input)?
3. Is there a THIRD route I am missing — e.g. directly: `Σ^r → Mat^{=r}` is a `H`-equivariant
   surjection, `Mat^{=r} = H·E` is a single H-orbit (homogeneous space!), so `Σ^r → Mat^{=r}` is a
   FIBRE BUNDLE (locally trivial in the Zariski/étale topology since `H` is a group), hence
   `dim Σ^r = dim Mat^{=r} + dim F` is the bundle dimension formula — no generic flatness needed,
   just local triviality of a `H`-bundle over a homogeneous space. Is THAT reachable at v4.29 (does
   Mathlib have homogeneous-space / principal-bundle dimension)? This feels like the real structure.
4. If ALL routes hit a Mathlib-absent theorem, say so plainly — that is a recalibration point.

Give me: the route ranking, the precise missing lemma(s) for the top route, a module-count estimate,
and whether any route avoids a from-scratch sub-library. Be honest if this rung is genuinely
sub-expedition-scale.

codex
I’ll inspect the local Lean dependency surface first, especially whether Mathlib already has relative Noether normalization, generic flatness beyond finite modules, and the dimension/going-down bridge you mentioned. After that I’ll rank the routes against what is actually available in this worktree.
exec
/bin/bash -lc 'rg -n "Noether( |ian)?[Nn]ormal|normalization|GenericFreeness|generic freeness|FlatQuasiFinite|height_eq_under|trdeg_add_eq|HasGoingDown|relative" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
./route-choice-prompt.md:1:# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)
./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-prompt.md:38:   algebra-finite-type (relative dim > 0) version is Mathlib-ABSENT.
./route-choice-prompt.md:40:   `Ideal.height_eq_under_of_flat_quasiFiniteAt` + `Algebra.HasGoingDown.of_flat` (LANDED in
./route-choice-prompt.md:41:   `FlatQuasiFiniteHeight`).
./route-choice-prompt.md:45:The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
./route-choice-prompt.md:46:0`), so it is NOT module-finite — rung-1 (module-case generic freeness) does NOT directly apply.
./route-choice-prompt.md:54:trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
./route-choice-prompt.md:56:close WITHOUT generic flatness? What is the precise missing lemma — is it "relative trdeg = generic
./route-choice-prompt.md:63:**Route (b) — algebra-case generic freeness (EGA IV 6.9.1).** Relative Noether normalization `R →
./route-choice-prompt.md:65:flatness + composition ⟹ flatness on a dense-open of `Spec R` ⟹ going-down ⟹ relative-dim formula.
./route-choice-prompt.md:66:The NEW Mathlib-side piece is **relative Noether normalization** (over a domain `R`, not a field).
./route-choice-prompt.md:67:Mathlib has Noether normalization over a FIELD. Is the relative/over-a-domain version present at
./route-choice-prompt.md:74:   `Spec`-level? The going-down machinery (b) wants `Ideal.height`/`HasGoingDown` on RING MAPS — does
./route-choice-answer.md:6:workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./route-choice-answer.md:16:# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)
./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:53:   algebra-finite-type (relative dim > 0) version is Mathlib-ABSENT.
./route-choice-answer.md:55:   `Ideal.height_eq_under_of_flat_quasiFiniteAt` + `Algebra.HasGoingDown.of_flat` (LANDED in
./route-choice-answer.md:56:   `FlatQuasiFiniteHeight`).
./route-choice-answer.md:60:The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
./route-choice-answer.md:61:0`), so it is NOT module-finite — rung-1 (module-case generic freeness) does NOT directly apply.
./route-choice-answer.md:69:trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
./route-choice-answer.md:71:close WITHOUT generic flatness? What is the precise missing lemma — is it "relative trdeg = generic
./route-choice-answer.md:78:**Route (b) — algebra-case generic freeness (EGA IV 6.9.1).** Relative Noether normalization `R →
./route-choice-answer.md:80:flatness + composition ⟹ flatness on a dense-open of `Spec R` ⟹ going-down ⟹ relative-dim formula.
./route-choice-answer.md:81:The NEW Mathlib-side piece is **relative Noether normalization** (over a domain `R`, not a field).
./route-choice-answer.md:82:Mathlib has Noether normalization over a FIELD. Is the relative/over-a-domain version present at
./route-choice-answer.md:89:   `Spec`-level? The going-down machinery (b) wants `Ideal.height`/`HasGoingDown` on RING MAPS — does
./route-choice-answer.md:109:I’ll inspect the local Lean dependency surface first, especially whether Mathlib already has relative Noether normalization, generic flatness beyond finite modules, and the dimension/going-down bridge you mentioned. After that I’ll rank the routes against what is actually available in this worktree.

exec
/bin/bash -lc "pwd && rg --files -g 'lakefile.*' -g 'lean-toolchain' -g 'lake-manifest.json' -g 'CLAUDE.md' -g 'README.md'" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 1 in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex

codex
The current thread directory only exposed the prompt artifacts in the first search, so I’m going to look upward for the actual Lake workspace and the vendored Mathlib cache. That matters because this is exactly the kind of question where a near-miss theorem name can change the cost estimate.
exec
/bin/bash -lc "find .. -maxdepth 6 \\( -name lakefile.lean -o -name lakefile.toml -o -name lean-toolchain -o -name lake-manifest.json -o -name Mathlib \\) -print" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:

codex
I found the actual Lean root at `.../fibre-codim/lean`. I’ll query Mathlib and the project files from there now, focusing on theorem availability rather than trying to build anything.
exec
/bin/bash -lc "sed -n '1,160p' lean-toolchain && sed -n '1,220p' lakefile.toml && sed -n '1,260p' lake-manifest.json" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
exec
/bin/bash -lc "find . -maxdepth 4 \\( -type d -name Mathlib -o -type d -name .lake -o -type d -name GeometryOfDlnFibre -o -type d -name GeometryOfDln \\) -print" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
exec
/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
 succeeded in 109ms:
leanprover/lean4:v4.29.0
name = "DLNFibre"
version = "0.1.0"
keywords = ["math"]
defaultTargets = ["DLNFibre"]

[leanOptions]
pp.unicode.fun = true # pretty-prints `fun a ↦ b`
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.29.0"

[[lean_lib]]
name = "DLNFibre"
{"version": "1.1.0",
 "packagesDir": ".lake/packages",
 "packages":
 [{"url": "https://github.com/leanprover-community/mathlib4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "8a178386ffc0f5fef0b77738bb5449d50efeea95",
   "name": "mathlib",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.29.0",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/plausible",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "83e90935a17ca19ebe4b7893c7f7066e266f50d3",
   "name": "plausible",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/LeanSearchClient",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "c5d5b8fe6e5158def25cd28eb94e4141ad97c843",
   "name": "LeanSearchClient",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/import-graph",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "48d5698bc464786347c1b0d859b18f938420f060",
   "name": "importGraph",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/ProofWidgets4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "3c52dee17f0cd89c1ec14de78920d1bdaa3d26b3",
   "name": "proofwidgets",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v0.0.95",
   "inherited": true,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/aesop",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "7152850e7b216a0d409701617721b6e469d34bf6",
   "name": "aesop",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/quote4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "707efb56d0696634e9e965523a1bbe9ac6ce141d",
   "name": "Qq",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/batteries",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "756e3321fd3b02a85ffda19fef789916223e578c",
   "name": "batteries",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover/lean4-cli",
   "type": "git",
   "subDir": null,
   "scope": "leanprover",
   "rev": "7802da01beb530bf051ab657443f9cd9bc3e1a29",
   "name": "Cli",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.29.0",
   "inherited": true,
   "configFile": "lakefile.toml"}],
 "name": "DLNFibre",
 "lakeDir": ".lake"}

 succeeded in 127ms:
./.lake

 succeeded in 157ms:
./DLNFibre.lean:30:import DLNFibre.Core.FlatQuasiFiniteHeight
./DLNFibre.lean:84:-- via the N=1 specialisation of the quiver engine (productRankLocusLE ![n,m] r = the determinantal variety).
./DLNFibre.lean:134:-- Endpoint-normalization gauge AlgEquiv (R2-3b-3): the vertex-unit conjugation `Aᵢ ↦ P_{i+1}·Aᵢ·P_i⁻¹`
./DLNFibre.lean:154:-- Route-c sweep structure (homogeneous sweep): `Σ^r = H·F` (`productRankLocus_eq_iUnion_smul_fibre`)
./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./DLNFibre.lean:169:-- (b)-build rung 1 — generic freeness (Grothendieck's lemma, MODULE case): a f.g. module over a
./DLNFibre.lean:173:import DLNFibre.Core.GenericFreeness
./CLAUDE.md:81:  set-level route `vanishingIdeal (shifted) = comap (algEquiv) (vanishingIdeal)` + `height_comap` is
./DLNFibre/DLN/RlctPayoffGeneral.lean:15:  (`Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`): the geometric codimension of the
./DLNFibre/DLN/RlctPayoffGeneral.lean:16:  *closed rank-`≤ r` product locus* `Σ̄^r = productRankLocusLE d r` equals the combinatorial `C`. This
./DLNFibre/DLN/RlctPayoffGeneral.lean:71:`Σ̄^r = productRankLocusLE d r`, folding in `codim Σ̄^r = codim Σ^r` (Cor. 4.4 + Lemma 4.5,
./DLNFibre/DLN/RlctPayoffGeneral.lean:90:      = codimRepCanonical (productRankLocusLE (k := K) d r)
./DLNFibre/DLN/RlctPayoffGeneral.lean:110:(`Core.codimRepCanonical_productRankLocusLE_eq_cCodim`) rewrites `codim Σ̄^r = cCodim d r`. Both
./DLNFibre/DLN/RlctPayoffGeneral.lean:126:  have hAfin : codimRepCanonical (productRankLocusLE (k := K) d r) ≠ ⊤ := by
./DLNFibre/DLN/RlctPayoffGeneral.lean:127:    rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h]; exact ENat.coe_ne_top _
./DLNFibre/DLN/RlctPayoffGeneral.lean:128:  have hAval : (codimRepCanonical (productRankLocusLE (k := K) d r)).toNat = (cCodim d r h).toNat := by
./DLNFibre/DLN/RlctPayoffGeneral.lean:129:    rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h, ENat.toNat_coe]
./DLNFibre/DLN/RlctPayoffGeneral.lean:149:theorem codimRepCanonical_productRankLocusLE_d222_one :
./DLNFibre/DLN/RlctPayoffGeneral.lean:150:    (codimRepCanonical (productRankLocusLE (k := AlgebraicClosure ℚ) Core.d222 1)).toNat = 1 := by
./DLNFibre/DLN/RlctPayoffGeneral.lean:151:  have h := codimRepCanonical_productRankLocusLE_eq_cCodim (k := AlgebraicClosure ℚ) Core.d222 1
./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./DLNFibre/Core/OrbitPullbackDim.lean:18:   (`vanishingIdeal_orbitRankLocus_eq_orbitSet`), and the orbit↔kernel identity
./DLNFibre/Core/OrbitPullbackDim.lean:19:   (`range_orbitMap` + `vanishingIdeal_range_orbitMap_eq_ker`).
./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./DLNFibre/Core/OrbitPullbackDim.lean:49:(`vanishingIdeal_orbitRankLocus_eq_orbitSet`) and the orbit↔kernel identity
./DLNFibre/Core/OrbitPullbackDim.lean:50:(`range_orbitMap` + `vanishingIdeal_range_orbitMap_eq_ker`) rewrite the vanishing ideal to
./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./DLNFibre/Core/OrbitPullbackDim.lean:58:    vanishingIdeal_range_orbitMap_eq_ker M]
./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./DLNFibre/DLN/RlctPayoff.lean:101:theorem fibre_zero_eq_productRankLocusLE_zero (d : Fin (N + 1) → ℕ) :
./DLNFibre/DLN/RlctPayoff.lean:102:    fibre (k := k) d 0 = productRankLocusLE (k := k) d 0 := by
./DLNFibre/DLN/RlctPayoff.lean:104:  rw [mem_fibre, mem_productRankLocusLE, Nat.le_zero]
./DLNFibre/DLN/RlctPayoff.lean:110:(definitional, via `fibre_zero_eq_productRankLocusLE_zero`). -/
./DLNFibre/DLN/RlctPayoff.lean:114:  rw [fibre_zero_eq_productRankLocusLE_zero]
./DLNFibre/DLN/RlctPayoff.lean:132:  -- RHS: ⨅ over corner-0 tuples M, of `codimRepCanonical (Ō_M) = (vanishingIdeal Ō_M).height`.
./DLNFibre/DLN/RlctPayoff.lean:136:    have hmem : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./DLNFibre/DLN/RlctPayoff.lean:139:        ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./DLNFibre/DLN/RlctPayoff.lean:142:    haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./DLNFibre/DLN/RlctPayoff.lean:144:      isPrime_vanishingIdeal_orbitRankLocus M
./DLNFibre/DLN/RlctPayoff.lean:197:    exact Ideal.height_ne_top (isPrime_vanishingIdeal_orbitRankLocus M).ne_top
./DLNFibre/DLN/RlctPayoff.lean:226:          (isPrime_vanishingIdeal_orbitRankLocus (realizerD (k := k) hm₀)).ne_top
./DLNFibre/Core/CCodimCornerMono.lean:329:    exact Ideal.height_ne_top (isPrime_vanishingIdeal_orbitRankLocus _).ne_top
./DLNFibre/Core/CCodimCornerMono.lean:374:partition. From G3 (`minimalPrimes_sigmaIdeal_eq`) `p = vanishingIdeal (Ō_{M'})` for a corner-`≤ r`
./DLNFibre/Core/CCodimCornerMono.lean:385:  -- G3: `p` is a corner-`≤ r` orbit ideal `vanishingIdeal (Ō_{M'})`
./DLNFibre/Core/DeterminantalStratumDim.lean:16:`productRankLocusLE ![n,m] r = {M | M.rank ≤ r}` **is** the classical rank-`≤ r` determinantal
./DLNFibre/Core/DeterminantalStratumDim.lean:21:1. **Primality** (irreducible): for `N = 1`, `productRankLocusLE ![n,m] r = orbitRankLocus M₀` for a
./DLNFibre/Core/DeterminantalStratumDim.lean:24:   `isPrime_vanishingIdeal_orbitRankLocus`).
./DLNFibre/Core/DeterminantalStratumDim.lean:25:2. **The codim value** (LANDED `codimRepCanonical_productRankLocusLE_eq_cCodim_enat`, unconditional
./DLNFibre/Core/DeterminantalStratumDim.lean:26:   in char 0 + alg-closed): `codimRepCanonical (productRankLocusLE ![n,m] r) = cCodim ![n,m] r`.
./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./DLNFibre/Core/DeterminantalStratumDim.lean:161:`productRankLocusLE ![n,m] r` — the only binding rank constraint at `N = 1` is the corner. Carries
./DLNFibre/Core/DeterminantalStratumDim.lean:163:theorem exists_orbitRankLocus_eq_productRankLocusLE_stratum (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m) :
./DLNFibre/Core/DeterminantalStratumDim.lean:165:      orbitRankLocus M₀ = productRankLocusLE (k := k) (dStratum n m) r := by
./DLNFibre/Core/DeterminantalStratumDim.lean:175:  · exact orbitRankLocus_subset_productRankLocusLE (dStratum n m) (hcorner.le)
./DLNFibre/Core/DeterminantalStratumDim.lean:177:    rw [mem_productRankLocusLE] at hA
./DLNFibre/Core/DeterminantalStratumDim.lean:196:flattening of) `productRankLocusLE ![n,m] r` is prime — it is `vanishingIdeal (Ō_{M₀})` of a single
./DLNFibre/Core/DeterminantalStratumDim.lean:197:orbit closure (LANDED `isPrime_vanishingIdeal_orbitRankLocus`). -/
./DLNFibre/Core/DeterminantalStratumDim.lean:198:theorem isPrime_vanishingIdeal_productRankLocusLE_stratum [IsAlgClosed k] (n m r : ℕ)
./DLNFibre/Core/DeterminantalStratumDim.lean:200:    (vanishingIdeal k
./DLNFibre/Core/DeterminantalStratumDim.lean:201:        (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r) :
./DLNFibre/Core/DeterminantalStratumDim.lean:203:  obtain ⟨M₀, hM₀⟩ := exists_orbitRankLocus_eq_productRankLocusLE_stratum (k := k) n m r hn hm
./DLNFibre/Core/DeterminantalStratumDim.lean:205:  exact isPrime_vanishingIdeal_orbitRankLocus M₀
./DLNFibre/Core/DeterminantalStratumDim.lean:222:`productRankLocusLE ![n,m] r`) is
./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.

exec
/bin/bash -lc "sed -n '1,260p' split-tractability-answer.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019efbd4-ff0e-7391-a56d-0ca4c4904ff1
--------
user
# Codex consult — the radical ideal-split: tractable, or needs absent machinery? (Lean v4.29)

Greenlit to grind the make-or-break radical ideal-split (route (c), thread 31). I need a sharp
read on tractability BEFORE sinking the module budget, and which ring the normalizing gauge lives
over. STOP→fallback (cite `hSweep`) is authorized if it needs a Mathlib-absent sub-theorem.

## The architecture (LANDED in the engine)

- `ΔPdeep` = the top-left r×r minor of `of (multPoly d)` (the TOTAL-ring pivot minor), in
  `MvPolynomial (RepCoord d) k`.
- `Sred = Localization.Away ΔPdeep ⧸ IadDeep`, where `IadDeep = (sigmaIdeal d r).map (algebraMap
  (MvPolynomial (RepCoord d) k) (Localization.Away ΔPdeep))`. `sigmaIdeal` = vanishing ideal of the
  rank-≤r product locus Σ̄^r (radical, alg-closed).
- `SchurLoc = Localization.Away detSchurS` (the BASE chart ring, a localized polynomial ring in δ
  vars, `dim = δ`). `basePresentationEquiv : Localization.Away detPivotPoly ⧸ Iad ≃ₐ[k] SchurLoc`.
- `baseLocMap : Localization.Away detPivotPoly →ₐ[k] Localization.Away ΔPdeep` (the base→total
  localized ring map, `IsLocalization.Away.mapₐ deepBaseComap`).
- `schurToSred : SchurLoc →ₐ[k] Sred` makes `Sred` a `SchurLoc`-algebra.
- I have LANDED `schurComplement_normal_form` (network-free): `L⁻¹·M·H⁻¹ = diag(I_r,0)` for
  `M = [[Δ,B12],[B21,B22]]`, `Δ` invertible, `B22 = B21 Δ⁻¹ B12`. And a gauge `gaugeEquiv` (an
  `AlgEquiv` of `MvPolynomial (RepCoord d) R`) for any coeff ring `R`, with `gaugeEquiv_multPoly`.

## The target (the split)

`ringKrullDim Sred = ringKrullDim SchurLoc + ringKrullDim FibreAlg = δ + ringKrullDim FibreAlg`,
where `FibreAlg = MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E`. Radical-level route:
`((gauge.map IadDeep).radical = splitBaseFibreIdeal.radical)`, then `Ideal.quotientEquivAlg` +
`ringKrullDim_quotient_eq_of_radical_eq` (LANDED) + the poly-extension dim.

## My ring confusion (resolve this first)

The normalizing gauge inverts the PIVOT minor. Two candidates for which ring it lives over:
(a) `SchurLoc` (the base — `detSchurS` is the base pivot), where I built my `endpointGauge`; or
(b) `Localization.Away ΔPdeep` (the total localization — `ΔPdeep` is the total pivot, which is the
    image of `detPivotPoly` under `deepBaseComap`).
`IadDeep` lives over (b). My `endpointGauge` is over (a). To gauge `IadDeep` I seemingly need the
gauge over (b), with blocks = images of the Schur blocks under `baseLocMap`. **Q1: is the gauge over
(b) the right object, and is it just `endpointGauge` transported along `baseLocMap`/`schurToSred`, or
do I rebuild it over (b) from `ΔPdeep`'s own pivot data?**

## The real questions

1. **Which ring for the gauge** (Q1 above) + the cleanest Lean shape to get a gauge that acts on
   `IadDeep`'s ambient ring `Localization.Away ΔPdeep`.
2. **Is the split `(gauge.map IadDeep).radical = splitBaseFibreIdeal.radical` tractable at v4.29, or
   does it need a Mathlib-absent sub-theorem?** Specifically the two containments:
   - `⊆`: the gauged `sigmaIdeal` generators (bordered (r+1)-minors of `multPoly`) become, after the
     Schur normalization, the "fibre" generators + the base δ-coordinate relations. Is this a finite
     explicit generator computation (tractable), or does it need a structural ideal-image theorem?
   - `⊇`: the harder direction (the R2-3b-4 wall was the forward map needing `sigmaIdeal ≤ ker`).
     At the RADICAL/dimension level, does `⊇` reduce to a height/dimension count (both ideals have
     the same height, both prime-ish → equal) that SIDESTEPS the explicit generator containment?
     I have `ringKrullDim_quotient_radical` (radical-insensitivity) landed.
3. **Is there a SHORTER dimension-only path** that avoids the explicit ideal-split entirely — e.g.:
   `Sred` is a `SchurLoc`-algebra (via `schurToSred`); if I can show `Sred` is module-finite or a
   localized-polynomial extension of `SchurLoc ⊗ (something dim 0)`... OR use that
   `Sred ≅ Localization.Away ΔPdeep ⧸ IadDeep` and compute `ringKrullDim` of the localized quotient
   directly via the LANDED determinantal/orbit dimension machinery (the engine already computes
   `dim Σ̄^r = card − C` and `dim Mat^{≤r} = δ`)? Could the chart dimension come from
   `dim Σ̄^r − dim(complement of chart)` or a localization-dim argument, WITHOUT building the split?
4. **Honest verdict**: is the radical ideal-split a ~2-3-module tractable grind, or is it the
   R2-3b-4 wall in disguise (needs the absent localized-quotient-interchange / structural ideal
   theorem)? If the latter, I STOP and cite `hSweep`. Be adversarial — I have a STOP→B authorization
   and would rather take a clean B than grind a wall.

Give me: the right gauge ring, the tractability verdict on each containment (or the height-count
sidestep), any shorter dimension-only path, and a clear "grind it (~N modules)" vs "STOP→B" call.

codex
I’ll read the local project instructions and the relevant Lean/exposition artifacts first, then I’ll give a tractability call grounded in what is actually present in this worktree.
exec
/bin/bash -lc "sed -n '1,220p' README.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 2 in 0ms:
sed: can't read README.md: No such file or directory

exec
/bin/bash -lc "sed -n '1,220p' CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 2 in 0ms:
sed: can't read CLAUDE.md: No such file or directory

exec
/bin/bash -lc "pwd && rg --files -g 'CLAUDE.md' -g 'README.md' -g '*.lean' -g '*.md' | head -200" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
split-tractability-prompt.md
rung2-lighter-path-prompt.md
rung2-regular-section-prompt.md
rung2-regular-section-answer.md
rung2-lighter-path-answer.md
route-choice-prompt.md
split-tractability-answer.md
noncirc-setlevel-prompt.md
noncirc-setlevel-answer.md
route-choice-answer.md

codex
This thread directory is mostly prompt/answer notes, so I’m moving up to the repo root to inspect the actual Lean engine and policy context.
exec
/bin/bash -lc 'git rev-parse --show-toplevel' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
2026-06-24T22:51:52.417439Z ERROR codex_app_server::bespoke_event_handling: request failed with client error: JSONRPCErrorError { code: -32000, data: None, message: "command execution approval is not supported in exec mode for thread `019efbd4-ff0e-7391-a56d-0ca4c4904ff1`" }
 exited 1:
2026-06-24T22:51:52.417739Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc 'git rev-parse --show-toplevel'`: CreateProcess { message: "Rejected(\"rejected by user\")" }
exec
/bin/bash -lc 'find .. -maxdepth 6 -name CLAUDE.md -o -name README.md -o -name lakefile.lean -o -name lake-manifest.json | head -100' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
exec
/bin/bash -lc "sed -n '1,240p' split-tractability-answer.md && sed -n '1,260p' route-choice-answer.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019efbd4-ff0e-7391-a56d-0ca4c4904ff1
--------
user
# Codex consult — the radical ideal-split: tractable, or needs absent machinery? (Lean v4.29)

Greenlit to grind the make-or-break radical ideal-split (route (c), thread 31). I need a sharp
read on tractability BEFORE sinking the module budget, and which ring the normalizing gauge lives
over. STOP→fallback (cite `hSweep`) is authorized if it needs a Mathlib-absent sub-theorem.

## The architecture (LANDED in the engine)

- `ΔPdeep` = the top-left r×r minor of `of (multPoly d)` (the TOTAL-ring pivot minor), in
  `MvPolynomial (RepCoord d) k`.
- `Sred = Localization.Away ΔPdeep ⧸ IadDeep`, where `IadDeep = (sigmaIdeal d r).map (algebraMap
  (MvPolynomial (RepCoord d) k) (Localization.Away ΔPdeep))`. `sigmaIdeal` = vanishing ideal of the
  rank-≤r product locus Σ̄^r (radical, alg-closed).
- `SchurLoc = Localization.Away detSchurS` (the BASE chart ring, a localized polynomial ring in δ
  vars, `dim = δ`). `basePresentationEquiv : Localization.Away detPivotPoly ⧸ Iad ≃ₐ[k] SchurLoc`.
- `baseLocMap : Localization.Away detPivotPoly →ₐ[k] Localization.Away ΔPdeep` (the base→total
  localized ring map, `IsLocalization.Away.mapₐ deepBaseComap`).
- `schurToSred : SchurLoc →ₐ[k] Sred` makes `Sred` a `SchurLoc`-algebra.
- I have LANDED `schurComplement_normal_form` (network-free): `L⁻¹·M·H⁻¹ = diag(I_r,0)` for
  `M = [[Δ,B12],[B21,B22]]`, `Δ` invertible, `B22 = B21 Δ⁻¹ B12`. And a gauge `gaugeEquiv` (an
  `AlgEquiv` of `MvPolynomial (RepCoord d) R`) for any coeff ring `R`, with `gaugeEquiv_multPoly`.

## The target (the split)

`ringKrullDim Sred = ringKrullDim SchurLoc + ringKrullDim FibreAlg = δ + ringKrullDim FibreAlg`,
where `FibreAlg = MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E`. Radical-level route:
`((gauge.map IadDeep).radical = splitBaseFibreIdeal.radical)`, then `Ideal.quotientEquivAlg` +
`ringKrullDim_quotient_eq_of_radical_eq` (LANDED) + the poly-extension dim.

## My ring confusion (resolve this first)

The normalizing gauge inverts the PIVOT minor. Two candidates for which ring it lives over:
(a) `SchurLoc` (the base — `detSchurS` is the base pivot), where I built my `endpointGauge`; or
(b) `Localization.Away ΔPdeep` (the total localization — `ΔPdeep` is the total pivot, which is the
    image of `detPivotPoly` under `deepBaseComap`).
`IadDeep` lives over (b). My `endpointGauge` is over (a). To gauge `IadDeep` I seemingly need the
gauge over (b), with blocks = images of the Schur blocks under `baseLocMap`. **Q1: is the gauge over
(b) the right object, and is it just `endpointGauge` transported along `baseLocMap`/`schurToSred`, or
do I rebuild it over (b) from `ΔPdeep`'s own pivot data?**

## The real questions

1. **Which ring for the gauge** (Q1 above) + the cleanest Lean shape to get a gauge that acts on
   `IadDeep`'s ambient ring `Localization.Away ΔPdeep`.
2. **Is the split `(gauge.map IadDeep).radical = splitBaseFibreIdeal.radical` tractable at v4.29, or
   does it need a Mathlib-absent sub-theorem?** Specifically the two containments:
   - `⊆`: the gauged `sigmaIdeal` generators (bordered (r+1)-minors of `multPoly`) become, after the
     Schur normalization, the "fibre" generators + the base δ-coordinate relations. Is this a finite
     explicit generator computation (tractable), or does it need a structural ideal-image theorem?
   - `⊇`: the harder direction (the R2-3b-4 wall was the forward map needing `sigmaIdeal ≤ ker`).
     At the RADICAL/dimension level, does `⊇` reduce to a height/dimension count (both ideals have
     the same height, both prime-ish → equal) that SIDESTEPS the explicit generator containment?
     I have `ringKrullDim_quotient_radical` (radical-insensitivity) landed.
3. **Is there a SHORTER dimension-only path** that avoids the explicit ideal-split entirely — e.g.:
   `Sred` is a `SchurLoc`-algebra (via `schurToSred`); if I can show `Sred` is module-finite or a
   localized-polynomial extension of `SchurLoc ⊗ (something dim 0)`... OR use that
   `Sred ≅ Localization.Away ΔPdeep ⧸ IadDeep` and compute `ringKrullDim` of the localized quotient
   directly via the LANDED determinantal/orbit dimension machinery (the engine already computes
   `dim Σ̄^r = card − C` and `dim Mat^{≤r} = δ`)? Could the chart dimension come from
   `dim Σ̄^r − dim(complement of chart)` or a localization-dim argument, WITHOUT building the split?
4. **Honest verdict**: is the radical ideal-split a ~2-3-module tractable grind, or is it the
   R2-3b-4 wall in disguise (needs the absent localized-quotient-interchange / structural ideal
   theorem)? If the latter, I STOP and cite `hSweep`. Be adversarial — I have a STOP→B authorization
   and would rather take a clean B than grind a wall.

Give me: the right gauge ring, the tractability verdict on each containment (or the height-count
sidestep), any shorter dimension-only path, and a clear "grind it (~N modules)" vs "STOP→B" call.

codex
I’ll read the local project instructions and the relevant Lean/exposition artifacts first, then I’ll give a tractability call grounded in what is actually present in this worktree.
exec
/bin/bash -lc "sed -n '1,220p' README.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 2 in 0ms:
sed: can't read README.md: No such file or directory

exec
/bin/bash -lc "sed -n '1,220p' CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 2 in 0ms:
sed: can't read CLAUDE.md: No such file or directory

exec
/bin/bash -lc "pwd && rg --files -g 'CLAUDE.md' -g 'README.md' -g '*.lean' -g '*.md' | head -200" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
split-tractability-prompt.md
rung2-lighter-path-prompt.md
rung2-regular-section-prompt.md
rung2-regular-section-answer.md
rung2-lighter-path-answer.md
route-choice-prompt.md
split-tractability-answer.md
noncirc-setlevel-prompt.md
noncirc-setlevel-answer.md
route-choice-answer.md

codex
This thread directory is mostly prompt/answer notes, so I’m moving up to the repo root to inspect the actual Lean engine and policy context.
exec
/bin/bash -lc 'git rev-parse --show-toplevel' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
2026-06-24T22:51:52.417439Z ERROR codex_app_server::bespoke_event_handling: request failed with client error: JSONRPCErrorError { code: -32000, data: None, message: "command execution approval is not supported in exec mode for thread `019efbd4-ff0e-7391-a56d-0ca4c4904ff1`" }
 exited 1:
2026-06-24T22:51:52.417739Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc 'git rev-parse --show-toplevel'`: CreateProcess { message: "Rejected(\"rejected by user\")" }
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019efab0-c1e0-7933-ba10-281ed659d0f8
--------
user
# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)

I am formalising one dimension identity in Lean 4 + Mathlib v4.29 (a research engine for the geometry
of deep-linear-network multiplication-map fibres). I need to pick the cheapest reachable route and
know the TRUE cost. Be adversarial about cost.

exec
/bin/bash -lc "find /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim -maxdepth 3 \\( -name CLAUDE.md -o -name README.md -o -name '*.lean' \\) -print | head -200" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/theory/README.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/CLAUDE.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/docs/policies/README.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/.agent-team/README.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/CLAUDE.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/README.md

exec
/bin/bash -lc 'rg -n "ΔPdeep|IadDeep|Sred|SchurLoc|baseLocMap|schurToSred|endpointGauge|gaugeEquiv|schurComplement_normal_form|splitBaseFibreIdeal|fibreGenIdeal|ringKrullDim_quotient_eq_of_radical_eq|ringKrullDim_quotient_radical|sigmaIdeal" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:91:-- and fibreGenIdeal = Ideal.map multComap (maxIdealOfPoint B) — the fibre-ring quotient F2 consumes.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:125:-- the open R2-3b wall) — `fibreGenIdeal` radical + the radical-collapse of MultComorphism pt4. The
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:128:-- Deep chart ring (R2-3b-1+2, the residual G2-3 wall foundation): `Sred = Localization.Away(ΔPdeep) ⧸
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:129:-- IadDeep` for general d (the engine's base presentation is N=1 only), the RepCoord↔stratum/endpoint
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:130:-- bridges, and the localized base→total map `schurToSred : SchurLoc → Sred` giving Sred its
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:131:-- SchurLoc-algebra structure (R2-3a's R = SchurLoc, S = Sred). The crux containments (det transport,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:132:-- base→deep sigmaIdeal, NON-circular) proved. Feeds R2-3b-3 (endpoint AlgEquiv) + R2-3b-4 (the iso e).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:135:-- (= landed `BaseChange.baseChange`) on the generic tuple, `gaugeEquiv d P`, over arbitrary CommRing R,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:136:-- + the transport `gaugeEquiv (multPoly) = P_last·M·P_0⁻¹` (endpoint gauge P_0=H, P_last=L⁻¹ ⟹ L⁻¹·M·H⁻¹).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:140:-- = height I, no hypotheses) + `codimRepCanonical_fibre_eq_height_fibreGenIdeal` (codim of the fibre =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:174:-- (b)-build route-c foundation: `VarietyDimRadical` — the non-circularity SHIELD `ringKrullDim_quotient_radical`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:177:-- — the Schur pivot block is a SchurLoc-unit (det = the inverted detSchurS), the unit the gauge L/H blocks use.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimCornerMono.lean:373:prime of `sigmaIdeal d r` of height `cCodim d r`) is the orbit ideal of *some corner-`r`* Kostant
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimCornerMono.lean:374:partition. From G3 (`minimalPrimes_sigmaIdeal_eq`) `p = vanishingIdeal (Ō_{M'})` for a corner-`≤ r`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimCornerMono.lean:386:  rw [topComponents, Set.mem_setOf_eq, minimalPrimes_sigmaIdeal_eq] at hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoffGeneral.lean:18:  same orbit-closure machinery that proved the `r = 0` case (`sigmaIdeal d r = sInf orbitIdeals`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:21:* **`fibreGen`** — the generator family; `span (range (fibreGen d B)) = fibreGenIdeal d B`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:62:/-- The span of the fibre generators is the fibre generator ideal `fibreGenIdeal d B`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:65:    Ideal.span (Set.range (fibreGen d B)) = fibreGenIdeal d B := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:113:localisation of `fibreGenIdeal d B` (`span (range (fibreGen d B)) = fibreGenIdeal d B`) at `A`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:30:  components", from `minimalPrimes_sigmaIdeal_eq` + Mathlib's `Ideal.height`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:109:/-- `codimRepCanonical (mult⁻¹(0))` is the height of the aggregate ideal `sigmaIdeal d 0` of `Σ̄^0`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:111:theorem codimRepCanonical_fibre_zero_eq_height_sigmaIdeal (d : Fin (N + 1) → ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:113:      = (sigmaIdeal (k := k) d 0).height := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:120:of its irreducible components". The height of `sigmaIdeal d 0 = sInf (orbitIdeals d 0)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:121:(`sigmaIdeal_eq_sInf_orbitIdeals`) is the infimum over its minimal primes
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:122:(`minimalPrimes_sigmaIdeal_eq`); each such prime is an orbit ideal, and every orbit ideal contains a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:130:  rw [codimRepCanonical_fibre_zero_eq_height_sigmaIdeal, Ideal.height]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:131:  -- LHS: ⨅ over minimal primes of `sigmaIdeal d 0`, of primeHeight.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:138:    have hle : sigmaIdeal (k := k) d 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:141:      rw [sigmaIdeal_eq_sInf_orbitIdeals]; exact sInf_le hmem
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:147:    calc ⨅ J ∈ (sigmaIdeal (k := k) d 0).minimalPrimes,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:159:    -- J is a minimal prime, hence in orbitIdeals (minimalPrimes_sigmaIdeal_eq), so J = Ō_M's ideal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:161:      have := (minimalPrimes_sigmaIdeal_eq (k := k) d 0).symm ▸ hJ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:162:      exact ((minimalPrimes_sigmaIdeal_eq (k := k) d 0) ▸ hJ).1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:43:/-- LANDED: H1 retarget — `codim(fibre B) = height(fibreGenIdeal B)`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:46:    codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:47:  codimRepCanonical_fibre_eq_height_fibreGenIdeal d B
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:7:# `DLNFibre.Core.SchurGauge` — the Schur-valued pivot block as a `SchurLoc`-unit (route-(c) rung 2)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:11:coordinates), mapped into the localization `SchurLoc = Localization.Away detSchurS`, is an
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:12:**invertible matrix**. Its determinant is `detSchurS`, the very element inverted in `SchurLoc`. It
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:14:— the `BaseChangeGroup` element over `SchurLoc` that drives the chart `AlgEquiv`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:20:- `schurΔLoc` — the pivot block over `SchurLoc`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:21:- `det_schurΔLoc` — its determinant is `detSchurS` pushed into `SchurLoc`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:22:- `isUnit_det_schurΔLoc` — that determinant is a unit (inverted in `SchurLoc`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:34:`SchurLoc = Localization.Away detSchurS`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:36:    Matrix (Fin r) (Fin r) (SchurLoc (k := k) q p r) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:39:/-- The determinant of `schurΔLoc` is `detSchurS`, pushed into `SchurLoc`. (`detSchurS` is by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:43:      = algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:45:  (RingHom.map_det (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:48:/-- **The pivot block is invertible over `SchurLoc`.** Its determinant `detSchurS` is the element
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:49:inverted in `SchurLoc = Localization.Away detSchurS`, hence a unit. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:54:/-- The pivot block is invertible as a matrix over `SchurLoc` (det is a unit, in a commutative
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:59:/-! ## The Schur off-diagonal blocks `B12`, `B21` over `SchurLoc`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:64:`SchurLoc`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:66:/-- The `B12` block (`Fin r × Fin (q−r)`) over `SchurLoc`, from the `Sum.inr ∘ Sum.inl` coords. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:68:    Matrix (Fin r) (Fin (q - r)) (SchurLoc (k := k) q p r) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:72:/-- The `B21` block (`Fin (p−r) × Fin r`) over `SchurLoc`, from the `Sum.inr ∘ Sum.inr` coords. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:74:    Matrix (Fin (p - r)) (Fin r) (SchurLoc (k := k) q p r) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:80:The pivot-cell factorization `M = L · E · H` (`M` the rank-`r` generic product over `SchurLoc`):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:86:`finSplit`. Both are units over `SchurLoc` — `Δ⁻¹` exists there (`isUnit_schurΔLoc`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:90:    Matrix (Fin r ⊕ Fin (p - r)) (Fin r ⊕ Fin (p - r)) (SchurLoc (k := k) q p r) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:95:    Matrix (Fin r ⊕ Fin (q - r)) (Fin r ⊕ Fin (q - r)) (SchurLoc (k := k) q p r) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:98:/-- `L` as a `p × p` matrix over `SchurLoc` (the `LblockSum` reindexed by the pivot split). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:100:    Matrix (Fin p) (Fin p) (SchurLoc (k := k) q p r) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:101:  reindexAlgEquiv (SchurLoc (k := k) q p r) (SchurLoc (k := k) q p r) (finSplit hp).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:104:/-- `H` as a `q × q` matrix over `SchurLoc` (the `HblockSum` reindexed by the pivot split). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:106:    Matrix (Fin q) (Fin q) (SchurLoc (k := k) q p r) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:107:  reindexAlgEquiv (SchurLoc (k := k) q p r) (SchurLoc (k := k) q p r) (finSplit hq).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:122:/-! ## The endpoint gauge as a `BaseChangeGroup` over `SchurLoc`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:125:over `SchurLoc`: the source-vertex unit (`v = 0`, dimension `d 0 = q`) is `H`, the target-vertex
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:130:/-- **The endpoint normalizing gauge** as a `BaseChangeGroup` over `SchurLoc`: `H` at the source
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:132:noncomputable def endpointGauge (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:134:    BaseChangeGroup (k := SchurLoc (k := k) (d 0) (d (Fin.last N)) r) d :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:143:theorem endpointGauge_zero (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:145:    (endpointGauge (k := k) d r hp hq) 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:147:  unfold endpointGauge; rw [dif_pos rfl]; rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:151:theorem endpointGauge_last {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:153:    (endpointGauge (k := k) d r hp hq) (Fin.last (N + 1))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:155:  unfold endpointGauge
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:168:theorem schurComplement_normal_form {R : Type*} [CommRing R] {r s t : ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:194:/-- Non-vacuity witness: at `(q,p,r) = (2,2,1)` over `ℚ`, the `1×1` pivot block over `SchurLoc` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CTheta.lean:35:components are the orbit closures (`Core.SigmaComponents.minimalPrimes_sigmaIdeal_eq`),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:5:# `DLNFibre.Core.DeepChartRing` — the deep chart ring `Sred` + the localized base→total map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:12:vector `d : Fin (N + 1) → ℕ`, the deep localized chart ring `Sred` of the rank-`≤ r` product locus
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:13:on the pivot chart, and the localized base→total `k`-algebra map that gives `Sred` its
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:14:`SchurLoc`-algebra structure (the `R = SchurLoc`-algebra structure that R2-3a's `e` needs).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:19:1. `ΔPdeep d r hp hq` — the deep pivot minor: the determinant of the top-left `r×r` submatrix of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:21:2. `IadDeep d r hp hq` — the localized base ideal `(sigmaIdeal d r).map (algebraMap …)` pushed into
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:22:   `Localization.Away (ΔPdeep …)` (the deep analog of `Iad`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:23:3. `Sred d r hp hq := Localization.Away (ΔPdeep …) ⧸ IadDeep …` — the deep chart quotient ring, with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:24:   its `CommRing` / `Algebra k` instances inherited, and `isReduced_Sred` : `IsReduced (Sred …)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:25:   (over `[IsAlgClosed k]`, justifying the name — this is R2-3a's `hSred`, now discharged).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:31:**R2-3b-2 — the localized base→total map + the `SchurLoc`-algebra structure.**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:33:   pivot minor `detPivotPoly` to the deep `ΔPdeep` (det commutes with `aeval`, `AlgHom.map_det`),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:35:6. `deepBaseComap_sigmaIdeal_le` — the (non-circular) ideal direction: `deepBaseComap d` maps the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:36:   base `sigmaIdeal (dStratum q p) r` into the deep `sigmaIdeal d r`. Mechanism: a **deep** total
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:39:   `aeval_deepBaseComap` + `singleTuple`). It does **not** assume the circular `sigmaIdeal ≤
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:40:   fibreGenIdeal`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:41:7. `baseLocMap` / `schurToSred` — the localized base map `Localization.Away detPivotPoly →ₐ[k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:42:   Localization.Away (ΔPdeep …)` (`IsLocalization.Away.mapₐ`), lifted to the quotients
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:44:   `SchurLoc q p r →ₐ[k] Sred d r hp hq`. The resulting `SchurLoc`-algebra structure on `Sred`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:45:   (`RingHom.toAlgebra`) + the `IsScalarTower k (SchurLoc …) (Sred …)` instance.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:47:**Scope (what is NOT here).** The full product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg`, the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:51:discharged here: `isReduced_Sred`, so R2-3b-4 needs only `e` itself.) The R2-3b-3
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:102:/-! ## R2-3b-1 — the deep chart ring `Sred` -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:104:/-- **The deep pivot minor** `ΔPdeep d r`: the determinant of the top-left `r×r` submatrix of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:107:noncomputable def ΔPdeep (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:113:/-- **The deep localized base ideal** `IadDeep d r`: the determinantal base ideal `sigmaIdeal d r`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:114:pushed into the localized total ring `Localization.Away (ΔPdeep …)`. The deep analog of `Iad`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:115:noncomputable def IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:117:    Ideal (Localization.Away (ΔPdeep (k := k) d r hp hq)) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:118:  (sigmaIdeal d r).map (algebraMap (MvPolynomial (RepCoord d) k)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:119:    (Localization.Away (ΔPdeep (k := k) d r hp hq)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:121:/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:124:noncomputable abbrev Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:126:  Localization.Away (ΔPdeep (k := k) d r hp hq) ⧸ IadDeep (k := k) d r hp hq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:128:/-! ## R2-3b-1 — `Sred` is reduced (justifying the name; discharges R2-3a's `hSred`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:130:The name `Sred` asserts reducedness, and that reducedness is precisely R2-3a's second hypothesis
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:131:`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:132:It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:133:`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:138:/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:139:base ideal `sigmaIdeal d r`. Via `IsLocalization.map_radical`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:140:(`(I.map …).radical = I.radical.map …`) and `sigmaIdeal`'s radicality
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:142:theorem IadDeep_isRadical [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:144:    (IadDeep (k := k) d r hp hq).IsRadical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:145:  have hsig : (sigmaIdeal (k := k) d r).IsRadical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:146:    rw [sigmaIdeal]; exact vanishingIdeal_isRadical _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:147:  rw [← Ideal.radical_eq_iff, IadDeep,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:148:    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:151:/-- **`Sred` is reduced** (`[IsAlgClosed k]`), justifying the name.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:152:`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:154:(`Ideal.isRadical_iff_quotient_reduced`). This is exactly R2-3a's `hSred : IsReduced S` for
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:155:`S = Sred` — so R2-3b-4 needs to build only `e` itself, not also `IsReduced S`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:156:theorem isReduced_Sred [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:158:    IsReduced (Sred (k := k) d r hp hq) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:159:  (Ideal.isRadical_iff_quotient_reduced _).mp (IadDeep_isRadical d r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:163:`deepBaseComap` carries the `N = 1` pivot minor `detPivotPoly` to the deep `ΔPdeep` (making the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:164:localized map well-typed), and the base `sigmaIdeal` into the deep `sigmaIdeal` (making the quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:168:`detPivotPoly (d 0) (d last) r` to the deep pivot minor `ΔPdeep d r`. The determinant commutes with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:176:      = ΔPdeep (k := k) d r hp hq := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:177:  rw [detPivotPoly, ΔPdeep, AlgHom.map_det]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:223:/-- **The base→deep `sigmaIdeal` direction** (non-circular): `deepBaseComap d` maps the base
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:224:`sigmaIdeal (dStratum q p) r` into the deep `sigmaIdeal d r`. Via `Ideal.map_le_iff_le_comap`: a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:229:Does **not** assume the circular `sigmaIdeal ≤ fibreGenIdeal`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:230:theorem deepBaseComap_sigmaIdeal_le (d : Fin (N + 1) → ℕ) (r : ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:231:    (sigmaIdeal (k := k) (dStratum (d 0) (d (Fin.last N))) r).map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:233:      ≤ sigmaIdeal (k := k) d r := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:236:  rw [Ideal.mem_comap, sigmaIdeal, mem_vanishingIdeal_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:242:  rw [sigmaIdeal, mem_vanishingIdeal_iff] at hf
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:246:/-! ## R2-3b-2 — the localized base map and the `SchurLoc`-algebra structure on `Sred`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:248:The localized base map `Localization.Away detPivotPoly →ₐ[k] Localization.Away (ΔPdeep …)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:251:discharged by `deepBaseComap_sigmaIdeal_le`), then composed with `basePresentationEquiv.symm`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:254:Localization.Away (ΔPdeep …)`, `IsLocalization.Away.mapₐ` of the deep base comorphism
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:256:codomain localization instance at `deepBaseComap d (detPivotPoly …)` is `ΔPdeep`'s (the transport
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:258:noncomputable def baseLocMap (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:261:      Localization.Away (ΔPdeep (k := k) d r hp hq) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:264:      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:269:/-- `baseLocMap` sends `algebraMap … x` to `algebraMap … (deepBaseComap d x)` — it intertwines the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:271:theorem baseLocMap_algebraMap (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:274:    baseLocMap (k := k) d r hp hq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:277:      = algebraMap (MvPolynomial (RepCoord d) k) (Localization.Away (ΔPdeep (k := k) d r hp hq))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:281:      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:283:  rw [baseLocMap, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:287:/-- The base ideal `Iad` is carried into `IadDeep` by `baseLocMap`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:288:(`Iad ≤ IadDeep.comap baseLocMap`), the hypothesis the quotient lift needs. `Iad`/`IadDeep` are the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:290:`sigmaIdeal`s; `baseLocMap` intertwines the localization maps (`baseLocMap_algebraMap`) and carries
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:291:the base `sigmaIdeal` into the deep one (`deepBaseComap_sigmaIdeal_le`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:292:theorem Iad_le_comap_IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:295:      ≤ (IadDeep (k := k) d r hp hq).comap (baseLocMap (k := k) d r hp hq) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:298:  rw [Ideal.mem_comap, Ideal.mem_comap, baseLocMap_algebraMap, IadDeep]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:299:  -- `deepBaseComap g ∈ sigmaIdeal d r` (the base → deep direction), then push into the localization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:300:  have hmem : deepBaseComap (k := k) d g ∈ sigmaIdeal (k := k) d r :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:301:    deepBaseComap_sigmaIdeal_le d r (Ideal.mem_map_of_mem _ hg)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:305:Sred d r`: the quotient lift of `baseLocMap` (`Ideal.quotientMapₐ`, the ideal hypothesis from
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:306:`Iad_le_comap_IadDeep`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:311:      →ₐ[k] Sred (k := k) d r hp hq :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:312:  Ideal.quotientMapₐ (IadDeep (k := k) d r hp hq) (baseLocMap (k := k) d r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:313:    (Iad_le_comap_IadDeep d r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:315:/-- **The base→total `k`-algebra map** `SchurLoc q p r →ₐ[k] Sred d r` (`q = d 0`, `p = d last`):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:317:algebra structure makes `Sred` a `SchurLoc`-algebra (the `R = SchurLoc`-algebra structure that
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:319:noncomputable def schurToSred [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:321:    SchurLoc (k := k) (d 0) (d (Fin.last N)) r →ₐ[k] Sred (k := k) d r hp hq :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:325:/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:327:The base→total map `schurToSred` induces (via `RingHom.toAlgebra`) the `SchurLoc q p r`-algebra
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:328:structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:329:`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:331:/-- **The `SchurLoc`-algebra structure on `Sred`**, induced by the base→total map `schurToSred`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:332:(`RingHom.toAlgebra`). The `R = SchurLoc q p r`-algebra structure R2-3a's product iso `e` needs. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:335:    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:336:  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:338:/-- The induced `SchurLoc`-algebra structure on `Sred` makes `k → SchurLoc q p r → Sred` a scalar
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:339:tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:343:    @IsScalarTower k (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:347:  -- `algebraMap (SchurLoc …) Sred = schurToSred.toRingHom` (by `toAlgebra`); `schurToSred` is a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:348:  -- `k`-algebra map, so it commutes with `algebraMap k (SchurLoc …)` (`AlgHom.commutes`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:349:  change algebraMap k (Sred (k := k) d r hp hq) x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:350:      = (schurToSred (k := k) d r hp hq).toRingHom (algebraMap k _ x)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:351:  exact (AlgHom.commutes (schurToSred (k := k) d r hp hq) x).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:408:`deepBaseComap (detPivotPoly …) = ΔPdeep …`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:412:      = ΔPdeep (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:417:`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:423:      →ₐ[AlgebraicClosure ℚ] Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:426:/-- `Sred` is reduced at the `N = 1` anchor `dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:427:name is honest there, and R2-3a's `hSred` is discharged. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:429:    IsReduced (Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:430:  isReduced_Sred (dStratum 2 2) 1 h h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:23:2. `gaugeEquiv d P` — the coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R`, assembled by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:219:noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:233:/-- `gaugeEquiv d P` acts as `aeval (gaugeSub d P)` (the forward `AlgHom` of the `ofAlgHom`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:234:@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:236:    gaugeEquiv d P p = aeval (R := R) (gaugeSub d P) p := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:238:/-- **The mult-transport, in `gaugeEquiv` form.** `gaugeEquiv d P` sends the generic product entry
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:242:theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:244:    gaugeEquiv d P (multPoly d r c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:248:  rw [gaugeEquiv_apply, aeval_gaugeSub_multPoly]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:266:    gaugeEquiv d (1 : BaseChangeGroup (k := R) d) p = p := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:267:  rw [gaugeEquiv_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:286:  gaugeEquiv dConst witnessGauge
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:288:/-- The mult-transport fires at the concrete non-identity gauge `witnessGauge`: `gaugeEquiv` carries
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:292:    gaugeEquiv (R := ℤ) dConst witnessGauge (multPoly dConst r c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:294:  gaugeEquiv_apply dConst witnessGauge (multPoly dConst r c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:19:  the aggregate ideal `sigmaIdeal d r := vanishingIdeal (canonicalCoord d '' Σ̄^r)` is the `sInf` of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:25:  worked `(2,2,2)`/`(2,3,2)` examples. The caveat is co-located at `minimalPrimes_sigmaIdeal_eq`.)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:130:noncomputable def sigmaIdeal (d : Fin (N + 1) → ℕ) (r : ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:137:theorem sigmaIdeal_eq_sInf_orbitIdeals (d : Fin (N + 1) → ℕ) (r : ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:138:    sigmaIdeal (k := k) d r = sInf (orbitIdeals (k := k) d r) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:140:  rw [sigmaIdeal, Submodule.mem_sInf]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:167:order — the bridge that turns `minimalPrimes_sigmaIdeal_eq` into a statement about maximal `Ō_M`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:193:/-- **G3 (minimal-primes form).** The minimal primes of the aggregate ideal `sigmaIdeal d r` of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:199:From the bridge `sigmaIdeal = sInf orbitIdeals` + the SPIKE (`minimalPrimes` of `sInf` of a finite
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:206:theorem minimalPrimes_sigmaIdeal_eq [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:207:    (sigmaIdeal (k := k) d r).minimalPrimes
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:209:  rw [sigmaIdeal_eq_sInf_orbitIdeals]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:214:incarnation of) `Σ̄^r`, namely `zeroLocus (sigmaIdeal d r)`, are in inclusion-reversing bijection
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:216:`Ideal.minimalPrimes.equivIrreducibleComponents`, combined with `minimalPrimes_sigmaIdeal_eq`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:217:noncomputable def irreducibleComponents_sigmaIdeal_equiv [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:221:        ((sigmaIdeal (k := k) d r : Ideal (MvPolynomial (RepCoord d) k)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:223:  (OrderIso.setCongr _ _ (minimalPrimes_sigmaIdeal_eq d r).symm).trans
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:224:    (Ideal.minimalPrimes.equivIrreducibleComponents (sigmaIdeal (k := k) d r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:258:codimension among the corner-`≤ r` family is a minimal prime of `sigmaIdeal d r`, i.e. an irreducible
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:269:      ∈ (sigmaIdeal (k := k) d r).minimalPrimes := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:270:  rw [minimalPrimes_sigmaIdeal_eq]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:290:d222 0`; the bridge `sigmaIdeal = sInf orbitIdeals` and the G3 minimal-primes characterisation fire.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:293:— here the machinery (family nonempty, `sigmaIdeal` the `sInf`, G3) is shown to fire over the genuine
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:317:    sigmaIdeal (k := AlgebraicClosure ℚ) dWitness 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:319:  sigmaIdeal_eq_sInf_orbitIdeals dWitness 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:324:    (sigmaIdeal (k := AlgebraicClosure ℚ) dWitness 0).minimalPrimes
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:327:  minimalPrimes_sigmaIdeal_eq dWitness 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:22:   image under `Ψ` of the bordered `(r+1)`-minor (LANDED `det_submatrix_multPoly_mem_sigmaIdeal`),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:51:abbrev SchurLoc (q p r : ℕ) : Type u :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:58:      ≃ₐ[k] MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:61:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:67:    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:68:        = C (algebraMap k (SchurLoc (k := k) q p r) x) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:69:      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:70:        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:76:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:80:        (S := SchurLoc (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:87:    (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:160:/-- **The bordered minor lies in the base ideal `sigmaIdeal`** (it is an `(r+1)`-minor of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:161:product, `det_submatrix_multPoly_mem_sigmaIdeal` after the `Fin r ⊕ Unit ≃ Fin (r+1)` reindex). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:162:theorem borderMinor_mem_sigmaIdeal (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:164:    borderMinor (k := k) q p r hp hq a' b' ∈ sigmaIdeal (k := k) (dStratum q p) r := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:169:  exact det_submatrix_multPoly_mem_sigmaIdeal (dStratum q p) _ _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:247:          (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:250:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:256:    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) y
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:257:        = C (algebraMap k (SchurLoc (k := k) q p r) y) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:258:      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:259:        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:263:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:266:        (M := Submonoid.powers (detSchurS (k := k) q p r)) (S := SchurLoc (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:269:/-- The localized base ideal `Iad = (sigmaIdeal …).map (algebraMap A_eng A_loc)`: the determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:273:  (sigmaIdeal (dStratum q p) r).map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:284:    C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:286:        * (X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b')))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:298:    IsLocalization.mk'_spec' (SchurLoc (k := k) q p r) ((forcedNum (k := k) q p r) a' b')
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:303:bordered minor (which is in `Iad`, `borderMinor_mem_sigmaIdeal`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:305:    graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:310:  show X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b'))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:313:  have hunit : IsUnit (C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:314:      (detSchurS (k := k) q p r)) : MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:316:      (C : SchurLoc (k := k) q p r →+* _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:319:    (Ideal.mem_map_of_mem _ (borderMinor_mem_sigmaIdeal q p r hp hq a' b'))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:334:      = graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:335:  set Q := MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:338:  set J : Ideal Q := graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) with hJ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:340:  haveI hsigmaPrime : (sigmaIdeal (k := k) (dStratum q p) r).IsPrime := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:341:    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:345:      (detPivotPoly_notMem_sigmaIdeal q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:349:      (sigmaIdeal (dStratum q p) r) hsigmaPrime hdisj
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:351:  haveI : IsDomain (SchurLoc (k := k) q p r) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:352:    IsLocalization.isDomain_of_le_nonZeroDivisors (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:359:    rw [Iad, height_map_sigmaIdeal_away_eq_cCodim q p r hp hq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:363:    height_graphIdeal_forcedB22_eq q p r (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:374:base ring `A_loc = Localization.Away detΔ`, modulo its base ideal `Iad = (sigmaIdeal …).map …`, is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:381:      ≃ₐ[k] SchurLoc (k := k) q p r := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:383:      ≃ₐ[k] (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:384:        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:386:      (graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:389:  have e₂ : (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:390:        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:391:      ≃ₐ[k] SchurLoc (k := k) q p r :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:392:    (graphIdealQuotientEquiv (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))).restrictScalars k
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:413:      ≃ₐ[k] SchurLoc (k := k) 2 2 1 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:14:`r`: `sigmaIdeal d r = sInf (orbitIdeals d r)` and `minimalPrimes_sigmaIdeal_eq` (both general in `r`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:45:/-- `codimRepCanonical Σ̄^r` is the height of the aggregate ideal `sigmaIdeal d r` of `Σ̄^r`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:47:locus, which is `sigmaIdeal d r`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:48:theorem codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal (d : Fin (N + 1) → ℕ) (r : ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:49:    codimRepCanonical (productRankLocusLE (k := k) d r) = (sigmaIdeal (k := k) d r).height :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:55:codimension of its irreducible components". General in `r`: `sigmaIdeal d r = sInf (orbitIdeals d r)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:56:and `minimalPrimes_sigmaIdeal_eq` are both general in `r` (`Core.SigmaComponents`). `[IsAlgClosed k]`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:63:  rw [codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal, Ideal.height]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:69:    have hle : sigmaIdeal (k := k) d r
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:72:      rw [sigmaIdeal_eq_sInf_orbitIdeals]; exact sInf_le hmem
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:78:    calc ⨅ J ∈ (sigmaIdeal (k := k) d r).minimalPrimes,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:91:      ((minimalPrimes_sigmaIdeal_eq (k := k) d r) ▸ hJ).1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:12:inclusion `sigmaIdeal ≤ ker`, available only as `≤ radical`. The **dimension** identity `hSweep`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:16:through `vanishingIdeal` (radical by construction) and never needs `fibreGenIdeal` to be radical.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:26:- `ringKrullDim_quotient_radical` — `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical)`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:27:- `ringKrullDim_quotient_eq_of_radical_eq` — same Krull dim for two ideals with equal radical.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:40:theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:46:presentation may hand it the generator ideal `fibreGenIdeal`, equal only up to radical). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:47:theorem ringKrullDim_quotient_eq_of_radical_eq {R : Type*} [CommRing R] {I J : Ideal R}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:50:  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:73:  apply DLNFibre.Core.ringKrullDim_quotient_eq_of_radical_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:10:`codimRepCanonical (fibre d B) = Ideal.height (fibreGenIdeal d B)` (H1, radical-insensitive), and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:18:* `hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height` — every component has codim `≥ v`;
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:19:* `hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v` — one (top) component has codim `≤ v`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:62:per-component height bounds on `fibreGenIdeal d B` — every minimal prime `height ≥ v`, one `≤ v` — the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:64:height (fibreGenIdeal d B)`) and the min-over-components closer. The route-B tide discharges `hge`/`hle`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:68:    (hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:69:    (hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:71:  rw [codimRepCanonical_fibre_eq_height_fibreGenIdeal]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:72:  exact height_eq_of_minimalPrimes_bounds (fibreGenIdeal d B) v hge hle
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:77:target `B` over an algebraically closed field, given that every minimal prime of `fibreGenIdeal d B`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:85:    (hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:87:    (hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:108:    (hge : ∀ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, v ≤ J.height)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:109:    (hle : ∃ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, J.height ≤ v) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaGeometric.lean:36:(`Core.SigmaComponents.minimalPrimes_sigmaIdeal_eq`); (iii) codimension-of-a-union =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean:24:minimal primes of `sigmaIdeal d r`. **Injectivity is unconditional** (the `diff/cumul` inversion:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean:290:/-- The **top-dimensional components** of `Σ̄^r`: the minimal primes of `sigmaIdeal d r` (the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean:300:  {p | p ∈ (sigmaIdeal (k := k) d r).minimalPrimes ∧ p.height = (cCodim d r h).toNat}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:222:/-! ## Step (a): the `(r+1)`-minor of the generic product lies in the base ideal `sigmaIdeal d r`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:246:`det ((multPoly d).submatrix br bc)` lies in `sigmaIdeal d r` (the vanishing ideal of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:249:theorem det_submatrix_multPoly_mem_sigmaIdeal {k : Type u} [Field k] {N : ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:252:    ((Matrix.of (multPoly d)).submatrix br bc).det ∈ sigmaIdeal (k := k) d r := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:253:  rw [sigmaIdeal, mem_vanishingIdeal_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:265:The localized base ideal `Iad = (sigmaIdeal ![q,p] r).map (algebraMap to the localization at detΔ)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:266:has the same height `C` as `sigmaIdeal`: localizing at `detΔ` (not in the prime `sigmaIdeal`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:268:`detΔ ∉ sigmaIdeal` is witnessed by `diag(I_r, 0)` in the base: rank `≤ r` (a pigeonhole column
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:341:/-- `detΔ ∉ sigmaIdeal ![q,p] r`: the pivot minor does not vanish on all of the base — it is `1`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:343:theorem detPivotPoly_notMem_sigmaIdeal (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:344:    detPivotPoly (k := k) q p r hp hq ∉ sigmaIdeal (k := k) (dStratum q p) r := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:345:  rw [sigmaIdeal, mem_vanishingIdeal_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:357:prime determinantal-base ideal `sigmaIdeal ![q,p] r` at the pivot minor `detΔ` (which is not in it)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:358:preserves height: `height Iad = height sigmaIdeal`. Over an algebraically closed field (for the base
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:360:(`height sigmaIdeal = cCodim = C`) it gives `height Iad = C`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:361:theorem height_map_sigmaIdeal_away [IsAlgClosed k] (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:362:    ((sigmaIdeal (k := k) (dStratum q p) r).map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:365:      = (sigmaIdeal (k := k) (dStratum q p) r).height := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:366:  haveI hprime : (sigmaIdeal (k := k) (dStratum q p) r).IsPrime := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:367:    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:370:    (detPivotPoly_notMem_sigmaIdeal q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:372:    (sigmaIdeal (dStratum q p) r) hdisj
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:375:transport with engine Brick A (`height sigmaIdeal = cCodim ![q,p] r`). Over an algebraically closed
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:377:theorem height_map_sigmaIdeal_away_eq_cCodim [IsAlgClosed k] [CharZero k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:381:    ((sigmaIdeal (k := k) (dStratum q p) r).map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:385:  rw [height_map_sigmaIdeal_away q p r hp hq,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:386:    ← codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:27:4. **`vanishingIdeal(fibre) = radical(fibreGenIdeal)`** — over `[IsAlgClosed k]`, the engine's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:29:   radical of `fibreGenIdeal d B = span {multPoly d r c − C (B r c)}`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:31:   `fibreGenIdeal d B = Ideal.map (multComap d) (maxIdealOfPoint B)`: the fibre generator-ideal is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:153:noncomputable def fibreGenIdeal (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:159:vanishing ideal of the fibre's image as the radical of `fibreGenIdeal d B`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:162:    vanishingIdeal k (canonicalCoord d '' (fibre d B)) = (fibreGenIdeal d B).radical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:163:  rw [image_fibre_eq_zeroLocus, fibreGenIdeal,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:188:`fibreGenIdeal d B = Ideal.map (multComap d) (maxIdealOfPoint d B)`: the fibre coordinate ring is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:190:theorem fibreGenIdeal_eq_map_maxIdealOfPoint (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:192:    fibreGenIdeal d B = Ideal.map (multComap d).toRingHom (maxIdealOfPoint d B) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:193:  rw [maxIdealOfPoint, Ideal.map_span, fibreGenIdeal, fibreGenSet]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:13:**inherited** from the reduced ambient rank-locus chart `Sred` via the **faithfully-flat product
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:28:2. **`fibreGenIdeal_isRadical_of_trivialization`** — the full route-(b) chain: given the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:31:   `fibreGenIdeal d B` is **radical** (`Ideal.isRadical_iff_quotient_reduced`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:33:3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:35:   radical (fibreGenIdeal d B) = fibreGenIdeal d B` — the `radical (·)` wrapper drops. This is the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:70:  MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:72:/-- `fibreGenIdeal d B` is radical **iff** `F_B` is reduced — the engine restatement of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:75:theorem fibreGenIdeal_isRadical_iff_isReduced_fibreAlg (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:77:    (fibreGenIdeal d B).IsRadical ↔ IsReduced (FibreAlg d B) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:78:  Ideal.isRadical_iff_quotient_reduced (fibreGenIdeal d B)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:101:/-- **Route (b): `fibreGenIdeal` radical, through the trivialization.** Given the chart
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:103:ring `S` is **reduced** (the engine's `Sred = (MvPol / sigmaIdeal)[1/ΔP]` is reduced, `sigmaIdeal`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:104:a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:106:⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:107:theorem fibreGenIdeal_isRadical_of_trivialization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:111:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:112:    (fibreGenIdeal d B).IsRadical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:113:  letI := hSred
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:117:  -- ⟹ `F_B` reduced (tensor-with-a-field descent) ⟹ `fibreGenIdeal` radical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:118:  exact (fibreGenIdeal_isRadical_iff_isReduced_fibreAlg d B).mpr (isReduced_of_tensor (R := R) hRF)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:121:ideal radical (`fibreGenIdeal_isRadical_of_trivialization`), the engine's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:122:`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:123:`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:126:theorem vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization [IsAlgClosed k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:130:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:131:    vanishingIdeal k (canonicalCoord d '' fibre d B) = fibreGenIdeal d B := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:133:    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:150:hypotheses of `fibreGenIdeal_isRadical_of_trivialization` — so the theorem is not vacuous. (Here the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:155:    (fibreGenIdeal d B).IsRadical :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:156:  fibreGenIdeal_isRadical_of_trivialization d B R (R ⊗[k] FibreAlg d B)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:11:`fibreGenIdeal d B` (`Core.MultComorphism.vanishingIdeal_image_fibre_eq_radical`). The point of this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:16:So `codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height` — **unconditionally** (no radicality
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:17:of `fibreGenIdeal` needed). This decouples the codimension from the scheme-structure / cut-ideal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:19:never depends on whether `fibreGenIdeal` is its own radical.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:45:ideal `fibreGenIdeal d B = span {multPoly d r c − C (B r c)}`. The chain:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:47:(definition of `codimRepCanonical`/`codimRep`); `vanishingIdeal (…) = (fibreGenIdeal d B).radical`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:49:(`Ideal.height_radical`). The codimension does **not** depend on whether `fibreGenIdeal` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:51:theorem codimRepCanonical_fibre_eq_height_fibreGenIdeal [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:53:    codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:61:height of the explicit fibre generator ideal — `codimRepCanonical_fibre_eq_height_fibreGenIdeal` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:64:    codimRepCanonical (fibre dWitness B) = (fibreGenIdeal dWitness B).height :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:65:  codimRepCanonical_fibre_eq_height_fibreGenIdeal dWitness B

codex
The local comments already mark this area as “R2-3b wall” adjacent, but there are useful landed pieces: `DeepChartRing`, `SchurGauge`, and `FibreReducedTrivialization`. I’m reading those declarations now to separate genuine blockers from bookkeeping.
exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
# geometry-of-dln-fibre

AI-assisted math-research + Lean-formalisation harness for **digesting and formalising** the paper
*"Geometry of the fibers of the multiplication map of deep linear neural networks"* (Simon Pepin
Lehalleur & Richárd Rimányi, 2024; `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).
Orientation is in [`README.md`](README.md); this file is the disposition and the working discipline.
The process harness (disposition + policies + roles + skills + the markdown→Lean pipeline) is ported
from the `ai-research-assistant` harness and is **domain-agnostic** — see [`TEMPLATE.md`](TEMPLATE.md)
to instantiate it for another paper.

## Disposition

The work here is research. Not coding, not ticking off a support ticket, not shipping a product. 
The stance: 
- careful, conscientious, objective as a scientist.
- meticulous in calculation as Euler, bold as Grothendieck. 
- methodical as Sherlock Holmes. Observe before theorising. Distinguish data from interpretation. 
- update like a Bayesian; do not collapse to the mode. 


- **Resist the move-fast-and-ship-it instinct.** Stackable, solid progress is the goal; the trap is
  *visible* progress raced ahead of it — a clean doc or confident headline that travels far while leaving
  holes behind. When you reach for a confident headline, that is the moment to look for the confound. Each
  layer should be solid and hole-free before the next stands on it.
- **Fill the layer — completion is your strength.** *The sea rises inexorably, but not in spikes*
  ([`docs/policies/bedrock.md`](docs/policies/bedrock.md)): within a boundary already staked, close the holes
  — the generality a statement promised, the cases it already claims, fidelity to the definition and the
  underlying spirit it invokes — rather than defer them. Such hardening is high-value, and it is where your
  **comparative advantage** lies: your bottleneck is scoping, taste, and direction, not the patient completion
  of well-scoped work — so do not treat that completion capacity, which is *abundant*, as if it were *scarce*.
  **Just do it!** Don't file it as a "chore" (an *unprobed* difficulty claim, not a defer). Surface to move the
  *boundary* — but an **earned** taste-judgment that a gap is the *right* extension is itself direction:
  **Just Do It** if within reach, else **roadmap** it; only a *bare, unargued* extension waits for the operator.
- **Name results for what they are.** A result's name and statement denote exactly what is proven — no more;
  reaching for an impressive name (or "done") is the visible-progress instinct in disguise. Separate Proved /
  Assumed / Cited / Deferred. See [`docs/policies/precision.md`](docs/policies/precision.md). (Here the
  recurring trap: a `rlct_…`-named result that in fact proves only a *codimension* — the `rlct = ½·codim`
  reading needs the cited analytic bound.)
- **Build to bedrock.** A sorry-free build defeats *technical* slop; it never defeats *conceptual* slop —
  "technically correct but subtly wrong, not The Way." **Bedrock is the rock the rising sea rises over**: build
  the theory so the next result can stand on it without re-opening it. Where short feedback loops fail, **beauty
  is the instrument** — a vacuous, mis-scoped, or overclaiming result is *ugly*, and the ugliness is
  information. The **controller holds this taste and judges against it**; a green build is necessary, never
  sufficient. See [`docs/policies/bedrock.md`](docs/policies/bedrock.md).
- **Caveats live next to claims, not in footnotes.** An assumed hypothesis or a cited interface goes in the
  same paragraph as any claim that depends on it.
- **Write to figure out the truth, not to persuade.** Concise and fact-based.
- **Elementary, precisely.** Build explanations up from precise but simple well-chunked objects, established locally in the
  document. "Elementary" does not mean imprecise or dumbed-down or toy analogies: every step stays
  mathematically precise. Introduce the objects you use before you use them; prefer a chain of small exact
  statements over one dense one. Resist over-naming things to do chunking. Reach for an analogy only when it is exact and load-bearing. See
  [`docs/policies/writing-style.md`](docs/policies/writing-style.md).

## Writing and communication discipline (object-level focus)
In writing or in communication, focus on object-level. Resist meta-level pull. 
Remove authorial self-reassurance: `honestly`, `fundamentally`, `this is the whole point`, `this is loadbearing`, `of course`, `simply`, `just`, and selling phrasing.
The full list and the review function that enforces it are in [`docs/policies/review.md`](docs/policies/review.md).

## How research runs here

- **Expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)) are the unit: a central
  question, a controller delegating to thread teammates (explore / formalisation / infra), reviewers, and a
  synthesis at close. Run on the Agent Teams substrate (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`); launch with
  cwd = this repo root.
- **Pipeline: markdown → Lean.** Theory develops in markdown (`theory/`, expedition notes). A stable claim is
  formalised in Lean (`lean/`, library `DLNFibre`). The reader-facing digest/expositions live in
  `docs/expositions/`.
  - *Scholium* is a **viewer** (renders these markdown docs with KaTeX + callouts), not an editor; write to its
    conventions in [`docs/policies/scholium-writing-format.md`](docs/policies/scholium-writing-format.md). The
    recurring trap: display math `$$…$$` needs a **blank line before and after**, fences on their own lines
    (indented inside `!!!`/`???` callouts) — packed against text it falls through to markdown and the `_`
    subscripts render as emphasis. A second trap: **fenced code does not render inside a callout** — use an
    indented code block (8-space indent) there; top-level fenced code is fine.
- **Claims** carry kill-conditions; new claims are stress-tested, established/cited results verified against
  source ([`docs/policies/claims.md`](docs/policies/claims.md)).
- **Codex** is the independent second model for strategy and review
  ([`docs/policies/codex-consultation.md`](docs/policies/codex-consultation.md)).

## Team structure

Roles are documented under [`.agent-team/roles/`](.agent-team/roles/):
- `controller` — this lead session: meta-planning, delegation, integration.
- `scout` — explore / reconnaissance threads: map the terrain (Mathlib, the paper, possibility spaces), compute / derive / claims.
- `pen-and-paper` — a specialised `scout`: design-space math adjudicating a truth-value (`witness` / `obstruction` seats), exact algebra, decorrelated Codex; hands a certificate to the formaliser. No Lean.
- `formaliser` — formalisation (tide) threads.
- `reviewer` — controller-spawned independent audit (soundness / fidelity).
- `hardener` — independent principles / taste reviewer (precision, bedrock).

If dispatched into a role, read its role file and agent definition first.

## Branch discipline

- **One remote: `origin = git@github.com:edmund-ukaisi/geometry-of-dln-fibre.git`.** All work lives here.
- **`dev` is the integration branch.** Feature and expedition branches branch off `dev` and PR back into
  `dev`. `master` is the **release** branch — promoted from `dev` deliberately by the operator, never pushed
  to directly.
- Use a **feature branch** for any non-trivial unit of work; you can push here; don't commit to `dev` or `master` directly. One
  expedition runs on one branch (`expedition/<slug>`); PR at close behind signal-and-wait.
- **Pushing feature/expedition branches to `origin` is pre-authorized** (operator standing instruction,
  2026-06-12) — push freely to bank and share work. **Opening/merging PRs and the `dev → master` promotion
  remain operator-gated** (signal-and-wait); the operator performs those. Always confirm the push target is
  `origin`, never a non-`origin` remote.

## Memory

Persistent context lives **in-repo**: this file, the policies in `docs/policies/`, the expedition docs
(`synthesis.md` / statement cards / `thread.md`), `ROADMAP.md`, and `lean/CLAUDE.md`. Save conventions and
decisions there.

**Do NOT write to global Claude memory (`~/.claude/**/memory/`).** It pollutes other workspaces and is
invisible to collaborators reading the repo. This binds the controller **and every teammate** — the harness
may prompt you to save a memory there; do not. If a teammate writes one, the controller deletes it and
re-homes the content in-repo. (Agent-Teams *runtime* state under `~/.claude/teams/` and `~/.claude/tasks/` is
fine — that's the substrate, not persistent context.)

## The destination, plainly

We want, in honest Lean, the paper's results about the **fibres of matrix multiplication** for deep linear
networks:

- the space $\operatorname{Rep}_{\underline d}$ of composable matrix tuples, the multiplication map
  $\operatorname{mult}$, the zero-product / rank-$r$ loci, and the fibres $\operatorname{mult}^{-1}(B)$;
- via the **type-A quiver** translation (orbits ↔ Kostant partitions ↔ rank patterns, Gabriel, orbit-closure
  order, the `Ext` codimension): the codimension $C$ and the number $\theta$ of top-dimensional components,
  in the paper's three forms (Poincaré series, a quadratic integer program, an explicit formula), and the
  surprising **permutation invariance** of $(C,\theta)$;
- the payoff: the real log-canonical threshold of the square-Frobenius loss is $C/2$ — DLNs are "mildly
  singular". The geometric codimension is the new content; the `rlct ≤ ½·codim` direction is **Cited**
  (Aoyagi / Watanabe).

The reusable **engine** (everything before "the payoff") is network-free and lives in `DLNFibre.Core`; the
DLN/RLCT **application** lives in `DLNFibre.DLN`. See [`ROADMAP.md`](ROADMAP.md) for the formalisation ladder.

## Pointers

- [`README.md`](README.md) — orientation, how to launch an expedition, Lean build.
- [`ROADMAP.md`](ROADMAP.md) — the result-map + the Core/DLN formalisation-target ladder.
- [`docs/policies/`](docs/policies/) — expedition, claims, review, precision, bedrock, codex-consultation, statement-cards, writing-style (+ the reader-facing exposition trio).
- [`docs/expositions/`](docs/expositions/) — the curated reader-facing digest (starts with `paper-digest/high-level-overview.md`).
- [`.claude/skills/`](.claude/skills/) — lean-formalisation, local-codex-consult.
- [`lean/CLAUDE.md`](lean/CLAUDE.md) — Lean build + Mathlib conventions; the Core/DLN split.
- [`theory/`](theory/) — markdown theory workspace.
- [`TEMPLATE.md`](TEMPLATE.md) — how to instantiate this harness for a new paper.

exec
/bin/bash -lc "sed -n '1,260p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.DeterminantalBasePresentation
import DLNFibre.Core.FibreReducedTrivialization

/-!
# `DLNFibre.Core.DeepChartRing` — the deep chart ring `Sred` + the localized base→total map
# (R2-3b-1+2)

The first rungs of the **deep** product trivialization `e` that R2-3a
(`Core.FibreReducedTrivialization`) carries as a hypothesis. The engine's localized determinantal
presentation (`Core.DeterminantalBasePresentation`) is `N = 1` only: `basePresentationEquiv` lives
over `dStratum q p = ![q, p]`, a single matrix. This module builds, for a **general** dimension
vector `d : Fin (N + 1) → ℕ`, the deep localized chart ring `Sred` of the rank-`≤ r` product locus
on the pivot chart, and the localized base→total `k`-algebra map that gives `Sred` its
`SchurLoc`-algebra structure (the `R = SchurLoc`-algebra structure that R2-3a's `e` needs).

The deliverables, with `q = d 0` (source dimension) and `p = d (Fin.last N)` (target dimension):

**R2-3b-1 — the deep chart ring (definitions + instances + bridges).**
1. `ΔPdeep d r hp hq` — the deep pivot minor: the determinant of the top-left `r×r` submatrix of the
   **deep** generic product `Matrix.of (multPoly d)` (the deep analog of `N = 1`'s `detPivotPoly`).
2. `IadDeep d r hp hq` — the localized base ideal `(sigmaIdeal d r).map (algebraMap …)` pushed into
   `Localization.Away (ΔPdeep …)` (the deep analog of `Iad`).
3. `Sred d r hp hq := Localization.Away (ΔPdeep …) ⧸ IadDeep …` — the deep chart quotient ring, with
   its `CommRing` / `Algebra k` instances inherited, and `isReduced_Sred` : `IsReduced (Sred …)`
   (over `[IsAlgClosed k]`, justifying the name — this is R2-3a's `hSred`, now discharged).
4. The **type bridge** `repStratumEquiv : RepCoord (dStratum q p) ≃ Fin p × Fin q` (the
   single-matrix stratum coords), via `Equiv.uniqueSigma` (the `Sigma` over the `Unique` base
   `Fin 1`), and the deep base comorphism `deepBaseComap d` carrying the `N = 1` base coordinate
   ring into the deep total coordinate ring (`multComap d` after the rename).

**R2-3b-2 — the localized base→total map + the `SchurLoc`-algebra structure.**
5. `deepBaseComap_detPivot` — the load-bearing transport: `deepBaseComap d` carries the `N = 1`
   pivot minor `detPivotPoly` to the deep `ΔPdeep` (det commutes with `aeval`, `AlgHom.map_det`),
   making the localized map well-typed.
6. `deepBaseComap_sigmaIdeal_le` — the (non-circular) ideal direction: `deepBaseComap d` maps the
   base `sigmaIdeal (dStratum q p) r` into the deep `sigmaIdeal d r`. Mechanism: a **deep** total
   point
   `A ∈ Σ̄^r_d` maps by `mult` to a single-matrix **base** point in `Σ̄^r_{(q,p)}` (chase via
   `aeval_deepBaseComap` + `singleTuple`). It does **not** assume the circular `sigmaIdeal ≤
   fibreGenIdeal`.
7. `baseLocMap` / `schurToSred` — the localized base map `Localization.Away detPivotPoly →ₐ[k]
   Localization.Away (ΔPdeep …)` (`IsLocalization.Away.mapₐ`), lifted to the quotients
   (`Ideal.quotientMapₐ`), then composed with `basePresentationEquiv.symm` to give a `k`-algebra map
   `SchurLoc q p r →ₐ[k] Sred d r hp hq`. The resulting `SchurLoc`-algebra structure on `Sred`
   (`RingHom.toAlgebra`) + the `IsScalarTower k (SchurLoc …) (Sred …)` instance.

**Scope (what is NOT here).** The full product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg`, the
endpoint-normalization `AlgEquiv`, and the descent of the iso to the reduced chart quotient are
**R2-3b-3 and R2-3b-4** (later tides). No result here claims `codim (fibre) = C + δ` or discharges
`BundleShiftInterface` — `e` is not yet built. (R2-3a's *other* hypothesis, `IsReduced S`, **is**
discharged here: `isReduced_Sred`, so R2-3b-4 needs only `e` itself.) The R2-3b-3
endpoint-normalization `aeval`-substitution contract is pre-staged below as an `example` block (an
arbitrary coefficient ring `R`, via `AlgEquiv.ofAlgHom`, **not** `baseChangeAlgEquiv` which carries
`[Infinite k]`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## R2-3b-1 — the type bridge and the deep base comorphism

For the single-arrow stratum `dStratum q p = ![q, p]`, the coordinate index
`RepCoord (dStratum q p)` is a `Sigma` over `Fin 1`; collapsing it gives `Fin p × Fin q` (the
single-matrix entry coords). The deep base comorphism is the `N = 1` base coordinate map
`multComap d` precomposed with this rename. -/

/-- **The single-matrix stratum-coordinate bridge** `RepCoord (dStratum q p) ≃ Fin p × Fin q`. The
coordinate index of `dStratum q p = ![q, p]` is `Σ i : Fin 1, Fin (dStratum q p i.succ) ×
Fin (dStratum q p i.castSucc)`; over the `Unique` base `Fin 1` this is the single fibre
`Fin p × Fin q` (`default = 0`, `dStratum q p (0).succ = p`, `dStratum q p (0).castSucc = q`). -/
def repStratumEquiv (q p : ℕ) : RepCoord (dStratum q p) ≃ Fin p × Fin q :=
  Equiv.uniqueSigma (fun i : Fin 1 ↦ Fin (dStratum q p i.succ) × Fin (dStratum q p i.castSucc))

@[simp] theorem repStratumEquiv_mk (q p : ℕ) (x : Fin p × Fin q) :
    repStratumEquiv q p ⟨0, x⟩ = x := rfl

/-- **The deep base comorphism** `MvPolynomial (RepCoord (dStratum q p)) k →ₐ[k]
MvPolynomial (RepCoord d) k` (`q = d 0`, `p = d (last N)`): the `mult` comorphism `multComap d`
precomposed with the single-matrix coordinate rename. Carries the `N = 1` base coordinate ring into
the deep total coordinate ring. -/
noncomputable def deepBaseComap (d : Fin (N + 1) → ℕ) :
    MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k →ₐ[k]
      MvPolynomial (RepCoord d) k :=
  (multComap d).comp (renameEquiv k (repStratumEquiv (d 0) (d (Fin.last N)))).toAlgHom

/-- `deepBaseComap d` sends the single-matrix coordinate variable `X ⟨0, (a, b)⟩` to the deep
generic product entry `multPoly d a b`. -/
@[simp] theorem deepBaseComap_X (d : Fin (N + 1) → ℕ)
    (a : Fin (d (Fin.last N))) (b : Fin (d 0)) :
    deepBaseComap (k := k) d (X ⟨0, (a, b)⟩) = multPoly d a b := by
  rw [deepBaseComap]
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, renameEquiv_apply,
    rename_X, repStratumEquiv_mk, multComap_X]

/-! ## R2-3b-1 — the deep chart ring `Sred` -/

/-- **The deep pivot minor** `ΔPdeep d r`: the determinant of the top-left `r×r` submatrix of the
deep generic product `Matrix.of (multPoly d)`. The deep analog of `N = 1`'s `detPivotPoly`;
inverting it is the pivot chart. -/
noncomputable def ΔPdeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) : MvPolynomial (RepCoord d) k :=
  ((Matrix.of (multPoly d)).submatrix
    (fun i : Fin r ↦ (Fin.castLE hp i : Fin (d (Fin.last N))))
    (fun j : Fin r ↦ (Fin.castLE hq j : Fin (d 0)))).det

/-- **The deep localized base ideal** `IadDeep d r`: the determinantal base ideal `sigmaIdeal d r`
pushed into the localized total ring `Localization.Away (ΔPdeep …)`. The deep analog of `Iad`. -/
noncomputable def IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Ideal (Localization.Away (ΔPdeep (k := k) d r hp hq)) :=
  (sigmaIdeal d r).map (algebraMap (MvPolynomial (RepCoord d) k)
    (Localization.Away (ΔPdeep (k := k) d r hp hq)))

/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
chart quotient of the rank-`≤ r` product locus for general `d`, on the pivot chart. The `CommRing` /
`Algebra k` instances are inherited from the localization-quotient. -/
noncomputable abbrev Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) : Type u :=
  Localization.Away (ΔPdeep (k := k) d r hp hq) ⧸ IadDeep (k := k) d r hp hq

/-! ## R2-3b-1 — `Sred` is reduced (justifying the name; discharges R2-3a's `hSred`)

The name `Sred` asserts reducedness, and that reducedness is precisely R2-3a's second hypothesis
`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
carries radical
ideals to radical ideals (`IsLocalization.map_radical`); a quotient by a radical ideal is reduced
(`Ideal.isRadical_iff_quotient_reduced`). No quotient↔localization interchange iso is needed. -/

/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
base ideal `sigmaIdeal d r`. Via `IsLocalization.map_radical`
(`(I.map …).radical = I.radical.map …`) and `sigmaIdeal`'s radicality
(`vanishingIdeal_isRadical`). -/
theorem IadDeep_isRadical [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    (IadDeep (k := k) d r hp hq).IsRadical := by
  have hsig : (sigmaIdeal (k := k) d r).IsRadical := by
    rw [sigmaIdeal]; exact vanishingIdeal_isRadical _
  rw [← Ideal.radical_eq_iff, IadDeep,
    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
    hsig.radical]

/-- **`Sred` is reduced** (`[IsAlgClosed k]`), justifying the name.
`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
by a radical ideal is reduced
(`Ideal.isRadical_iff_quotient_reduced`). This is exactly R2-3a's `hSred : IsReduced S` for
`S = Sred` — so R2-3b-4 needs to build only `e` itself, not also `IsReduced S`. -/
theorem isReduced_Sred [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    IsReduced (Sred (k := k) d r hp hq) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (IadDeep_isRadical d r hp hq)

/-! ## R2-3b-2 — the load-bearing transports

`deepBaseComap` carries the `N = 1` pivot minor `detPivotPoly` to the deep `ΔPdeep` (making the
localized map well-typed), and the base `sigmaIdeal` into the deep `sigmaIdeal` (making the quotient
lift well-typed). -/

/-- **The pivot-minor transport** (load-bearing): `deepBaseComap d` carries the `N = 1` pivot minor
`detPivotPoly (d 0) (d last) r` to the deep pivot minor `ΔPdeep d r`. The determinant commutes with
the algebra map (`AlgHom.map_det`); each pivot entry `X ⟨0, (castLE i, castLE j)⟩` goes to
`multPoly d (castLE i) (castLE j)` (`deepBaseComap_X`), the corresponding entry of `Matrix.of
(multPoly d)`. (Exact analog of the landed `renameEquiv_detPivot`.) -/
theorem deepBaseComap_detPivot (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    deepBaseComap (k := k) d
        (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)
      = ΔPdeep (k := k) d r hp hq := by
  rw [detPivotPoly, ΔPdeep, AlgHom.map_det]
  congr 1
  funext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    show (Matrix.of (multPoly (k := k) (dStratum (d 0) (d (Fin.last N)))))
        (Fin.castLE hp i) (Fin.castLE hq j)
        = X ⟨0, (Fin.castLE hp i, Fin.castLE hq j)⟩ from multPoly_stratum_apply _ _ _ _,
    deepBaseComap_X]
  rfl

/-! ### The single-matrix tuple and the comorphism chase -/

/-- The **single-matrix tuple** over `dStratum q p` from a matrix `M : Mat (p × q)`: the `N = 1`
`Tuple` whose lone factor is `M`. -/
def singleTuple (k : Type u) [Field k] (q p : ℕ) (M : Matrix (Fin p) (Fin q) k) :
    Tuple (k := k) (dStratum q p) :=
  fun i ↦ match i with | 0 => M

/-- `mult` of the single-matrix tuple is its matrix (the `N = 1` product is the lone factor). -/
theorem mult_singleTuple (q p : ℕ) (M : Matrix (Fin p) (Fin q) k) :
    mult (dStratum q p) (singleTuple k q p M) = M := by
  rw [mult_stratum_eq q p (singleTuple k q p M)]; rfl

/-- **The comorphism chase.** Evaluating `deepBaseComap d f` at the coordinates of a deep tuple `A`
equals evaluating `f` at the coordinates of the single-matrix base tuple of `mult d A`. Both are
`k`-algebra maps in `f`; on the generator `X ⟨0, (a, b)⟩` both give `(mult d A) a b`
(`eval_multPoly`). -/
theorem aeval_deepBaseComap (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d)
    (f : MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k) :
    aeval (canonicalCoord d A) (deepBaseComap d f)
      = aeval (R := k) (canonicalCoord (dStratum (d 0) (d (Fin.last N)))
          (singleTuple k (d 0) (d (Fin.last N)) (mult (k := k) d A))) f := by
  have hgen : (aeval (canonicalCoord d A)).comp (deepBaseComap d)
      = aeval (R := k) (canonicalCoord (dStratum (d 0) (d (Fin.last N)))
          (singleTuple k (d 0) (d (Fin.last N)) (mult (k := k) d A))) := by
    apply MvPolynomial.algHom_ext
    intro x
    obtain ⟨i, a, b⟩ := x
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp only [AlgHom.comp_apply, deepBaseComap_X]
    rw [show aeval (R := k) (canonicalCoord d A) (multPoly d a b)
          = eval (canonicalCoord d A) (multPoly d a b) from by rw [aeval_def, eval]; rfl,
      eval_multPoly, aeval_X, canonicalCoord_apply]
    rfl
  exact DFunLike.congr_fun hgen f

/-- **The base→deep `sigmaIdeal` direction** (non-circular): `deepBaseComap d` maps the base
`sigmaIdeal (dStratum q p) r` into the deep `sigmaIdeal d r`. Via `Ideal.map_le_iff_le_comap`: a
base generator `f` vanishing on `Σ̄^r_{(q,p)}` pulls back to a polynomial vanishing on `Σ̄^r_d`,
because a **deep** total point `A ∈ Σ̄^r_d` maps by `mult` to a single-matrix **base** point in
`Σ̄^r_{(q,p)}` (`mult_singleTuple`, `rank (mult d A) ≤ r`), where `f` vanishes
(`aeval_deepBaseComap`).
Does **not** assume the circular `sigmaIdeal ≤ fibreGenIdeal`. -/
theorem deepBaseComap_sigmaIdeal_le (d : Fin (N + 1) → ℕ) (r : ℕ) :
    (sigmaIdeal (k := k) (dStratum (d 0) (d (Fin.last N))) r).map
        (deepBaseComap (k := k) d).toRingHom
      ≤ sigmaIdeal (k := k) d r := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, sigmaIdeal, mem_vanishingIdeal_iff]
  intro x hx
  obtain ⟨A, hA, rfl⟩ := hx
  rw [mem_productRankLocusLE] at hA
  change aeval (R := k) (canonicalCoord d A) ((deepBaseComap d).toRingHom f) = 0
  rw [show (deepBaseComap d).toRingHom f = deepBaseComap d f from rfl, aeval_deepBaseComap]
  rw [sigmaIdeal, mem_vanishingIdeal_iff] at hf
  exact hf _ ⟨singleTuple k (d 0) (d (Fin.last N)) (mult d A), by
    rw [mem_productRankLocusLE, mult_singleTuple]; exact hA, rfl⟩

/-! ## R2-3b-2 — the localized base map and the `SchurLoc`-algebra structure on `Sred`

The localized base map `Localization.Away detPivotPoly →ₐ[k] Localization.Away (ΔPdeep …)`
(`IsLocalization.Away.mapₐ deepBaseComap detPivotPoly`, well-typed by the transport
`deepBaseComap_detPivot`), lifted to the quotients (`Ideal.quotientMapₐ`, the ideal hypothesis
discharged by `deepBaseComap_sigmaIdeal_le`), then composed with `basePresentationEquiv.symm`. -/

/-- **The localized base map** `Localization.Away (detPivotPoly …) →ₐ[k]
Localization.Away (ΔPdeep …)`, `IsLocalization.Away.mapₐ` of the deep base comorphism
`deepBaseComap d` at `detPivotPoly`. The
codomain localization instance at `deepBaseComap d (detPivotPoly …)` is `ΔPdeep`'s (the transport
`deepBaseComap_detPivot`). -/
noncomputable def baseLocMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq) →ₐ[k]

exec
/bin/bash -lc "sed -n '1,240p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.MultComorphism
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# `DLNFibre.Core.FibreReducedTrivialization` — route-(b) reducedness via the trivialization

The route-(b) reducedness chain of `G2-3` (thread 17, R2-3), wired against the **trivialization** of
the rank-`r` chart as a hypothesis. The certified pen-and-paper input (thread 16) is that the fibre
ideal `I_E = (mult(Ã) − E)` is **radical** (`F_E = k[Ã]/I_E` **reduced**), for every `N ≥ 1`, every
dimension vector, every target (it depends only on `rank E`). The MECHANISM is that reducedness is
**inherited** from the reduced ambient rank-locus chart `Sred` via the **faithfully-flat product
trivialization** `S ≅ₐ[k] R ⊗_k F_E` (endpoint normalization), then **descends** to `F_E` over the
field `k`.

This module supplies, sorry-free and unconditionally, the **two ends of that chain** plus the
**closer that consumes it**, leaving the single open rung — the deep product trivialization `e`
itself, together with the reducedness `IsReduced S` of the chart ring — as an explicit
**hypothesis**, not an asserted fact:

1. **`isReduced_of_tensor`** — the tensor-with-a-field reducedness **descent** `F` reduced ⟸
   `R ⊗_k F` reduced (over a field `k`, any nontrivial `k`-algebra `R`). The "one open dependency"
   the thread-16 certificate flagged; here it is the direct `includeRight` injection
   (`Algebra.TensorProduct.includeRight_injective` + `isReduced_of_injective`), **not** the
   geometric `IsGeometricallyReduced` (which descends in the opposite direction).

2. **`fibreGenIdeal_isRadical_of_trivialization`** — the full route-(b) chain: given the
   trivialization `e : S ≃ₐ[k] R ⊗_k FibreAlg d B` and `IsReduced S` (the reduced chart ring),
   `R ⊗_k F_E` is reduced (transfer along `e`), hence `F_E` is reduced (descent (1)), hence
   `fibreGenIdeal d B` is **radical** (`Ideal.isRadical_iff_quotient_reduced`).

3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
   `MultComorphism` point 4: with the cut ideal radical, `vanishingIdeal (fibre d B) =
   radical (fibreGenIdeal d B) = fibreGenIdeal d B` — the `radical (·)` wrapper drops. This is the
   identity the height-squeeze (R2-5/R2-6, `height m_B = δ`) consumes.

**What is Proved vs Assumed here.** Everything above is proved sorry-free *given* the trivialization
`e : S ≃ₐ[k] R ⊗_k F_B` and `IsReduced S`, which are carried as **explicit hypotheses** — never as a
`sorry` or a global axiom. The deep trivialization `e` itself (the endpoint-normalization product
iso, built from a deep localized chart ring `S = O(Σ̄^r ∩ chart)`) is **not** constructed here: it
is the **open residual `G2-3` wall, R2-3b** (new scheme-free affine scaffolding — no deep localized
total ring exists in the engine yet, G2-2's machinery is `N = 1` only; ~5–8 modules). No downstream
result may claim `codim (fibre) = C + δ` or discharge `BundleShiftInterface` on the strength of
these conditional theorems while `e` is a hypothesis — that discharge waits for R2-3b to prove `e`.
The theorems here are an honest, clearly-labelled *conditional* pre-build of the downstream: every
consumer of `e` is **already proved against the hypothesis**, so R2-3b closes the chain with no
further reducedness work. (Codex's recommended build order for `e` is recorded in the thread's
`codex/algequiv-answer.md`.)

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The fibre coordinate algebra `F_E` -/

/-- The **fibre coordinate algebra** `F_B = k[Ã] / (mult(Ã) − B)`: the coordinate ring of the cut
scheme `mult⁻¹(B)`, i.e. `MvPolynomial (RepCoord d) k` modulo the fibre generator ideal. (`F_E` in
the certificate is this at the rank normal form `B = E`; the construction is uniform in `B`.) -/
abbrev FibreAlg (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) : Type u :=
  MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B

/-- `fibreGenIdeal d B` is radical **iff** `F_B` is reduced — the engine restatement of
`Ideal.isRadical_iff_quotient_reduced` for the fibre algebra. The bridge route-(b) crosses (the
geometric reducedness of `F_B` is exactly the radical-collapse the height-squeeze wants). -/
theorem fibreGenIdeal_isRadical_iff_isReduced_fibreAlg (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    (fibreGenIdeal d B).IsRadical ↔ IsReduced (FibreAlg d B) :=
  Ideal.isRadical_iff_quotient_reduced (fibreGenIdeal d B)

/-! ## The tensor-with-a-field reducedness descent (the pinned dependency)

`F` reduced ⟸ `R ⊗_k F` reduced over a field `k`. Direct via the **injection**
`includeRight : F →ₐ[k] R ⊗_k F` (a nonzero `k`-algebra `R` makes `algebraMap k R` injective, and
`F` is `k`-flat as a vector space, so `includeRight` is injective by
`Algebra.TensorProduct.includeRight_injective`), then `isReduced_of_injective`. This is the standard
char-0 descent the certificate named — but it needs only a field base and a nontrivial `R`. -/

/-- **Tensor-with-a-field reducedness descent.** Over a field `k`, for any nontrivial commutative
`k`-algebra `R` and commutative `k`-algebra `F`: if `R ⊗_k F` is reduced then `F` is reduced. The
injection `F ↪ R ⊗_k F` (`includeRight`, injective since `F` is `k`-flat and `algebraMap k R` is
injective) pulls back reducedness. -/
theorem isReduced_of_tensor {R F : Type u} [CommRing R] [Nontrivial R] [CommRing F]
    [Algebra k R] [Algebra k F] (h : IsReduced (R ⊗[k] F)) : IsReduced F :=
  letI := h
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : F →ₐ[k] R ⊗[k] F)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k R).injective)

/-! ## The route-(b) chain through the trivialization (the open rung as a hypothesis) -/

/-- **Route (b): `fibreGenIdeal` radical, through the trivialization.** Given the chart
trivialization `e : S ≃ₐ[k] R ⊗_k F_B` (the endpoint-normalization product iso) and that the chart
ring `S` is **reduced** (the engine's `Sred = (MvPol / sigmaIdeal)[1/ΔP]` is reduced, `sigmaIdeal`
a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
`S` reduced ⟹ `R ⊗_k F_B` reduced (transfer along `e.symm`) ⟹ `F_B` reduced (`isReduced_of_tensor`)
⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
theorem fibreGenIdeal_isRadical_of_trivialization
    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (R S : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
    (fibreGenIdeal d B).IsRadical := by
  letI := hSred
  -- `S` reduced ⟹ `R ⊗ F_B` reduced (it injects into `S` via `e.symm`)
  have hRF : IsReduced (R ⊗[k] FibreAlg d B) :=
    isReduced_of_injective e.symm.toRingEquiv e.symm.injective
  -- ⟹ `F_B` reduced (tensor-with-a-field descent) ⟹ `fibreGenIdeal` radical
  exact (fibreGenIdeal_isRadical_iff_isReduced_fibreAlg d B).mpr (isReduced_of_tensor (R := R) hRF)

/-- **The radical-collapse of `MultComorphism` point 4** (through the trivialization). With the cut
ideal radical (`fibreGenIdeal_isRadical_of_trivialization`), the engine's
`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
identity the height-squeeze (`height m_B = δ`, R2-5/R2-6) consumes. `[IsAlgClosed k]` (the
Nullstellensatz bridge). -/
theorem vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization [IsAlgClosed k]
    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (R S : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
    vanishingIdeal k (canonicalCoord d '' fibre d B) = fibreGenIdeal d B := by
  rw [vanishingIdeal_image_fibre_eq_radical,
    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]

/-! ## Non-vacuity witnesses

The descent (1) is non-vacuous over any field. The chain (2)/(3) is non-vacuous with `S := R ⊗ F_B`
and the identity equiv `e := AlgEquiv.refl` — exhibiting that the hypotheses are jointly satisfiable
(a reduced `S` admitting the iso), so the conclusions are not vacuously
derived from contradictory hypotheses. -/

section Witness

/-- The tensor-descent fires over `ℚ` (a field) for `R = ℚ`, `F = ℚ`: `ℚ ⊗_ℚ ℚ` reduced ⟹ `ℚ`
reduced — non-vacuous. -/
example (h : IsReduced (ℚ ⊗[ℚ] ℚ)) : IsReduced ℚ := isReduced_of_tensor (k := ℚ) h

/-- The chain's hypotheses are jointly satisfiable: with `S := R ⊗_k F_B`, `R` a nontrivial reduced
domain and `F_B` reduced, the identity equiv `e := AlgEquiv.refl` and `IsReduced S` discharge the
hypotheses of `fibreGenIdeal_isRadical_of_trivialization` — so the theorem is not vacuous. (Here the
content is the *shape* of the contract; the genuine `e` for the rank chart is the deferred rung.) -/
example [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (R : Type u) [CommRing R] [Nontrivial R]
    [Algebra k R] [IsReduced (R ⊗[k] FibreAlg d B)] :
    (fibreGenIdeal d B).IsRadical :=
  fibreGenIdeal_isRadical_of_trivialization d B R (R ⊗[k] FibreAlg d B)
    (AlgEquiv.refl) ‹_›

end Witness

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '1,260p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.DeterminantalBasePresentation

/-!
# `DLNFibre.Core.SchurGauge` — the Schur-valued pivot block as a `SchurLoc`-unit (route-(c) rung 2)

The first easier piece of the route-(c) pivot-chart trivialization (thread 31 rung 2): the pivot
block `schurΔ` (the top-left `r×r` submatrix of the generic base matrix, in the `SchurVar`
coordinates), mapped into the localization `SchurLoc = Localization.Away detSchurS`, is an
**invertible matrix**. Its determinant is `detSchurS`, the very element inverted in `SchurLoc`. It
is the unit out of which the endpoint normalizing gauge `L`, `H` (Schur-complement blocks) is built
— the `BaseChangeGroup` element over `SchurLoc` that drives the chart `AlgEquiv`.

This module stays strictly at the `varietyDim`/radical level (the `VarietyDimRadical` shield); it
never re-enters the strict-ideal / reducedness level that walled R2-3b-4.

## Main results
- `schurΔLoc` — the pivot block over `SchurLoc`.
- `det_schurΔLoc` — its determinant is `detSchurS` pushed into `SchurLoc`.
- `isUnit_det_schurΔLoc` — that determinant is a unit (inverted in `SchurLoc`).
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k]

/-- The pivot block `schurΔ` mapped into the localization
`SchurLoc = Localization.Away detSchurS`. -/
noncomputable def schurΔLoc (q p r : ℕ) :
    Matrix (Fin r) (Fin r) (SchurLoc (k := k) q p r) :=
  (schurΔ (k := k) q p r).map (algebraMap _ _)

/-- The determinant of `schurΔLoc` is `detSchurS`, pushed into `SchurLoc`. (`detSchurS` is by
definition `det schurΔ`, and `det` commutes with the algebra map.) -/
theorem det_schurΔLoc (q p r : ℕ) :
    (schurΔLoc (k := k) q p r).det
      = algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
          (detSchurS (k := k) q p r) :=
  (RingHom.map_det (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r))
    (schurΔ (k := k) q p r)).symm

/-- **The pivot block is invertible over `SchurLoc`.** Its determinant `detSchurS` is the element
inverted in `SchurLoc = Localization.Away detSchurS`, hence a unit. -/
theorem isUnit_det_schurΔLoc (q p r : ℕ) : IsUnit (schurΔLoc (k := k) q p r).det := by
  rw [det_schurΔLoc]
  exact IsLocalization.Away.algebraMap_isUnit (detSchurS q p r)

/-- The pivot block is invertible as a matrix over `SchurLoc` (det is a unit, in a commutative
ring). -/
theorem isUnit_schurΔLoc (q p r : ℕ) : IsUnit (schurΔLoc (k := k) q p r) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_schurΔLoc (k := k) q p r)

/-! ## The Schur off-diagonal blocks `B12`, `B21` over `SchurLoc`

The `SchurVar` coordinate type is `(Fin r × Fin r) ⊕ ((Fin r × Fin (q−r)) ⊕ (Fin (p−r) × Fin r))`:
the pivot `Δ` is `Sum.inl`, the `B12` block is `Sum.inr ∘ Sum.inl`, the `B21` block is
`Sum.inr ∘ Sum.inr`. We read each off-diagonal block directly off those coordinates, pushed into
`SchurLoc`. -/

/-- The `B12` block (`Fin r × Fin (q−r)`) over `SchurLoc`, from the `Sum.inr ∘ Sum.inl` coords. -/
noncomputable def schurB12Loc (q p r : ℕ) :
    Matrix (Fin r) (Fin (q - r)) (SchurLoc (k := k) q p r) :=
  Matrix.of fun i j ↦ algebraMap (MvPolynomial (SchurVar q p r) k) _
    (X (Sum.inr (Sum.inl (i, j))))

/-- The `B21` block (`Fin (p−r) × Fin r`) over `SchurLoc`, from the `Sum.inr ∘ Sum.inr` coords. -/
noncomputable def schurB21Loc (q p r : ℕ) :
    Matrix (Fin (p - r)) (Fin r) (SchurLoc (k := k) q p r) :=
  Matrix.of fun i j ↦ algebraMap (MvPolynomial (SchurVar q p r) k) _
    (X (Sum.inr (Sum.inr (i, j))))

/-! ## The endpoint normalizing units `L`, `H`

The pivot-cell factorization `M = L · E · H` (`M` the rank-`r` generic product over `SchurLoc`):
- `L` (`p × p`, the `d_N`-vertex unit): lower-unitriangular `[[I, 0], [B21 · Δ⁻¹, I]]`.
- `H` (`q × q`, the `d_0`-vertex unit): upper-triangular `[[Δ, B12], [0, I]]`.

Each is built block-wise over `Fin r ⊕ Fin (n−r)` (where `isUnit_fromBlocks_zero₁₂/₂₁` makes
invertibility immediate from the diagonal blocks), then reindexed to `Fin n` by the pivot split
`finSplit`. Both are units over `SchurLoc` — `Δ⁻¹` exists there (`isUnit_schurΔLoc`). -/

/-- The lower-unitriangular `L` block, `[[I, 0], [B21 · Δ⁻¹, I]]`, on `Fin r ⊕ Fin (p−r)`. -/
noncomputable def LblockSum (q p r : ℕ) :
    Matrix (Fin r ⊕ Fin (p - r)) (Fin r ⊕ Fin (p - r)) (SchurLoc (k := k) q p r) :=
  Matrix.fromBlocks 1 0 (schurB21Loc q p r * (schurΔLoc q p r)⁻¹) 1

/-- The upper-triangular `H` block, `[[Δ, B12], [0, I]]`, on `Fin r ⊕ Fin (q−r)`. -/
noncomputable def HblockSum (q p r : ℕ) :
    Matrix (Fin r ⊕ Fin (q - r)) (Fin r ⊕ Fin (q - r)) (SchurLoc (k := k) q p r) :=
  Matrix.fromBlocks (schurΔLoc q p r) (schurB12Loc q p r) 0 1

/-- `L` as a `p × p` matrix over `SchurLoc` (the `LblockSum` reindexed by the pivot split). -/
noncomputable def Lmat (q p r : ℕ) (hp : r ≤ p) :
    Matrix (Fin p) (Fin p) (SchurLoc (k := k) q p r) :=
  reindexAlgEquiv (SchurLoc (k := k) q p r) (SchurLoc (k := k) q p r) (finSplit hp).symm
    (LblockSum q p r)

/-- `H` as a `q × q` matrix over `SchurLoc` (the `HblockSum` reindexed by the pivot split). -/
noncomputable def Hmat (q p r : ℕ) (hq : r ≤ q) :
    Matrix (Fin q) (Fin q) (SchurLoc (k := k) q p r) :=
  reindexAlgEquiv (SchurLoc (k := k) q p r) (SchurLoc (k := k) q p r) (finSplit hq).symm
    (HblockSum q p r)

/-- `L` is a unit: lower-unitriangular (diagonal `I`, `I`), reindexing preserves units. -/
theorem isUnit_Lmat (q p r : ℕ) (hp : r ≤ p) : IsUnit (Lmat (k := k) q p r hp) := by
  apply IsUnit.map
  rw [LblockSum, isUnit_fromBlocks_zero₁₂]
  exact ⟨isUnit_one, isUnit_one⟩

/-- `H` is a unit: upper-triangular with diagonal `Δ` (a unit) and `I`. -/
theorem isUnit_Hmat (q p r : ℕ) (hq : r ≤ q) : IsUnit (Hmat (k := k) q p r hq) := by
  apply IsUnit.map
  rw [HblockSum, isUnit_fromBlocks_zero₂₁]
  exact ⟨isUnit_schurΔLoc q p r, isUnit_one⟩

/-! ## The endpoint gauge as a `BaseChangeGroup` over `SchurLoc`

The pivot-cell factorization `M = L · E · H` is realized as a base-change datum acting on `Tuple d`
over `SchurLoc`: the source-vertex unit (`v = 0`, dimension `d 0 = q`) is `H`, the target-vertex
unit (`v = last N`, dimension `d (last N) = p`) is `L⁻¹`, and every interior vertex is `1` (those
units telescope away in `mult`). The dependent dimension `Fin (d v)` is aligned to `Fin q`/`Fin p`
by a `cast` along `v = 0` / `v = last N`. -/

/-- **The endpoint normalizing gauge** as a `BaseChangeGroup` over `SchurLoc`: `H` at the source
vertex, `L⁻¹` at the target vertex, `1` interior. -/
noncomputable def endpointGauge (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    BaseChangeGroup (k := SchurLoc (k := k) (d 0) (d (Fin.last N)) r) d :=
  fun v ↦
    if hv0 : v = 0 then
      cast (by rw [hv0]) (isUnit_Hmat (k := k) (d 0) (d (Fin.last N)) r hq).unit
    else if hvl : v = Fin.last N then
      cast (by rw [hvl]) (isUnit_Lmat (k := k) (d 0) (d (Fin.last N)) r hp).unit⁻¹
    else 1

/-- The source-vertex unit of the endpoint gauge is `H` (the `cast` at `v = 0` is the identity). -/
theorem endpointGauge_zero (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    (endpointGauge (k := k) d r hp hq) 0
      = (isUnit_Hmat (k := k) (d 0) (d (Fin.last N)) r hq).unit := by
  unfold endpointGauge; rw [dif_pos rfl]; rfl

/-- The target-vertex unit of the endpoint gauge is `L⁻¹` (the `cast` at `v = last N` is the
identity; needs `N ≥ 1` so `last N ≠ 0`). -/
theorem endpointGauge_last {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (endpointGauge (k := k) d r hp hq) (Fin.last (N + 1))
      = (isUnit_Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).unit⁻¹ := by
  unfold endpointGauge
  rw [dif_neg Fin.last_pos.ne', dif_pos rfl]; rfl

/-! ## The Schur-complement normal-form identity

The pivot-cell factorization, abstractly: for a block matrix `M = [[Δ, B12], [B21, B22]]` over a
commutative ring with `Δ` invertible and `B22 = B21 Δ⁻¹ B12` (the rank-`r` / fibre condition),
`L⁻¹ · M · H⁻¹ = diag(I_r, 0)`, where `L = [[I,0],[B21 Δ⁻¹,I]]`, `H = [[Δ,B12],[0,I]]` (so
`L⁻¹ = [[I,0],[−B21 Δ⁻¹,I]]`, `H⁻¹ = [[Δ⁻¹,−Δ⁻¹ B12],[0,I]]`). The matrix heart of the chart
normalization; network-free, over any `CommRing`. -/

/-- **Schur-complement normal form** (block form). With `Δ` invertible and the Schur relation
`B22 = B21 Δ⁻¹ B12`, the lower/upper unitriangular conjugation collapses `M` to `diag(I_r, 0)`. -/
theorem schurComplement_normal_form {R : Type*} [CommRing R] {r s t : ℕ}
    (Δ : Matrix (Fin r) (Fin r) R) (B12 : Matrix (Fin r) (Fin t) R)
    (B21 : Matrix (Fin s) (Fin r) R) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) R) (0 : Matrix (Fin r) (Fin s) R)
        (-(B21 * Δ⁻¹)) (1 : Matrix (Fin s) (Fin s) R))
      * (Matrix.fromBlocks Δ B12 B21 (B21 * Δ⁻¹ * B12))
      * (Matrix.fromBlocks Δ⁻¹ (-(Δ⁻¹ * B12)) (0 : Matrix (Fin t) (Fin r) R)
          (1 : Matrix (Fin t) (Fin t) R))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) R) 0 0 0 := by
  have hinv : Δ * Δ⁻¹ = 1 := Matrix.mul_nonsing_inv Δ hΔ
  have hinv' : Δ⁻¹ * Δ = 1 := Matrix.nonsing_inv_mul Δ hΔ
  have c1 : B21 * Δ⁻¹ * Δ = B21 := by rw [Matrix.mul_assoc, hinv', Matrix.mul_one]
  have c2 : Δ * (Δ⁻¹ * B12) = B12 := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj.mpr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_zero, hinv]
  · simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.mul_neg, c2,
      neg_add_cancel]
  · rw [Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.neg_mul, c1, Matrix.add_mul,
      Matrix.neg_mul, neg_add_cancel]
  · rw [Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, c1, Matrix.one_mul, Matrix.add_mul,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc B21 Δ⁻¹ B12]
    abel

end DLNFibre.Core

/-- Non-vacuity witness: at `(q,p,r) = (2,2,1)` over `ℚ`, the `1×1` pivot block over `SchurLoc` is
invertible (the existential is inhabited). -/
example : IsUnit (DLNFibre.Core.schurΔLoc (k := ℚ) 2 2 1).det :=
  DLNFibre.Core.isUnit_det_schurΔLoc 2 2 1

codex
The important shape is clear: `endpointGauge` is currently a `BaseChangeGroup` over `SchurLoc`, while `IadDeep` sits in the total localization. I’m checking whether there is an existing coefficient-extension/transport API for `BaseChangeGroup` or `gaugeEquiv`; if not, rebuilding over the target ring is the low-friction path.
exec
/bin/bash -lc "sed -n '260,620p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
    Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq) →ₐ[k]
      Localization.Away (ΔPdeep (k := k) d r hp hq) := by
  haveI : IsLocalization.Away
      (deepBaseComap (k := k) d (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq))
      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
    rw [deepBaseComap_detPivot]; infer_instance
  exact IsLocalization.Away.mapₐ _ _ (deepBaseComap d)
    (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)

/-- `baseLocMap` sends `algebraMap … x` to `algebraMap … (deepBaseComap d x)` — it intertwines the
two localization maps (`IsLocalization.Away.mapₐ` / `IsLocalization.map` on the base ring). -/
theorem baseLocMap_algebraMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0)
    (x : MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k) :
    baseLocMap (k := k) d r hp hq
        (algebraMap (MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k)
          (Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)) x)
      = algebraMap (MvPolynomial (RepCoord d) k) (Localization.Away (ΔPdeep (k := k) d r hp hq))
          (deepBaseComap d x) := by
  haveI : IsLocalization.Away
      (deepBaseComap (k := k) d (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq))
      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
    rw [deepBaseComap_detPivot]; infer_instance
  rw [baseLocMap, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rfl

/-- The base ideal `Iad` is carried into `IadDeep` by `baseLocMap`
(`Iad ≤ IadDeep.comap baseLocMap`), the hypothesis the quotient lift needs. `Iad`/`IadDeep` are the
localized images of the base / deep
`sigmaIdeal`s; `baseLocMap` intertwines the localization maps (`baseLocMap_algebraMap`) and carries
the base `sigmaIdeal` into the deep one (`deepBaseComap_sigmaIdeal_le`). -/
theorem Iad_le_comap_IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Iad (k := k) (d 0) (d (Fin.last N)) r hp hq
      ≤ (IadDeep (k := k) d r hp hq).comap (baseLocMap (k := k) d r hp hq) := by
  rw [Iad, Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap, Ideal.mem_comap, baseLocMap_algebraMap, IadDeep]
  -- `deepBaseComap g ∈ sigmaIdeal d r` (the base → deep direction), then push into the localization
  have hmem : deepBaseComap (k := k) d g ∈ sigmaIdeal (k := k) d r :=
    deepBaseComap_sigmaIdeal_le d r (Ideal.mem_map_of_mem _ hg)
  exact Ideal.mem_map_of_mem _ hmem

/-- **The localized base→total map on the quotients** `(Localization.Away detPivotPoly ⧸ Iad) →ₐ[k]
Sred d r`: the quotient lift of `baseLocMap` (`Ideal.quotientMapₐ`, the ideal hypothesis from
`Iad_le_comap_IadDeep`). -/
noncomputable def baseQuotMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    (Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)
        ⧸ Iad (k := k) (d 0) (d (Fin.last N)) r hp hq)
      →ₐ[k] Sred (k := k) d r hp hq :=
  Ideal.quotientMapₐ (IadDeep (k := k) d r hp hq) (baseLocMap (k := k) d r hp hq)
    (Iad_le_comap_IadDeep d r hp hq)

/-- **The base→total `k`-algebra map** `SchurLoc q p r →ₐ[k] Sred d r` (`q = d 0`, `p = d last`):
`baseQuotMap` precomposed with `basePresentationEquiv.symm`. This is the morphism whose induced
algebra structure makes `Sred` a `SchurLoc`-algebra (the `R = SchurLoc`-algebra structure that
R2-3a's product iso `e` needs). `[IsAlgClosed k] [CharZero k]` (for `basePresentationEquiv`). -/
noncomputable def schurToSred [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    SchurLoc (k := k) (d 0) (d (Fin.last N)) r →ₐ[k] Sred (k := k) d r hp hq :=
  (baseQuotMap (k := k) d r hp hq).comp
    (basePresentationEquiv (k := k) (d 0) (d (Fin.last N)) r hp hq).symm.toAlgHom

/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower

The base→total map `schurToSred` induces (via `RingHom.toAlgebra`) the `SchurLoc q p r`-algebra
structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/

/-- **The `SchurLoc`-algebra structure on `Sred`**, induced by the base→total map `schurToSred`
(`RingHom.toAlgebra`). The `R = SchurLoc q p r`-algebra structure R2-3a's product iso `e` needs. -/
@[reducible] noncomputable def sredSchurAlgebra [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ)
    (r : ℕ) (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq) :=
  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra

/-- The induced `SchurLoc`-algebra structure on `Sred` makes `k → SchurLoc q p r → Sred` a scalar
tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
localization-quotient maps are `k`-algebra maps). -/
theorem sredSchur_isScalarTower [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    @IsScalarTower k (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq)
      _ (sredSchurAlgebra (k := k) d r hp hq).toSMul _ := by
  letI := sredSchurAlgebra (k := k) d r hp hq
  refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
  -- `algebraMap (SchurLoc …) Sred = schurToSred.toRingHom` (by `toAlgebra`); `schurToSred` is a
  -- `k`-algebra map, so it commutes with `algebraMap k (SchurLoc …)` (`AlgHom.commutes`).
  change algebraMap k (Sred (k := k) d r hp hq) x
      = (schurToSred (k := k) d r hp hq).toRingHom (algebraMap k _ x)
  exact (AlgHom.commutes (schurToSred (k := k) d r hp hq) x).symm

/-! ## R2-3b-3 pre-stage (durable contract, NOT proved here)

The endpoint-normalization `AlgEquiv` for R2-3b-3 is an `aeval`-substitution on the **unquotiented**
`MvPolynomial (RepCoord d) R` over an **arbitrary** coefficient ring `R` (Codex: NOT
`baseChangeAlgEquiv`, which carries `[Infinite k]` from polynomial-function ext). The contract — two
`aeval` substitutions that round-trip on generators, assembled by `AlgEquiv.ofAlgHom` — is pinned
here so R2-3b-3 inherits the exact shape. (`example`: the contract, not the genuine
substitution.) -/

/-- **R2-3b-3 pre-stage contract.** Two coordinate substitutions `toSub`, `fromSub : RepCoord d →
MvPolynomial (RepCoord d) R` over an arbitrary commutative ring `R`, mutually inverse on the
generators, assemble to a coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R` via
`AlgEquiv.ofAlgHom` (each direction an `aeval`; the round-trips by `MvPolynomial.algHom_ext` +
`aeval_X`). The endpoint-normalization substitution of R2-3b-3 instantiates this. -/
noncomputable example {R : Type u} [CommRing R] (d : Fin (N + 1) → ℕ)
    (toSub fromSub : RepCoord d → MvPolynomial (RepCoord d) R)
    (h_to_from : ∀ x, aeval toSub (fromSub x) = (X x : MvPolynomial (RepCoord d) R))
    (h_from_to : ∀ x, aeval fromSub (toSub x) = (X x : MvPolynomial (RepCoord d) R)) :
    MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R :=
  AlgEquiv.ofAlgHom (aeval toSub) (aeval fromSub)
    (by
      apply MvPolynomial.algHom_ext
      intro x
      change aeval toSub (aeval fromSub (X x)) = _
      rw [aeval_X]; exact h_to_from x)
    (by
      apply MvPolynomial.algHom_ext
      intro x
      change aeval fromSub (aeval toSub (X x)) = _
      rw [aeval_X]; exact h_from_to x)

/-! ## Non-vacuity witnesses

The deep constructions fire on the `N = 1` specialization `(d 0, d last) = (q, p)`, where they
reproduce the `N = 1` base data. We exhibit (i) the type bridge at `(2, 2)`, (ii) `deepBaseComap` /
`deepBaseComap_detPivot` at the `N = 1` stratum `dStratum 2 2`, `r = 1`, where the deep pivot minor
**is** the `N = 1` `detPivotPoly` (`deepBaseComap` is the identity-up-to-rename there), and (iii)
the localized base→total quotient map `baseQuotMap` available at that anchor over
`AlgebraicClosure ℚ`. -/

section Witness

/-- The type bridge `RepCoord (dStratum 2 2) ≃ Fin 2 × Fin 2` round-trips on a concrete coordinate
(the `(1, 0)` entry of the single matrix). -/
example : repStratumEquiv 2 2 ⟨0, (⟨1, by norm_num⟩, ⟨0, by norm_num⟩)⟩
    = (⟨1, by norm_num⟩, ⟨0, by norm_num⟩) := rfl

/-- `deepBaseComap` at the `N = 1` stratum `dStratum 2 2` sends `X ⟨0, (a, b)⟩` to the deep generic
product entry `multPoly (dStratum 2 2) a b` — non-vacuous (`N = 1` specialization). -/
example (a : Fin (dStratum 2 2 (Fin.last 1))) (b : Fin (dStratum 2 2 0)) :
    deepBaseComap (k := AlgebraicClosure ℚ) (dStratum 2 2) (X ⟨0, (a, b)⟩)
      = multPoly (dStratum 2 2) a b :=
  deepBaseComap_X _ a b

/-- The pivot-minor transport fires at the `N = 1` stratum `dStratum 2 2`, `r = 1`:
`deepBaseComap (detPivotPoly …) = ΔPdeep …`. -/
example (h : (1 : ℕ) ≤ 2) :
    deepBaseComap (k := AlgebraicClosure ℚ) (dStratum 2 2)
        (detPivotPoly (k := AlgebraicClosure ℚ) (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
      = ΔPdeep (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
  deepBaseComap_detPivot (dStratum 2 2) 1 h h

/-- The localized base→total quotient map `baseQuotMap` is available at the `N = 1` anchor
`dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — non-vacuous. (It needs no `IsAlgClosed` /
`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
noncomputable example (h : (1 : ℕ) ≤ 2) :
    (Localization.Away
          (detPivotPoly (k := AlgebraicClosure ℚ)
            (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
        ⧸ Iad (k := AlgebraicClosure ℚ) (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
      →ₐ[AlgebraicClosure ℚ] Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
  baseQuotMap (dStratum 2 2) 1 h h

/-- `Sred` is reduced at the `N = 1` anchor `dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — the
name is honest there, and R2-3a's `hSred` is discharged. -/
example (h : (1 : ℕ) ≤ 2) :
    IsReduced (Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h) :=
  isReduced_Sred (dStratum 2 2) 1 h h

end Witness

end DLNFibre.Core

exec
/bin/bash -lc 'rg -n "def .*Gauge|theorem .*Gauge|gaugeEquiv|BaseChangeGroup|baseChange|map.*BaseChange|coeff|AlgEquiv.ofAlgHom|quotientEquivAlg|radical_eq|ringKrullDim.*radical|poly.*extension|tensor.*quotient|quotient.*tensor" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesOrth.lean:11:This is the coefficient form of `(x;q)_∞ · (x;q)_∞^{-1} = 1`. Mathlib v4.29 has no `q`-binomial /
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:21:  vertex; the partner sits at coefficient exactly `−1` and "shortest covering" kills all positive
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:22:  coefficients, so `delta ≤ −1 < 0`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:289:/-! ## The strict split delta: a present partner at coefficient `−1`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:291:The `codimForm_*_le` sign lemmas of `Core.CCodimZeroMono` bound the split delta `∑_Y m̄ Y · coeff Y`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:292:by `0` (positive coeffs killed by minimality). The strict upgrade: a *present* partner interval `B`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:293:(`m B ≥ 1`) at coefficient `≤ −1` forces `∑ ≤ −1`. The generic sum lemma below feeds each move's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:294:`coeff`/`_pos_imp` plus the partner. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:296:/-- **Generic strict sum bound.** If every interval with a *positive* coefficient has multiplicity `0`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:297:(minimality kills positives) and some present interval `B` (`m B ≥ 1`) has coefficient `≤ −1`, then
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:298:`∑_Y m̄ Y · coeff Y ≤ −1`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:299:theorem sum_coeff_le_neg_one (m : Fin (N + 1) × Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:300:    (coeff : Fin (N + 1) × Fin (N + 1) → ℤ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:301:    (hkill : ∀ Y, 0 < coeff Y → m Y = 0)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:302:    {B : Fin (N + 1) × Fin (N + 1)} (hB : 1 ≤ m B) (hBc : coeff B ≤ -1) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:303:    ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * coeff Y ≤ -1 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:306:  have hnonpos : ∀ Y, (m Y : ℤ) * coeff Y ≤ 0 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:308:    rcases lt_or_ge 0 (coeff Y) with hc | hc
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:312:  have hBterm : (m B : ℤ) * coeff B ≤ -1 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:313:    calc (m B : ℤ) * coeff B ≤ (m B : ℤ) * (-1) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:321:  have hrest : ∑ Y ∈ Finset.univ.erase B, (m Y : ℤ) * coeff Y ≤ 0 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:325:/-! ### Partner coefficients are `≤ −1` (`omega` on the indicator combinations)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:328:partner-adjacent vertex assigns `B` coefficient exactly `−1`; symmetrically when `[a,d']` is the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:390:same shortest-covering hypothesis `hshort` (kills positive coefficients) plus a *present* partner
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:391:interval at coefficient `≤ −1`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:408:  have := sum_coeff_le_neg_one m (splitCoeff a b c d') hkill hPpres hPc
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:426:  have := sum_coeff_le_neg_one m (leftCoeff a c d') hkill hPpres hPc
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:444:  have := sum_coeff_le_neg_one m (rightCoeff a b d') hkill hPpres hPc
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:534:/-- **`removeMove` strict.** Singleton `[a,a]` present, plus a present partner at coefficient `≤ −1`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:544:  have := sum_coeff_le_neg_one m (removeCoeff a) hkill hPpres hPc
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:552:atomic move) has the partner at coefficient `−1`, so `codimForm` drops by `≥ 1`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:257:  · -- surjectivity: range = ker(mapBaseChange) = everything since Ω[k/k] = 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:270:cokernel of the base-changed conormal inclusion: the `B`-submodule `K := ker (mapBaseChange) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:272:theorem tensorKaehler_equiv_quotient_conormal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:278:          (LinearMap.ker (KaehlerDifferential.mapBaseChange k R B)).subtype).restrictScalars k))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:280:  -- `Ω[B⁄k] = (B ⊗[R] Ω[R⁄k]) ⧸ K` via `mapBaseChange`, `K = ker(mapBaseChange)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:281:  have hfsurj : Function.Surjective (KaehlerDifferential.mapBaseChange k R B) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:282:    KaehlerDifferential.mapBaseChange_surjective k R B hsurj
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:283:  -- exactness of the inclusion `K ↪ B⊗Ω` and `mapBaseChange`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:285:      (LinearMap.ker (KaehlerDifferential.mapBaseChange k R B)).subtype
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:286:      (KaehlerDifferential.mapBaseChange k R B) := (LinearMap.exact_subtype_ker_map _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:289:        (LinearMap.ker (KaehlerDifferential.mapBaseChange k R B)).subtype).restrictScalars k)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:290:      ((LinearMap.lTensor k (KaehlerDifferential.mapBaseChange k R B)).restrictScalars k) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:293:      ((LinearMap.lTensor k (KaehlerDifferential.mapBaseChange k R B)).restrictScalars k) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:341:  obtain ⟨eExact⟩ := tensorKaehler_equiv_quotient_conormal (k := k)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:344:  -- Pin `Module A A` to `Semiring.toModule` so both `baseChange` steps use the same self-module.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:351:    (((KaehlerDifferential.mvPolynomialBasis k σ).baseChange
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:352:      (MvPolynomial σ k ⧸ Ideal.span (Set.range g))).baseChange k).equivFun
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:361:    simp only [Ψ, Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:367:  -- `K := ker(mapBaseChange)` is `B`-spanned by the conormal generators `1 ⊗ D(g i)`; base-changing
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:370:      ((LinearMap.lTensor k (LinearMap.ker (KaehlerDifferential.mapBaseChange k (MvPolynomial σ k)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:373:    set K := LinearMap.ker (KaehlerDifferential.mapBaseChange k (MvPolynomial σ k)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:404:    -- LHS range = `K.baseChange k` = `span k (range tgen)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:407:      change K.baseChange k = _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:408:      rw [hKspanB, Submodule.baseChange_span, ← Set.range_comp]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:53:arbitrary coefficient ring `R`, via `AlgEquiv.ofAlgHom`, **not** `baseChangeAlgEquiv` which carries
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:147:  rw [← Ideal.radical_eq_iff, IadDeep,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:356:`MvPolynomial (RepCoord d) R` over an **arbitrary** coefficient ring `R` (Codex: NOT
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:357:`baseChangeAlgEquiv`, which carries `[Infinite k]` from polynomial-function ext). The contract — two
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:358:`aeval` substitutions that round-trip on generators, assembled by `AlgEquiv.ofAlgHom` — is pinned
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:365:`AlgEquiv.ofAlgHom` (each direction an `aeval`; the round-trips by `MvPolynomial.algHom_ext` +
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:372:  AlgEquiv.ofAlgHom (aeval toSub) (aeval fromSub)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:20:* `baseChange_normalForm` — **the Gabriel normal-form object** (cast-free): every tuple is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:24:`RankPattern.cumulDiffEquiv` + the realizability in `baseChange_normalForm` assemble into a genuine
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:27:**Typeclass.** `Field k` (the barcode existence; `Tuple`/`baseChange` themselves only need
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:45:    (P : BaseChangeGroup (k := k) d) (h : P • A = B) (i j : Fin (N + 1)) (hij : i ≤ j) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:130:theorem baseChange_of_intertwine {d : Fin (N + 1) → ℕ} (A B : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:134:    ∃ P : BaseChangeGroup (k := k) d, P • A = B := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:145:  rw [smul_eq_baseChange, baseChange_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:161:intertwiner `φ_t` of the two `mulVecLin` chains, which `baseChange_of_intertwine` turns into the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:166:    ∃ P : BaseChangeGroup (k := k) d, P • A = B := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:250:  refine baseChange_of_intertwine A B φ (fun e ↦ (bvA e.castSucc).ext (fun s ↦ ?_))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:269:      ↔ ∃ P : BaseChangeGroup (k := k) d, P • A = B :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:340:theorem baseChange_normalForm {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:341:    ∃ (L : List (Fin (N + 1) × Fin (N + 1))) (h : foldDim L = d) (P : BaseChangeGroup (k := k) d),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:369:list `L` of `baseChange_normalForm` has its multiplicity array pinned by `A`'s rank pattern: there
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:373:`diff_cumul` inversion of the cumulative equality in `baseChange_normalForm`; makes the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:376:    ∃ (L : List (Fin (N + 1) × Fin (N + 1))) (h : foldDim L = d) (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:381:  obtain ⟨L, h, P, hP, hbd, hcum⟩ := baseChange_normalForm A
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:403:object `baseChange_normalForm` fires on the witness — so the complete invariant and the Gabriel
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:414:def witnessBaseChangeQ : BaseChangeGroup (k := ℚ) dWitness :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:423:example : ∃ Q : BaseChangeGroup (k := ℚ) dWitness,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:432:    ↔ ∃ Q : BaseChangeGroup (k := ℚ) dWitness,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:519:    (P : BaseChangeGroup (k := ℚ) dWitness),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:521:  obtain ⟨L, h, P, hP, _, _⟩ := baseChange_normalForm tupleWitnessRankOneQ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:527:    (P : BaseChangeGroup (k := ℚ) dWitness), P • tupleWitnessQ = h ▸ intervalDirectSum L := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:528:  obtain ⟨L, h, P, hP, _, _⟩ := baseChange_normalForm tupleWitnessQ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:13:- `submult_baseChange` / `submult_smul` — **telescoping conjugation** of the interval sub-product:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:17:- `rankPattern_baseChange` / `rankPattern_smul` — **rank-pattern base-change invariance**:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:41:abbrev BaseChangeGroup (d : Fin (N + 1) → ℕ) : Type u :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:48:def baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) : Tuple (k := k) d :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:52:@[simp] theorem baseChange_apply (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:54:    baseChange P A i = Units.val (P i.succ) * A i * Units.val ((P i.castSucc)⁻¹) := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:57:theorem baseChange_one (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:58:    baseChange (1 : BaseChangeGroup (k := k) d) A = A := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:60:  simp only [baseChange_apply, Pi.one_apply, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:63:theorem baseChange_mul (P Q : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:64:    baseChange (P * Q) A = baseChange P (baseChange Q A) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:66:  simp only [baseChange_apply, Pi.mul_apply, Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:69:instance : MulAction (BaseChangeGroup (k := k) d) (Tuple (k := k) d) where
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:70:  smul := baseChange
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:71:  one_smul := baseChange_one
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:72:  mul_smul := baseChange_mul
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:75:@[simp] theorem smul_eq_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:76:    P • A = baseChange P A := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:84:theorem submult_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:86:    submult d (baseChange P A) i j hij
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:103:      rw [submult_succ d (baseChange P A) i p hcast, ih hcast, submult_succ d A i p hcast,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:104:          baseChange_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:110:theorem submult_smul (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:114:  submult_baseChange P A i j hij
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:121:theorem rankPattern_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:123:    rankPattern d (baseChange P A) i j hij = rankPattern d A i j hij := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:124:  rw [rankPattern, rankPattern, submult_baseChange,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:129:theorem rankPattern_smul (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:132:  rankPattern_baseChange P A i j hij
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:152:def witnessBaseChange : BaseChangeGroup (k := ℤ) dWitness :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:14:— the `BaseChangeGroup` element over `SchurLoc` that drives the chart `AlgEquiv`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:122:/-! ## The endpoint gauge as a `BaseChangeGroup` over `SchurLoc`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:130:/-- **The endpoint normalizing gauge** as a `BaseChangeGroup` over `SchurLoc`: `H` at the source
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:132:noncomputable def endpointGauge (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:134:    BaseChangeGroup (k := SchurLoc (k := k) (d 0) (d (Fin.last N)) r) d :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:143:theorem endpointGauge_zero (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:151:theorem endpointGauge_last {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:8:`Rep_d` through the two end factors (here the full base-change group `BaseChangeGroup`; the inner units
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:10:matrices are `H`-equivalent (`exists_baseChange_of_rank_eq`). Hence the **exact-rank locus is one
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:37:/-- The det of a `BaseChangeGroup` value (a `Units` of the matrix ring) is a unit. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:38:theorem isUnit_det_baseChangeGroup (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:42:/-- **Rank of the endpoint-conjugated target is unchanged.** For `P : BaseChangeGroup` and any target
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:45:theorem rank_endpoint_conj (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:49:        (isUnit_det_baseChangeGroup d P (Fin.last N)),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:51:        (by simpa using isUnit_det_baseChangeGroup d P⁻¹ 0)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:62:(`rank_endpoint_conj`). `(→)` `rank(mult A) = r = E.rank`, so `exists_baseChange_of_rank_eq` gives `P`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:69:      ∃ P : BaseChangeGroup (k := k) d, A ∈ (fun A' ↦ P • A') '' (fibre d E) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:73:    obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN E (mult d A) (by rw [hE, hA])
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:85:      = ⋃ P : BaseChangeGroup (k := k) d, (fun A' ↦ P • A') '' (fibre d E) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:98:    (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesDurfee.lean:16:`1 − X^{b+1}` is a unit in `ℤ⟦X⟧` (constant term `1`), so the inductive step cancels. No coefficient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesFivegon.lean:68:/-- `fivegonSum` has non-negative coefficients (a sum of `X^c · Pm m`, each non-negative — M1). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesFivegon.lean:75:    rw [coeff_X_pow]; split_ifs <;> norm_num
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:117:    (Module.finrank_baseChange).trans hΩ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:63:/-! ## Direct sum of polynomial-coefficient tuples and the constant polynomial tuple -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:65:/-- The direct sum of two polynomial-coefficient tuples, block-diagonal per edge. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:99:    (P : BaseChangeGroup (k := k) d) : BaseChangeGroup (k := k) (fun l ↦ d l + d' l) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:112:    (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) (B : Tuple (k := k) d') :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:115:  rw [smul_eq_baseChange, baseChange_apply, smul_eq_baseChange, dirSum, dirSum, baseChange_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:138:    (horb : ∀ t : k, t ≠ 0 → ∃ P : BaseChangeGroup (k := k) d, P • U₀ = tupleEval F₀ t) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:152:A constant `k`-base change `Q` conjugates a polynomial-coefficient family entrywise (the unit matrices
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:158:/-- The base change `Q • F` of a polynomial-coefficient family `F`: the unit matrices `Q` mapped into
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:160:noncomputable def smulPoly {d : Fin (N + 1) → ℕ} (Q : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:167:theorem tupleEval_smulPoly {d : Fin (N + 1) → ℕ} (Q : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:171:  rw [smul_eq_baseChange, baseChange_apply, tupleEval, smulPoly,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:189:    (U D₀ D' : Tuple (k := k) d) (F : Tuple (k := Polynomial k) d) (Q : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:191:    (horb : ∀ t : k, t ≠ 0 → ∃ P : BaseChangeGroup (k := k) d, P • U = tupleEval F t) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:209:    (Q : BaseChangeGroup (k := k) (fun l ↦ d l + d' l)) (D' : Tuple (k := k) (fun l ↦ d l + d' l))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:211:    (horb : ∀ t : k, t ≠ 0 → ∃ P : BaseChangeGroup (k := k) d, P • U₀ = tupleEval F₀ t) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:288:    BaseChangeGroup (k := k) (intervalDim a e) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:315:  rw [smul_eq_baseChange, baseChange_apply, splitBaseChange_val, splitBaseChange_inv_val]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:340:    ∃ P : BaseChangeGroup (k := k) (intervalDim a e),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:512:    ∃ P : BaseChangeGroup (k := k) (intervalDim a e),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:558:    ∃ Q : BaseChangeGroup (k := k) (fun l ↦ intervalDim a e l + foldDim rest l),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1092:    ∃ P : BaseChangeGroup (k := k) (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1101:    ∃ Q : BaseChangeGroup (k := k) (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1125:    ∃ Q : BaseChangeGroup (k := k)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1192:example : ∃ P : BaseChangeGroup (k := ℚ) (intervalDim (0 : Fin 3) 2),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1251:    ∃ P : BaseChangeGroup (k := ℚ) (fun l ↦ intervalDim (0 : Fin 3) 2 l + intervalDim 1 1 l),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:11:(`Core.BaseChange.baseChange`) specialised to the **two end vertices** `0` and `N` acts on `Rep_d`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:19:2. **codim-invariance** (`codimRep_baseChange_image`): a base change is a *linear* change of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:20:   matrix-entry coordinates, so it induces the `k`-algebra automorphism `baseChangeAlgEquiv P` of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:26:(`codimRepCanonical_fibre_baseChange`). With the rank-normal-form fact that any two matrices of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:27:same rank are `GL × GL`-equivalent (`exists_baseChange_of_rank_eq`), this gives the headline
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:30:**Typeclass.** `[Field k] [Infinite k]` — `Infinite` carries `baseChangeAlgEquiv` (the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:53:example (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:63:/-- `eval_baseChangePullback`: pullback evaluates as the `G_d`-shift. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:64:example [Infinite k] (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:66:    MvPolynomial.eval x (baseChangePullback P f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:68:  eval_baseChangePullback P x f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:77:theorem mult_smul (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:87:theorem image_smul_fibre (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:108:`(P • ·) '' Z` is the `comap` of the vanishing ideal of `Z` along `baseChangePullback P`: a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:110:(`eval_baseChangePullback`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:112:    (P : BaseChangeGroup (k := k) d) (Z : Set (Tuple (k := k) d)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:115:          (baseChangePullback P : MvPolynomial (RepCoord d) k →+* _) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:122:    show MvPolynomial.eval (canonicalCoord d A) (baseChangePullback P f) = 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:123:    rw [eval_baseChangePullback, Equiv.symm_apply_apply, ← MvPolynomial.aeval_eq_eval]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:133:      ← eval_baseChangePullback P (canonicalCoord d A) f]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:139:ideal as a `comap` along `baseChangeAlgEquiv P` (a ring equiv), and `RingEquiv.height_comap`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:141:theorem codimRep_baseChange_image [Infinite k] (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:142:    (P : BaseChangeGroup (k := k) d) (Z : Set (Tuple (k := k) d)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:145:  have he : (baseChangePullback P : MvPolynomial (RepCoord d) k →+* _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:146:      = ((baseChangeAlgEquiv P).toRingEquiv.toRingHom) := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:148:  exact RingEquiv.height_comap (baseChangeAlgEquiv P).toRingEquiv _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:151:and `codimRep_baseChange_image`: `codimRepCanonical (fibre d (P_N · B · P_0⁻¹)) = codimRepCanonical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:153:theorem codimRepCanonical_fibre_baseChange [Infinite k] (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:154:    (P : BaseChangeGroup (k := k) d) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:157:  rw [codimRepCanonical, codimRepCanonical, ← image_smul_fibre, codimRep_baseChange_image]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:279:theorem exists_baseChange_of_rank_eq (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:282:    ∃ P : BaseChangeGroup (k := k) d,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:298:  -- assemble the BaseChangeGroup: `last N ↦ equivUnitMatrix eL`, `0 ↦ (equivUnitMatrix eR)⁻¹`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:299:  set P : BaseChangeGroup (k := k) d :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:326:  obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN B B' h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:327:  rw [hP, codimRepCanonical_fibre_baseChange]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:34:  (`Orbit.baseChange_normalForm`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:71:    rankFn d A = rankFn d B ↔ ∃ P : BaseChangeGroup (k := k) d, P • A = B := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:89:  r A B := ∃ P : BaseChangeGroup (k := k) d, P • A = B
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:31:4. **Chain composition + assembly** (`box_move_chain_of_le` + `baseChange_normalForm`): `Ō_M ⊆
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:97:    rw [smul_eq_baseChange, baseChange_mul, ← smul_eq_baseChange, ← smul_eq_baseChange, ← hP₀,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:101:    rw [smul_eq_baseChange, baseChange_mul, ← smul_eq_baseChange, ← smul_eq_baseChange, hP₀]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:116:matrix-entry coordinates, so it lifts to an algebra endomorphism `baseChangePullback P` of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:124:noncomputable def baseChangeSub {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:133:/-- The base-change pullback algebra endomorphism `aeval (baseChangeSub P)`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:134:noncomputable def baseChangePullback {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:136:  MvPolynomial.aeval (baseChangeSub P)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:138:/-- **Evaluation of the pullback is evaluation at the shifted point.** `eval x (baseChangeSub P
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:141:theorem eval_baseChangeSub {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:143:    MvPolynomial.eval x (baseChangeSub P coord)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:145:  rw [baseChangeSub, canonicalCoord_apply, smul_eq_baseChange, baseChange_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:167:/-- The pullback evaluates as the shift: `eval x (baseChangePullback P f) = eval (shifted x) f`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:168:theorem eval_baseChangePullback {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:170:    MvPolynomial.eval x (baseChangePullback P f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:172:  rw [baseChangePullback,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:173:    show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:174:      = (MvPolynomial.eval x).comp ((MvPolynomial.aeval (baseChangeSub P)).toRingHom) f from rfl]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:175:  have hhom : (MvPolynomial.eval x).comp ((MvPolynomial.aeval (baseChangeSub P)).toRingHom)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:179:      show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) (MvPolynomial.C r)) = _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:183:      show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) (MvPolynomial.X coord)) = _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:184:      rw [MvPolynomial.aeval_X, MvPolynomial.eval_X, eval_baseChangeSub]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:189:theorem orbitSet_baseChange_stable {d : Fin (N + 1) → ℕ} (U : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:190:    (P : BaseChangeGroup (k := k) d) {y : RepCoord d → k} (hy : y ∈ orbitSet U) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:194:  · rw [smul_eq_baseChange, baseChange_mul, ← smul_eq_baseChange, ← smul_eq_baseChange, hQ]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:199:theorem baseChangePullback_mem_vanishingIdeal_orbitSet {d : Fin (N + 1) → ℕ} (U : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:200:    (P : BaseChangeGroup (k := k) d) {f : MvPolynomial (RepCoord d) k}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:202:    baseChangePullback P f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:206:  rw [MvPolynomial.aeval_eq_eval, eval_baseChangePullback, ← MvPolynomial.aeval_eq_eval]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:207:  exact hf _ (orbitSet_baseChange_stable U P hy)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:225:    ← eval_baseChangePullback Q (canonicalCoord d D) f]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:228:  have := hmem (baseChangePullback Q f) (baseChangePullback_mem_vanishingIdeal_orbitSet U Q hf)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:8:# `DLNFibre.Core.VarietyDimRadical` — `varietyDim`/`ringKrullDim` is radical-insensitive
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:26:- `ringKrullDim_quotient_radical` — `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical)`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:27:- `ringKrullDim_quotient_eq_of_radical_eq` — same Krull dim for two ideals with equal radical.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:40:theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:41:    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:42:  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:47:theorem ringKrullDim_quotient_eq_of_radical_eq {R : Type*} [CommRing R] {I J : Ideal R}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:50:  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:73:  apply DLNFibre.Core.ringKrullDim_quotient_eq_of_radical_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean:328:  is the Gabriel normal form (`exists_orbitRankLocus_mem_rankPattern_eq` / `baseChange_normalForm`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:27:Plus a base-change rank brick (`finrank_range_baseChange`): for a `k`-linear `f` between `k`-spaces
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:28:and a field extension `K/k`, `finrank K (range (f.baseChange K)) = finrank k (range f)` — base
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:104:`range f` finite-dimensional, and a field extension `K/k`, the base-changed map `f.baseChange K`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:105:(`= K ⊗ f`) has `finrank K (range (f.baseChange K)) = finrank k (range f)`. Factor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:109:`≅ K ⊗ range f`); then `Module.finrank_baseChange`. The rank-side tool for the A4.3 bound. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:110:theorem finrank_range_baseChange {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:113:    finrank K (LinearMap.range (f.baseChange K)) = finrank k (LinearMap.range f) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:114:  have hfac : f.baseChange K
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:115:      = (LinearMap.range f).subtype.baseChange K ∘ₗ f.rangeRestrict.baseChange K := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:116:    rw [← LinearMap.baseChange_comp, subtype_comp_codRestrict]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:118:  have hsurj : LinearMap.range (f.rangeRestrict.baseChange K) = ⊤ := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:119:    rw [LinearMap.range_eq_top, LinearMap.baseChange_eq_ltensor]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:122:  have hinj : Function.Injective ((LinearMap.range f).subtype.baseChange K) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:123:    rw [LinearMap.baseChange_eq_ltensor]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:125:  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:17:but the construction (`T`, `T_leadingcoeff_isUnit`) is **`private`**. This module re-derives the one
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:59:noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:75:    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:89:    (T f <| monomial v <| coeff v f).degreeOf 0 ≠
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:90:    (T f <| monomial w <| coeff w f).degreeOf 0 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:97:    (finSuccEquiv k n ((T f) ((monomial v) (coeff v f)))).leadingCoeff =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:98:    algebraMap k _ (coeff v f) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:101:    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:103:    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:114:/-- `T` maps `f` to a polynomial in `X₀` whose `X₀`-leading coefficient is a unit. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:115:private lemma T_leadingcoeff_isUnit (fne : f ≠ 0) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:118:    (fun v ↦ (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:119:  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:128:  have coeff : (finSuccEquiv k n ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:137:  nth_rw 2 [← f.support_sum_monomial_coeff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:139:  rw [leadingCoeff_finSuccEquiv_t] at coeff
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:140:  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:147:coefficient** in `X₀` — i.e. up to a unit scalar, `φ f` is monic in `X₀` over `k[x₁,…,xₙ]`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:151:  ⟨MonicPositioning.T f, MonicPositioning.T_leadingcoeff_isUnit f fne⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:155:/-- An ideal of `A[X]` containing an element with unit leading coefficient contains a monic. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:176:`≥ 1`: the monic `g` has leading coefficient `1 ∉ q`, so `g ∉ q·A[X] = ker (mk)`, so its image lies
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:188:  -- `g ∉ J`: its leading coefficient is `1 ∉ q`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:194:      rwa [mon.coeff_natDegree] at this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:236:    (Ideal.quotientEquivAlg p (p.map (e : R →+* S)) e rfl).symm.toRingEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:70:    Ideal.quotientEquivAlg I J e rfl with hΦ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:143:= 0` at `P_ε` (over `DualNumber k`) and reading the `ε`-coefficient. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:279:its value `a_M x = (M)_x` and its `ε`-coefficient `v x = (δ⁰ φ)_x`, by the landed certificate
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:299:/-- `snd (orbitPointε M φ x) = v x` where `v = canonicalCoord (δ⁰ φ)` (the `ε`-coefficient). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:310:`M`: the `ε`-coefficient of the dual-number evaluation, `D_v f = snd (aeval (orbitPointε M φ) f)`. A
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:351:evalGroupRingε M φ (orbitPullback M f) = 0`, hence its `ε`-coefficient vanishes. Needs `[Infinite k]`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:129:    Ideal.quotientEquivAlg I J e rfl with hΦ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:35:`baseChangePullback P` (from `OrbitClosure`) is `aeval (baseChangeSub P)`, the coordinate-ring
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:40:/-- The pullback composition law (contravariant): `baseChangePullback P (baseChangePullback Q f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:41:= baseChangePullback (Q * P) f`. Both polynomials evaluate to the same value at every point `x`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:42:(`eval_baseChangePullback`, chasing the `G_d`-shift `shift_Q ∘ shift_P = shift_{Q*P}`), so they are
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:44:theorem baseChangePullback_comp [Infinite k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:45:    (P Q : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:46:    baseChangePullback P (baseChangePullback Q f) = baseChangePullback (Q * P) f := by

exec
/bin/bash -lc "rg -n \"Ideal\\.quotientEquivAlg|quotientEquivAlg|ringKrullDim_quotient_eq_of_radical_eq|ringKrullDim_quotient_radical|ringKrullDim.*quotient.*radical|Localization.*quotient|quotient.*Localization|IsLocalization.*quotient|map_radical|height_map|height.*local\" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib | head -300" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 141ms:
otient map `mk : M → S → Localization S` equals the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Radical.lean:54:@[simp] lemma IsometryEquiv.map_radical {Q' : QuadraticMap R M' P}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Radical.lean:63:  rw [← e.map_radical, LinearEquiv.finrank_map_eq]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:182:instance : (HomotopyCategory.quotient C c ⋙ Qh).IsLocalization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:184:  Functor.IsLocalization.of_iso _ (quotientCompQhIso C c).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:216:variable [(HomotopyCategory.quotient C c).IsLocalization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:223:  Functor.IsLocalization.of_comp (HomotopyCategory.quotient C c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:244:    Localization.StrictUniversalPropertyFixedTarget (HomotopyCategory.quotient C c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:254:lemma ComplexShape.quotient_isLocalization :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:255:    (HomotopyCategory.quotient C c).IsLocalization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:275:instance : (HomotopyCategory.quotient C (ComplexShape.down ι)).IsLocalization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:277:  (ComplexShape.down ι).quotient_isLocalization (fun _ => ⟨_, rfl⟩) C
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:300:instance : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).IsLocalization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:302:  (ComplexShape.up ℤ).quotient_isLocalization (fun n => ⟨n - 1, by simp⟩) C
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:370:  [(HomotopyCategory.quotient C c).IsLocalization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/Localization.lean:378:  Localization.liftNatIso (HomotopyCategory.quotient C c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/Radical.lean:33:theorem OrderIso.map_radical (f : α ≃o β) : f (Order.radical α) = Order.radical β := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Altitude.lean:244:@[simp] lemma height_map {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Altitude.lean:254:  convert (s.restrict S hS).height_map S.subtypeₐᵢ i
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean:689:  H.isDistinguishedAt.algEquivQuotient.trans <| Ideal.quotientEquivAlgOfEq A <|
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean:695:      (H.isDistinguishedAt.isWeierstrassDivisorAt'.mod' <| Ideal.quotientEquivAlgOfEq A
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Quotient.lean:36:  (Ideal.quotientEquivAlgOfEq R (ker_evalRingHom x).symm).trans
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Quotient.lean:53:  (Ideal.quotientEquivAlgOfEq R (J := _ ⊔ Ideal.span {C x}) <| by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Quotient.lean:56:      (Ideal.quotientEquivAlg _ _ (quotientSpanXSubCAlgEquiv y) rfl).trans <|
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Quotient.lean:57:        Ideal.quotientEquivAlgOfEq R <| by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:860:  rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_radical, Ideal.radical_eq_sInf]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/NoetherNormalization.lean:192:    MvPolynomial (Fin (n + 1)) k ⧸ I.map (T f) := quotientEquivAlg
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/NoetherNormalization.lean:208:  quotientEquivAlg (R₁ := k) (I.map (T f)) I (T f).symm <| by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/StandardEtale.lean:240:  Ideal.quotientEquivAlg _ _ (Bivariate.equivMvPolynomial R)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Dedekind.lean:41:      IsLocalization.map_radical q.primeCompl,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/Defs.lean:50:* `Localization M S`, a construction of the localization as a quotient type, defined in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/Defs.lean:73:These show the quotient map `mk : R → M → Localization M` equals the surjection
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:270:theorem isIntegral_isLocalization_polynomial_quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:275:    (IsLocalization.map Sₘ (quotientMap P C le_rfl) (Submonoid.powers (pX.map (Ideal.Quotient.mk
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:361:        (IsLocalization.surjective_quotientMap_of_maximal_of_localization (Submonoid.powers x) Rₘ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:384:    exact isIntegral_isLocalization_polynomial_quotient P p pP
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:464:    exact @isIntegral_isLocalization_polynomial_quotient R _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:504:        -- convert isIntegral_isLocalization_polynomial_quotient P pX hpX
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:506:        exact @isIntegral_isLocalization_polynomial_quotient R _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:599:  let w : (S[X] ⧸ Q) ≃ₐ[R] (T ⧸ P) := Ideal.quotientEquivAlg Q P v hw.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/Ideal.lean:253:lemma map_radical (I : Ideal R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/Ideal.lean:255:  refine (I.map_radical_le (algebraMap R S)).antisymm ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ideal.lean:321:    rw [map_radical_of_surjective hf (le_of_eq mk_ker),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ideal.lean:326:    rw [comap_radical, comap_jacobson_of_surjective hf,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/QuasiFinite/Weakly.lean:66:  refine Algebra.QuasiFinite.iff_of_algEquiv ((Ideal.quotientEquivAlg _ _ (.refl) ?_).trans
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/QuasiFinite/Weakly.lean:102:    (p.under R).map (algebraMap R (Localization.AtPrime p))) (Ideal.quotientMapₐ _ f H)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/QuasiFinite/Weakly.lean:196:  let e := (Ideal.quotientEquivAlg ((q.under A).map (algebraMap _ _)) _ (.refl) (by simpa)).trans
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/QuasiFinite/Polynomial.lean:75:    .trans ((AlgEquiv.quotientBot _ _).symm.trans (Ideal.quotientEquivAlgOfEq _ H'.symm))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/FinitePresentationLocal.lean:70:  we quotient out by an ideal and apply `finitePresentation_ofLocalizationSpanTarget_aux`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:709:def quotientEquivAlg (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:715:lemma quotientEquivAlg_symm (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:716:    (quotientEquivAlg I J f hIJ).symm = quotientEquivAlg J I f.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:722:lemma quotientEquivAlg_mk (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) (x : A) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:723:    Ideal.quotientEquivAlg I J f hIJ x = f x :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:758:def quotientEquivAlgOfEq {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:760:  quotientEquivAlg I J AlgEquiv.refl <| h ▸ (map_id I).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:763:theorem quotientEquivAlgOfEq_mk {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) (x : A) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:764:    quotientEquivAlgOfEq R₁ h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:768:theorem quotientEquivAlgOfEq_coe_eq_factorₐ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:770:    (quotientEquivAlgOfEq R₁ h : A ⧸ I →ₐ[R₁] A ⧸ J) = Quotient.factorₐ R₁ (le_of_eq h) := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:773:theorem quotientEquivAlgOfEq_coe_eq_factor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:775:    (quotientEquivAlgOfEq R₁ h : A ⧸ I →+* A ⧸ J) = Quotient.factor (le_of_eq h) := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:778:theorem quotientEquivAlgOfEq_symm {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:779:    (quotientEquivAlgOfEq R₁ h).symm = quotientEquivAlgOfEq R₁ h.symm := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:804:  (Ideal.quotientEquivAlgOfEq R (AlgHom.ker_rangeRestrict f).symm).trans <|
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:124:  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R h).toRingEquiv,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:211:  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R eq).toRingEquiv,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/Basic.lean:59:These show the quotient map `mk : R → M → Localization M` equals the surjection
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Algebra.lean:135:    (Ideal.quotientEquivAlgOfEq R h)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Algebra.lean:155:  simp only [evalₐ, smul_eq_mul, Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Algebra.lean:170:  exact (Ideal.quotientEquivAlgOfEq R h).injective (H n)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:68:  rwa [← e.height_map <| P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:72:lemma height_map_C (p : Ideal R) [p.IsMaximal] : (p.map C).height = p.height := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:97:    rw [height_map_of_disjoint p.primeCompl]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:100:    rw [height_map_of_disjoint (Submonoid.map C <| p.primeCompl) _ disj]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Defs.lean:207:See also `Submodule.quotEquivOfEq` and `Ideal.quotientEquivAlgOfEq`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsAdjoinRoot.lean:169:  (Ideal.quotientEquivAlgOfEq R h.ker_map.symm).trans <|
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean:645:theorem comap_radical : comap f (radical K) = radical (comap f K) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean:652:  rw [← hK.radical, comap_radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean:657:theorem map_radical_le : map f (radical I) ≤ radical (map f I) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean:1104:theorem map_radical_of_surjective {f : R →+* S} (hf : Function.Surjective f) {I : Ideal R}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:94:      (Ideal.quotientEquivAlgOfEq T (Ideal.map_pow _ _ _))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:42:* `HomogeneousLocalization`: `NumDenSameDeg 𝒜 x` quotiented by kernel of `embedding 𝒜 x`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/IsPrimary.lean:82:  simp only [mem_comap, map_mul, ← comap_radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Smooth/AdicCompletion.lean:40:  | 1 => (Ideal.quotientEquivAlgOfEq R (show I = I ^ 1 by simp)).toAlgHom.comp f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Smooth/Basic.lean:445:    let e := (Ideal.quotientEquivAlgOfEq _ ((pow_two _).trans H)).trans
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:224:/-- The prime height of the maximal ideal equals the Krull dimension in a local ring -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:231:/-- The height of the maximal ideal equals the Krull dimension in a local ring. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:289:lemma RingEquiv.height_map {S : Type*} [CommRing S] (e : R ≃+* S) (I : Ideal R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:345:lemma IsLocalization.height_map_of_disjoint {S : Type*} [CommRing S] [Algebra R S] (M : Submonoid R)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Ideal.lean:125:      Ideal.algebraMap_quotient_residueField_mk, IsLocalization.AtPrime.to_map_mem_maximal_iff _ I,

codex
So far, I see no reusable “transport this `BaseChangeGroup` along an algebra map” declaration. That is not fatal; it means the target-localized gauge should be defined directly as the same endpoint matrices with coefficients mapped into the total localization.
exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.Submult

/-!
# `DLNFibre.Core.BaseChange` — the `G_d` base-change action and rank-pattern invariance

The change-of-basis action of Le Halleur–Rimányi 2024 (§2.2): the group
`G_d = ∏_{v} GL_{d_v}` acts on `Tuple d` by conjugating each edge map by the units at its two
endpoints. For `P : ∀ v, GL_{d_v}` (units = invertible matrices) the action is
`(P • A)_i = P_{i+1} · A_i · P_i⁻¹` — the target-vertex unit `P i.succ` on the left, the
source-vertex unit inverse `(P i.castSucc)⁻¹` on the right.

**Headlines.**
- `submult_baseChange` / `submult_smul` — **telescoping conjugation** of the interval sub-product:
  `submult (P • A) i j = P_j · (submult A i j) · P_i⁻¹`. The inner units cancel along the product
  (`… P_t⁻¹ P_t …`), so only the two boundary units survive; proved by induction mirroring
  `submult_succ`.
- `rankPattern_baseChange` / `rankPattern_smul` — **rank-pattern base-change invariance**:
  `rankPattern (P • A) i j = rankPattern A i j`. A unit matrix has invertible determinant
  (`Matrix.isUnits_det_units`), and multiplying by such a matrix preserves rank
  (`Matrix.rank_mul_eq_left_of_isUnit_det` / `…_right_…`), so the boundary conjugation drops out.

This is the orbit-side input to Prop 3.1b (the rank pattern is a base-change invariant): two tuples
in the same `G_d`-orbit have the same rank pattern.

**Typeclass.** `CommRing k` throughout — the two rank levers
`Matrix.rank_mul_eq_left_of_isUnit_det` / `…_right_…` are stated over a `CommRing` (no `Field`
needed). The non-vacuity witness additionally uses `Nontrivial ℤ` (via `Matrix.rank_of_isUnit`).
**Dependency rule:** never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-- `G_d = ∏_v GL_{d_v}`: a base-change datum is one invertible matrix per vertex (a unit of the
square matrix ring = an element of `GL_{d_v}`). -/
abbrev BaseChangeGroup (d : Fin (N + 1) → ℕ) : Type u :=
  ∀ v : Fin (N + 1), (Matrix (Fin (d v)) (Fin (d v)) k)ˣ

variable {d : Fin (N + 1) → ℕ}

/-- The `G_d` base-change action on `Tuple d`: on edge `i`, conjugate `A i` by the target-vertex
unit `P i.succ` on the left and the source-vertex unit inverse `(P i.castSucc)⁻¹` on the right. -/
def baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) : Tuple (k := k) d :=
  fun i ↦ Units.val (P i.succ) * A i * Units.val ((P i.castSucc)⁻¹)

/-- The defining formula of the action, edge by edge. -/
@[simp] theorem baseChange_apply (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
    (i : Fin N) :
    baseChange P A i = Units.val (P i.succ) * A i * Units.val ((P i.castSucc)⁻¹) := rfl

/-- The identity base change fixes every tuple. -/
theorem baseChange_one (A : Tuple (k := k) d) :
    baseChange (1 : BaseChangeGroup (k := k) d) A = A := by
  funext i
  simp only [baseChange_apply, Pi.one_apply, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one]

/-- Base change is compatible with multiplication in `G_d`: `(P * Q) • A = P • (Q • A)`. -/
theorem baseChange_mul (P Q : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
    baseChange (P * Q) A = baseChange P (baseChange Q A) := by
  funext i
  simp only [baseChange_apply, Pi.mul_apply, Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

/-- The base change is a genuine group action of `G_d = ∏_v GL_{d_v}` on `Tuple d`. -/
instance : MulAction (BaseChangeGroup (k := k) d) (Tuple (k := k) d) where
  smul := baseChange
  one_smul := baseChange_one
  mul_smul := baseChange_mul

/-- `•` is the base-change action (definitional). -/
@[simp] theorem smul_eq_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
    P • A = baseChange P A := rfl

/-! ## Telescoping conjugation of the sub-product -/

/-- **Telescoping conjugation.** The interval sub-product of a base-changed tuple is the sub-product
conjugated by the two boundary units: `submult (P • A) i j = P_j · (submult A i j) · P_i⁻¹`. The
inner units cancel (`P_t⁻¹ P_t = 1`); proved by induction on the upper index mirroring
`submult_succ`. -/
theorem submult_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    submult d (baseChange P A) i j hij
      = Units.val (P j) * submult d A i j hij * Units.val ((P i)⁻¹) := by
  revert hij
  induction j using Fin.induction with
  | zero =>
    intro hij
    obtain rfl := Fin.le_zero_iff.mp hij
    simp only [submult_self]
    rw [Matrix.mul_one, Units.mul_inv]
  | succ p ih =>
    intro hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · -- diagonal `i = p.succ`: the empty sub-product, boundary units cancel
      simp only [submult_self]
      rw [Matrix.mul_one, Units.mul_inv]
    · -- active edge `i ≤ p.castSucc`: peel the top factor and cancel the inner units
      have hcast : i ≤ p.castSucc := Fin.le_castSucc_iff.mpr hlt
      rw [submult_succ d (baseChange P A) i p hcast, ih hcast, submult_succ d A i p hcast,
          baseChange_apply]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Units.val ((P p.castSucc)⁻¹)) (Units.val (P p.castSucc)),
          Units.inv_mul, Matrix.one_mul]

/-- Telescoping conjugation, in `•` notation. -/
theorem submult_smul (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    submult d (P • A) i j hij
      = Units.val (P j) * submult d A i j hij * Units.val ((P i)⁻¹) :=
  submult_baseChange P A i j hij

/-! ## Rank-pattern base-change invariance -/

/-- **Rank-pattern base-change invariance.** Conjugating by units does not change rank, so the rank
pattern is constant on `G_d`-orbits: `rankPattern (P • A) i j = rankPattern A i j`. (Orbit-side
input to Prop 3.1b.) -/
theorem rankPattern_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern d (baseChange P A) i j hij = rankPattern d A i j hij := by
  rw [rankPattern, rankPattern, submult_baseChange,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units _),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units _)]

/-- Rank-pattern base-change invariance, in `•` notation. -/
theorem rankPattern_smul (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern d (P • A) i j hij = rankPattern d A i j hij :=
  rankPattern_baseChange P A i j hij

section Witness

/-! ## Non-vacuity witness

Conjugate the landed `(2,2,2)` witness `Setup.tupleWitness` by the `GL₂(ℤ)` element `!![1,1;0,1]`
(determinant `1`) at every vertex, and check the rank pattern is unchanged. The off-diagonal value
`r_{02} = rank(A₂A₁) = 2` survives the conjugation — the headline `rankPattern_smul` applied to a
genuine, non-identity base change of a concrete tuple. -/

/-- A concrete `GL₂(ℤ)` element, `!![1,1;0,1]` (determinant `1`), with explicit inverse
`!![1,-1;0,1]` (so the unit is computable: `val * inv = inv * val = 1` by `decide`). -/
def witnessUnit : (Matrix (Fin 2) (Fin 2) ℤ)ˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by decide
  inv_val := by decide

/-- Base-change the `(2,2,2)` witness by `witnessUnit` at every vertex. -/
def witnessBaseChange : BaseChangeGroup (k := ℤ) dWitness :=
  fun v ↦ match v with
    | 0 => witnessUnit
    | 1 => witnessUnit
    | 2 => witnessUnit

/-- The headline applies to a concrete non-identity base change: the rank pattern is unchanged at
every `(i, j)`. -/
example (i j : Fin 3) (hij : i ≤ j) :
    rankPattern dWitness (witnessBaseChange • tupleWitness) i j hij
      = rankPattern dWitness tupleWitness i j hij :=
  rankPattern_smul witnessBaseChange tupleWitness i j hij

/-- The off-diagonal product rank survives the base change: `r_{02} = rank(A₂A₁) = 2`. -/
example : rankPattern dWitness (witnessBaseChange • tupleWitness) 0 2 (Fin.zero_le _) = 2 := by
  rw [rankPattern_smul, rankPattern]
  have hsub : submult dWitness tupleWitness 0 2 (Fin.zero_le _) = !![1, 2; 3, 7] := by
    rw [submult_zero]; unfold multPrefix tupleWitness dWitness; decide
  have hunit : IsUnit (!![1, 2; 3, 7] : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.isUnit_iff_isUnit_det,
      show (!![1, 2; 3, 7] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 from by decide]
    exact isUnit_one
  have hrank : (!![1, 2; 3, 7] : Matrix (Fin 2) (Fin 2) ℤ).rank = 2 := by
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  rw [hsub]; exact hrank

end Witness

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '1,230p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.OrbitClosure
import DLNFibre.Core.OrbitVariety
import DLNFibre.Core.OrbitPullbackDim
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# `DLNFibre.Core.OrbitSmooth` — smoothness of the orbit closure at the normal-form point (L3)

The orbit-closure variety `Z_M = orbitRankLocus M = Ō_M` is smooth at the orbit normal-form point
`M`: the coordinate ring `A = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(canonicalCoord '' Z_M)`
is formally smooth over `k` at the maximal ideal `m_M = ker(eval at canonicalCoord M)`.

The proof is **homogeneity + Route DENSE** (thread 34/18): the `G_d`-action acts on `Z_M` with a
dense orbit `O_M`; generic smoothness over the perfect (algebraically closed) field `k` produces a
smooth closed point, and the dense orbit guarantees one such smooth point is an orbit point;
transporting it along the `G_d`-action (a `k`-algebra automorphism of `A`) to the normal-form point
`M` gives `IsSmoothAt k m_M`.

**Typeclass.** `[Field k] [IsAlgClosed k]` (⟹ `PerfectField k`, Jacobson, `k`-points = closed
points). **Dependency rule:** `Core` only.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## L3.0 — the `G_d`-action as a `k`-algebra automorphism of the coordinate ring

`baseChangePullback P` (from `OrbitClosure`) is `aeval (baseChangeSub P)`, the coordinate-ring
incarnation of the linear change of variables `A ↦ P • A`. It is invertible: its inverse is the
pullback by `P⁻¹`, witnessed by the composition law `pullback P ∘ pullback Q = pullback (Q * P)`
(pullbacks are contravariant). -/

/-- The pullback composition law (contravariant): `baseChangePullback P (baseChangePullback Q f)
= baseChangePullback (Q * P) f`. Both polynomials evaluate to the same value at every point `x`
(`eval_baseChangePullback`, chasing the `G_d`-shift `shift_Q ∘ shift_P = shift_{Q*P}`), so they are
equal by `MvPolynomial.funext` over the infinite field `k`. -/
theorem baseChangePullback_comp [Infinite k] {d : Fin (N + 1) → ℕ}
    (P Q : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
    baseChangePullback P (baseChangePullback Q f) = baseChangePullback (Q * P) f := by
  refine MvPolynomial.funext (fun x ↦ ?_)
  rw [eval_baseChangePullback, eval_baseChangePullback, eval_baseChangePullback]
  -- `shift_Q (shift_P x) = shift_{Q*P} x`: chase the `G_d`-action through `canonicalCoord`/`symm`
  rw [Equiv.symm_apply_apply, SemigroupAction.mul_smul]

/-- The identity base change pulls back to the identity: `baseChangePullback 1 = id`. The shift by
`1` is the identity (`one_smul`), so `eval x (pullback 1 f) = eval x f` for all `x`. -/
theorem baseChangePullback_one [Infinite k] {d : Fin (N + 1) → ℕ}
    (f : MvPolynomial (RepCoord d) k) :
    baseChangePullback (1 : BaseChangeGroup (k := k) d) f = f := by
  refine MvPolynomial.funext (fun x ↦ ?_)
  rw [eval_baseChangePullback, one_smul, Equiv.apply_symm_apply]

/-- **L3.0 — the `G_d`-action as a `k`-algebra automorphism.** `baseChangeAlgEquiv P` is the
coordinate-ring automorphism `aeval (baseChangeSub P)` (= the change of variables `A ↦ P • A`), with
inverse the pullback by `P⁻¹` (the composition law `pullback P ∘ pullback Q = pullback (Q*P)` and
`pullback 1 = id`). -/
noncomputable def baseChangeAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ}
    (P : BaseChangeGroup (k := k) d) :
    MvPolynomial (RepCoord d) k ≃ₐ[k] MvPolynomial (RepCoord d) k :=
  AlgEquiv.ofAlgHom (baseChangePullback P) (baseChangePullback P⁻¹)
    (by refine AlgHom.ext (fun f ↦ ?_)
        rw [AlgHom.comp_apply, AlgHom.id_apply, baseChangePullback_comp, inv_mul_cancel,
          baseChangePullback_one])
    (by refine AlgHom.ext (fun f ↦ ?_)
        rw [AlgHom.comp_apply, AlgHom.id_apply, baseChangePullback_comp, mul_inv_cancel,
          baseChangePullback_one])

@[simp] theorem baseChangeAlgEquiv_apply [Infinite k] {d : Fin (N + 1) → ℕ}
    (P : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
    baseChangeAlgEquiv P f = baseChangePullback P f := rfl

/-! ## The coordinate ring `A` of the orbit closure and the descended `G_d`-automorphism

`A = MvPolynomial (RepCoord d) k ⧸ I` with `I = vanishingIdeal (orbitSet M)`. By L6.4
(`vanishingIdeal_orbitRankLocus_eq_orbitSet`) this is the coordinate ring of the rank locus
`Z_M = canonicalCoord '' orbitRankLocus M`; by L1 (`isPrime_vanishingIdeal_orbitSet`) it is a
domain. The `G_d`-automorphism `baseChangeAlgEquiv P` stabilises `I`, descending to `A ≃ₐ[k] A`. -/

/-- The vanishing ideal `I = vanishingIdeal (orbitSet M)` we quotient by — the defining ideal of the
orbit closure `Z_M` (L6.4 identifies it with the rank-locus ideal). -/
noncomputable def orbitIdeal {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    Ideal (MvPolynomial (RepCoord d) k) :=
  MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet M)

/-- The coordinate ring `A = MvPolynomial (RepCoord d) k ⧸ I` of the orbit closure `Z_M`. -/
abbrev orbitRing {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) : Type u :=
  MvPolynomial (RepCoord d) k ⧸ orbitIdeal M

/-- `A` is a **domain**: `I = vanishingIdeal (orbitSet M)` is prime (L1, orbit irreducible). -/
instance orbitRing_isDomain [IsAlgClosed k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    IsDomain (orbitRing M) :=
  haveI : (orbitIdeal M).IsPrime := isPrime_vanishingIdeal_orbitSet M
  Ideal.Quotient.isDomain (orbitIdeal M)

/-- The orbit ideal is `G_d`-stable: `baseChangeAlgEquiv P` maps `I` into `I`
(`baseChangePullback_mem_vanishingIdeal_orbitSet`). -/
theorem orbitIdeal_map_le [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) :
    (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _)
      ≤ orbitIdeal M := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap]
  exact baseChangePullback_mem_vanishingIdeal_orbitSet M P hf

/-- The orbit ideal is **invariant** under `baseChangeAlgEquiv P`: `I.map (α_P) = I`. Both `α_P` and
its inverse `α_{P⁻¹}` map `I` into `I`, and `map` of an equiv is monotone with a `map`-inverse. -/
theorem orbitIdeal_map_eq [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) :
    (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _)
      = orbitIdeal M := by
  refine le_antisymm (orbitIdeal_map_le M P) ?_
  -- `I ≤ I.map α_P` ⟸ `I.map α_{P⁻¹} ≤ I` pushed through `α_P` (an equiv)
  have hinv : (orbitIdeal M).map
      (baseChangeAlgEquiv P⁻¹ : MvPolynomial (RepCoord d) k →+* _) ≤ orbitIdeal M :=
    orbitIdeal_map_le M P⁻¹
  calc orbitIdeal M
      = ((orbitIdeal M).map
          (baseChangeAlgEquiv P⁻¹ : MvPolynomial (RepCoord d) k →+* _)).map
          (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _) := by
        rw [Ideal.map_map]
        refine (Ideal.map_id (orbitIdeal M)).symm.trans ?_
        congr 1
        refine RingHom.ext (fun f ↦ ?_)
        rw [RingHom.id_apply, RingHom.comp_apply]
        change f = baseChangePullback P (baseChangePullback P⁻¹ f)
        rw [baseChangePullback_comp, inv_mul_cancel, baseChangePullback_one]
    _ ≤ (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _) :=
        Ideal.map_mono hinv

/-- **The descended `G_d`-automorphism** `α_P : A ≃ₐ[k] A` of the orbit-closure coordinate ring,
from the polynomial-ring automorphism `baseChangeAlgEquiv P` (which stabilises `I`,
`orbitIdeal_map_eq`). -/
noncomputable def orbitRingAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) :
    orbitRing M ≃ₐ[k] orbitRing M :=
  Ideal.quotientEquivAlg (orbitIdeal M) (orbitIdeal M) (baseChangeAlgEquiv P)
    (orbitIdeal_map_eq M P).symm

/-- `α_P` on a residue class is the residue class of the pullback: `α_P (mk f) = mk (pullback P f)`.
-/
@[simp] theorem orbitRingAlgEquiv_mk [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
    orbitRingAlgEquiv M P (Ideal.Quotient.mk (orbitIdeal M) f)
      = Ideal.Quotient.mk (orbitIdeal M) (baseChangePullback P f) :=
  rfl

/-! ## The orbit `k`-points and their point ideals `m_{P•M}` in `A`

For `P : G_d`, the orbit point `canonicalCoord (P • M) ∈ orbitSet M` evaluates every element of
`I = vanishingIdeal (orbitSet M)` to `0`, so `eval (canonicalCoord (P • M)) : R → k` descends to a
`k`-algebra hom `A → k`. Its kernel `m_{P•M}` is a maximal ideal of `A` (residue field `k`), and the
`G_d`-automorphism `α_P` carries `m_{P•M}` to `m_M` (the normal-form point ideal). -/

/-- The orbit point `canonicalCoord (P • M)` lies in `orbitSet M`. -/
theorem canonicalCoord_smul_mem_orbitSet {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) : canonicalCoord d (P • M) ∈ orbitSet M :=
  ⟨P • M, ⟨P, rfl⟩, rfl⟩

/-- Evaluation at the orbit point `canonicalCoord (P • M)` kills the orbit ideal `I`: every `f ∈ I`
vanishes at every orbit point. -/
theorem eval_orbitPoint_mem_orbitIdeal {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) {f : MvPolynomial (RepCoord d) k} (hf : f ∈ orbitIdeal M) :
    MvPolynomial.eval (canonicalCoord d (P • M)) f = 0 := by
  rw [orbitIdeal, MvPolynomial.mem_vanishingIdeal_iff] at hf
  have := hf _ (canonicalCoord_smul_mem_orbitSet M P)
  rwa [MvPolynomial.aeval_eq_eval] at this

/-- The descended **evaluation** `A → k` at the orbit point `canonicalCoord (P • M)`: the
`k`-algebra hom factoring `eval (canonicalCoord (P • M))` through `A = R ⧸ I` (which kills `I`). -/
noncomputable def orbitEval {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) : orbitRing M →ₐ[k] k :=
  Ideal.Quotient.liftₐ (orbitIdeal M)
    (MvPolynomial.aeval (R := k) (canonicalCoord d (P • M)))
    (fun f hf ↦ by rw [MvPolynomial.aeval_eq_eval]; exact eval_orbitPoint_mem_orbitIdeal M P hf)

/-- `orbitEval` on a residue class is evaluation of the representative. -/
@[simp] theorem orbitEval_mk {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
    orbitEval M P (Ideal.Quotient.mk (orbitIdeal M) f)
      = MvPolynomial.eval (canonicalCoord d (P • M)) f := by
  rw [orbitEval, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact congrFun (MvPolynomial.aeval_eq_eval (canonicalCoord d (P • M))) f

/-- The **point ideal** `m_{P•M} = ker (orbitEval M P)` of the orbit `k`-point
`canonicalCoord (P•M)` in `A`. The normal-form point ideal is `m_M = orbitPointIdeal M 1`. -/
noncomputable def orbitPointIdeal {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) : Ideal (orbitRing M) :=
  RingHom.ker (orbitEval M P).toRingHom

/-- The normal-form point ideal `m_M = ker (orbitEval M 1)` (the orbit point `canonicalCoord M`). -/
noncomputable abbrev normalFormIdeal {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    Ideal (orbitRing M) :=
  orbitPointIdeal M 1

/-- `m_{P•M}` is **maximal**: the kernel of the surjective `k`-algebra hom `orbitEval M P : A → k`
onto a field (`orbitEval` is split by `algebraMap k A`). -/
instance orbitPointIdeal_isMaximal {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) : (orbitPointIdeal M P).IsMaximal := by
  have hsurj : Function.Surjective (orbitEval M P).toRingHom := fun y ↦
    ⟨algebraMap k (orbitRing M) y, (orbitEval M P).commutes y⟩
  rw [orbitPointIdeal]
  exact (RingHom.ker_isMaximal_of_surjective _ hsurj)

instance orbitPointIdeal_isPrime {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) : (orbitPointIdeal M P).IsPrime :=
  (orbitPointIdeal_isMaximal M P).isPrime

/-- **L3.0 transport — `orbitEval M 1 ∘ α_P = orbitEval M P`.** The normal-form evaluation
precomposed with the `G_d`-automorphism `α_P` is evaluation at the orbit point `P • M`: chasing
the shift `eval (canonicalCoord M) ∘ pullback P = eval (canonicalCoord (P•M))`. -/
theorem orbitEval_comp_orbitRingAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) :
    (orbitEval M 1).comp (orbitRingAlgEquiv M P).toAlgHom = orbitEval M P := by
  refine AlgHom.ext (fun a ↦ ?_)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [AlgHom.comp_apply]
  change orbitEval M 1 (orbitRingAlgEquiv M P (Ideal.Quotient.mk (orbitIdeal M) f))
    = orbitEval M P (Ideal.Quotient.mk (orbitIdeal M) f)
  rw [orbitRingAlgEquiv_mk, orbitEval_mk, orbitEval_mk, one_smul,
    show MvPolynomial.eval (canonicalCoord d M) (baseChangePullback P f)
      = MvPolynomial.eval (canonicalCoord d (P • (canonicalCoord d).symm (canonicalCoord d M)))
        f from eval_baseChangePullback P (canonicalCoord d M) f,

exec
/bin/bash -lc 'rg -n "gaugeEquiv" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:23:2. `gaugeEquiv d P` — the coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R`, assembled by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:219:noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:233:/-- `gaugeEquiv d P` acts as `aeval (gaugeSub d P)` (the forward `AlgHom` of the `ofAlgHom`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:234:@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:236:    gaugeEquiv d P p = aeval (R := R) (gaugeSub d P) p := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:238:/-- **The mult-transport, in `gaugeEquiv` form.** `gaugeEquiv d P` sends the generic product entry
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:242:theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:244:    gaugeEquiv d P (multPoly d r c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:248:  rw [gaugeEquiv_apply, aeval_gaugeSub_multPoly]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:266:    gaugeEquiv d (1 : BaseChangeGroup (k := R) d) p = p := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:267:  rw [gaugeEquiv_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:286:  gaugeEquiv dConst witnessGauge
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:288:/-- The mult-transport fires at the concrete non-identity gauge `witnessGauge`: `gaugeEquiv` carries
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:292:    gaugeEquiv (R := ℤ) dConst witnessGauge (multPoly dConst r c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:294:  gaugeEquiv_apply dConst witnessGauge (multPoly dConst r c)

exec
/bin/bash -lc "sed -n '100,190p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
    refine ⟨P * P₀, ?_⟩
    rw [smul_eq_baseChange, baseChange_mul, ← smul_eq_baseChange, ← smul_eq_baseChange, hP₀]

/-- **Same rank pattern ⟹ same orbit closure.** The `repClosure` of the orbit set depends only on
the rank pattern — the bridge that absorbs every list-shape / reassociation choice. -/
theorem repClosure_orbitSet_eq_of_rankPattern_eq {d : Fin (N + 1) → ℕ} {A B : Tuple (k := k) d}
    (h : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      rankPattern d A i j hij = rankPattern d B i j hij) :
    repClosure (orbitSet A) = repClosure (orbitSet B) := by
  rw [orbitSet_eq_of_rankPattern_eq h]

/-! ## Piece 2b — `G_d`-stability of an orbit closure (single point ⟹ whole orbit)

A geometric per-move lemma lands a *single* point `canonicalCoord D ∈ repClosure (orbitSet U)`; to
feed the chain I need the *whole* orbit `orbitSet D ⊆ repClosure (orbitSet U)`. The closure
`repClosure (orbitSet U)` is `G_d`-stable: the action `A ↦ P • A` is a *linear* change of the
matrix-entry coordinates, so it lifts to an algebra endomorphism `baseChangePullback P` of the
coordinate ring with `eval x ∘ pullback = eval (canonicalCoord (P • canonicalCoord.symm x))`. A
polynomial vanishing on `orbitSet U` (itself `G_d`-stable) still vanishes after the shift, so the
zero locus is `G_d`-stable. -/

/-- The base-change substitution: coordinate `⟨i,r,c⟩ ↦` the `(r,c)` entry of
`(P_{i+1}) · X_i · (P_i)⁻¹` where `X_i` is the generic matrix of edge-`i` coordinate variables. The
coordinate-ring incarnation of the linear map `A ↦ P • A`. -/
noncomputable def baseChangeSub {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
    RepCoord d → MvPolynomial (RepCoord d) k :=
  fun x ↦ ((((Units.val (P x.1.succ)).map MvPolynomial.C)
      * (Matrix.of (fun (r : Fin (d x.1.succ)) (c : Fin (d x.1.castSucc)) ↦
          MvPolynomial.X (⟨x.1, r, c⟩ : RepCoord d)))
      * ((Units.val (P x.1.castSucc)⁻¹).map MvPolynomial.C) :
        Matrix (Fin (d x.1.succ)) (Fin (d x.1.castSucc)) (MvPolynomial (RepCoord d) k)))
      x.2.1 x.2.2

/-- The base-change pullback algebra endomorphism `aeval (baseChangeSub P)`. -/
noncomputable def baseChangePullback {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
    MvPolynomial (RepCoord d) k →ₐ[k] MvPolynomial (RepCoord d) k :=
  MvPolynomial.aeval (baseChangeSub P)

/-- **Evaluation of the pullback is evaluation at the shifted point.** `eval x (baseChangeSub P
coord)` recovers the coordinate of `P • (canonicalCoord.symm x)`: the substitution computes the
base-changed entry. -/
theorem eval_baseChangeSub {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
    (x : RepCoord d → k) (coord : RepCoord d) :
    MvPolynomial.eval x (baseChangeSub P coord)
      = canonicalCoord d (P • (canonicalCoord d).symm x) coord := by
  rw [baseChangeSub, canonicalCoord_apply, smul_eq_baseChange, baseChange_apply]
  -- the matrix `map (eval x)` of the symbolic product is the numeric base-changed factor
  set Xmat : Matrix (Fin (d coord.1.succ)) (Fin (d coord.1.castSucc)) (MvPolynomial (RepCoord d) k)
      := Matrix.of (fun (r : Fin (d coord.1.succ)) (c : Fin (d coord.1.castSucc)) ↦
          MvPolynomial.X (⟨coord.1, r, c⟩ : RepCoord d)) with hXmat
  have hmat : ((((Units.val (P coord.1.succ)).map MvPolynomial.C) * Xmat
        * ((Units.val (P coord.1.castSucc)⁻¹).map MvPolynomial.C) :
        Matrix (Fin (d coord.1.succ)) (Fin (d coord.1.castSucc))
          (MvPolynomial (RepCoord d) k)).map (MvPolynomial.eval x))
      = (Units.val (P coord.1.succ)) * ((canonicalCoord d).symm x coord.1)
        * (Units.val (P coord.1.castSucc)⁻¹) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 1
    · congr 1
      · funext r c; simp only [Matrix.map_apply, MvPolynomial.eval_C]
      · funext r c
        simp only [hXmat, Matrix.map_apply, MvPolynomial.eval_X, Matrix.of_apply]
        rw [← canonicalCoord_apply ((canonicalCoord d).symm x) ⟨coord.1, r, c⟩,
          Equiv.apply_symm_apply]
    · funext r c; simp only [Matrix.map_apply, MvPolynomial.eval_C]
  exact congrFun (congrFun hmat coord.2.1) coord.2.2

/-- The pullback evaluates as the shift: `eval x (baseChangePullback P f) = eval (shifted x) f`. -/
theorem eval_baseChangePullback {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
    (x : RepCoord d → k) (f : MvPolynomial (RepCoord d) k) :
    MvPolynomial.eval x (baseChangePullback P f)
      = MvPolynomial.eval (canonicalCoord d (P • (canonicalCoord d).symm x)) f := by
  rw [baseChangePullback,
    show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) f)
      = (MvPolynomial.eval x).comp ((MvPolynomial.aeval (baseChangeSub P)).toRingHom) f from rfl]
  have hhom : (MvPolynomial.eval x).comp ((MvPolynomial.aeval (baseChangeSub P)).toRingHom)
      = MvPolynomial.eval (canonicalCoord d (P • (canonicalCoord d).symm x)) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun coord ↦ ?_)
    · rw [RingHom.comp_apply]
      show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) (MvPolynomial.C r)) = _
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C,
        MvPolynomial.eval_C]
    · rw [RingHom.comp_apply]
      show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) (MvPolynomial.X coord)) = _
      rw [MvPolynomial.aeval_X, MvPolynomial.eval_X, eval_baseChangeSub]
  exact congrFun (congrArg DFunLike.coe hhom) f

/-- The orbit set is **`G_d`-stable** as a point set: shifting an orbit point by a base change stays
in the orbit. -/
theorem orbitSet_baseChange_stable {d : Fin (N + 1) → ℕ} (U : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) {y : RepCoord d → k} (hy : y ∈ orbitSet U) :

codex
The `gaugeEquiv` itself is already coefficient-ring polymorphic, which is good. The remaining issue is not automorphism construction; it is proving the target ideal after normalization is exactly the split ideal, and that is where generator-vs-structural machinery matters.
exec
/bin/bash -lc "sed -n '1,340p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.MultComorphism
import DLNFibre.Core.BaseChange

/-!
# `DLNFibre.Core.EndpointNormalization` — the gauge-change `AlgEquiv` (R2-3b-3)

The second rung of the deep product trivialization `e`. On the **unquotiented** coordinate ring
`MvPolynomial (RepCoord d) R` over an **arbitrary** commutative ring `R`, the gauge-change map is the
linear coordinate substitution implementing the vertex-unit conjugation action
`Aᵢ ↦ P_{i+1} · Aᵢ · P_i⁻¹` of `Core.BaseChange.baseChange` on the generic tuple. For the endpoint
normalization of the paper's route, the gauge `P` is identity at every interior vertex and carries
`H` at the source vertex `0`, `L⁻¹` at the target vertex `Fin.last N`: then
`mult(Ã) = L⁻¹ · mult(A) · H⁻¹`, normalizing the two endpoint factors only. Kept GENERAL in the gauge
`P` (one invertible matrix per vertex over `R`) so R2-3b-4 instantiates it with the Schur-data
unipotents.

The deliverables, for a fixed dimension vector `d : Fin (N + 1) → ℕ` over `[CommRing R]` and a gauge
`P : ∀ v, (Matrix (Fin (d v)) (Fin (d v)) R)ˣ`:

1. `gaugeSub d P` — the coordinate substitution `RepCoord d → MvPolynomial (RepCoord d) R`: the
   `⟨i, (r, c)⟩` entry of `baseChange (P.map C) (genericTuple d)`, i.e. the entries of
   `P_{i+1} · Xᵢ · P_i⁻¹` with the unit matrices pushed into the coefficient ring by `C`.
2. `gaugeEquiv d P` — the coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R`, assembled by
   `AlgEquiv.ofAlgHom` from `aeval (gaugeSub P)` and `aeval (gaugeSub P⁻¹)`. The round-trips collapse
   by the group-action laws `baseChange_mul` / `baseChange_one` on the generic tuple.
3. The **mult-transport** `aeval_gaugeSub_multPoly` : `aeval (gaugeSub P) (multPoly d r c) =
   (P_last.val.map C · Matrix.of (multPoly d) · (P 0)⁻¹.val.map C) r c` — the generic product matrix
   transforms by the two end-vertex gauges (interior units telescope away, `mult_smul`). For the
   endpoint normalization this is `L⁻¹ · multPoly · H⁻¹` (the bridge R2-3b-4 needs to turn
   `mult(A) = LEH` into `mult(Ã) = E`).

The `N = 1` coincidence (first factor = last factor) is automatic: `baseChange` is defined uniformly
per edge from both endpoint vertices, so the single edge `0` of `Fin 1` already carries both end
gauges.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`. The gauge is over the arbitrary
coefficient ring `R`; nothing here needs a field, `IsAlgClosed`, or `Infinite` (in particular we
avoid `baseChangePullback`, which carries `[Infinite k]` from polynomial-function ext).
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {R : Type u} [CommRing R] {N : ℕ}

/-! ## Lifting a gauge into the coefficient ring -/

/-- Lift a gauge `P : ∀ v, (Matrix (Fin (d v)) (Fin (d v)) R)ˣ` to one over the coordinate ring
`MvPolynomial (RepCoord d) R` by pushing each unit matrix through `C` (the `RingHom.mapMatrix` of the
inclusion `C : R →+* MvPolynomial (RepCoord d) R`). -/
noncomputable def liftGauge (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    BaseChangeGroup (k := MvPolynomial (RepCoord d) R) d :=
  fun v ↦ Units.map (RingHom.mapMatrix (C : R →+* MvPolynomial (RepCoord d) R)).toMonoidHom (P v)

/-- `liftGauge` is a group homomorphism on the gauge group (it lifts `Units.map` of a monoid hom,
pointwise). Stated as the two facts the round-trip needs: it preserves `1` and `⁻¹` pointwise via the
defining `Units.map`. -/
theorem liftGauge_mul (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d) :
    liftGauge d (P * Q) = liftGauge d P * liftGauge d Q := by
  funext v
  simp only [liftGauge, Pi.mul_apply, map_mul]

@[simp] theorem liftGauge_one (d : Fin (N + 1) → ℕ) :
    liftGauge d (1 : BaseChangeGroup (k := R) d) = 1 := by
  funext v
  simp only [liftGauge, Pi.one_apply, map_one]

theorem liftGauge_inv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    liftGauge d (P⁻¹) = (liftGauge d P)⁻¹ := by
  funext v
  simp only [liftGauge, Pi.inv_apply, map_inv]

/-! ## The gauge substitution -/

/-- **The gauge substitution** `gaugeSub d P : RepCoord d → MvPolynomial (RepCoord d) R`: the
`⟨i, (r, c)⟩` coordinate maps to the `(r, c)` entry of the gauged generic factor
`baseChange (liftGauge d P) (genericTuple d) i = P_{i+1} · Xᵢ · P_i⁻¹` (units lifted by `C`). -/
noncomputable def gaugeSub (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    RepCoord d → MvPolynomial (RepCoord d) R :=
  fun x ↦ baseChange (liftGauge d P) (genericTuple d) x.1 x.2.1 x.2.2

/-- `aeval (gaugeSub P)` carries the generic factor `genericTuple i` to the gauged factor
`baseChange (liftGauge d P) (genericTuple d) i`. The generator goes to the corresponding entry by
definition of `gaugeSub`; `aeval_X` evaluates it. -/
theorem aeval_gaugeSub_genericTuple (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (i : Fin N) :
    (genericTuple d i).map (aeval (R := R) (gaugeSub d P))
      = baseChange (liftGauge d P) (genericTuple d) i := by
  funext r c
  rw [Matrix.map_apply, genericTuple_apply, aeval_X, gaugeSub]

/-! ## The ring hom commutes with the prefix product -/

/-- A coordinate substitution commutes with the generic prefix product: applying `aeval φ`
(rectangular `Matrix.map`) to `multPrefix (genericTuple d) j` gives the prefix product of the image
tuple `Ã i = (genericTuple d i).map (aeval φ)`. The `aeval`-analog of
`Core.MultComorphism.map_eval_multPrefix`. -/
theorem map_aeval_multPrefix (d : Fin (N + 1) → ℕ)
    (φ : RepCoord d → MvPolynomial (RepCoord d) R) (j : Fin (N + 1)) :
    (multPrefix d (genericTuple d) j).map (aeval (R := R) φ)
      = multPrefix d (fun i ↦ (genericTuple d i).map (aeval (R := R) φ)) j := by
  induction j using Fin.induction with
  | zero =>
    simp only [multPrefix_zero]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  | succ i ih =>
    rw [multPrefix_succ, multPrefix_succ, Matrix.map_mul, ih]

/-- The full generic product under `aeval (gaugeSub P)` is `mult` of the gauged generic tuple:
`(Matrix.of (multPoly d)).map (aeval (gaugeSub P)) = mult d (baseChange (liftGauge d P)
(genericTuple d))`. Combines `map_aeval_multPrefix` with `aeval_gaugeSub_genericTuple`. -/
theorem map_aeval_gaugeSub_mult (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    (Matrix.of (multPoly d)).map (aeval (R := R) (gaugeSub d P))
      = mult d (baseChange (liftGauge d P) (genericTuple d)) := by
  have hof : (Matrix.of (multPoly d) : Matrix _ _ (MvPolynomial (RepCoord d) R))
      = multPrefix d (genericTuple d) (Fin.last N) := by
    funext r c; rfl
  have htup : (fun i ↦ (genericTuple d i).map (aeval (R := R) (gaugeSub d P)))
      = baseChange (liftGauge d P) (genericTuple d) := by
    funext i; exact aeval_gaugeSub_genericTuple d P i
  rw [hof, map_aeval_multPrefix d (gaugeSub d P) (Fin.last N), htup]
  rfl

/-! ## The mult-transport -/

/-- **mult-equivariance over a `CommRing`.** `mult d (P • A) = P_last · mult d A · P_0⁻¹`: the
interior units of the base change telescope away (`submult_baseChange` at the full interval,
through `mult_eq_submult`). The `Core.FibreNormalForm.mult_smul` proof is over a `Field`; this is
the same statement over the weaker `CommRing` (the proof uses only `CommRing` facts). -/
theorem mult_smul_commRing (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (A : Tuple (k := R) d) :
    mult d (baseChange P A)
      = Units.val (P (Fin.last N)) * mult d A * Units.val ((P 0)⁻¹) := by
  rw [mult_eq_submult, mult_eq_submult, submult_baseChange]

/-- **The mult-transport.** Applying `aeval (gaugeSub P)` to the generic product entry `multPoly d r
c` gives the `(r, c)` entry of `P_last · Matrix.of (multPoly d) · P_0⁻¹` (the end-vertex units lifted
by `C`); the interior units telescope away (`mult_smul`). For the endpoint normalization
(`P_0 = H`, `P_last = L⁻¹`, interior `= 1`) this is `L⁻¹ · multPoly · H⁻¹`. -/
theorem aeval_gaugeSub_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    aeval (R := R) (gaugeSub d P) (multPoly d r c)
      = ((Units.val (liftGauge d P (Fin.last N)) * Matrix.of (multPoly d)
            * Units.val ((liftGauge d P 0)⁻¹)
          : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) (MvPolynomial (RepCoord d) R)) r c) := by
  have h : aeval (R := R) (gaugeSub d P) (multPoly d r c)
      = ((Matrix.of (multPoly d)).map (aeval (R := R) (gaugeSub d P))) r c := rfl
  rw [h, map_aeval_gaugeSub_mult d P,
    mult_smul_commRing d (liftGauge d P) (genericTuple d)]
  rfl

/-! ## The composition law and the gauge `AlgEquiv` -/

/-- The entries of `Units.val (liftGauge d Q v)` are `C`-images: `(liftGauge d Q v).val = (Q v).val.map
C` (it is `Units.map (C.mapMatrix)` of `Q v`). -/
theorem liftGauge_val_eq (d : Fin (N + 1) → ℕ) (Q : BaseChangeGroup (k := R) d) (v : Fin (N + 1)) :
    Units.val (liftGauge d Q v)
      = (Units.val (Q v)).map (C : R →+* MvPolynomial (RepCoord d) R) := by
  show Units.val (Units.map _ (Q v)) = _
  rw [Units.coe_map]
  rfl

/-- The entries of `Units.val ((liftGauge d Q v)⁻¹)` are `C`-images: `= (Q v)⁻¹.val.map C`. -/
theorem liftGauge_inv_val_eq (d : Fin (N + 1) → ℕ) (Q : BaseChangeGroup (k := R) d)
    (v : Fin (N + 1)) :
    Units.val ((liftGauge d Q v)⁻¹)
      = (Units.val ((Q v)⁻¹)).map (C : R →+* MvPolynomial (RepCoord d) R) := by
  show Units.val (Units.map _ (Q v))⁻¹ = _
  rw [Units.coe_map_inv]
  rfl

/-- A `C`-lifted (constant) gauge matrix is fixed by `aeval (gaugeSub P)`: its entries are `C`-images
in the coefficient ring, and `aeval` fixes constants (`aeval_C`). -/
theorem map_aeval_gaugeSub_liftGauge (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (v : Fin (N + 1)) :
    (Units.val (liftGauge d Q v)).map (aeval (R := R) (gaugeSub d P)) = Units.val (liftGauge d Q v)
    ∧ (Units.val ((liftGauge d Q v)⁻¹)).map (aeval (R := R) (gaugeSub d P))
        = Units.val ((liftGauge d Q v)⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [liftGauge_val_eq]
    funext a b
    rw [Matrix.map_apply, Matrix.map_apply, aeval_C, MvPolynomial.algebraMap_eq]
  · rw [liftGauge_inv_val_eq]
    funext a b
    rw [Matrix.map_apply, Matrix.map_apply, aeval_C, MvPolynomial.algebraMap_eq]

/-- **The composition law on the generic tuple.** Applying `aeval (gaugeSub P)` to the gauged
generic factor `baseChange (liftGauge Q) (genericTuple) i` re-gauges by `P` inside: the result is
`baseChange (liftGauge Q) (baseChange (liftGauge P) (genericTuple)) i`. The constant `C`-lifted
`Q`-matrices are fixed (`map_aeval_gaugeSub_liftGauge`), the variable block re-gauges
(`aeval_gaugeSub_genericTuple`). -/
theorem map_aeval_gaugeSub_baseChange (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (i : Fin N) :
    (baseChange (liftGauge d Q) (genericTuple d) i).map (aeval (R := R) (gaugeSub d P))
      = baseChange (liftGauge d Q) (baseChange (liftGauge d P) (genericTuple d)) i := by
  rw [baseChange_apply, baseChange_apply, Matrix.map_mul, Matrix.map_mul,
    (map_aeval_gaugeSub_liftGauge d P Q i.succ).1,
    (map_aeval_gaugeSub_liftGauge d P Q i.castSucc).2,
    aeval_gaugeSub_genericTuple d P i]

/-- The two `aeval (gaugeSub …)` directions compose to the identity on the generators: for any gauges
`P`, `Q`, `aeval (gaugeSub P) (gaugeSub Q x)` is the `x`-entry of `baseChange (liftGauge (Q * P))
(genericTuple)`. Specialized to `Q = P⁻¹` (resp. `P = Q⁻¹`) it collapses to `X x`. -/
theorem aeval_gaugeSub_gaugeSub (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (x : RepCoord d) :
    aeval (R := R) (gaugeSub d P) (gaugeSub d Q x)
      = baseChange (liftGauge d (Q * P)) (genericTuple d) x.1 x.2.1 x.2.2 := by
  have h : aeval (R := R) (gaugeSub d P) (gaugeSub d Q x)
      = ((baseChange (liftGauge d Q) (genericTuple d) x.1).map
          (aeval (R := R) (gaugeSub d P))) x.2.1 x.2.2 := rfl
  rw [h, map_aeval_gaugeSub_baseChange d P Q x.1, ← baseChange_mul, liftGauge_mul]

/-- **The gauge `AlgEquiv`** of `MvPolynomial (RepCoord d) R`: `aeval (gaugeSub P)`, with inverse
`aeval (gaugeSub P⁻¹)`. The round-trips collapse by the group-action laws (`baseChange_mul` /
`baseChange_one`) on the generic tuple. The endpoint normalization instantiates `P`. -/
noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R :=
  AlgEquiv.ofAlgHom (aeval (gaugeSub d P)) (aeval (gaugeSub d P⁻¹))
    (by
      apply MvPolynomial.algHom_ext
      intro x
      rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, aeval_gaugeSub_gaugeSub, inv_mul_cancel,
        liftGauge_one, baseChange_one, genericTuple_apply])
    (by
      apply MvPolynomial.algHom_ext
      intro x
      rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, aeval_gaugeSub_gaugeSub, mul_inv_cancel,
        liftGauge_one, baseChange_one, genericTuple_apply])

/-- `gaugeEquiv d P` acts as `aeval (gaugeSub d P)` (the forward `AlgHom` of the `ofAlgHom`). -/
@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (p : MvPolynomial (RepCoord d) R) :
    gaugeEquiv d P p = aeval (R := R) (gaugeSub d P) p := rfl

/-- **The mult-transport, in `gaugeEquiv` form.** `gaugeEquiv d P` sends the generic product entry
`multPoly d r c` to the `(r, c)` entry of `P_last · multPoly · P_0⁻¹`. This is the bridge R2-3b-4
needs: with the endpoint gauge (`P_0 = H`, `P_last = L⁻¹`), it turns the chart target `mult(A) = LEH`
into `mult(Ã) = E`. -/
theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    gaugeEquiv d P (multPoly d r c)
      = ((Units.val (liftGauge d P (Fin.last N)) * Matrix.of (multPoly d)
            * Units.val ((liftGauge d P 0)⁻¹)
          : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) (MvPolynomial (RepCoord d) R)) r c) := by
  rw [gaugeEquiv_apply, aeval_gaugeSub_multPoly]

/-! ## Non-vacuity witnesses

(i) The identity gauge `P = 1` reproduces the identity `AlgEquiv` — the construction is honest at
`H = L = 1`. (ii) The transport on the `(2,2,2)` witness with a non-identity end-vertex gauge over
`ℚ` is the genuine conjugation `P_last · M · P_0⁻¹` of the generic product. -/

section Witness

/-- The identity gauge substitution is the identity on coordinates: `gaugeSub d 1 x = X x`. -/
theorem gaugeSub_one (d : Fin (N + 1) → ℕ) (x : RepCoord d) :
    gaugeSub d (1 : BaseChangeGroup (k := R) d) x = X x := by
  rw [gaugeSub, liftGauge_one, baseChange_one, genericTuple_apply]

/-- At the identity gauge the `AlgEquiv` is the identity (`H = L = 1` reproduces the identity) —
the construction is non-vacuous and honest. -/
example (d : Fin (N + 1) → ℕ) (p : MvPolynomial (RepCoord d) R) :
    gaugeEquiv d (1 : BaseChangeGroup (k := R) d) p = p := by
  rw [gaugeEquiv_apply]
  have : aeval (R := R) (gaugeSub d (1 : BaseChangeGroup (k := R) d))
      = AlgHom.id R (MvPolynomial (RepCoord d) R) := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [aeval_X, gaugeSub_one, AlgHom.id_apply]
  rw [this, AlgHom.id_apply]

/-- The constant dimension vector `(2, 2, 2)` (every `d v = 2` definitionally, so the uniform gauge
type-checks without `![…]`-reduction friction). -/
def dConst : Fin 3 → ℕ := fun _ ↦ 2

/-- The uniform `(2,2,2)` gauge over `ℤ` carrying `witnessUnit` (`!![1,1;0,1]`) at every vertex. -/
def witnessGauge : BaseChangeGroup (k := ℤ) dConst := fun _ ↦ witnessUnit

/-- The gauge `AlgEquiv` is available at the concrete non-identity `(2,2,2)` gauge `witnessGauge` over
`ℤ` — the construction is non-vacuous at a genuine `!![1,1;0,1]`-conjugation. -/
noncomputable example :
    MvPolynomial (RepCoord dConst) ℤ ≃ₐ[ℤ] MvPolynomial (RepCoord dConst) ℤ :=
  gaugeEquiv dConst witnessGauge

/-- The mult-transport fires at the concrete non-identity gauge `witnessGauge`: `gaugeEquiv` carries
each generic product entry to the conjugation `P_last · multPoly · P_0⁻¹` of the generic product.
Non-vacuous (the gauge is the genuine `!![1,1;0,1]` at every vertex, not the identity). -/
example (r : Fin (dConst (Fin.last 2))) (c : Fin (dConst 0)) :
    gaugeEquiv (R := ℤ) dConst witnessGauge (multPoly dConst r c)
      = aeval (R := ℤ) (gaugeSub dConst witnessGauge) (multPoly dConst r c) :=
  gaugeEquiv_apply dConst witnessGauge (multPoly dConst r c)

end Witness

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '330,430p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
plus `height_strict_mono_of_is_prime` forces equality. This is the honest hard direction. -/
theorem map_Iad_eq_graphIdeal_forcedB22 [IsAlgClosed k] [CharZero k] (q p r : ℕ)
    (hp : r ≤ p) (hq : r ≤ q) :
    ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq)
      = graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) := by
  set Q := MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
  set K : Ideal Q :=
    ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq) with hK
  set J : Ideal Q := graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) with hJ
  -- both ideals are prime
  haveI hsigmaPrime : (sigmaIdeal (k := k) (dStratum q p) r).IsPrime := by
    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
  haveI hIadPrime : ((Iad (k := k) q p r hp hq)).IsPrime := by
    have hdisj := (Ideal.disjoint_powers_iff_notMem
        (detPivotPoly (k := k) q p r hp hq) hsigmaPrime.isRadical).2
      (detPivotPoly_notMem_sigmaIdeal q p r hp hq)
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (S := Localization.Away (detPivotPoly (k := k) q p r hp hq))
      (Submonoid.powers (detPivotPoly q p r hp hq))
      (sigmaIdeal (dStratum q p) r) hsigmaPrime hdisj
  haveI hKprime : K.IsPrime := Ideal.map_isPrime_of_equiv (blockAlgEquivLoc (k := k) q p r hp hq)
  haveI : IsDomain (SchurLoc (k := k) q p r) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (SchurLoc (k := k) q p r)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (detSchurS_ne_zero (k := k) q p r))
  haveI hJprime : J.IsPrime := graphIdeal_isPrime _
  -- `height K = height Iad` (Ψ an equiv); `height Iad = C` (landed); `height J = C` (landed)
  have hKIad : K.height = ((Iad (k := k) q p r hp hq)).height :=
    height_map_algEquiv (blockAlgEquivLoc (k := k) q p r hp hq) ((Iad (k := k) q p r hp hq))
  have hIadC : ((Iad (k := k) q p r hp hq)).height = ((q - r) * (p - r) : ℕ) := by
    rw [Iad, height_map_sigmaIdeal_away_eq_cCodim q p r hp hq
        (kostantPartitions_stratum_nonempty q p r hq hp), cCodim_stratum_eq q p r hq hp
        (kostantPartitions_stratum_nonempty q p r hq hp), Int.toNat_natCast]
  have hheightJ : J.height = ((p - r) * (q - r) : ℕ) :=
    height_graphIdeal_forcedB22_eq q p r (SchurLoc (k := k) q p r)
  have hJK : J.height = K.height := by
    rw [hheightJ, hKIad, hIadC, Nat.mul_comm]
  -- the squeeze: `J ⊆ K`, equal finite heights, both prime ⟹ `J = K`
  refine (eq_of_le_of_not_lt (graphIdeal_forcedB22_le_map_Iad q p r hp hq) (fun hlt ↦ ?_)).symm
  haveI : J.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]; right; rw [hheightJ]; exact ENat.coe_ne_top _
  exact absurd ((Ideal.height_strict_mono_of_is_prime hlt).trans_le hJK.ge)
    (lt_irrefl _)

/-- **The localized base presentation `A_loc / Iad ≅ₐ[k] Sd`** (`G2-2`). The localized determinantal
base ring `A_loc = Localization.Away detΔ`, modulo its base ideal `Iad = (sigmaIdeal …).map …`, is
the free Schur localization `Sd = Localization.Away detSchurS` — a regular ring of dimension `δ`.
Via the height squeeze `Ψ(Iad) = J` (`map_Iad_eq_graphIdeal_forcedB22`) and the graph-ideal quotient
`Q ⧸ J ≅ Sd` (`graphIdealQuotientEquiv`, the `B22`-block elimination). -/
noncomputable def basePresentationEquiv [IsAlgClosed k] [CharZero k] (q p r : ℕ)
    (hp : r ≤ p) (hq : r ≤ q) :
    (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
      ≃ₐ[k] SchurLoc (k := k) q p r := by
  have e₁ : (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
      ≃ₐ[k] (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))) :=
    Ideal.quotientEquivAlg ((Iad (k := k) q p r hp hq))
      (graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
      (blockAlgEquivLoc (k := k) q p r hp hq)
      (map_Iad_eq_graphIdeal_forcedB22 q p r hp hq).symm
  have e₂ : (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
      ≃ₐ[k] SchurLoc (k := k) q p r :=
    (graphIdealQuotientEquiv (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))).restrictScalars k
  exact e₁.trans e₂

/-! ## Non-vacuity witness — `(q, p, r) = (2, 2, 1)`

The `2 × 2` rank-`≤ 1` determinantal base: `#B22block = (2−1)(2−1) = 1 = C` eliminated coordinate,
`#SchurVar = 1·(2 + 2 − 1) = 3 = δ` free coordinates. The presentation exhibits `A_loc/Iad` as the
free Schur localization `Sd` (a regular ring of dimension `δ = 3`). -/

/-- **Witness (`2 × 2`, `r = 1`).** `#B22block = 1 = C` (one eliminated `B22` coordinate),
`#SchurVar = 3 = δ` (three free Schur coordinates). -/
example : Nat.card (B22block 2 2 1) = 1 ∧ Nat.card (SchurVar 2 2 1) = 3 := by
  refine ⟨?_, ?_⟩
  · rw [card_B22block]
  · rw [card_SchurVar 2 2 1 (by norm_num) (by norm_num)]

/-- The presentation equivalence is available at `(2, 2, 1)` for any algebraically closed field of
characteristic `0` — non-vacuous. -/
noncomputable example [IsAlgClosed k] [CharZero k]
    (h : (1 : ℕ) ≤ 2) :
    (Localization.Away (detPivotPoly (k := k) 2 2 1 h h) ⧸ Iad (k := k) 2 2 1 h h)
      ≃ₐ[k] SchurLoc (k := k) 2 2 1 :=
  basePresentationEquiv 2 2 1 h h

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '1,180p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.NullstellensatzCodim
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# `DLNFibre.Core.VarietyDimRadical` — `varietyDim`/`ringKrullDim` is radical-insensitive

The formal linchpin of the route-(c) non-circularity de-risk (thread 31). The earlier scheme-level
product-iso route (R2-3b-4) was circular *for reducedness*: the forward map needed the strict ideal
inclusion `sigmaIdeal ≤ ker`, available only as `≤ radical`. The **dimension** identity `hSweep`
(`varietyDim Σ^r = δ + varietyDim F`) never touches that question, because `varietyDim` reads only
the **reduced / closed-set** structure: `ringKrullDim (R ⧸ I)` depends on `I` only through its
radical (both quotients have the same prime spectrum). So the route-(c) dimension build works
through `vanishingIdeal` (radical by construction) and never needs `fibreGenIdeal` to be radical.

A companion `varietyDim` invariance, the foundation of the route-(c) chart trivialization
(thread 31 rung 2): `varietyDim` transports across a **coordinate-ring `AlgEquiv`**
(`varietyDim_eq_of_coordRingAlgEquiv`) — even between varieties in *different* ambient affine
spaces. A regular isomorphism of affine varieties induces such an `AlgEquiv`, so this is the bridge
that carries the pivot-chart trivialization `mult⁻¹(U) ∩ Σ^r ≅ U × F` to a `varietyDim` equality
without ever realizing both sides in one ambient space.

## Main results
- `ringKrullDim_quotient_radical` — `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical)`.
- `ringKrullDim_quotient_eq_of_radical_eq` — same Krull dim for two ideals with equal radical.
- `varietyDim_eq_of_coordRingAlgEquiv` — `varietyDim` transport across a coordinate-ring `AlgEquiv`.
-/

namespace DLNFibre.Core

open PrimeSpectrum MvPolynomial

universe u

/-- **Radical-insensitivity of the quotient Krull dimension.** `ringKrullDim (R ⧸ I)` depends on `I`
only through its radical: `Spec (R ⧸ I) = zeroLocus I = zeroLocus I.radical = Spec (R ⧸ I.radical)`
as ordered sets, and Krull dimension is a spectrum invariant. -/
theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]

/-- Two ideals with the same radical give the same quotient Krull dimension — the form the route-(c)
fibre-dimension build consumes (it reads `varietyDim` off `vanishingIdeal`, while a chart
presentation may hand it the generator ideal `fibreGenIdeal`, equal only up to radical). -/
theorem ringKrullDim_quotient_eq_of_radical_eq {R : Type*} [CommRing R] {I J : Ideal R}
    (h : I.radical = J.radical) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ J) := by
  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]

/-- **`varietyDim` transports across a coordinate-ring `AlgEquiv`.** If the coordinate rings
`MvPolynomial σ k ⧸ vanishingIdeal Z` and `MvPolynomial τ k ⧸ vanishingIdeal W` are `k`-algebra
isomorphic (the algebraic content of a regular isomorphism `Z ≅ W` of affine varieties, possibly in
different ambient spaces `σ`, `τ`), then `varietyDim Z = varietyDim W`. The Krull dimension is a
ring-isomorphism invariant (`ringKrullDim_eq_of_ringEquiv`); the `unbotD 0` wrapper is preserved. -/
theorem varietyDim_eq_of_coordRingAlgEquiv {k : Type u} [Field k] {σ τ : Type u}
    {Z : Set (σ → k)} {W : Set (τ → k)}
    (e : (MvPolynomial σ k ⧸ vanishingIdeal k Z) ≃ₐ[k]
          (MvPolynomial τ k ⧸ vanishingIdeal k W)) :
    varietyDim Z = varietyDim W := by
  unfold varietyDim
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]

end DLNFibre.Core

/-- Non-vacuity witness: in `ℚ[X]`, the square `(X)^2` of the prime `(X)` shares its radical, so the
two quotient Krull dimensions agree — a genuinely non-reduced ideal `(X)^2` reduced to `(X)` without
changing the dimension. -/
example :
    ringKrullDim (Polynomial ℚ ⧸ (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ)) ^ 2)
      = ringKrullDim (Polynomial ℚ ⧸ (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ))) := by
  apply DLNFibre.Core.ringKrullDim_quotient_eq_of_radical_eq
  exact Ideal.radical_pow (I := (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ))) (by norm_num)

exec
/bin/bash -lc 'rg -n "splitBaseFibreIdeal|BaseFibre|FibreAlg|tensor.*Fibre|Sred.*tensor|product iso|trivialization|poly.*extension|ringKrullDim.*tensor|ringKrullDim.*MvPolynomial|PolynomialDimension|quotient.*map" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:8:The first rungs of the **deep** product trivialization `e` that R2-3a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:43:   (`Ideal.quotientMapₐ`), then composed with `basePresentationEquiv.symm` to give a `k`-algebra map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:47:**Scope (what is NOT here).** The full product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg`, the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:131:`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:318:R2-3a's product iso `e` needs). `[IsAlgClosed k] [CharZero k]` (for `basePresentationEquiv`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:329:`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:332:(`RingHom.toAlgebra`). The `R = SchurLoc q p r`-algebra structure R2-3a's product iso `e` needs. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:340:localization-quotient maps are `k`-algebra maps). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:390:the localized base→total quotient map `baseQuotMap` available at that anchor over
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:415:/-- The localized base→total quotient map `baseQuotMap` is available at the `N = 1` anchor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:17:fibre-bundle / rank-chart local-trivialization of `mult` over the exact-rank determinantal stratum
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:18:A companion `varietyDim` invariance, the foundation of the route-(c) chart trivialization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:22:that carries the pivot-chart trivialization `mult⁻¹(U) ∩ Σ^r ≅ U × F` to a `varietyDim` equality
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:2:import DLNFibre.Core.PolynomialDimension
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:64:    (ringKrullDim (MvPolynomial (Fin n) k ⧸ p)).unbotD 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:33:  -- Abbreviations: `pS = (Q.under R) S`, `f = quotient map onto the fibre`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:38:  -- `comap f ⊥ = pS` (the kernel of the quotient map), in usable form.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:87:The correct trivialization (decorrelated-Codex, 2026-06-23) is NOT a polynomial algebra: the fibre
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:95:the `Algebra.TensorProduct.instFree` lever the corrected Schur trivialization closes on. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:99:/-- **The Schur closer (model, corrected).** A chart trivialization `Rt ≃ₐ[Rb] Rb ⊗[k] F_E` to the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:59:      ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p) = (s : WithBot ℕ∞) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:94:    (Ideal.primeHeight p : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:122:      ringKrullDim ((MvPolynomial (Fin 1) k) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) k)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:77:quotient `comap`, strictly monotone) into the primes `⊇ I` of `R`; its head contains a minimal prime
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:94:  -- map the chain into `Spec R` via the (strictly monotone) quotient comap.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:120:    (I.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ I) = (Nat.card σ : WithBot ℕ∞) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:55:      = (ringKrullDim (MvPolynomial (RepCoord d) k ⧸
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:8:import DLNFibre.Core.PolynomialDimension
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:232:theorem ringKrullDim_quotient_map_algEquiv {R S : Type*} [CommRing R] [CommRing S] {k : Type*}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:236:    (Ideal.quotientEquivAlg p (p.map (e : R →+* S)) e rfl).symm.toRingEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:277:      have hdimP : ringKrullDim (MvPolynomial (Fin (d + 1)) k ⧸ p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:278:          = ringKrullDim ((MvPolynomial (Fin d) k)[X] ⧸ P) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:279:        (ringKrullDim_quotient_map_algEquiv Φ p).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:283:      have hdimq : ringKrullDim ((MvPolynomial (Fin d) k)[X] ⧸ P)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:284:          = ringKrullDim (MvPolynomial (Fin d) k ⧸ q) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:339:    (p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:350:    (Ideal.primeHeight p : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:360:    + ringKrullDim ((MvPolynomial (Fin 2) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:367:example : ringKrullDim ((MvPolynomial (Fin 2) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:378:    (1 : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin 2) ℚ) ⧸ p) = (2 : WithBot ℕ∞) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:64:prime `q.comap g` has zero-dimensional quotient: `B/(q.comap g)` embeds finitely (Zariski's lemma)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:66:theorem ringKrullDim_quotient_comap_etale_eq_zero {n : ℕ} {S : Type*} [CommRing S] [Algebra k S]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:68:    ringKrullDim ((MvPolynomial (Fin n) k) ⧸ q.comap g) = 0 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:87:  -- the induced quotient map `B/(q.comap g) → S/q` is integral injective, `S/q` a field of dim 0.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:89:  have hdim : ringKrullDim (S ⧸ q) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ q.comap g) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:101:  have hL5 := height_add_ringKrullDim_quotient_eq k n (q.comap g)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:102:  rw [ringKrullDim_quotient_comap_etale_eq_zero g hg q, add_zero] at hL5
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:9:import DLNFibre.Core.PolynomialDimension
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:43:`height_A p = height_B q`; the induced quotient map `B ⧸ q ↪ A ⧸ p` is integral injective so
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:93:/-! ### The induced quotient map of a contracted prime is integral injective -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:116:    (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:117:      = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:141:  -- `dim (A ⧸ p) = dim (B ⧸ q)` via the integral injective induced quotient map.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:146:    -- `quotientMap p g le_rfl : (B ⧸ p.comap g) →+* (A ⧸ p)`, and `q = p.comap g`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:161:    (m.height : WithBot ℕ∞) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:175:    ringKrullDim (Localization.AtPrime m) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:194:      + ringKrullDim (((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) ⧸
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:196:      = ringKrullDim ((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:204:      = ringKrullDim ((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SchurGauge.lean:9:The first easier piece of the route-(c) pivot-chart trivialization (thread 31 rung 2): the pivot
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:59:    (m.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ k ⧸ I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:79:    height_map_algEquiv Φ m, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL4d
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:89:    ringKrullDim (Localization.AtPrime m) = ringKrullDim (MvPolynomial σ k ⧸ I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:568:ambient `ringKrullDim (MvPolynomial (RepCoord d) k) = card < ⊤` and `≥ 0` (nontrivial). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:7:The second rung of the deep product trivialization `e`. On the **unquotiented** coordinate ring
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:38:theorem ringKrullDim_quotient_graphIdeal_eq (c : σ → MvPolynomial τ k) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:39:    ringKrullDim (MvPolynomial σ (MvPolynomial τ k) ⧸ graphIdeal c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:66:  have hdim : ringKrullDim (MvPolynomial (σ ⊕ τ) k ⧸ J₀)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:67:      = ringKrullDim (MvPolynomial σ (MvPolynomial τ k) ⧸ graphIdeal c) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:68:    rw [hmap]; exact ringKrullDim_quotient_map_algEquiv e.symm (graphIdeal c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:56:    ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:72:  have hne : ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸ I) ≠ ⊥ :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:74:      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (RepCoord (dStratum n m)) k ⧸ I)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:106:`affine_domain_height_add_ringKrullDim_quotient_eq` is over `MvPolynomial (Fin n) k`. Transport it to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:119:    (p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial σ k ⧸ I) ⧸ p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:120:      = ringKrullDim (MvPolynomial σ k ⧸ I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:136:    ringKrullDim_quotient_map_algEquiv Φ p, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:32:    ringKrullDim (MvPolynomial ι k) = Nat.card ι := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:37:    ringKrullDim (MvPolynomial (Fin n) k) = n := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:132:example : ringKrullDim (MvPolynomial (Fin 1) ℚ) = 1 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean:20:scheme, no algebra map between the base/total coordinate quotient rings). Building that ring map +
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:7:# `DLNFibre.Core.FibreReducedTrivialization` — route-(b) reducedness via the trivialization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:9:The route-(b) reducedness chain of `G2-3` (thread 17, R2-3), wired against the **trivialization** of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:14:trivialization** `S ≅ₐ[k] R ⊗_k F_E` (endpoint normalization), then **descends** to `F_E` over the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:18:**closer that consumes it**, leaving the single open rung — the deep product trivialization `e`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:28:2. **`fibreGenIdeal_isRadical_of_trivialization`** — the full route-(b) chain: given the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:29:   trivialization `e : S ≃ₐ[k] R ⊗_k FibreAlg d B` and `IsReduced S` (the reduced chart ring),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:33:3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:38:**What is Proved vs Assumed here.** Everything above is proved sorry-free *given* the trivialization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:40:`sorry` or a global axiom. The deep trivialization `e` itself (the endpoint-normalization product
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:68:abbrev FibreAlg (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:77:    (fibreGenIdeal d B).IsRadical ↔ IsReduced (FibreAlg d B) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:99:/-! ## The route-(b) chain through the trivialization (the open rung as a hypothesis) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:101:/-- **Route (b): `fibreGenIdeal` radical, through the trivialization.** Given the chart
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:102:trivialization `e : S ≃ₐ[k] R ⊗_k F_B` (the endpoint-normalization product iso) and that the chart
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:107:theorem fibreGenIdeal_isRadical_of_trivialization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:111:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:115:  have hRF : IsReduced (R ⊗[k] FibreAlg d B) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:120:/-- **The radical-collapse of `MultComorphism` point 4** (through the trivialization). With the cut
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:121:ideal radical (`fibreGenIdeal_isRadical_of_trivialization`), the engine's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:126:theorem vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization [IsAlgClosed k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:130:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:133:    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:150:hypotheses of `fibreGenIdeal_isRadical_of_trivialization` — so the theorem is not vacuous. (Here the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:154:    [Algebra k R] [IsReduced (R ⊗[k] FibreAlg d B)] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:156:  fibreGenIdeal_isRadical_of_trivialization d B R (R ⊗[k] FibreAlg d B)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:65:    (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:66:      = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:72:    (m.height : WithBot ℕ∞) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:102:    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:15:The catenary dimension formula `Ideal.height p + ringKrullDim (R ⧸ p) = n` for `R = MvPolynomial
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:28:   transport lemmas (`height_map_algEquiv`, `ringKrullDim_quotient_map_algEquiv`):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:29:   `height_add_ringKrullDim_quotient_eq_card`, `ringKrullDim (MvPolynomial σ k) = Nat.card σ`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:108:    ringKrullDim (MvPolynomial σ k) = (Nat.card σ : WithBot ℕ∞) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:115:theorem height_add_ringKrullDim_quotient_eq_card [Finite σ] (p : Ideal (MvPolynomial σ k))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:117:    (p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ p) = (Nat.card σ : WithBot ℕ∞) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:125:  have hdim : ringKrullDim (MvPolynomial (Fin (Fintype.card σ)) k ⧸ q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:126:      = ringKrullDim (MvPolynomial σ k ⧸ p) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:127:    ringKrullDim_quotient_map_algEquiv e p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:140:  (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:153:  have hne : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z) ≠ ⊥ :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:155:      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ vanishingIdeal k Z)

codex
One more check: there is a `ChartFlatnessProbe` that often records earlier route choices and failed simplifications. I’m reading it because it may already contain the answer to the “shorter dimension-only path” question.
exec
/bin/bash -lc "sed -n '1,180p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Ideal.GoingDown
import DLNFibre.Core.MultComorphism

/-!
# `DLNFibre.Core.ChartFlatnessProbe` — the G2a chart-flatness API-surface contract

**Status: API contract / thermometer artefact, NOT a theorem.** Thread 09 (2026-06-23) is the GATING
probe for route **M-goingdown** of the rank-chart fibre-codimension build: localize F1's `multComap`
at the pivot minor and ask whether the chart-localized total ring is **flat** (via free, through the
Schur section) over the chart-localized base ring — which would feed the LANDED going-down
additivity `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`.

This module records the **verified-present localization + flatness API** as `example`-blocks
(durable pins), and states — without `sorry` — the precise SHAPE of the gating object, so the
verdict rests on confirmed contracts rather than recalled signatures.

**The verdict (in the thread report):** the localization + flatness *API* is present at v4.29
and the localized comorphism `Localization.Away.mapₐ` is constructible. But the *object* route
M-goingdown needs flat is NOT the global `multComap` — that map is provably **not flat** (the fibre
dimension jumps 4 → 5 as the target degenerates rank 1 → rank 0 on the `(2,2,2)` anchor, recorded in
`Core.FibreCodim`). The flatness lives only on the **exact-rank determinantal chart**, whose
base/total rings are quotients by determinantal ideals carried in the engine ONLY as opaque
`vanishingIdeal`s — so the Schur section cannot be exhibited as an `AlgEquiv` without first building
an explicit presentation of those quotient rings (a determinantal-algebra build). See the report.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core.ChartFlatProbe

open scoped TensorProduct
open MvPolynomial

universe u

/-! ## The localized comorphism exists (the chart-localized `algebraMap`)

`Localization.Away.mapₐ f a : Localization.Away a →ₐ[R] Localization.Away (f a)` is the localized
algebra map. Specialised to F1's `multComap d` and a pivot element `Δ` of the base coordinate ring,
it IS the chart-localized comorphism the route wants — its mere existence is not the wall. -/

/-- **The chart-localized comorphism exists.** For a base-ring element `Δ` (the pivot minor in
target coords), `Localization.Away.map` builds the localized comorphism of `mult`:
`(R_base)[1/Δ] →ₐ[k] (R_tot)[1/multComap Δ]`. Construction, not flatness. -/
noncomputable example {k : Type u} [Field k] {N : ℕ} (d : Fin (N + 1) → ℕ)
    (Δ : MvPolynomial (Fin (d (Fin.last N)) × Fin (d 0)) k)
    (Rb : Type u) [CommRing Rb] [Algebra (MvPolynomial (Fin (d (Fin.last N)) × Fin (d 0)) k) Rb]
    [IsLocalization.Away Δ Rb]
    (Rt : Type u) [CommRing Rt] [Algebra (MvPolynomial (RepCoord d) k) Rt]
    [IsLocalization.Away (multComap d Δ) Rt] :
    Rb →+* Rt :=
  IsLocalization.Away.map Rb Rt (multComap d).toRingHom Δ

/-! ## Localization is always flat over the base (`IsLocalization.flat`)

The localization `R[1/Δ]` is flat over `R` — present and unconditional. This is the EASY flatness
(localizing a single ring); it is NOT the route's flatness (total-over-base via the comorphism). -/

/-- A localization is flat over the ring it localizes (`IsLocalization.flat`). -/
example {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] : Module.Flat R S :=
  IsLocalization.flat S M

/-! ## The route's flatness, stated honestly as a hypothesis (the gating object)

The fact route M-goingdown needs: total-localized FLAT over base-localized THROUGH the comorphism,
with the base/total being the EXACT-RANK quotient rings (not the full polynomial rings). The engine
has no explicit presentation of those quotient rings, so we can only *state* the target as a
hypothesis here — this `example` pins its TYPE (the going-down consumer), not a proof. -/

/-- **The going-down consumer.** Given the route's flatness as a `[Module.Flat]` instance on a tower
`Rb → Rt`, the LANDED height-additivity fires — confirming the gating fact, once proved, needs no
hypothesis beyond Noetherianity. This is the contract the chart-flatness proof must discharge. -/
example {Rb Rt : Type u} [CommRing Rb] [CommRing Rt] [Algebra Rb Rt] [IsNoetherianRing Rb]
    [IsNoetherianRing Rt] [Module.Flat Rb Rt]
    (p : Ideal Rb) [p.IsPrime] (P : Ideal Rt) [P.IsPrime] [P.LiesOver p] :
    P.height = p.height + (P.map (Ideal.Quotient.mk (p.map (algebraMap Rb Rt)))).height :=
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P

/-! ## The Schur-freeness model shape (free total over base on a TRIVIALIZED chart)

The correct trivialization (decorrelated-Codex, 2026-06-23) is NOT a polynomial algebra: the fibre
over `E` is **reducible** (`F_E = k[u,v,X,Z,ℓ,m]/(uX+vZ−1, ℓm)` for the anchor — note the `ℓm = 0`
relation), so the chart is the BASE CHANGE `Rt ≃ₐ[Rb] Rb ⊗[k] F_E`, not `MvPolynomial _ Rb`. Over a
field `k` the fibre `F_E` is free as a `k`-module (every vector space is free), so the base change
is free, hence flat, over `Rb`. This pins what the Schur section must DELIVER; the wall is building
the trivializing `AlgEquiv` from the engine's opaque `vanishingIdeal`-quotients, not the closer. -/

/-- The base change `Rb ⊗[k] F` of a `k`-module `F` is free over `Rb` (over a field, `F` is free) —
the `Algebra.TensorProduct.instFree` lever the corrected Schur trivialization closes on. -/
example {k : Type u} [Field k] (Rb F : Type u) [CommRing Rb] [Algebra k Rb]
    [AddCommGroup F] [Module k F] : Module.Free Rb (Rb ⊗[k] F) := inferInstance

/-- **The Schur closer (model, corrected).** A chart trivialization `Rt ≃ₐ[Rb] Rb ⊗[k] F_E` to the
base change of the (reducible, free-over-`k`) fibre algebra `F_E` makes `Rt` free, hence flat, over
`Rb` — the one-liner the route ends on, once the trivializing `AlgEquiv` exists. -/
example {k : Type u} [Field k] (Rb Rt F : Type u) [CommRing Rb] [CommRing Rt] [Algebra k Rb]
    [AddCommGroup F] [Module k F] [Algebra Rb Rt] (e : Rt ≃ₗ[Rb] Rb ⊗[k] F) :
    Module.Flat Rb Rt :=
  Module.Flat.of_linearEquiv e

end DLNFibre.Core.ChartFlatProbe

exec
/bin/bash -lc "sed -n '1,170p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.MultComorphism

/-!
# `DLNFibre.Core.FibreCodim` — the fibre-codimension LOWER bound (partial F2 / Lemma 4.6)

**Scope, stated honestly.** Lehalleur–Rimányi Lemma 4.5/4.6 is the *codimension identity*

> `codimRepCanonical (mult⁻¹ B) = codimRepCanonical Σ̄^r + r·(d_0 + d_N − r)`  (`B` rank `r`).

This module proves the **easy half** that is reachable from the committed engine — the inclusion
lower bound

> `codimRepCanonical Σ̄^r ≤ codimRepCanonical (mult⁻¹ B)`

— and **only** that half. The identity itself is **NOT** proved here: its honest proof needs the
fibre-bundle / rank-chart local-trivialization of `mult` over the exact-rank determinantal stratum
`Mat^{rk=r}` (the paper's Lie-group submersion argument), which is **absent from Mathlib v4.29**.
The naïve "two-inequality sandwich" (Krull lower bound + affine-domain upper bound) provably cannot
close the gap: Krull's height theorem bounds height *above* by the generator count `d_N·d_0`, the
wrong direction and far larger than the shift `δ = r(d_0+d_N−r)`; and `mult` is **not flat** — the
fibre dimension *jumps* as the rank drops (witness `(2,2,2)`: the rank-`1` fibre has dimension `4`,
the rank-`0` fibre `mult⁻¹(0) = Σ̄^0` has dimension `5`), so the going-down additivity
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` does not apply to the comorphism at the
closed point `B`. The shift `δ` only materialises after restricting to the exact-rank chart where
the map *is* flat — a substantial new build (explicit pivot charts, the section `D = C A⁻¹ B`, the
product `mult⁻¹(U) ∩ Σ̄^r ≅ U × mult⁻¹(E)`, flatness per top component). The full identity stays
**Cited** (`DLN.BundleShiftInterface.cited_bundle_shift`) until that build lands.

What this lower bound *is*: a rigorous, non-overclaiming piece of bedrock the future chart build can
stand on. Mechanism: `mult⁻¹(B) ⊆ Σ̄^r` (rank of the product on the fibre is `rank B = r ≤ r`), so
`canonicalCoord '' (mult⁻¹ B) ⊆ canonicalCoord '' Σ̄^r`; `vanishingIdeal` is order-reversing and
`Ideal.height` is monotone, giving the codimension inequality. No `[IsAlgClosed]`/`[CharZero]`
needed — this half is pure inclusion monotonicity.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## `codimRepCanonical` is monotone under set inclusion (general lemma) -/

/-- **`codimRepCanonical` is monotone under inclusion.** A subset's geometric codimension is at
least that of any superset: a larger set has a smaller vanishing ideal (`vanishingIdeal_anti_mono`),
and `Ideal.height` is monotone, so `codimRepCanonical Z' ≤ codimRepCanonical Z` when `Z ⊆ Z'`.
Network-free, no field-closure hypothesis. -/
theorem codimRepCanonical_mono {d : Fin (N + 1) → ℕ} {Z Z' : Set (Tuple (k := k) d)}
    (h : Z ⊆ Z') : codimRepCanonical Z' ≤ codimRepCanonical Z := by
  apply Ideal.height_mono
  exact MvPolynomial.vanishingIdeal_anti_mono (Set.image_mono h)

/-! ## The fibre sits inside the closed rank-`≤ r` locus -/

/-- **The fibre over a rank-`r` matrix lies in `Σ̄^r`.** If `mult A = B` and `B.rank = r` then
`(mult A).rank = r ≤ r`, so `A ∈ productRankLocusLE d r`: `mult⁻¹(B) ⊆ Σ̄^r`. -/
theorem fibre_subset_productRankLocusLE {d : Fin (N + 1) → ℕ}
    {B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k} {r : ℕ} (hB : B.rank = r) :
    fibre d B ⊆ productRankLocusLE d r := by
  intro A hA
  rw [mem_productRankLocusLE]
  rw [mem_fibre] at hA
  rw [hA, hB]

/-! ## The fibre-codimension lower bound (the reachable half of Lemma 4.6) -/

/-- **The fibre-codimension lower bound (partial Lemma 4.6).** For `B` of rank `r`, the geometric
codimension of the closed rank-`≤ r` product locus `Σ̄^r` is at most that of the fibre `mult⁻¹(B)`:

> `codimRepCanonical Σ̄^r ≤ codimRepCanonical (mult⁻¹ B)`.

This is the **easy half** of LR Lemma 4.5/4.6 (`codim mult⁻¹ B = codim Σ̄^r + r(d_0+d_N−r)`), the
inequality `C ≤ codim mult⁻¹ B` that follows from `mult⁻¹ B ⊆ Σ̄^r` alone. The full identity — the
shift `+ r(d_0+d_N−r)` — is **Cited** (`DLN.BundleShiftInterface.cited_bundle_shift`); it needs the
exact-rank fibre-bundle structure absent from Mathlib v4.29 (see the module docstring). No closure /
characteristic hypothesis. -/
theorem codimRepCanonical_productRankLocusLE_le_codimRepCanonical_fibre {d : Fin (N + 1) → ℕ}
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) {r : ℕ} (hB : B.rank = r) :
    codimRepCanonical (productRankLocusLE (k := k) d r) ≤ codimRepCanonical (fibre d B) :=
  codimRepCanonical_mono (fibre_subset_productRankLocusLE hB)

/-! ## Non-vacuity witness — `(2,2,2)`, `B = 0`, `r = 0`

The lower bound fires at the cleanest base point `B = 0` (`rank 0 = 0`, `Matrix.rank_zero`): there
`mult⁻¹(0) = Σ̄^0`, so the inequality `codim Σ̄^0 ≤ codim mult⁻¹(0)` is in fact an equality (`0 = 0`
shift) — the lower bound is non-vacuous and tight at `r = 0`, the only case where the full Lemma 4.6
needs no shift (already a LANDED equality in `DLN.RlctPayoff`). -/

section Witness

/-- The fibre-codimension lower bound fires on `(2,2,2)` at `B = 0` (`r = 0`):
`codim Σ̄^0 ≤ codim mult⁻¹(0)`, over `AlgebraicClosure ℚ`. -/
example :
    codimRepCanonical (productRankLocusLE (k := AlgebraicClosure ℚ) dWitness 0)
      ≤ codimRepCanonical (fibre dWitness (0 : Matrix (Fin (dWitness (Fin.last 2)))
          (Fin (dWitness 0)) (AlgebraicClosure ℚ))) :=
  codimRepCanonical_productRankLocusLE_le_codimRepCanonical_fibre _ Matrix.rank_zero

end Witness

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# `DLNFibre.Core.FlatTrivialProductProbe` — the L1-0 `Module.Flat` API-surface contract

**Status: API contract / checkpoint artefact, NOT the L1-0 theorem.** L1-0 (flatness of `mult`
restricted to a rank-`r` chart) was **checkpointed, not proved** (thread 04, 2026-06-23): the
`Module.Flat` *API* is fully viable at Mathlib v4.29 — every lever the local-triviality⟹trivial-
product⟹free⟹flat route needs is present and compiles (the `example`-blocks below are the durable
pins) — but the route is **unreachable this run** because the prerequisite object is missing: there
is no coordinate-ring pullback `A →+* B` of `mult` (the engine carries `mult` only as a *set-level*
function on `Tuple d`, with codim read through `vanishingIdeal`/`Ideal.height`; no `Spec`, no
scheme, no algebra map between the base/total coordinate quotient rings). Building that ring map +
the
determinantal chart localisation + the section-of-the-torsor trivialisation is a from-scratch
affine-AG construction (≈ 8–12 modules), not an API gap. See the thread-04 report for the verdict
and the recommended fallback (the two-inequality dimension sandwich).

This module records the **verified-present API** as `example`-blocks so the next attempt (or the
real L1-0, once the ring map exists) can stand on confirmed contracts rather than re-probing.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core.FlatProbe

open scoped TensorProduct

universe u

/-! ## Free ⟹ flat, and the polynomial / tensor trivial-product shapes -/

/-- Free modules are flat (instance), the base of the route. -/
example (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M] [Module.Free A M] :
    Module.Flat A M := inferInstance

/-- `MvPolynomial (Fin r) A` is free, hence flat, over `A` — the trivial-product model fibre. -/
example (A : Type u) [CommRing A] (r : ℕ) :
    Module.Flat A (MvPolynomial (Fin r) A) := inferInstance

/-- Tensor of frees is free over the base — the `A ⊗ F` trivial-product shape. -/
example (A F : Type u) [CommRing A] [AddCommGroup F] [Module A F] [Module.Free A F] :
    Module.Free A (A ⊗[A] F) := inferInstance

/-! ## Transport flatness across an equivalence (the "B ≃ free" closer) -/

/-- Flatness transports across a linear equivalence. -/
example (A M N : Type u) [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Flat A M] (e : N ≃ₗ[A] M) : Module.Flat A N :=
  Module.Flat.of_linearEquiv e

/-- Flatness transports across an *algebra* equivalence: `B ≃ₐ[A] (free A-algebra)` gives
`Module.Flat A B` — the one-liner the route ends on, once such an equivalence exists. -/
example (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (e : B ≃ₐ[A] MvPolynomial (Fin r) A) : Module.Flat A B :=
  Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Flatness composes along a tower `A → S → M` (`Module.Flat.trans`). -/
example (A S M : Type u) [CommRing A] [CommRing S] [AddCommGroup M] [Algebra A S]
    [Module A M] [Module S M] [IsScalarTower A S M] [Module.Flat A S] [Module.Flat S M] :
    Module.Flat A M := Module.Flat.trans A S M

/-! ## Flat-local-on-base, scheme-free (the local-triviality lever, when the ring map exists)

`mult : Σ^r → Mat^{rk=r}` is Zariski-*locally* (not globally) trivial, so the route needs a
flat-local-on-base lemma. Mathlib v4.29 has it at the **ring/module level, no schemes** — the
levers to glue per-chart freeness into global flatness over the base. They are unusable here only
because no `algebraMap A B` for `mult` exists yet. -/

/-- **Module-level flat-local-on-base.** To prove `Module.Flat R M` it suffices to prove flatness of
`LocalizedModule.Away r M` for each `r` in a spanning set `s ⊆ S` (a principal-open cover) — the
scheme-free local-triviality lever (`Module.flat_of_localized_span`). -/
example (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (s : Set R) (spn : Ideal.span s = ⊤)
    (h : ∀ r : s, Module.Flat R (LocalizedModule.Away r.1 M)) : Module.Flat R M :=
  Module.flat_of_localized_span (S := R) (M := M) s spn h

/-- **Ring-hom-level flat-local-on-base.** `RingHom.Flat` is a local property: its `propertyIsLocal`
bundles `ofLocalizationSpanTarget`, `ofLocalizationSpan`, composition stability, and iso-respect —
the descent package for gluing per-chart flatness of a ring map. -/
example : RingHom.PropertyIsLocal @RingHom.Flat := RingHom.Flat.propertyIsLocal

/-! ## Downstream levers (NOT in L1-0 scope — confirming they sit on `Module.Flat`)

These belong to L1-1 (a later tide); pinned here only to confirm the flatness fact, once proved,
feeds the height-additivity squeeze with no further hypothesis beyond Noetherianity. -/

/-- Flat ⟹ going-down (instance). -/
example (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] :
    Algebra.HasGoingDown A B := inferInstance

/-- The height-additivity lemma sits on going-down + Noetherianity (both rings Noetherian). -/
example (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] [Algebra.HasGoingDown A B]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    P.height = p.height + (P.map (Ideal.Quotient.mk (p.map (algebraMap A B)))).height :=
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P

end DLNFibre.Core.FlatProbe

exec
/bin/bash -lc "sed -n '1,180p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.DeterminantalStratumDim
import DLNFibre.Core.FibreCodim
import DLNFibre.Core.FibreHeightDirect
import DLNFibre.Core.AffineDomainDimension
import DLNFibre.Core.OrbitTangentCotangent

/-!
# `DLNFibre.Core.FibreDimFibration` — the fibre-dimension count toward Lemma 4.6 (H4)

Rung **H4** of the HEIGHT-DIRECT route to Lehalleur–Rimányi Lemma 4.6's geometry: the dimension of
the multiplication-map fibre `mult⁻¹(E)` over a rank-`r` normal form `E`, via the fibration
`mult|_{Σ̄^r} : Σ̄^r ↠ Mat^{≤r}` (dominant) and the generic-fibre-dimension count

> `codimRepCanonical (mult⁻¹ E) = C + δ`,   `C = cCodim d r`,  `δ = r(d_0 + d_N − r)`.

This module banks the **base-stratum dimension brick** the count consumes, and the **easy
inequality** `codimRepCanonical (fibre E) ≤ C + δ` (the flatness-free half), proved via the no-
going-down height inequality (Stacks 00OM) — see the per-theorem docstrings. The **hard inequality**
`codimRepCanonical (fibre E) ≥ C + δ` is the genuine no-jump residual (it needs that `E` lies in the
exact-rank good locus where the fibre dimension does not jump — generic flatness / generic
smoothness, with the going-down equality `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`
requiring `Algebra.HasGoingDown ⟸` flatness, which `mult` lacks globally since the fibre dimension
jumps as the rank drops). It is **NOT** proved here and is named honestly as such; nothing in this
module claims the full identity.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k]

/-! ## The base-stratum Krull dimension brick: `ringKrullDim O(Mat^{≤r}) = δ`

The base of the fibration is the rank-`≤ r` determinantal variety in the target matrices
`Mat_{m × n}` (`n = d_0`, `m = d_N`), encoded as the `N = 1` product-rank locus
`productRankLocusLE (dStratum n m) r`. Its coordinate ring `O(Mat^{≤r}) = MvPolynomial (RepCoord
(dStratum n m)) k ⧸ vanishingIdeal(…)` is a finite-type domain (the vanishing ideal is prime —
irreducible determinantal variety) of Krull dimension `δ = r(n + m − r)`. From the LANDED thermometer
`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
nontrivial, so `ringKrullDim ≠ ⊥`). -/

/-- **The base-stratum Krull dimension** `ringKrullDim O(Mat^{≤r}) = δ`. For `r ≤ n`, `r ≤ m`, over an
algebraically closed field of characteristic `0`, the coordinate ring of the rank-`≤ r` determinantal
variety `Mat^{≤r}_{m × n}` (the `N = 1` product-rank locus) has Krull dimension `r(n + m − r) = δ`.
The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
it to the genuine `WithBot ℕ∞` Krull dimension, using that the vanishing ideal is prime (the quotient
is a nontrivial domain, so `ringKrullDim ≠ ⊥`). -/
theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
    (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m) :
    ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸
        MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
          (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r))
      = (r * (n + m - r) : ℕ) := by
  set I := MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
    (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r) with hI
  haveI hIp : I.IsPrime :=
    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
      productRankLocusLE (k := k) (dStratum n m) r) = (r * (n + m - r) : ℕ) :=
    varietyDim_productRankLocusLE_stratum n m r hn hm
  rw [varietyDim, ← hI] at hvd
  -- the quotient is a nontrivial domain, so `ringKrullDim ≠ ⊥`.
  haveI : Nontrivial (MvPolynomial (RepCoord (dStratum n m)) k ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr hIp.ne_top
  have hne : ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸ I) ≠ ⊥ :=
    fun h ↦ by simpa [h] using
      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (RepCoord (dStratum n m)) k ⧸ I)
  obtain ⟨w, hw⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hw, WithBot.unbotD_coe] at hvd
  rw [← hw, hvd]
  norm_cast

/-! ## The base-stratum closed-point height: `height m = δ` for any maximal ideal of `O(Mat^{≤r})`

By equidimensionality at a closed point (`OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
`Fintype`-indexed) and the base Krull dimension `= δ` just established: every maximal ideal of the
irreducible base `O(Mat^{≤r})` has height `δ`. The base-side input to the going-down/00OM easy
direction. -/

/-- **The base-stratum closed-point height `= δ`.** For `r ≤ n`, `r ≤ m`, every maximal ideal `𝔪` of
the base coordinate ring `O(Mat^{≤r}_{m×n}) = MvPolynomial (RepCoord (dStratum n m)) k ⧸
vanishingIdeal(…)` has height `δ = r(n + m − r)` — equidimensionality at a closed point of the
irreducible determinantal base, with `ringKrullDim O(Mat^{≤r}) = δ`. -/
theorem height_maximal_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
    (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m)
    (𝔪 : Ideal (MvPolynomial (RepCoord (dStratum n m)) k ⧸
        MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
          (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)))
    [𝔪.IsMaximal] :
    (𝔪.height : WithBot ℕ∞) = (r * (n + m - r) : ℕ) := by
  haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
      (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)).IsPrime :=
    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
  rw [height_eq_ringKrullDim_of_isMaximal_fintype,
    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]

/-! ## Affine-domain equidimensionality over a `Fintype` coordinate index

`affine_domain_height_add_ringKrullDim_quotient_eq` is over `MvPolynomial (Fin n) k`. Transport it to
`MvPolynomial σ k` (`σ` finite) through `renameEquiv`, exactly as
`height_eq_ringKrullDim_of_isMaximal_fintype` does for the maximal corollary. This is the engine the
nested catenary `height P = height Q + height_{R/Q}(P/Q)` (the `+C` composition for the easy
direction) is built from. -/

/-- **Affine-domain equidimensionality, finite index.** For `σ` finite, `I` a prime of
`MvPolynomial σ k`, the domain `A = MvPolynomial σ k ⧸ I`, and a prime `p` of `A`:
`height p + ringKrullDim (A ⧸ p) = ringKrullDim A`. Transports
`affine_domain_height_add_ringKrullDim_quotient_eq` through `renameEquiv` and the induced quotient
algebra equivalences. -/
theorem affine_domain_height_add_ringKrullDim_quotient_eq_fintype {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (p : Ideal (MvPolynomial σ k ⧸ I)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial σ k ⧸ I) ⧸ p)
      = ringKrullDim (MvPolynomial σ k ⧸ I) := by
  classical
  haveI : Fintype σ := Fintype.ofFinite _
  set e : MvPolynomial σ k ≃ₐ[k] MvPolynomial (Fin (Fintype.card σ)) k :=
    MvPolynomial.renameEquiv k (Fintype.equivFin σ) with he
  set J : Ideal (MvPolynomial (Fin (Fintype.card σ)) k) := I.map (e : _ →+* _) with hJ
  haveI : J.IsPrime := by rw [hJ]; exact Ideal.map_isPrime_of_equiv e
  -- the induced quotient algebra equivalence `A ≃ₐ[k] A'`
  set Φ : (MvPolynomial σ k ⧸ I) ≃ₐ[k] (MvPolynomial (Fin (Fintype.card σ)) k ⧸ J) :=
    Ideal.quotientEquivAlg I J e rfl with hΦ
  -- transport `p` to a prime `p'` of `A'`
  set p' : Ideal (MvPolynomial (Fin (Fintype.card σ)) k ⧸ J) := p.map (Φ : _ →+* _) with hp'
  haveI : p'.IsPrime := by rw [hp']; exact Ideal.map_isPrime_of_equiv Φ
  have hL := affine_domain_height_add_ringKrullDim_quotient_eq k (Fintype.card σ) J p'
  -- transport the three terms back along `Φ` (heights, both quotient Krull dims) and `e`.
  rw [hp', height_map_algEquiv Φ p,
    ringKrullDim_quotient_map_algEquiv Φ p, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL
  exact hL

end DLNFibre.Core

codex
The probes confirm the shorter flatness/fibration routes were intentionally left as cited because the needed affine chart trivialization is the missing object. I’m doing one last targeted scan for determinantal-minor ideal generation, because that determines whether the `⊆` containment is merely finite computation or needs another theorem.
exec
/bin/bash -lc 'rg -n "minor|determinantal|rank.*ideal|Ideal.*minor|vanishingIdeal.*rank|Matrix.*submatrix.*det|rank_le.*zeroLocus|zeroLocus.*rank|det_submatrix.*mem_sigmaIdeal|span.*det" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib | head -400' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/SiegelsLemma.lean:29:- `‖_‖ ` : Matrix.seminormedAddCommGroup is the sup norm, the maximum of the absolute values of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/SiegelsLemma.lean:39:/- We set ‖⬝‖ to be Matrix.seminormedAddCommGroup  -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/SiegelsLemma.lean:40:attribute [local instance] Matrix.seminormedAddCommGroup
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:66:`Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (up to a minor correction at `s = 0`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/WellApproximable.lean:40:* `approxOrderOf`: in a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approxOrderOf A n δ`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/WellApproximable.lean:42:* `wellApproximable`: in a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/WellApproximable.lean:69:/-- In a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approxOrderOf A n δ` is the set of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/WellApproximable.lean:71:@[to_additive /-- In a seminormed additive group `A`, given `n : ℕ` and `δ : ℝ`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/WellApproximable.lean:73:def approxOrderOf (A : Type*) [SeminormedGroup A] (n : ℕ) (δ : ℝ) : Set A :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/WellApproximable.lean:77:theorem mem_approxOrderOf_iff {A : Type*} [SeminormedGroup A] {n : ℕ} {δ : ℝ} {a : A} :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/WellApproximable.lean:81:/-- In a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`, `wellApproximable A δ`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/WellApproximable.lean:84:@[to_additive addWellApproximable /-- In a seminormed additive group `A`, given a sequence of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/WellApproximable.lean:88:def wellApproximable (A : Type*) [SeminormedGroup A] (δ : ℕ → ℝ) : Set A :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/WellApproximable.lean:92:theorem mem_wellApproximable_iff {A : Type*} [SeminormedGroup A] {δ : ℕ → ℝ} {a : A} :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/WellApproximable.lean:99:variable {A : Type*} [SeminormedCommGroup A] {a : A} {m n : ℕ} (δ : ℝ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Bounds.lean:36:variable {E : Type*} [SeminormedAddCommGroup E]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Lean/MessageData/ForExprs.lean:83:        too minor to change.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/RamificationInertia/Basic.lean:124:  -- since `span S {det A} / M = 0`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/RamificationInertia/Basic.lean:137:  have span_d : (Submodule.span S ({algebraMap R S A.det} : Set S)).restrictScalars R ≤ M := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/RamificationInertia/Basic.lean:151:        ⊤ = (Ideal.span {algebraMap R L A.det}).restrictScalars K := ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/RamificationInertia/Basic.lean:153:  -- Because `det A ≠ 0`, we have `span L {det A} = ⊤`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/RamificationInertia/Basic.lean:172:  -- And we conclude `L = span L {det A} ≤ span K b`, so `span K b` spans everything.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Padics/MahlerBasis.lean:118:nonarchimedean seminormed group. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Padics/MahlerBasis.lean:120:    [AddCommMonoid M] [SeminormedAddCommGroup G] [IsUltrametricDist G]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:9:(`Core.FibreReducedTrivialization`) carries as a hypothesis. The engine's localized determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:19:1. `ΔPdeep d r hp hq` — the deep pivot minor: the determinant of the top-left `r×r` submatrix of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:33:   pivot minor `detPivotPoly` to the deep `ΔPdeep` (det commutes with `aeval`, `AlgHom.map_det`),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:104:/-- **The deep pivot minor** `ΔPdeep d r`: the determinant of the top-left `r×r` submatrix of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:113:/-- **The deep localized base ideal** `IadDeep d r`: the determinantal base ideal `sigmaIdeal d r`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:138:/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:163:`deepBaseComap` carries the `N = 1` pivot minor `detPivotPoly` to the deep `ΔPdeep` (making the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:167:/-- **The pivot-minor transport** (load-bearing): `deepBaseComap d` carries the `N = 1` pivot minor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:168:`detPivotPoly (d 0) (d last) r` to the deep pivot minor `ΔPdeep d r`. The determinant commutes with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:388:`deepBaseComap_detPivot` at the `N = 1` stratum `dStratum 2 2`, `r = 1`, where the deep pivot minor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:407:/-- The pivot-minor transport fires at the `N = 1` stratum `dStratum 2 2`, `r = 1`:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Tactic/Widget/SelectPanelUtils.lean:19:There are also some minor helper functions.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:17:fibre-bundle / rank-chart local-trivialization of `mult` over the exact-rank determinantal stratum
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Padics/Complex.lean:209:  · letI S := (Valued.toNormedField ℂ_[p] NNReal).toNormedCommRing.toNormedRing.toSeminormedRing
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Padics/Complex.lean:210:    letI := S.toNonUnitalSeminormedRing.toSeminormedAddCommGroup.toSeminormedAddGroup
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:10:level**: the vanishing ideal of the determinantal rank locus `orbitRankLocus M` equals the vanishing
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:12:sets). With L1's `isPrime_vanishingIdeal_orbitSet` this gives the rank locus a prime vanishing ideal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:960:of the determinantal rank locus lies in the Zariski closure of the orbit. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:968:ideal of the determinantal rank locus `orbitRankLocus M` equals the vanishing ideal of the orbit
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:987:an infinite field, the flattened determinantal rank locus `canonicalCoord '' orbitRankLocus M`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:1003:/-- **The rank locus has a prime vanishing ideal (L1★, irreducibility).** `vanishingIdeal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:1006:(`isPrime_vanishingIdeal_orbitSet`, L1). So the determinantal rank locus `Ō_M = orbitRankLocus M` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean:25:distinct partitions ⟹ distinct rank patterns ⟹ distinct orbit closures ⟹ distinct vanishing ideals);
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:14:at the pivot minor and ask whether the chart-localized total ring is **flat** (via free, through the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:26:`Core.FibreCodim`). The flatness lives only on the **exact-rank determinantal chart**, whose
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:27:base/total rings are quotients by determinantal ideals carried in the engine ONLY as opaque
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:29:an explicit presentation of those quotient rings (a determinantal-algebra build). See the report.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:47:/-- **The chart-localized comorphism exists.** For a base-ring element `Δ` (the pivot minor in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:22:`I = orbitIdeal M = vanishingIdeal(orbitSet M)` directly — no determinantal minors, no radical. The
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:82:(`vanishingIdeal_orbitRankLocus_eq_orbitSet`) this is the coordinate ring of the rank locus
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:87:orbit closure `Z_M` (L6.4 identifies it with the rank-locus ideal). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:661:(`[Infinite k]`): the variety dimension of the determinantal rank locus `Z_M = canonicalCoord d ''
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/House.lean:36:attribute [local instance] Matrix.seminormedAddCommGroup
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/House.lean:121:attribute [local instance] Matrix.seminormedAddCommGroup
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/DiophantineApproximation/Basic.lean:318:Another minor reason is that this demonstrates that the proof
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:69:`Core.RankLocusClosed`, where they were first built for the minor-polynomial / zero-locus work — this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/SelbergSieve.lean:20:minor notational difference is that we write $\nu(n)$ in place of $\frac{\omega(n)}{n}$.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:16:# `DLNFibre.Core.DeterminantalChartRing` — the bordered Schur minor (G2-2 foundation)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:19:Schur minor identity**, valid over any commutative ring (no invertibility of the pivot block):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:24:This is the polynomial that, on the determinantal locus `Mat^{rk ≤ r}`, forces the Schur relation
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:26:`(r+1)×(r+1)` minor, hence vanishes on `Σ̄^r` (rank `≤ r`). It is the generator-free handle on the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:27:localized base presentation — it avoids any determinantal-ideal generating-set theory (absent in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:28:Mathlib v4.29), reducing the base presentation to this single explicit minor + height comparison.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:47:/-! ## The bordered Schur minor identity (over any commutative ring) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:49:/-- The bordered Schur minor identity as a predicate on the four blocks, so it transfers along ring
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:119:/-- **Bordered Schur minor identity (general commutative ring).** The determinant of the bordered
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:182:/-! ## The Schur relation vanishes on the rank-`≤ r` locus (the bridge to the base ideal) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:184:/-- **The Schur expression is an `(r+1)`-minor, hence vanishes on `Mat^{rk ≤ r}`.** For a matrix
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:188:Schur minor identity) the determinant of the `(r+1)×(r+1)` bordered submatrix, which vanishes since
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:209:  -- its determinant is the Schur expression (bordered Schur minor identity)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:212:  -- and it vanishes, being an `(r+1)`-minor of a rank-`≤ r` matrix
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:222:/-! ## Step (a): the `(r+1)`-minor of the generic product lies in the base ideal `sigmaIdeal d r`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:226:(`eval_multPoly`), so an `(r+1)`-minor of `multPoly d` evaluates to the corresponding minor of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:230:/-- Evaluating any square minor of the generic product matrix `multPoly d` at the coordinates of a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:231:tuple `A` gives the corresponding minor of the actual product `mult d A` (`eval_multPoly` entrywise
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:232:through `det`/`submatrix`). General in the minor index type `ι`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:236:    eval (canonicalCoord d A) (((Matrix.of (multPoly d)).submatrix br bc).det)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:244:/-- **Step (a): the determinantal base ideal contains every `(r+1)`-minor of the generic product.**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:245:For any choice of `r+1` rows `br` and `r+1` columns `bc`, the `(r+1)×(r+1)` minor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:247:`Σ̄^r = productRankLocusLE d r`): it evaluates on every `A ∈ Σ̄^r` to an `(r+1)`-minor of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:249:theorem det_submatrix_multPoly_mem_sigmaIdeal {k : Type u} [Field k] {N : ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:252:    ((Matrix.of (multPoly d)).submatrix br bc).det ∈ sigmaIdeal (k := k) d r := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:257:  rw [show aeval (R := k) (canonicalCoord d A) ((Matrix.of (multPoly d)).submatrix br bc).det
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:258:        = eval (canonicalCoord d A) ((Matrix.of (multPoly d)).submatrix br bc).det from by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:269:count) yet its top-left `r×r` minor is `det I_r = 1 ≠ 0`. This is the localized base codimension
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:274:/-- The pivot minor polynomial: the determinant of the top-left `r×r` submatrix of the generic
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:284:determinantal base `Σ̄^r` whose top-left `r×r` block is the identity. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:299:/-- The witness has rank `≤ r`: every `(r+1)×(r+1)` minor vanishes — among `r+1` chosen columns,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:315:/-- The witness lies in the determinantal base `Σ̄^r = productRankLocusLE ![q,p] r`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:320:/-- The witness's top-left `r×r` minor of `mult` is the identity matrix. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:333:/-- The witness's top-left `r×r` minor is `det I_r = 1`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:341:/-- `detΔ ∉ sigmaIdeal ![q,p] r`: the pivot minor does not vanish on all of the base — it is `1`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:357:prime determinantal-base ideal `sigmaIdeal ![q,p] r` at the pivot minor `detΔ` (which is not in it)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MvPolynomialKerAeval.lean:22:ideal when `R` is a domain — is what the localized determinantal base presentation (`G2-2`) uses to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:16:This is the lower-bound engine for the localized determinantal base presentation (`G2-2`): the Schur
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:106:localized target the determinantal elimination's height-squeeze uses (`det ≠ 0`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:145:(`height_coordIdeal_localization_eq`). This is the engine the determinantal elimination's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaStratification.lean:35:**What is proved vs. labelled.** Throughout, `orbitRankLocus M` is the **determinantal set**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaStratification.lean:39:claim re-established in this module. So the headline asserts the determinantal-set equality it
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaStratification.lean:45:this is a SET equality of determinantal loci, not a codimension statement. **Dependency rule:**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:84:(d last N)) r` — its vanishing ideal is PRIME (irreducible determinantal variety), so the domain
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitImageDim.lean:92:the variety dimension of the determinantal rank locus `Z_M` is at most the dimension of the orbit
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:78:`M ↦ vanishingIdeal (canonicalCoord d '' Ō_M)` over `{M | (mult d M).rank ≤ r}`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:100:/-- The family map `M ↦ vanishingIdeal (Ō_M)` factors through `rpBounded`: equal bounded rank
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:102:(`orbitRankLocus_eq_of_rankPattern_eq`), hence equal images and ideals. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:117:/-- The orbit-ideal family is finite: `vanishingIdeal (Ō_M)` depends only on `rankPattern M`, which
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:289:product `0` (rank `0 ≤ 0`), so it lies in `Σ̄^0` and its orbit ideal is in the family `orbitIdeals
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GenericTuple.lean:12:`Core.RankLocusClosed` (minor polynomials of `submult`) and `Core.MultComorphism` (the coordinate-ring
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:9:The final identification of `G2-2`: the localized determinantal base ring `A_loc = Localization.Away
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:22:   image under `Ψ` of the bordered `(r+1)`-minor (LANDED `det_submatrix_multPoly_mem_sigmaIdeal`),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:90:/-! ## The bordered `(r+1)`-minor `m_b` and its `blockAlgEquiv` image `(*)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:92:For a `B22` entry `(a', b')` the bordered `(r+1)×(r+1)` minor `m_b` of the generic product (rows
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:93:`[pivots, r+a']`, columns `[pivots, r+b']`) lies in the base ideal (an `(r+1)`-minor), and under
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:94:`blockAlgEquiv` becomes `C detSchurS · X (a', b') − C (forcedNum a' b')` (the bordered Schur minor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:98:/-- The four blocks of the bordered minor at the `B22` entry `(a', b')` (entries are coordinate
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:136:/-- The bordered minor `m_b`: the determinant of the `multPoly` submatrix on rows `[pivots, r+a']`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:146:/-- The bordered minor is the determinant of `fromBlocks borderΔ borderU borderV borderD`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:160:/-- **The bordered minor lies in the base ideal `sigmaIdeal`** (it is an `(r+1)`-minor of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:161:product, `det_submatrix_multPoly_mem_sigmaIdeal` after the `Fin r ⊕ Unit ≃ Fin (r+1)` reindex). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:169:  exact det_submatrix_multPoly_mem_sigmaIdeal (dStratum q p) _ _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:215:/-- **`(*)` the bordered Schur minor identity, transported.** `blockAlgEquiv (m_b) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:236:the unit `C (algebraMap detSchurS)`, is the `Ψ`-image of the bordered minor (in `Iad`), so it
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:269:/-- The localized base ideal `Iad = (sigmaIdeal …).map (algebraMap A_eng A_loc)`: the determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:279:`Ψ (algebraMap A_eng A_loc (borderMinor …))` — the `Ψ`-image of a bordered minor (hence in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:303:bordered minor (which is in `Iad`, `borderMinor_mem_sigmaIdeal`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:373:/-- **The localized base presentation `A_loc / Iad ≅ₐ[k] Sd`** (`G2-2`). The localized determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:397:The `2 × 2` rank-`≤ 1` determinantal base: `#B22block = (2−1)(2−1) = 1 = C` eliminated coordinate,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:9:The Zariski-closedness of `orbitRankLocus M ⊆ Rep_d` — the determinantal locus cut out by the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:15:1. **The determinantal-rank bridge** (`rank_le_iff_forall_submatrix_det_eq_zero`, built here —
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:23:   variables, evaluated at `canonicalCoord A`), so each `(r+1)`-minor is a polynomial `minorPoly`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:25:   by the minor polynomials, and a `zeroLocus` is Zariski-closed (Galois-connection `l_u_l_eq_l`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:28:`rankPattern`-invariance, `rankPattern_eq_iff_orbit`) and the resulting ideal inclusion. No field
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:42:/-! ## The determinantal-rank bridge (pure matrix lemma, network-free) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:62:/-- **Direction A** (`rank ≤ r ⟹ minors vanish`). If `A.rank ≤ r` then every `(r+1)×(r+1)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:106:/-- **Direction B** (`minors vanish ⟹ rank ≤ r`, contrapositive form). If `r + 1 ≤ A.rank` then some
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:137:/-- **The determinantal-rank bridge.** Over a field, `A.rank ≤ r` iff every `(r+1)×(r+1)` submatrix
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:152:/-! ## Polynomialization: the rank-pattern minors as coordinate polynomials
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:158:the ring hom `eval`), and each `(s)`-minor of the generic `submult` is a polynomial whose value at
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:159:`canonicalCoord d A` is the corresponding numerical minor of `submult d A i j`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:186:/-- The **minor polynomial**: the determinant of an `(s)×(s)` submatrix of the generic interval
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:188:`canonicalCoord d A` is the corresponding numerical minor of `submult d A i j`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:189:(`eval_minorPoly`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:190:noncomputable def minorPoly {d : Fin (N + 1) → ℕ} (i j : Fin (N + 1)) (hij : i ≤ j) {s : ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:194:/-- Evaluating `minorPoly` at the point `canonicalCoord d A` yields the numerical `(s)`-minor of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:198:theorem eval_minorPoly {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) (i j : Fin (N + 1))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:200:    MvPolynomial.eval (canonicalCoord d A) (minorPoly i j hij er ec)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:202:  rw [minorPoly, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:207:/-- The set of **defining minor polynomials** of `orbitRankLocus M`: for each `(i, j)` with `i ≤ j`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:208:and each pair of index maps `er, ec` of size `rankPattern M i j hij + 1`, the minor polynomial
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:209:`minorPoly i j hij er ec`. Its common zero locus is exactly `canonicalCoord '' orbitRankLocus M`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:214:      (ec : Fin (rankPattern d M i j hij + 1) → Fin (d i)), p = minorPoly i j hij er ec}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:217:satisfies every rank bound `rankPattern A i j ≤ rankPattern M i j` — by the determinantal-rank
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:219:theorem mem_zeroLocus_rankMinorSet_iff {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:232:    have hmem : minorPoly i j hij er ec ∈ rankMinorSet M := ⟨i, j, hij, er, ec, rfl⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:234:    rw [hxA, eval_minorPoly A i j hij er ec] at this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:239:    rw [hxA, eval_minorPoly A i j hij er ec]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:244:/-- `canonicalCoord '' orbitRankLocus M` is the zero locus of the minor ideal `span (rankMinorSet
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:245:M)`: it is cut out by the defining minor polynomials. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:248:      = MvPolynomial.zeroLocus k (Ideal.span (rankMinorSet M)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:255:  rw [heval, mem_zeroLocus_rankMinorSet_iff M x]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:261:zero locus of its own vanishing ideal — it is cut out by the determinantal minor polynomials
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:283:every orbit point in the determinantal locus. With `isZariskiClosed_orbitRankLocus`, the Zariski
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:302:The determinantal-rank bridge fires on a concrete rank-1 matrix; the rank locus is inhabited (every
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:306:the bridge by every `1×1` minor (an entry) being `0`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:314:`2×2` minor (its determinant `1`) is nonzero. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:319:  rw [Matrix.submatrix_id_id, Matrix.det_one] at this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:6:# `DLNFibre.Core.DeterminantalStratumDim` — the determinantal-stratum dimension (AG rung 1)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:16:`productRankLocusLE ![n,m] r = {M | M.rank ≤ r}` **is** the classical rank-`≤ r` determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:150:/-! ## Brick 1 — primality of the determinantal variety at `N = 1` -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:159:/-- **The determinantal variety is the rank locus of a realizer (N = 1).** There is a tuple
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:195:/-- **Brick 1: the determinantal variety is irreducible (N = 1).** The vanishing ideal of (the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:217:/-! ## The headline — the determinantal-stratum dimension -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:219:/-- **The determinantal-stratum dimension (AG rung 1).** For `r ≤ n` and `r ≤ m`, over an
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:221:determinantal variety `Mat^{rk ≤ r}_{m × n}` (encoded as the `N = 1` product-rank locus
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:40:The base of the fibration is the rank-`≤ r` determinantal variety in the target matrices
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:44:irreducible determinantal variety) of Krull dimension `δ = r(n + m − r)`. From the LANDED thermometer
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:49:algebraically closed field of characteristic `0`, the coordinate ring of the rank-`≤ r` determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:90:irreducible determinantal base, with `ringKrullDim O(Mat^{≤r}) = δ`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean:22:determinantal chart localisation + the section-of-the-torsor trivialisation is a from-scratch
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:8:The localized determinantal base ring `A_loc = Localization.Away detΔ` of the rank-`≤ r` stratum, on
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:15:minor `detΔ` lives in the `SchurVar` block. The forced-block graph ideal then has height `C`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:107:minor `detΔ` is a polynomial in the `SchurVar` coordinates only. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:185:/-! ## The pivot minor `detΔ` lives in the `SchurVar` block
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:187:Under the block reindex `Φ = renameEquiv (repCoordReindex)`, the pivot minor `detΔ = detPivotPoly`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:198:/-- Under the reindex `renameEquiv (repCoordReindex)`, the pivot minor `detΔ` maps to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:223:/-- Under `blockAlgEquiv`, the pivot minor `detΔ` becomes the constant `C detSchurS`: it lives
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:239:`SchurVar` coefficient ring. These are the entry-images the bordered-minor identity uses. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:312:localized determinantal ideal `Iad` equals. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:9:The first explicit handle on the exact-rank determinantal locus (G2-1, foundation of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:10:determinantal-presentation build). Over a field `k`, on the **pivot chart** where the top-left
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:228:/-- **`δ` matches `r(p+q−r)`.** The three free-block coordinate counts sum to the determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitCodim.lean:18:   determinantal locus `{A | rankPattern A ≤ rankPattern M pointwise}`). Thm 3.8 is **PROVED in the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitCodim.lean:58:dimension theorems (catenary `dim R/I = n − ht I`, determinantal height, Nullstellensatz radical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitCodim.lean:76:determinantal subset of `Rep_d` cut out by the rank conditions on the interval sub-products. For the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Types/Products.lean:37:-- The increased `@[simp]` priority here results in a minor speed up in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:9:dimension of the determinantal rank locus `Z_M = canonicalCoord '' orbitRankLocus M` is identified
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimCornerMono.lean:19:  `(mult d M').rank`, with the SAME orbit rank locus (hence the same orbit ideal, the same geometric
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimCornerMono.lean:375:tuple `M'`; the Gabriel partition has corner `s = (mult M').rank ≤ r` and the same orbit ideal; the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimCornerMono.lean:389:  -- the Gabriel partition of `M'`: Kostant of corner `s = (mult M').rank ≤ r`, same orbit ideal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:244:  rw [Matrix.det_submatrix_equiv_self, Matrix.det_permute', abs_mul, abs_unit_intCast, one_mul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:446:integral in terms of suitable seminorms of `f`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Probability/Moments/Variance.lean:10:import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean:38:  of seminorms.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean:54:open Function Seminorm SeminormFamily Set TopologicalSpace UniformSpace
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:56:- `N[𝕜; F]_{K, n, i}` (or simply `N[𝕜]_{K, n, i}`): the `𝕜`-seminorm on `𝓓^{n}_{K}(E, F)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:58:- `N[𝕜; F]_{K, i}` (or simply `N[𝕜]_{K, i}`): the `𝕜`-seminorm on `𝓓_{K}(E, F)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:85:open TopologicalSpace Set Function UniformSpace WithSeminorms
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:607:/-- The seminorms on the space `𝓓^{n}_{K}(E, F)` given by the sup norm of the iterated derivatives.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:608:In the scope `Distributions.Seminorm`, we denote them by `N[𝕜; F]_{K, n, i}`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:610:protected noncomputable def seminorm (i : ℕ) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:611:  (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[ℝ] F))).comp (structureMapLM 𝕜 n i)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:613:-- Note: If these end up conflicting with other seminorms (e.g `SchwartzMap.seminorm`),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:615:@[inherit_doc ContDiffMapSupportedIn.seminorm]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:617:  ContDiffMapSupportedIn.seminorm 𝕜 _ _ n K i
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:619:@[inherit_doc ContDiffMapSupportedIn.seminorm]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:621:  ContDiffMapSupportedIn.seminorm 𝕜 _ _ ⊤ K i
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:623:@[inherit_doc ContDiffMapSupportedIn.seminorm]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:625:  ContDiffMapSupportedIn.seminorm 𝕜 _ F n K i
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:627:@[inherit_doc ContDiffMapSupportedIn.seminorm]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:629:  ContDiffMapSupportedIn.seminorm 𝕜 _ F ⊤ K i
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:631:/-- The seminorms on the space `𝓓^{n}_{K}(E, F)` given by sup of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:632:`ContDiffMapSupportedIn.seminorm k`for `k ≤ i`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:633:protected noncomputable def supSeminorm (i : ℕ) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:634:  (Finset.Iic i).sup (ContDiffMapSupportedIn.seminorm 𝕜 E F n K)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:636:protected theorem withSeminorms :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:637:    WithSeminorms (ContDiffMapSupportedIn.seminorm 𝕜 E F n K) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:638:  let p : SeminormFamily 𝕜 𝓓^{n}_{K}(E, F) ((_ : ℕ) × Fin 1) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:639:    SeminormFamily.sigma fun i _ ↦
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:640:      (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[ℝ] F))).comp (structureMapLM 𝕜 n i)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:641:  have : WithSeminorms p :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:642:    withSeminorms_iInf fun i ↦ LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:645:protected theorem withSeminorms' :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:646:    WithSeminorms (ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:647:  (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K).partial_sups
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:651:protected theorem seminorm_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:655:protected theorem seminorm_eq_bot_of_gt {i : ℕ} (hin : n < i) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:659:  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.ext_iff,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:662:protected theorem seminorm_le_iff {C : ℝ} (hC : 0 ≤ C) (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:670:  · simp [hi, forall_const, ContDiffMapSupportedIn.seminorm_apply, structureMapCLM_apply,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:673:    simp [hi, ContDiffMapSupportedIn.seminorm_eq_bot_of_gt _ hi, hC]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:675:protected theorem seminorm_top_le_iff {C : ℝ} (hC : 0 ≤ C) (i : ℕ) (f : 𝓓_{K}(E, F)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:677:  simp_rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 hC, le_top, forall_const]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:679:theorem norm_iteratedFDeriv_apply_le_seminorm {i : ℕ} (hin : i ≤ n)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:688:theorem norm_iteratedFDeriv_apply_le_seminorm_top {i : ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:691:  norm_iteratedFDeriv_apply_le_seminorm 𝕜 (mod_cast le_top)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:693:theorem norm_apply_le_seminorm {f : 𝓓^{n}_{K}(E, F)} {x : E} :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:696:  exact norm_iteratedFDeriv_apply_le_seminorm 𝕜 (zero_le _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:701:    ContDiffMapSupportedIn.seminorm_apply, structureMapCLM_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:708:    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:709:      (norm_withSeminorms 𝕜 _) _ (fun _ ↦ ⟨{0}, 1, fun f ↦ ?_⟩)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:729:theorem seminorm_postcompLM_le [LinearMap.CompatibleSMul F F' ℝ 𝕜] {i : ℕ} (T : F →L[𝕜] F')
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:734:  rw [ContDiffMapSupportedIn.seminorm_le_iff ℝ (by positivity)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:742:  _ ≤ ‖T'‖ * N[ℝ]_{K, n, i} f := by grw [norm_iteratedFDeriv_apply_le_seminorm ℝ hi]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:753:    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:754:      (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ⟨{i}, ‖T‖, fun f ↦ ?_⟩)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:755:    simpa using seminorm_postcompLM_le 𝕜 T f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:763:theorem seminorm_monoLM_le {i : ℕ} (f : 𝓓^{n₁}_{K₁}(E, F)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:766:  · simp (discharger := positivity) only [ContDiffMapSupportedIn.seminorm_le_iff, monoLM_apply, H,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:769:    exact norm_iteratedFDeriv_apply_le_seminorm _ (hik.trans (mod_cast H.1))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:772:theorem seminorm_monoLM_eq {i : ℕ} (h₁ : n₁ = n₂) (h₂ : K₁ ≤ K₂) (f : 𝓓^{n₁}_{K₁}(E, F)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:774:  simp [BoundedContinuousFunction.norm_eq_iSup_norm, ContDiffMapSupportedIn.seminorm_apply,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:792:    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:793:      (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _) _ (fun i ↦ ⟨{i}, 1, fun f ↦ ?_⟩)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:794:    simpa using seminorm_monoLM_le 𝕜 f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:811:theorem seminorm_fderivLM_le {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:814:  · rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 (apply_nonneg ..)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:818:      norm_iteratedFDeriv_apply_le_seminorm 𝕜 hi'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:821:theorem seminorm_fderivLM_top {i : ℕ} (f : 𝓓_{K}(E, F)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:823:  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.norm_eq_iSup_norm,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:834:    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:835:      (ContDiffMapSupportedIn.withSeminorms ..) _ (fun i ↦ ⟨{i+1}, 1, fun f ↦ ?_⟩)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:836:    simpa using seminorm_fderivLM_le 𝕜 f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:8:public import Mathlib.Analysis.LocallyConvex.WithSeminorms
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:26:We construct the topology on the Schwartz space by a family of seminorms, which are the best
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:28:`SeminormFamily.moduleFilterBasis` and `WithSeminorms.toLocallyConvexSpace` turns the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:35:* `SchwartzMap.seminorm`: The family of seminorms as described above
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:45:* `SchwartzMap.one_add_le_sup_seminorm_apply`: For a Schwartz function `f` there is a uniform bound
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:50:The implementation of the seminorms is taken almost literally from `ContinuousLinearMap.opNorm`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:203:section SeminormAux
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:205:/-- Helper definition for the seminorms of the Schwartz space. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:206:private protected def seminormAux (k n : ℕ) (f : 𝓢(E, F)) : ℝ :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:209:private theorem seminormAux_nonneg (k n : ℕ) (f : 𝓢(E, F)) : 0 ≤ f.seminormAux k n :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:212:private theorem le_seminormAux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:213:    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ f.seminormAux k n :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:217:private theorem seminormAux_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:218:    (hM : ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ M) : f.seminormAux k n ≤ M :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:221:end SeminormAux
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:235:        use f.seminormAux k n * ‖c‖
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:241:          _ ≤ SchwartzMap.seminormAux k n f * ‖c‖ := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:243:            apply f.le_seminormAux }⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:255:private theorem seminormAux_smul_le (k n : ℕ) (c : 𝕜) (f : 𝓢(E, F)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:256:    (c • f).seminormAux k n ≤ ‖c‖ * f.seminormAux k n := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:257:  refine (c • f).seminormAux_le_bound k n (mul_nonneg (norm_nonneg _) (seminormAux_nonneg _ _ _))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:260:  exact mul_le_mul_of_nonneg_left (f.le_seminormAux k n x) (norm_nonneg _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:297:private theorem seminormAux_zero (k n : ℕ) : (0 : 𝓢(E, F)).seminormAux k n = 0 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:298:  le_antisymm (seminormAux_le_bound k n _ rfl.le fun _ => by simp [Pi.zero_def])
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:299:    (seminormAux_nonneg _ _ _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:308:      use f.seminormAux k n
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:310:      grw [f.decay_neg_aux k n x, f.le_seminormAux k n x]⟩⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:322:      use f.seminormAux k n + g.seminormAux k n
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:324:      grw [decay_add_le_aux k n f g x, f.le_seminormAux k n x, g.le_seminormAux k n x]⟩⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:330:private theorem seminormAux_add_le (k n : ℕ) (f g : 𝓢(E, F)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:331:    (f + g).seminormAux k n ≤ f.seminormAux k n + g.seminormAux k n :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:332:  (f + g).seminormAux_le_bound k n
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:333:    (add_nonneg (seminormAux_nonneg _ _ _) (seminormAux_nonneg _ _ _)) fun x =>
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:335:      add_le_add (f.le_seminormAux k n x) (g.le_seminormAux k n x)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:345:      refine ⟨f.seminormAux k n + g.seminormAux k n, fun x => ?_⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:346:      grw [← f.le_seminormAux k n x, ← g.le_seminormAux k n x]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:399:section Seminorms
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:401:/-! ### Seminorms on Schwartz space -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:407:/-- The seminorms of the Schwartz space given by the best constants in the definition of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:410:protected def seminorm (k n : ℕ) : Seminorm 𝕜 𝓢(E, F) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:411:  Seminorm.ofSMulLE (SchwartzMap.seminormAux k n) (seminormAux_zero k n) (seminormAux_add_le k n)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:412:    (seminormAux_smul_le k n)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:414:/-- The seminorm is given by infimum over all `c` such that the estimate
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:417:Note that it is usually better to use `seminorm_le_bound` or `le_seminorm` instead of this lemma. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:418:theorem seminorm_apply {k n : ℕ} (f : 𝓢(E, F)) : SchwartzMap.seminorm 𝕜 k n f =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:421:/-- If one controls the seminorm for every `x`, then one controls the seminorm. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:422:theorem seminorm_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:423:    (hM : ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ M) : SchwartzMap.seminorm 𝕜 k n f ≤ M :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:424:  f.seminormAux_le_bound k n hMp hM
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:426:/-- If one controls the seminorm for every `x`, then one controls the seminorm.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:429:theorem seminorm_le_bound' (k n : ℕ) (f : 𝓢(ℝ, F)) {M : ℝ} (hMp : 0 ≤ M)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:430:    (hM : ∀ x, |x| ^ k * ‖iteratedDeriv n f x‖ ≤ M) : SchwartzMap.seminorm 𝕜 k n f ≤ M := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:431:  refine seminorm_le_bound 𝕜 k n f hMp ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:434:/-- The seminorm controls the Schwartz estimate for any fixed `x`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:435:theorem le_seminorm (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:436:    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ SchwartzMap.seminorm 𝕜 k n f :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:437:  f.le_seminormAux k n x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:439:/-- The seminorm controls the Schwartz estimate for any fixed `x`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:442:theorem le_seminorm' (k n : ℕ) (f : 𝓢(ℝ, F)) (x : ℝ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:443:    |x| ^ k * ‖iteratedDeriv n f x‖ ≤ SchwartzMap.seminorm 𝕜 k n f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:444:  have := le_seminorm 𝕜 k n f x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:447:theorem norm_iteratedFDeriv_le_seminorm (f : 𝓢(E, F)) (n : ℕ) (x₀ : E) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:448:    ‖iteratedFDeriv ℝ n f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 0 n) f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:449:  have := SchwartzMap.le_seminorm 𝕜 0 n f x₀
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:452:theorem norm_pow_mul_le_seminorm (f : 𝓢(E, F)) (k : ℕ) (x₀ : E) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:453:    ‖x₀‖ ^ k * ‖f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 k 0) f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:454:  have := SchwartzMap.le_seminorm 𝕜 k 0 f x₀
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:457:theorem norm_le_seminorm (f : 𝓢(E, F)) (x₀ : E) : ‖f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 0 0) f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:458:  have := norm_pow_mul_le_seminorm 𝕜 f 0 x₀
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:463:/-- The family of Schwartz seminorms. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:464:def _root_.schwartzSeminormFamily : SeminormFamily 𝕜 𝓢(E, F) (ℕ × ℕ) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:465:  fun m => SchwartzMap.seminorm 𝕜 m.1 m.2
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:468:theorem schwartzSeminormFamily_apply (n k : ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:469:    schwartzSeminormFamily 𝕜 E F (n, k) = SchwartzMap.seminorm 𝕜 n k :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:473:theorem schwartzSeminormFamily_apply_zero :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:474:    schwartzSeminormFamily 𝕜 E F 0 = SchwartzMap.seminorm 𝕜 0 0 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:479:/-- A more convenient version of `le_sup_seminorm_apply`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:483:theorem one_add_le_sup_seminorm_apply {m : ℕ × ℕ} {k n : ℕ} (hk : k ≤ m.1) (hn : n ≤ m.2)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:486:      2 ^ m.1 * (Finset.Iic m).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:498:  grw [le_seminorm 𝕜 i n f x]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:499:  apply Seminorm.le_def.1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:503:end Seminorms
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:514:  (schwartzSeminormFamily ℝ E F).moduleFilterBasis.topology'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:516:theorem _root_.schwartz_withSeminorms : WithSeminorms (schwartzSeminormFamily 𝕜 E F) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:517:  have A : WithSeminorms (schwartzSeminormFamily ℝ E F) := ⟨rfl⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:518:  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at A ⊢
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:525:  rw [(schwartz_withSeminorms 𝕜 E F).withSeminorms_eq]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:526:  exact (schwartzSeminormFamily 𝕜 E F).moduleFilterBasis.continuousSMul
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:529:  (schwartzSeminormFamily ℝ E F).addGroupFilterBasis.isTopologicalAddGroup
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:532:  (schwartzSeminormFamily ℝ E F).addGroupFilterBasis.uniformSpace
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:535:  (schwartzSeminormFamily ℝ E F).addGroupFilterBasis.isUniformAddGroup
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:538:  (schwartz_withSeminorms ℝ E F).toLocallyConvexSpace
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:541:  (schwartz_withSeminorms ℝ E F).firstCountableTopology
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:588:      ‖x‖ ^ n.fst * ‖iteratedFDeriv ℝ n.snd (A f) x‖ ≤ C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:596:        exact ⟨C * (s.sup (schwartzSeminormFamily 𝕜 D E)) f, h f⟩ }
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:608:      ‖x‖ ^ n.fst * ‖iteratedFDeriv ℝ n.snd (A f) x‖ ≤ C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:613:      WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms 𝕜 D E)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:614:        (schwartz_withSeminorms 𝕜' F G) _ fun n => ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:617:    exact (mkLM A hadd hsmul hsmooth hbound f).seminorm_le_bound 𝕜' n.1 n.2 (by positivity) (h f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:625:      ‖A f‖ ≤ C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:634:      apply WithSeminorms.continuous_normedSpace_rng G (schwartz_withSeminorms 𝕜 D E)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:653:  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:658:    _ ≤ ‖m‖ * SchwartzMap.seminorm 𝕜 k n f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:661:      apply le_seminorm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:721:  refine le_trans ?_ (one_add_le_sup_seminorm_apply le_rfl hi f x)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:889:        _ ≤ ‖L‖ * 1 * (SchwartzMap.seminorm 𝕜 (k + 1) n) f +
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:890:              ‖L‖ * n * (SchwartzMap.seminorm 𝕜 k (n - 1) f) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:891:          grw [le_opNorm, ← le_seminorm 𝕜 (k + 1) n f x, ← le_seminorm 𝕜 k (n - 1) f x]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:895:            max ((SchwartzMap.seminorm 𝕜 (k + 1) n) f) ((SchwartzMap.seminorm 𝕜 k (n - 1)) f) +
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:897:            max ((SchwartzMap.seminorm 𝕜 (k + 1) n) f) ((SchwartzMap.seminorm 𝕜 k (n - 1)) f) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:900:          simp only [Finset.sup_insert, schwartzSeminormFamily_apply, Finset.sup_singleton,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:901:            Seminorm.coe_sup, Pi.sup_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:934:  let seminorm_f := ((Finset.Iic (k', n)).sup (schwartzSeminormFamily 𝕜 _ _)) f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:945:      ‖iteratedFDeriv ℝ i f (g x)‖ ≤ 2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k' := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:949:    exact one_add_le_sup_seminorm_apply le_rfl hi _ _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:965:        (n ! * (2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k') * ((C + 1) * (1 + ‖x‖) ^ l) ^ n) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:967:        ((C + 1) ^ n * n ! * 2 ^ k' * seminorm_f) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1040:  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1050:    _ ≤ ‖L‖ * (SchwartzMap.seminorm 𝕜 k n) f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1051:      grw [le_seminorm 𝕜 k n f x]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1112:        (SchwartzMap.seminorm 𝕜 0 n f + SchwartzMap.seminorm 𝕜 (k + μ.integrablePower) n f) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1113:  integral_pow_mul_le_of_le_of_pow_mul_le (norm_iteratedFDeriv_le_seminorm ℝ _ _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1114:    (le_seminorm ℝ _ _ _)

exec
/bin/bash -lc 'rg -n "sigmaIdeal(_| ).*=|def sigmaIdeal|theorem .*sigmaIdeal.*span|minimalPrimes_sigmaIdeal|sigmaIdeal_eq_sInf|productRankLocusLE.*zeroLocus|vanishingIdeal_productRankLocusLE|rank.*det.*vanishing" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:145:  have hsig : (sigmaIdeal (k := k) d r).IsRadical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:231:    (sigmaIdeal (k := k) (dStratum (d 0) (d (Fin.last N))) r).map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:233:      ≤ sigmaIdeal (k := k) d r := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:300:  have hmem : deepBaseComap (k := k) d g ∈ sigmaIdeal (k := k) d r :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:19:  the aggregate ideal `sigmaIdeal d r := vanishingIdeal (canonicalCoord d '' Σ̄^r)` is the `sInf` of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:25:  worked `(2,2,2)`/`(2,3,2)` examples. The caveat is co-located at `minimalPrimes_sigmaIdeal_eq`.)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:130:noncomputable def sigmaIdeal (d : Fin (N + 1) → ℕ) (r : ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:137:theorem sigmaIdeal_eq_sInf_orbitIdeals (d : Fin (N + 1) → ℕ) (r : ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:138:    sigmaIdeal (k := k) d r = sInf (orbitIdeals (k := k) d r) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:167:order — the bridge that turns `minimalPrimes_sigmaIdeal_eq` into a statement about maximal `Ō_M`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:199:From the bridge `sigmaIdeal = sInf orbitIdeals` + the SPIKE (`minimalPrimes` of `sInf` of a finite
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:206:theorem minimalPrimes_sigmaIdeal_eq [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:207:    (sigmaIdeal (k := k) d r).minimalPrimes
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:209:  rw [sigmaIdeal_eq_sInf_orbitIdeals]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:216:`Ideal.minimalPrimes.equivIrreducibleComponents`, combined with `minimalPrimes_sigmaIdeal_eq`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:221:        ((sigmaIdeal (k := k) d r : Ideal (MvPolynomial (RepCoord d) k)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:223:  (OrderIso.setCongr _ _ (minimalPrimes_sigmaIdeal_eq d r).symm).trans
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:224:    (Ideal.minimalPrimes.equivIrreducibleComponents (sigmaIdeal (k := k) d r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:269:      ∈ (sigmaIdeal (k := k) d r).minimalPrimes := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:270:  rw [minimalPrimes_sigmaIdeal_eq]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:290:d222 0`; the bridge `sigmaIdeal = sInf orbitIdeals` and the G3 minimal-primes characterisation fire.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:317:    sigmaIdeal (k := AlgebraicClosure ℚ) dWitness 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:319:  sigmaIdeal_eq_sInf_orbitIdeals dWitness 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:324:    (sigmaIdeal (k := AlgebraicClosure ℚ) dWitness 0).minimalPrimes
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:327:  minimalPrimes_sigmaIdeal_eq dWitness 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CTheta.lean:35:components are the orbit closures (`Core.SigmaComponents.minimalPrimes_sigmaIdeal_eq`),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:164:    borderMinor (k := k) q p r hp hq a' b' ∈ sigmaIdeal (k := k) (dStratum q p) r := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:340:  haveI hsigmaPrime : (sigmaIdeal (k := k) (dStratum q p) r).IsPrime := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:341:    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:198:theorem isPrime_vanishingIdeal_productRankLocusLE_stratum [IsAlgClosed k] (n m r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:238:    (isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:63:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:100:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:91:  isPrime_vanishingIdeal_productRankLocusLE_stratum (d 0) (d (Fin.last N)) r hq hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:14:`r`: `sigmaIdeal d r = sInf (orbitIdeals d r)` and `minimalPrimes_sigmaIdeal_eq` (both general in `r`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:49:    codimRepCanonical (productRankLocusLE (k := k) d r) = (sigmaIdeal (k := k) d r).height :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:55:codimension of its irreducible components". General in `r`: `sigmaIdeal d r = sInf (orbitIdeals d r)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:56:and `minimalPrimes_sigmaIdeal_eq` are both general in `r` (`Core.SigmaComponents`). `[IsAlgClosed k]`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:69:    have hle : sigmaIdeal (k := k) d r
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:72:      rw [sigmaIdeal_eq_sInf_orbitIdeals]; exact sInf_le hmem
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:78:    calc ⨅ J ∈ (sigmaIdeal (k := k) d r).minimalPrimes,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:91:      ((minimalPrimes_sigmaIdeal_eq (k := k) d r) ▸ hJ).1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimCornerMono.lean:374:partition. From G3 (`minimalPrimes_sigmaIdeal_eq`) `p = vanishingIdeal (Ō_{M'})` for a corner-`≤ r`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimCornerMono.lean:386:  rw [topComponents, Set.mem_setOf_eq, minimalPrimes_sigmaIdeal_eq] at hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean:300:  {p | p ∈ (sigmaIdeal (k := k) d r).minimalPrimes ∧ p.height = (cCodim d r h).toNat}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaGeometric.lean:36:(`Core.SigmaComponents.minimalPrimes_sigmaIdeal_eq`); (iii) codimension-of-a-union =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:252:    ((Matrix.of (multPoly d)).submatrix br bc).det ∈ sigmaIdeal (k := k) d r := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:344:    detPivotPoly (k := k) q p r hp hq ∉ sigmaIdeal (k := k) (dStratum q p) r := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:360:(`height sigmaIdeal = cCodim = C`) it gives `height Iad = C`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:362:    ((sigmaIdeal (k := k) (dStratum q p) r).map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:365:      = (sigmaIdeal (k := k) (dStratum q p) r).height := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:366:  haveI hprime : (sigmaIdeal (k := k) (dStratum q p) r).IsPrime := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:367:    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:375:transport with engine Brick A (`height sigmaIdeal = cCodim ![q,p] r`). Over an algebraically closed
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:381:    ((sigmaIdeal (k := k) (dStratum q p) r).map

exec
/bin/bash -lc 'rg -n "height_strict_mono_of_is_prime|eq_of_le_of_not_lt|IsPrime.*height|height.*prime.*equal|catenary|principal ideal theorem|equidimensional|unmixed|same height|minimalPrimes.*height" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:5:then `Q` and the prime `Q.under R` it lies over have the same height: the fibre over
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:33:same minimal primes (`Ideal.radical_minimalPrimes`), and `Ideal.height` is the infimum of the prime
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:30:  additive half of the catenary content (the `≥` direction), proved unconditionally from the flat
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:34:(`primeHeight_add_ringKrullDim_quotient_le`). The catenary `≥` direction `height p ≥ n − dim(R/p)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:101:/-! ### The polynomial-tower additive brick (the `≥`/catenary additive half) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:108:the catenary content for polynomial rings. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:117:  refine congr_arg c (eq_of_le_of_not_lt' ?_ fun hi => ?_)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:15:  field `S/q` — Zariski's lemma), so `p.height = n` by the affine-space catenary equality
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:94:height exactly `n`: `B/(q.comap g)` is zero-dimensional, so the affine-space catenary equality
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean:300:  {p | p ∈ (sigmaIdeal (k := k) d r).minimalPrimes ∧ p.height = (cCodim d r h).toNat}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:22:reducible-locus catenary `Core.RadicalCatenary` (true for any nonempty subset of affine space),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:44:identity `hSweep`, the Cited closure bridge `hClosure`, and the two reducible-locus catenary
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:94:/-! ## The catenary hypotheses discharged (only the sweep + closure remain) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:96:/-- **Route-c assembly with the catenary hypotheses discharged.** For a rank-`r` target `B`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:99:hypotheses — the two reducible-locus catenary relations are now **proved** from
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Noetherian/Defs.lean:148:    rw [eq_of_le_of_not_lt (le_sup_right : N₀ ≤ _) (h₂
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:13:The catenary `≥` direction for `MvPolynomial (Fin n) k` (`k` any field) needs a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:238:/-! ### The catenary `≥` direction and the full L5.7 equality -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:241:/-- Induction core for the catenary `≥` direction: for every prime `p` of `k[x₁,…,xₙ]`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:335:`Ideal.height p + ringKrullDim (R ⧸ p) = n`. The catenary identity for affine space — `R` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:336:equidimensional, so height and coheight are exactly complementary. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:377:example (p : Ideal (MvPolynomial (Fin 2) ℚ)) [p.IsPrime] (hp : p.height = 1) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:50:/-! ## GAP 3 — L4d over a `Fintype` index (equidimensionality at the orbit point) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:52:/-- **GAP 3 — equidimensionality at a closed point, `Fintype`-indexed.** For `A = MvPolynomial σ k ⧸ I`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:86:and the equidimensionality `height_eq_ringKrullDim_of_isMaximal_fintype`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:274:map between equidimensional finite spaces, via `LinearEquiv.ofBijective`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:18:* `hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height` — every component has codim `≥ v`;
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:19:* `hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v` — one (top) component has codim `≤ v`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:25:(`SmoothLocalRelativeDimension`) + the catenary `height P + dim(R⧸P) = card` — and the full identity
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:47:    (hge : ∀ J ∈ I.minimalPrimes, v ≤ J.height)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:48:    (hle : ∃ J ∈ I.minimalPrimes, J.height ≤ v) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:66:theorem codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds [IsAlgClosed k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:68:    (hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:69:    (hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:79:codimension is `C + δ`. `codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds` at `v := C + δ`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:81:+ `= C+δ` (top component), via H3a + generic smoothness + the catenary. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:91:  codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds d B _ hge hle
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:108:    (hge : ∀ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, v ≤ J.height)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:109:    (hle : ∃ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, J.height ≤ v) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:112:  exact codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds d Bstar v hge hle
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:266:has the same height `C` as `sigmaIdeal`: localizing at `detΔ` (not in the prime `sigmaIdeal`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:356:/-- **Step (b₀): the localized base ideal has the same height as the base ideal.** Localizing the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:7:# `DLNFibre.Core.RadicalCatenary` — the catenary identity for a reducible (radical) locus
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:9:The prime catenary `height p + ringKrullDim (R ⧸ p) = card` (`Core.NullstellensatzCodim`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:16:and dimension `= max` component dimension, and the polynomial ring is catenary, so the two are dual.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:22:  dim (R ⧸ p)`, while `height I ≤ height p`, and the per-prime catenary closes `≤ card`;
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:25:  catenary for `p₀` reads `card = height I + dim (R ⧸ p₀) ≤ height I + dim (R ⧸ I)`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:29:discharging the reducible-locus catenary that `Core.RouteCAssembly` carries as the named hypotheses
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:46:minimal prime `p ∈ I.minimalPrimes` has `p.height = I.height`. The infimum `I.height = ⨅_{p}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:50:    ∃ p ∈ I.minimalPrimes, p.height = I.height := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:62:    have : @Ideal.primeHeight _ _ J (Ideal.minimalPrimes_isPrime hJ) = J.height :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:112:/-! ## The radical-locus catenary -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:114:/-- **The reducible-locus catenary.** For `R = MvPolynomial σ k` (`σ` finite, `k` any field) and a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:115:proper ideal `I ≠ ⊤`, `height I + ringKrullDim (R ⧸ I) = Nat.card σ` — the per-prime catenary
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:123:  -- the per-prime catenary, restated as `dim (R ⧸ p) = card − height p` in the additive form.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:150:    -- the per-prime catenary for `p₀`, with `height p₀ = height I`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:177:irreducibility hypothesis — the reducible-locus catenary converted to `ℕ∞` (the quotient is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:203:The reducible-locus catenary at `codimRepCanonical`/`varietyDim` fires on the whole space `univ`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:12:`MvPolynomial τ k` (dimension `Nat.card τ`), so by the field catenary
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:21:`Core.NullstellensatzCodim` (the field catenary `height_add_ringKrullDim_quotient_eq_card`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:46:of `aeval c`, eliminating the `σ`-block) has height `Nat.card σ`. The catenary identity
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:53:  -- transport to the field ring `MvPolynomial (σ ⊕ τ) k` to apply the field catenary
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:69:  -- the field catenary on `MvPolynomial (σ ⊕ τ) k`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:72:  -- drop `WithBot` to the `ℕ∞` catenary `height + #τ = #σ + #τ`, then cancel (landed pattern)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:55:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:62:/-- LANDED: affine-domain equidimensionality (NO flatness) — `height p + dim(A/p) = dim A`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:29:  (`orbitRankLocus_minCodim_mem_minimalPrimes`), via the strict drop of `Ideal.height` under proper
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:231:(`Ideal.height_strict_mono_of_is_prime`): a non-maximal `Ō_M` sits strictly inside another corner
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:262:(`Ideal.height_strict_mono_of_is_prime`) forces `codim Ō_M' < codim Ō_M`, contradicting minimality.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:279:    have hstrict := Ideal.height_strict_mono_of_is_prime (R := MvPolynomial (RepCoord d) k) hlt
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:226:Proof: the catenary bridge `codim + dim = card = m·n` (primality, Brick 1) with the LANDED codim
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:236:  -- catenary bridge: `codim + dim = card`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:82:By equidimensionality at a closed point (`OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:89:vanishingIdeal(…)` has height `δ = r(n + m − r)` — equidimensionality at a closed point of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:104:/-! ## Affine-domain equidimensionality over a `Fintype` coordinate index
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:109:nested catenary `height P = height Q + height_{R/Q}(P/Q)` (the `+C` composition for the easy
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:112:/-- **Affine-domain equidimensionality, finite index.** For `σ` finite, `I` a prime of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:24:3. **`Iad = J`** — by `Ideal.height_strict_mono_of_is_prime` (both prime, `height Ψ(Iad) = height
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:324:(step 2). `Ideal.height_strict_mono_of_is_prime` rules out `J ⊊ Ψ(Iad)`, so `J = Ψ(Iad)` — this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:330:plus `height_strict_mono_of_is_prime` forces equality. This is the honest hard direction. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:367:  refine (eq_of_le_of_not_lt (graphIdeal_forcedB22_le_map_Iad q p r hp hq) (fun hlt ↦ ?_)).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:370:  exact absurd ((Ideal.height_strict_mono_of_is_prime hlt).trans_le hJK.ge)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:13:of `Z` (the Krull dimension of its coordinate ring) via the catenary identity for affine space.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:15:The catenary dimension formula `Ideal.height p + ringKrullDim (R ⧸ p) = n` for `R = MvPolynomial
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:103:/-! ## Finite-index dimension transport: the catenary identity over a `Fintype` index -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:111:/-- **The catenary identity over a `Fintype` index (`WithBot ℕ∞` form).** For a prime `p` of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:143:`(vanishingIdeal Z).IsPrime` — the height of its vanishing ideal plus its variety dimension equals
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:145:catenary identity over `σ`, read at the prime `vanishingIdeal Z`. Geometric codimension `=` ambient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/PID.lean:39:  apply eq_of_le_of_not_lt ?_ fun h' ↦ h ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:13:# Affine-domain dimension formula / equidimensionality (network-free engine)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:15:The **L4d** layer: lift the polynomial-ring catenary equality
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:20:    `Ideal.height p + ringKrullDim (A ⧸ p) = ringKrullDim A`  (equidimensionality).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:23:  (equidimensionality at closed points).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:29:## Route — Noether normalization + integral height transport (reusing L5, no catenary re-induction)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:37:domain (`@[stacks 00H8]`) via `Ideal.exists_ltSeries_of_hasGoingDown`. No new catenary induction is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:38:needed — the polynomial-ring catenary content is L5, reused as a black box.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:108:/-- **Affine-domain dimension formula (equidimensionality).** For `R = MvPolynomial (Fin n) k`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:112:polynomial-ring catenary equality on the base. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:154:/-! ### The maximal-ideal corollary (equidimensionality at closed points) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitCodim.lean:58:dimension theorems (catenary `dim R/I = n − ht I`, determinantal height, Nullstellensatz radical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:130:    {p : Ideal R} [p.IsPrime] (h : p.height = ringKrullDim R) (hp : r ∈ p) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:45:lemma Ideal.height_eq_primeHeight [I.IsPrime] : I.height = I.primeHeight := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:125:lemma Ideal.height_strict_mono_of_is_prime {I J : Ideal R} [I.IsPrime]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:177:lemma Ideal.mem_minimalPrimes_of_height_eq {I J : Ideal R} (e : I ≤ J) [J.IsPrime]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:181:  refine (eq_of_le_of_not_lt h₂ fun h₃ ↦ ?_).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:185:     ((height_strict_mono_of_is_prime h₃).trans_le (e'.trans <| height_mono h₁.1.2))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:248:    p.height ≤ n ↔ ∀ q : Ideal R, q.IsPrime → q < p → q.height < n := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:257:      (∀ q' : Ideal R, q'.IsPrime → q < q' → ¬ q' < p) → q.height < n := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:270:    (p : Ideal S) [p.IsPrime] : (p.comap e).height = p.height := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:295:    ringKrullDim R ≤ n ↔ ∀ ⦃p : Ideal R⦄, p.IsPrime → p.height ≤ n := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:357:lemma mem_minimalPrimes_of_primeHeight_eq_height {I J : Ideal R} [J.IsPrime] (e : I ≤ J)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:360:  exact mem_minimalPrimes_of_height_eq e (e' ▸ le_refl _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:371:    let S := { K | K ∈ J.minimalPrimes ∧ Ideal.height K = r }
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:411:        refine ⟨mem_minimalPrimes_of_primeHeight_eq_height (le_sup_left.trans hp.1.2) this.symm, ?_⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:18:In this file, we prove **Krull's principal ideal theorem** (also known as
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:25:  **Krull's principal ideal theorem** (also known as **Krullscher Hauptidealsatz**), which states
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:104:/-- **Krull's principal ideal theorem** (also known as **Krullscher Hauptidealsatz**) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:108:    (I : Ideal R) [I.IsPrincipal] (p : Ideal R) (hp : p ∈ I.minimalPrimes) : p.height ≤ 1 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:118:    (hp : p ∈ (I ⊔ span {x}).minimalPrimes) : (p.map (Ideal.Quotient.mk I)).height ≤ 1 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:290:    refine ⟨I, Ideal.mem_minimalPrimes_of_height_eq hI e₂.ge, e₁.symm ▸ ?_⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:300:    ∃ s : Finset R, p ∈ (span s).minimalPrimes ∧ s.card = p.height := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:301:  obtain ⟨I, hI, hr⟩ := (p.height_le_iff_exists_minimalPrimes <| p.height).mp le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/GoingDown.lean:67:  have : P = Q := eq_of_le_of_not_lt hPQ hc
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Valuation/RankOne.lean:109:  refine (eq_of_le_of_not_lt (zero_le' (a := x)) fun h_lt ↦ ?_).symm

codex
A subtle correction emerged: `schurToSred` is too late for gauging `IadDeep`; it lands in the quotient. For the pre-quotient ideal action, the gauge has to live on the total localized ambient ring, with entries interpreted there before passing to `Sred`.
exec
/bin/bash -lc 'rg -n "blockAlgEquivLoc|SchurLoc|include|algebraMap.*SchurLoc|to.*Schur|schur.*base|forcedB22|B22block|block.*Loc|coord.*Schur|detSchurS" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:9:the pivot chart, eliminates the bottom-right `B22` block: the Schur relation forces
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:13:along the block split `RepCoord ≃ B22block ⊕ SchurVar` (`B22block = Fin (p−r) × Fin (q−r)`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:14:`#B22block = (p−r)(q−r) = C`; `SchurVar = Δ ⊕ B12 ⊕ B21`, `#SchurVar = r(p+q−r) = δ`), so the pivot
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:30:/-- The eliminated `B22` block: bottom-right `(p−r) × (q−r)` matrix coordinates. `#B22block = C`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:31:abbrev B22block (q p r : ℕ) : Type := Fin (p - r) × Fin (q - r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:34:`r × (q−r)` block `B12`, the bottom-left `(p−r) × r` block `B21`. `#SchurVar = δ = r(p+q−r)`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:38:/-- `#B22block = (p − r)(q − r) = C`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:39:theorem card_B22block (q p r : ℕ) : Nat.card (B22block q p r) = (p - r) * (q - r) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:40:  simp [B22block, Nat.card_eq_fintype_card]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:54:/-- The block reindex of the four products `(Δ ⊕ B12) ⊕ (B21 ⊕ B22)` into `B22block ⊕ SchurVar`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:59:      ≃ B22block q p r ⊕ SchurVar q p r where
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:85:/-- The full block reindex `RepCoord (dStratum q p) ≃ B22block ⊕ SchurVar`. Drops the `Σ _ : Fin 1`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:89:    RepCoord (dStratum q p) ≃ B22block q p r ⊕ SchurVar q p r :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:106:maps under the reindex into the `Δ`-block of `SchurVar`: `Sum.inr (Sum.inl (i, j))`. So the pivot
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:119:maps under the reindex to the outer `B22block`: `Sum.inl (a, b)`. So the `B22` entries become the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:134:/-- A `B12` coordinate (pivot row `i`, non-pivot column `b`) maps to the `B12`-block of `SchurVar`:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:148:/-- A `B21` coordinate (non-pivot row `a`, pivot column `i`) maps to the `B21`-block of `SchurVar`:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:188:maps to `rename Sum.inr detSchurS` — a polynomial in the `SchurVar` (specifically `Δ`) coordinates
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:189:only. Pushing further through `sumAlgEquiv` (with `B22block` outermost), `detΔ` becomes the constant
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:190:`C detSchurS`, so localizing `A_eng` at `detΔ` is localizing the coefficient ring at `detSchurS`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:195:noncomputable def detSchurS (q p r : ℕ) : MvPolynomial (SchurVar q p r) k :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:199:`rename Sum.inr (detSchurS)`: it is a polynomial in the `SchurVar` coordinates only. (`det` commutes
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:204:      = rename Sum.inr (detSchurS (k := k) q p r) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:205:  rw [detPivotPoly, detSchurS, AlgEquiv.map_det, AlgHom.map_det (rename Sum.inr)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:215:`A_eng ≃ₐ[k] MvPolynomial B22block (MvPolynomial SchurVar k)`: relabel the coordinates
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:216:(`renameEquiv (repCoordReindex)`) then split off the `B22` block (`sumAlgEquiv`, `B22block`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:220:      ≃ₐ[k] MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:223:/-- Under `blockAlgEquiv`, the pivot minor `detΔ` becomes the constant `C detSchurS`: it lives
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:225:So localizing `A_eng` at `detΔ` corresponds to localizing the `SchurVar` coefficient ring at
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:226:`detSchurS`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:229:      = C (detSchurS (k := k) q p r) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:231:  have h := sumAlgEquiv_comp_rename_inr (R := k) (S₁ := B22block q p r) (S₂ := SchurVar q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:232:  have hs := congrArg (fun f ↦ f (detSchurS (k := k) q p r)) h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:274:/-- `detSchurS ≠ 0`: it is the determinant of the generic `Δ`-coordinate matrix (a renamed
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:275:`mvPolynomialX`), nonzero by `det_mvPolynomialX_ne_zero`. So `Sd = Localization.Away detSchurS` is a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:276:nontrivial localization (a domain), and `detSchurS` is a valid localization element. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:277:theorem detSchurS_ne_zero (q p r : ℕ) : detSchurS (k := k) q p r ≠ 0 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:278:  rw [detSchurS]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:296:`Sd = Localization.Away detSchurS`: `forcedB22 a b = (B21 · adjugate Δ · B12)_{ab} / detSchurS`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:298:graphIdeal forcedB22` of `MvPolynomial B22block Sd` has height `(p−r)(q−r) = C` — the lower bound
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:310:/-- The forced `B22` value in `Sd = Localization.Away detSchurS`: the Schur numerator divided by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:311:`detSchurS` (`= B21 Δ⁻¹ B12` once the pivot det is inverted). The graph map whose ideal `J` the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:313:noncomputable def forcedB22 (q p r : ℕ) (Sd : Type u) [CommRing Sd]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:315:    [IsLocalization.Away (detSchurS (k := k) q p r) Sd] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:316:    B22block q p r → Sd :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:318:    (⟨detSchurS q p r, Submonoid.mem_powers _⟩ : Submonoid.powers (detSchurS (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:320:/-- **`height J = C`** for the forced Schur graph ideal `J = graphIdeal forcedB22` in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:321:`MvPolynomial B22block Sd`: it eliminates the `B22` block, so its height is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:322:`#B22block = (p−r)(q−r) = C` (`height_graphIdeal_localization_eq` at `Sd = Localization.Away
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:323:detSchurS`, `detSchurS ≠ 0`). The lower bound the `Iad = J` squeeze needs. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:324:theorem height_graphIdeal_forcedB22_eq (q p r : ℕ) (Sd : Type u) [CommRing Sd]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:326:    [IsLocalization.Away (detSchurS (k := k) q p r) Sd] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:327:    (graphIdeal (forcedB22 (k := k) q p r Sd)).height = ((p - r) * (q - r) : ℕ) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:328:  rw [height_graphIdeal_localization_eq (k := k) (detSchurS q p r) (detSchurS_ne_zero q p r) Sd,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:329:    card_B22block]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:11:detSchurS`) — a regular ring of dimension `δ`. The eliminated `B22` block (`B22 = B21 Δ⁻¹ B12`) is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:15:`Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd` (localizing the LANDED `blockAlgEquiv` at `detΔ ↦
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:16:C detSchurS`) carries `Iad` to a prime of `MvPolynomial B22block Sd`. The forced-block graph ideal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:17:`J = graphIdeal forcedB22` (the genuine forced value `B21 adjΔ B12 / detΔ ∈ Sd`) satisfies:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:20:   is `#B22block = C` (LANDED `height_coordIdeal_localization_eq`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:21:2. **`J ⊆ Ψ(Iad)`** — each generator `X_b − C(forcedB22 b)` is, up to the unit `C detSchurS`, the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:28:Then `A_loc/Iad ≅ (MvPolynomial B22block Sd)/J ≅ Sd` via `graphIdealQuotientEquiv`. `J` stays
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:46:`Sd := Localization.Away detSchurS`, `Q := MvPolynomial B22block Sd`. We use `Localization` (the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:49:/-- The free Schur localization `Sd = Localization.Away detSchurS` — the downstream-composable base
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:51:abbrev SchurLoc (q p r : ℕ) : Type u :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:52:  Localization.Away (detSchurS (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:54:/-- **The localized block equivalence** `Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd`, localizing the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:55:LANDED `blockAlgEquiv` at `detΔ` (which maps to `C detSchurS`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:56:noncomputable def blockAlgEquivLoc (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:58:      ≃ₐ[k] MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:60:  haveI tower : IsScalarTower k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:61:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:63:    have hkB : (algebraMap k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))) x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:66:        (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))]; rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:67:    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:68:        = C (algebraMap k (SchurLoc (k := k) q p r) x) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:69:      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:70:        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:73:  -- `Q` is the localization of `B` at `powers (C detSchurS)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:74:  haveI hloc : IsLocalization (Submonoid.powers (C (detSchurS (k := k) q p r) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:75:      MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:76:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:78:      (MvPolynomial.isLocalization (σ := B22block q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:79:        (M := Submonoid.powers (detSchurS (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:80:        (S := SchurLoc (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:83:      = Submonoid.powers (C (detSchurS (k := k) q p r)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:87:    (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:94:`blockAlgEquiv` becomes `C detSchurS · X (a', b') − C (forcedNum a' b')` (the bordered Schur minor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:95:identity, transported). Dividing by the unit `C detSchurS` lands `X (a', b') − C (forcedB22 …)` in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:122:/-- The `SchurVar`-side pivot block `ΔS` (whose determinant is `detSchurS`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:171:/-- Each bordered block maps under `blockAlgEquiv` to the `C`-image of its `SchurVar`-side block
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:200:      = Matrix.of fun _ _ : Unit ↦ (X (a', b') : MvPolynomial (B22block q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:206:/-- The numerator bridge: the bordered Schur numerator (row `a'` of `B21`, `adjugate Δ`, column `b'`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:216:C detSchurS · X (a', b') − C (forcedNum a' b')`. Via `AlgEquiv.map_det` + `Matrix.fromBlocks_map` +
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:217:`det_fromBlocks_scalar_eq` on the mapped (`SchurVar`-`C`) blocks; `det (ΔS.map C) = C detSchurS`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:222:      = C (detSchurS (k := k) q p r) * X (a', b') - C ((forcedNum (k := k) q p r) a' b') := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:226:    show ((schurΔ (k := k) q p r).map C).det = C (detSchurS (k := k) q p r) from
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:235:(`algEquivOfAlgEquiv_eq`). Each generator `X (a',b') − C (forcedB22 (a',b'))` of `J`, multiplied by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:236:the unit `C (algebraMap detSchurS)`, is the `Ψ`-image of the bordered minor (in `Iad`), so it
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:240:(blockAlgEquiv x)`. (`Ψ = IsLocalization.algEquivOfAlgEquiv blockAlgEquiv`.) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:241:theorem blockAlgEquivLoc_algebraMap (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:243:    blockAlgEquivLoc (k := k) q p r hp hq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:246:      = algebraMap (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:247:          (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:249:  haveI tower : IsScalarTower k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:250:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:252:    have hkB : (algebraMap k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))) y
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:255:        (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))]; rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:256:    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) y
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:257:        = C (algebraMap k (SchurLoc (k := k) q p r) y) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:258:      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:259:        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:261:  haveI hloc : IsLocalization (Submonoid.powers (C (detSchurS (k := k) q p r) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:262:      MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:263:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:265:      (MvPolynomial.isLocalization (σ := B22block q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:266:        (M := Submonoid.powers (detSchurS (k := k) q p r)) (S := SchurLoc (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:277:/-- **The cleared Schur relation in `Q = MvPolynomial B22block Sd`.** The unit `C (algebraMap
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:278:detSchurS)` times the graph generator `X (a',b') − C (forcedB22 (a',b'))` equals
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:280:`Ψ(Iad)`). The `mk'` denominator clears: `algebraMap detSchurS · forcedB22 = algebraMap
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:284:    C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:285:          (detSchurS (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:286:        * (X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b')))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:287:      = blockAlgEquivLoc (k := k) q p r hp hq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:291:  rw [blockAlgEquivLoc_algebraMap, blockAlgEquiv_borderMinor, map_sub, map_mul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:297:  rw [forcedB22,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:298:    IsLocalization.mk'_spec' (SchurLoc (k := k) q p r) ((forcedNum (k := k) q p r) a' b')
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:299:      (⟨detSchurS q p r, Submonoid.mem_powers _⟩ : Submonoid.powers (detSchurS (k := k) q p r))]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:301:/-- **Step (2): `J ⊆ Ψ(Iad)`.** Each generator `X (a',b') − C (forcedB22 (a',b'))` of the forced
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:302:graph ideal lies in `Ψ(Iad)`: it is the unit `C (algebraMap detSchurS)⁻¹` times the `Ψ`-image of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:304:theorem graphIdeal_forcedB22_le_map_Iad (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:305:    graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:306:      ≤ ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:310:  show X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b'))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:311:      ∈ ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:312:  -- the generator × the unit `C (algebraMap detSchurS)` is `Ψ (algebraMap borderMinor) ∈ Ψ(Iad)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:313:  have hunit : IsUnit (C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:314:      (detSchurS (k := k) q p r)) : MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:315:    (IsLocalization.Away.algebraMap_isUnit (detSchurS (k := k) q p r)).map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:316:      (C : SchurLoc (k := k) q p r →+* _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:323:Both `Ψ(Iad)` and `J = graphIdeal forcedB22` are prime of height `C`, and `J ⊆ Ψ(Iad)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:331:theorem map_Iad_eq_graphIdeal_forcedB22 [IsAlgClosed k] [CharZero k] (q p r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:333:    ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:334:      = graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:335:  set Q := MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:337:    ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq) with hK
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:338:  set J : Ideal Q := graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) with hJ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:350:  haveI hKprime : K.IsPrime := Ideal.map_isPrime_of_equiv (blockAlgEquivLoc (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:351:  haveI : IsDomain (SchurLoc (k := k) q p r) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:352:    IsLocalization.isDomain_of_le_nonZeroDivisors (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:353:      (powers_le_nonZeroDivisors_of_noZeroDivisors (detSchurS_ne_zero (k := k) q p r))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:357:    height_map_algEquiv (blockAlgEquivLoc (k := k) q p r hp hq) ((Iad (k := k) q p r hp hq))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:363:    height_graphIdeal_forcedB22_eq q p r (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:367:  refine (eq_of_le_of_not_lt (graphIdeal_forcedB22_le_map_Iad q p r hp hq) (fun hlt ↦ ?_)).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:375:the free Schur localization `Sd = Localization.Away detSchurS` — a regular ring of dimension `δ`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:376:Via the height squeeze `Ψ(Iad) = J` (`map_Iad_eq_graphIdeal_forcedB22`) and the graph-ideal quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:381:      ≃ₐ[k] SchurLoc (k := k) q p r := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:383:      ≃ₐ[k] (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:384:        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:386:      (graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:387:      (blockAlgEquivLoc (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:388:      (map_Iad_eq_graphIdeal_forcedB22 q p r hp hq).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:389:  have e₂ : (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:390:        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:391:      ≃ₐ[k] SchurLoc (k := k) q p r :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:392:    (graphIdealQuotientEquiv (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))).restrictScalars k
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:397:The `2 × 2` rank-`≤ 1` determinantal base: `#B22block = (2−1)(2−1) = 1 = C` eliminated coordinate,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:401:/-- **Witness (`2 × 2`, `r = 1`).** `#B22block = 1 = C` (one eliminated `B22` coordinate),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:403:example : Nat.card (B22block 2 2 1) = 1 ∧ Nat.card (SchurVar 2 2 1) = 3 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:405:  · rw [card_B22block]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:413:      ≃ₐ[k] SchurLoc (k := k) 2 2 1 :=

exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.DeterminantalChartRing
import DLNFibre.Core.GraphIdealHeight
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# `DLNFibre.Core.DeterminantalBaseElimination` — the localized base presentation (`Iad = J`)

The localized determinantal base ring `A_loc = Localization.Away detΔ` of the rank-`≤ r` stratum, on
the pivot chart, eliminates the bottom-right `B22` block: the Schur relation forces
`B22 = B21 Δ⁻¹ B12`, so the localized base ideal `Iad` is the graph ideal `J` of that forced value.

This module reindexes the engine coordinate ring `A_eng = MvPolynomial (RepCoord (dStratum q p)) k`
along the block split `RepCoord ≃ B22block ⊕ SchurVar` (`B22block = Fin (p−r) × Fin (q−r)`,
`#B22block = (p−r)(q−r) = C`; `SchurVar = Δ ⊕ B12 ⊕ B21`, `#SchurVar = r(p+q−r) = δ`), so the pivot
minor `detΔ` lives in the `SchurVar` block. The forced-block graph ideal then has height `C`
(`Core.GraphIdealHeight`), which — with the LANDED `height Iad = C` and `J ⊆ Iad` — squeezes
`Iad = J` and exhibits `A_loc ⧸ Iad` as the free Schur localization (regular of dimension `δ`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

/-! ## The block coordinate types and the reindex equivalence -/

/-- The eliminated `B22` block: bottom-right `(p−r) × (q−r)` matrix coordinates. `#B22block = C`. -/
abbrev B22block (q p r : ℕ) : Type := Fin (p - r) × Fin (q - r)

/-- The free Schur coordinates `Δ ⊕ B12 ⊕ B21`: the top-left `r×r` pivot block `Δ`, the top-right
`r × (q−r)` block `B12`, the bottom-left `(p−r) × r` block `B21`. `#SchurVar = δ = r(p+q−r)`. -/
abbrev SchurVar (q p r : ℕ) : Type :=
  (Fin r × Fin r) ⊕ ((Fin r × Fin (q - r)) ⊕ (Fin (p - r) × Fin r))

/-- `#B22block = (p − r)(q − r) = C`. -/
theorem card_B22block (q p r : ℕ) : Nat.card (B22block q p r) = (p - r) * (q - r) := by
  simp [B22block, Nat.card_eq_fintype_card]

/-- `#SchurVar = r·r + (r·(q−r) + (p−r)·r) = r(p + q − r) = δ` (for `r ≤ p`, `r ≤ q`). -/
theorem card_SchurVar (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Nat.card (SchurVar q p r) = r * (p + q - r) := by
  simp only [SchurVar, Nat.card_eq_fintype_card, Fintype.card_fin,
    Fintype.card_prod, Fintype.card_sum]
  -- r*r + (r*(q−r) + (p−r)*r) = r(p+q−r), via `q = r+b`, `p = r+a`
  obtain ⟨a, rfl⟩ := Nat.le.dest hp
  obtain ⟨b, rfl⟩ := Nat.le.dest hq
  rw [show r + a + (r + b) - r = r + a + b by omega, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel_left]
  ring

/-- The block reindex of the four products `(Δ ⊕ B12) ⊕ (B21 ⊕ B22)` into `B22block ⊕ SchurVar`
(B22 outermost for the elimination; `SchurVar = Δ ⊕ (B12 ⊕ B21)`). -/
def blockRearrange (q p r : ℕ) :
    (((Fin r × Fin r) ⊕ (Fin r × Fin (q - r))) ⊕
        ((Fin (p - r) × Fin r) ⊕ (Fin (p - r) × Fin (q - r))))
      ≃ B22block q p r ⊕ SchurVar q p r where
  toFun := fun x ↦ match x with
    | .inl (.inl d) => .inr (.inl d)
    | .inl (.inr b12) => .inr (.inr (.inl b12))
    | .inr (.inl b21) => .inr (.inr (.inr b21))
    | .inr (.inr b22) => .inl b22
  invFun := fun x ↦ match x with
    | .inr (.inl d) => .inl (.inl d)
    | .inr (.inr (.inl b12)) => .inl (.inr b12)
    | .inr (.inr (.inr b21)) => .inr (.inl b21)
    | .inl b22 => .inr (.inr b22)
  left_inv := by rintro (⟨d|b12⟩|⟨b21|b22⟩) <;> rfl
  right_inv := by rintro (b22|⟨d|⟨b12|b21⟩⟩) <;> rfl

/-- The pivot split `Fin n ≃ Fin r ⊕ Fin (n−r)` (first `r` ↦ left). -/
def finSplit {n r : ℕ} (h : r ≤ n) : Fin n ≃ Fin r ⊕ Fin (n - r) :=
  (finCongr (show n = r + (n - r) by omega)).trans finSumFinEquiv.symm

/-- `finSplit` sends a pivot index `castLE i` (`i < r`) to `Sum.inl i`. -/
@[simp] theorem finSplit_castLE {n r : ℕ} (h : r ≤ n) (i : Fin r) :
    finSplit h (Fin.castLE h i) = Sum.inl i := by
  rw [finSplit, Equiv.trans_apply,
    show (finCongr (show n = r + (n - r) by omega)) (Fin.castLE h i) = Fin.castAdd (n - r) i from by
      apply Fin.ext; simp [finCongr, Fin.castLE, Fin.castAdd],
    finSumFinEquiv_symm_apply_castAdd]

/-- The full block reindex `RepCoord (dStratum q p) ≃ B22block ⊕ SchurVar`. Drops the `Σ _ : Fin 1`
(`Equiv.uniqueSigma`), splits `Fin p ≃ Fin r ⊕ Fin (p−r)` and `Fin q ≃ Fin r ⊕ Fin (q−r)`
(`finSplit`), distributes the product, then rearranges (`blockRearrange`). -/
def repCoordReindex (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    RepCoord (dStratum q p) ≃ B22block q p r ⊕ SchurVar q p r :=
  (Equiv.uniqueSigma _).trans <|
    (Equiv.prodCongr (finSplit hp) (finSplit hq)).trans <|
      (Equiv.sumProdDistrib _ _ _).trans <|
        (Equiv.sumCongr (Equiv.prodSumDistrib _ _ _) (Equiv.prodSumDistrib _ _ _)).trans
          (blockRearrange q p r)

/-- `finSplit` sends a non-pivot index `cast (natAdd r a)` (`≥ r`) to `Sum.inr a`. -/
@[simp] theorem finSplit_natAdd {n r : ℕ} (h : r ≤ n) (a : Fin (n - r)) :
    finSplit h (Fin.cast (show r + (n - r) = n by omega) (Fin.natAdd r a)) = Sum.inr a := by
  rw [finSplit, Equiv.trans_apply,
    show (finCongr (show n = r + (n - r) by omega))
        (Fin.cast (show r + (n - r) = n by omega) (Fin.natAdd r a)) = Fin.natAdd r a from by
      apply Fin.ext; simp [finCongr, Fin.natAdd],
    finSumFinEquiv_symm_apply_natAdd]

/-- A pivot coordinate `⟨0, (castLE i, castLE j)⟩` (pivot row `i`, pivot column `j`, both `< r`)
maps under the reindex into the `Δ`-block of `SchurVar`: `Sum.inr (Sum.inl (i, j))`. So the pivot
minor `detΔ` is a polynomial in the `SchurVar` coordinates only. -/
theorem repCoordReindex_pivot (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (i j : Fin r) :
    repCoordReindex q p r hp hq
        ⟨0, (Fin.castLE hp i, Fin.castLE hq j)⟩
      = Sum.inr (Sum.inl (i, j)) := by
  change ((Equiv.sumCongr (Equiv.prodSumDistrib _ _ _) (Equiv.prodSumDistrib _ _ _)).trans
      (blockRearrange q p r)) ((Equiv.sumProdDistrib _ _ _)
        ((finSplit hp (Fin.castLE hp i), finSplit hq (Fin.castLE hq j)))) = _
  rw [finSplit_castLE, finSplit_castLE]
  rfl

/-- A `B22` coordinate `⟨0, (cast (natAdd r a), cast (natAdd r b))⟩` (non-pivot row `a`, column `b`)
maps under the reindex to the outer `B22block`: `Sum.inl (a, b)`. So the `B22` entries become the
outer (eliminated) coordinates under `blockAlgEquiv`. -/
theorem repCoordReindex_b22 (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a : Fin (p - r)) (b : Fin (q - r)) :
    repCoordReindex q p r hp hq
        ⟨0, (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a),
             Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b))⟩
      = Sum.inl (a, b) := by
  change ((Equiv.sumCongr (Equiv.prodSumDistrib _ _ _) (Equiv.prodSumDistrib _ _ _)).trans
      (blockRearrange q p r)) ((Equiv.sumProdDistrib _ _ _)
        ((finSplit hp (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a)),
          finSplit hq (Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b))))) = _
  rw [finSplit_natAdd, finSplit_natAdd]
  rfl

/-- A `B12` coordinate (pivot row `i`, non-pivot column `b`) maps to the `B12`-block of `SchurVar`:
`Sum.inr (Sum.inr (Sum.inl (i, b)))`. -/
theorem repCoordReindex_b12 (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (i : Fin r) (b : Fin (q - r)) :
    repCoordReindex q p r hp hq
        ⟨0, (Fin.castLE hp i, Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b))⟩
      = Sum.inr (Sum.inr (Sum.inl (i, b))) := by
  change ((Equiv.sumCongr (Equiv.prodSumDistrib _ _ _) (Equiv.prodSumDistrib _ _ _)).trans
      (blockRearrange q p r)) ((Equiv.sumProdDistrib _ _ _)
        ((finSplit hp (Fin.castLE hp i),
          finSplit hq (Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b))))) = _
  rw [finSplit_castLE, finSplit_natAdd]
  rfl

/-- A `B21` coordinate (non-pivot row `a`, pivot column `i`) maps to the `B21`-block of `SchurVar`:
`Sum.inr (Sum.inr (Sum.inr (a, i)))`. -/
theorem repCoordReindex_b21 (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a : Fin (p - r)) (i : Fin r) :
    repCoordReindex q p r hp hq
        ⟨0, (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a), Fin.castLE hq i)⟩
      = Sum.inr (Sum.inr (Sum.inr (a, i))) := by
  change ((Equiv.sumCongr (Equiv.prodSumDistrib _ _ _) (Equiv.prodSumDistrib _ _ _)).trans
      (blockRearrange q p r)) ((Equiv.sumProdDistrib _ _ _)
        ((finSplit hp (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a)),
          finSplit hq (Fin.castLE hq i)))) = _
  rw [finSplit_natAdd, finSplit_castLE]
  rfl

/-! ## The generic product entries are the coordinate variables (`N = 1`) -/

variable {k : Type u} [Field k]

/-- At `N = 1`, the product `mult (dStratum q p) A` is the lone factor `A 0` (the empty prefix
product is the identity). General over any commutative ring. -/
theorem mult_stratum_eq {R : Type*} [CommRing R] (q p : ℕ) (A : Tuple (k := R) (dStratum q p)) :
    mult (dStratum q p) A = A 0 := by
  have hdef : mult (dStratum q p) A
      = A 0 * multPrefix (dStratum q p) A (Fin.castSucc (0 : Fin 1)) := rfl
  have h1 : multPrefix (dStratum q p) A (Fin.castSucc (0 : Fin 1))
      = (1 : Matrix (Fin (dStratum q p (Fin.castSucc (0 : Fin 1))))
            (Fin (dStratum q p (Fin.castSucc (0 : Fin 1)))) R) := rfl
  rw [hdef, h1]; exact Matrix.mul_one _

/-- The generic single-matrix product entries are the coordinate variables:
`multPoly (dStratum q p) a b = X ⟨0, (a, b)⟩`. -/
theorem multPoly_stratum_apply (q p : ℕ) (a : Fin p) (b : Fin q) :
    (Matrix.of (multPoly (k := k) (dStratum q p))) a b
      = (X ⟨0, (a, b)⟩ : MvPolynomial (RepCoord (dStratum q p)) k) := by
  rw [Matrix.of_apply, multPoly, mult_stratum_eq q p (genericTuple (dStratum q p))]
  rfl

/-! ## The pivot minor `detΔ` lives in the `SchurVar` block

Under the block reindex `Φ = renameEquiv (repCoordReindex)`, the pivot minor `detΔ = detPivotPoly`
maps to `rename Sum.inr detSchurS` — a polynomial in the `SchurVar` (specifically `Δ`) coordinates
only. Pushing further through `sumAlgEquiv` (with `B22block` outermost), `detΔ` becomes the constant
`C detSchurS`, so localizing `A_eng` at `detΔ` is localizing the coefficient ring at `detSchurS`. -/

/-- The pivot determinant in the free Schur coordinate ring: `det` of the `Δ`-block coordinate
matrix `(i, j) ↦ X (Sum.inl (i, j))` in `MvPolynomial (SchurVar q p r) k`. This is `detΔ` after
eliminating the `B22` block — the localization element on the Schur side. -/
noncomputable def detSchurS (q p r : ℕ) : MvPolynomial (SchurVar q p r) k :=
  (Matrix.of (fun i j : Fin r ↦ (X (Sum.inl (i, j)) : MvPolynomial (SchurVar q p r) k))).det

/-- Under the reindex `renameEquiv (repCoordReindex)`, the pivot minor `detΔ` maps to
`rename Sum.inr (detSchurS)`: it is a polynomial in the `SchurVar` coordinates only. (`det` commutes
with the algebra maps; each pivot entry `X ⟨0, (castLE i, castLE j)⟩` maps to the `Δ`-coordinate
`X (Sum.inr (Sum.inl (i, j)))`, by `repCoordReindex_pivot`.) -/
theorem renameEquiv_detPivot (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    (renameEquiv k (repCoordReindex q p r hp hq)) (detPivotPoly (k := k) q p r hp hq)
      = rename Sum.inr (detSchurS (k := k) q p r) := by
  rw [detPivotPoly, detSchurS, AlgEquiv.map_det, AlgHom.map_det (rename Sum.inr)]
  congr 1
  funext i j
  rw [AlgEquiv.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply,
    Matrix.submatrix_apply, multPoly_stratum_apply, renameEquiv_apply, rename_X, Matrix.of_apply,
    rename_X]
  congr 1
  exact repCoordReindex_pivot q p r hp hq i j

/-- The full block algebra equivalence
`A_eng ≃ₐ[k] MvPolynomial B22block (MvPolynomial SchurVar k)`: relabel the coordinates
(`renameEquiv (repCoordReindex)`) then split off the `B22` block (`sumAlgEquiv`, `B22block`
outermost). -/
noncomputable def blockAlgEquiv (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    MvPolynomial (RepCoord (dStratum q p)) k
      ≃ₐ[k] MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k) :=

exec
/bin/bash -lc "sed -n '1,130p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.DeterminantalBaseElimination
import DLNFibre.Core.DeterminantalChartRing
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# `DLNFibre.Core.DeterminantalBasePresentation` — the localized base presentation `A_loc/Iad ≅ Sd`

The final identification of `G2-2`: the localized determinantal base ring `A_loc = Localization.Away
detΔ`, modulo its base ideal `Iad`, is the free Schur localization `Sd` (`= Localization.Away
detSchurS`) — a regular ring of dimension `δ`. The eliminated `B22` block (`B22 = B21 Δ⁻¹ B12`) is
forced by the Schur relation once `detΔ` is inverted.

**The route (Codex-vetted, thread-13 `codex-g22c-route` consult).** The localized block equivalence
`Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd` (localizing the LANDED `blockAlgEquiv` at `detΔ ↦
C detSchurS`) carries `Iad` to a prime of `MvPolynomial B22block Sd`. The forced-block graph ideal
`J = graphIdeal forcedB22` (the genuine forced value `B21 adjΔ B12 / detΔ ∈ Sd`) satisfies:

1. **`height J = C`** — the translation automorphism maps `J` to the coordinate ideal, whose height
   is `#B22block = C` (LANDED `height_coordIdeal_localization_eq`).
2. **`J ⊆ Ψ(Iad)`** — each generator `X_b − C(forcedB22 b)` is, up to the unit `C detSchurS`, the
   image under `Ψ` of the bordered `(r+1)`-minor (LANDED `det_submatrix_multPoly_mem_sigmaIdeal`),
   which lies in `Iad`. This carries the actual Schur content.
3. **`Iad = J`** — by `Ideal.height_strict_mono_of_is_prime` (both prime, `height Ψ(Iad) = height
   Iad = C = height J`, `J ⊆ Ψ(Iad)` ⟹ no strict containment ⟹ equal). This honestly **earns** the
   hard direction `Iad ⊆ J`.

Then `A_loc/Iad ≅ (MvPolynomial B22block Sd)/J ≅ Sd` via `graphIdealQuotientEquiv`. `J` stays
internal; the domain / dimension `δ` follow from `Sd` being a polynomial localization.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## The localized block equivalence `Ψ`

`Sd := Localization.Away detSchurS`, `Q := MvPolynomial B22block Sd`. We use `Localization` (the
canonical localization) so the `k`-algebra instances on `Sd` and `Q` resolve automatically. -/

/-- The free Schur localization `Sd = Localization.Away detSchurS` — the downstream-composable base
ring (a regular ring of dimension `δ`). -/
abbrev SchurLoc (q p r : ℕ) : Type u :=
  Localization.Away (detSchurS (k := k) q p r)

/-- **The localized block equivalence** `Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd`, localizing the
LANDED `blockAlgEquiv` at `detΔ` (which maps to `C detSchurS`). -/
noncomputable def blockAlgEquivLoc (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Localization.Away (detPivotPoly (k := k) q p r hp hq)
      ≃ₐ[k] MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r) := by
  -- the scalar tower `k → B → Q`
  haveI tower : IsScalarTower k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
    have hkB : (algebraMap k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))) x
        = C (algebraMap k (MvPolynomial (SchurVar q p r) k) x) := by
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (SchurVar q p r) k)
        (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))]; rfl
    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) x
        = C (algebraMap k (SchurLoc (k := k) q p r) x) := by
      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
    rw [hkB, hkQ, algebraMap_def, MvPolynomial.map_C]
    congr 1
  -- `Q` is the localization of `B` at `powers (C detSchurS)`
  haveI hloc : IsLocalization (Submonoid.powers (C (detSchurS (k := k) q p r) :
      MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k)))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    simpa [Submonoid.map_powers] using
      (MvPolynomial.isLocalization (σ := B22block q p r)
        (M := Submonoid.powers (detSchurS (k := k) q p r))
        (S := SchurLoc (k := k) q p r))
  have H : Submonoid.map (blockAlgEquiv (k := k) q p r hp hq)
        (Submonoid.powers (detPivotPoly q p r hp hq))
      = Submonoid.powers (C (detSchurS (k := k) q p r)) := by
    rw [Submonoid.map_powers, blockAlgEquiv_detPivot]
  exact IsLocalization.algEquivOfAlgEquiv
    (Localization.Away (detPivotPoly (k := k) q p r hp hq))
    (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
    (blockAlgEquiv q p r hp hq) H

/-! ## The bordered `(r+1)`-minor `m_b` and its `blockAlgEquiv` image `(*)`

For a `B22` entry `(a', b')` the bordered `(r+1)×(r+1)` minor `m_b` of the generic product (rows
`[pivots, r+a']`, columns `[pivots, r+b']`) lies in the base ideal (an `(r+1)`-minor), and under
`blockAlgEquiv` becomes `C detSchurS · X (a', b') − C (forcedNum a' b')` (the bordered Schur minor
identity, transported). Dividing by the unit `C detSchurS` lands `X (a', b') − C (forcedB22 …)` in
`Ψ(Iad)`. -/

/-- The four blocks of the bordered minor at the `B22` entry `(a', b')` (entries are coordinate
variables of `multPoly`). Pivot block `Δ`, pivot-row × non-pivot-col `u`, non-pivot-row × pivot-col
`v`, corner `d`. The non-pivot index is the landed reindex form `Fin.cast (natAdd r ·)`. -/
noncomputable def borderΔ (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Matrix (Fin r) (Fin r) (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun i j ↦ (Matrix.of (multPoly (dStratum q p))) (Fin.castLE hp i) (Fin.castLE hq j)

noncomputable def borderU (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (b' : Fin (q - r)) :
    Matrix (Fin r) Unit (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun i _ ↦ (Matrix.of (multPoly (dStratum q p))) (Fin.castLE hp i)
    (Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b'))

noncomputable def borderV (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (a' : Fin (p - r)) :
    Matrix Unit (Fin r) (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun _ j ↦ (Matrix.of (multPoly (dStratum q p)))
    (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a')) (Fin.castLE hq j)

noncomputable def borderD (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    Matrix Unit Unit (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun _ _ ↦ (Matrix.of (multPoly (dStratum q p)))
    (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a'))
    (Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b'))

/-- The `SchurVar`-side pivot block `ΔS` (whose determinant is `detSchurS`). -/
noncomputable def schurΔ (q p r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (SchurVar q p r) k) :=
  Matrix.of fun i j ↦ X (Sum.inl (i, j))

/-- The `SchurVar`-side `B12` column `uS` at non-pivot column `b'` (the `b'`-th column of `B12`). -/
noncomputable def schurU (q p r : ℕ) (b' : Fin (q - r)) :
    Matrix (Fin r) Unit (MvPolynomial (SchurVar q p r) k) :=
  Matrix.of fun i _ ↦ X (Sum.inr (Sum.inl (i, b')))


codex
**Verdict: STOP -> B.** The gauge-ring question is tractable, but the radical split is the R2-3b-4 wall in another form, not a 2-3 module grind.

**Gauge Ring**

Use **(b)**: the gauge that acts on `IadDeep` must live over the pre-quotient total chart
`T := Localization.Away (ΔPdeep d r hp hq)`.

Do **not** use `schurToSred` for this. It lands after quotienting by `IadDeep`, so it is too late to define `gauge.map IadDeep`.

Clean Lean shape:

1. Define the total localized pivot/off-diagonal blocks directly from `Matrix.of (multPoly d)` mapped into `T`.
2. Use `IsLocalization.Away.algebraMap_isUnit (ΔPdeep ...)` to make the pivot block invertible.
3. Build the endpoint `BaseChangeGroup (k := T) d`.
4. Induce the localized coordinate automorphism of `T`.

You can view this as the Schur gauge transported through the pre-quotient chart data, but in Lean I would **rebuild it over `T` from `ΔPdeep`'s own product blocks**. Transport through `schurToSred` is the wrong object.

**Containments**

`⊆`: not a finite generator grind as stated. The engine has lemmas that `(r+1)`-minors lie in `sigmaIdeal`, but `sigmaIdeal` itself is a `vanishingIdeal` / `sInf` of orbit ideals, not a proved span of those minors. Mathlib v4.29 lacks the determinantal-ideal generation theorem you would need to reduce arbitrary elements of `sigmaIdeal` to bordered-minor computations. So checking transformed minors is insufficient for `gauge.map IadDeep ≤ splitBaseFibreIdeal.radical`.

`⊇`: height count does not sidestep it. The deep `sigmaIdeal` is generally reducible, and the fibre side is also reducible. Equal height plus radicality does not imply equality of radical ideals unless you also prove a minimal-prime/component correspondence or prime/unmixed structure strong enough to rule out extra components. That is essentially the missing chart trivialization / structural ideal theorem.

**Shorter Dimension Path**

No real shortcut here. Directly computing `ringKrullDim Sred` from the landed `dim Σbar = card - C` only gives the chart’s ambient-rank-locus dimension after proving localization keeps a top component. It does not identify the fibre term. A module-finite route is impossible because the relative dimension is positive. A flat/local-product route would be exactly the missing `Sred ≃ SchurLoc ⊗[k] FibreAlg`.

**Call**

Do not grind the radical split now. Build/cite the fallback using `hSweep`.

If you still want a useful non-wasted module, build only the **total-localized gauge over `Localization.Away ΔPdeep`** as infrastructure. But the radical equality itself needs absent structural machinery, not bookkeeping.
tokens used
188,552
**Verdict: STOP -> B.** The gauge-ring question is tractable, but the radical split is the R2-3b-4 wall in another form, not a 2-3 module grind.

**Gauge Ring**

Use **(b)**: the gauge that acts on `IadDeep` must live over the pre-quotient total chart
`T := Localization.Away (ΔPdeep d r hp hq)`.

Do **not** use `schurToSred` for this. It lands after quotienting by `IadDeep`, so it is too late to define `gauge.map IadDeep`.

Clean Lean shape:

1. Define the total localized pivot/off-diagonal blocks directly from `Matrix.of (multPoly d)` mapped into `T`.
2. Use `IsLocalization.Away.algebraMap_isUnit (ΔPdeep ...)` to make the pivot block invertible.
3. Build the endpoint `BaseChangeGroup (k := T) d`.
4. Induce the localized coordinate automorphism of `T`.

You can view this as the Schur gauge transported through the pre-quotient chart data, but in Lean I would **rebuild it over `T` from `ΔPdeep`'s own product blocks**. Transport through `schurToSred` is the wrong object.

**Containments**

`⊆`: not a finite generator grind as stated. The engine has lemmas that `(r+1)`-minors lie in `sigmaIdeal`, but `sigmaIdeal` itself is a `vanishingIdeal` / `sInf` of orbit ideals, not a proved span of those minors. Mathlib v4.29 lacks the determinantal-ideal generation theorem you would need to reduce arbitrary elements of `sigmaIdeal` to bordered-minor computations. So checking transformed minors is insufficient for `gauge.map IadDeep ≤ splitBaseFibreIdeal.radical`.

`⊇`: height count does not sidestep it. The deep `sigmaIdeal` is generally reducible, and the fibre side is also reducible. Equal height plus radicality does not imply equality of radical ideals unless you also prove a minimal-prime/component correspondence or prime/unmixed structure strong enough to rule out extra components. That is essentially the missing chart trivialization / structural ideal theorem.

**Shorter Dimension Path**

No real shortcut here. Directly computing `ringKrullDim Sred` from the landed `dim Σbar = card - C` only gives the chart’s ambient-rank-locus dimension after proving localization keeps a top component. It does not identify the fibre term. A module-finite route is impossible because the relative dimension is positive. A flat/local-product route would be exactly the missing `Sred ≃ SchurLoc ⊗[k] FibreAlg`.

**Call**

Do not grind the radical split now. Build/cite the fallback using `hSweep`.

If you still want a useful non-wasted module, build only the **total-localized gauge over `Localization.Away ΔPdeep`** as infrastructure. But the radical equality itself needs absent structural machinery, not bookkeeping.
