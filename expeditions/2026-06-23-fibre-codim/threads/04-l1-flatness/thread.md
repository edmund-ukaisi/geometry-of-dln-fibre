# thread 04 — l1-flatness  (Tide A, formalisation / tide — GATING)

**Type:** formalisation (tide) · `OPENED → SPECIFY → PROVE → AUDIT`. The **gating** rung of the layer-1
flat-height squeeze: the whole squeeze (Tides B, C) hinges on this, and it is the recon's
**wall-within-the-wall** (HIGH risk, no landed template). So: **SPECIFY-first with a hard checkpoint** —
de-risk the API before committing to the proof.

**Goal (L1-0):** flatness of the multiplication map `mult` restricted to a rank-`r` **chart** — i.e.
`Module.Flat A B` for the coordinate-ring map of `mult : Σ^r → Mat^{rk=r}` localised where the bundle
is trivial. Route (LR / recon): local triviality ⟹ the chart pulls back to a *trivial product* ⟹ the
total coordinate ring is *free* over the base ⟹ *flat*. Flatness then feeds L1-1 (the going-down
height-additivity lemma) to extract `dim fibre`.

## Read first
- **The thread-03 design report** (`…/threads/03-layer1-design/thread.md`) — the precise L1-0 statement,
  the squeeze `(★)`, the rung-ladder, the landed substrate (`AffineDomainDimension`,
  `FlatQuasiFiniteHeight`, `PolynomialDimension`), and the fallback. **This is your spec source.**
- `lean/CLAUDE.md` (zero sorry/axiom/native_decide; `decide +kernel`; `↦`; name=content; bedrock).
- `Core.FlatQuasiFiniteHeight` (the landed `Module.Flat → HasGoingDown.of_flat → height-additivity`
  pattern — note its quasi-finite shortcut does NOT apply here: positive-dim fibre).

## Process — SPECIFY-first, HARD checkpoint
1. **SPECIFY / API PROBE:** pin the exact Lean statement of L1-0 (the rings `A` (base/chart) and `B`
   (total), the `Module.Flat A B` claim, the chart/localisation). Probe the **v4.29 `Module.Flat` API
   surface** with `example`-blocks: base-change/descent (`Module.Flat.of_*`), flat-local-on-base,
   free ⟹ flat (`Module.Flat.of_free`), trivial-product freeness. State exactly which lemmas exist and
   what each demands of our setup.
2. **CHECKPOINT (no-skip):** report the pinned statement + the API viability verdict + the route. Proceed
   to PROVE **only if the route is clearly viable** in this run. If the flat-descent API does NOT support
   it (or the route needs machinery absent at v4.29), **STOP and report** the API surface + recommend the
   **fallback** (two-inequality sandwich: cheap lower bound via going-down/up + the equidimensionality
   upper bound; or discharge the witness range `r ≤ 1` + roadmap generality). Do NOT grind a doomed route.
3. **PROVE** L1-0 to green, then **AUDIT.**

## AUDIT gate (if proved)
`lake build` green (whole library); `scripts/sorries` 0; `#print axioms` `[propext, Classical.choice, Quot.sound]`.
New module under `lean/DLNFibre/Core/` (or `DLN/` if it must mention `mult` — but prefer Core; check the
dependency rule). Controller aggregates `DLNFibre.lean`.

## Scope
**Just L1-0** (the flatness fact). L1-1→L1-6 (height-additivity, fibre-ring id, assembly, reducibility,
output bridge) are **subsequent tides (B, C) — NOT in scope.** `decide +kernel` not `native_decide`.
Don't touch other worktrees or any stash. In-repo memory only.

## Build note
Worktree builds via a **symlinked shared `lean/.lake/packages`** — do NOT run `lake exe cache get`.
`lake build` from `lean/` works incrementally.

## Report
(i) the **API viability verdict** — is the `Module.Flat` flat-descent route viable at v4.29 (→ PROVE), or
not (→ which fallback)? Be concrete about the lemmas found/missing.
(ii) if proved: final theorem name + signature; green/sorries/axioms; module path + aggregator line.
(iii) if checkpointed: the pinned statement + the precise API gap + the recommended fallback.

## Notes / progress
(appended during work)
