# priorities — fibre-codimension bundle-shift (LR Lemma 4.6)  (taste ledger)

Controller proposes (VOI × directed suspicion); operator edits directly. Nothing unranked;
"unclear-but-keep-going" is first-class.

## Done

- **[recon · thread 01] Scope Lemma 4.6 reachability** → **GENUINE BLOCKER** (needs a from-scratch
  finite-type-morphism dimension theorem, ~8–15 modules; decorrelated-Codex-confirmed). Operator
  committed to building it; thermometer first.

## Done

- **[recon · thread 01]** Lemma 4.6 reachability → GENUINE BLOCKER (layer 1 = a from-scratch
  finite-type-morphism dimension theorem). Operator committed to the build.
- **[tide · thread 02] Thermometer — LANDED.** `varietyDim (productRankLocusLE ![n,m] r) = r(n+m−r)`
  (`Core.DeterminantalStratumDim`), via the N=1 quiver specialisation. Green, axiom-clean, reviewed.
  **Reading: layer 1 NOT de-risked** (rode the single-variety catenary, not a morphism-dim theorem).

## Done

- **[recon · thread 03] Layer-1 design recon** → **GO, REFRAMED.** We need only `dim fibre` via the
  going-down height-additivity lemma (not the general morphism theorem); scope ~5–8 modules; risk on
  L1-0 (flatness) + L1-5 (reducibility). Tide sequencing A/B/C adopted. Codex-converged.

## Pursue (ranked)

**Tide A (L1-0) CHECKPOINTED, not proved** (`Core.FlatTrivialProductProbe`, builds green): the
`Module.Flat` API is viable at v4.29, but the flat route needs a from-scratch coordinate-ring map
`A →+* B` for `mult` (none in the engine) + chart localisation + trivialisation — ~8–12 modules, NOT an
API gap. Revises L1-0 cost up.

**Operator re-scope decision (the resume fork — synthesis § HOLD is authoritative):**
1. **Ring-map / Spec construction for `mult`** (~8–12 modules) — the honest flat route; would warrant
   its own design recon.
2. **Fallback: two-inequality dimension sandwich** — cheap lower bound (going-down/up) + the
   equidimensionality upper bound (the residual hard half).
3. **Discharge `r ≤ 1` + roadmap generality** — minimal; retire `cited_bundle_shift` only at `r ≤ 1`.

## Park (unclear-but-keep-going)

- **L1-5 reducibility/per-component** (MED-HIGH): the squeeze must hold per top-dimensional component
  (`Σ^r`/`fibre` reducible — the θ-story); local triviality bijects the components preserving dim up to
  the shift. Deferred to Tide C; flagged now so Tide A/B don't assume irreducibility.
- **Layer 3 future need:** the matrix-rank-locus identification (dropped in thread 02).

## Park (unclear-but-keep-going)

- **Layer 1 construction:** does `dim total = dim base + fibre dim` for `mult⁻¹(B) → Mat^{rk=r}` build
  from the `voigt-discharge` library + Mathlib's `ringKrullDim`/`Flat`/`relativeDimension` API, or need
  genuinely new AG? The layer-1 design recon would settle the rung-ladder.
- **Layer 3 future need:** the matrix-rank-locus identification `productRankLocusLE ![n,m] r =
  {M | M.rank ≤ r}` (dropped in thread 02) — needed when `Mat^{rk=r}` is the bundle base.

## Drop / escalate

- (none yet)
