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

1. **[tide · thread 04 = Tide A] L1-0: flatness of `mult` on a rank-`r` chart** (`Module.Flat`). The
   **gating** rung (the whole squeeze hinges on it) and the wall-within. Route: local triviality ⟹
   trivial product ⟹ free ⟹ flat. **SPECIFY-first:** probe the v4.29 `Module.Flat` descent/base-change
   API surface; **checkpoint** if it doesn't support the route — don't grind. **Fallback:**
   two-inequality sandwich, or discharge `r ≤ 1` (the witness range) + roadmap generality. **VOI:
   decisive** (gates Tides B, C). **Suspicion: HIGH** (no landed template; `FlatQuasiFiniteHeight`'s
   shortcut does NOT apply — positive-dim fibre, not quasi-finite).

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
