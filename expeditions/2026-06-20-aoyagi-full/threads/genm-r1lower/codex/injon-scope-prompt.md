# Scope check: injectivity of (BchartLeaf ∘ kLDU) for the LIVE+kLDU achiever chart (Lean 4 / Mathlib)

## Context

I'm proving `Set.InjOn (interiorLivePhi) {u | u leafPivot ≠ 0 ∧ ∀ j ∈ E, u j ≠ 0}` where
`interiorLivePhi = phiFlatLiveAt … leafPivot ∘ kLDU` for an L=2 deep-linear-network achiever chart.

I have a MACHINE-CHECKED factorization (via hmap_leaf at the point kLDU x + a proven commute):
  interiorLivePhi = (BchartLeaf ∘ kLDU) ∘ pivotBlowupOn activeM leafPivot
where:
- `pivotBlowupOn activeM leafPivot` : the radial blow-up. INJECTIVE off {u leafPivot = 0} — BANKED
  (Mathlib-style pivotBlowupOn_injOn).
- `kLDU` : the K-slot LDU reparametrization. `kLDU x` rewrites each per-boundary K-block from its raw
  free entries to the LDU matrix `(1+L)·diag(q)·(1+U)` via `kLens K = matrixSplit.symm(lduCoreMap(matrixSplit K))`.
  Identity on all non-K slots.
- `BchartLeaf` : the `u`-FREE boundary factor — radial scalar hardwired to the constant 1, residual
  coords read DIRECTLY (rfinDirect) from its input; it's `paramsEquivFlat ∘ chartParamsGen 1 (decoder)`.
  `paramsEquivFlat` is a (linear) Equiv (injective). The content is `chartParamsGen 1` recovery: recover
  the residual chart coords from the per-layer matrices `Agen 1 … s` (the Schur-frame blocks).

## The chain to prove

`InjOn ((BchartLeaf ∘ kLDU) ∘ pbo) S`, S = {u leafPivot ≠ 0 ∧ ∀j∈E q-pivots ≠ 0}. Via Set.InjOn.comp:
peel pbo (banked inj off {leafPivot=0}), then `InjOn (BchartLeaf ∘ kLDU) (pbo '' S)`.

## What I learned earlier (genm-hinj obstruction note)

The DEAD-leaf chart was NON-injective SOLELY because of a radial scaling degeneracy (radial u entered
only as `u•Rmat`, so (u, readE) ↦ (λu, readE/λ) was invariant). The note explicitly said: "Off-diagonal
LDU params (l,u) and X/N/W recover fine once the LDU diagonal pivots q ≠ 0 (in E); the defect is SOLELY
the radial." The LIVE chart fixes the radial via the (0,0)=1 anchor + the pbo blow-up.

## My BOUNDED read (please red-team)

Since the radial defect is now handled by pbo (peeled off first, banked), the remaining
`InjOn (BchartLeaf ∘ kLDU)` is the OFF-RADIAL residual recovery — which the genm-hinj note says "recovers
fine once q ≠ 0". With kLDU LDU-coordinatizing K, the K-block recovery is the single-block LDU recovery
(`lduCoreMap` injective off {∏q_i ≠ 0}: from (1+L)·diag(q)·(1+U) recover l,q,u when q_i≠0), and the X/N/E
residuals are linear reads. So I claim `InjOn (BchartLeaf ∘ kLDU) (pbo '' S)` is the composition of:
  (a) lduCoreMap/kLens injective off the q-pivots (single-block LDU recovery, NEW but standard),
  (b) the X/N/E + leaf residual recovery (linear, from the Schur-frame blocks Agen 1 … s),
  (c) paramsEquivFlat injective (banked Equiv).
and is MUCH cheaper than the monolithic 27-coordinate `chartParams3333_injOn` triangular back-solve,
because the radial — the ONLY genuinely-coupled coordinate — is no longer in this map.

## Questions

Q1. Is my decomposition sound — specifically, does peeling pbo FIRST genuinely remove the radial coupling
    so that BchartLeaf∘kLDU injectivity is "just" the off-radial residual recovery? Or does pbo '' S still
    carry a coupling that forces a joint recovery?

Q2. Is `BchartLeaf` injectivity (the chartParamsGen-1 residual recovery from the per-layer Agen matrices)
    genuinely decomposable into per-block recoveries (K via LDU, X/N/E linear), or is there a CROSS-block
    coupling in the Schur frame `C = Bmat·chainQ + Rmat` (where Bmat = [K; XK]) that entangles K with X
    (e.g. recovering X needs K⁻¹, so X-recovery couples to K-recovery)? If the latter, the recovery is
    still triangular (recover K first via LDU, then X = (XK)·K⁻¹) — is THAT the right structure, and is it
    bounded at opaque width?

Q3. Net: is this a bounded build (a few hundred lines of per-block recovery + Set.InjOn.comp glue), or does
    the opaque-width Schur-frame block-recovery hide a genuine wall (e.g. needing a generic bmatStack /
    Schur block-inverse injectivity lemma that doesn't exist and is itself hard)? Be skeptical — the
    genm-hinj note's Codex estimate for the FULL chart was "very heavy, not a 200-line lemma", but that
    INCLUDED the radial. Does removing the radial (via pbo) actually drop it to bounded, or is the
    block-recovery the real cost regardless?
