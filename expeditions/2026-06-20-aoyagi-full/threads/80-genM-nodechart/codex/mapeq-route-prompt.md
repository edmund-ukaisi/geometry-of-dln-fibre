<task>
Lean 4 + Mathlib formalisation, research-grade. I must decide a FACTORIZATION ROUTE before a multi-day cold build, and want a decorrelated read on a possible structural obstruction.

CONTEXT (deep-linear-network achiever chart, opaque dimensions). I have a chart map
  phi := phiFlatLiveR1 ∘ kLDU : (Fin N → ℝ) → (Fin N → ℝ),  where N = routeMAmbient M (an OPAQUE ℕ, = flatDim M).
Concretely phi x = paramsEquivFlat M (chartParamsGen (x p₀) M t (decoder x) hle), where:
  - paramsEquivFlat : Params M ≃L (Fin N → ℝ) is a LINEAR reshape (det ±1).
  - chartParamsGen reindexes the layers A_0,...,A_{L-1} of a telescoping matrix CHAIN `chainOfMt u M t (decoder x)`.
    The chain's layer A_k is built from the decoder's per-boundary blocks Bmat_k, Nblk_k, Wblk_k, Rmat_k, Rfin
    via products (chainQ(N), Bmat·chainQ + u·Rmat, etc). The layers ENTANGLE blocks: A_k depends on boundary-k AND
    chained data. The chain is the standard DLN "C_s = Bmat_s·chainQ(N_s) + u·Rmat_s" recursion.
  - decoder x = genBlkFlatLiveR1(..., kLDU x, x): reads, per boundary s = k+1, the Schur-frame role blocks
    K_s, X_s, N_s, E_s and a lift W_s from DISJOINT flat slots of x (via a Classical bijection chartIdxEquiv :
    Fin N ≃ Σ k:Fin L, Fin(schurDim k) ⊕ Fin(liftDim k), then frameSplitEquiv splitting the Schur slot into K/X/N/E).
    kLDU rewrites only the K-slots to an LDU matrix; identity elsewhere.

GOAL (the "item-3 map equality"): produce `fs : List (ChartFactor N)` with
  composeFold fs = phi   (composeFold = fs.foldr (fun F g => F.f ∘ g) id).
The downstream consumer (`interiorDet_of_factored`) then gives |det Dphi| = ∏_j |u_j|^{leafH j} via a per-factor
det telescope. Each non-trivial factor is a `conjBlockFactor E_s g_s`: E_s.symm ∘ (g_s on a block, id on rest) ∘ E_s,
for a CLE E_s : (Fin N → ℝ) ≃L Block_s × R_s. The proposed fs (head applied LAST):
  [ linearFactor Q (= paramsEquivFlat ∘ pack, det 1);
    radialFactor active p₀ (radial blow-up, det |u_p₀|^{minAdm−1});
    per boundary s descending: lduChartFactor E'_s, schurChartFactor E_s (det |det K_s|^{r+c});
    chainChartFactor ... (det 1) ].

THE PROPOSED PROOF DESIGN (call it F1): "prefix-threading via apply_symm_apply".
Each factor reads/writes ONLY its own boundary's block via E_s; the E_s block-slots are claimed DISJOINT across
boundaries (distinct chartIdxEquiv role-slots). Key lemma B-2 ("prefix-invariance"): for s' ≠ s,
  (E_s (conjBlockMap E_{s'} g u)).1 = (E_s u).1  -- factor-s' doesn't touch boundary-s's block.
Then funext + threading each per-factor match (B-3: conjBlockMap E_s g_s reproduces the decoder's boundary-s
transform) through the fold.

WHAT I'M WORRIED ABOUT (the possible obstruction). The chart is NOT a coordinate-wise / per-block map: the chain
layer products MIX blocks across boundaries (A_k = Bmat_k · chainQ(N_k) + u·Rmat_k, and the loss-relevant product
A_0·A_1·...·A_{L-1} couples ALL boundaries). The (3,3,3,3) concrete case (L=3, drops at all boundaries) was NEVER
expressed as a composeFold — it was matched at the chart-parameter level (chartParamsGen = a hand-built chart) and
its determinant taken via a DIRECT fused-frame det_comp, NOT a composeFold telescope. The only composeFold map
equality that exists (4,4,2,2) is PURE-RADIAL (no Schur/LDU factors at all). So there is NO t≥2 precedent for the
composeFold route.

The conjBlockFactor model says factor-s acts as `E_s.symm ∘ (g_s ⊕ id) ∘ E_s` — a map that is identity on
coordinates OUTSIDE block-s (in the E_s splitting). For composeFold fs = phi to hold, phi itself must be a
COMPOSITION of such block-local maps in some shared/threaded coordinate system. But phi sends the flat slots
(K,X,N,E,W per boundary) to the FLATTENED PRODUCT of chain layers — an entangling, non-block-local map.
</task>

<output_contract>
Answer in 4 sections, terse and concrete:

1. VERDICT (one of): (A) F1 is sound and the per-block factorization genuinely exists — the entanglement is an
   illusion because [reason]; (B) F1 has a real structural obstruction — the chart is NOT a composeFold of
   block-local conjBlockFactors over a SHARED coordinate system, because [reason]; (C) F1 can work but ONLY if
   [precise extra structure]. Pick one and commit.

2. THE KEY DISTINCTION I may be conflating: is phi = composeFold fs asking the per-boundary factors to compose in
   ONE fixed flat coordinate system (E_s all splitting the SAME Fin N → ℝ), or in DIFFERENT spaces threaded by
   reshapes? In the conjBlockFactor model every E_s splits the SAME Fin N → ℝ. Does the DLN chart's block-coupling
   (layer products) survive expression as a composition of {block-local map in fixed coords}? Give the cleanest
   yes/no argument. If the chain product A_0·...·A_{L-1} is the obstruction, say so explicitly.

3. IF F1 IS OBSTRUCTED: is the fallback F2 (DEFINE the interior chart AS composeFold fs, and separately prove a
   RATE-level map equality phiFlatLiveR1 = composeFold fs only where the rate engine consumes it) actually LIGHTER,
   or does it hit the SAME entanglement (since the rate also reads the chain product)? One paragraph.

4. CHEAPEST DISCRIMINATING TEST: the single smallest Lean check (or pen-and-paper computation on a 2-boundary
   example, e.g. (2,2,2) with one Schur factor) that would CONFIRM-or-KILL whether composeFold of conjBlockFactors
   can equal a chart with a non-trivial Schur frame. Be specific about what to compute.
</output_contract>

<grounding_rules>
You do NOT have the repo. Reason from the mathematical structure I described (the conjBlockFactor model: factor =
E.symm ∘ (g ⊕ id) ∘ E, all E splitting the same Fin N → ℝ; the chart = linear reshape of a telescoping chain
product). Flag any step where you are INFERRING the DLN chart's structure vs reasoning from what I stated. Do NOT
assume the factorization works just because a spec proposes it — the absence of a t≥2 precedent is the data point.
The crux is whether a flatten-of-chain-product map decomposes as a composition of fixed-coordinate block-local maps.
