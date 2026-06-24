# R1 achiever-wedge design + hfin corank probe (the box-divergence atom)

**Seat:** `pen-and-paper` (`witness`-leaning: construct the divergence wedge; `obstruction`-leaning on
hfin). **Date:** 2026-06-24.
**Gate:** R1 `resolution_charts` lower-bound atom `routeMCore_box_diverges_achiever`
(`RouteMLayerCoverGE.lean:117`) + the hfin (upper-bound / completeness) corank-sensitivity probe.
**Brief:** controller dispatch (design the achiever wedge for the hdiv atom + probe hfin).
**Method:** exact sympy (symbolic flat-coordinate factorizations, exact monomial-exponent arithmetic,
brute weighting search) + one decorrelated `local-codex-consult` (gpt-5.x, xhigh; frame-in/facts-in/
hypothesis-out). Scripts: `/tmp/wedge_*.py`, `/tmp/flat_tube_222.py`. Codex prompt/answer in
`codex/wedge-soundness-{prompt,answer}.md`.

---

## VERDICT (two lines)

**(a) The achiever wedge is SOUND and build-ready, with one binding axis `(1, minAdm−1)` feeding the
existing `monomialIntegrand_lintegral_box_eq_top` atom.** For `L=2` RRR cores (incl. the binding
corank-2 `(3,3,4)`) it is a **single weighted radial blow-up** with `F∘φ = u²·U` (`U` bounded below
on a positive-measure slice) — verified EXACT in flat coordinates, no gauge. For `L≥3` the wedge is a
**recursive gauge chain** (still only the ONE achiever path, so lighter than the full cover).

**(b) hfin (the upper bound) IS corank-sensitive** — it is the headline's `≥` direction ("`minAdm/2`
is the global-min RLCT"), and proving it needs the corank strata resolved correctly (the coupled
`diag(b)` cover up to null) OR the cited analytic bound. The wedge does NOT give it.

---

## The load-bearing mechanism (all M, exact)

The atom needs `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤` for `c' ≥ ½·minAdm M`, every `ε>0`. The
existing Lean atom `monomialIntegrand_lintegral_box_eq_top` (Case222Cover.lean:283) diverges via a
**single binding axis** `j₀` with `e j₀ = h j₀ − 2 k j₀ c' ≤ −1` (Tonelli: that one axis carries
`∫₀^ε u^{≤−1} = ⊤`, all other axes finite). The `routeLayerAtlas` achiever leaf already carries
`foldDivisors[minAdm]` = the **single** divisor `(k,h)=(1, minAdm−1)`, threshold `minAdm/2`. At
`c'=½·minAdm`:

    e = (minAdm−1) − 2·1·(minAdm/2) = minAdm − 1 − minAdm = −1.   [exact, all minAdm — F1]

So the chart must deliver, on a positive-measure box mapping into `cubeBox`,

    F∘φ(u) = u_b² · U(u),   U ≥ c₀ > 0,    |det Dφ(u)| = u_b^{minAdm−1} · (positive, finite).

Then `∫ Jac·|F∘φ|^{−c'} ≥ c₀^{−c'} ∫ u_b^{minAdm−1} u_b^{−2c'} = ∫ u_b^{−1} = ⊤` at `c'=½·minAdm`,
and `φ''(box) ⊆ cubeBox` + `lintegral_mono_set` lift it to the flat box integral. This is exactly the
`(2,2,2)` template (`routeM222_box_diverges`, Case222RouteMCover.lean:163), generalised.

## The `L=2` wedge — a single weighted radial blow-up (build-ready, EXACT)

For an `L=2` core `M=(M₀,M₁,M₂)` (the RRR cores; the binding corank-2 family `(n,n,p)` lives here),
the wedge is one **weighted blow-up of the `minAdm`-dim achiever center**: scale exactly `minAdm`
flat coordinates by the binding parameter `u`, hold the rest generic-bounded, so the matrix product
picks up **exactly one** `u` per entry.

**`(3,3,4)`, `minAdm=8`, `c'=4`, verified EXACT in flat coordinates (`/tmp/wedge_weighted_334.py`):**
with `C¹` pivot `(0,0)=1`, the `2×2` residual block `Δ = u·D̄`, and `C²` top row `= u·t̄`, bottom
`2×4` block `S` generic:

    F = ‖C¹C²‖² = u²·U   EXACTLY (pure degree 2 in u; sympy: F as a poly in u is u²·const_in_u),
    U = ‖t̄‖² + ‖D̄·S‖²  (≥ ‖t̄‖² ≥ t̄₀² ≥ 1/4 on the slice {t̄₀ ∈ [½,1], rest in box}),
    |Jac| = u^{8−1} = u⁷   (weighted blow-up of the 8-dim center; 8 = minAdm = 4+4 = block codims).

The binding axis `u` carries `(k,h)=(1,7)` → threshold `(7+1)/(2·1)=4=½·minAdm`. Even when ALL
non-pivot `C¹` entries are also `u`-scaled, `F = u²·U₂ + O(u³)` with `U₂` still bounded below by the
clean `t̄`-block (`/tmp/wedge_gauge_honest2.py`) — and on `u∈(0,δ]`, `F ≤ u²·(U₂ + δ|A| + δ²|B|) ≤
C·u²` (bounded above), giving `|F|^{−c'} ≥ C^{−c'}u^{−2c'}`. Divergence is robust to the slice choice.

**`(2,2,2)` cross-check:** the binding axis is the step-2 pivot `z1` with `(1,2)`, `minAdm−1=2`, the
exceptional vertex `{E=F0=δ=0}` has codim `3 = minAdm` (`/tmp/wedge_single_vs_multi.py`). Matches the
banked `phiUnit` chart and the `monomialThreshold ≤ 3/2` leaf.

## The `L≥3` wedge — the recursive gauge chain (still lighter than the cover)

A single weighted blow-up is a **depth-2 phenomenon** (confirms the header's "depth-2 miracle"). A
brute search over `{0,1}` weightings of `(2,2,2,2)`'s 12 coords found **0** weightings making every
product entry order-1 with `minAdm=3` scaled coords (`/tmp/wedge_2222_search.py`) — a path can cross
two drops (`u⁴` in that entry) or none. For `L≥3` the disjoint normal form emerges only **after the
Aoyagi gauge**:

    after peeling layer 1 at the achiever rank (C¹ ~ diag(1, δ₁) by the gauge):
        F = ‖Q_row0‖² + δ₁²·‖Q_row1‖²,   Q = C²·C³·…  (a FRESH lower-depth product),

and the achiever recurses on `Q` (`/tmp/wedge_2222_gauge.py`). The blocks chain layer-by-layer; the
multi-radial form `F = Σ_i r_i²·U_i` (disjoint vars, the Watanabe-additive structure certified for
`(3,3,4)` in `verify-r1-diagb-334.md`) holds after the full gauge chain. The multi-radial divergence
transcribes to the **single binding axis** the Lean atom wants via the blow-up `s=u, a=u·w`:

    ∫ s^{c₁−1} a^{c₂−1} (s²+a²)^{−c'} ds da  ──(s=u,a=uw)──►  u^{minAdm−1−2c'} · [finite w-integral],

a single axis `(1, minAdm−1)` (`/tmp/wedge_transcribe.py`). So even for `L≥3` the atom is fed by the
SAME `(1, minAdm−1)` leaf — the chart just takes more steps to build.

**Cost.** The `L≥3` wedge uses the same recursive gauge machinery as the upper-bound cover, BUT only
along the ONE achiever path (all other strata ignored) — so it is strictly lighter than `hfin`.

## Soundness gate (binding) — the wedge GENUINELY achieves the rate

- The `u²·U` factorization is **exact polynomial algebra** in the flat entries (`F − u²·U = 0`
  symbolically for `(3,3,4)`), not an asserted `=⊤`. The divergence is transcribed to the cited leaf
  `monomialIntegrand_lintegral_box_eq_top` via an honest pullback `F∘φ ≤ C·u²` (smaller loss ⟹ larger
  `|·|^{−c'}`), exactly the `(2,2,2)` `leaf_box_div` discipline.
- **`U` bounded below on POSITIVE MEASURE, not just the curve** (Codex's flagged pitfall, Q1): `U ≥
  ‖t̄‖² ≥ ¼` on `{t̄₀∈[½,1], rest in box}` — a positive-measure slice. The clean `t̄`-block alone
  suffices; the corank coupling `‖D̄S‖²` only ADDS to `U`.
- **NOT an overcount** (`/tmp/wedge_reconcile.py`): at `c' < ½·minAdm` the exponent `minAdm−1−2c' >
  −1`, so the wedge integral CONVERGES — the boundary is sharp at `½·minAdm`, consistent with the
  upper bound (no contradiction with `rlctAtOn ≤ ½·minAdm` being false below threshold).

## Corank immunity (Q2) — the wedge is corank-IMMUNE

The lower bound integrand is `F^{−c'}`; smaller `F` makes it LARGER (helps divergence). The corank
coupling makes `F` vanish faster/more, only helping. Concretely `U = ‖t̄‖² + ‖D̄S‖²` is bounded below
by the CLEAN block `‖t̄‖²` alone — the wedge never touches the rank-2 `Δ`-coupling that made `hnode`
unprovable. The trap Codex flagged ("faster vanish, thinner tube") does NOT bite: the tube is the
fixed positive-measure slice `{t̄₀∈[½,1]}`, independent of the coupling. **The lower bound is honestly
general-M and corank-immune** (the route adjudication's premise, now verified).

## hfin / upper bound (Q3) — corank-SENSITIVE; commit to the coupled cover or cite the bound

The `cover_le` field (`routeM_coverLe_of_finiteness`, RouteMCoverLemmas.lean:44) requires: **whenever
the leaf-sum is finite, `∫_U |F|^{−c'} < ⊤`** — a GLOBAL finiteness over the whole box, for `c' <
½·minAdm`. This is precisely the headline's `≥` direction: `rlctAtOn F ≥ ½·minAdm`, i.e. "`½·minAdm`
is the global-min RLCT, no stratum beats the achiever."

- **Corank-sensitive.** Proving the global min must control EVERY stratum, including corank-≥2. A
  threshold-only cover mis-resolves them: for `(3,3,4)` it computes codim `3` (rlct `3/2`), not the
  true `8` (rlct `4`) — `verify-r1-diagb-334.md` §2. A cover built from threshold-only charts gives a
  WRONG/weak bound (`rlctAtOn ≥ 3/2`), and worse, a mis-resolving cover may not validly tile `U` up to
  null (the `∫_U = Σ_leaf` identity fails on the corank stratum), so it is not even a valid `cover_le`.
- **No cheaper route** (`/tmp/hfin_probe2.py`): a global `F ≥ dist(·,fibre)²` bound just relocates the
  problem to the determinantal variety's RLCT = the codim = `minAdm`. No free lunch.
- **Honest options for hfin:** (i) the full **coupled `diag(b)` resolution atlas** covering `U` up to
  null (corank charts resolved correctly — as hard as the route that refuted `hnode`, exactly the
  controller's prior Decision option (ii)); or (ii) **cite** the analytic bound `rlct ≥ ½·codim_min`
  (Aoyagi/Watanabe), the S2-style citation, and keep hfin out of honest Lean.

So the lower/upper asymmetry the route adjudication conjectured is **confirmed**: hdiv is
corank-immune (one wedge), hfin is corank-sensitive (genuine cover). The honest move is to commit to
Aoyagi's coupled-`diag(b)` recursion as the chart producer for hfin (BOTH bounds at `L≥3` use it; the
wedge only borrows the achiever path of it), OR cite the `≥` bound.

## Build-ready statement for the formaliser

`routeMCore_box_diverges_achiever M hpos c' hc' ε hε` — for `c' ≥ ½·minAdm M`, `∫⁻_{cubeBox (routeMAmbient M) ε} |routeMCore M|^{−c'} = ⊤`. Discharge via the `(2,2,2)` template (`routeM222_box_diverges`):

1. **The achiever chart `φ_M : (Fin N → ℝ) → (Fin N → ℝ)`** (the weighted blow-up for `L=2`; the
   recursive gauge chain for `L≥3`), with `φ_M(0)=0`, continuous, and `φ_M '' (box [0,δ]^N) ⊆ cubeBox
   N ε` (the `phiUnit_image_subset_cubeBox` analog).
2. **The factorization** `routeMCore M (φ_M u) = u_b² · U_M(u)` with `U_M ≥ c₀ > 0` on the box (the
   `myF222_phiUnit_eq_mul_Uval` + `step2E_unit_ge_one` analog) — and `|det Dφ_M(u)| = u_b^{minAdm−1} ·
   (positive, finite)` (the `step1A_det`/`step2E_det` analog).
3. **The change of variables** (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`, off the null
   pivot-zero loci via `coordZero_null`) → `∫ u_b^{minAdm−1}·|u_b²U_M|^{−c'}`, then drop `U_M^{−c'} ≤
   c₀^{−c'}` and apply `monomialIntegrand_lintegral_box_eq_top` with the single divisor `(1,
   minAdm−1)` (`hk = ⟨b, by decide⟩`, `hc' : monomialThreshold ≤ ofReal c'` from `½·minAdm ≤ c'`).

The simplest first formalisation target: redo `(3,3,4)` (the binding corank-2 anchor) with the single
weighted blow-up, mirroring `Case222RouteMCover`. The general `L=2` weighted blow-up is the next lift;
`L≥3` is the recursive gauge chain (shared with hfin).

## Scope / caveats / what would break this

- **Levels kept separate.** This adjudicates the `rlctAtOn ≤ ½·minAdm` (divergence) mechanism — the
  cover's `cover_ge_div`. The VALUE `⨅ monomialThreshold = ½·minAdm` is already PROVEN
  (`routeLayerAtlas_value`); the `rlct = ½·codim` reading still rides the cited S2 bound.
- **Verified EXACT:** the `(3,3,4)` `F = u²·U` factorization (pure degree-2 in `u`, flat coords); the
  binding-axis exponent `−1` for all `minAdm`; the `(2,2,2,2)` weighting non-existence (search, 0
  hits); the multi-radial→single-axis transcription; `U` bounded below on a positive-measure slice.
- **Inference (structural, NOT a closed certificate):** that the `L≥3` recursive gauge chain produces
  the disjoint `Σ r_i²U_i` form for EVERY M (verified for `(3,3,4)` `L=2` exactly and `(2,2,2,2)` one
  gauge step; the full chain rests on the Aoyagi-Lemma-2 disjointness, certified for `(3,3,4)`, not
  re-proven for arbitrary depth). The MC RLCT estimates (`(2,2,2)`≈1.38, `(3,3,2,2)`≈1.19) are GUIDES
  only, undercounting at high RLCT — not load-bearing.
- **The one thing most likely to break the BUILD (not the math):** the `L≥3` gauge chain's Jacobian
  composition (the header's "triangularity loss"). The math is sound (the disjoint blocks commute);
  the Lean cost is real. **Mitigation:** ship `L=2` first (single weighted blow-up, clean Jacobian
  `u^{minAdm−1}`, no triangularity), which already covers the binding corank-2 family and the headline
  obstruction `(3,3,4)`. The `L≥3` chain is the same machinery hfin needs anyway.
- **Next construction:** the explicit general-`L=2` weighted blow-up chart (the `(3,3,4)` worked case
  lifted to `(M₀,M₁,M₂)`), with the Jacobian-`u^{minAdm−1}` lemma — the formaliser's first target.
