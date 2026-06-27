# Producer (d')/(e') — the `Rcore ↔ deepestCoreAbsorb` block-LDU identity (pinned)

The hproducer's last structural piece (front-pivot route, (b)-exact, S5a/leak banked). The
decomp-cert under-specified (iv) as "pure wiring to `schur_core_germ_comparability`" — it needs ONE
unbuilt structural bridge first: tying the producer's GLOBAL Schur `Rcore` (from the framed-product
blocks) to `deepestCoreAbsorb`'s per-layer cutoff-Schur core. Pinned build-ready; decorrelated Codex
(xhigh) independently agreed on every point. Read-only.

## Q1 — the EXACT relationship: `Rcore = S0·W·S1`, NOT `= ∏S`; S5c charges the difference

`Rcore(w) = P11 − P10·P00⁻¹·P01` (the producer's global Schur, M×M, from the framed-telescoped product's
blocks). By the banked S5c block-LDU (`schur_core_germ_comparability`, the `R = S0·W·S1` form):

    Rcore = S0·W0·S1·W1·…·S_{L-1},   W_k = I − Z_{k+1}·A_k⁻¹·Y_k → I  (the middle factors).

It is **NOT** `= ∏S = S0·S1·…` (the per-layer Schur product) exactly — the difference is the middle
factors `W_k`. Front pivot makes the telescope clean and `W_k → I`, but does NOT make `W_k = I` on a
neighborhood (only at w0 / under stronger vanishing). **So (d')/(e') closes via the S5c GERM CHARGE, not
an exact equality:**

    |frobSq(Rcore) − frobSq(∏S)| ≤ C · Sreg    on a 𝓝 of w0    [the S5c atom output]

This is the in-sum form (NOT a standalone `frobSq(Rcore) ≍ coreΦ`, which fails when both are tiny vs
Sreg — the S5c germ lesson). It closes (d')/(e') at γ₁=γ₂=1+C (verified, below).

## Q2 — the route + the ONE new structural identity

`coreΦ = ‖∏S‖²` (Q3, exact) and the S5c atom gives the germ charge on `Rcore = S0·W·S1`. The bridge has
three steps; only the THIRD is new:

1. **(b)-exact reconstruction (BANKED, front-pivot route):** the producer's blocks `P00,P01,P10,P11` =
   the blocks of `reindex(rThr, rThr)(P0·(∏A−B)·QL)` = (by (b)-exact, front pivot) the blocks of the
   framed telescoped product `reindex(rThr,rThr)(∏ framedParamsPivot)` built from the per-layer
   `fromBlocks X_s Y_s Z_s T_s`. (The clean telescope `endpoint_telescoping_eq` applies — front pivot.)
2. **S5c block-LDU (BANKED, `schur_core_germ_comparability`):** applying the Schur complement to the
   framed telescoped block product gives `P11 − P10·P00⁻¹·P01 = S0·W0·…·S_{L-1}` with
   `S_s = T_s − Z_s(1+X_s)⁻¹Y_s`, and the germ charge `|frobSq − frobSq(∏S)| ≤ C·Sreg`.
3. **NEW — `rcore_eq_schurLDU` (the identification):** the producer's NAMED `Rcore = P11 − P10·P00⁻¹·P01`
   (P00,P01,P10,P11 the producer's block-decomp outputs) IS the S5c atom's input — i.e. the S5c atom
   must be applied to the SAME framed-telescoped blocks the producer named. This is a definitional/`rfl`-
   adjacent rewrite IF the producer's blocks and the S5c atom's blocks are the same objects (they are,
   both = `toBlocks` of `reindex(rThr,rThr)(∏ framedParamsPivot)` post step 1), but needs the explicit
   `P00⁻¹ = ⅟P00` (Invertible from S5a) reconciliation and the block-name alignment.

**Build-ready new lemma:**

    -- in GaugeChart.DeepestEFullSregComparability (or the producer module — references deepestEFull/coreAbsorb)
    theorem rcore_coreAbsorb_germ_charge (H r hr hL J Pf Qf …) (hfront : J = front) :
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ w in 𝓝 w0,
        |(∑ i j, ((P11 − P10·⅟P00·P01) w i j)^2) − deepestCoreF (deepestCoreAbsorb (split w)).2.1|
          ≤ C · Sreg w
Proof: `deepestCoreF(coreAbsorb…) = ‖∏S‖²` (Q3) ▸ the S5c atom `schur_core_germ_comparability` applied to
the producer's blocks (step 3 identification: the producer's `Rcore` = the S5c `R = S0 W S1`). The atom's
`C` is the operator-norm bound from the `W_k − I` higher-order terms.

## Q3 — `coreΦ = ‖∏S‖²` is EXACT (modulo cutoff)

`deepestCoreAbsorb = coreShearHomeo(schurCutoffShift)`; `coreShearHomeo shift q = (q.1, (q.2.1 + shift, q.2.2))`
(`DeepestGaugeBlocks.lean:373`, ADDS the shift). On the cutoff nbhd (`χ = 1`), `schurCutoffShift =
schurShiftRaw = paramsEquivFlat(M)(s ↦ −Z_s(1+X_s)⁻¹Y_s)`. So:

    (deepestCoreAbsorb (split w)).2.1 = (split w).2.1 + schurShiftRaw
      = paramsEquivFlat(M)(T_s) + paramsEquivFlat(M)(−Z_s(1+X_s)⁻¹Y_s)   [paramsEquivFlat additive]
      = paramsEquivFlat(M)(s ↦ T_s − Z_s(1+X_s)⁻¹Y_s) = paramsEquivFlat(M)(S_s),

and `deepestCoreF(that) = ‖∏ (paramsEquivFlat M).symm (paramsEquivFlat M)(S_s)‖² = ‖∏ S_s‖² = ‖∏S‖²`
(the round-trip cancels). **EXACT** on the `χ=1` nbhd. Subtleties: (a) the cutoff support — the germ
must stay inside `{χ=1}` (already the squeeze's `𝓝 w0`); (b) the `paramsEquivFlat(M)` additive-split +
round-trip rewrites (`map_add` + `symm_apply_apply`), routine. Build-ready sub-lemma:

    theorem deepestCoreF_coreAbsorb_eq_prodSchur (H r hr hL …) :
      ∀ᶠ w in 𝓝 w0,
        deepestCoreF (deepestCoreAbsorb (split w)).2.1 = ∑ i j, ((∏_s S_s) w i j)^2
where `S_s = T_s − Z_s(1+X_s)⁻¹Y_s` (= `schurCorrection`-shifted). Uses banked `coreShearHomeo` add-form,
`schurCutoffShift = schurShiftRaw on χ=1`, `paramsEquivFlat` additivity + round-trip.

## Composition — closes (d')/(e') at γ = 1+C (verified)

The squeeze's core conjuncts are the IN-SUM two-sided (the `core_comparability_squeeze` shape). From the
germ charge `|frobSq(Rcore) − coreΦ| ≤ C·Sreg` (sympy-verified the algebra):

    Sreg + frobSq(Rcore) ≤ (1+C)·(Sreg + coreΦ),   Sreg + coreΦ ≤ (1+C)·(Sreg + frobSq(Rcore)).

So γ₁ = γ₂ = 1+C closes (d')/(e') folded into the squeeze. (NOT a standalone `frobSq(Rcore) ≍ coreΦ` —
that fails the lower bound when both → 0 faster than Sreg; the in-sum form is what survives, the S5c germ
lesson. **Soundness-critical: the producer must consume the IN-SUM charge, not a standalone ratio.**)

## Dependency order (the producer's last piece)
1. `deepestCoreF_coreAbsorb_eq_prodSchur` (Q3, coreΦ = ‖∏S‖², exact on χ=1) — uses banked coreShearHomeo
   add-form + schurShiftRaw + paramsEquivFlat additivity.
2. `rcore_coreAbsorb_germ_charge` (Q2 step 3, the NEW identification: producer's Rcore = S5c's S0 W S1,
   then the S5c germ charge) — uses (1) + the BANKED `schur_core_germ_comparability` + S5a's `⅟P00`.
3. (iv) `eventually_core_comparable` (the decomp-cert's folded (d')/(e')): `Sreg+frobSq(Rcore) ≍
   Sreg+coreΦ` at γ=1+C, from (2). Then the producer assembly (v) folds it via `core_comparability_squeeze`.

## Banked vs new
- BANKED: `schur_core_germ_comparability` (S5c, `R=S0 W S1` + germ charge); `coreShearHomeo` add-form +
  fixes (`DeepestGaugeBlocks`); `schurCutoffShift`/`schurShiftRaw` + `χ=1`-on-nbhd; `paramsEquivFlat`
  additivity/round-trip; S5a `eventually_P00_invertible` (the `⅟P00`); the (b)-exact reconstruction
  (front-pivot, the clean telescope).
- NEW: (1) `deepestCoreF_coreAbsorb_eq_prodSchur` (the coreΦ=‖∏S‖² decode — routine, ~tens of LoC); (2)
  `rcore_coreAbsorb_germ_charge` (the identification + S5c application — the load-bearing piece, the
  block-name alignment + `P00⁻¹=⅟P00` + the S5c-input matching). l2-leak-core's "~several-hundred LoC"
  estimate is dominated by step-2's block-LDU identification (the S5c atom rewrites it, but the
  framed-telescoped-blocks = S5c-input-blocks alignment is the genuine glue).

## Build-risk ranking
1. **`rcore_coreAbsorb_germ_charge` step-3 identification** (highest): aligning the producer's named
   `P11−P10⅟P00 P01` with the S5c atom's `R = S0 W S1` input — both are `toBlocks` of the same framed
   telescoped product, but the block-extraction conventions + `P00⁻¹` vs `⅟P00` + the S5c atom's exact
   input signature must match. The math is banked (S5c); the glue is the risk.
2. **`deepestCoreF_coreAbsorb_eq_prodSchur`** (medium): the `paramsEquivFlat(M)` additive-split +
   round-trip + the cutoff `χ=1` localization — routine but several rewrites.
3. **composition** (low): the γ=1+C arithmetic (sympy-verified, `linarith`-shaped).

## Scope (honest)
The `Rcore = S0·W·S1` + germ charge is the S5c atom (exact-certified r=1/H0=1/H2=2 + r=2 matrix-pivot,
germ-scoped, banked). `coreΦ = ‖∏S‖²` is exact (coreAbsorb add-form). The NEW glue (step 3) is an
identification, NOT new geometry — but the block-name/convention alignment is where the LoC lives. NO new
comparability math; it's wiring the banked S5c atom to the producer's named blocks + the coreΦ decode.

## Files
- `/tmp/rcore_compose.py` (the γ=1+C composition + the coreΦ=‖∏S‖² decode chain). `codex/rcore-coreabsorb-
  {prompt,answer}.md` (decorrelated, agrees). The S5c atom: `s5c-cert.md` + `s5c-r2-cert.md` (banked).
