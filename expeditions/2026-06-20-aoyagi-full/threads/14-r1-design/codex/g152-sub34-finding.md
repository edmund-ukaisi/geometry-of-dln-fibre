# #44c sub-34 route finding (fm-sub34, 2026-06-22) — the gauge-normalization squeeze trap

## The question
Discharge `deepest_gauge_chart_exists` (populate `DeepestGaugeChart`). Before sinking 600-1500
lines into the literal `chart ≃ₜ` + `Dchart` + `HasFDerivAt` + `jac_unit` measure-Jacobian, is that
machinery actually NEEDED, or is the structure over-specified relative to a squeeze route?

## The decorrelated reads (Claude exact-numeric + Codex xhigh — CONVERGED)

1. The downstream RLCT split (`rlctAt = nReg/2 + reduced-core RLCT`) needs only same-domain germ
   comparability + a measure-preserving product reindex + spectator-peel + `rlct_additive_smooth_block`.
   The `Dchart`/`HasFDerivAt`/`jac_unit` **measure-Jacobian** fields are DEAD WEIGHT for the split.

2. **Codex independently flagged a SOUNDNESS concern with the current structure:** `chart : Flat ≃ₜ Flat`
   with `hasDeriv : ∀ x, HasFDerivAt chart (Dchart x) x` is asserted GLOBALLY, but block-elimination /
   the gauge slice is only defined LOCALLY near invertible blocks (the (0,0) block ≈ I_r). A global
   self-homeomorphism of flat space with an everywhere derivative may be UNbuildable as stated (or
   buildable only by an artificial global extension that does not match the cert geometry).

3. **THE TRAP (load-bearing, exact-numeric + Codex agree).** The CORRECTED cert core is the
   GAUGE-NORMALIZED `‖T̃₁···T̃_L‖² = ‖T·(I−VY)⁻¹·S‖²`, NOT raw `‖T·S‖²`. The naive squeeze
   `Φ₀ = ∑E² + dlnLoss M 0 (RAW T)` is **FALSE for matrices**: `g=(I−VY)⁻¹` sits BETWEEN T and S (not a
   scalar), so it maps a `TS=0` direction to `TgS≠0` — ratio `‖TgS‖²/‖TS‖²` → ∞ as `TS→0` with `g≠I`
   (verified: T=[[1,0]], S=[[0],[1]], g=I+εN gives ‖TS‖²=0, ‖TgS‖²=ε²). So you CANNOT squeeze the loss
   against the raw reduced chain. The scalar (2,2,2)r1 case hides this (everything 1×1, g scalar).

## The resolution (what the structure's `loss_form` ALREADY encodes correctly)
`loss_form` lands on `dlnLoss M 0 ((paramsEquivFlat M).symm q.2.1)` where `q.2.1` are the CORE coords.
For this to be clean `dlnLoss M 0`, the core coords MUST be the gauge-normalized `T̃` blocks — the
change of variables must ABSORB `g` into the reduced coordinates. The g-absorption is a genuine
NON-MP c-o-v on the reduced block: for fixed V,Y, `T̃ = T·g(V,Y)` is LINEAR in T with
Jacobian det `= det(g)^{M0} = det(I−VY)^{−M0}` — a UNIT ≠ 1 (matches the cert's
`det(A)^{−(r+M2)}·det(B)^{−M0}`).

## Two honest routes (the chart is NOT eliminable; the measure-Jacobian half MIGHT be)
- **R-germ-MJ** (structure as-is): literal `chart ≃ₜ` + `Dchart` + `jac_unit`, germ-pullback
  `loss∘chart` + measure-peel of `|det Dchart|`. The 600-1500 line obligation. Codex's soundness
  flag (global ∀-hasDeriv) bites here.
- **R-squeeze-T̃** (proposed): the c-o-v that absorbs g into T̃ is a UNIT-Jacobian map; transport its
  RLCT contribution by `rlctAtOn_unit_invariant_aux` on the REDUCED factor (peel `det(g)^{M0}`),
  NOT `comp_homeomorph`, NOT a measure-Jacobian of a global chart. Combined with the spectator-peel
  (task #52) and `rlct_additive_smooth_block`. NO `Dchart`/`HasFDerivAt`/global-`jac_unit`.

## Recommendation
Propose to crux2 (owns the consuming interface + sub-5): TRIM `DeepestGaugeChart` of the
`Dchart`/`hasDeriv`/`jac_unit` measure-Jacobian fields. Keep `split`/`split_mp`/`split_zero` (MP
reindex) and a `chart`-or-equivalent germ datum, but replace the measure-Jacobian peel with a
unit-Jacobian-on-the-reduced-factor squeeze/unit-strip. The structure decision is crux2's; this is
the surfaced confound + recommendation, NOT a unilateral rewrite.

## The single most-likely sink (whichever route)
The matrix comparability `‖T·g·S‖² ≍ dlnLoss M 0` via the g-absorbing c-o-v: making the absorption a
clean Lean map (bijection of the reduced block for fixed V,Y) whose unit Jacobian is peelable, WITHOUT
the global ∀-hasDeriv. This is the one new obligation either route must discharge.

## ADDENDUM (after reading weightedThreshold_transport / S1.1) — PARTIAL SELF-CORRECTION

The cert names `weightedThreshold_transport` (S1.1, ALREADY PROVEN) as the transport. Its docstring
records (Codex-caught, pp-verified): the UNWEIGHTED `rlctAt(F∘π) = rlctAt(F)` is **FALSE** for a
genuine diffeo — `F=x²+y²`, chart `(u,uv)` gives `1/2 ≠ 1`, the missing factor being exactly
`|det Dπ| = |u|`. So the regular-RESIDUAL coordinate change `E = product residuals` (a genuine
nonlinear diffeo of flat space) CANNOT be transported for free — it needs the `|det Dπ|`-weighted
S1.1 transport, then `rlctAtOn_unit_invariant_aux` peels the unit weight (the cert's exact recipe).

⟹ The `Dchart`/`hasDeriv`/`jac_unit` fields are NOT dead weight if sub-5 transports via S1.1: they
ARE the `Dπ` and the `|det Dπ|`∈[a,b] bound S1.1 + the unit-peel consume. My FINDING-1 "dead weight"
was too strong — it holds ONLY for the pure-squeeze route (which does NO coordinate change, comparing
loss vs Φ at the SAME flat point).

So the real fork is sharper than I first said:
- **R-S1.1** (structure as-is): build `chart` (a proper a.e.-diffeo of flat space) + `Dchart` +
  `jac_unit`, transport via `weightedThreshold_transport` + unit-peel + germ (`loss_form`). The
  chart/Dchart/jac_unit are LOAD-BEARING. Codex's global-∀-hasDeriv soundness flag must be addressed
  (the diffeo is global; block-elim is local — but S1.1 ALLOWS a null exceptional set `E` and only
  needs `π` proper + injective + differentiable OFF `E`, so a global proper extension with a null
  bad-set may suffice — this SOFTENS the soundness flag).
- **R-squeeze** (no chart): compare `loss` vs `Φ = ∑(flat reg gens)² + ‖core‖²` at the same flat
  point. Avoids S1.1 + Dchart entirely. BUT FINDING-2 stands: the core in `Φ` cannot be the raw
  reduced chain (squeeze false for matrices). The squeeze target's core must already be the
  gauge-normalized chain — and whether THAT is expressible as a clean flat-coord function squeezing
  the loss, without a c-o-v, is the open question.

NET: I retract "Dchart is dead weight" as unconditional. It's dead weight ONLY under R-squeeze, and
R-squeeze has its own unresolved matrix-core question. The structure (R-S1.1) is defensible. Which
route is cheaper is genuinely unclear and is crux2's call (it owns sub-5's transport choice). The S1.1
docstring's null-exceptional-set `E` is the key that may make the global chart sound.

## DEEPEST FINDING (the design decision for the whole #44c) — LOCAL vs GLOBAL

`rlctAtOn` / `weightedThreshold` are LOCAL (a 𝓝 of w*). So the transport MATHEMATICALLY needs only a
chart that is a diffeo on a NEIGHBOURHOOD of w0. But:

- The banked `DeepestGaugeChart` demands a GLOBAL `chart : Flat ≃ₜ Flat` with `∀x, HasFDerivAt`.
- S1.1 `weightedThreshold_transport` ALSO has GLOBAL hypotheses: `IsProperMap π` + `Surjective π`
  (+ injective/differentiable off a null set).
- The actual gauge-slice chart is only a LOCAL diffeo at w0: its inverse uses `A⁻¹ = (I_r+X₁)⁻¹` and
  `(I−VY)⁻¹`, which blow up away from w0 (A singular at `X₁=−I_r`). The forward map `π = ∏C − D` is a
  global polynomial (differentiable everywhere) but is NOT globally injective (gauge redundancy) and
  need NOT be proper (polynomial level sets noncompact).

So there is a GAP between the local reality and the global demands of BOTH the structure AND S1.1.
Three ways to close it, in increasing cost:
 1. **R-squeeze (purely local, NO chart):** compare loss vs Φ on a 𝓝 0 via `rlctAtOn_squeeze` (local
    by construction). Sidesteps the entire local/global problem. Cost: the matrix-core question
    (FINDING-2) — Φ's core must be the gauge-normalized chain, expressed in flat coords without a c-o-v.
 2. **A LOCAL transport variant of S1.1:** `rlctAtOn` of `F∘π` on a 𝓝 where π is a diffeo, with the
    |det Dπ| weight — but stated locally (π a `PartialHomeomorph` / diffeo on the nbhd, not global
    proper+surjective). This lemma does NOT exist yet (S1.1 is global). New analytic lemma to add.
 3. **A GLOBAL proper extension** of the local gauge chart to `Flat ≃ₜ Flat` — a real construction,
    arguably the heaviest, and the source of Codex's soundness flag.

RECOMMENDATION (sharpened): the structure's GLOBAL `chart : Flat ≃ₜ Flat` is the WRONG shape — it
over-reaches relative to what the local RLCT needs AND relative to what's buildable from the local
gauge slice. Either go R-squeeze (purely local) OR re-shape the chart field to a LOCAL diffeo (a
`PartialHomeomorph` on a 𝓝 0) and add the local-transport variant (option 2). The current
global-≃ₜ + ∀-hasDeriv is both over-demanding and (per Codex) possibly unsound to assert. This is
crux2's interface call; I will not write the structure until it's resolved.

## g153 — raw-∏T core REFUTED (Codex caught it before the build)

Tempted by a simplification: skip the Schur complement, use the RAW ∏T core as the squeeze target Φ.
MC evidence looked good (L/Φ→1 as deviation→0). Codex xhigh REFUTED it with an exact counterexample
(verified sympy):
    C1=[[1,0],[−ε²,ε]], C2=[[1,ε],[ε,0]], C3=[[1,−ε²],[0,ε]]  ⟹  C1C2C3 = blockdiag[1, −ε⁴].
So ∑E²=0, raw ∏T = ε·0·ε = 0 (interior T2=0), but P11 = −ε⁴. Hence loss=ε⁸, Φ=0 — the upper
squeeze loss ≤ c₂·Φ=0 is IMPOSSIBLE. The clean lemma |‖P11‖²−‖∏T‖²| ≤ K·∑E² is FALSE (LHS=ε⁸, RHS=0).

WHY it fails: "carries a regular factor" ≠ "charged by E". A zero interior reduced block (T2=0) can
produce a nonzero product P11 via gauge interactions that CANCEL in the three regular residuals E.
The MC missed it because the configuration is a measure-zero coincidence (exact cancellation in E).

⟹ The Schur / gauge-normalized core (sub-lemmas 1a #53 + 1b #54) is REQUIRED — not eliminable. The
g-absorption / Schur complement R = P11 − E10(I+E00)⁻¹E01 is load-bearing. GOOD NEWS: the
GeneralR1Recursion bedrock `schur_row_decomp` + `schur_lossDiff_eq_cofactor` (already-proven CommRing
matrix identities) ARE the Schur-complement content — sub-lemma 1a is a specialization, not a rebuild.
Lesson reinforced: MC guides, exact algebra adjudicates; the "too clean" simplification was the trap.

## VERDICT (controller's route-reopen question) — chart collapses YES; coreEmbed fix needed

Controller asked: does a squeeze sub-5 eliminate the chart? Read crux2's PROVEN sub-5 + sub-6:

**YES, the chart collapses.** sub-5 (`deepest_squeeze_transport`, PROVEN) uses ONLY `Γ.split`
(continuity), `Γ.loss_squeeze`, and the `paramsEquivFlat-H` MP transport. No `chart`/`Dchart`/`jac_unit`
(gone in the trimmed structure). So the XL chart-existence (cutoff-extension/Dchart/jac_unit/loss_form
germ) is ELIMINATED. sub-3 (`deepest_gauge_squeeze_exists`) now only produces
`nGauge`/`split`/`split_mp`/`split_basepoint`/`loss_squeeze`. My job shrinks to: the comparability
(banked, `DeepestGaugeBlocks`) + the `split` MP reindex + the `loss_squeeze` assembly.

**BUT a consistency bug gates sub-3.** sub-6 (`deepest_regular_smooth_split`, PROVEN) calls
`rlctAtOn_comp_homeomorph Γ.split Γ.split_mp` ⟹ `split` MUST be measure-preserving. MP `split` (det 1)
⟹ `(split w).2.1` is a linear reindex of raw flat coords ⟹ the `Φ`-core
`dlnLoss M 0 ((paramsEquivFlat M).symm (split w).2.1)` is the RAW `∏T` core — which g153 REFUTED. So
`loss_squeeze` is FALSE as the structure stands; sub-3's `sorry` is currently a FALSE statement.

g153 applies AT the deepest point (confirmed): the CE `C1C2C3 = blockdiag[1,−ε⁴]` has max layer
deviation `= ε → 0`, so it is in every neighbourhood of `w0`; `rlctAtOn` integrates the full nbhd
(incl. full-rank points like the CE's rank-2 `C2`). So the refutation is genuinely at `w0`.

**FIX (crux2's structure call, minimal):** add a field
`coreEmbed : (Fin (flatDim M) → ℝ) → Params M` (the g-absorbing reduced reparametrization), change
`loss_squeeze`'s `Φ`-core to `dlnLoss M 0 (coreEmbed q.2.1)`. Then `split` stays a pure MP reindex
(sub-6 unchanged), the g-absorption (`det(I−VY)⁻ᴹ⁰`, a bounded unit) lives in `coreEmbed` and is peeled
in sub-7 via crux2's PROVEN `weightedThreshold_weight_unit_invariant` (replacing the plain
`paramsEquivFlat-M comp_homeomorph`). `loss_squeeze` becomes TRUE — the comparability is the banked
Schur split (`P11 = R + leak`, `R = ‖T̃-chain‖² = dlnLoss M 0(coreEmbed core)`, leak ∈ ideal(reg) ⟹
`schur_node_squeeze_unif`). Sent to crux2 + controller. Held sub-3 assembly for the coreEmbed fix.

## g154 — MP-split exact germ: dischargeable in principle, but coreEmbed is the right route

crux2 added `ofExactGerm` (MP split + EXACT germ `loss =ᶠ ∑reg² + dlnLoss M 0((paramsEquivFlat M).symm core)`,
c₁=c₂=1). I first claimed it undischargeable; Codex (xhigh) refined:

- **Dischargeable IN PRINCIPLE if dim spec > 0:** the non-MP gauge chart (det = the g-unit) can be
  composed with a spectator reparametrization `h(reg,core,s)` whose fiber Jacobian cancels the volume
  density — `NF ∘ H = NF` while `H` corrects the density. No RLCT/Newton/multiplicity obstruction forces
  det=1; the unit only changes the measure density.
- **BUT the Lean-cheap path is (b): `coreEmbed` + a bounded-unit Jacobian-weight invariance lemma.**
  Building the volume-preserving MP split is standard maths but Lean-expensive (global Homeomorph +
  monotone integral inverse + product-Lebesgue MeasurePreserving proof). The coreEmbed route peels the
  g-unit as a bounded positive weight — much cheaper, and it reuses crux2's PROVEN
  `weightedThreshold_weight_unit_invariant`.
- **CAVEAT (decisive):** the spectator-compensation needs dim spec > 0. `nGauge = 0` for **ALL L=1
  cases** (verified: scan — single layer, no interior gauge freedom). So the MP-split route GENUINELY
  FAILS for L=1; the coreEmbed/unit-peel route works for all L (incl. nGauge=0).

NET (reconciled, decorrelated): the chart collapses (controller confirmed); `ofExactGerm` with an MP
split + hardcoded raw `(paramsEquivFlat M).symm` core is the wrong target (impossible at L=1, expensive
otherwise). The right target is `coreEmbed` (g-absorbing reduced map) + peel the g-unit in the
reduced-core transport. My banked Schur bedrock (`DeepestGaugeBlocks`) IS the coreEmbed content
(`R = ‖T̃-chain‖²`). This is crux2's structure call; I've recommended it twice now with the L=1
nGauge=0 evidence. The comparability itself (the load-bearing obligation) is route-final and banked.

## g156 — the LITMUS (controller's decider): per-layer-UNIT core FAILS; need per-layer SCHUR

Controller's litmus: run g153 C1C2C3=blockdiag[1,−ε⁴] through design-D Φ. Result (exact + Codex xhigh):

- design-D Φ = ∑E² + deepestCoreF((coreAbsorb(split w)).2.1). At g153: ∑E²=0.
- IF coreAbsorb is the per-layer UNIT `T_s ↦ T_s·(I−V_sY_s)⁻¹`: the raw T_s = (ε,0,ε) [the (1,1)
  entries], ∏T̃ = ε·0·ε·units = 0 ⟹ Φ = 0. But loss = ε⁸. UPPER SQUEEZE loss ≤ c₂·0 = 0 FAILS.
- The CORRECT core is the per-layer SCHUR complement `S_s = T_s − Z_s(I+X_s)⁻¹Y_s` (NOT the unit
  `T_s·(I−V_sY_s)⁻¹`). On {E=0}: R(full Schur)|_{E=0} = t1·(t2−zy)·t3 = ∏S_s (verified sympy, diff=0).
  The middle factor S2 = t2−zy carries the `−zy` Schur correction the per-layer-UNIT misses.

So Codex verdict (C): deepestCoreF(core) = ‖S1·S2···SL‖² on the per-layer SCHUR-reduced layers
S_s = T_s − Z_s(I+X_s)⁻¹Y_s = dlnLoss (H−r) 0 of the Schur-reduced tuple. NOT raw T_s·unit (g153-false),
NOT the full-vars R (depends on reg coords — not core-only for the additive split). The route:
loss ≍ ∑E²+‖R‖², R = G(core) + ∑E_i·H_i (reg dependence ∈ ideal(E), bounded), so ∑E²+‖R‖² ≍ ∑E²+‖G(core)‖²
with G(core) = ‖∏S_s‖² core-only; rlct_additive_smooth_block applies to G(core).

⟹ CERT-FIDELITY for design D: is crux2's coreAbsorb the per-layer UNIT (g153-unsound) or the per-layer
SCHUR complement S_s = T_s − Z_s(I+X_s)⁻¹Y_s (correct)? If unit, coreAbsorb is the wrong map. My banked
schur_P11_decomp (full Schur R) is the FULL-product object; the per-layer S_s is the right per-slot
object, and ∏S_s = R|_{E=0} (they agree on the reduced locus, differ off it by the reg-ideal leak).
Settle with crux2 before transcribing — controller's "resolve via the g153 litmus" directive.

## g157 — coreAbsorb factors as (a) MP shear + (b) non-MP inter-layer unit (Codex xhigh)

Probing coreAbsorb's construction surfaced a TWO-PART structure (Codex confirmed, exact):
- **(a) per-layer Schur shear** `T_s ↦ S_s = T_s − Z_s(I+X_s)⁻¹Y_s`: ADDITIVE, triangular in
  (T_s, X_s,Y_s,Z_s) with identity on the T_s diagonal ⟹ Jacobian det = 1 ⟹ MEASURE-PRESERVING. The
  cert's "non-MP det(I−VY)⁻ᴹ⁰" does NOT apply to this additive shear (it was about the wrong
  multiplicative-unit form). coreAbsorb_rlct for the shear ALONE is trivial (rlctAtOn_comp_homeomorph).
- **(b) inter-layer interstitial unit**: the loss core is the FULL-PRODUCT Schur
  R = P11 − P10·P00⁻¹·P01, NOT ∏S_s. For 2 layers Schur(C₁C₂) = S₁·(I + G·E⁻¹·A⁻¹·B)⁻¹·S₂ — an
  interstitial unit remains between the per-layer Schur blocks. So ∏S_s = R|{E=0} is a {E=0}/scalar
  ACCIDENT, NOT a general matrix identity (verified: 2-layer matrix, ‖R−∏S‖≈0.0009 ≠ 0 off {E=0}).

⟹ coreAbsorb (raw T-tuple → the core whose dlnLoss M 0 = ‖R‖² = loss core) factors as:
  (a) MP shear T→S (free, comp_homeomorph) THEN (b) the non-MP inter-layer unit absorption (∏S_s → R,
  the det(I−VY)-style unit between layers — THIS is where the cert's non-MP peel genuinely lives).

So my core_comparability_squeeze (loss ≍ ∑E²+‖R‖², R = full-product Schur) is the CORRECT target —
R, not ∏S_s. The coreAbsorb_rlct field's non-MP peel is needed for (b) (the inter-layer unit), NOT (a).
The simplification: (a) is free; the non-MP machinery is only for (b), and the loss core is R (my banked
comparability is right). Net for the build: coreAbsorb's core-output = R (full Schur), reached by
(a) shear + (b) inter-layer-unit; coreAbsorb_rlct peels the (b) unit via weightedThreshold_weight_unit_invariant.
DON'T identify ∏S_s with R (the danger Codex flagged). My #54 R is the right object; ∏S_s is not.
