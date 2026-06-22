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
