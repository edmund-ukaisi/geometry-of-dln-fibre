# Regrounding — fresh-eyes cartographer (2026-07-23)

Convened independently at the operator's request ("treadmill or local min again?"). Read-only;
kernel + math first; no inherited controller model. Verdict cross-checked and CONFIRMED by the
controller (2026-07-23), who sharpened finding 4 (see the WALL note below). Tags: **VERIFIED** = a
command I ran; **INFERRED** = reasoning; **SUSPECT** = needs a decorrelated adjudication.

## Verdict (one line)
TREADMILL confirmed on the integration branch; a distinct LOCAL-MIN is SUSPECTED at the *encoding*
level (the geometric-fold KILL/support machinery), NOT at the objective (the geometric resolution is
genuinely necessary).

## 1. Math-first — what the proof must build; is the code faithful/necessary
Paper (`theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:501–649`, VERIFIED by reading):
after the deepest-point reduction (zero-product, r=0) the core is `rlct₀⟨∏_s C^{(s)}⟩`. The resolution
is an iterated blow-up indexed by (S,J) maintaining an **IDEAL IDENTITY** (:562–567)
`⟨∏C⟩ = ⟨diag(b₁..b_{M(S)})·[[E_J,O],[O,D_J]]·∏_{s>S}C⟩`, the `bᵢ` monomials in exceptional coords
`u_{s,k}` with `b₁|…|b_M` by construction; terminally fully diagonal, `‖∏C‖²=∑bᵢ²` = normal crossing
(:574–577); Jacobian `u_{s,k}^{M_{s,k}−1}`, so `rlct=½·min M_{s,k}` (:589–594). Step = Cases 1&2
(:609–629): blow up a determinantal center, then **regular (unimodular) Q,P** reduce `D_J→[[1,O],[O,D_{J+1}]]`.
Cross-term drop is **ideal membership by inspection** — `F₃F₂` is literally a product of the regular
generators `{C₁−E_r,F₂,F₃}`, and rlct is the ideal invariant, so it drops (:466; controller-sharpened).

- **Faithful?** YES at structure level (VERIFIED, `Core/Aoyagi/ProductResolution.lean:62–139`): `Chart`
  carries analytic `g`, `bexp` (k≡1=`hunit_mult`), `jac` (`M_{s,k}−1`, certified vs `|det Dg|` by `hjac`),
  `hchain`, `hideal_fwd/bwd` (the ideal identity for pulled-back gens), birational `hg_inj`, `Resolution`
  adds localizing `hcover`. No structural drift.
- **Necessary?** YES (INFERRED, math): `⟨∏C⟩=⟨diag(b)⟩` with `bᵢ` monomial exists ONLY in exceptional
  coords (original `⟨∏C⟩` is determinantal, not monomial; Object C needs monomial gens). The ideal route
  A+C+D cannot dodge the coordinate change — the resolution IS the monomialisation. **Monument is the
  right KIND of object; not a local min at the objective.**
- **The drift (SUSPECT — local-min candidate):** paper maintains an IDEAL IDENTITY via ideal-preserving
  regular Q,P + ideal-membership drop. Code instead builds a provenance-heavy GEOMETRIC FOLD —
  `FoldStepInvAt`/`canonNormalizationOf`/the KILL (`sourceClearedResid_ignoresEscapedBelow`)/`couplingClear`/
  row-col phantoms (`MonumentAtlas.lean:544–629,1035–1108`). All ~29 fidelity catches cluster there
  (charter §3: 16th/26th/29th, `canonCenterOf` tripwire 3×; compass F6: 10th–12th). Charter's OWN strategy
  is ideal-level (F1/F2). **WALL note (controller-sharpened):** `case1_preserves_stepInv`'s docstring
  (`MonumentAtlas.lean:1518–1526`) records an ideal-membership form (`hsupp=SupportedOn`) was tried and
  refuted — BUT that was membership AFTER the `blockBlowupCoordQuot` coordinate SUBSTITUTION, NOT the
  paper's matrix-level ideal identity. So the history does not refute the suspicion — the substitution
  encoding is what forced the support-tracking.

## 2. True via_engine cone (42 raw → honest partition)
VERIFIED: **42 sorry, 3 axiom** (`scripts/sorries`). 3 axioms all located `@[cited]`
(`cited_watanabe_upper_ax`, `cited_aoyagi_lower_ax`, `cited_local_zeta_pole`) — cordon-clean.
Wire (VERIFIED, `LearningCoefficient.lean:323–332`): `aoyagi_learning_coefficient_via_engine` consumes
`exists_coreResolution` (:327), body refines through sorry-free `RecursionAdapter` to ONE geometric
`sorry` at **:311**. **Wire gap CONFIRMED:** `MonumentAtlas.exists_coreResolution_via_monument` (:1948)
re-proves the identical statement via the leaves but is consumed ONLY by AxCheck's `#print axioms` —
`exists_coreResolution` does not call it. Swapping :311→via_monument RELOCATES the frontier (1 opaque
hole → ~11 named leaves); NOT closure (via_monument carries sorryAx, its own docstring :1943).

| bucket | sorries | where |
|---|---|---|
| via_engine as-wired | **1** | `LearningCoefficient`:311 |
| monument (fills :311) | **~11** | `MonumentAtlas` leaves incl. **L4 WALL `case1_preserves_stepInv`:1532** (coupled corank≥2), L5:1791, L6:1821, L7:1855, L8:1882 |
| monument wiring (integ.) | **~5** | `LastLayerWire` 2, `CanonShear` 1, `MergeBoostSplit` 1, `MonumentAssembly` 1 |
| relocated on seats | **~16** | `SourceClearedResid` 6, `ClearedFold` 8, `CapDescent` 2, `LeafCoverTiling` 2 (dedup ~10–14) |
| literal-name/hbox (aoyagi-full's, F7) | **20** | `RouteM*` 17 + `Skeleton` 3 — registered root `aoyagi_learning_coefficient` (AxCheck:1385), OFF this objective |
| pure fossils (retired chart Engine) | **5** | `Engine/{CanonicalWitness224,ClearableReify,GeoAlphaGauge,GeoAtlasTransfer}` 4 + `DeepestGaugeChart` 1 |

Live via_engine frontier ≈ **17** on integration (heart = ~11 MonumentAtlas leaves); **~25 of 42 (60%)
are off-this-expedition.** `RecursionAdapter` (combinatorial half) is sorry-free — frontier is purely the
geometric `AtlasRealizesExponents`.

## 3. Treadmill evidence (quantitative, VERIFIED)
- Census flat **489→495 sorry-lines / 260 commits / ~15h** (2026-07-23 08:05→22:54; robust
  `git grep -w sorry` minus comment lines — absolute differs from the 42-token count; the FLATNESS is the
  datum, matches controller's "~660 flat").
- **78% of last 120 commits journal-only** (94/26).
- **Seats relocate, don't close:** every active #73 seat total census HIGHER than integration (495→499–507);
  none reduces `MonumentAtlas` (~15); new modules carry 6/8/2/2 sorries; L4 WALL open on every active seat
  (only stale `L4C`, behind=549, shows MA~11).
- 30+ seat branches, most **167 commits behind**, not rebasing.
- **#73 is mis-framed as "the keystone that greens the build"** — it is bookkeeping that RAISES the visible
  cone and leaves the L4 WALL open. The real keystone = the L4 WALL + the encoding decision.

## 4. Close-out sequence (ranked)
1. **(controller executing) Settle the encoding fork BEFORE more grinding** — pen-and-paper: does Aoyagi's
   matrix-level ideal-identity invariant (worked.tex:565), via ideal-preserving Q,P + membership-drop (:466),
   discharge the per-leaf StepInv WITHOUT the geometric KILL/couplingClear/row-phantom machinery? YES ⟹
   KILL/`SourceClearedResid`/`ClearedFold` scaffolding is the local min → re-architect leaner. NO ⟹ monument
   confirmed → grind, treadmill is pure process. Decorrelated panel: fresh-carto + elder + pnp-ideal.
2. **(my step ii, after fork) Clear the census signal:** prune the 5 chart-Engine fossils; quarantine the 20
   literal-name/hbox sorries (operator-gated — touches #94 definition-of-done). 42 → ~17; convergence
   measurable. Plus the ~30-branch triage (dead/merged/superseded vs live).
3. Only after (1): wire :311→via_monument to make the frontier honest (~11 named leaves). Bill as
   bookkeeping that RAISES the count; not progress.
4. Close leaves in dep order, CLOSING not relocating: L3T atoms → **L4 WALL (coupled corank≥2)** → L5 →
   L6/L8 → L7 cover. Gate each seat on **census-DROP on the via_engine cone**, not commit count.
5. Literal-name #94 residual: close-phase, operator-gated.

**STOP:** review-loop churn on L7/KILL before (1); new-seat spawning; journal-tick-as-progress; calling #73
the keystone.

## Caveat on this evidence
I did NOT run a full build / `#print axioms` (read-only, time). Cite-dodge is STRUCTURALLY verified
(`two_mul_rlctAt_eq_cCodim` clean-three per AxCheck:1331–1339; `RecursionAdapter` sorry-free; only sorry is
geometric existence) but not kernel-reconfirmed here — worth one re-run before trusting "cite genuinely dodged".

## Re-run commands (for cross-check)
- census: `cd lean && python3 scripts/sorries | tail -3`
- trend: `for off in 0 60 120 200 260; do sha=$(git log --format=%h expedition/aoyagi-engine | sed -n "$((off+1))p"); git grep -w -h sorry $sha -- lean/DLNFibre | grep -vE '^\s*--' | grep -c sorry; done`
- commit ratio: `git log --format=%s expedition/aoyagi-engine | head -120 | grep -cE '^journal'`
- seat census: `for b in KILLFIN CAPR GM CFF; do git grep -w -h sorry expedition/aoyagi-engine-$b -- lean/DLNFibre | grep -vE '^\s*--' | grep -c sorry; done`
- wire gap: `grep -rn exists_coreResolution_via_monument lean/DLNFibre --include=*.lean | grep -v '^\s*--'`
