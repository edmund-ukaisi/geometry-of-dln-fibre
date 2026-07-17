# Overlay — banked-family cards (cartographer, curated layer)

*The banked substrate the engine CONSUMES (never rebuilds — "survey before commissioning", compass
standing counsel). One card per family: what it gives, what it assumes, the exact names, near-misses.
Created pass #1; sorry counts verified against the live tree. All paths `lean/DLNFibre/DLN/RLCT/…`.*

## Transport family (Q5 route (b)'s engine)

**What it gives.** RLCT invariance under a local-homeomorph change of variables — the mechanism
`region_glue` uses to pull each blow-up chart back to the banked monomial atoms.
- `rlctAtOn_boundedUnit_localHomeomorph` (`Foundations/S1NonMPTransport.lean:292`) — the 0-sorry
  LOCAL-homeomorph transport (proper, not globally injective — fits blow-up charts; the global-injective
  variant does NOT fit).
- `weightedThreshold_le_transport` (`Foundations/S1Transport.lean:88`) — the ONE-SIDED (`≤`) transport,
  sorry-free; one-sided finiteness suffices for the box (compass fork 8). `weightedThreshold_transport_aux`
  (full equality) also sorry-free.

**CORRECTION to the charter's "S1Transport 2-sorry caveat" (VERIFIED FALSE).**
`Foundations/S1Transport.lean` has **ZERO real `sorry` tokens** — a `grep sorry` returns 2 lines, but
BOTH are the word "sorry-free" inside the module docstring (lines 14, 18). The whole transport family is
sorry-free: `S1Transport`, `S1NonMPTransport`, `S1ChartTransfer`, `S1QuasiSplit` all 0 real sorries. The
only transport-space open piece is `RouteMSJTransport.lean` (1 real sorry) — a general-composer piece,
not the boundedUnit transport. Any note claiming "S1Transport carries 2 sorries" is a miscount of
"sorry-free" and should be repointed.

**What it still needs (P8 gap).** The ONE new analytic lemma: the homogeneity scaling bridge
`∫_{εK} F^{-c'} = ε^{N−2Lc'} ∫_K F^{-c'}` (its degree-2L homogeneity input banked — see homogeneity
family). Route (b) collapses the P8 composer gap to this single lemma.

**Guards (compass fork 8).** circularity (transport gives INVARIANCE only — no path may consume
`rlct=c*` / `cited_aoyagi_dln`); no-laundering (transport hypotheses DISCHARGED from the construction,
never relocated to fresh holes); edge data = the monomial ledger, never opaque derivative fields.

## `ParamsFlatLinear` (the normed-`Params` bank)

**What it gives.** `Foundations/ParamsFlatLinear.lean` — the `NormedAddCommGroup`/`NormedSpace`
instances on `Params M` + a CLE + fderiv, rfl-compatible topology. 0-sorry, 13 consumers, built expressly
to close the "Params not normed" blocker. **Near-miss / lesson:** the Q5 "no normed Params" probe ran
WITHOUT importing this — the false-premise fork (see [[dead-routes]]). Any fderiv-over-`Params` design
imports this first.

## minAdm / QIP arithmetic family (the combinatorial budget)

**What it gives.** The whole banked combinatorial budget — consume verbatim, never re-derive.
- `RouteMLayerSplit.lean` — `minAdm` / `minAdmRec` (`minAdmRec_eq_minAdm`); `minAdm_le_Mval` (the
  minAdm-as-minimum direction `exponent_ledger_bridge` and `theorem4-localization` need — NOT
  `MinAdmMono`, see [[dead-routes]]).
- `RouteMSJCorankRec.lean` — the QIP family (the quadratic integer program form of minAdm).
- `MinAdmCCodim`, `MinAdmPermInvariance`, `RouteMSJDecoratedCharge` (peelCharge). `MinAdmMono` exists but
  is the WRONG direction for threshold preservation.

**What it assumes.** Nothing new — these are closed. `minAdm_M224 = 4` (`decide` via `minAdmRec`) and
`minAdm_rr4_eq` (:88) are the concrete reads the witnesses use.

## Homogeneity family (theorem4 far-point + the scaling bridge input)

**What it gives.** The exact homogeneity-scaling CoV that dominates non-deepest / far points.
- `deepest_le_of_homogeneous_core` (`Validate/DeepestMinRlct.lean:157`) — the deepest domination,
  ALREADY BANKED HYPOTHESIS-FREE (theorem4's dissolve rests on this; degree 2L).
- `Validate/LossHomogeneity.lean` (`dlnLoss_homogeneous_layer`), `Foundations/S1NodeFlatHomog.lean`
  (`S1NodeFlatHomog`) — the degree-2L homogeneity input the scaling bridge lemma consumes.

**What it assumes.** Nothing new for the deepest leg. The far-point leg (L≥3 coupled non-origin) is the
OPEN LEG on `theorem4-localization` — discharges via this banked domination, not a chain-IH.

## Cover / null family (region_glue assembly primitives)

**What it gives.** Finite box covers + measure-zero disposal — the assembly `region_glue` glues over.
`Foundations/S1Cover.lean`, `S1BoxAdditive`, `Validate/RouteMCoverLemmas.lean`,
`Validate/RouteMNullSliceCov.lean`. **What it assumes:** the SEPARATED leaf integrand (a chain leaf is
`∑ bᵢ² = b₁²·unit`, single dominant monomial × unit) — load-bearing precondition
`IsFullMonomialization`; witnessed exact by `g-leaf-chain-separation`, `g-glue-lossy-vs-exact`,
`g-pivot-conull`. Near-miss: the abstract `ChartsCover` over these covers is VACUOUS (univ atlas) — the
ChartBridge fix is required (see [[dead-routes]]).

## Terminal atoms (the monomial reads region_glue bottoms out on)

**What it gives.** The Layer-D monomial threshold reads — each finite below its ratio `divExp/2`.
`RouteMSJGammaAtom.lean` (`gammaAtom_aniso_shifted_eq`), `RouteMSJQBoxCore.lean`,
`RouteMSJProductTube.lean` (`detGram_lintegral_lt_top`), `RouteMSJRadialInt`/`RadialPolar`;
`MonomialThresholdIdentity`, `S1NodeBlowup`, `S1ProductMin`. **What it assumes:** monomial × bounded-unit
(OR disjoint Morse core with `resRank ≥ minAdm` — the Morse residual is genuinely singular, contributes
`resRank/2` to the min; `resRank ≥ minAdm` is a THEOREM the tide OWES, never assumed — elder amendment,
tick 20). 0-sorry, consume as-is.

## Worked precedent (the pattern the generic engine reproduces)

`RouteMBoxThresholdRR4.lean` — the (r,r,4) family end-to-end 0-sorry (sub → det-Jacobian → gammaAtom →
cover → threshold). See [[landmark-cards]] `rr4-precedent` for the pinned decl names + the depth≥3 inner
wall. The engine IS this pattern made generic; RR4's SchurCore/front-peel INNER core does NOT generalise
(depth ≥ 3), so it is an OUTER-plumbing precedent only.
