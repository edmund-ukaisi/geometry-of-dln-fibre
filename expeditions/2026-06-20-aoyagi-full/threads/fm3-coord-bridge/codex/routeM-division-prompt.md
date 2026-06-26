<task>
DLNFibre Lean 4 + Mathlib formalisation. We are proving the general-M case of the R1 resolution
theorem `resolution_charts`:
    rlctAtOn (dlnLoss M 0) 0 = ⨅ i : ι, monomialThreshold (d i) (k i) (h i)
where `dlnLoss M 0 A = ‖prod M A‖²_F` (squared Frobenius norm of the matrix-chain product over reduced
widths M, at the deepest point 0), and the right side is a finite infimum over a chart family `(ι,d,k,h)`
(per-leaf dimension + monomial loss/Jacobian exponents). This is the singular-core RLCT.

The work is split between two agents and I (fm3) need to decide the cleanest NON-DUPLICATING division.

WHAT crux2 ALREADY HAS (banked, green, on branch route-m-atlas):
- `ChainDimSplit M` : a structure {drop, red : Fin(L+1)→ℕ, hsum : drop+red=M, hdrops : 0<Σdrop}. The
  one-step reduction state: red = the residual chain widths.
- `schur_straighten_of_data` : given a supplied chart factorisation hypothesis (`hfactor`: flatCore∘χ =ᶠ
  u·(Σqᵢ² + dlnLoss S.red 0 (redEmbed q))), produces an `IsSchurStraighten` (the det-1 GL straighten +
  the reduced core). It CONSUMES the chart, does not construct it.
- `rlctAtOn_reduced_transport` : transports rlctAtOn across a measure-preserving reindex to the reduced core.
- `schur_recursion_step_sound` : the one-step descent rlctAtOn(dlnLoss M 0) = nReg/2 + rlctAtOn(dlnLoss Mred 0),
  CONDITIONAL on a supplied chart.
- the L=1 base (`dlnLoss_one_layer_deepest`).
- The BRIDGE `routeM_rlctAtOn_eq_iInf` : consumes `IsRouteMCover F U ι d k h` (a Prop with 5 fields:
  Fmeas, Uopen, Umem, cover_le, cover_ge_div) ABSTRACTLY and yields rlctAtOn F 0 = ⨅ monomialThreshold.
- The VALUE `resolution_value_of_atlas` : consumes `IsResolutionAtlas M ι d k h` (threshold_ge + achiever,
  pure combinatorics on (d,k,h)) and yields ⨅ monomialThreshold = ofReal(lambdaCore M).
- `RouteMAtlas` bundles {isCover, isValue} over a shared (ι,d,k,h); the headline is a one-line Eq.trans.
- Cover atoms (Case222Cover): monomialIntegrand_integrable_of_lt, _lintegral_box_eq_top, integrableOn_monomial_mul_unit_iff, etc.
- g5_pivotNode / argmaxCellOn_cover / pivotBlowupOn(Deriv_det) (the per-node blow-up cover-split atoms).

WHAT fm3 (me) HAS (banked, green, on branch fm3/routem):
- G2 node factorization: `node_loss_pivot_factor` (L∘pivotBlowupOn = x_p²·(L∘hardPivot) given homogeneity),
  `node_jacobian_det` (det = x_p^(card-1)). The per-node monomial blow-up.
- `schur_node_loss_presentation` (the residual row-split ‖Â·A2‖² = ‖row0‖²+‖lower‖²).
- `dlnLoss_homogeneous_layer` (degree-2 homogeneity per layer, feeding node_loss_pivot_factor).
- A SEPARATE recursion scaffold in RouteMTree.lean: my own `RouteState {L, M}`, `routeMeasure = lex(L,ΣM,ncDefect)`,
  `routeRel_wf`, and a `routeAtlas = WellFounded.fix` that dispatches on `classify : RouteCase S` (leaf/C1/C2/C4/C5)
  into a `NodeChartFamily {ι, fintype, data : ι → MonoData}`. classify + the state-maps schurState/passState/etc
  + the per-leaf (d,k,h) accumulation are all STUBBED/sorry. The cover-facts routeM_cover_le/_ge_div are stubbed
  in the exact IsRouteMCover field shapes, but reference routeMCore/routeMAmbient/routeMBaseNbhd which are
  also sorry (they need the concrete routeAtlas).

THE FORK: my RouteMTree re-invents a recursion-state (`RouteState`/`schurState`) that PARALLELS crux2's
`ChainDimSplit`. Two candidate divisions:

(A) fm3 builds the WHOLE general-M geometry recursion standalone (my RouteState/classify/schurState +
    concrete routeAtlas + the cover integral facts cover_le/cover_ge_div for the actual flat dlnLoss M 0),
    handing crux2 a finished RouteMAtlas. Risk: duplicates crux2's ChainDimSplit/schur_straighten_of_data
    descent; the cover_le requires composing the per-node blow-up cover-split DOWN a tree I build from scratch.

(B) fm3 builds ONLY the chart-family producer (ι,d,k,h) + the value facts (IsResolutionAtlas: threshold_ge +
    achiever, pure (d,k,h) combinatorics) — and the cover facts are obtained by crux2's recursion
    (schur_recursion_step_sound composed to the L=1 base) rather than a fresh tree cover integral. i.e. the
    RLCT identity rlctAtOn(dlnLoss M 0) 0 = ⨅ comes from crux2's recursion telescoping, NOT from my cover_le.
    Then my routeAtlas produces (ι,d,k,h) for the VALUE half only, and the IsRouteMCover is crux2's job built
    on its ChainDimSplit recursion.

(C) a hybrid: fm3's routeAtlas recursion is REBASED onto crux2's ChainDimSplit (consume it as the node
    reduction state instead of my parallel RouteState), so there is ONE recursion; fm3 owns the (d,k,h)
    accumulation + value facts on it, crux2 owns the RLCT-transport + cover on it.
</task>

<output_contract>
1. RECOMMENDATION: which division (A/B/C or a refinement) minimises duplicated proof effort AND keeps a
   clean single-writer seam. One paragraph + the decisive reason.
2. THE COVER FACTS: is `cover_le`/`cover_ge_div` (a SINGLE tree-wide integral bound over the WHOLE chart
   family at once) the right vehicle for general M, or does the general-M RLCT identity more naturally come
   from telescoping crux2's PER-STEP `schur_recursion_step_sound` down to the L=1 base (so the ⨅ over leaves
   is reconstructed step-by-step, not via one global cover integral)? Which is less Lean effort?
3. THE PARALLEL-RECURSION HAZARD: is my separate `RouteState` recursion a genuine liability (two recursions
   to keep in sync, double termination proofs) or benign (the value-combinatorics genuinely wants its own
   index recursion independent of the analytic descent)?
4. CONCRETE NEXT STEP for fm3 that is stackable and does NOT depend on resolving the whole fork — one piece
   I can prove green now regardless of A/B/C.
</output_contract>

<grounding_rules>
You do not have the files; reason from the structures/signatures described. Flag any place where your
recommendation depends on a fact about the code you cannot verify from this description (e.g. "IF
schur_recursion_step_sound's chart hypothesis is dischargeable per-node via node_loss_pivot_factor, THEN
…"). Distinguish "this is the cleaner architecture" (judgement) from "this is forced by the type theory"
(claim). Do not invent Mathlib lemma names.
</grounding_rules>
