# 2b-i SOUNDNESS GAP — the radial-separability cert is for the LIVE-leaf decoder; the chart uses DEAD-leaf

Surfaced 2026-06-28 before opening 2b-i deep-fill (verify-not-subtly-wrong / green≠right). A load-bearing
mismatch between the radial-separability WITNESS certificate's model and the decoder the interior `cov`
actually builds on.

## THE MISMATCH (verified in-code)
- The radial-separability cert (`codex/radial-separability-{prompt,answer}.md`) proves det = u^{minAdm−1}·(u-free)
  for a model where: `R_k` is a FIXED 0/1 constant (NOT free), `Rfin` is FREE, `C_L = u·Rfin` (the prompt
  lines 10-16). Its worked instance is `R_1 = e_{33}`, `R_2` free-scaled, `Rfin` free = the LIVE-leaf `B_det`
  family. The verified `(3,3,3,3)` monomial `|u0|^5·…` (`RouteM3333Atom.phi3333_abs_det`) ALSO uses the
  LIVE-leaf `B_det3333` (`Rfin 3 = [ζ] ≠ 0`, `RouteM3333Det:25,69`).
- BUT `achieverPhi = phiFlatStructV M (tach M) ha hN` (the interior `cov` chart, sub-tide 1's `phiFlatLDU`
  base) uses `genBlkFlatStruct` — the DEAD-leaf decoder: `Rfin := fun _ => 0` (`RouteMGenFlatStruct:155`),
  `Rmat (k+1) = rmatPad (readE)` (the E-block FREE). The codebase explicitly flags the dead-leaf subtlety
  (`RouteMAchieverRateFields:28-29`: dead-leaf `UvalStructV ≡ 0` for L=1; the live-leaf `B_det` is the
  alternative). The two decoders are DIFFERENT.

## WHY IT MATTERS (the budget differs)
- Dead-leaf `genBlkFlatStruct`: the u-carriers are `u·rmatPad(readE)` per interior boundary; the angular
  coords are the free E-block entries. NB minAdm is the LAYER-PEELING recursion (Aoyagi descent), NOT a
  simple `∑ r_k·c_k`: at (3,3,3,3), minAdm = 6 but `∑_k (Text k − Text(k+1))(Wext k − Text(k+1)) = 0+1+2 = 3`
  (the raw E-block-dim sum) — so #(free E-entries) ≠ minAdm in general. [arithmetic re-checked 2026-06-28; an
  earlier draft wrongly equated them.] The verified (3,3,3,3) monomial is |u0|^5·|u1|^4·|u4|^2·|u9|^3: the
  RADIAL exponent u0^5 = minAdm−1 = 5, and u1^4·u4^2·u9^3 is the LDU/Schur monomial. So the radial exponent
  IS minAdm−1, but the budget (how the minAdm−1 angular columns lay out in the dead-leaf E-blocks + whether
  the chart is square) is the OPEN decoder-specific question — the cert's budget (#angular=minAdm−1, free
  Rfin, one fixed pivot) is the LIVE-leaf layout, NOT the dead-leaf E-block layout.
- With `Rfin = 0`, the leaf `C_L = u·0 = 0` — the leaf angular contribution the cert's worked instance used
  (free Rfin) is ABSENT. Whether the dead-leaf chart is still a square diffeomorphism with det =
  u^{minAdm−1}·(monomial), angular columns supplied by the interior E-blocks, is OPEN.

## THE QUESTION
Does the DEAD-leaf `genBlkFlatStruct` (Rfin=0) chart `phiFlatLDU ∘ kLDU` have the monomial Jacobian
det = u^{minAdm−1}·(LDU-pivot monomial), with the budget #angular = minAdm−1 + square-chart? The cert
established this for the LIVE-leaf `B_det` only. The radial MATH (affine-in-u, unipotent chainA shear) likely
transfers, but the BUDGET (which/how-many coords are angular, square-chart) is decoder-specific and the
dead-leaf's E-block-vs-Rfin structure is materially different.

## OPTIONS (controller scope call)
(A) SWITCH the interior chart to the LIVE-leaf `B_det M` decoder (for which the cert + the (3,3,3,3) monomial
    det hold). Cost: re-bank the rate (decoder-agnostic, cheap via routeMCore_phiGen) + re-derive the interior
    witness for B_det (the witness `exists_achieverUfun_ne_zero_interior` is currently genBlkFlatStruct-specific;
    but the LIVE-leaf is the cert's §2/§5 witness regime, likely EASIER — live leaf ⟹ unit ≢ 0 directly).
    This ALIGNS the chart with the verified cert. RECOMMENDED.
(B) Keep the dead-leaf `genBlkFlatStruct` and adjudicate ITS budget (a focused pen-and-paper: does the
    dead-leaf chart have det = u^{minAdm−1}·monomial with #angular = minAdm−1, given Rfin=0 and minAdm free
    E-entries?). Risk: the dead-leaf may NOT be a clean square radial chart (the E-budget = minAdm not
    minAdm−1, and Rfin=0 kills the leaf direction) → possibly degenerate / wrong exponent.
(C) The kLDU + phiFlatLDU sub-tides 1-2a are decoder-agnostic (any reparam, any decoder), so they SURVIVE
    either choice — only the det-route's decoder needs pinning.

## RECOMMENDATION
Surface BEFORE 2b-i deep-fill. The radial-separability cert does NOT cover the dead-leaf decoder the chart
uses; building 2b-i's det = u^{minAdm−1} on genBlkFlatStruct would be building on an unverified budget. Prefer
Option A (switch to the live-leaf B_det decoder, aligning with the cert + the worked (3,3,3,3) monomial), OR a
focused pen-and-paper adjudication of the dead-leaf budget (Option B) if the dead-leaf is preferred for the
witness. Confirm the decoder choice before I open 2b-i.

## CODEX-CONFIRMED REFINEMENT (decision A made concrete; the budget is the crux) — 2026-06-28
Decision (A) = switch the det-route to the LIVE-leaf B_det decoder. Codex xhigh
(`codex/liveleaf-budget-{prompt,answer}.md`) sharpens it with two DECISIVE findings:

1. **The dead-leaf decoder gives the WRONG threshold.** The dead-leaf's angular directions are the interior
   E-blocks; their count `q = ∑ (Text k − Text(k+1))(Wext k − Text(k+1))`, which at 3333 is 3, NOT
   minAdm−1 = 5. The radial mechanism is decoder-agnostic (affine-in-u + unipotent chainA shear, needs only
   "C linear in u + independent u-scaled free directions"), so the dead-leaf DOES factor as u^q·(u-free) —
   but with exponent `q` (the E-count), NOT minAdm−1. So Route B (prove radial-sep directly on the dead-leaf)
   is MATHEMATICALLY WRONG for the cov target (gives the wrong RLCT threshold). The det genuinely NEEDS the
   live-leaf, whose Rfin-based angular layout supplies the minAdm−1 directions.

2. **`#angular = minAdm−1` for the live layout is a NEW slot-cardinality identity** that does NOT follow from
   `card ChartIdx = flatDim`. The flatDim budget is entirely consumed by per-boundary schur+lift slots — NO
   separate Rfin slot. A general-M live-leaf decoder on `Fin N = flatDim` must REROUTE existing ChartIdx slots
   (the leaf boundary's E/lift slots → free Rfin + fixed interior Rmat pivots), and prove the rerouted layout
   has exactly minAdm−1 free angular coords + is a square chart. The (3,3,3,3) B_det3333 is square only because
   it reuses Fin-27 bespoke; it is NOT evidence the genBlkFlatStruct reader layout already has the right homes.

## SCOPE CONSEQUENCE (the rate+witness must ALSO move to the live-leaf — not just the det)
The contract's `NodeAchieverChart` ties the SAME `phi` to BOTH the rate (`leaf_integrand`) AND the det (`cov`).
So I CANNOT use dead-leaf for the rate/witness and live-leaf for the det in one bundle — `phi` must be ONE
chart. Since the det NEEDS the live-leaf (finding 1), the WHOLE interior chart must be the live-leaf decoder:
the rate (decoder-agnostic, cheap via routeMCore_phiGen — survives), the det (live-leaf, the minAdm−1 budget),
AND the interior witness (re-derive `exists_achieverUfun_ne_zero_interior` for the live-leaf — Codex/controller
note this is EASIER on the live leaf: live ⟹ unit ≢ 0 directly, the cert's §2/§5 regime). Sub-tides 1+2a
(phiFlatLDU/kLDU) are decoder-agnostic so they SURVIVE (re-instantiate with the live decoder + kLDU).

## REVISED PLAN (live-leaf throughout)
- 2a' : `genBlkFlatLive M t ha` — the general-M live-leaf decoder, rerouting ChartIdx slots (leaf E/lift →
  free Rfin + fixed interior Rmat pivots); the BUDGET IDENTITY #angular = minAdm−1 + square-chart (the heavy,
  delicate cardinality piece — the genuine 2b residual the cert+controller flagged).
- 2b-i : affine-in-u radial extraction on phiFlatLive ∘ kLDU (the cert applies DIRECTLY — live-leaf).
- 2b-ii/iii/iv : per-layer det_comp → Schur×LDU → assemble.
- 2e : live-leaf interior witness + the 4 fields + interiorContractLDU.

The budget identity (2a') is the load-bearing delicate piece. Recommend the controller weigh: is the
general-M live-leaf decoder + its budget identity within this thread's scope, or does it want a pen-and-paper
`witness` adjudication of the minAdm−1 slot-cardinality FIRST (it's a fresh combinatorial identity over opaque
widths, decorrelated from the radial-sep cert)?

## BUDGET WITNESS RECEIVED + a BANKED-IDENTITY find (2026-06-28)
genm-budget's witness: `#angular = minAdm−1` is a THEOREM (`Σ_{k=1..L-1} r_k·c_k + Text(L)·Wext(L) = minAdm`,
129k cases + symbolic L=2..5 + Codex); square-chart + det=u^{minAdm−1}·(u-free) verified. CRITICAL REFINEMENT:
71/351 interior M (e.g. (2,2,4), (2,2,2,4)) have NO live-leaf (Text(L)=0 → empty leaf Rfin); the angular
coords + the fixed pivot RELOCATE to the active-center block (interior/leading, not leaf). So
`genBlkFlatLive` (live-LEAF @edeb60b2) is correct for ~280 M but DEGENERATE for the 71 → generalize to
active-center placement (parameterized by the achiever path).

**FIND: the budget identity's CORE is ALREADY BANKED.** `RouteMAchieverPath.sum_rBlock_cBlock_eq_minAdm`:
`∑_{j:Fin L} rBlock·cBlock = minAdm M`, with `rBlock j = tPrev − tStar_j`, `cBlock j = M_{j+1} − tStar_j`
(over ℤ; via `Mval_tStar_eq : Mval (tStar) = minAdm`, all banked). The controller's
`Σ_{k=1..L-1} r_k·c_k + Text(L)·Wext(L)` is the SAME `Fin L` sum reorganized: the `j=L-1` (leaf) summand IS
the `Text(L)·Wext(L)` term after the chain↔Aoyagi width translation (`Text(tach)(k+1) = tStar k`). So
sub-tide 2 (the budget identity) reduces to: a WIDTH BRIDGE connecting the chart's chain-width E-block + leaf
dims (`Text`/`Wext`) to the banked Aoyagi `rBlock`/`cBlock`. The combinatorial heavy-lift is DONE banked;
the remaining is the cast/width bridge — much lighter than a fresh ∑-identity.

NB the leaf saturation: `Text M (tach M) (k+2) = 1` for the leaf when `tStar(last)=0` (the +1 convention,
RouteMAchieverStructAdm:88) — this is the `ρ = Text(L)` business and the source of the 71-case `Text(L)=0`
distinction (active center off-leaf). The active-center placement must respect this.

HOLDING the genBlkFlatLive generalization for genm-budget's (2,2,4) active-center layout + the structural
confirmation (is interior Rmat free-E or fixed-pivot in the live model?) — requested via controller, to build
the correct pivot-placement once. The no-regret decoder + rate (@edeb60b2) stand; only the pivot placement +
the (active-center vs leaf) routing need the cert.

## WIDTH-BRIDGE STRUCTURE worked out (no-wait move 2, 2026-06-28) — the budget identity's chain form
Reading (a) CONFIRMED by controller (interior E-blocks + leaf Rfin BOTH free-angular; the refinement is ONLY
the fixed-pivot+radial-u placement, dispatched on ρ=Text(L): leaf for ~280, interior/leading for the 71).
genBlkFlatLive already spans both block families; only the pivot/u placement needs the active-center dispatch.

The budget identity (sub-tide 2) chain form + its reduction to the BANKED Aoyagi core:
- Banked: `sum_rBlock_cBlock_eq_minAdm : ∑_{j:Fin L} rBlock·cBlock = minAdm`, `rBlock j = tPrev−tStar_j`,
  `cBlock j = M_{j+1}−tStar_j` (`Mval_tStar_eq`). `Mval = ∑_j (tPrev−T_j)(M_{j+1}−T_j)`, `tPrev j = M0`(j=0)
  else `T_{j-1}`.
- Chain widths (achiever `tach M`): `Text M (tach M) (k+1) = tach k` (`Text_tach_succ`+`tach_succ`); `tach 0 =
  M0`, `tach(k+1) = tStar_k`; `Wext k = M k`. So chain `r_k = Text k − Text(k+1)`, `c_k = M k − Text(k+1)`.
- KEY STRUCTURE (worked out): chain boundary k=0 has `r_0 = M0 − tach(0) = M0 − M0 = 0` ⟹ the IDENTITY
  boundary contributes ZERO E-block. So the chain E-blocks live at k=1..L-1, and the budget is
  `Σ_{k=1..L-1} r_k·c_k + (leaf term Text(L)·Wext(L)) = minAdm` — EXACTLY the controller's stated form. The
  `k=1..L-1` range (not 0..L-1) is BECAUSE boundary 0 is zero; the leaf term is separate because the chain's
  per-boundary E-block stops at L-1 while Aoyagi's `Fin L` sum's last term (j=L-1) becomes the leaf
  `Text(L)·Wext(L)` after the saturation `Text(L) = tStar(last)` (or 1 / 0 per the +1 convention).
- The reduction to banked: re-index the chain `Σ_{k=1..L-1} r_k c_k + leaf` to the Aoyagi `∑_{j:Fin L}
  rBlock·cBlock` (chain boundary k+1 ↔ Aoyagi j=k for interior; leaf ↔ j=L-1), then `sum_rBlock_cBlock_eq_minAdm`.
  The delicate piece = the leaf saturation index-match (Text(L) chain vs Aoyagi leaf), which interacts with the
  active-center (Text(L)=0 for the 71). HOLDING the exact statement for genm-budget's (2,2,4) slot map +
  identity-proof structure (the leaf-index convention is decoder-layout-dependent — building it on the wrong
  convention would redo it). Artefacts not yet on any remote branch (genm-budget local); requested via controller.
