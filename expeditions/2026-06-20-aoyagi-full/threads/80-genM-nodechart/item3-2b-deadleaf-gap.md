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
