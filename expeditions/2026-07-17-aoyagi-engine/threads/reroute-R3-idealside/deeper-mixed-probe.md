# Deeper-mixed Gröbner probe (#167) — VERIFIED-BUT-LOCALIZES

**Seat:** reroute-R3derisk. Decorrelated: faithful exact-algebra + real Gröbner (sympy over ℚ) + independent
Codex xhigh — CONVERGED. Persisted by the controller (seat barred from writing report files).
Scripts: `/tmp/deepmix_faithful.py`, `/tmp/fatal_exclusion.py`; Codex `/tmp/deepmix-codex-{prompt,answer}.md`.

## NET VERDICT: VERIFIED-BUT-LOCALIZES. (Not a clean GO-univ; not a BITE.)

The monument's exact-algebra CORE survives one deeper rung — BUT the probe DECISIVELY REFUTES the over-clean
"nbhd=univ general" banked earlier. Honest recalibration: nbhd=univ is SINGLE-PEEL / JOINED-CASCADE-special;
**separated-depth deep mixing genuinely LOCALIZES** the terminal to `{local-unit ≠ 0} ⊊ univ`. Benign
(handled), not fatal.

## THE INSTANCE
A DEEP corank-2 heart (genuine 2×2 Schur Δ, radial `a`) mixed with a SHALLOW corank-1 shared factor (radial
`w`) at SEPARATED depths — the (3,3,3,4) t=(2,0,0) / (3,3,3,2,2)-class regime, beyond every banked single-block
witness (334/444 are single-block or joined-cascade; this is separated). Corroborated by the BANKED REAL
witness (3,3,3,2,2), whose kept residual `Y00 = 1+p·d` is already a local unit ≠ 1 — the localization is
visible in an existing sorry-free witness, not just the model.

## THE THREE CHECKS
- **(i) I_terminal = ⟨b₁⟩ — CLEAN (holds LOCALLY).** Real Gröbner (Rabinowitsch saturation): the residual
  ideal contains 1 after inverting the kept pivot quotient ⟹ `⟨∏C∘g⟩_local = ⟨b₁⟩` (b₁ = product of the
  radials). Principal at the origin.
- **(ii) det Dg = ±monomial — CLEAN (EXACTLY).** Unipotent block-elim peels det = 1 (verified) + radial
  Jacobians = pure monomials ⟹ det = ±w^·a^·, no unit factor, NO localization from the Jacobian.
- **(iii) corner-join localization-free? — NO.** The kept pivot quotient = 1 + cross-terms (e.g. 1+p·d,
  1+p₁·rr₀), a LOCAL UNIT (value 1 at origin, vanishes on a proper hypersurface {unit=0}). So
  `nbhd = {unit≠0} ⊊ univ`, and the reverse Bézout cofactor = 1/(local unit), continuous on {unit≠0}. The
  cross-terms are exactly products of distinct radial-pivot ratio rows ([1,p]·[1;d] = 1+pd) — so ≥2
  non-joinable radials generically produce them (single peel / joined-cascade keeps the quotient exactly 1).

## WHY BENIGN, NOT A BITE
The localization is EXACTLY what `terminal_bezout` is built for (it shrinks V→V∩{unit≠0} for any unit with
unit 0≠0), and `Resolution.hcover` is already UP-TO-NULL (`volume(U\⋃ g''dom)=0`). {unit=0} is a proper
real-analytic hypersurface (measure zero). Route P still CLOSES up-to-null with a LOCAL single-chain
principality — the source's own framing ("principality is a LOCAL-ring statement at the origin"). NOT a
1/monomial wall, NOT a cleared-coord dependency.

**Fatal-case exclusion (structural, inference-not-proof):** a fatal 1/monomial would need the local unit's
CONSTANT TERM to vanish — which (33322 anti-check `d`, reproduced exactly) requires NO kept rank-survivor row.
A binding/minimising branch has terminal rank r≥1 (product not identically 0) ⟹ a kept survivor row always
exists ⟹ unit(0)≠0 ⟹ benign. Strong structural argument; not proven at arbitrary depth.

## IMPLICATION FOR THE P-vs-V FORK
Does NOT trigger objects-only. Route P remains viable — its "monument" is SHARPENED and CORRECTED:
- NOT the global nbhd=univ single-chain (FALSE at separated-depth mixing).
- IS: **(a)** the inferred-general LOCAL single-chain principality (VERIFIED one deeper rung here:
  I_terminal=⟨b₁⟩ locally + det=monomial, Gröbner-exact, no counterexample) + **(b) THE SHARP RESIDUAL** — an
  all-depth, FAMILY-INDEXED, up-to-null `hcover` subordinate to the per-leaf unit loci {u_leaf≠0}. Both
  decorrelated sources independently flag (b): a compact dom ⊆ open {unit≠0} stays ε from {unit=0}, MISSING a
  positive-measure tube — so nullity of {unit=0} ALONE is insufficient; sibling charts must cover the tubes
  (atlas completeness). This is the load-bearing R2 obligation, now precisely characterized — it is the SAME
  object as the #145 "sector-count ~98% vs decomp-5b 100%" cover reconciliation (the ~2% gap IS the {unit≈0}
  tubes).

Codex precision adopted: deeper mixing does not LOGICALLY force the localization (triangularity /
zero-couplings / cancellation could keep quotient 1 in special charts); the probe PROVES it for this generic
deep-separated instance, generality is inference.

## RECOMMENDATION (for the elder's P-vs-V adjudication)
- **If route P:** the cite-free claim rests on (a) LOCAL single-chain principality (inferred-general, verified
  one rung deeper, structurally robust via the r≥1 kept-survivor argument) + (b) the family-indexed up-to-null
  cover over the unit-locus tubes. **(b) — NOT the ideal composition — is the true remaining
  monument-adjacent labour, and it is a COVER/geometry obligation (R2), not ideal-side.** Re-scope R2's
  "family-cover" to explicitly be "subordinate to the leaf unit-loci {u≠0}, null complement."
- **The ideal side itself is CLEAN one rung deeper** (principality local + det monomial); no denominator wall,
  no cleared-coord read. The ideal conjunct of the unified fold is NOT the blocker — the family-cover is.
- **V (value-floor)** remains the strictly-monument-avoiding option if the operator's steer is
  "strictly-cite-free-or-nothing"; this probe does NOT make V necessary (P closes up-to-null), but it confirms
  P's residual is real and geometric.

## CLOSE
FIRMEST: at a genuinely deeper-mixed (separated deep corank-2 + shallow) instance, I_terminal=⟨b₁⟩ LOCALLY
(Gröbner) and det=±monomial EXACTLY — the monument's core verified one rung deeper. CORRECTION: nbhd=univ is
single-peel-special; separated-depth mixing benignly localizes to {local-unit≠0} (handled by terminal_bezout +
up-to-null hcover). MOST LIKELY TO BREAK IT: the all-depth family-indexed up-to-null cover over the {unit=0}
tubes (R2/geometry, = the #145 cover gap), NOT the ideal composition. The fatal 1/monomial is structurally
excluded for binding branches (r≥1 ⟹ kept survivor ⟹ unit(0)≠0). NEXT: fold the "subordinate-to-unit-loci"
refinement into R2's family-cover spec; the ideal conjunct is clear to build.
