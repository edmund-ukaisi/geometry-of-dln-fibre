# Deep-mixed realization probe (the F-order side) — #124

Seat: pen-and-paper, obstruction-primary. Re-convened by controller. Exact algebra + decorrelated Codex
(xhigh). Question: at deep-mixed coupled corank≥2, does every terminal divisor `v` of buildTree satisfy
ratio `(h_v+1)/(2 a_v) ≥ ½·minAdm` (F-order side / no-over-vanishing), or does a deeper divisor undershoot?
KILL = one deeper divisor with ratio `< ½·minAdm`.

## STEP 1 — PAPER-FIRST (charter §3 DEFECT gate): what does AOYAGI say at worked.tex:663 and around?
Read BEFORE the exact-algebra, per the elder's condition. Source: worked.tex:555–664 (the faithful
transcription of Aoyagi's §resolution from her page images p.14–22) + the paper abstract
(`aoyagi-2023-extracted-text.txt` p.1; the body OCR is ligature-mangled and un-greppable for math, so the
worked.tex reproduction is the authoritative transcription).

**Finding P0 — Aoyagi RESOLVES the no-over-vanishing / realization; it is NOT open in the source.**
- Her method (worked.tex:562–577, from p.14–22): the recursive blow-up MAINTAINS the **two-sided** ideal
  identity `⟨∏C⟩ = ⟨diag(b₁..b_{M(S)})·[[E_J,O],[O,D_J]]·∏_{s>S}C⟩` through Cases 1 & 2, and TERMINATES at
  `S=L+1` fully diagonal: `⟨∏C⟩ = ⟨diag(b₁..b_M)⟩`, whence `‖∏C‖²` is (in these coords) `∑bᵢ²` — normal
  crossing. The Jacobian ledger (worked.tex:589–594) gives each exceptional `u_{s,k}` ratio `M_{s,k}/2`.
  The abstract states this for GENERAL depth ("learning coefficients are bounded even though the number of
  layers goes to infinity") — she claims a COMPLETE resolution map + normal crossing divisors + exact
  values, all `L`.
- **So the realization ("F does not over-vanish") is NOT a separate F-order check in her proof.** It is the
  REVERSE half of the two-sided terminal ideal identity `⟨∏C⟩ ⊇ ⟨diag b⟩` (the `bᵢ` are recovered from the
  entries), established by the induction's maintenance (each blow-up creates a unit top-left pivot; the
  block-elim = L-A clears it), and then transferred to `F = ‖∏C‖²` by **Lemma 1 (Object A, ideal-invariance)**:
  `rlct(‖∏C‖²) = rlct(∑bᵢ²) = ½·min M_{s,k}`. Frobenius is NOT preserved (g-coupled-334 finding D), so the
  transfer genuinely goes through Lemma 1, not through `F = ∑bᵢ²` as functions.
- **The ":663 deeper-mixed open end is the EXPEDITION's (thread-28 certificate), NOT Aoyagi's.**
  worked.tex:661–663 reads: "the paper's single-chain inductive invariant survives every kill-instance the
  expedition could construct; the flagged open end is documented in the thread-28 certificate (deeper mixed
  instances)." Aoyagi's inductive statement is claimed general (all `v`); the expedition verified it on
  instances and neither closed nor broke it — that gap is the expedition's verification residual, not a spot
  Aoyagi flags as open. For a fidelity project the prior is: **reproduce-and-verify her induction, do not
  de-novo attack.**
- **The ONE genuine source DEFECT (worked.tex:579–587, T-F):** Aoyagi's inductive statement additionally
  asserts pairwise TOTALITY of the carried profiles (`T_{s,k} ≤ or ≥`), which is FALSE ((2,2,1,1) gives
  incomparable profiles). But nothing downstream needs it (the `min` needs no total order; the chain
  `b₁|…|b_M` is ordered by construction). So her induction closes with totality DROPPED — the expedition's
  repair, already banked. This is the only place her literal argument has a hole, and it is repairable.

**Verdict of the paper-first step: Aoyagi RESOLVES it (GREEN reading).** The no-over-vanishing/realization
is her two-sided `(S,J)` terminal ideal identity + Lemma 1, general `L`; it is DETAIL-AT-SCALE
(reproduce-and-verify her Cases 1/2 with the T-F totality dropped), NOT open-in-source, NOT a monument. My
exact-algebra work below then VERIFIES her construction at (3,3,3,2,2) + the L=4 coupled-binding instances —
it confirms her answer, it does not attack a de-novo object.

**Correction to my earlier "distinct third obligation" framing (honest).** In the #122 audit I called the
realization "a THIRD obligation distinct from the ideal-algebra (the F-order side)." The paper-first read
sharpens this: per Aoyagi's ACTUAL route the realization is the **reverse half of the `(S,J)` ideal
maintenance** (L-A/L-B, two-sided) + Lemma 1 — i.e. it is PART of the ideal-algebra spine, not a separate
F-order check. It IS still distinct from the geometric COVER (route-a). So the residual map is: (i) `(S,J)`
two-sided ideal maintenance [INCLUDES the realization/reverse] — render-assessed general; (ii) the cover
[route-a, GREEN]; (iii) Object A / Object C [landed]. Not a new F-order obligation.

## Scripts (exact, re-run this dispatch)
- `/tmp/dm_monomial_valuations.py` — the toric (monomial-valuation) min ratio, all instances + L≥4 scan.
- `/tmp/dm_accumulation.py` — the discrepancy-accumulation identity `h_E = Mval−1` for the binding branch.
- `/tmp/dm_mc_rlct.py` — Monte-Carlo rlct estimate (GUIDE only; shown biased).
- Coupled constructions reused: `g-coupled-{334,3322-shareddepth,444-twoblock,33322-separated}.py`.

## What the kill-condition can and cannot do (stated first, honestly)
`rlct_0(F) = inf_v A(v)/ord_v(F)`. **If** Aoyagi's value `rlct = ½·minAdm` holds, then by definition NO
divisor undershoots — the kill cannot trigger. So a triggered kill would refute a published theorem
(Watanabe upper `rlct ≤ ½codim` + Aoyagi equality); the realistic outcomes are: (a) no undershoot found
(expected), which CHECKS that buildTree realizes the value on the tested instances but does not by itself
prove the general induction; or (b) a CONSTRUCTION gap (my error, or the tree missing a chart). Decorrelated
Codex (Q1) confirms this framing: "Watanabe supplies only `rlct ≤ ½minAdm`; codimension alone gives no
lower bound — ruling out an undershooting divisor is precisely the load-bearing content of Aoyagi's `(S,J)`
lower-bound induction, not of the QIP codimension calculation."

## Findings (exact)

**F1 — the toric (monomial) divisors NEVER undershoot.** The min over all per-entry monomial valuations
of `A(v)/(2 a_v)` is `≥ ½·minAdm` for every instance. It EQUALS `½·minAdm` for the monomial-binding
instances (`(3,3,2,2)`, `(3,3,3,2,2)`, `(4,4,2,2)`, `(4,4,4,2,2)`) and is STRICTLY GREATER for the
coupled-binding ones (`(3,3,4)`: toric `9/2 > 4`; `(4,4,4,2)`: `4 > 7/2`; `(4,4,4,4,2)`: `4 > 7/2`;
`(4,4,4,4,3)`: `6 > 9/2`). ⟹ in the coupled-binding instances the RLCT-binding divisor is a genuinely
NON-MONOMIAL (coupled) valuation, strictly below the toric floor — but the toric floor is itself always
`≥ ½·minAdm`, so no monomial divisor undershoots.

**F2 — the binding divisor (monomial or coupled) `= ½·minAdm`, via the discrepancy-accumulation identity,
GENERAL.** For the binding rank-profile, `Mval = Σ_s (M^s−t_s)(M^{s+1}−t_s)` and the resolution's dominant
divisor `E` has `h_E = Σ(per-blow-up dim − 1) + #joins = Mval − 1` and `a_E = 1` (a retained pivot supplies
an order-1 entry), so ratio `= Mval/2 = ½·minAdm`. Verified `h_E = Mval−1`, ratio `= ½·minAdm`, and
"a pivot survives the binding profile" for ALL tested instances INCLUDING the L=4 coupled-binding
`(4,4,4,4,2)` (ratio `7/2`), `(4,4,4,4,3)` (ratio `9/2`), and Gröbner-verified coupled constructions
`(3,3,4)→4`, `(4,4,4)→6`. The join makes the discrepancies ADD (coupling raises), the retained pivot keeps
`a_E = 1` — this is the general mechanism, corank-agnostic (`/tmp/radial_collapse_general.py`).

**F3 — NO undershoot found anywhere probed.** Toric floor `≥ ½·minAdm` (F1), binding `= ½·minAdm` (F2),
and the coupled constructions all land at exactly `½·minAdm`. No divisor `< ½·minAdm` surfaced.

**F4 — Monte-Carlo is BIASED LOW (artifact, NOT a kill).** MC rlct slopes run ~0.3–0.5 below `½·minAdm`
and DECREASE toward small `ε` — but they undershoot IDENTICALLY in the monomial-binding cases
(`(3,3,2,2)`, `(3,3,3,2,2)`) where `rlct = ½·minAdm` is EXACT (F1). So the undershoot is a uniform
high-dimensional / homogeneity sampling bias (thin-shell sampling in `n≈20–30` dims + `|log ε|^{m−1}`
multiplicity corrections), NOT a coupled undershoot. MC gives no reliable kill signal here — logged as a
calibration lesson (float rlct at these dims is untrustworthy; use exact toric + construction).

## The refinement the probe surfaced (decorrelated Codex Q2 — load-bearing)
Per-divisor minima are NOT sufficient: **realization is a JOINT condition at divisor INTERSECTIONS, not a
generic condition along each divisor.** Codex's exact witness: `I = (x,y)` has order 0 generically along
BOTH coordinate divisors, yet NO generator is a unit at their intersection (the origin). Translated to the
DLN tree: the danger is not a single divisor but the DEEPEST STRATA where several exceptionals meet and
EVERY residual generator vanishes — a non-pivot intersection where "further blow-up adds residual
multiplicity faster than discrepancy" (Codex Q1). My F2 "a retained pivot supplies `a_E=1`" holds along
each binding divisor and at the constructed terminal charts, but the GENERAL claim — that a realizing pivot
survives every recursive shear at every deepest intersection, for all branches — is the joint condition,
and it is exactly Aoyagi's `(S,J)` lower-bound induction ("global combinatorics, not a new analytic
theorem" — Codex Q2).

## Verdict — does no-over-vanishing close general at deep-mixed?
**It closes iff Aoyagi's `(S,J)` LOWER-BOUND induction closes — which is DETAIL-AT-SCALE (global
combinatorics), NOT a monument, and NOT the QIP codimension calc, and NOT the cover.** Precisely:
- The kill did NOT trigger. Every divisor probed — toric (F1), binding (F2), coupled constructions — is
  `≥ ½·minAdm`, with the binding exactly `½·minAdm`. Strong evidence the realization holds; buildTree
  realizes the value on all tested deep-mixed instances (incl. L=4 coupled-binding).
- The realization obligation (`AtlasRealizesExponents` / no-over-vanishing) is:
  - **per fixed instance:** a BOUNDED CAS check (factor the claimed monomial per leaf, confirm a residual
    entry has nonzero constant term at each terminal intersection) — Codex Q2 [FACT]. Detail-at-scale.
  - **general-`d`:** the `(S,J)` induction proving a realizing pivot survives every recursive shear at the
    deepest intersections. Detail-at-scale (global combinatorics), un-probed beyond instances at deep-mixed
    — the honest residual. This is DISTINCT from (i) the QIP codim (`minAdm`, landed), (ii) the geometric
    cover (hcover OBL-1/2, route-a), (iii) the ideal-algebra maintenance (L-A/L-B, dissolved). It is the
    F-order / joint-realization piece.
- **No monument:** Codex Q1/Q2 concur — this is Aoyagi's lower-bound induction, "not a new analytic
  theorem." No deep open fact is load-bearing; the labour is the reproduce-and-verify of her `(S,J)` cases.

## Confidence + what would move it
- No divisor undershoots at the tested deep-mixed instances: **HIGH** (F1 exact + F2 general identity + F3).
- Realization is detail-at-scale (not a monument): **MEDIUM-HIGH** (Codex concurs; the mechanism is the
  pivot-survival + accumulation, both explicit). Moved DOWN by: a deep-mixed instance where the deepest
  intersection has NO surviving pivot AND slack < the multiplicity gain (Codex's failure mode) — the one
  thing to CAS-check per instance during the build.
- No independent CAS certificate available this session (no Singular/M2/Sage; Codex Q3's Gröbner-degeneration
  `lct_ℂ(in_w I) = minAdm` route is the practical one but 20–40-var instances may explode) — so the general
  claim rests on reproducing the induction, not on an instance oracle.

## Bottom line
No-over-vanishing/realization CLOSES general at deep-mixed **conditional on Aoyagi's `(S,J)` lower-bound
induction** — which is detail-at-scale (global combinatorics), the reproduce-and-verify, NOT a monument.
The probe found NO undershoot (kill did not trigger), and sharpened the residual: the realization is a
JOINT (deepest-intersection) condition = the `(S,J)` lower-bound induction, a THIRD obligation distinct
from the QIP codim, the cover, and the ideal-algebra. Route P is buildable cite-free; its realization
residual should be CAS-checked per-instance as the build proceeds (the failure mode is a pivot-less deepest
intersection), and the general proof is the induction, un-probed beyond instances today.
