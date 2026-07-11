# §7.5 route-audit — the corrected native-blow-up architecture vs the locked bar + Q1/Q2

**Seat:** pen-and-paper (decorrelated fidelity audit — genm-sj5-cover, the descent's auditor). **Date:**
2026-07-11. **NO Lean.** **Charge (team-lead):** audit `cov-ledger-design.md §7.5` (the corrected native
bounded-box (S,J) blow-up on the PRE-atom integral) against the pre-committed bar (i)/(ii)/(iii) + Q1
(general-width charge, second anchor) + Q2 (native peel vs decorated IH). This GATES the formaliser's build.

**Exact algebra (mine):** `/tmp/prodD/{audit75,corner75,deep75,verify_fast}.py` (charge recursion 7 anchors;
the nD homogeneous corner + reciprocal chart; the (2,2,1,2) atom; the `H^{−4}` residual + scalar log; the
v=0 branch). **Consumed:** `cov-ledger-design.md`, `corank2-cert.md §1/§2/§4` (genm-vsastruct),
`minadm-ccodim-cert.md`, `route-reconcile.md §3′`, the design's own `codex/covledger-answer.md`.
**Decorrelated:** own xhigh `local-codex-consult`, conclusion WITHHELD, framed adversarially on a DEEP chain
`(4,4,4,4)` and told to hunt a decoupling/leak/obstruction: `codex/audit75-{prompt,answer}.md`. It found the
same `H^{−4}` residual I then verified by hand — I did not paste it; I re-derived and numerically checked
every load-bearing integral (V1–V5).

Tags: **[V]** = my exact algebra / numeric-confirmed. **[CX]** = decorrelated Codex, independently
re-derived by me. **[ANCHOR]** = corank2-cert-verified. **[FLAG]** = build obligation.

---

## ★ HEADLINE VERDICT

**§7.5's ROUTE is correct — its "plain-hIH handoff" is NOT.** The redirect (drop the full-space Γ-atom on
degeneration cells; native bounded-box (S,J) blow-up; joint coupled corner; coupling load-bearing) is SOUND
and decorrelated-confirmed. **But §7.5's specific assertion — "one native peel discharges the decoration,
then hand a PLAIN shifted integral to hIH(redChain) at exactly `c'−ab/2`" — is FALSE.** A residual det-Gram
weight `H^{−4}` survives in the `R≲H` regime of the front peel; it equals `[plain reduced integrand]·[H^{−4}]`,
and plain hIH at the zero-slack binding cut cannot carry it. **The IH must be DECORATED** (carry the truncated
`H^{−4}` weight) — OR a simultaneous multi-level discharge lemma must be built; after full discharge the
surviving log is absorbed by the strict slack (`c'<½minAdm`, so `c'−ab/2+ε`). **This is a CONSTRUCTION gap,
NOT a finiteness obstruction** — every branch (incl. the `v=0` rank-one angular = the equally-binding `t=3`
cut) has charge `≥ minAdm`; no branch below `½minAdm`; the integral is finite. **Net: the plain-hIH
simplification §7.5 hoped for is unavailable; the descent is inherently DECORATED — which VINDICATES the
original `descent-buildplan.md` (#137: "decorated (S,J) descent, plain-IH insufficient, zero-slack Hölder").**

**Recommendation: build on §7.5's native blow-up WITH a decorated IH** (Q2), plus the two acknowledged
construction gaps (bar (iii) quantitative-sector cover; the terminal/deficient-rank bookkeeping, Q1). Do NOT
commission the formaliser on the "plain hIH at `c'−ab/2`" handoff — it will hit the residual `H^{−4}` and the
zero-slack wall.

---

## Bar (i) — JOINT flag-tube, not marginal/scalar: **PASS** (with the both-charts requirement)

§4 uses the joint two-scale density `μ{s₂≤t₂,s₃≤t₃} ≍ t₂³·t₃·log(e/t₂)` and explicitly rejects the marginals
(`min(t₂⁴,t₃)`, closes only for `η<1/4`) and the symmetric `∧²`-compound (`b≥3/2` vs `b<1`, no overlap) —
matching `corank2-cert §2/§4` and my locked RED-FLAG. **Stronger:** §4 identifies the corner blow-up AS the
joint density in blow-up coordinates (`u₀=max(s₂,s₃)`, `τ=min/max`), so no separate joint-density module is
needed — the coupled corner intrinsically realises the joint tube. [V] confirmed: the nD homogeneous corner
`∫∏|u_i|^{p_i}(∑u_i²U_i)^{−c'}` converges ⟺ `c' < ½Σ(p_i+1)`; for the (3,3,3,4) front (`p₀=3,p₁=2`) this is
`7/2`, and independent divisors undershoot to `3/2` (2.33×). **Caveat (bar-(i) completeness):** the coupled
sector `u₁=u₀τ` covers only `{|u₁|≲|u₀|}`; the RECIPROCAL chart `u₀=u₁s` is required for `{|u₀|≲|u₁|}` — both
give `7/2` [V]. §7.5 acknowledges "BOTH coupled charts." PASS provided the build includes both.

## Bar (ii) — charges ADD to minAdm at `sjLoss_terminal`: **PASS** (arithmetic + coupled-sector geometry) + 2 flags

- **[V] Arithmetic, width-general.** Along the achieving recursion the peelCharges sum to `minAdm` at all
  tested anchors: `(3,3,3,4)=7` `[4,3,0]`, **`(4,4,4,4)=11` `[4,3,4]`**, `(2,4,4,5)=7` `[3,4,0]`,
  `(3,3,3,3,4)=6` `[1,2,3,0]`, `(4,4,4,4,4)=10` `[1,2,3,4]`. Every first-level cut `t` has `Mval(t) ≥ minAdm`
  (the achiever is the WORST/lowest), so per-branch corner threshold `½Mval ≥ ½minAdm`.
- **[V/CX] Geometry, the coupled sector (NOT single-`u₀`).** The `(4,3,4)` sector `r₁=r₀τ₁, r₂=r₀τ₂` →
  measure `r₀^{10}τ₁²τ₂³`, loss `r₀²(1+τ₁²+τ₂²)` → `c'<11/2 = ½minAdm(4,4,4,4)` [CX, and [V] the 3-divisor
  corner `p=(0,1,2)` → threshold `3 = ½·6`]. Q1's blanket "single `u₀^{minAdm−1}`" is WRONG (design's own
  Codex + §7.5 + mine agree); the correct statement is the per-divisor coupled-sector inequality, which §7.5
  adopts.
- **[FLAG-1] Nontrivial terminal.** `(4,4,4,4)` bottoms at the terminal `(1,4)` with charge `4` (a dim-4
  FREE block, threshold `2`), unlike `(3,3,3,4)`'s trivial `(0,4)`. [V] `∫_{box⊂ℝ⁴}‖x‖^{−2c'}` finite ⟺
  `c'<2=½·4`. The banked terminal (`sjLoss_terminal`, B4 brick) is `b=1`; **the terminal lemma must cover a
  free block of dim `M₀·M₁ > 1`.**
- **[FLAG-2] `a>1` rank-deficient branch.** On `rank Q_b = r < b`, the Γ-integration charges only the `ar`
  active directions; the missing `a(b−r)` must come from rank-normal coordinates (Codex Q_C: they appear as
  products of an extracted radial/minor coordinate with the inactive Γ-directions). The `a=2` FRONT of
  `(3,3,3,4)`/`(4,4,4,4)` is the SAME 2×2 corank block → [ANCHOR]-verified; `(4,4,4,4)`'s redChain `(2,4,4)`
  peels are `a=1` (clean). But the general `a>1` deficient bookkeeping is a per-branch obligation, not yet a
  theorem.

## Bar (iii) — finite Borel cover: **GAP** (acknowledged; construction, not obstruction)

§5 + the design's own Codex (§7 Q3) + my Codex (Q_C) concur: the rank-flag cover is set-theoretically finite
but **analytically INCOMPLETE**. Competing pivot charts overlap on positive measure; the divergence lives in
the punctured seam NEIGHBOURHOOD, not the null seam; "recurse the rank flag" does not supply quantitative
sectors / Jacobians. **No intrinsic pivot obstruction** [CX Q_C]: near the `v=0` (rank-drop) locus one RETAINS
`v` as an exceptional coordinate — inverting it would create the uncontrolled `|det|^{−1}` the bounded
construction avoids; finitely many reciprocal charts (each largest-Γ-entry choice) have bounded Jacobian
`|u|³`. **But the explicit finite-cover CoV theorem (quantitative sectors + both coupled charts + explicit
bounded Jacobians + bounded overlap) is UNBUILT.** GAP with a stated route.

---

## Q1 (general-width charge count, second anchor) — **PASS with the corrected statement + FLAG-1/FLAG-2**

The ADD-arithmetic is width-general [V, 7 anchors]; the geometric realisation is the coupled sector [V/CX,
`(4,3,4)→11/2`, 3-divisor→3], NOT the fragile single-`u₀^{minAdm−1}`. No divergence at any second anchor. The
`(4,4,4,4)` recursion decomposes as **[a=2 anchor front (corank2-cert-verified)] + [a=1 clean redChain peels]
+ [nontrivial free terminal (1,4)]** — so the only genuinely-new pieces are FLAG-1 (terminal dim>1) and
FLAG-2 (`a>1` deficient `a(b−r)` bookkeeping). **The coupling is load-bearing [V]:** decoupling ANY divisor
gives a `min` undershoot (`3/2` at (3,3,3,4); `1.5` at the 3-divisor corner) vs the coupled sum. The
formaliser must keep every peel's divisor coupled (units `U_i` bounded below), recursing where a unit
vanishes.

## Q2 (native peel vs DECORATED IH) — **the deepest finding: plain-hIH FALSE, decorated IH REQUIRED**

This resolves the design's own flagged "deepest risk" (§8 [OPEN, Q2]) in the NEGATIVE for the plain-hIH
version. On the explicit front-`t=2` chart `Γ = u·[[1,s],[t,st+v]]` (`|dΓ|=|u|³`), with
`H² = |q₁+s q₂|² + v²|q₂|²`, radial integration of the 4-dim Γ-block gives [CX, and [V] verified V1]:

    ∫₀¹ u³ (R² + u²H²)^{−c'} du  ≍  R^{−2c'}        (H ≲ R)
                                    R^{4−2c'}·H^{−4}  (R ≲ H),   for c'>2.

Now `R^{4−2c'}` **is exactly the plain reduced integrand** `R^{−2(c'−ab/2)} = R^{−2(c'−2)}` [V, V2]. So on the
`R≲H` regime the front peel emits `[plain reduced integrand] · [EXTRA H^{−4}]`. The residual `H^{−4}` **cannot
be bounded by a constant times the plain integrand** (at `v=0`, `H` loses the `q₂`-direction; resolving it
needs the deeper variables and the determinant-normal coordinate `v`), and at the binding cut
`c'−ab/2 ↗ ½minAdm(redChain)` there is ZERO slack for it. Even the scalar model
`∫∫(R²+γ²y²)^{−c'}dγdy ≍ R^{1−2c'}·log(1/R)` [V, V3] — a LOG, not the exact plain power. **Conclusion:** "one
native peel + plain hIH at exactly `c'−ab/2`" is FALSE. **Required: a DECORATED IH carrying the truncated
`H^{−4}` (det-Gram remnant), OR a simultaneous multi-level discharge lemma; after full discharge the log is
absorbed by strict slack (plain hIH at `c'−ab/2+ε`).** This is precisely the original `descent-buildplan.md`
decorated descent — §7.5's plain-hIH simplification over-reached.

**Not a finiteness obstruction [V/CX Q_D].** The `H^{−4}` is integrable against the redChain measure (it is a
DECORATION the plain IH omits, not a new pole); the `v=0` branch is the equally-binding `t=3` cut
(`1+minAdm(3,4,4)=1+10=11 = minAdm(4,4,4,4)` [V]) — same threshold, only higher LOG multiplicity at the
excluded borderline `c'=11/2`. No branch below `½minAdm` was found.

---

## Decorrelated Codex read (adversarial, `codex/audit75-answer.md`) — CONVERGES, re-derived by me

My conclusion was withheld; Codex was told to hunt a decoupling/leak/obstruction on `(4,4,4,4)`. Verdicts:
Q_A **GAP** (homogeneous SUM-rule holds only AFTER the sector blow-up; the pre-sector product form gives
`min_i(p_i+1)/(2m_i)`, so the coupling is what converts min→sum — matches [V] G); Q_B **FATAL for plain-hIH**
(the `H^{−4}` residual, above); Q_C **GAP** (finite-cover CoV unbuilt, no intrinsic obstruction); Q_D
**UNPROVEN finiteness** ("no genuine finiteness obstruction — only a fatal flaw in the literal plain-IH
handoff and an unresolved finite-chart construction"). **I re-derived Q_B/Q_A/Q_D by hand (V1–V5); I did not
adopt Codex's code.** The one caution I preserve as Codex's (not mine): Q_D is UNPROVEN, not proven-finite —
"every rank-flag path has charge ≥ 11, but that every exceptional valuation of the coupled ideal is
represented by such a rank flag is unproved."

---

## Precise minimal gaps (what the build actually needs) + the definitive test

1. **[Q2, deepest] A DECORATED inner recursion** carrying the truncated det-Gram weight (`H^{−4}` shape), OR a
   simultaneous multi-level discharge lemma — NOT plain `hIH` at `c'−ab/2`. This is the real remaining lane
   content (and it is what `descent-buildplan.md`/#137 always said). The log is absorbable by strict slack
   after discharge.
2. **[bar iii] The quantitative-sector finite-cover CoV** with explicit bounded Jacobians (both coupled
   charts; `v` retained as an exceptional coordinate near the rank drop, no inverse-det; pivot charts with
   `P⁻¹` bounded). "Recurse the rank flag" alone is insufficient.
3. **[Q1 flags] The terminal free-block dim>1 lemma** (FLAG-1) and the **`a>1` rank-deficient `a(b−r)`
   bookkeeping** (FLAG-2).

**Definitive discriminating test (if the controller wants no-obstruction CERTIFIED, not just
strong-evidenced) [CX cheapest]:** principalize, on the explicit rank-one angular chart, the ideal
`I = (P·Q_tp, u(q₁+sq₂), u·v·q₂)` after inserting the two binding reduced-chain charts, and tabulate
`(ord_E I, ord_E Jac + 1)` for every primitive toric ray. **All ratios `≥ 11/2` ⟹ construction/labour gap
(finiteness holds); any ratio `< 11/2` ⟹ a genuine finiteness obstruction.** I can run this next if you want
Q_D upgraded from UNPROVEN to certified.

---

## Firmest / most-likely-to-break / next

- **Firmest.** §7.5's route (drop full-space atom; native bounded-box blow-up; coupled corner = joint density;
  coupling load-bearing) is SOUND and decorrelated-confirmed; charges ADD to `minAdm` (7 anchors); bar (i)
  PASS, bar (ii) PASS (2 flags). No finiteness obstruction found ([V/CX], all branches `≥ ½minAdm`).
- **Most likely to break the clean plan (already broke it).** The "plain hIH at `c'−ab/2`" handoff — the
  `H^{−4}` residual + zero-slack forces a DECORATED IH. §7.5's plain-hIH simplification is unavailable;
  build the decorated descent (#137).
- **Next.** Build on §7.5's native blow-up WITH the decorated IH (gap 1) + the quantitative-sector cover
  (gap 2) + the terminal/deficient flags (gap 3). If Q_D-certification is wanted, run the toric-ray
  principalization test above.
