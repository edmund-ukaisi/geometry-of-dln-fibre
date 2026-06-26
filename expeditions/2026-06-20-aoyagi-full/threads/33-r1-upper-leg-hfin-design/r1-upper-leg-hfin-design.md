# R1-general UPPER leg (hfin / `cover_le`) — reachability/cost design read (obstruction-leaning)

**Seat:** `pen-and-paper` (obstruction-leaning; honest cost read decisive). **Date:** 2026-06-26.
**Gate:** the general-`M` UPPER leg of the R1 gate `resolution_charts` — `hfin` / `cover_le` /
`rlctAtOn ≥ ½·minAdm`, i.e. `∫⁻_{routeMBaseNbhd M} |routeMCore M|^{−c'} < ⊤` for `c' < ½·minAdm M`
(`routeMCore_threshold_lt_top`, the N4 skeleton at `RouteMSchur.lean:284`).
**Method:** read the two done upper-leg anchors + the banked atoms + the `RouteMSchur` N1–N4 spec; exact
sympy/symbolic (the cancellation bound, the general-`k` Cramer shear, the recursion-threshold arithmetic);
one decorrelated `local-codex-consult` (gpt-5.x, xhigh, conclusion withheld). Scripts `scripts/*.py`;
Codex prompt/answer `codex/upper-leg-{prompt,answer}.md`.

---

## VERDICT (one line)

**NEEDS-DESIGN-then-build, NOT a build-ready tide and NOT a research wall** — and the load-bearing
worry the brief flagged is RESOLVED in the negative: **the corank-≥2 obstruction that broke the
threshold-only *value*-lane recursion does NOT break the upper-leg comparison.** The single direction of
the Schur comparison that hfin actually needs (the LOWER bound) holds with a UNIFORM positive constant at
*every* corank, reducing exactly to the classical complete-pivoting shear bound (`‖M21·M11⁻¹‖ ≤ 1`), which
I verified exact for general `k`. The cost is **not** the comparison (N2b); it is the **depth-`r`
measure-theoretic recursion assembly** (the WellFounded-on-corank `recStep` + the parameter-dependent
per-chart change-of-variables), for which no general-DEPTH Lean template yet exists (both done anchors are
fixed-depth, hand-composed). Decorrelated Codex (xhigh) independently returned **needs-design-then-build**,
the SAME lower-bound-suffices reduction with the SAME cancellation mechanism, and ranked the measure-
theoretic cover plumbing the heaviest — concurring on the verdict and the crux while differing (honestly)
on the within-design risk ordering.

---

## 1. The two DONE upper-leg anchors use TWO DIFFERENT mechanisms — and NEITHER is N2b

Reading the actual proofs (not the `RouteMSchur` spec), the two banked corank-2 hfin instances are
**S2-free, sorry-free**, and reach `½·minAdm` by **different** routes — and crucially **neither uses the
abstract `RouteMSchur` N2b two-sided Schur comparison** (which is still `sorry`):

- **`(4,4,2,2)`** (`RouteM4422Hfin.lean`): the **iterated matrix-fibre** route. Tonelli outside-in, peel
  each layer by `fibre_lintegral_mul_le` (`∫_X frobSq(X·Y)^{−c'} ≤ fibreConst·frobSq(Y)^{−c'}`, threshold
  `(rows X)/2`), terminate at the `A2` Morse leaf. **No Schur split, no corank stratification at all** —
  threshold `p/2 = 2 = ½·minAdm` carried by the last layer. (Route **F**.)
- **`(3,3,4)`** (`RouteM334Hfin.lean` + `RouteM334Ratiofin.lean`): the **explicit radial-Schur** route.
  Its own headline docstring states the abstract `RouteMSchur` recStep-atlas "is NOT on this path." The
  binding corank-2 core forces a radial blow-up (`A0 = a·R`, 9 max-modulus-entry charts), per chart the
  one-sided lower bound `frobSq(R·A1) ≥ (1/5)·(∑_j T_j² + frobSq(Δ·S))` (`frobSq_angularR_ge`, a CONCRETE
  Schur normal form `angularR`/`schurNF`, ratios `|γ|≤1`), then an explicit `z`-change-of-variables onto
  the banked `resolved334_box_lt_top`. (Route **S**, hand-instantiated at depth 2.)

**Why this matters for the general read.** Route F is INSUFFICIENT at a binding corank-≥2 RRR core: the
fibre threshold there caps at `3r/2 ≤ 3/2 ≪ 4` (the (3,3,4) docstring confirms it "caps … so a Jacobian-
weighted blow-up is genuinely forced"). So general `M` with a binding corank-≥2 core genuinely needs Route
S — the radial-Schur recursion `RouteMSchur` N1–N4 proposes. The done (3,3,4) is Route S **at depth 2,
hand-coded**; the general `M` needs Route S at **arbitrary depth, uniform in `r`**.

**Decisive observation (the (3,3,4) anchor already does it one-sided).** The (3,3,4) anchor proves only a
ONE-SIDED lower bound (`≥ 1/5·…`), NOT the two-sided sandwich. So the actually-built mechanism already
confirms the brief's hidden lever: **hfin needs only the LOWER direction.**

## 2. The load-bearing question — does the LOWER comparison hold UNIFORMLY at corank ≥ 2? **YES (exact).**

The brief's load-bearing test: does the two-sided uniform Schur comparison (N2b) hold at corank ≥ 2, or is
there a rank profile where `frobSq(R·S)` is NOT two-sided-comparable with uniform constants? **The honest
answer reframes the question:** the *two-sided* sandwich is **overspecified** — hfin (`∫ F^{−c'} < ⊤`)
needs only `c₀·D ≤ frobSq(R·S)` (the LOWER bound), since `c' > 0 ⟹ frobSq(R·S)^{−c'} ≤ c₀^{−c'}·D^{−c'}`.
The UPPER half of N2b is needed only for sharpness/value-matching, which is a SEPARATE (already-proven)
lane. **The LOWER bound holds uniformly at any corank**, by exact algebra:

**The reduction (exact, `scripts/n2b_exact_cancellation.py`).** With `R = [[M11,M12],[M21,M22]]`, the det-1
column reparam `S = U·(P;Q)`, `U = [[I,−M11⁻¹M12],[0,I]]`:

    (R·S)_top = M11·P =: top,   (R·S)_bot = M21·P + Sc·Q,   Sc = M22 − M21·M11⁻¹·M12,
    frobSq(R·S) = frobSq(top) + frobSq(M21·P + Sc·Q),   D := frobSq(top) + frobSq(Sc·Q).

The danger the brief names — `frobSq(R·S)` small while `D` bounded away from 0 — is **bottom-block
cancellation**: `M21·P + Sc·Q ≈ 0` while `Sc·Q` is large. It IS possible, but the cancellation cost is
**bounded**, because the cancelling term is controlled by the top:

    M21·P = (M21·M11⁻¹)·(M11·P) = F·top,    F := M21·M11⁻¹  (the complete-pivoting shear).

Cancellation `Sc·Q ≈ −F·top` forces `‖top‖` large in lockstep, and the top term `frobSq(top)` records
exactly that cost. Quantitatively (the chain, all standard inequalities):

    frobSq(Sc·Q) = frobSq((M21·P+Sc·Q) − M21·P) ≤ 2·frobSq(R·S)_bot + 2·frobSq(F·top)
                  ≤ 2·frobSq(R·S)_bot + 2‖F‖²·frobSq(top)
    ⟹ D ≤ (1 + 2‖F‖²)·frobSq(top) + 2·frobSq(R·S)_bot ≤ max(1+2‖F‖², 2)·frobSq(R·S)
    ⟹ frobSq(R·S) ≥ c₀·D,   c₀ = 1 / max(1 + 2‖F‖²_F, 2).

On the bounded complete-pivoting cell `‖F‖²_F ≤ k(r−k)` (each of `k(r−k)` shear entries `|·| ≤ 1`), so
`c₀ ≥ 1/(1 + 2k(r−k))` — **a UNIFORM positive constant, dimension-only.** (Codex's cleaner derivation:
`(X,Y) = (X, FX+Y) + (0,−FX)` gives `c₀ = (1+√(k(r−k)))⁻²` — same mechanism, sharper constant.)

**The exact stress tests (all pass):**
- `scripts/n2b_shear_and_ratio.py` (C): on the **full-cancellation line** `Sc·Q = −F·top`, the ratio is
  `frobSq(top)/(frobSq(top)+frobSq(F·top)) = 1/(1+‖F‖²)`, worst case `1/3` at `r=3,k=1` (`|F|=1`) —
  **bounded away from 0**, matching `c₀`. The worst case is real, and it is bounded.
- `scripts/n2b_shear_and_ratio.py` (B), MC guide: `inf F/D` over complete-pivoting cells stays ABOVE the
  predicted `c₀` at `r=3,4,5` (0.32, 0.27, 0.27 vs 0.20, 0.14, 0.11). Consistent (a guide, not the cert).

**The single fact it all reduces to: the complete-pivoting shear bound `‖M21·M11⁻¹‖_entries ≤ 1` (R2).**
Verified EXACT for general `k` (`scripts/r2_shear_general_k.py`): each shear entry equals
`(a k×k minor of R)/det(M11)` by the row-replacement Cramer identity (symbolically confirmed for
`(r,k) = (3,1),(3,2),(4,2),(4,3)`), and with `M11` the **max-modulus** `k`-minor, `|numerator| ≤ |det M11|
⟹ |·| ≤ 1`. **It even survives the `det(M11)→0` edge** (concrete `det M11 = 1/1000` max-modulus cell:
shear `= [1,0]`, both `≤ 1`) — the numerator minor shrinks in lockstep, no blow-up. Numeric worst over
20k cells per `(r,k)` up to `(5,3)`: `0.9999…`, never `> 1`.

**Contrast with the value-lane break (kept separate, per the levels discipline).** The threshold-only
recursion BREAKS at corank ≥ 2 at the **VALUE** level: a per-row weight multiplicity cannot encode WHICH
divisor variables are SHARED, and sharing changes the Newton polytope/RLCT (⟨δx,δy⟩ rlct ½ vs ⟨δ₁x,δ₂y⟩
rlct 1). That break is about computing `⨅ monomialThreshold = ½·minAdm` correctly. The upper leg takes
that VALUE as given (proven separately, `routeLayerAtlas_value`) and asks only for FINITENESS strictly
below it. The S5c box-comparability counterexample (`S0=εE12,S1=εE21 ⟹ R=0, ∏S≠0`) is a DIFFERENT object
(the LDU telescope `∏S_s` on a non-germ box), not the single-step `frobSq(top)+frobSq(Sc·Q)` split on the
bounded complete-pivoting cell — and there `top` is the genuine top rows of `R·S`, not a separate factor,
so the cancellation is charged to `frobSq(top)` and stays bounded. **No corank obstruction here.**

## 3. The recursion threshold arithmetic composes (exact, 30/30)

The disjoint-sum recursion `λ(r,p) = min(r²/2, min_{1≤j≤r}(jp/2 + λ(r−j,p)))`, `λ(0,p)=0`, matches
`½·minAdm(r,r,p)` (the binding RRR core's value) **30/30** over `r∈2..6, p∈2..7`
(`scripts/threshold_recursion_check.py`; the cert's 10/10 widened). The three terms: `r²/2` = the radial
`a`-axis divisor; `jp/2` = the full-rank Morse-top block `frobSq(M11·P)`; `λ(r−j,p)` = recurse on the
corank-`(r−j)` Schur core. The "thresholds ADD" bridge (`jp/2 + λ(r−j,p)`) is the **residual-power**
mechanism — and it is **already banked sorry-free, S2-free, general-`n`**: `radial_morse_residual_power_le`
(`RadialResidualPower.lean:157`), `∫_{[−T,T]^{m+1}}(∑Pᵢ²+w)^{−c'} dP ≤ Cresid·w^{−(c'−(m+1)/2)}`, which
feeds the core at the shifted exponent `c'' = c' − jp/2`. This retires the genuinely-new analytic atom the
cert and thread-28 Codex both flagged.

## 4. The single heaviest sub-piece + the honest risk

**Heaviest: the depth-`r` measure-theoretic recursion assembly — the WellFounded-on-corank `recStep` +
the parameter-dependent per-chart change-of-variables (N4, with (b)/(c) tightly coupled).** NOT the N2b
comparison (N2b's needed direction is a finite-dimensional bounded-shear inequality, §2 — clean). The
reasons:
- **No general-DEPTH template exists.** Case222 (`myF222_threshold_lt_top'`) and the (3,3,4) hfin both use
  `recStep` at FIXED, shallow depth, **hand-composed** (`recStep {…} p` written out, depth ≤ 2). The N4
  skeleton proposes a genuine `termination_by`-style WellFounded recursion on corank that runs the
  cover → radial blow-up c-o-v → minor-pivot Schur peel → recurse at EVERY level uniformly in `r`. That
  recursion object does not exist yet; it is the design content.
- **Dependent dimensions.** The Schur complement `Sc : (r−j)×(r−j)` changes the matrix type at each level;
  the recursion is over a dependent `Fin (r−j)` arity — `Fin`/dimension casts on the chaining are the Lean
  fight, not the analysis.
- **The per-level c-o-v is parameter-dependent.** Each level's radial blow-up + det-1 triangular reparam
  is a `lintegral_image_eq_lintegral_abs_det_fderiv_mul` with a fresh null-slice drop and `InjOn`-off-a-
  plane; the API burden (restricted domains, finite covers, measurability, ae facts, Tonelli rearrangement)
  is the weight Codex ranked #1. The atoms exist per-instance (the (3,3,4) `cov` template, `g5_pivotNode`,
  `coordZero_null`, `pivotBlowupOnDeriv_det`); the UNIFORM-in-`r` fold over the minor-pivot cover is new.

**The honest risk.**
- *What makes me too OPTIMISTIC:* the WellFounded-on-corank recursion over **dependently-typed** Schur
  blocks could be a multi-week Lean fight on its own (the dependent-`Fin` arity casts + the nested
  minor-pivot `argmaxCellOn`-over-minors cover, which is itself not-yet-a-verbatim-reuse — flagged in
  `minorpivot-cert.md` as the one piece needing a standalone prototype). The MATH being settled (§2, §3)
  does not bound the measure-plumbing cost; Codex's Q4 names exactly this — "the threshold value being
  known is not the same as a Lean-usable finiteness certificate through the recursive charts."
- *What makes me too PESSIMISTIC:* the iterated-fibre Route F (banked, sorry-free, no Schur split) already
  discharges ALL "fat-decreasing" `M` (binding minimum at a single layer's `p/2`); Route S is forced ONLY
  on the binding corank-≥2 RRR-core family (the `(n,n,p)`, `n≥3` ≈22% of cases). So the GENERAL upper leg
  may be a DISPATCH: Route F for most `M`, Route S only on the corank-≥2 binding strata — and Route S's
  depth is bounded by the corank, not `L`. If the dispatch is clean, the hard recursion is confined.

**A concrete build-now instance that would de-risk it (the (3,3,3,3) analog for the lower leg).** Yes — a
**depth-3** Route-S instance (a `corank ≥ 3` binding core, the smallest being an `(n,n,n,p)` or
`(4,4,p)`-type core whose recursion needs TWO nested Schur peels, not one). The done (3,3,4) is depth-2
(ONE Schur peel); it does NOT exercise the WellFounded recursion at depth ≥ 2 or the *nested* minor-pivot
cover. Building one depth-3 hfin instance would force the genuine recursion bookkeeping and the
dependent-dimension cast at one extra level — exactly the heaviest piece — banking a third instance and
stress-testing the N4 design before the general lift. (It is the upper-leg twin of shipping (3,3,3,3) for
the lower leg.) Whether it is worth banking NOW vs roadmapping behind the (A)/(B) decision is the
controller's call; it is a bounded build, not a research item.

## 5. Codex (decorrelated, xhigh, conclusion withheld) — CONCURS, no rubber stamp

Prompt `codex/upper-leg-prompt.md` framed objects + facts + the four sub-questions, **withholding** my
verdict (whether the lower bound is a wall, the heaviest piece, the classification). Answer
`codex/upper-leg-answer.md`:
- **Q1 (concurs):** "one direction suffices … the reverse inequality is useful for sharpness/value
  matching, but not for the hfin upper leg." (Independent of my §2.)
- **Q2 (concurs, sharper):** lower bound holds uniformly at corank ≥ 2; `c₀ = (1+√(k(r−k)))⁻²`; SAME
  cancellation mechanism — "cancellation forces `X = AP` large … the top term `‖AP‖²` records exactly that
  cost." Derived independently via `(X,Y)=(X,FX+Y)+(0,−FX)`.
- **Q3 (differs, honestly):** ranks **(c) the depth-`r` Tonelli/cover plumbing heaviest**, then (b)
  WellFounded recStep, then (a) N2b "not the bottleneck." I lean (b) heaviest (no general-depth template);
  Codex leans (c) (the measure API burden). These are the SAME region (the recursion assembly IS the cover
  plumbing) and the disagreement is a within-design ordering, not a verdict split — both put N2b last.
- **Q4 (concurs):** "needs-design-then-build, not a research wall." Most-likely-wrong: "using only numeric
  threshold data … the threshold value being known is not the same as having a Lean-usable finiteness
  certificate through the recursive charts" — exactly my optimism risk.

No rubber stamp: Codex independently produced a different (sharper) constant and a different heaviest-piece
ordering, while corroborating the verdict and the load-bearing reduction.

## Close (the discipline trio)

- **Firmest result.** The corank-≥2 worry is RESOLVED in the negative: the LOWER direction of the Schur
  comparison (the only direction hfin needs) holds with a UNIFORM dimension-only constant
  `c₀ = 1/(1+2k(r−k))` (Codex: `(1+√(k(r−k)))⁻²`) at any corank, reducing exactly to the classical
  complete-pivoting shear bound `‖M21·M11⁻¹‖ ≤ 1` (verified exact for general `k`, surviving `det M11→0`).
  The recursion threshold composes 30/30, and the "thresholds-add" residual-power atom is banked sorry-free
  general-`n`. **Verdict: needs-design-then-build.**
- **Most likely to break it.** The depth-`r` WellFounded-on-corank recursion over DEPENDENTLY-TYPED Schur
  blocks (the `Fin (r−j)` arity casts + the nested minor-pivot cover) being a heavy Lean fight independent
  of the settled math — the cost is the measure-theoretic recursion assembly, not the comparison.
- **Next construction / consult.** (a) Build ONE depth-3 Route-S hfin instance (a corank-≥3 binding core)
  to exercise the WellFounded recursion + nested minor-pivot cover at depth ≥ 2 — the upper-leg twin of
  (3,3,3,3), de-risking N4 before the general lift; OR (b) roadmap N4 behind the (A)/(B) decision. The one
  open piece for a follow-up consult: the exact Lean shape of the **nested minor-pivot `argmaxCellOn`-over-
  minors cover** (the not-yet-verbatim-reuse flagged in `minorpivot-cert.md`), best prototyped standalone.

## Scope / levels kept separate

- **This is the `≥` / hfin / `cover_le` UPPER leg ONLY.** The `rlctAtOn = ⨅ monomialThreshold = ½·minAdm`
  VALUE is proven separately (`routeLayerAtlas_value`); the `rlct = ½·codim` reading still rides the cited
  S2 bound (Aoyagi/Watanabe). Not addressed here. The UPPER half of the N2b sandwich (sharpness) is the
  value lane, also separate.
- **Proved (exact symbolic):** the lower-bound cancellation chain + uniform `c₀`; the general-`k` Cramer
  shear bound `≤ 1` (incl. the `det→0` edge); the recursion-threshold match 30/30. **Banked-confirmed:**
  the residual-power "thresholds-add" atom is general-`n` sorry-free.
- **Inference (not certificate):** that the depth-`r` recursion assembly is "one design pass + a bounded
  build" rather than a multi-week dependent-type fight — this is the cost read, not a proof; the math
  being settled does not bound the Lean measure-plumbing cost (Codex's Q4 caveat).
- **Decorrelated-corroborated:** Codex (xhigh, conclusion withheld) returned needs-design-then-build, the
  same lower-bound-suffices reduction, the same cancellation mechanism, N2b-not-the-bottleneck. Differed
  (honestly) on the within-design heaviest-piece ordering and produced a sharper constant.
