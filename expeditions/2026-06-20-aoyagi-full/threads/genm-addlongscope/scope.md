# genm-addlongscope — SIZE/RISK scoping of the R1-UPPER sub-generic gap (#72) — AOYAGI-NATIVE re-scope

**Seat:** scout (reconnaissance), RECON + DESIGN only — no Lean built, no proof started.
**Charge (re-aimed):** the operator caught a conflation. Re-scope the sub-generic gap **Aoyagi-natively**
— the expedition is **independent of Lehalleur–Rimányi** (brief.md:27–30: no quiver, no `Core` codimension,
no `C/2`; Aoyagi's DLN RLCT via **explicit charts**, cite **S2 only** = `monomial_rlct`). The paper theorem
`thm:addlongest` (an L&R quiver result) is **off-limits** — neither cite it nor import `Core`.

---

## ⚠ RETRACTION (of this file's prior revision)

The prior revision scoped the gap as "the analytic sibling of L&R's `thm:addlongest` normal-slice iso" and
weighed building/citing that object. **That framing is RETRACTED** — it imported the L&R lens the brief
forbids. The shifted-chain structure was a *correct analogy* but the wrong home. The reference to
`Core.CThetaGeometric` / the L&R codim heart as a route (from the first, superseded redirect) is likewise
**RETRACTED** — off-limits by the independence rule. The Mathlib inventory (§4) survives unchanged; the
verdict is materially revised below.

---

## HEADLINE (controller-facing)

- **Verdict: NOT a genuine wall, read Aoyagi-natively.** The sub-generic (product-rank-deficient
  intermediate) strata are **covered by Aoyagi's own recursion** — his running-minimum corank
  `M(S) = min{M^{(s)} : s ≤ S}` in the blow-up invariant is *exactly* the device that tracks a small
  intermediate width. Aoyagi resolves the **whole product** `‖∏_{s=1}^L C^{(s)}‖²` directly, along
  **coordinate** submanifolds `{d_{ij}=0, u_{s,k}=0}` (Cases 1 & 2), and his Theorem 2 proof is **complete**
  (published, "End of Proof"). There is no separate "sub-generic" branch in Aoyagi and **no coupled-det
  object**.
- **The `det(Q_bQ_bᵀ)` borderline (cert §2.2, #72) is an ARTIFACT of the repo's peel, not Aoyagi's method.**
  It is manufactured by the repo's `sjJointResolution` lane: front-peel one boundary matrix (Schur), then
  **integrate out** the freed block `Γ` via a Gram CoV `Γ ↦ Γ·Q_b`, which produces
  `det(Q_bQ_bᵀ)^{−(M₀−t)/2}` — a *half-resolved* integrand sitting at threshold. Aoyagi never integrates a
  block out; he blows up the product and reads the exponents off the *fully* normal-crossing form, where
  "borderline integrability" cannot arise (post-resolution everything is monomial × unit, threshold exact).
- **Classification of the Lean gap: (a) — formalise Aoyagi's explicit coordinate-chart recursion.**
  Large-but-bounded, cite-only-S2 (`monomial_rlct` for the monomial endpoint). **NOT (c)** a Mathlib-missing
  resolution-of-singularities. The **AG primitives Mathlib lacks (blow-up, principalisation, determinantal
  ideals) are NOT needed** for the native route — it uses only explicit coordinate change-of-variables
  (`Jacobian.lean`, PRESENT) + monomial integrability (S2). This aligns with the repo's own r1flip (#60) /
  #58-RESOLVED "native route is bounded" pole and against the r1subgenwall (#72) "wall" pole, which is about
  the *atom* lane.
- **Size: multi-week / multi-module LABOR — dominant risk is CARRIER DESIGN, not missing mathematics.**
  Effort tier **b/c-labor** (~15–35 tides / multi-week), consistent with the controller's own #47/#51/#54
  "bounded multi-week mountain." The recurring difficulty — empirically hit ~4× (sjcarrier2/3/4, sjbuild4,
  r1carrier) — is **expressing the carrier**: the `diag(b₁,…,b_{M(S)})` shared-divisor ledger + the
  `[E_J | D_J]` block invariant preserved across the `(S,J)→(S,J+1)` and `S→S+1` double induction. That is
  data-structure + invariant-preservation engineering, not a research wall.
- **Weaker sufficient form: now easy / moot.** An upper bound on the sub-generic strata is not a separate
  object under the native route — it is a sub-part of the same coordinate recursion. There is no separate
  small shortcut to hunt because there is no separate wall to shortcut.

**One-line recommendation:** the re-aim is correct — this is **not** a genuine analytic wall. Aoyagi-natively
the sub-generic strata are covered by his coordinate-blow-up recursion; the R1-UPPER leg is the **general-L
Aoyagi recursion build** (large, bounded, cite-only-S2), whose honest cost is carrier-engineering labor, not
a Mathlib-AG detour. The genuine operator dimension is a **labour-budget** call (build the multi-week native
recursion vs. cite Aoyagi's Theorem 2 for these strata) — **not** a forced build-vs-cite over missing math.

---

## 1. The gap, stated Aoyagi-natively (no L&R, no `Core`, no `C/2`, no normal slices)

After Aoyagi's **Theorem 4** (deepest singular point, from the 2013 *Entropy* paper) sets the layer ranks
`r(s) = r` WLOG, the object is the RLCT of

$$
\Bigl\lVert \prod_{s=1}^{L} C^{(s)} \Bigr\rVert^2, \qquad
C^{(s)}\ \text{an } M^{(s)}\times M^{(s+1)}\ \text{matrix of variables},\quad M^{(s)} = H^{(s)} - r .
$$

The **sub-generic strata** (repo term) are the width configurations where an *intermediate* product rank is
forced below its generic maximum by a small `M^{(s)}`. In Aoyagi's own language this is **not a special
case** — it is exactly what the **running-minimum corank** `M(S) = min\{M^{(s)} : 1 ≤ s ≤ S\}`
(preprint p.14) records. His recursive blow-up carries the invariant

$$
\Bigl\langle \prod_{s=1}^{L} C^{(s)} \Bigr\rangle
= \Bigl\langle \operatorname{diag}(b_1,\dots,b_{M(S)})\cdot
   \begin{bmatrix} E_J & O \\ O & D_J \end{bmatrix}\cdot
   \prod_{s=S+1}^{L} C^{(s)} \Bigr\rangle,
$$

blowing up along the **coordinate** submanifold `{d_{ij}=0 (block), u_{s,k}=0}` in two branches:
- **Case 1** (`b_{J+1}=…=b_{J+J₁} ≠ b_{J+J₁+1}`): factor `u_{s,k}` out of a `J₁`-row block; sub-branches
  1(1)/1(2) decrement the multiplicity or advance `J`.
- **Case 2** (`b_{J+1}=…=b_{M(S)}`): factor `u_{S,J+1}` out of the whole remaining `(M(S)−J)×(M(S+1)−J)`
  block; advance `S`.

The `u_{s,k}` are **shared** across generators and accumulated in the `b_i` diagonal
(`b_i = ∏_{t̃_{s,k}=i-1} u_{s,k}·b_{i-1}`) — this is the "shared-divisor ledger." The induction terminates
on the ordering invariant `T_{s,k} ≤ or ≥ T_{s',k'}` and yields a normal-crossing resolution; the LCT is
read off the monomial exponents (Theorem 2 formula, Definition 3's binding-width set `M`). **Proof complete.**

**The Lean gap, Aoyagi-native:** *formalise this recursion as explicit coordinate charts* — the pullback of
`‖∏C^{(s)}‖²` under each chart is `unit·∏|u_j|^{2k}`, the Jacobian is `pos·∏|u_j|^{h}`, the charts cover a
neighbourhood of `0 ∩ {∏C = 0}`, and the monomial thresholds reconstruct the RLCT. This is precisely the
repo's `resolution_charts` Skeleton node (`Skeleton.lean:1228`) and the `SJState`/`sjRunMin` scaffolding
(`RouteMSJResolution.lean:748–775` — `sjRunMin` literally *is* `M(S)`, and `sjRunMin_antitone` is the
proved block-dimension monotonicity). The sub-generic strata are inside this one recursion; they are **not**
a distinct target.

---

## 2. Does Aoyagi hit the coupled-det borderline? NO — and why the repo's lane does

**Aoyagi's recursion never forms `det(Q_bQ_bᵀ)`.** He keeps the whole product and blows up its
*coordinate* rank-drop loci; the shared exceptional variables live in `diag(b)`. The determinant coupling
requires **integrating one matrix block out** (the Gram CoV `Γ ↦ Γ·Q_b`), a move that is *nowhere* in
Aoyagi. Three consequences:

1. **The zero-slack borderline is a property of a HALF-resolved integrand.** The repo's `gammaPeelIntegral`
   removes `Γ` but leaves the product `P = A₁·A₂···` unresolved; the leftover `det(Q_bQ_bᵀ)^{−a/2}` factor
   then sits at its integrability threshold with `a/2` **independent of `c'`** (cert §2.2). Aoyagi resolves
   `P` **fully** *before* reading any threshold, so there is no leftover borderline factor — the exponents
   are exact monomials.
2. **The "non-coordinate center forced by a dense-torus witness" claim (r1carrier, #59) does not survive the
   Aoyagi-native reading.** Aoyagi's published centers are **coordinate** submanifolds and his proof is
   complete; if that is correct, coordinate centers **suffice** for the RLCT at the deepest point. The
   dense-torus witness `[[1,1,2,1],[1,1,2,1]]` is a **positive-loss** point (off `{∏C=0}`, the only locus
   the deepest-point resolution touches — r1flip's F1, #60), so it is never on the resolved variety. It is
   an object of the *atom* lane's `det(Q_bQ_bᵀ)` geometry, not of Aoyagi's `∏C` geometry.
3. **This reconciles the flip-flop.** #72 (r1subgenwall) is **not wrong about its object** — the repo's
   *current sorry* `sjJointResolution` genuinely lives on the atom lane (it is stated in terms of
   `gammaPeelIntegral`), and on that lane the coupling is real and borderline. The error was *architectural*:
   the atom peel was substituted where Aoyagi's native whole-product recursion belongs. The re-aim fixes the
   architecture, and the wall dissolves into "the native recursion is a large build."

**Honest caveat.** This verdict rests on Aoyagi's Theorem 2 proof being **complete and coordinate-center-only
at general depth** for product-rank-deficient intermediates. I read Cases 1, 1(1), 1(2), 2 and the closure
directly: the centers are coordinate, the running-min carries the product-rank structure, the induction
closes. I did **not** re-derive every chart's monomial exponent (that is the build). If a hidden step in
Aoyagi's recursion secretly needed a non-coordinate center, the verdict would move back toward (c) — but the
published proof gives no such indication, and the whole expedition's premise (loop-prompt:39) is that
Aoyagi's explicit charts are formalisable. The residual risk is therefore **formalisation**, not soundness.

---

## 3. Size / risk re-scope (given the native route)

**Classification: (a)** formalise Aoyagi's explicit coordinate-chart recursion. **Effort tier: b/c-LABOR**
— a multi-week, multi-module build (~**15–35 tides** in this repo's unit), consistent with the controller's
prior honest ETAs (#47 "deepest mountain", #51 "genuine (S,J) double induction, bounded", #54 "multi-week").
**Not** a from-scratch AG development.

**Dominant formalisation difficulty (ranked):**
1. **The carrier data structure + invariant preservation (THE risk).** Representing
   `diag(b)·[E_J|D_J]·∏_{s>S}C^{(s)}` as a Lean type and proving the invariant is preserved across
   `(S,J)→(S,J+1)` (Case 1) and `S→S+1` (Case 2), with the **shared-divisor ledger** `b_i = ∏ u_{s,k}·b_{i-1}`
   tracking which exceptional variable divides which generator. This is where the repo hit "carrier
   insufficiency" ~4× (SJDecoration/ChainDecoration could not express the block peel). It is engineering, but
   it is *hard, un-templated* engineering.
2. **Chart algebra + termination/covering.** The Case 1/Case 2 chart formulas (Eqs. 3–5), the ordering
   invariant `T_{s,k} ≤/≥ T_{s',k'}`, and the finite-cover / termination argument (`T` strictly decreases).
   Bounded but voluminous; dependent-width casts (`Fin (M^{(s)})`) will grind.
3. **The monomial endpoint = S2.** The final "normal-crossing ⟹ RLCT" step is the *permitted* citation
   `monomial_rlct` — already carried, no new footprint. The arithmetic minimisation (Theorem 2 formula,
   Def 3 binding widths) is separately in-hand (repo's `cleanCore`/`printedCore`, `minAdm`).

**Top 3 risks:**
1. **Carrier re-architecture cost** (as above) — the empirically-realized risk; a wrong carrier wastes tides.
   Mitigation: the `SJState`/`sjRunMin` stub is the right skeleton; the ledger must be designed before build.
2. **Casts / chart bookkeeping explosion** uniform in `L` and the widths (dependent `Fin` arithmetic across
   the double induction).
3. **A latent non-coordinate subtlety in Aoyagi's recursion** (low probability, high impact) — see §2 caveat.
   Retire cheaply with the pen-and-paper probe in the Reflection before committing formaliser weeks.

**Tractability at v4.29 via the native route (coordinate CoV + monomial endpoint, no AG primitive):** HIGH
for the mathematics (Aoyagi's proof is coordinate-only and complete); the uncertainty is *labour*, not
feasibility. Contrast the atom lane (prior revision): ~35% general / ~60% forces AG detour — those numbers
were for the *wrong* (atom) object and no longer bind the decision.

---

## 4. Mathlib v4.29 inventory (unchanged facts; re-read for the native route)

**PRESENT and SUFFICIENT for the native route:**
- `Matrix.rank`, `Matrix/SchurComplement`, `Matrix/Determinant/*` (chart algebra).
- **`MeasureTheory/Function/Jacobian.lean`** (`integral_image_eq_integral_abs_det_fderiv_smul` + `lintegral`
  variants) — the explicit coordinate change-of-variables the blow-up charts need. This is the workhorse;
  the repo's banked atoms already use it.
- `LinearAlgebra/ExteriorPower` (available if any minor norm is wanted; the native route may not even need it).
- The permitted S2 citation `monomial_rlct` (normal-crossing ⟹ RLCT) is the endpoint.

**ABSENT — but NOT NEEDED by the native route** (they were only implicated by the retracted atom-lane
framing): algebraic-geometry blow-up, resolution of singularities, principalisation, determinantal ideals,
normal-crossing divisors as objects, Plücker normal form. Aoyagi's blow-up is realised as **explicit
coordinate charts** (finite family + monomial pullback + monomial Jacobian + cover), which is a *statement
about integrals*, not an invocation of AG machinery — so the missing AG primitives do not gate it.

---

## 5. Weaker sufficient form

Under the native route the question largely dissolves: we need finiteness (box-threshold) for
`c' < ½·minAdm`, and Aoyagi's recursion delivers the *exact* RLCT, which is `≥` any such `c'` immediately.
There is no separate borderline factor to dominate (that was the atom lane). A genuinely weaker target — a
crude upper bound on just the sub-generic strata — is a **sub-part** of the same coordinate recursion (the
charts covering the strata where `M(S)` has already dropped), not a different, smaller lemma. So: **no
separate shortcut exists because there is no separate wall**; the "weaker form" saving is subsumed into
"build fewer chart cases," which the recursion structure already organises.

---

## 6. Build-vs-cite under the corrected framing

- **(A) BUILD** = formalise Aoyagi's general-L coordinate-blow-up recursion (the carrier + `(S,J)` double
  induction + Case 1/Case 2 charts + `monomial_rlct` endpoint). Honors the brief (explicit charts, cite S2
  only). Cost: multi-week/multi-module labor; dominant risk = carrier design. This IS the R1-UPPER leg — the
  sub-generic strata are not a separable extra.
- **(B) CITE** = cite Aoyagi's **Theorem 2** (the RLCT value) for the sub-generic strata (or for R1-UPPER
  wholesale). This is a **labour-saving** cite of *the very paper whose charts the expedition formalises* —
  the mildest possible citation (the expedition's subject), but a real **character** change: the geometry for
  those strata is then *cited*, not *built from explicit charts*, departing from the brief's
  "explicit charts, cite S2 only." **Footprint accounting is the controller's** — under the L&R-independent
  framing the R1-UPPER leg's whole point is to derive the geometry from charts, so a new Aoyagi-Theorem-2
  interface would be a genuine addition to the permitted-citation set (`monomial_rlct` only), unlike the
  payoff's separate value citation. I flag this rather than assert footprint-neutrality (the prior revision's
  neutrality claim was an L&R-framing artifact and is retracted).

**Recommendation:** per the brief's "explicit charts, cite S2 only" mandate and the corrected (bounded)
verdict, the default is **(A) BUILD** — it is large labor, not a wall, and no Mathlib-AG detour is forced.
Reserve (B) for a pure labour-budget decision by the operator.

---

## Reflection (scout close)

- **Most likely to advance the expedition:** the **architectural correction** — the sub-generic gap is the
  atom lane's artifact, and Aoyagi-natively the strata are covered by the running-min coordinate recursion.
  This dissolves the #72 "wall" into "the general-L Aoyagi recursion is a large build," re-aligning the
  R1-UPPER leg with the controller's own #47/#51/#54 reads and the brief.
- **Most likely to break:** the **carrier**. The math is bounded (Aoyagi's coordinate proof is complete), but
  the formalisation has hit carrier-insufficiency ~4× — a wrong carrier design will keep costing tides. The
  claim at genuine (low) risk is §2's "coordinate centers suffice at general depth" *for the formalisation*;
  the math is Aoyagi's, but a build could still discover a chart-level subtlety.
- **Next computation that would clarify (cheap, before committing formaliser weeks):** a **pen-and-paper**
  pass reproducing Aoyagi's Case 1/Case 2 recursion by hand on the binding `(3,3,3,4) r=0` example
  end-to-end — verify the coordinate charts fully resolve `‖∏C^{(s)}‖²` (monomial × unit, no leftover
  determinant), the running-min `M(S)` steps correctly, and the monomial thresholds reconstruct
  `½·minAdm(3,3,3,4)=7/2`. If it closes with coordinate charts (expected), (A) is firmly bounded and the
  carrier design can be pinned from the worked example. This is the `witness`-seat probe that should precede
  any build — and it directly tests the §2 caveat.

**Decorrelated Codex (high, neutral prompt):** consult fired on the Aoyagi-native question
(`codex/aoyagi-prompt.md`); result folded into the addendum below on completion.
