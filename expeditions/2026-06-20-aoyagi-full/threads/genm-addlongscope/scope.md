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

**One-line recommendation:** the re-aim is correct — this is **not** a genuine analytic wall. See **§0** for
the Voight-shortened-algebra + analytic-transport sizing the operator's latest steer asks for; the controller
drives the build, so this is a **size/tide** read, not a build-vs-cite call.

---

## 0. REFINEMENT — Voight-shortened algebra + the analytic transport (the operator's latest steer)

**Steer:** independence is *judicious* — light reuse of the in-tree Voight/Ext-codim backbone to shorten the
**algebra** is fine; the **substance** is the **analytic RLCT-transport** for the sub-generic strata. Drop
build-vs-cite; report SIZE. All claims below verified against the repo.

### Q1 — is the algebra (normal-slice iso) reducible to the in-tree Voight/Ext-codim? How much is free?

**Substantially free — a light wiring job, not a build.** The backbone is proved and sorry-free in `Core`:
- `Core.CTheta.codimForm_update_corner` (`CTheta.lean:215`) — **the `addlongest` codim heart**, sorry-free:
  the codim quadratic form never reads the `(0, N)` "longest-root" corner (proved by direct index bookkeeping,
  no analysis). Plus `dropCorner` (`CTheta.lean:~228`, the explicit **rank-`r`→rank-`0` shift map**) and
  `dminus d r = d − r` (the shifted dimension vector). This is exactly the codim-blindness that makes adding
  longest roots free.
- `Core.OrbitCodim` — **Voigt's lemma is PROVED in-engine** (`VoigtDischarge.codimRep_orbitRankLocus_eq_orbitLinearCodim`,
  char 0 + alg-closed): `codim Ō_M = orbitLinearCodim M = dim Ext¹(M,M)`. So the codim equality **upgrades to
  the normal-slice iso** (Ext-vanishing of the injective-projective longest-root module) essentially for free.

**Caveat (the load-bearing distinction):** this delivers the iso of the normal slices **as varieties / the
codim equality**. It does *not* by itself give that the **loss germ** corresponds under the iso — that is the
analytic step (Q2), not the algebra.

### Q2 — SIZE/RISK of the analytic transport. Bounded, or a hard gap? Does Aoyagi's own recursion give the shifted-chain RLCT?

**The transport is a BOUNDED analytic build — NOT a hard gap — and its RLCT-invariance primitives already
exist in-tree and are already used at L=2.** Three legs, all in hand:

1. **Aoyagi's own recursion gives the shifted-chain RLCT — YES.** The shifted chain `(M₁−q,…,M_N−q)` is just a
   DLN width vector; its RLCT is Aoyagi's Theorem 2 at shifted widths = the repo's `resolution_charts` /
   `minAdm` / `lambdaCore` there. So the *target value* of the transport is Aoyagi-native and bounded. (It is
   an **instance of the R1-UPPER recursion at smaller widths**, i.e. it closes by the descent — see the
   induction-measure caveat below.)
2. **The RLCT-through-iso primitives are BUILT** (`Skeleton.lean` / `Foundations/S1*`, all proved, used in the
   L=2 D1 close `D1L2ExplChartClose2`):
   - `rlct_unit_invariant` (S1.3 = **Aoyagi Lemma 1**, "RLCT depends only on the ideal");
   - `rlct_germ_local` (S1.4, germ-locality);
   - `rlctAtOn_comp_homeomorph` (`S1Fubini:54`, **RLCT invariant under an analytic iso / homeomorphism** — the
     transport primitive);
   - `rlctAtOn_congr_germ` (`S1ChartTransfer:28`);
   - `rlct_additive_smooth_block` (S1.5) — `λ(Σxᵢ² + G²) = n/2 + λ(G²)`, **exactly the "identity-block ⟹
     regular shift + shifted-chain core" split** the rank-shift produces (the `I_r` block gives regular
     directions; the core is the shifted chain). This is the analytic realisation of the iso's
     loss-compatibility.
3. **The det coupling is NOT on this route** (last-round finding, decorrelated-Codex-confirmed): it is
   manufactured only by the atom lane's "integrate-out-`Γ` via Gram CoV." The transport realises the
   normal-slice iso as an explicit chart and reads Aoyagi's RLCT on the shifted chain — the determinant never
   forms.

**Hardest analytic sub-piece:** constructing the **explicit analytic iso / homeomorphism** (general-`L`) that
carries the sub-generic-stratum **loss germ** to `(regular smooth block) + (shifted-chain core germ)` with a
bounded/unit Jacobian, so `rlctAtOn_comp_homeomorph` + `rlct_additive_smooth_block` + `rlct_germ_local` fire.
This is the **same class as the D1 general-`L` explicit chart** (the L=2 instance `D1L2ExplChartClose2` is
DONE; the general-`L` is the D1 leg's known multi-tide build, #120). Bounded analytic labor, not a new theory.

**Two honest caveats to verify before building:**
- **Induction measure.** The shifted chain `(M−q)` is the **same length** as `M` (not arity-smaller — cert
  §1a: "not any `redChain t M`"). So it does *not* close under a plain arity-IH; it closes under **Aoyagi's
  well-founded descent** (running-min corank `M(S)` / the `T`-vector ordering). The transport therefore folds
  the sub-generic strata **into** the main Aoyagi recursion (they stop being a *separate* target) rather than
  eliminating that recursion. Hence Q2 leg 1's "closes by the descent," not "a trivial IH."
- **Smooth vs general additivity.** `rlct_additive_smooth_block` is scoped to the **smooth/regular** block
  (the general real-analytic disjoint additivity, Aoyagi App. C Lemma 2, is a flagged **roadmap** lemma — the
  bare form is false, the general form needs Laplace/Tauberian). The rank-shift's identity-block directions
  **are** regular (sum-of-squares), so the smooth form should suffice — as it did at L=2 — but this must be
  checked for the general-`L` sub-generic chart, not assumed.

### Size (the tide read)

- **Algebra (normal-slice iso):** ~**1–2 tides** of wiring on the sorry-free Core Voight/corner-blindness
  results (import + Ext-vanishing upgrade + loss-block bookkeeping). Not a build.
- **Analytic transport (the substance):** ~**5–12 tides** — dominated by the general-`L` explicit iso-chart
  (D1-class) + the per-stratum/per-`q` chart family + wiring the existing invariance/additivity primitives.
- **Gated on** the shifted-chain RLCT being available from the main R1-UPPER recursion (`resolution_charts`,
  the separate Aoyagi-native build) — the transport *plugs into* that, it does not replace it.

**Effort tier:** the sub-generic transport is a **bounded analytic build (tier b), ~6–14 tides total**,
materially smaller than a standalone Aoyagi carrier recursion because it **offloads the resolution to the
shifted-chain instance** of the main recursion and **reuses proved RLCT-invariance primitives**. Residual
risk = the general-`L` iso-chart (D1-class, real but bounded) + the two caveats — **not** a hard analytic gap,
**not** a Mathlib-AG detour.

---

## 1. The gap, stated Aoyagi-natively (no `C/2`; light Voight reuse now permitted — §0)

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

**Decorrelated Codex (high, neutral prompt) — CORROBORATES the re-frame independently** (`codex/aoyagi-prompt.md`,
`codex/aoyagi-answer.md`):
- **`det(Q_bQ_bᵀ)` is a ROUTE ARTEFACT, not intrinsic.** "The rank-deficient intermediate strata are real,
  and some bind. What is not intrinsic is the inverse Gram factor… In the native recursion, `Γ` is not
  integrated out as a standalone Gaussian block; the product ideal is transformed directly, and the shared
  divisors remain in the `b_i` ledger." It cited `RouteMSJFreedPeel.lean:25` (the freed-`Γ` route carries a
  `Q_bQ_bᵀ` positive-definite hypothesis that "fails on bottleneck/rank-drop charts") as the direct evidence.
- **The dense-torus / non-coordinate-center obstruction does NOT survive.** "It may be a correct obstruction
  to principalising the Gram determinant of a matrix product. But that is not the same object as resolving
  the zero locus of `‖∏C‖²`… If the witness is a positive-loss point, it is off `{∏C=0}`… any pole there
  comes from the marginalised Gram density," i.e. self-inflicted by the Gram route.
- **Gap classification: (a)**, "large but bounded, citing only the monomial normal-crossing integrability
  endpoint." The `(c)` appearance is "a self-inflicted route wall, not an intrinsic DLN wall."
- **Dominant difficulty: (i) the carrier data structure** — needs `S, J, M(S)`, residual block dims,
  branch/rank-profile, and crucially a **per-generator support map** `support : Gen → Finset DivVar` with the
  *sharing* identity (which `u` divides which generators). "A per-row multiplicity is too weak" — corroborated
  by the repo's own `theory/aoyagi-2023-reproduction/verify-r1-diagb-334.md` (the `(3,3,4)` core binds at
  `rlct = 4`; a threshold-only/per-row recursion returns `3` — undercount by 1 on a value-setting branch, so
  the shared `diag(b)` support is **necessary**, not decorative).
- **Size:** "6–12 person-weeks for a serious Aoyagi-native core recursion, more like 10–16 if the integral
  plumbing and finite chart cover are included cleanly" — somewhat tighter than my ~15–35-tide read (the repo
  already has substantial infrastructure); the ranges are compatible. **Top risk (agreed):** "building a
  carrier that is still too weak and discovering late that another sharing relation is missing." Chart algebra
  "large but more mechanical"; termination/covering "finite/lexicographic once the state is right."
- **Practical call:** "If the goal is a fully from-scratch Lean RLCT proof, build Aoyagi-native. If the goal
  is the DLN fibre theorem with controlled citation footprint, cite Aoyagi's exact RLCT. Do not spend effort
  principalising `det(Q_bQ_bᵀ)` unless the project explicitly chooses the Gram route."

**Net:** two independent lines (this scout reading Aoyagi's primary proof + a decorrelated Codex) agree the
sub-generic "wall" is a route artefact, the gap is a bounded Aoyagi-native coordinate-chart build
(~6–16 pw / ~15–35 tides), and the make-or-break is the shared-divisor carrier. The **first** (general,
atom-lane) consult (`codex/answer.md`) is retained for provenance but its numbers were for the retracted
object.
