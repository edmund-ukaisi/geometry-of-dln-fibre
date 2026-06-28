# Synthesis — `rlct-bridge` (controller's internal read; flushed every tick)

Not a deliverable. Current integrative ground + drift-guard + recovery substrate after compaction.

## Where we are (tick 0 — setup, 2026-06-27)

Expedition stood up off merged `dev` (`origin/dev` = `e2fbf7fb`, the fibration-geometry PR #12 merge),
on branch `expedition/rlct-bridge`. Base build merged-green by construction (fibration-geometry close
green-gate; dev Lean tree = that tree). The destination: replace `RlctInterface.cited_aoyagi_dln`.

**Operator-fixed scope (2026-06-27):** the RLCT bridge, with the **thin cited interface + prove all DLN
geometry** seam — cite the general analytic theorems (rlct-of-a-quadratic; Watanabe `rlct ≤ ½·codim`;
the resolution criterion "all divisors `≥ ½·codim` ⟹ `rlct ≥ ½·codim`") as a thin named `RlctInterface`;
prove all DLN-geometric inputs against it. Roll in the fibration-geometry bundle-completion residual
(projection compatibility + R1). Open with the `(2,2,2,2,2)` deepest-stratum computation.

## The seam, precisely

```
rlct(lossDLN) = ½·codim
  = [rlct ≤ ½·codim]        (Watanabe-universal; smooth locus achieves c/2, global = min)  ── CITED
  ∧ [rlct ≥ ½·codim]        (Aoyagi DLN: singular strata MILD — the wall)                  ── the prize
                              ↑ via cited "all resolution divisors ≥ c/2 ⟹ rlct ≥ c/2" (CITED criterion)
                                + DLN-geometric mildness of the strata (PROVED)
```
The pure analytic core (zeta / resolution / Watanabe / rlct-of-a-quadratic) = CITED thin interface. The
DLN geometry (loss=sum-of-squares [banked]; lci/regular-sequence at smooth pts → local rlct = c/2;
singular-stratum mildness) = PROVED.

## Opening recon (launched tick 0)

- **01 (R0 interface design):** the exact cited theorems + the precise geometric hypothesis the
  lower-bound criterion consumes. Sets the seam.
- **02 (R1 the decisive computation):** local rlct of the deepest stratum of `(2,2,2,2,2)` r=0. Mild, or
  a subtlety?
- **03 (Rm Mathlib coverage):** regular sequence / lci / Koszul / Kähler for the local model.

On recon landing → synthesize + refine the rung ladder (R2–R5) + surface the plan to the operator before
formaliser tides (per pattern). Then drive.

## Drift-guard

- name = content: never an `rlct_…` result that secretly assumes the analytic interface. The cited
  boundary is the thin `RlctInterface`, stated explicitly.
- The wall is the LOWER bound (singular-stratum mildness), not the upper. Don't let the upper-bound slab
  (R2) get named as if it closed the equality.
- Don't build the analytic core (out of scope — cited). Don't pre-pull R5 to look complete.
- L3: sweep the semantic class on any framing fix (fibration-geometry cost 5 review rounds).

## Tick log

- **tick 0 (setup, 2026-06-27):** branch + brief + machinery + cron backstop; opening recon (01/02/03)
  launched.

- **tick 1 (Rm coverage landed, 2026-06-27):** recon-mathlib (thread 03) closed. Key results +
  corrections to the brief's R2 framing:
  - **R2's algebraic slab is banked / in Mathlib:** the S2b conormal statement (`I/I²` free of rank `c`
    at a smooth pt) IS Mathlib's `SubmersivePresentation.free_cotangent`/`basisCotangent`; repo has the
    Jacobian↔conormal bridge (`finrank_cotangentSpace_eq_finrank_ker_jacobian`, `CotangentJacobian`),
    `smooth_point_isRegularLocalRing`, `fibre_smoothBlock_certificate` (reports Ω rank `ambient−c`,
    leaving the conormal-rank-`c` side on the table — reachable via `free_cotangent`).
  - **Brief correction:** "the `c` equations form a regular sequence (lci)" was a partial RED HERRING —
    a literal length-`c` Koszul/regular sequence is a sub-wall (no Koszul/lci/CM in Mathlib) AND unneeded
    (it proves no rlct value — that's irreducibly analytic). The **conormal-free** statement carries the
    upper-bound algebra. ⟹ reframe R2 around conormal-free / Jacobian-rank-`c`, not regular-sequence.
  - **THE R2 WALL (Codex xhigh-corroborated): the real↔complex / presentation seam**, NOT the lci gap.
    Banked geometry is over alg-closed `K` (`[IsAlgClosed k]`); the cited analytic rlct is over **ℝ** and
    needs a REAL map `F:ℝ^N→ℝ^c`, a real smooth point of `F⁻¹(0)`, Jacobian rank `c` THERE. ⟹ R0 + R2
    must co-design: the refined `RlctInterface` + its geometric hypothesis stated **over ℝ**, with
    "∃ real smooth pt, rank dF = c" as the PROVED input. **Steered recon-interface (01) accordingly.**
  - **R2 route (3 rungs):** (1b) read `rank(Jacobian)=c` off banked `CotangentJacobian` — LOW-RISK
    bounded-but-new; (2) real smooth point over ℝ + the ℝ interface restatement — NET-NEW, the wall;
    (3) refined `RlctInterface` over ℝ. Mathlib GAP confirmed: no Koszul / lci-scheme / CM / real-RLCT.
  - **Probe overlap:** whether a real smooth point of `mult⁻¹(0)` over ℝ is constructible — the `(2,2,2)`
    / `(2,2,2,2,2)` r=0 witness (R1, thread 02) is the natural probe.
  - Holding the full recon synthesis + rung-ladder refinement (R2–R5) until R0 (01) + R1 (02) land.

- **tick 2 (R0 interface design landed, 2026-06-27):** recon-interface (thread 01) closed, `survived`.
  Reshapes the seam — three structural findings:
  - **The lower-bound hypothesis is a condition on the IDEAL, not the set; the brief's R3 candidate
    ("strata smooth of expected codim ⟹ rlct = ½·codim") is FALSE** (Codex counterexample: `I=(x,y²−z³)`,
    `F=x²+(y²−z³)²`, rlct = 11/12 < 1 — a deep cusp valuation). **Sharp condition:** the pair
    `(ℝ^N, c·I_fibre)` is **log canonical**, i.e. `lct(I_fibre) = c`, i.e. the per-divisor inequality
    `h_E+1 ≥ c·ord_E(I)` for every divisorial valuation `E`. (Same set, different ideal power ⟹ different
    rlct, so no set-only condition works.) **R3 retargeted: prove `(ℝ^N, c·I_fibre)` log canonical.**
  - **The three CITED theorems (over ℝ), thin seam:** C1 `rlct(Σ_{i≤c} xᵢ²) = c/2` (ALREADY in repo:
    `monomial_rlct`, `rlct_additive_smooth_block`); C2 Watanabe `rlct(Σfᵢ²) ≤ ½·codim_ℝ` (cite Lin); C3
    monomial extraction `rlctAt = ⨅ (hⱼ+1)/(2kⱼ)` over a normal-crossing chart datum (= the existing
    `monomial_rlct` axiom — the irreducible cited boundary; the lower-bracket
    `axisRatio_ge_of_mult`/`monomialThreshold_ge_of_mult` already PROVED). NB **C3 must be a
    log-principalization of the IDEAL, not a resolution of the set.**
  - **The real↔complex transfer `T` is PROVABLE, not cited (and is the genuine wall, RISK-1):**
    `codim_ℝ(mult⁻¹_ℝ B) = codim_K(mult⁻¹_K B) + "every minimising component has a real smooth point"`.
    Scout verified the load-bearing fact — `realizerD` = `intervalDirectSum` of 0/1 entries, defined over
    ℚ ⊆ ℝ ⟹ each top-dim minimising component has a rational (∴ real) point ⟹ real points Zariski-dense
    ⟹ `dim_ℝ = dim_K`. The monolith HIDES `T` ("no base-change lemma needed" — the visible-progress
    trap); the refined interface must EXPOSE it. Banked lever: `codimRepCanonical_orbitRankLocus_realizerD`.
  - **Existing RLCT scaffolding in the repo** (earlier rlct-payoff expedition): `monomial_rlct` (cited
    boundary), the proved lower-bracket, `aoyagiLambda`, a `Skeleton.lean`/`Validate/` resolution scaffold.
    Aoyagi's actual lower bound = a BESPOKE explicit real blow-up (Cases 1/2 induction), citing only the
    monomial extraction (= C3) once the resolution is in hand; LR Thm 8.6 = pure formula-match
    `2·λ_Aoyagi = C`. NO `aoyagiLambda = ½·cCodim` bridge in Lean yet (the monolith short-circuits it).
  - **R3 routes:** (R3-Newton) DLN core Newton-nondegenerate ⟹ ONE citable theorem (Saito–Varchenko)
    discharges all divisor inequalities — collapses the mountain; **UNTESTED — R1's job** (steered).
    (R3-resolution) Aoyagi's bespoke blow-up via the banked `Skeleton`/`Mval=codimForm` → combinatorial
    `min_T Mval ≥ cCodim`. (R3-slc) reduced-lci + semi-log-canonical — heavy.
  - **RECOMMENDED SEAM:** CITED = C1+C2+C3 (keep `monomial_rlct`); PROVED = loss=Σc-squares (banked) +
    real resolution/Newton datum → C3 + lower-bracket → `rlct ≥ ½·codim_ℝ` + transfer `T`. Compose
    C2+R3+T → refined `cited_aoyagi_dln` on a thin named boundary. Do NOT add a standalone "lc-pair ⟹
    rlct≥½codim" cited field unless R3-Newton/slc discharges cheaply (R1 decides).
  - **NAME-HONESTY GATE (expedition-wide):** no `rlct_…` may assert `≥½codim` while secretly assuming C3
    for a resolution it doesn't exhibit, nor bury `T` in a citation. (→ lessons L4.)
  - **Awaiting R1** (the decisive computation + Newton-nondegeneracy verdict, steered) — then full
    synthesis + rung ladder + operator sign-off before tides.

- **tick 3 (backstop, 2026-06-27):** drift-glance. R1 (recon-deepest-stratum `a502ccc1`) still running
  (no commits — pen-and-paper; the `(2,2,2,2,2)` rlct + Newton-nondegeneracy is genuinely hard). No tide
  to merge, no hardener pending, no operator edit. Discipline self-check: vision held; correctly waiting
  on R1's decisive verdict (sets R3 cost), not busywork; name-gate banked; sea on the right wall.
  **NB — isolation watch-item:** the read-only recon scouts' artefacts (thread.md + codex for 01/03)
  landed in MY worktree's expedition dir (their isolation didn't fully separate). Harmless for read-only
  recon (lean/ untouched, confirmed), and convenient (I'll bank them at recon-synthesis). BUT verify the
  first FORMALISER tide gets a genuinely distinct worktree before parallelizing Lean writers (the
  fibration-geometry tides DID get distinct trees, so likely fine — but confirm). Re-sleep.

- **tick 4 (R1 landed — RECON COMPLETE, 2026-06-27):** recon-deepest-stratum (thread 02) closed.
  **VERDICT: MILD — green light.** Local rlct at the deepest stratum of `(2,2,2,2,2)` r=0 = **λ = 3/2 =
  ½·codim** (codim `C=3`, `δ=0`; θ=binom(4,2)=6 matches; repo `Aoyagi.lambda(d22222,0)=3/2`). Certified 3
  ways: rigorous Jacobian-rank-3 upper bound (smooth codim-3 CI, origin in closure); decorrelated Codex
  (xhigh, value-withheld) independently → 3/2 via SVD/rank blow-up → toric ideal `J=⟨zr−cp,a(c−zq),dr,adq⟩`;
  `(2,2,2)` r=0 clean-numeric validation vs the classical Aoyagi–Watanabe value. **The kill-condition
  (λ<½·codim) does NOT fire.**
  - **R3-Newton in STANDARD coords is DEAD:** explicit torus point (A₁=A₂=A₃=[[1,1],[1,1]],
    A₄=[[1,−1],[2,−2]]: all entries ≠0 yet product=0 ⟹ K=0, ∇K=0) ⟹ Newton-degenerate; naive toric bound
    = 2 ≠ 3/2. So "cite one Saito–Varchenko on the coordinate Newton polyhedron" FAILS. **R3-resolution
    needed** (rank/SVD blow-up à la Aoyagi, on the repo `Skeleton`/`Validate` scaffold). **Refined gamble
    that survives:** Newton-nondegenerate IN THE RESOLVED CHART may still discharge R3 with one citable
    theorem — worth probing first.
  - **OPEN (the genuine wall, R3):** the rigorous lower bound λ≥3/2 (mildness) is NOT float-certifiable
    (multiplicity m=5 log factor biases sampling to ~1.2–1.5); no evidence of <3/2, but it must be PROVED
    in R3. (Minor: pole mult m=5 Aoyagi/repo vs Codex m=4 — low stakes.)

## RECON COMPLETE — the refined plan (for operator sign-off before tides)

**Seam (CITED thin / PROVED prize):** CITED over ℝ = C1 `rlct(Σxᵢ²)=c/2` + C2 Watanabe `≤½·codim_ℝ` + C3
monomial-extraction (all ≈ banked `monomial_rlct` + proved lower-bracket). PROVED = loss=Σc-squares
(banked) + R2/T (upper bound + transfer) + R3 (lower bound) → R4 compose → retire monolith
`cited_aoyagi_dln`. NAME-GATE: no `rlct_…` may assume C3 for a resolution it doesn't exhibit, nor bury T.

**Rung ladder (recommended sequencing):**
- **Wave 1 (parallel):** (A) **R2 + T** — the upper-bound + real↔complex transfer: real smooth pt +
  Jacobian rank c (banked-ish `CotangentJacobian`/`free_cotangent`) → C2; transfer T `codim_ℝ=codim_K`
  via the rational `realizerD` (banked `codimRepCanonical_orbitRankLocus_realizerD`). Bounded-but-new; the
  achievable first win that EXPOSES the hidden transfer. (B) **R3-route probe** — drive the repo
  `Skeleton`/`Validate` resolution scaffold toward the combinatorial `min_T Mval ≥ cCodim`
  (`Mval=codimForm` banked) + test the refined Newton-in-resolved-chart gamble. Sets R3's cost.
- **Wave 2:** **R3 (the lower bound, the wall)** — the resolution → C3 + lower-bracket → `rlct ≥ ½·codim_ℝ`.
  Multi-tide; route set by the Wave-1 probe.
- **Wave 3:** **R4 assemble** (compose → refined `cited_aoyagi_dln`); **R5 bundle completion**
  (projection compatibility + R1-gluing).

- **tick 5 (operator sign-off + Wave 1 LAUNCHED, 2026-06-27):** operator chose **"Full proof,
  probe-first"** (maximal but methodical).
  - **GROUND-TRUTH CORRECTION (supersedes ticks 2/4's "≈ banked `monomial_rlct`/`Skeleton`"):** controller
    grep verified there is **NO `monomial_rlct`, NO `aoyagiLambda`, NO `Skeleton`/`Validate` resolution
    scaffold** on dev. The analytic-rlct side is **GREENFIELD**. What IS banked is GEOMETRY:
    `codimRepCanonical`, `cCodim`, the proved formula-match `codimRepCanonical_fibre_eq_two_aoyagiLambda`
    (`codim = 2·Aoyagi.lambda`, `DLN/Aoyagi/ClosedForm.lean`), `realizerD` +
    `codimRepCanonical_orbitRankLocus_realizerD`. The monolith = `RlctInterface.cited_aoyagi_dln`
    (`RlctPayoff.lean:288–300`): opaque `rlct` map + one equality field; docstring 267–272 carries the
    verbatim trap *"No from-scratch real↔complex … base-change lemma is needed"* (the hidden T). So the
    "thin cited interface" IS C1/C2/C3 stated fresh (not a wrap of existing scaffold) — cleaner: exposing
    the axioms is the goal.
  - **Wave 1a — `thin-interface` tide** (lean-formaliser `a756ff2f0ed17ceb6`, isolated worktree, branch
    `expedition/rlct-bridge-04-thin-interface` from `origin/dev`): monolith → `ThinRlctInterface`
    (C1/C2/C3) + EXPOSE T (prove via rational `realizerD` if reachable, else explicit named field), delete
    trap docstring, re-derive downstream; R2/R3 enter as named holes. **Design-proposal-first → controller
    seam-taste review before finalize.**
  - **Wave 1b — `r3-route-probe`** (pen-and-paper): resolved-chart-Newton vs Aoyagi-bespoke verdict +
    resolution-datum spec + R3-tide cost estimate.
  - Holding for 04's design proposal + 05's verdict. Then: review 04 to equilibrium before integrating;
    refine R3's Wave-2 shape from 05.

- **tick 6 (MAJOR PIVOT — discovery of the parallel aoyagi line + operator's BLIND decision, 2026-06-28):**
  - **Discovery (tide 04 + controller git-verified):** there is a large ACTIVE parallel formalisation of
    **Aoyagi's paper** (separate from L&R), on `origin/expedition/aoyagi-full` (tip `648ebe18`) + many
    `fm*`/`g1*`/`crux2*`/`cover/*` branches — **183 RLCT files, 12 code sorries, ONE axiom (`monomial_rlct`)**,
    the GENUINE `rlctAt` (Aoyagi integral def), headline `aoyagi_learning_coefficient : ⨅ rlctAt =
    aoyagiLambda` (Skeleton.lean:1725), and `(2,2,2)` rlct computed END-TO-END from `rlctAt` modulo only
    `monomial_rlct` (no sorry). **NOT on dev.** It shares ZERO Lean dependency with dev/Core (does not
    import `codimRepCanonical`/`fibre`/`mult`); the two worlds meet only at the field-free combinatorial
    identity `aoyagiLambda_RLCT(H) ↔ Aoyagi.lambda_dev(d)` (H↔d index reversal). My "greenfield" tick-5
    correction was right about dev but blind to these unmerged branches.
  - **OPERATOR DECISION: the L&R/rlct-bridge line stays BLIND to the aoyagi expeditions.** No import, no
    copy, no dependency on `rlctAt`/`aoyagiLambda_RLCT`/`monomial_rlct`/Skeleton. Rationale: decorrelation
    (two independent formalisations of `rlct=½·codim` cross-check on later reconciliation), self-contained
    cleanliness (inherit none of that line's sorries/churn), fidelity to L&R (who CITE Aoyagi). **This is
    the original charter made strict** (loop-prompt: "the analytic RLCT core we CITE as the thin honest
    seam — that is the scope, not a retreat").
  - **Entailment (surfaced to operator, awaiting final nod):** blindness FORCES the opaque `rlct` (dev has
    no genuine `rlctAt`), so the thin **opaque** cited interface (tide 04's design — C1/C2/C3 + expose T)
    is the principled deliverable. **The analytic LOWER bound `rlct ≥ ½·codim` (Aoyagi's bespoke
    resolution) is CITED, NOT formalised on our side** — formalising it blind = re-deriving Aoyagi in the
    Tuple world (huge, duplicative-in-spirit). "Full proof" narrows honestly to: full proof of the L&R
    GEOMETRY + a thin named cited analytic seam (Watanabe `≤`, Aoyagi `=`). Transfer T stays ours (prove
    via dev `realizerD` if reachable, else explicit named field).
  - **R1/R5 probe (05) CLOSED — banked as decorrelated L&R-side confidence in the citation** (NOT copied):
    independent mildness confirmation rlct=3/2=½·codim at the `(2,2,2,2,2)` r=0 deepest stratum via exact
    monomial-sos reduction `w₁²+w₂²+δ²(s²+v²)` (Newton-LP + polar integral, decorrelated Codex agreed).
    Width-split map of what the citation rests on: VIABLE (one citable theorem per step on a clean monomial
    depth-(L−1) tower) for all-width-2; NEEDED (bespoke recursive blow-up, the corank-≥2 shear = Aoyagi
    diag(b)) for general widths ≥3. (Resolution-datum spec + L=3 next-construction → out of scope under
    blind/cite.) Probe stood down.
  - **NEXT (on operator nod):** resume tide 04 to finalize the blind thin interface (C1/C2/C3 + T,
    re-derive downstream, delete trap docstring, retire monolith — green/sorry-free/axiom-clean/blind),
    then the proved-geometry rungs (R2 upper bound via Watanabe+T+connector; R5 bundle completion).

- **tick 7 (SCOPE CORRECTED + Wave A LAUNCHED, 2026-06-28, operator "Yes, let's do it!"):** the operator
  corrected my over-narrow tick-6 framing: "full proof (blind)" is NOT "opaque interface + cite everything
  analytic + a little geometry" — it is **cite ONLY `rlct = ½·codim_ℝ`, and PROVE all the geometry up to
  it**. The monolith `cited_aoyagi_dln` cheats by citing `rlct = ½·codim_K` directly — one field that
  silently swallows three GEOMETRIC facts to reclaim and prove: (1) connector `loss=Σres²`, real zero-set
  = real fibre; (2) the real codim `codim_ℝ`; (3) **transfer T: `codim_ℝ = codim_K`** (the genuine
  geometric wall, via `realizerD` density). Interface SHRINKS (drop C1/C3; carry just Watanabe-upper +
  Aoyagi-lower, or the one equality); proved side GROWS (the full `C/θ` engine [banked] + T + connector +
  R5, composed → `rlct = ½·C`).
  - **Wave A LIVE (two tides, parallel):** **04 foundation** (resumed `a756ff2f`): honest `codim_ℝ` def +
    shrunk cited interface + connector + compose (T as named hole) + re-derive downstream + delete trap
    docstring; design-proposal-first (codim_ℝ def + T-feasibility verdict). **06/R5 bundle** (`a8c0b116`):
    projection compatibility + overlap-gluing → `Flat π` over `rankROpen`; independent geometry.
  - **Wave B (gated on 04 pinning `codim_ℝ`):** **T** transfer tide (the wall); **compose + engine
    wire/harden** → retire monolith. Tracked tasks #4–#7 (#5 T blocked-by #4; #7 compose blocked-by #4,#5;
    #6 R5 independent).
  - Holding for 04's design proposal (codim_ℝ + T-feasibility — controller seam-taste review) + R5's report.

- **tick 8 (04 design APPROVED + T-route scout launched, 2026-06-28):** 04 posted its fuller-scope design
  proposal (decorrelated Codex on the load-bearing def); controller seam-taste review settled (a)-(d):
  - **codim_ℝ** = `codimRepCanonical (k:=ℝ)` as a named abbrev (`codimRealLocus`/`codimRealFibre`). KEY: the
    banked field-parametric def, evaluated at ℝ, IS the honest real-locus codim (height of the real-points
    vanishing ideal). Discriminator: `x²+y²` has generator-ideal height 1 but `vanishingIdeal ℝ {0}=(x,y)`
    height 2 = real codim. (The earlier "don't reuse over ℝ" caveat was about ASSUMING =codim_K, not the
    DEFINITION.) Docstring records the discriminator + "bare real-locus codim, NONE of the alg-closed
    geometry — T bridges to K".
  - **Two cited bounds** `cited_watanabe_upper` (universal, no guard) + `cited_aoyagi_lower` (DLN, 0<N),
    equality derived by `le_antisymm`. Drop C1/C3.
  - **T = standalone NAMED hypothesis, NOT a cited structure field** — it's to-be-PROVED geometry (Wave B),
    not cited analytic content; the cited boundary is honestly just the two bounds; T discharges + drops out
    when proved.
  - **Re-point the 7 consumers threading T — NO `ofReal` shim** (the shim re-buries T one def deep = the
    visible-progress trap; name=content forbids it). L3 sweep on the trap-docstring deletion + framing.
  - **T-feasibility verdict (04):** NOT provable this tide. Gap: rational point alone insufficient — need a
    SMOOTH real point per top component + the real-density⟹dim bridge; Mathlib v4.29 lacks semialgebraic
    dim / real-Nullstellensatz / `height` base-change. T is the single named hole.
  - **Wave B recon launched — thread 07 `t-route-scout`** (pen-and-paper): scope the T proof route
    (smooth-realizer check; height=dim−trdeg vs chain-of-primes vs height-base-change; Mathlib inventory) +
    FEASIBILITY VERDICT (bounded tide / big build / honest cited fallback). Gated on 04's pinned def (done),
    not on 04's green — runs in parallel. **T is the expedition CRUX.**
  - 3 fronts live: 04 finalizing, 06/R5 bundle, 07 T-route. Holding for their reports.

- **tick 9 (T-route VERDICT — T is CITED; the crux settled, 2026-06-28):** thread 07 closed. **Verdict
  (iii): T is TRUE but NOT bounded-provable at Mathlib v4.29** — `codim_ℝ = height(vanishingIdeal_ℝ) =
  height(REAL RADICAL)`; v4.29 has NO real radical / real-Nullstellensatz / semialgebraic dim /
  `vanishingIdeal` base-change (`IsRealClosed` is purely field-theoretic). So T is a **named CITED field** —
  fidelity to L&R/Aoyagi's real-analytic-over-ℝ resolution, not a retreat. This SUPERSEDES tick 8's "T =
  to-be-proved Wave-B hole" — T is cited, not a hole; Wave B (a T-PROOF tide) is cancelled for this
  expedition.
  - **Sharpening (taken):** the catenary `codim + varietyDim = card` is field-generic (banked
    `RadicalCatenary.codimRepCanonical_add_varietyDim_eq_card_of_nonempty`, card field-independent) ⟹
    **T ⟺ T′** with both fibres nonempty. So cite the ATOMIC **T′: `varietyDim_ℝ(fibre ℝ B) =
    varietyDim_K(fibre K)`** (real dim = complex dim — the real-radical-density fact) and **PROVE**
    `codim_ℝ=codim_K` from T′ + the banked catenary. Cited content shrinks to the irreducible fact; the
    codim bridge is proved. (Fallback: cite codim_ℝ=codim_K directly.)
  - **T confirmed TRUE** (exact-rational Jacobian, not float): `realizerD` smooth full-dim at (2,2,2) r=0
    and (2,3,2) r=1; disjoint-interval-support lands it in a single smooth component (other 0/1 points sit
    at component crossings, Jrank≠codim). Banked as soundness of the citation + seed for the future proof.
  - **Cited boundary (final, honest):** {`cited_watanabe_upper` (analytic, universal), `cited_aoyagi_lower`
    (analytic, DLN/Aoyagi), **T′** (geometric real↔complex dim)} — three named atomic cited facts, each
    sourced + caveated. Everything else PROVED: catenary, codim_K=C, connector, the C/θ engine, R5.
  - **ROADMAP (future expedition — the `rlct-runway-target` wall):** PROVE T′. Scout's 4-step ladder:
    varietyDim↔height [banked] → "smooth full-dim real pt ⟹ real dim = complex dim" (regular-local-dim over
    ℝ + real-radical density) → "`realizerD` smooth full-dim per top component, all d,r" (generalize the
    Jacobian-rank certificate; disjoint-support ⟹ single component) → glue per-component. **ℚ-unirationality
    of the orbit/sweep = the clean sufficient hypothesis.** NOT this blind/cite expedition.
  - 04 messaged to wire T′ as the cited field (T′+catenary preferred). Task #5 reframed (cited-wiring;
    proof roadmapped). Holding for 04 finalize + 06/R5.

- **tick 10 (backstop, 2026-06-28):** drift-glance — no operator edit; both tides (04 foundation, 06/R5
  bundle) still working (neither branch pushed); 07 closed. Self-check vs the CORRECTED plan (not the stale
  cron "lower bound = wall to formalise"): vision held; load-bearing geometry in flight (04 + R5); lower
  bound + T CITED (genuine Mathlib-v4.29 blockers, roadmapped — not busywork-avoidance); name=content
  intact. Nothing actionable. **Integration/review plan for when 04 lands:** (1) pull from worktree disk;
  (2) green-gate — `scripts/lb DLNFibre` + `scripts/sorries` + `#print axioms` on the composed payoff
  (expect `[propext, Classical.choice, Quot.sound]`, the 3 cited facts as structure fields, NO new global
  axiom); (3) wire the aggregator (single-writer); (4) **convene hardener + a decorrelated reviewer on the
  name=content seam — L4 existential** (no `rlct_…` overclaiming; the 3 cited facts each sourced + caveated;
  T′ visible, no shim); (5) integrate R5 likewise. Re-sleep.

- **tick 11 (04 FOUNDATION INTEGRATED GREEN + review convened, 2026-06-28):** tide 04 finalized
  (branch `…-04-thin-interface` @ `66102d67`, Lean `c07c5c5d`); controller merged into
  `expedition/rlct-bridge` (merge `3d92c754`) + swept the stale aggregator comment
  (`DLNFibre.lean:260`, single-writer) → `ae8f6605` (pushed). **Gates re-verified in controller worktree:
  full `scripts/lb DLNFibre` GREEN (3815 jobs), `scripts/sorries` clean (0 sorry/axiom/native_decide),
  04 reported `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all 10 load-bearing theorems
  (no sorryAx / monomial_rlct / new axiom).** (Long-line linter warnings in `DLNFibre.lean` are
  pre-existing + endemic to the file's comment convention — non-failing; my comment matches the style.)
  - **Delivered (3 files RlctPayoff/RlctPayoffGeneral/BundleShiftDischarge):** `codimRealFibre :=
    codimRepCanonical(k:=ℝ)` (x²+y² discriminator docstring); `RlctRealInterface` = opaque rlct + 2 cited
    bounds (`cited_watanabe_upper` universal, `cited_aoyagi_lower` 0<N); equality derived; T = standalone
    named cited hyp threaded through 7 consumers, NO shim; `fibre_zero_nonempty` PROVED;
    `codimRealFibre_eq_codimRepCanonical_of_dimTransfer` PROVED (atomic dim-transfer ⟹ codim via banked
    field-generic catenary); trap docstring DELETED; L3 sweep done. **The monolith `cited_aoyagi_dln` is
    RETIRED** — the compose `rlct=½·codim_ℝ=½·codim_K=½·C` lands on the 3-atomic-cited-fact boundary.
  - **Tasks:** #4 (foundation) + #5 (T cited-wiring) COMPLETED; #7 (compose+retire) — LANDED via 04, now =
    the bedrock AUDIT, in-progress.
  - **Review convened (L4 existential name=content gate, decorrelated):** `fidelity-rev-04` (`a3ed3e41`,
    reviewer) + `hardener-04` (`af1b0a5d`, hardener) on 04's branch — fidelity (#print axioms, the bounds'
    asymmetry, codim_ℝ discriminator, T no-shim, no rlct_… overclaim) + bedrock/taste (atomic-citation
    honesty, name=content, caveats-next-to-claims, non-vacuity, beauty). Loop findings to equilibrium
    before close.
  - Holding for the two reviews + R5 (06, bundle, still running).

- **tick 12 (hardener verdict — SOLID + 2 tightenings, 2026-06-28):** `hardener-04` (`af1b0a5d`) verdict on
  04's seam: **SOLID on the L4 gate** — a genuine factorization (one opaque fused field → 3 named cited
  facts + le_antisymm-proved equality + proved codim_K=C + route-β bundle-shift discharge), name=content
  holds, codimRealFibre is the right object, runway honest. Technical floor re-verified independently
  (BundleShiftDischarge green 3731 jobs; #print axioms `[propext, Classical.choice, Quot.sound]` on all 6
  load-bearing payoffs; monolith genuinely gone). TWO HARDEN-THESE (neither breaks soundness; both → task #8):
  - **HARDEN-2 (soundness, mine to own):** the bounds quantify `∀ B` (I approved "unconditional upper") —
    but off `image(mult)` the fibre is ∅ ⟹ `codimRealFibre = height ⊤ = ⊤` ⟹ `(⊤).toNat = 0` ⟹ upper bound
    collapses to `rlct ≤ 0`, which the true `rlctAt` (∞ on a nowhere-zero loss) CANNOT satisfy ⟹ the
    unguarded interface is UNINHABITABLE by the intended rlct. **Fix: restore the monolith's attainability
    guard `B.rank=r → (∀ k', r ≤ d k')` (⟺ fibre nonempty)** on both bounds + thread through the 7
    consumers. The (2,2,2) witnesses (B=0, rank-1) already satisfy the guard — survive unchanged.
  - **HARDEN-1 (prose):** docstrings/card say "irreducible cited content = atomic `hdim`" but the reduction
    lemma `codimRealFibre_eq_codimRepCanonical_of_dimTransfer` is ORPHAN (zero payoffs invoke it; grep +
    decorrelated Codex confirm); every consumer threads codim-level `hT`. `hT ⟹ hdim` not licensed. Fix:
    correct prose — the payoff cites `hT`; `hdim`+nonemptiness ⟹ `hT` via the banked reduction, not threaded
    this tide.
  - **Held:** dispatch the consolidated tightening (task #8) to tide 04 only AFTER the fidelity reviewer
    (`a3ed3e41`) lands — integrate both decorrelated reviews, avoid fix-then-contradict. Then re-green-gate
    + re-#print-axioms + hardener re-review. Holding for fidelity + R5.

- **tick 13 (fidelity PASS + reviews reconciled + tightening DISPATCHED, 2026-06-28):** `fidelity-rev-04`
  (`a3ed3e41`): **PASS on all 6 checks** (cited boundary = exactly the 3 facts via force-elaborated
  `#print axioms` on 14 decls; bounds' asymmetry verified vs paper main.tex — upper = universal Atiyah/
  Watanabe `eqn:rlct_upper_bound_glob`, lower = DLN `thm:aoyagi-rlct` citing Aoyagi Thm 1; codim_ℝ honest;
  T threaded no-shim; composition sound; L3 clean). Beyond brief: CONSTRUCTED axiom-clean inhabitant
  `rlctRealInterfaceWitness d` (formal non-vacuity).
  - **Reviews RECONCILE (not contradict):** fidelity's witness = a CONSTRUCTED rlct (½codim on-image, 0
    off-image) ⟹ FORMAL inhabitability ✓; hardener's HARDEN-2 = the INTENDED analytic rlctAt (∞ off-image)
    can't satisfy the UNGUARDED upper bound ⟹ re-guard needed for the real rlctAt to discharge it (the
    aoyagi-full fold). Complementary. Fidelity flag (banked): re-guarding the bound FIELDS ⟹ the witness
    must be re-shown inhabitable under the (weaker, easier) re-guarded struct; docstring = "the interface
    TYPE is inhabited," NOT "the rlct exists."
  - **CONSOLIDATED TIGHTENING DISPATCHED → tide 04 (task #8):** (1) re-guard both bounds `B.rank=r → ∀k',
    r≤d k'` + thread 7 consumers [HARDEN-2]; (2) permanent in-file `rlctRealInterfaceWitness` re-derived
    under the re-guarded struct, honest docstring [bedrock non-vacuity]; (3) orphan-`hdim` prose → cite
    codim-level `hT` [HARDEN-1]; (4) banned-word scrub (full L3 sweep) [fidelity-1]; (5) verify/soften "LR
    Thm 8.6" [fidelity-4]. Re-green-gate + re-#print-axioms + bump card. `_via_aoyagi` left as-is (both
    reviews agree hT-in-type is sufficient).
  - Both reviewers thanked + stood down; will re-review the landed tightening. Holding for 04's tightening +
    R5 (06, bundle).

- **tick 14 (tightening INTEGRATED GREEN + re-review running, 2026-06-28):** tide 04's tightening landed
  (branch @ `5bc1e7e4`, Lean `a3bd2b5f`); controller merged → `expedition/rlct-bridge` (merge `100559c0`,
  pushed); my aggregator fix (`ae8f6605`) preserved (04 doesn't touch the single-writer; its repeated
  flag is stale-from-its-own-branch). **Gates re-verified in controller worktree: `scripts/lb DLNFibre`
  GREEN (3815 jobs), sorries clean.** Controller spot-checks: re-guard `0<N → B.rank=r → (∀k', r≤d k')`
  present on BOTH `cited_watanabe_upper` + `cited_aoyagi_lower` (`RlctPayoff.lean:365-376`);
  `rlctRealInterfaceWitness` present (`:385`); banned words clean (rg, 3 files); no stale "8.6". 04 reported
  `#print axioms` clean on all 11 decls incl. the witness.
  - All 5 tightenings in: (1) re-guard [HARDEN-2 soundness — restores intended-inhabitability so the
    aoyagi-full fold can instantiate with the real rlctAt]; (2) `rlctRealInterfaceWitness` (formal
    inhabitant, honest docstring); (3) orphan-`hdim` prose → cite codim-level `hT`, lemma docstring "unused
    by payoffs"; (4) banned-word L3 sweep; (5) citation → "Aoyagi Thm 1 / LR §8 (thm:aoyagi-rlct)".
  - **Hardener re-review (`af1b0a5d`) RUNNING** — targeted re-confirm of the 5 fixes (re-guard soundness +
    no consumer dropped it; witness inhabits the re-guarded struct; axioms clean; prose honest; words/cite).
    Fidelity items spot-verified by controller (lower-value re-review skipped).
  - Tasks: #8 (tightening) → completes on the re-review confirm; #7 (compose+retire) likewise. Holding for
    the hardener re-confirm + R5 (06, bundle).

- **tick 15 (backstop, 2026-06-28):** drift-glance — no operator edit; hardener re-review (`af1b0a5d`)
  running; R5 (`a8c0b116`, bundle) still working (no branch pushed) — long runtime on a hard target
  (global `Flat π` needs the residue-field-rank bridge = new math). Sent R5 a gentle check-in reinforcing
  the honest-ceiling escape hatch (land the strongest honestly-provable bundle headline + name the
  residual; don't force/overclaim new math) + asked for status (a close-to-green / b at-ceiling /
  c stuck). Self-check vs corrected plan: vision held; seam core landed+hardened; R5 = the remaining
  proved-geometry rung; correctly waiting, not busywork. Re-sleep.
