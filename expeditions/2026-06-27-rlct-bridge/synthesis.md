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

- **tick 16 (R5 at HONEST CEILING — projection compatibility landed, 2026-06-28):** R5 (`a8c0b116`)
  replied (b): at the honest ceiling, landing partials (finishing gates + commit on
  `…-06-bundle-completion`). **Genuine win:** `Core/FibreProjectionCompat.lean` — **projection
  compatibility** (`schurToDsigAt` IS `mult`'s comorphism `multComap`, gauge-transported, at every pivot;
  factors through `multPoly` via `chartPhiVarSub` — genuine, dodges the vacuous-restatement trap) +
  `ProjCompatOverBaseChart` (projection-compat + S4b over-base triv + flatness). **This closes the S5/S4b
  open item (i)** the fibration-geometry expedition left as its residual. Axiom-clean. Also
  `Core/FibreTargetOverlap.lean` — the R1 target-side transition OBJECT (`targetProductOverlapTransition`,
  pairwise) + reusable `awayCongr'` brick + base round-trip.
  - **Named residuals (NOT forced, honest ceiling):** (i) the target-side cocycle ROUND-TRIP PROOF — math
    immediate from the base round-trip, but stalls on Lean infra (kernel-cost blowup on the double-localized
    reducible type via `ext`; missing `AlgEquiv.trans_assoc`/`refl_trans` in Mathlib v4.29). (ii) global
    `Flat π` over `rankROpen` — needs the cocycle + triple-overlap + local-to-global flatness = infra beyond
    the banked atlas + S1 rank-tie. **ROADMAP (future infra tide):** the two Mathlib-v4.29 AlgEquiv gaps +
    the double-localized kernel-cost workaround → then the cocycle → triple-overlap → global Flat π.
  - Steered R5: build via `scripts/lb` (not bare lake), name=content on the headline (global Flat π / cocycle
    EXPLICITLY named residuals in file + card, in-file roadmap), commit + report → I integrate.
  - Holding for R5's committed report + the hardener re-review (`af1b0a5d`).

- **tick 17 (hardener RE-REVIEW SOLID → 04 seam CLOSED, 2026-06-28):** `hardener-04` re-review of the
  tightening (@ `5bc1e7e4`): **SOLID — all 5 fixes sound, nothing regressed; the seam holds at the L4 gate
  without the two HARDEN caveats.** Verified: re-guard threaded through all 7 consumers (none silently
  dropped; r=0 discharges inline via `Matrix.rank_zero`, general-r forwards `hB hr`); the witness
  type-checks as a genuine `RlctRealInterface Core.d222` inhabitant under the re-guarded fields (rebuilt via
  `scripts/lb` after catching + resolving a stale-`.olean` artifact — "don't trust a cached green"); `#print
  axioms` clean incl. the witness; HARDEN-1 prose fixed (orphan lemma docstring'd "unused by payoffs");
  banned words + citation clean. **Micro-note adjudicated:** the two card "load-bearing" uses
  ("…for soundness", "…decls") are the precision.md technical term-of-art, NOT the banned `this is
  loadbearing` self-reassurance — LEFT as-is (controller taste call, hardener concurred). **Tasks #7
  (compose+retire) + #8 (tightening) COMPLETED.**
  - **04 thin-interface seam CLOSED:** monolith `cited_aoyagi_dln` retired; honest `rlct = ½·C` on the
    3-fact cited boundary {Watanabe ≤, Aoyagi ≥, transfer T}; re-guarded for intended-inhabitability
    (the genuine rlctAt can discharge it → aoyagi-full fold stays possible); non-vacuous (in-file witness);
    axiom-clean `[propext, Classical.choice, Quot.sound]`; name=content confirmed by TWO decorrelated review
    rounds (fidelity PASS + hardener SOLID, each re-confirmed).
  - **Remaining for close:** integrate R5 (06, finishing gates + commit — projection-compatibility landed,
    global Flat π = named ceiling), then expedition close shape → synthesis + close summary + PR behind
    signal-and-wait (operator-gated; controller opens, does NOT merge). Holding for R5's committed report.

- **tick 18 (R5 INTEGRATED GREEN + fidelity review running, 2026-06-28):** R5 committed (branch @
  `d137cbfb`); controller merged → `expedition/rlct-bridge` + wired the single-writer aggregator
  (`FibreProjectionCompat` then `FibreTargetOverlap`, dependency order; updated the stale FibreBundleHeadline
  "projection compat — open" → "CLOSED by R5") → `e357a168` (pushed). **Gates: full `scripts/lb DLNFibre`
  GREEN (3817 jobs, +2 modules), sorries clean.** Landed: `schurToDsigAt_comp_localizeSchur` +
  `chartPhiSchurAeval_eq_comp_multComap` (projection compatibility — closes fibration-geometry S5/S4b item
  (i)) + `ProjCompatOverBaseChart` + `awayCongr'` + `targetProductOverlapTransition` +
  `chartOverlapTransitionK_trans_symm`. Named residuals: target-side cocycle round-trip (Mathlib-v4.29
  `AlgEquiv.trans_assoc`/`refl_trans` gaps + double-localized kernel-cost) + global `Flat π` over rankROpen.
  - **Fidelity review (`fidelity-rev-06` `a54cd3f3`) RUNNING** — key checks: projection-compat is GENUINE
    (factors through multComap, not a vacuous restatement — Codex's flagged trap) + the global Flat π/cocycle
    are honestly NAMED residuals not overclaimed. #6 completes on its PASS.
  - Holding for the fidelity verdict → then expedition CLOSE shape.

---

## EXPEDITION CLOSE (2026-06-28)

**Central question (achieved):** replace the monolithic Cited axiom `RlctInterface.cited_aoyagi_dln`
(`rlct = ½·codim` in one opaque field) with a **thin cited analytic interface + genuinely-proved DLN
geometry**. DONE — the L&R line stayed BLIND to the parallel aoyagi-paper formalisation (decorrelation).

### Proved / landed (all green, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)
- **Monolith RETIRED.** `RlctRealInterface d` (opaque `rlct` + 2 cited bounds `cited_watanabe_upper`
  [universal] + `cited_aoyagi_lower` [DLN, 0<N, attainability-guarded]); equality `rlct = ½·codim_ℝ`
  DERIVED by `le_antisymm`. The payoff composes `rlct = ½·codim_ℝ → ½·codim_K → ½·C`.
- **`codimRealFibre := codimRepCanonical (k:=ℝ)`** — the honest real-locus codim (x²+y² discriminator).
- **Connector** (`loss = Σ residuals²`, real zero-set = fibre) + **catenary reduction**
  (`codimRealFibre_eq_codimRepCanonical_of_dimTransfer`: atomic dim-transfer ⟹ codim, via the banked
  field-generic `RadicalCatenary` catenary) + **`codim_K = C`** (banked engine) — all PROVED.
- **Non-vacuity witness** `rlctRealInterfaceWitness d : RlctRealInterface d` (formal inhabitant, NOT the
  analytic rlct — honestly docstring'd; re-guarded for intended-inhabitability so the genuine `rlctAt` can
  discharge the interface — the future aoyagi-full fold stays possible).
- **R5 bonus: projection compatibility** (`schurToDsigAt_comp_localizeSchur` /
  `chartPhiSchurAeval_eq_comp_multComap` — `schurToDsigAt` IS `mult`'s comorphism `multComap`) — **closes
  the prior fibration-geometry S5/S4b open item (i)**; + `ProjCompatOverBaseChart`, `awayCongr'`,
  `targetProductOverlapTransition`.

### Cited boundary (the honest thin seam) — exactly THREE named atomic facts
1. **Watanabe `≤`** (universal analytic upper bound), 2. **Aoyagi `≥`** (DLN-specific analytic lower bound),
3. **real↔complex dim-transfer T** (`codim_ℝ = codim_K`). Each named, sourced (Aoyagi Thm 1 / LR §8
`thm:aoyagi-rlct`), caveated, attainability-guarded. Everything else PROVED. **Verified by TWO decorrelated
review rounds each** (seam: fidelity PASS + hardener SOLID, re-confirmed after the tightening; R5: fidelity
PASS).

### Roadmap (named residuals — future expeditions, NOT this blind/cite line)
- **Prove T** (`codim_ℝ = codim_K` via `realizerD` smooth-rational density) — the `rlct-runway-target`
  wall; needs real-AG in Mathlib (real radical / real-Nullstellensatz / semialgebraic dim, all absent at
  v4.29). Scout's ladder: varietyDim↔height [banked] → smooth-full-dim-real-pt ⟹ dim-eq → realizerD smooth
  per top component → glue; **ℚ-unirationality of the orbit/sweep = the clean sufficient hypothesis.**
- **Global `Flat π` / fibre bundle over `rankROpen`** — the target-side cocycle round-trip (math immediate,
  blocked on Mathlib-v4.29 `AlgEquiv.trans_assoc`/`refl_trans` + double-localized kernel-cost) + triple-
  overlap + local-to-global flatness.
- **(Cross-paper)** connect to aoyagi-full's genuine `rlctAt` via the field-free `aoyagiLambda ↔
  Aoyagi.lambda` identity (the re-guard keeps this fold possible).

### Lessons banked
L5 (blindness=decorrelation), L6 (codim_ℝ def vs the transfer assumption), L7 (formal vs intended
inhabitability → the re-guard), L3-recurrence (re-grep the class to empty). See `lessons.md`.

### Status: CLOSE shape — branch `expedition/rlct-bridge` pushed (`9560b0e6`), green. PR
operator-gated (signal-and-wait): controller signals ready, does NOT open/merge unilaterally.
**PR #13 opened into `dev` (2026-06-28, operator-authorized) — https://github.com/edmund-ukaisi/geometry-of-dln-fibre/pull/13 — NOT merged (operator merges). Awaiting review.**

(The "EXPEDITION CLOSE" above is now the **Phase 1 close**. PR #13 review came in — no math blocker; 5
prose/precision/bookkeeping items, addressed: aggregator + status-file + whitespace by controller, the
`FibreProjectionCompat`/`FibreOverBaseTriv`/`FibreFlatness` prose by the `prose-sweep` tide. **#13 stays
open** to grow into the well-rounded Phase-1+2 PR.)

---

## PHASE 2 (RE-OPENED 2026-06-28, operator) — discharge `hT` by building real-AG

**Operator directive:** don't leave `hT` cited — build the (well-established, Mathlib-v4.29-absent) real-AG
to PROVE it, folded into THIS expedition. The payoff then rests on only the two analytic citations
(Watanabe `≤`, Aoyagi `≥`); every geometric fact — including the real↔complex transfer — proved.

- **Reduction (banked):** `hT ⟺ varietyDim_ℝ(fibre ℝ) = varietyDim_K(fibre K)` (field-generic catenary);
  `≤` free ⟹ the work is `varietyDim_ℝ ≥ varietyDim_K` per top component.
- **Two routes (recon 08 picks):** (1) smooth rational point `realizerD` + IFT ⟹ real `d`-manifold ⟹
  `dim ≥ d` (crux bridges: `pderiv`↔`fderiv`, the IFT/constant-rank API, manifold-dim ↔ `varietyDim`); (2)
  ℚ-unirationality of the GL-orbit closures ⟹ ℝ-points dense + full-dim.
- **Plan:** recon 08 (`realag-recon`, live) → route + lemma ladder (surface for sign-off) → build rungs in
  `DLNFibre.Core` (reusable, eventual Mathlib-upstream), decorrelated-reviewed to bedrock → generalize the
  `realizerD` smooth-full-dim certificate (all `d,r`) → discharge `hT` across interface + 7 consumers →
  `#13` grows into the well-rounded final PR (operator wants one complete PR; willing to wait).
- **Scaffold updated for Phase 2:** `brief.md` (Phase-2 central question + scope fences), `loop-prompt.md`
  (Phase status; load-bearing = the real-AG build; "do NOT stop at Phase-1 close"), `priorities.md`
  (Phase-2 rung table), `threads.md` (Phase 1 closed / Phase 2 active + thread 08). Backstop cron
  re-established (`f5b4cf8a`, hourly). Tasks #9–#11. Still BLIND to the aoyagi `RLCT/*`.
- **In flight:** recon 08 (route map) + the `#13` prose-sweep tide (review fixes). Holding for both.

### Phase 2 recon (thread 08) CLOSED — ROUTE DECIDED: the algebraic orbit-dimension squeeze

**`hT` IS bounded-provable at Mathlib v4.29 (~3–4 tides, NO new hard math) — thread 07's "T is cited"
verdict is SUPERSEDED** (decorrelated: recon 08 + its Codex both converged). The find: the repo already
banks `varietyDim_k(orbit closure) = finrank_k(range δ⁰_M)` as a **field-generic algebraic squeeze** over
a fixed 0/1 integer structure matrix (`realizerD`), never touching the real radical. The `≤` half is proved
over `[CharZero][Infinite]` (holds over ℝ); the `≥` half (`finrank_range_deformationδ_le_varietyDim`,
`OrbitTangentCotangent:641`) is stated `[IsAlgClosed]` but uses it **only to derive `PerfectField`** — and
ℝ is `CharZero ⟹ PerfectField`. So `varietyDim_ℝ = varietyDim_K` = the SAME field-independent integer-matrix
rank ⟹ `T′` by an **algebraic squeeze at the rational point M** — no real-IFT, no density; the `x²+y²` trap
dissolved by the smooth rational point of full local dim. The brief's IFT-route + unirationality-route are
both DOMINATED by this (the repo's smooth-point machinery IS the algebraic IFT).
- **CRUX:** relax `[IsAlgClosed]→[PerfectField]` on the orbit smooth-point squeeze core (the `[IsAlgClosed]`
  is vestigial — docstrings already assert PerfectField suffices). **Biggest unknown (L7):**
  `finrank(range deformationδ)` base-change invariance = a `LinearMap`-vs-`Matrix` packaging snag (integer
  structure matrix ⟹ rank field-independent in char 0), NOT math. Kill-condition (a rung consuming alg-closed
  beyond PerfectField) stress-tested, did NOT fire.
- **Ladder (G2 = minimal `T′`, ~3–4 tides):** L1 `dense_smoothLocus`/ℝ → L2 orbit prime `[Infinite]` → L3
  orbit smooth@M `[PerfectField][Infinite]` → L4 cotangent=dim `[PerfectField]` (CRUX) → L5 reverse → L6
  orbit-dim EQUALITY/ℝ → L7 δ⁰ base-change rank invariance → L8 chart δ-shift/ℝ → L9 assemble `T′` → L10
  discharge `hT` via banked `codimRealFibre_eq_codimRepCanonical_of_dimTransfer`. (G1 = full `codim_ℝ=C`/ℝ
  = the earned bedrock extension that retires `hT` as a theorem — pursue if within reach after G2.)
- **FIRST MOVE (launching): a 1-tide PROBE** — relax `finrank_range_deformationδ_le_varietyDim` to
  `[PerfectField k]` + green-build over ℝ; pin the exact L7 base-change lemma shape. Settles the crux + the
  biggest unknown before the full build commits. Build placement: `DLNFibre.Core` (reusable, upstream
  candidate). Task #9 done; #10 (build) gated on the probe.

### PR #13 review CLOSED OUT (2026-06-28)

Owner deep-review (no math-fidelity blocker) → all 5 items resolved. The `prose-sweep` tide (the 5 Core
files) + controller's aggregator/status/whitespace parts merged green (merge `4c09c28e`, pushed):
(1) stale "projection compat — open" swept — **L3 re-grep of the full class now EMPTY across aggregator +
Core** (it recurred in MORE sites than flagged, incl. `FibreBundleHeadline:138` — the sweep had been
incomplete twice; re-grep-to-empty is the fix); (2) "IS the comorphism" softened to the precomposition
form + doc-names fixed; (3) PR-body Watanabe scope corrected (universal-in-source / attainability-scoped);
(4) `threads.md`+`priorities.md` → final/Phase-2 state; (5) trailing whitespace stripped. PR body updated
(via REST — `gh pr edit` choked on a Projects-classic GraphQL deprecation) + marked **NOT-ready-to-merge**
(Phase 2 growing it); itemized reply posted to the PR. Build green 3817 jobs, sorry-free, axiom-clean.
**#13 now carries Phase 1 complete + review-addressed; Phase 2 (discharge `T`) crux-probe in flight.**

### Phase 2 — crux-probe INTEGRATED (L1–L6 landed over ℝ); L7+L8 wave dispatched (2026-06-28)

Crux-probe GO + over-delivery merged (merge `07691215`, pushed): **L1–L6 of the G2 ladder LANDED over ℝ**
— the `[IsAlgClosed]→[PerfectField]/[Infinite]` relaxation across the orbit-dim squeeze; `varietyDim_ℝ(orbit)
= finrank_ℝ(range deformationδ)` a named theorem at ℝ (axiom-clean); orbit-dim EQUALITY over ℝ; `codimRep =
orbitLinearCodim` over ℝ (free G1 partial). Reviewer SOUND; crux-probe also fixed 3 extra `[IsAlgClosed]`
rungs the recon's chain missed (caught only by the full-aggregator gate — the stale-olean lesson).
**Full-aggregator green-gate re-verified by controller: 3817 jobs, exit 0, sorry-free.**
- **L7+L8 wave DISPATCHED** (thread 10, `realag-l7l8`): L7 = `deformationδ` base-change finrank invariance
  (packaging, route R2 via `MatrixKaehler.finrank_range_baseChange` + the tensor-conjugacy square); L8 =
  chart δ-shift over ℝ (the remaining unknown — probe chart-vs-sigma, relax the lighter layer; report a
  kill-condition if a genuine non-PerfectField alg-closed dep fires on the fibre layer). Then L9 assemble
  fibre-level `T′` + L10 discharge `hT`.
- **BUILD-INFRA NOTE:** box under heavy load (loadavg ~15 on 8 cores; other sessions/the aoyagi line) —
  **detached/background `scripts/lb` builds were REAPED twice** (status `killed`, not OOM — 21 GiB free);
  the foreground build with the 10-min cap completed (incremental, `.lake` progress persists across kills).
  Mandate to tides: foreground green-gates; re-run on kill (progress persists). Task #10 in-progress.

### L7+L8 INTEGRATED (green); CAPSTONE discharge dispatched (2026-06-28)

L7+L8 tide merged (merge `7182d0eb`, pushed; full-aggregator green 3818 jobs, sorry-free, axiom-clean):
**L7** `Core.DeformationBaseChange` — `finrank_range_deformationδ_baseChange` (orbit-tangent dim same
integer over k and any extension); **L8** the fibre-codim headline
`FibreCodimFinal.codimRepCanonical_fibre_eq_cCodim_add_shift` (= C+δ) relaxed to `[CharZero][Infinite]`
(holds over ℝ) via a 10-file sweep, + the θ-count/perm-invariance headlines over ℝ. **Kill-condition did
NOT fire** (the "strong Nullstellensatz" suspect was field-generic — `vanishingIdeal` radical over any
field — reproved directly).
- **KEY: the discharge is now DIRECT — no `T′`/varietyDim-transfer needed.** Both sides of `hT` equal the
  same field-independent `C+δ` via the relaxed headline; the only micro-gap is `(B.map ι).rank = B.rank`
  (rank base-change). So the realizerD-smooth-point generalization (the recon's `T′` route) is SUPERSEDED
  — not needed for `hT`. (Recorded the route change; #11 reframed.)
- **CAPSTONE tide DISPATCHED (thread 11, `discharge-hT`):** prove `(B.map ι).rank=B.rank` → prove `hT` as a
  named theorem (headline both sides) → DISCHARGE the `hT` hypothesis across the 7 consumers → payoff rests
  on only `{Watanabe ≤, Aoyagi ≥}`; L3-sweep "T cited" → PROVED + re-grep empty; `#print axioms` stays
  clean. Then controller convenes the decorrelated fidelity+hardener re-review (cited boundary 3→2).
- **NOT in scope (roadmap):** the fibre-component/θ-count-AT-fibre layer (~10 files still `[IsAlgClosed]`,
  the LR Lemma 4.6 bundle content) — NOT needed for `hT`; a separate full-relaxation tide if wanted.

### CAPSTONE LANDED — `hT` PROVED + discharged; cited boundary 3→2 (2026-06-28)

Capstone tide integrated (merge `58ebb01c`, pushed; full aggregator GREEN 3818 jobs, sorry-free,
axiom-clean). **`hT` is now a PROVED theorem** `DLN.codimRealFibre_eq_codimRepCanonical_baseChange` (both
`codim_ℝ(fibre B)` and `codim_K(fibre B·ι)` = the same field-independent `C+δ` via the relaxed Core
headline + `Matrix.rank_map_eq_of_injective`; DIRECT route, no `T′`). The `hT` hypothesis is REMOVED from
all 8 payoffs ⟹ **`rlct(K^DLN_B) = ½·C` rests on ONLY {Watanabe `≤`, Aoyagi `≥`}** — every geometric fact,
incl. the real↔complex transfer, PROVED. `#print axioms` clean (no new axiom — hT a genuine theorem); L3
re-grep empty (no "hT cited" prose). Two traps caught: `Matrix.`-namespace-shadow (rank lemma → top-level
`Matrix` in `Core.RankLocusClosed`); Type-0 narrowing of the R/R2 sections (inherited from the Type-0 Core
headline; witnesses ℂ/AlgClosure-ℚ are Type 0 — honest, documented in the card's Scope note).
- **PHASE-2 GOAL ACHIEVED** (pending re-review): the operator's "discharge hT by building the real-AG" is
  done — and the real-AG turned out to be a typeclass relaxation of the repo's own field-generic squeeze,
  not a from-scratch build.
- **Decorrelated re-review convened (the final gate):** `fidelity-cap` (`a15102e4`) + `hardener-cap`
  (`a2b12a44`) on the capstone — fidelity (#print axioms / transfer genuine / discharge complete / Type-0
  honest / rank-lemma relocation / L3) + bedrock (discharge genuine-not-sleight / name=content / cited
  boundary honestly 2 / non-vacuity / beauty). Loop to equilibrium → then `#13` is the well-rounded PR.
  Task #11 lands on the re-review PASS.
  - **HARDENER re-review: SOLID** (`a2b12a44`, decorrelated Codex converged). VERIFIED (not relayed): the
    `git show` diff shows `hT` dropped at the signature level + the proved theorem invoked internally; the
    interface carries NO geometric field; `bundleShift_of_core` is a proved axiom-clean instance ⟹ `J` also
    genuinely discharged; all 10 load-bearing decls axiom-clean over the ℝ-compatible `[CharZero][Infinite]`
    Core headline (full build typechecks at `k:=ℝ`). The `x²+y²` pathology genuinely doesn't bite (both
    sides = the field-INDEPENDENT `cCodim`+δ; `realizerD` gives an explicit ℝ-rational full-rank top-component
    point via `[Infinite]`, not `[IsAlgClosed]`). name=content holds; Type-0 narrowing honest (inherited
    same-universe from the Schur-side no-drop); non-vacuous. **2 cosmetics → consolidation:** restore
    `_via_aoyagi` on the 2 fully-J-discharged BundleShiftDischarge payoffs (still rest on `I` = the cited
    bounds); fix 2 >100-char comment lines (`:117,:124`).
  - **Framing-precision correction (hardener caught my dispatch prose):** what's proved is the **codimension
    identity + the real↔complex codim TRANSFER**, NOT "all real↔complex geometry" — the fibre-bundle/
    component-count/smoothness layer over ℝ (LR Lemma 4.6) is separate + roadmapped, not the payoff's
    dependency. (Looser word didn't reach the repo/card.) Keep operator-facing language precise.
  - Holding for fidelity (`a15102e4`), then ONE consolidation pass (the 2 cosmetics + any fidelity findings)
    → finalize → `#13` well-rounded PR.

## PHASE 2 CLOSED — `hT` PROVED; the programme's prize landed (2026-06-28)

**Both capstone re-reviews PASS/SOLID** (decorrelated, each with Codex): fidelity PASS (all 14 load-bearing
decls axiom-clean, full DLN chain rebuilt 3732 jobs; the chain is alg-closed-FREE over ℝ — no `[IsAlgClosed]`
instance exists for ℝ, so the clean `#print axioms` over ℝ IS the proof) + hardener SOLID (discharge
genuine via the git-diff, boundary honestly 2, Type-0 inherited, non-vacuous, bedrock). **Consolidation:**
the `_via_aoyagi` "nit" was on closer read DELIBERATE (no-suffix = J-discharged destination; `_via_aoyagi` =
J-explicit; renaming would collide) — fixed the one genuine slop (a misleading "via_aoyagi" mention in the
no-suffix docstring); left the long comment lines (codebase-pervasive, non-failing lint). Final build green
3818 jobs, sorry-free, axiom-clean (`68562f2c`).

**THE RESULT:** `rlct(K^DLN_B) = ½·C` rests on **exactly two cited facts — Watanabe `≤` + Aoyagi `≥`,
both irreducibly analytic** — with EVERY codimension fact, including the real↔complex transfer, PROVED in
honest Lean. The "build the real-AG library" turned out to be a typeclass relaxation of the repo's own
field-generic squeeze, not a from-scratch build. Tasks #4–#11 all complete.

**PR #13 updated to the well-rounded final** (Phase 1 + 2 complete, ready for operator review/merge —
operator-gated; controller does NOT merge). Roadmap residuals (future, NOT needed for this result): global
`Flat π` + the fibre-component/Lemma-4.6 `[IsAlgClosed]` layer; the cross-paper `rlctAt` fold.
