# General-`d` build surface — the next phase of `aoyagi-engine`

_Scout `geo-atlas-gd`, 2026-07-27. A deep, math-first re-grounding of the surface for the GENERAL-`d`
theorem, after the `(3,3,4)` `rlct = ½·codim` landing (cite-free, monument-free, honest Lean). This is a
MAP, not a build — objects / crux / ladder / risks. Grounded in the source math (`worked.tex`, L&R) + the
LANDED Lean (`r2ov-integration` @ `39e24057d`), not just a restatement of the compass._

Registers used: **Observation** (from a specific read/computation), **Claim** (believed, with a
kill-condition), **Speculation**, **Question**.

---

## 1. THE GOAL OBJECT — the general-`d` theorem + its dependency structure

**The theorem.** For every DLN dimension vector `d = (d_0,…,d_L)` (`Monotone d`, `0 < N = L`, positive
widths, nonempty fibre) at the base point `B = 0`:

> `rlctGlobal (lossDLN d 0) = ½·(codimRealFibre d 0)`.

**The precise Lean landing point (Observation, verified in `r2ov-integration`).** The payoff
`DLN.rlct_lossDLN_eq_half_codimRealFibre` (`RlctPayoff.lean:478`) takes an `I : RlctRealInterface d` and
composes its two fields into the equality. `RlctRealInterface d` (`AoyagiCited.lean`) has **exactly two
fields**:

- `cited_watanabe_upper` : `rlctGlobal (lossDLN d B) ≤ ½·codimRealFibre d B` — **the ≤ half.**
- `cited_aoyagi_lower`  : `½·codimRealFibre d B ≤ rlctGlobal (lossDLN d B)` — **the ≥ half. THE CRUX.**

The general-`d` destination = build a **cite-free** `aoyagiRlctRealInterface : RlctRealInterface d` (today
its two fields are the `cited_*_ax` axioms) and delete the axioms. Equivalently: discharge the general
monument `exists_coreResolution` (currently `sorryAx`, `LearningCoefficient.lean:292`) OR bypass it with a
direct cite-free proof of the two bounds.

**Dependency structure — what is already general-`d` vs what is the gap.**

- **The GEOMETRIC half is DONE at general `d`.** `codim = minAdm = cCodim` is PROVEN general-`L`
  (`minAdm_eq_cCodim`, `MinAdmCCodim.lean:315`, `hL : 1 ≤ L`), with the base-change transfer
  `codimRealFibre_eq_codimRepCanonical_baseChange`. So `codimRealFibre d 0` is a solved, computable ℕ. The
  gap is entirely the **analytic RLCT side**.
- **The deepest-point reduction is DONE at general `d`.** `rlctGlobal (lossDLN d 0) = rlctAt (coreGen d) 0`
  via homogeneity + lower-semicontinuity (`rlctGlobal_eq_rlctAt_zero_of_homogeneous`, landed;
  `worked.tex:509–553`, Aoyagi Thm 4). So both bounds reduce to bounds on `rlctAt (∑ (coreGen d)ᵢ²) 0`.
- **The ≤ half is general-`d`-liftable (Observation, Card 3).** The single-chart change-of-variables upper
  `rlctAt_sumSqFam_le_chartMin_half` is general (any one `Chart`), and the forward-only variant
  `rlctAt_coreGen334_le_four_forward` witnesses that it needs only ONE chart's FORWARD ideal inclusion — no
  atlas, no cover, no `θ`, no reverse principality. Matches `worked.tex`: V-upper is complete-general. So
  `cited_watanabe_upper` is the **easy half** — a bounded lift, not the crux.
- **The ≥ half is the crux** — everything below is about `cited_aoyagi_lower`.

---

## 2. BUILT + REUSABLE (general-`d`) vs `(3,3,4)`-SPECIFIC

### Built general-`d`, sorry-free, clean-three (the engine survives the re-scope)

_All verified present + banked in `r2ov-integration`._

| Object | File | What it gives at general `d` |
|---|---|---|
| **SoS/Tonelli engine** `monoSumSq_integrableAtFilter_of_lt` | `Core/Aoyagi/MonomialSumSqRLCT.lean:269` | For arbitrary `D`, monomial `a`/`jac`, block `Z`: integrable for every `cc < min(monomialThreshold a jac, |Z|/2)`. The `|Z|/2` term is where the binding value lives. **Network-free.** |
| **Abstract V-lower wire** `rlctAt_ge_iInf_threshold_of_sandwich_cover` | `Core/Aoyagi/SandwichCover.lean:237` | Finite chart family + area-formula data + `hchain` + per-chart FROM-BELOW sandwich + a.e.-cover ⟹ `rlct ≥ minᵪ monomialThreshold`. **`hideal_bwd`-free / `exists_coreResolution`-free.** |
| **Integrability spine core** `mem_localAdmissible_of_sandwich_lt` | `Core/Aoyagi/SandwichCover.lean` | Takes per-chart integrability `hint` DIRECTLY; **both** leaf engines (chain + SoS) feed it. |
| **Per-chart survivor sandwich** `chart_rlct_ge_half_of_survivor`, `chart_rlct_ge_half_chartMin` | `SurvivorSandwich.lean:96`, `Core/Aoyagi/ChartValueLower.lean:50` | General `D`: `hpull : K = (∏ u^{ek₀})²·∑ fᵢ²` + survivor `f i₀ 0 = 1` ⟹ `infₐₓₑₛ (h+1) ≤ 2·wrlct`. |
| **General-`d` COVER** `covers_fanOfSteps`, `exists_ball_subset_outerFan_leafImages`, `outerShear_covers`, `blockShear_covers_*` | `GeneralGeoAtlas.lean:375, 428, …` | Inductive fold over an **arbitrary-depth** step-list fan of per-node triangular det-1 `outerShear`s (one scalar pivot/node); per-node box-containment brick PROVEN; closes a ball around `0`. All in `#assert_banked_clean_batch`. |
| **Single-chart V-upper** `rlctAt_sumSqFam_le_chartMin_half` | `Corank2UpperBound334.lean` | The ≤ half, general. |
| **`minAdm = cCodim`** | `MinAdmCCodim.lean:315` | General-`L` geometry. |
| **b-chain / exponent ledger** `bexp`, `divExp`, `terminalExponents`, `minAdm_le_terminalExponents` | `ResolutionTree.lean`, `RecursionAdapter.lean` | General-`L`; the `b₁|b₂|…` divisibility is by construction (`worked.tex:596–607`). |
| **Recursion engine** `buildTree`, `stepUpdate`, `conRel_wf` | `EngineConstruction.lean:414`, `EngineDefs.lean:175` | General `M`; the WF fold idiom. A few sorries remain in `EngineConstruction`/`EngineDriver`/`EngineObligations` (the geometric obligations). |

**Observation (the decisive re-scope survivor).** The abstract V-lower wire is `hideal_bwd`-free AND
clean-three at general `d`. So the general-`d` lower bound does **not** need the two-sided principal normal
form — it needs a ONE-SIDED cover-atlas (charts + Jacobians + from-below sandwiches + cover). This is what
`(3,3,4)` used, and it is genuinely lighter than the monument (skips reverse principality). **Confirmed two
ways**: the Lean (the wire's type has no `hideal_bwd`) and the source (`worked.tex:718–720`: the cover lower
bound is "structural/inductive … no full atlas needed"; F10: the lower bound needs `R>0`, not two-sided
principality).

### `(3,3,4)`-SPECIFIC — needs generalization (mostly mechanical, one exception)

- The 288-chart **folded fan** `Corank2NativeFan334`/`Corank2FoldedFamily334`, the 16-way `IsClean`
  classifier, the `σ_{p1}` per-type straightening — the concrete cover enumeration. **(3,3,4)-bound.**
- The over-vanishing binding spine `rlctAt_coreGen334_ge_four_of_perchart_integrable`
  (`Corank2OverVanishAssembly334.lean:130`): hardcodes `Fin 21`, `dvec`, threshold `4`. **But its proof is a
  thin wrapper over the general `mem_localAdmissible_of_sandwich_lt`** (`hint` fed directly). Generalizing =
  `Fin 21 → flatDim d`, `4 → ½·minAdm d`, `dvec → d`. **Mechanical.**
- The concrete leaf census (144 clean + 144 over-vanishing), `folded_hint`, `folded_hg_inj`. **(3,3,4)-bound.**
- `atlasRealizesExponents_334` (`Corank2Realize334.lean:104`) — the `(3,3,4)` instance of L3.

---

## 3. THE TRUE CRUX — is L1/L2/L3 the right surface? does general-`d` bypass the monument?

**The crux is the general-`d` lower bound `½·minAdm ≤ rlctAt (∑ (coreGen d)ᵢ²) 0`.** Everything else is
landed or mechanical (§1–§2).

**Precise reduction (Claim, grounded).** Via the landed engines, `rlct ≥ ½·minAdm` reduces to supplying,
over a general-`d` a.e.-cover of a neighbourhood of `0`, the per-leaf datum `hint`: for each leaf chart
`g_c`, the pulled-back weighted loss is integrable for every `cc < ½·minAdm`. Per leaf `hint` is discharged
by ONE of two landed engines:

- **CLEAN leaves** → `chart_rlct_ge_half_of_survivor`: `loss∘g_c ≥ E²·∑fᵢ²` (survivor `E = Pmat[0][0]` the
  pivot entry); reads the MONOMIAL threshold.
- **OVER-VANISHING (binding) leaves** → `monoSumSq_integrableAtFilter_of_lt`: `loss∘g_c ≥ vm²·∑_Z u²`; the
  binding value `½·minAdm` comes from the SoS `|Z|/2` term, NOT the monomial threshold.

So the GAP is not the wire, not the cover, not the engines — it is producing the per-leaf `hpull`/`hint`
FACTORIZATION over the general-`d` recursion. That is L1 (the from-below sandwich SHAPE) + L3 (the
exponents/`|Z|` REALIZE `½·minAdm`), threaded through the recursion.

### Is L1/L2/L3 the right decomposition? — mostly yes, with two sharpenings

1. **L2 (cover) is much further along than L1/L3 and is not the crux.** The cover fold is landed general-`d`
   (`covers_fanOfSteps`, `exists_ball_subset_outerFan_leafImages`), and the per-node box-containment brick is
   proven for the `outerShear` form. The only L2 residual is the **fidelity link** — that the ACTUAL
   recursion's per-node shears equal the `outerShear corr`-with-kept-sources shape (the hypothesis `hout`).
   Low–medium risk; it rides L1's construction anyway. **Recommendation: fold L2 into L1's build, do not
   track it as a peer.**
2. **L1 and L3 are one derivation, not two.** Both are read off the SAME per-leaf pullback
   `K∘g_c = (monomial)²·(nondegenerate SoS)`: L1 is "there is such a factorization from below", L3 is "its
   exponents/`|Z|` sum to `½·minAdm`". The compass already flags "the exact `L1=L3` identity is a to-adjudicate
   item"; I read them as **the same object at two scales** — keep them named distinctly for audit, but expect
   one construction to discharge both, and treat a divergence between them as a red flag (the realization
   `AtlasRealizesExponents` clause-(ii) not matching what the sandwich actually delivers).

### Does general-`d` BYPASS `exists_coreResolution`? — YES, structurally. But read the fine print.

**YES** (Observation, verified): the `(3,3,4)` lower bound closed via `rlctAt_ge_iInf_threshold_of_sandwich_cover`
(`hideal_bwd`-free), and `exists_coreResolution` stayed off its axiom cone. The general-`d` abstract wire is
the same object, clean-three. So general-`d` does not need the two-sided principal normal form.

**But the fine print is the honest hard part.** The one-sided cover-atlas is still **Aoyagi's full Cases-1&2
RECURSION** (`worked.tex:609–630`) — charts + Jacobian exponents + cover — merely without the
reverse-principality bookkeeping. And here `(3,3,4)` is a **luxury instance**:

> **Observation (the L=2 luxury — `worked.tex:709–710, 712–723`, verified against the source).** At `L=2`,
> ONE incidence + ONE blow-up leaves a **nondegenerate rank-`r` Morse quadratic** residual — so the SoS/Tonelli
> engine closes the binding leaf IMMEDIATELY, at the top. "That is precisely why `L=2` works and only `L=2`."
> At `L≥3`, one blow-up does NOT leave a Morse residual (a `(2,2,2,2)` witness vanishes to order 4). One must
> **DEPTH-RECURSE**: one (incidence + one blow-up) peels EXACTLY one layer, `F = α²·ρ²·‖X·C^(3)⋯C^(L)‖²`, a
> **fresh depth-`(L−1)` core**. For coupled corank-`≥2` branches the peel does NOT factor
> (`F_core = ‖T C^(3)‖² + δ²‖R C^(3)‖²` shares `C^(3)`); the recursion continues on a COUPLED core.

So at general `d`: the SoS engine applies only at the recursion **bottom** (`L=1` Morse). The binding value
is assembled from the intermediate divisor thresholds (`α`-divisor `≥ ½Mval(0)`, `ρ`-divisor `= ½Mval(branch)`,
recursive divisors `≥ ½·min` by induction — `worked.tex:718–720`) COMPOSED with the bottom SoS. **This
intermediate-threshold composition is not exercised by `(3,3,4)` at all** (one step, immediate Morse bottom).
It is the true general-`d`-specific content, and the most likely place a gap hides.

### Where the coupling actually bites (Claim)

Not in the cover (landed), not in the engines (landed), but in the per-leaf `hpull` derivation THROUGH the
multi-step recursion:

- **(a) Composition of the born-α fed form (F13's named risk).** Does the born shear at each node keep
  exposing a survivor / keep the intermediate cores in a form the next step can shear — through several
  `stepUpdate`s, including rollover-after-Case-2 where a Case-2-cleared slot feeds a later shear input? This
  was ASSERTED for the pivot-adapted fed form (verified at `(3,3,4)`, one step; one instance `(3,3,3,2,2)`),
  never re-derived from the actual multi-step `stepUpdate`.
- **(b) Termination at a nondegenerate SoS bottom (`#172`, WITNESS-CLEARED but not built).** The `{R=0}`
  recursion: depth drops 1/peel, bottoms at `L=1` Morse, `≤ L` steps. Believed sound; needs building +
  the per-step invariant preserved.
- **(c) The realization `L3` at general `d`.** The recursion's produced exponents must match `minAdm`'s
  attaining leaf (`AtlasRealizesExponents` clause-(ii)); `(3,3,4)` discharged `atlasRealizesExponents_334`,
  general `d` needs the general form.

**The `<δx,δy>` vs `<δ₁x,δ₂y>` obstruction is NOT a killer for the bypass (Observation).** `worked.tex:766–770`:
threshold-only data is insufficient (rlct `½` vs `1`, identical light data). But the SoS engine reads `|Z|/2`,
which COUNTS the independent residual directions — exactly the sharing content threshold-only misses. So the
from-below survivor + SoS route DOES capture the symbolic support; it is not the threshold-only trap. This is
consistent with the `(3,3,4)` coupled corank-2 success (SoS gave the correct `4`). The residual worry is
depth (b), not width.

### The pivot-cross survivor FAILS as a general-depth bound (Claim — Codex-sharpened, the sharpest correction)

The compass F13 "corank-insensitive pivot-cross survivor" (`Pmat[0][0] = E` ⟹ `loss ≥ E²`) is
**corank-insensitive ALGEBRA but NOT, by itself, a general-DEPTH lower bound.** At `L=2`, `P = C^(1)C^(2)` and
`loss = ‖P‖_F² ≥ E²` immediately. At `L≥3`, `loss = ‖P·C^(3)⋯C^(L)‖_F²`, and `P₀₀ = E` does **NOT** imply
`loss ≥ E²`: set the deeper product `C^(3)⋯C^(L)` to zero while keeping `E ≠ 0`. The true per-leaf model is
`E²·‖v‖²` (a survivor TIMES a unit tail) or a coupled sum — and **certifying that unit tail is exactly the
recursive obligation** (L1 at depth). So the `(3,3,4)` survivor argument does not lift verbatim; the general
lower bound needs the tail model, which is the coupled-core induction. (This also corrects the compass's own
framing: F13's "structurally cannot touch the residual block" is true of the pivot-cross entry as ALGEBRA,
but the LOSS at depth is not that single entry.)

### The geometry and the ledger are TWO SEPARATE Lean objects — the correspondence is the missing theorem (Observation — Codex-surfaced, verified)

A structural fact the compass/synthesis under-state: in the landed Lean, **`buildTree`/`stepUpdate` carry the
LEDGER only, not the geometry.** `stepUpdate` returns `ResolutionTree.RootLedger L` (`EngineDefs.lean:175`), and
its docstring states "SUPPORT PROPAGATION is STOP-AND-SURFACEd (NOT modelled here) … deferred to the named
`genDivExp` redesign rung" — so the SYMBOLIC divisor SUPPORT (which `u`-variables are shared, the load-bearing
content of `worked.tex:784`) is **not propagated by the recursion.** And `case2Decision` installs
`⟨id, 0, 0, 0, Fin.elim0⟩` — `localSub := id` (`EngineConstruction.lean:1965`); `buildTree` carries **no
geometric substitution.** The real geometry lives SEPARATELY in `MonumentAtlas.stepMapRaw` / `foldG` /
`canonNormalizationOf`. **Consequence: L1 and L3 are NOT yet consequences of the landed recursion.** The
central missing object is a **geometry↔ledger correspondence theorem** — that the composite geometric pullback
`loss∘(foldG …)` at each leaf has monomial/`|Z|` data matching what `stepUpdate` records — proved by induction
on a STRENGTHENED class (see §5). This is where "recursive divisors are good by induction" stops being
circular. This is the true seam, and it re-frames the first rung (§4).

---

## 4. THE LADDER — rungs (3,3,4) → general-`d`, and the FIRST rung

**Rungs (each a build unit once the first rung clears):**

1. Generalize the over-vanishing spine `…_ge_four_of_perchart_integrable` → general `d`
   (`Fin 21 → flatDim d`, `4 → ½·minAdm d`). **Mechanical, low risk** — do it early to pin the target type.
2. Build the general-`d` recursion chart family from `buildTree`/`stepUpdate` (leaves + Jacobians) — the R3
   geometry-valued WF fold (charter §1-B: "THE risk"; the 9×-proven WF idiom threading analytic charts).
3. **Prove the per-leaf `hpull` factorization (L1) through the recursion** — the composition-critical rung;
   bottoms at the SoS engine via (b).
4. Prove the realization L3 (exponents/`|Z| = ½·minAdm`); shares leaves with L1.
5. Wire the cover fidelity (actual shears `= outerShear corr` with kept sources) — L2, low–medium risk.
6. Compose → cite-free `cited_aoyagi_lower` → delete the axiom in `aoyagiRlctRealInterface`; the `≤` half
   (§1) lifts in parallel; `le_antisymm` → the general-`d` equality; `#print axioms` clean-three.

**THE FIRST RUNG (the pivotal de-risk — highest value, do this BEFORE committing the ~10–16-tide build):**

> **The multi-step GEOMETRY↔LEDGER CORRESPONDENCE probe, from the ACTUAL `stepMapRaw`/`canonNormalizationOf`
> (NOT `stepUpdate`).** Take a genuine binding deeper instance — `(3,3,3,2,2)`, `t = (2,2,1,0)` is the
> compass's existing coupled witness — and a reachable path containing (1) a genuine Case-2/Case-1 geometric
> step, (2) a ROLLOVER, (3) the first nontrivial POST-rollover step. Generate the composite geometric map from
> the real `stepMapRaw`/`foldG`/`canonNormalizationOf` (`MonumentAtlas.lean:325, 373, 939`), **not** a
> hand-written fed-form model and **not** `stepUpdate` (which carries no geometry — §3). Verify SIMULTANEOUSLY,
> by exact algebra:
> - the exact composite Jacobian monomial;
> - the pulled-back loss domination `loss∘g ≥ m²·∑_{z∈Z} z²` **or its coupled recursive analogue** (the unit-tail
>   model `E²‖v‖²`, per the §3 depth counterexample — not the bare `E²`);
> - the claimed survivor `m` is the SAME monomial the ledger `stepUpdate` records (the correspondence);
> - `monomialThreshold(m) ≥ ½·minAdm` AND `|Z|/2 ≥ ½·minAdm` where applicable;
> - **the child core satisfies the SAME (strengthened, coupled-`diag(b)`) induction invariant** — this is the
>   clause that makes the induction non-circular (§5).

One probe tests L1, L3, composition, AND threshold realization together. It is a **pen-and-paper /
exact-algebra seat** (`witness` if the correspondence holds and the child stays in the invariant class;
`obstruction` if the composite over-vanishes or leaves the class), decorrelated Codex, **not a build.**

**On the compass's two gates** (composition probe + α-uniformity probe): **merge them, and REJECT the
"`stepUpdate`-only" framing.** The α-uniformity question is the single-step shadow of the composition
question; and a `stepUpdate`-based probe is insufficient because `stepUpdate` currently contains no geometric
substitution (§3). Run ONE deeper instance end-to-end from the real geometry (`stepMapRaw`/`foldG`); it is
strictly stronger and the true gate.

---

## 5. RISKS / MONUMENT-FLAGS

**Standing tripwires (carry forward — each caught a real defect):**
- **from-below-not-toric** — a toric-LP / Newton-polytope / monomial-ideal reading is an UPPER bound on the
  true rlct (SoS-RLCT monotone under ideal inclusion); it does NOT certify the lower bound. Verify every
  lower-bound cert is from-below (resolution / regular-sequence).
- **engine-reads-the-shape** — the chain wire collapses `∑bₖ² = b_{k₀}²·U` and caps at the monomial threshold,
  discarding the SoS vanishing; the `|Z|/2` binding value lives only in the SoS block. Match the RHS shape to
  the engine (product-shaped regular sequence → the SoS/Tonelli engine, NOT the chain wire).
- **ledger-is-not-geometry** — `resRank` is hardcoded `0`; derive `bexp`/`k₀` from the ACTUAL pulled-back loss
  `K∘g = monomial²·unit`, never off the hardcoded field.

**NEW flags (this re-grounding):**
- **The SoS-at-bottom DEPTH risk (the sharpest new flag).** `(3,3,4)`'s SoS closure is an `L=2` luxury (one
  blow-up → Morse). At `L≥3` the SoS engine applies only at the recursion BOTTOM, and the value must be
  assembled from intermediate divisor thresholds composed with the bottom SoS via the structural/inductive
  lower bound. `(3,3,4)` exercises NONE of this (one step, immediate bottom). It IS the general-`d`-specific
  content and the most likely gap. → the first-rung probe targets exactly this.
- **L1≠L3 (the realization gap).** If the recursion's exponents don't match `minAdm`'s attaining leaf
  (`AtlasRealizesExponents` clause-(ii)), the bound is `½·(something)`, not provably `½·minAdm`. Keep L1/L3
  named distinctly and treat a divergence as a red flag.
- **The geometry↔ledger CORRESPONDENCE is unbuilt (the sharpest structural gap, §3).** `stepUpdate` carries no
  geometry (`localSub := id`), and its symbolic-support propagation is explicitly deferred (`genDivExp`
  redesign rung). So "the recursion's exponents realize `½·minAdm`" is a statement about the LEDGER; "the
  pulled-back loss factors from below with those exponents" is a statement about the SEPARATE geometry
  (`stepMapRaw`/`foldG`). No theorem yet links them at general `d`. Building L1/L3 = building this
  correspondence + reviving support-propagation.

**What would make general-`d` a MONUMENT (the kill-condition on the "detail-at-scale" verdict).** The
concentrated unresolved item is a **coupled-core lower-integrability INDUCTION INVARIANT, closed under the
composed Case-1/Case-2 geometric maps**, whose monomial/Jacobian data match `stepUpdate`. Precisely (Codex,
corroborating `worked.tex:753–784`): the residual core at a coupled leaf is **not a fresh bare DLN loss** — it
belongs to a STRENGTHENED class containing `diag(b)` and its shared support, and "recursive divisors are good
by induction" is **circular** until that induction hypothesis is formulated for coupled weighted cores and
shown STABLE UNDER COMPOSITION. If it closes by induction on the symbolic `diag(b)` support → substantial but
decomposable engineering (detail-at-scale). **If it fails — a composed pullback over-vanishes, or the child
leaves the induction class — the precise monument is a NEW coupled-core integrability/resolution theorem
repairing Aoyagi's induction** (fall back to the two-sided resolution, or objects-only). This claim is
verified at ONE coupled step `(3,3,4)`, UNVERIFIED through the depth recursion. The first-rung probe is the
decisive test.

---

## 6. VERDICT + REFLECTION

**Verdict (Claim; the decorrelated Codex consult CORROBORATES and sharpens it — §7).** General-`d` is
**leaning detail-at-scale, but "monument-free" is NOT YET EARNED.** No single deep new-math obstacle is
VISIBLE: resolution is via explicit toric/monomial blow-ups (not general Hironaka), and every abstract engine
(SoS/Tonelli, the `hideal_bwd`-free wire, the general-`d` cover fold, the survivor sandwich, `minAdm=cCodim`,
the deepest-point reduction) is landed general-`d` and clean-three. BUT the concentrated unresolved item is
not routine plumbing: it is the **whole one-sided recursive-resolution invariant** — a coupled-core
lower-integrability induction closed under the composed Case-1/Case-2 geometric maps, WITH its monomial/`|Z|`
data matching `stepUpdate` (the geometry↔ledger correspondence, §3/§5). The one-sided route generalizes only
as a FULL one-sided recursive resolution, **not** as "cover plus one final SoS call" — that shape is the
`L=2` luxury. If the coupled induction closes on the symbolic `diag(b)` support, it is substantial but
decomposable engineering (~10–16 tides); if a composed pullback over-vanishes or leaves the induction class,
the precise monument is a new coupled-core integrability theorem repairing Aoyagi's induction. The honest
present state is EXTRAPOLATION from `L=2` + locally-modelled single steps.

**Kill-condition (stated before hunting confirmers):** the first-rung composition probe exhibits a deeper-`L`
adversarial rollover instance where the born shear FAILS to expose a survivor / the intermediate residual is
NOT a nondegenerate SoS at the bottom / the per-step thresholds do NOT compose to `½·minAdm`. Any of these ⟹
the bypass is `L=2`-only and general-`d` is a monument (or objects-only).

**Which claim is most likely to advance the expedition:** the reduction of the entire general-`d` gap to
`cited_aoyagi_lower` (§1) + the recognition that the engines are all landed and the gap is the per-leaf
`hpull` through the recursion (§3). This turns a vague "build the general resolution" into a precise, gated
build.

**Which claim is most likely to break:** the "corank-insensitive survivor bypass composes through depth"
inference (F13). It is the least-tested and the one the L=2-luxury observation most directly threatens.

**The next computation that would clarify:** the first-rung geometry↔ledger correspondence probe (§4) — a
`witness`/`obstruction` seat on a deeper-`L` adversarial rollover instance (`(3,3,3,2,2)`, `t=(2,2,1,0)`),
generated from the REAL geometry `stepMapRaw`/`foldG`/`canonNormalizationOf` (NOT `stepUpdate`, which carries
no geometry — §3), checking the coupled induction invariant is stable under composition.

---

## 7. Decorrelated Codex consult (xhigh) — CORROBORATES + sharpens

Fired on the crux ("detail-at-scale or monument, and the true first rung?"; prompt `/tmp/codex-gend-crux.md`).
Codex's independent verdict AGREES with §6 and sharpens three points — all integrated above:

1. **Verdict: "plausible detail-at-scale, but 'monument-free' is not yet earned. The unresolved item is the
   whole one-sided recursive-resolution invariant, not routine plumbing."** The precise risk: closure of a
   weighted, coupled `diag(b)` lower-integrability invariant under the actual composed Case-1/Case-2
   geometric maps, with monomial/Jacobian data matching `stepUpdate`. (→ §6, §5 kill-condition.)
2. **The pivot-cross survivor is NOT a general-depth bound.** At `L≥3`, `P₀₀ = E` does not give `loss ≥ E²`
   (set the deeper product to zero); the true model is `E²‖v‖²` and certifying the unit tail IS the recursive
   obligation. (→ §3 new subsection.)
3. **The Lean reads (independently found): `stepUpdate` updates only `RootLedger`, support-propagation absent
   (`EngineDefs.lean:170`); `buildTree` installs `localSub := id` (`EngineConstruction.lean:1965`); real
   geometry is `TreePath.stepMapRaw`/`foldG`. So L1/L3 are not yet consequences of the landed recursion — the
   geometry↔ledger correspondence theorem is missing.** (→ §3 new subsection, §5 new flag.) This is why the
   first-rung probe must run from `stepMapRaw`/`canonNormalizationOf`, not `stepUpdate` (§4).

Codex's over-vanishing-threshold correction (adopted): the binding value is `min(T_m, |Z|/2)`; at `(3,3,4)`,
`T_m ≥ 4` and `|Z|/2 = 4` — if `T_m = 4` both mechanisms bind, if `T_m > 4` the SoS block alone binds. So the
value is neither "entirely survivor-driven" nor universally "entirely SoS-driven"; the SoS block is
INDISPENSABLE, the survivor supplies `T_m`.

Codex's bottom line, adopted verbatim as the phase gate: **"run the actual composite geometry–ledger probe
first. A clean result would justify the detail-at-scale classification; without it, the current general-`d`
confidence is extrapolation from `L=2` and locally modelled steps."**

