# scout-lr1 — long-range paper-first gap sweep (decorrelated)

**Seat:** scout-lr1, decorrelated long-range SCOUT for expedition 2026-07-17-aoyagi-engine.
**Posture (operator steer):** the PAPER is the touchstone — Aoyagi (2023)'s resolution mechanism
(via `theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex`) — and MATHEMATICAL NECESSITY is the
bar, never Lean-build convenience. Hunting AVOIDANCE: built-less / built-narrower / hard-part-scoped.
**Method:** read the worked reproduction end-to-end + ROADMAP.md first, built my own mechanism-contents
list, THEN swept the Lean surface (`lean/DLNFibre/DLN/RLCT/**`, `AxCheck.lean`, `Skeleton.lean`,
`HeadlineGenAssembly`, `Core/CThetaValue`) mapping each item BUILT / BUILT-NARROWER / STATED / ABSENT.
Fired ONE decorrelated `local-codex-consult` (xhigh) on the draft list — `codex/gap-list-{prompt,answer}.md`.
I was NOT shown the team's own scoping rationales or the elder charge-7 memo first (decorrelation).

---

## A. Mechanism-contents list, with verdicts

Aoyagi's mechanism, item by item (page/section cites into `aoyagi-2023-worked.tex`).

| # | Item | Paper | Lean verdict |
|---|------|-------|--------------|
| M1 | RLCT def (`rlctAt`) | Def 1, §1.2 | **BUILT-NARROWER** — `rlctAt` is the φ-free *germ* threshold; no φ-parameterised def matching Def 1's bump, and the germ→compact-box step exists only as the one deepest-box instance (`box_integrable_of_lt_rlctAtOn_deepest`), not generically. φ-independence is *used*, not a general theorem. Mathematically the germ threshold is the right object (φ(w*)≠0 ⟹ φ-independent), so this is a fidelity/definitional narrowing, not a value gap. |
| M2 | Lemma 1: RLCT depends only on the ideal (monotone under ideal inclusion) | Lemma 1 | **BUILT-NARROWER** — S1.3 gives germ-locality + unit-multiplication invariance + a.e.-diffeo transport (`rlct_unit_invariant`/`rlct_germ_local`, S1.1 transport). The paper's *general* statement (arbitrary analytic ideal inclusion `G∈J ⟹ rlct(ΣG²)≥rlct(ΣF²)` for finite generator families) is NOT stated. The mechanism only uses the unit/CoV special cases (block-elim transforms are units), so the value is safe; the general lemma is unbuilt. |
| M3 | Monomial rule (Hironaka pullback → `min_j (h_j+1)/(2k_j)`) — the paper's ONLY permitted citation (S2) | boxed rule | **BUILT — S2 RETIRED (better than the paper needs).** The former axiom `monomial_rlct` is *gone*; the threshold conjunct is PROVEN S2-free via `monomialThreshold_eq_iInf_axisRatio` (`MonomialThresholdIdentity`). No live `monomial_rlct` declaration exists. |
| M4 | Lemma 2: block elimination / Schur, unipotent transforms | Lemma 2 | **BUILT** — `block_elimination` (Skeleton.lean:242), general. |
| M5 | Theorem 3: peel the regular rank-r part; RLCT splits = Morse block + `rlct_0(core)` | Thm 3, eq (thm3-split) | **BUILT (value) / NARROWER (local identity).** `product_reduction` (Skeleton.lean:1105) + the sorry-free general-L front chain `deepest_regular_core_reduces_frontPivot_front` (0 sorries, bypasses the old #120-sorried `deepest_gauge_construction`) give `rlctAt(deepest)=ofReal(aoyagiLambda)` for general L, r>0. The paper's *general-point* local RLCT-split equality is only ever used one-directionally (a `≤`, the D1 leg); the two-sided local identity is not a standalone theorem. |
| M6 | Theorem 4: deepest-point domination (homogeneity + l.s.c.) | Thm 4 | **BUILT** — `deepest_le_of_homogeneous_core` hypothesis-free; the general-L D1 `≥` leg is wired sorry-free (`d1ge_deepestPoint_via_explicit_core_genL_wired`). Far/non-origin points ride the banked domination. |
| M7 | The recursive blow-up, Cases 1 & 2 — **THE MOUNTAIN** (monomialise the core ideal) | §3.3, p.15–22 | **IN FLIGHT** — the coverage theorem + `region_glue` = the box-finiteness `hbox` (the `½·min_t Mval(t)` geometric LOWER bound). This is the one genuine new proof; correctly the expedition's spine. NOT avoidance. |
| M8 | The Jacobian (each exceptional divisor `u_{s,k}` carries power `M_{s,k}−1`) | §3.3, p.15,492–494 | **IN FLIGHT** — `LeafJacobian`/fold-det cocycle (`GeoJacobianFold`, task #21/#43 open). |
| M9 | Candidate thresholds `M_{s,k}=Mval(t)=codim S(t)`; `rlct_core = ½·min_t Mval(t)` | §3.4 | value banked (`minAdm = cCodim`, axiom-clean); the *geometric* `=½·min` proof IS `hbox` (IN FLIGHT). |
| M10 | Lemma 3: within-set balance, `min_b A(b)=a·ℓ·(ℓ−a)` | Lemma 3, p.24 | **BUILT (value) / NARROWER.** The value is folded into `lambdaCore`; the explicit quadratic `A(b)` and the *adjacent-minimiser tie* `A(a−1)=A(a)` — which is exactly what θ counts — are (per source read + Codex) absent as such. |
| M11 | Closed form `2·rlct_core = ½(Σqᵢ² − Σmₖ²)` | §5.3 | **BUILT** — `lambdaCore`. |
| M12 | Lemmas 4–5: the ORDER `θ = a(ℓ−a)+1` (two-envelope characterisation + count) | §5.4, p.25–26 | **ABSENT** — only a bare `aoyagiTheta ℓ a := a(ℓ-a)+1` on *given* (ℓ,a) data (`RRR.lean`); no theorem computes (ℓ,a) from widths, no count proof, no loss-binding. The earlier placeholder `aoyagiTheta_eq` was EXCISED (Skeleton.lean:1662). |
| M13 | Theorems 1 & 2 (value theorems) | Thm 1,2 | **L2: PROVEN clean-three, sorry-free, S2-free** (`aoyagi_learning_coefficient_L2`). **General L≥2: proven CONDITIONAL only on `hbox`** (`aoyagi_learning_coefficient_gen`, HeadlineGenAssembly:55) — plus the `hpos` narrowing below. |
| M14 | RRR / L=2 case | §6 | **BUILT** (the L2 headline is its instance). |

**The `hpos` narrowing (cross-cutting, load-bearing):** every learning-coefficient theorem — L1, L2,
and general-L — carries `hpos : ∀ s, r < H s`, i.e. **all reduced widths `M^(s)=H^(s)−r` STRICTLY
positive**. Aoyagi's theorem covers reduced widths = 0 (a layer at exactly rank r; the closed form uses
the ℓ+1 smallest widths, possibly 0). The team documented (compass instance #6, witness `M=[2,2,0]`) that
at a zero reduced width the *attainment* half `minAdm ∈ terminalExponents` is FALSE — a zero last-width
forces immediate rollover, so the minimiser stratum is never realised by the resolution tree. So this is a
real narrowing of the **primary** result, not a trivial add.

---

## B. Top-5 "the math wants this built" (ranked by mathematical necessity)

Ranking adopts the decorrelated Codex reorder: the PRIMARY value theorem on Aoyagi's FULL domain
outranks the secondary θ result.

1. **`hbox` = the coverage theorem + `region_glue` (M7/M8/M9)** — the resolution mountain's `½·min_t
   Mval(t)` lower bound; the one genuine new proof. *IN FLIGHT — the expedition's correctly-chosen spine,
   NOT avoidance.* **Composite** (atlas coverage · pullback monomialisation · Jacobian powers ·
   small-box→unit globalisation). Size: large — the whole current spine.

2. **Extend the value theorem to ZERO reduced widths (drop `hpos>0`).** This completes Aoyagi's *full
   domain* for the PRIMARY result — the single highest-value AVOIDANCE item (a live narrowing of the hero
   theorem, present at L1/L2/gen). **Composite**: (a) the arithmetic collapse of `lambdaCore` at a zero
   width (independent, cheap); (b) a genuine analytic *layer-collapse* — a zero-width layer must reduce
   the depth L, else (Codex) the identically-zero core has RLCT `⊤` and naïvely dropping `hpos` is FALSE.
   Part (b) is within Aoyagi's mechanism spirit (it is a reduction-to-lower-depth). Size: medium–large;
   part (a) alone is small and shippable now.

3. **Aoyagi's combinatorial `θ = a(ℓ−a)+1` (M12 = Lemmas 4–5).** ABSENT; Aoyagi's *second* deliverable;
   needs a well-defined (ℓ,a) selector, Lemma 3's tie-structure `A(a−1)=A(a)` (M10, currently only its
   value), and the two-envelope count. Fully independent of the in-flight analytic resolution. The
   *analytic* binding (count = pole multiplicity) is correctly out of scope (meromorphic continuation,
   Mathlib-absent). Size: medium.

4. **Record the θ NON-IDENTITY (`aoyagiTheta ≠ numTop`) and correct the ROADMAP.** See §D — this is a
   genuine mathematical clarification, not just docs. Size: small (one `#eval` + a documented
   non-identity), high clarifying value; a prerequisite framing for #3.

5. **Axiom/docstring hygiene.** `AxCheck.lean` docstrings still name the *retired* `monomial_rlct` as an
   expected axiom on the achiever-divergence lemmas (e.g. `routeMCore_box_diverges_achiever_full`), while
   the code routes S2-free (`RouteMAchieverFull.lean:32` says so explicitly and no `monomial_rlct`
   declaration exists). Stale-comment vs real-residual — confirm with a forced `#print axioms`. Size: small.

---

## C. Independently-buildable lines (NO dependence on the in-flight `hbox`/coverage/`region_glue`)

Candidates for parallel lanes right now:

- **[strongest] Aoyagi combinatorial `θ = a(ℓ−a)+1` (top-5 #3).** Pure combinatorics on the (ℓ,a)
  selection + Lemma 3 tie. Reuses the already-banked `lambdaCore` (ℓ,a) machinery. No analytic dependency.
- **The θ non-identity check + ROADMAP correction (top-5 #4).** A pen-and-paper/scout task: one `#eval` of
  `cTheta ![2,2,2,2,2]` against Aoyagi's `a(ℓ−a)+1` for equal-width L=4, then a documented non-identity.
- **Zero-width VALUE/arithmetic side (top-5 #2, part (a)).** The `lambdaCore` collapse at a zero reduced
  width — arithmetic only. (The attainment side, part (b), touches the resolution tree, so is *not* fully
  independent.)
- **Lemma 1 as the general analytic ideal-inclusion monotonicity (M2).** A Foundations-level bedrock lemma,
  independent of the spine; sharpens `rlctAt` fidelity to Aoyagi Lemma 1 (and would retire the "used only in
  special cases" caveat). Size: medium; a real bedrock nicety, not on the critical path.
- **Axiom-footprint hygiene (top-5 #5).** Independent, small.

---

## D. The load-bearing finding: two DIFFERENT θ's are conflated

`ROADMAP.md` Bundle 4 (lines 190–199) states: *"the RLCT **multiplicity** m=θ — the pole ORDER at −λ,
the paper's number of top-dimensional components θ = a(ℓ−a)+1."* This single sentence names **two distinct
invariants** as one θ:

- **Aoyagi's θ** = RLCT pole order = number of binding divisor-branches over the deepest stratum = `a(ℓ−a)+1`.
- **LR's `numTop`** = number of top-dimensional irreducible components of `Σ̄^r`, BUILT unconditionally in
  Bundle 1 as `cTheta d = Nat.choose (qipM d) (qipDelta d).natAbs = binom(m,|δ|)`
  (`Core.CThetaValue`, `numTop_eq_ncard_topComponents`).

They coincide at `(2,2,2)` (both `1`) — a small-case accident. Decorrelated Codex counterexample:
**`M=(2,2,2,2,2)`, r=0 (equal widths, L=4):** Aoyagi `ℓ=4, a=2 ⟹ a(ℓ−a)+1 = 5`; the fibre formula gives
`m=4, |δ|=2 ⟹ binom(4,2) = 6`. **5 ≠ 6.** (Aoyagi (ℓ,a): equal-width `Ms−1 < 5/4·2 = 2.5 ≤ Ms ⟹ Ms=3`,
`a = 5·2 − 2·4 = 2` — matches the worked reproduction's equal-width example. The `numTop=6` value should be
confirmed by `#eval cTheta ![2,2,2,2,2]` — I did not run a build.)

Consequence (mathematical necessity): the RLCT pole order is **not** the global number of top-dimensional
fibre components. The deferred "θ analytic-multiplicity seam" must bind Aoyagi's pole order to `a(ℓ−a)+1`
(M12), **never** to the built `numTop`. Any mint framing or ROADMAP text implying `numTop` *is* the RLCT
multiplicity is a fidelity error. This is Codex's blindspot warning made concrete: three counts get
conflated — (i) tied divisor ratios in one chart, (ii) Aoyagi's binding branches, (iii) global top-dim
components — and only (ii) is Aoyagi's θ.

---

## E. Not gaps (checked, sound)

- **S2 genuinely retired** — no live `monomial_rlct`; threshold proven S2-free. Better than the paper.
- **General-L r>0 value** — sorry-free via the front chain; Theorem 3 is not deferred (my initial
  suspicion, refuted on read).
- **The paper's own defects the expedition correctly fixed** (Def-3 sign typo, case-2 raw-width,
  the p.15 chain, the realisation gap `P(M)=Clearable-Adm`) — these are documented typo-fixes where the
  Lean is *more* honest than the paper; fidelity strengths, not avoidance.
- **LR "second half"** (θ/Poincaré/QIP/explicit-formula/perm-invariance for the *fibre* paper) — landed
  reviewed+bedrock (Bundles 1–3); `numTop` unconditional. Complete at the paper's generality — with the
  §D caveat that its θ is a *different* θ from Aoyagi's.
