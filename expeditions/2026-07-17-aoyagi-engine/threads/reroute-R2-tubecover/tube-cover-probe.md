# Tube-cover probe (#169, #145-at-depth) — WITNESS: the fan covers up-to-null (detail-at-scale)

**Seat:** reroute-R2-tubecover (fresh pen-and-paper, decorrelated). Exact algebra (sympy over ℚ) +
own Codex xhigh (`codex/tubecover-{prompt,answer}.md`, EXIT 0) — CONVERGED by an independent route.
NO Lean. Scripts (this dir): `probe1_unit_vs_R.py`, `probe2_fan_cover.py`, `probe3_mc_cover.py`.
Instance: **(3,3,3,2,2) t=(2,2,1,0)** — the SAME separated-depth deep-mixed instance as the ideal-side
probe (`reroute-R3-idealside/deeper-mixed-probe.md`), so the two probes COMPOSE.

## NET VERDICT: WITNESS — the born-sibling fan covers the {unit≈0} tubes UP-TO-NULL for the LOWER
bound. **DETAIL-AT-SCALE**, not a monument hole. Prices route P's destination = **(A) fully-cite-free
reachable / (B) P-with-small-cite**, NOT (C) objects-only. Two decorrelated sources agree.

The concern was mis-scoped by using the WRONG unit. The tube is a property of the *two-sided
principality proof technique*, not of the *lower bound*. Corrected, the tube is covered — by the SAME
chart (dominant mechanism), with survivor-entry siblings covering the wide-box residue.

---

## THE INSTANCE (faithful; from thread-28 / `g-coupled-33322-separated.py`)
Terminal leaf, C3bar=[[1,p],[q,s],[u,v]] (3×2, radial `w`), C4bar=[[1,c],[d,cd+f]] (2×2, radial `y`),
Y=C3bar·C4bar (3×2), and in ORIGINAL coords X=C3·C4:
- **loss = (w·y)² · R**,  R = ‖Y_row0‖² + δ₂²‖Y_row1‖² + δ₁²‖Y_row2‖²,  **R(origin)=1**.
- pivot-quotient unit  u_piv = Y[0,0] = **1+pd** = X[0,0]/(w·y).   {u_piv=0}={X[0,0]=0}: **codim 1**.
- The two-sided identity ⟨loss⟩=⟨(wy)²⟩ via the pivot needs 1/(1+pd) → regular only on {1+pd≠0}.
  THIS is where the ideal-side probe saw the leaf "localize."

## THE CORRECTION: the load-bearing unit for the LOWER bound is **R, not 1+pd** (Codex Q1, PROVEN)
The lower bound uses loss ≥ c·(wy)², i.e. it needs **R** (the full residual sum-of-squares) bounded
below — NOT the single pivot quotient. |1+pd| bounded below is merely *sufficient* (R ≥ (1+pd)²), never
necessary. Consequences, all verified:

1. **{R=0} is CODIM 4, not codim 1** (`probe1`). Real sum of squares ⇒ R=0 iff every summand=0 ⇒
   (generic δ₁,δ₂≠0) Y=0 ⇒ (C3bar injective, C4bar[0,0]=1) forces the rank-1 degeneration
   {pd=−1, f=0, q=s/p, u=v/p} = **{C3bar·C4bar=0}**. In orig coords {X=0}={C4=0 given C3 generic}=codim 4.
2. **On the codim-1 tube {1+pd≈0} minus {R=0}: R>0** (sampled min 0.012). loss=(wy)²·R is then
   loss-REGULAR where wy≠0, and reads as the monomial (wy)² where wy≈0 — the vanishing of the single
   pivot quotient does NOT lower the RLCT (Codex Q2, PROVEN).
3. **R>0 on a whole ball of radius <1** (EXACT: R ≥ (1+pd)² ≥ (1−rad²)² for |p|,|d|≤rad<1; `probe3`
   MC matches 0.83/0.42/0.044 = (1−0.09)²/(1−0.36)²/(1−0.81)²). So {1+pd=0} (needs |pd|=1, dist √2 from
   origin) is **ABSENT near the origin**; the tube only appears at box scale ≥1.

## Q3 (Codex, PROVEN): the SAME canonical chart covers the tube via 1/R
At the exceptional corner {1+pd≈0} ∧ {wy≈0} ∧ {R>0}: ⟨loss⟩=⟨(wy)²⟩ holds in the local ring using
**1/R** (regular, R>0) as the cofactor — the *pivot-based* proof of the identity fails but the identity
does not. **No sibling is needed to cover the {1+pd≈0} tube.** Only corners accumulating on {R=0}
need more. This is the dominant mechanism and it dissolves the brief's headline worry.

## The FAN mechanism (for the wide box needed by angular coverage) — which sibling covers which tube
When a generator genuinely vanishes (X[0,0]=0) AND R is also small (approaching {R=0}), the cover is by
a **survivor-ENTRY sibling**, and here a SHARP, ACTIONABLE distinction emerges (`probe2`, exact):

- **(A) RADIAL-PIVOT-only fan FAILS.** The four charts that vary which input entry is the radial but
  keep X[0,0] as the survivor all have unit = X[0,0]/monomial ⇒ **all vanish on {X[0,0]=0}** ⇒ they
  cover **0%** of the tube at every box size (`probe3`: X00-only = 0.0% at boxR=1,2,4). [FACT]
- **(B) SURVIVOR-ENTRY fan COVERS.** The sibling pivoting on a DIFFERENT generator — X[0,1] =
  C300·C401+C301·C411, generically ≠0 on {X[0,0]=0} — is valid on the tube. The full 6-generator fan
  covers **100% at boxR≥1** (`probe3`). [FACT + MC guide]
- **The common-uncovered set = {all generators=0} = {X_row0=0} (codim 2) / {X=0} (codim 4, generic δ)**
  (`probe2` exact solve; `probe3` MC: {all 6 gens < 0.1·max} = 0.0000% over 2M samples). No
  positive-measure common hole.

**Which sibling covers which tube:** the {X[i,j]≈0} tube is covered (1) by the SAME chart via 1/R
wherever R>0 (dominant), and (2) by the survivor-entry sibling pivoting on any generator X[i′,j′]≠0
there, for the wide-box generator-vanishing residue. The residual common hole is the deep stratum {X=0}.

## The deep stratum {R=0}={C3bar·C4bar=0}: RECURSION, must be performed (Codex Q4, INFERENCE)
{R=0} is a smaller matrix-product-vanishing locus — the SAME DLN-fibre problem one level down ⇒ the
recursion resolves it (self-similar, detail-at-scale). Codex's sharp caveat: **codim-4 alone is NOT a
free pass** — the deeper charts must actually cover the {R=0} tube AND verify no new exceptional divisor
has ratio < ½·minAdm. Why it holds (INFERENCE, instance-verified): the recursion's deeper divisors are
the OTHER admissible-t values, all with codim ≥ minAdm by minimality ⇒ ratios ≥ ½·minAdm ⇒ the lower
bound survives. Instance check: thread-28 got rlct=2=½·minAdm(=4) exactly via the single chain b₁=wy
(ratios w:3, y:2, min 2) — the recursion terminates at the right value here.

## FIRMEST / MOST-LIKELY-TO-BREAK / GENERALITY
- **FIRMEST [FACT, exact + decorrelated]:** the {1+pd≈0} pivot-quotient tube is NOT an uncovered hole
  for the lower bound. The correct cofactor is 1/R (R = full residual, R(0)=1); R>0 on a ball of radius
  <1 (exact), so the canonical chart alone covers a neighbourhood, tube included. For the wide box, the
  full survivor-entry fan covers the tube 100% at boxR≥1; the common-uncovered locus is {X=0} codim ≥2.
- **MOST LIKELY TO BREAK IT (two, both scoped):**
  1. **A radial-pivot-only fan is a REAL no-go** (covers 0% of the tube). The build MUST fan over the
     survivor ENTRY (each generator of the residual ideal), not just the input radial pivot. This is
     the SAME lesson as the sector-count's "the shear must be fanned with the pivot" / "coinciding
     charts are needed" and its route (A) "(pivot, pivot-adapted-normalization) pair fan." If R2 drifts
     to a fixed-survivor fan, the tube is uncovered.
  2. **The recursion's divisor-ratio bound at general L** (Codex Q4). The minAdm-minimality argument
     (deeper divisors ≥ minAdm) is INFERENCE; instance-verified at (3,3,3,2,2). A general-L reproduction
     is the build labour, not a monument, but it must be *done*, not assumed.
- **GENERALITY:** verified EXACT at ONE instance (3,3,3,2,2), the canonical separated-depth deep-mixed
  case. The mechanism (loss=monomial²·R, R sum-of-squares with a kept-"1" ⇒ R(0)=1, {R=0} high-codim
  self-similar) is the thread-28 kept-rank-survivor structure (inductive), so it should generalize —
  but that is INFERENCE, not exhaustive proof. Codex's unproved residue (sibling common-zero algebra)
  is closed here by the exact solve; its recursive divisor-ratio residue remains inference.

## RELATION TO #145 / sector-count (the reconciliation, made rigorous at depth)
The #145 ~2% "escape" splits into TWO independent phenomena:
- **(B2) the {unit≈0} tube** — THIS probe. RESOLVED: detail-at-scale (1/R + survivor-entry fan; deep
  stratum = recursion). The ~2% here was an over-worry from using the single pivot quotient 1+pd
  instead of the full residual R.
- **(B1) the sector-count "escape cone"** {max_W > C·max_V} — SEPARATE, shear-slot-induced (the 128
  non-normal-crossings charts), order-dependent (the sector-cert's own "shear outermost" note suggests
  it may be a Cartesian-fan artifact). NOT this probe's question; still priced by sector-count as route
  (A) pivot-adapted normalizations OR loss-regularity OR route (C). This probe does NOT close (B1).

## CLOSE
The tube-cover gate is GREEN for the lower bound: **WITNESS, detail-at-scale**, pricing route P as
(A)/(B), not (C). The load-bearing correction — bound R (the full sum-of-squares residual), not the
single pivot quotient — dissolves the headline worry; the residual obligations (survivor-entry fan
spec + the recursion actually performed with the minAdm-ratio check) are honest detail-at-scale build
labour, precisely named. NEXT: (i) fold "fan over the survivor ENTRY, subordinate to the generators of
the residual ideal" into R2's family-cover spec; (ii) the general-L recursion-ratio check is build
labour, not a de-risk gate; (iii) the sector-count escape cone (B1) remains a separate, already-priced
question — do not conflate it with the tube.
