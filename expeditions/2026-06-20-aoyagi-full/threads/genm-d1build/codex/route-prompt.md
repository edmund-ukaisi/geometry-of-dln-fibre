<task>
I am a Lean 4 (Mathlib v4.29) formaliser closing two `sorry`s in a large formalisation of
Aoyagi's deep-linear-network RLCT computation. I need a DECORRELATED strategic-route judgment
BEFORE I spend compute, because my task brief and the actual Lean state appear to diverge, and I
want an independent read on what is genuinely closable vs. what is a research wall.

## The two target sorries (both currently `sorryAx`), stated for GENERAL L (`H : Fin (L+1) → ℕ`):

(a) `deepest_regular_core_normal_form H r B ... (hpos : ∀ s, r < H s)`:
    `rlctAt H (dlnLoss H B) (deepestPoint ...) = (r*(H 0 + H last - r) : ℕ)/2 + ofReal(lambdaCore (H·-r))`
    — i.e. at the DEEPEST fibre point, the local RLCT splits as a regular shift nReg/2 plus a
    reduced-core term. This is Aoyagi's Lemma 2 + Theorem 3 (block-diagonal normal form + additive
    RLCT split).

(b) `rlctAt_deepest_le_of_optimal H r B ... (v : Params H) (hv : v ∈ optimalSet H B)`:
    `rlctAt H (dlnLoss H B) (deepestPoint ...) ≤ rlctAt H (dlnLoss H B) v`
    — the ≥-leg: deepest point has minimal local RLCT over the fibre (Aoyagi Theorem 4 / homogeneity).

## What is ACTUALLY BANKED (I have read the code):

For (a): There is a chain
  `deepest_regular_core_normal_form_of` (PROVEN) ← `deepest_regular_core_reduces` (PROVEN modulo one
  sorry) ← `deepest_gauge_squeeze_exists` (a bare `sorry`, produces `Nonempty (DeepestGaugeChart ...)`)
  ← `deepest_gauge_chart_construct` ← `deepest_gauge_construction`.
  `deepest_gauge_construction` DISPATCHES on L: the `L < 3` arm is SORRY-FREE but only CONDITIONAL on
  two hypotheses `hJfront` (front-pivot WLOG: B's rank-r pivot columns are the first r) and `htop`
  (row WLOG: B's top r rows are full rank). The `L ≥ 3` arm has 3 real geometry `sorry`s (a
  "grouped-G0 diffeo" / interior recursive reparam, roadmapped as "#120"). So (a) at general L is
  WALLED at L≥3; at L=2 it needs hJfront + htop discharged (by a claimed banked row/col permutation
  WLOG on the RLCT infimum) AND the R1 core value `rlctAtOn(dlnLoss (H-r) 0) 0 = ofReal(lambdaCore)`.

For (b): There is `rlctAt_deepest_le_of_optimal_L2` (PROVEN, but scoped to `H : Fin (2+1) → ℕ`,
  i.e. L=2 ONLY), using a TWO-PEEL IFT chart route: it threads `hDeepest` (= (a) at deepest),
  a first-peel C¹ residual `q` + chart-transfer equality `hchart`, a second-peel Jacobian-minor rank
  bound, and an R1 "interface" value at a degraded core M'. The first-peel `hchart` producer
  (`dln_hchart_residual`) is claimed banked, but the general-v middle-stratum `(m,a,b)` extraction
  (identifying the degraded reduced widths at an arbitrary optimal v) is open.

## The pen-and-paper certs (decorrelated, from 3 prior threads) claim:

The ≥-leg is "de-risked to a bounded explicit linear-algebra build, NOT the Morse-Bott/splitting
wall." Specifically: (i) rank(∏ partial product) ≥ r at every partial product & every fibre point
(full product factors through each partial), so an invertible r×r minor always exists ⟹ a FIXED
row/col permutation moves it to the corner and iterated corner-elimination NEVER STALLS ⟹ the
reduction is a FINITE explicit rational-chart atlas (one chart per invertible-r-minor), NOT a
parametrized constant-rank existence theorem. (ii) nReg = r(H0+Hlast−r) is CONSTANT over the fibre
(Aoyagi Thm 3 peels the SAME r×r FINAL-rank corner at every point; a higher stratum's extra rank
stays INSIDE the core as a nonzero basepoint), so λ_v = nReg/2 + λ_v(core) and Thm 4
(`deepest_le_of_homogeneous_core`, PROVEN) gives λ_v(core) ≥ λ_0(core).

BUT the current Lean route for (a) and (b) is the abstract IFT/splitting route (Gromoll-Meyer-style
local diffeo, "regStraighten", "second-peel chart"), which is exactly what the cert says is
OVER-GENERAL. Mathlib v4.29 has no Morse-Bott/constant-rank/splitting lemma. The cert's finite-atlas
re-scope does NOT appear to be reflected in the Lean; adopting it would mean re-architecting the
DeepestGaugeConstruction / D1SecondPeel machinery.

## What I have already established as fact:
- Baseline build is GREEN with the 4 named Skeleton sorries (2671 jobs, exit 0).
- Both (a) and (b) at general L currently = `[propext, sorryAx, Classical.choice, Quot.sound]`.
- There is NO general-L sorry-free path to either; the L=2 paths are conditional on open gates.
</task>

<output_contract>
Answer in exactly these 4 sections, terse and concrete:

1. VERDICT on the divergence: Is the cert's "finite-atlas, bounded" claim COMPATIBLE with closing
   the CURRENT general-L Lean sorries in a single formaliser tide, or does the current Lean
   architecture (abstract IFT/splitting + L≥3 #120 wall) mean a general-L close requires either
   (i) grinding the 3 #120 L≥3 geometry sorries, or (ii) re-architecting onto the finite-atlas
   route? Give the single most-likely-correct answer.

2. Given a leaf-executor formaliser (cannot re-architect, must not add axioms, must not paper over
   gaps): what is the LARGEST honestly-closable increment here? Rank these candidates by
   value-per-risk:
     (A) close (a)/(b) at general L via the finite-atlas re-scope (large, possibly a re-architecture);
     (B) wire the EXISTING L=2 conditional pieces into new sorry-free `_L2` theorems, leaving the
         general-L Skeleton sorries bare (banks L=2 progress, does not touch the headline);
     (C) reduce the bare general-L Skeleton sorries to a SMALLER, precisely-named set of open
         hypotheses (a "legible reduction" that names hJfront/htop/#120/R1-interface as explicit
         gated hypotheses) without closing them;
     (D) attempt only the discharge of hJfront/htop (the WLOG permutation reductions) at L=2 if
         those are genuinely network-free linear algebra.
   For the top-ranked, name the concrete first sub-step.

3. TRAPS: what would make a naive formaliser THINK they closed a sorry when they actually (i)
   introduced a hidden circular dependency, (ii) weakened the statement, or (iii) smuggled the wall
   into an unproven hypothesis? Name the 2-3 specific traps for THIS situation.

4. Is closing (b) at general L POSSIBLE at all with the "nReg constant over fibre" + banked Thm4
   route WITHOUT a splitting lemma, or does delivering `nReg/2 + coreV ≤ Lv` at an arbitrary
   fibre point v FUNDAMENTALLY require a local normal form (= a splitting lemma) that Mathlib lacks?
   One paragraph, decisive.
</output_contract>

<grounding_rules>
You do not have the repo. Reason from the structural facts I gave you (which I verified by reading
the code). Flag clearly when you are INFERRING vs. reasoning from a stated fact. Do NOT invent
Mathlib lemma names as if they exist. If a claim depends on a fact I did not state, say so.
</grounding_rules>
