# Thread-41 — Object-E ρ count-object certificate (pnp, decorrelated)

Charge (P6.2, PNP-gated): pin the exact object Aoyagi's pole multiplicity ρ counts over the tree/atlas,
and verify ρ = a(ℓ−a)+1 EXACTLY (both directions). Kill-set: the naive-divergent instances (led by
[3,3,1,1]) + tree-ρ ground truths (2,2,2)→1, (3,3,4)→1, (2,2,3,2)→1, (2,2,2,2)→3, (2,1,2)→2.
Read: charter §1-E, pp.23–26 images, worked.tex:912-957. No Lean.

## VERDICT: the object is the MAX-CROSSING NUMBER over the DEEPEST STRATUM. ρ = a(ℓ−a)+1 is EXACT.
The printed a(ℓ−a)+1 is CORRECT for the true object — NO graduation to the fidelity ledger.
Finding-2's looseness is confirmed an argument-shape (proof) issue, not a wrong printed value.

### The precise object (page-anchored)
    ρ  =  max over leaves (charts) of  #{ terminal (t̃=0) exceptional divisors u_{s,k}
                                          with M_{s,k} = minAdm,  co-crossing at that chart }.
- This IS worked.tex:216's `ρ = max_u #{j : (h_j+1)/(2k_j) = λ}`, made precise: since k_j≡1 the ratio
  of divisor u_{s,k} is M_{s,k}/2, so binding (ratio=λ) ⟺ M_{s,k}=minAdm; and within one normal-crossing
  chart all binding coordinate-divisors {u=0} pass through the chart's deepest point, so the per-chart
  crossing count = the per-chart binding-divisor count, and ρ = max over charts.
- The **t̃=0 (deepest-stratum) restriction is LOAD-BEARING and page-faithful**: page 22 takes the RLCT
  candidates as `½·min{M_{s,k} : t̃_{s,k}=0}` — ONLY terminal divisors are candidates (Aoyagi's local
  Def 1 + the Theorem-4 deepest-point reduction localise everything at w*=0). Non-terminal (t̃>0)
  divisors are NOT binding: e.g. [2,2,5] has a t̃>0 divisor of exponent 1 < minAdm=4, which is correctly
  NOT the RLCT. Dropping the restriction overcounts a(ℓ−a)+1 at 72/993 scanned cores.

### Why the NAIVE minimiser-count is the WRONG object (two distinct divergence classes)
1. **Loose-lattice artifact** (seat-E's [3,3,1,1], naive=2, ρ=1): the loose lattice (cap min(M¹,M²) for
   every t^(j)) admits DEGENERATE profiles whose rank exceeds a later width — e.g. (3,2,0) with t^(2)=2 >
   M^(3)=1 gives a spurious Mval=1 tie. These are not real strata. With the CORRECT running-min
   rank-bounded lattice, [3,3,1,1] has naive=1. (34 such artifact instances in the L≤3 range; 106 wider.)
2. **GENUINE incidence gap** (the decisive witness): [2,2,2,2,2] has SIX *valid* minimising profiles
   {(1,0,0,0),(1,1,0,0),(1,1,1,0),(2,1,0,0),(2,1,1,0),(2,2,1,0)} but ρ = max-crossing = 5 = a(ℓ−a)+1
   (a=2,ℓ=4). The profile (1,1,1,0) lives on a DIFFERENT branch and never co-crosses with the other five
   in any single chart. So even the correct-lattice minimiser count OVERCOUNTS ρ — max-crossing is
   STRICTLY the right object (6 such genuine instances in L=4). This is the sharp reconciliation the
   elder's hypothesis predicted.

## Exact verification (batteries, EXIT 0; exact integer/Fraction; `rho_battery.py`)
- CHECK 0: the Def-3 (a,ℓ) selector (ℓ+1 smallest reduced widths, max-ℓ, worked.tex ≥-fix; balanced
  ℓ-split a=P−(M*−1)ℓ) reproduces all hand values.
- CHECK 1: ρ = max-crossing = a(ℓ−a)+1 = known ρ on ALL FIVE ground truths.
- CHECK 2: 993 distinct cores (L∈{2,3,4}); **max-crossing = a(ℓ−a)+1 for every core** (0 mismatches);
  minAdm_tree == minAdm_lattice everywhere (rank-bounded lattice validated); loose-naive divergence
  reproduced incl. [3,3,1,1].
- CHECK 3: BOTH directions — UPPER (every chart ≤ a(ℓ−a)+1 co-crossing binding divisors) and ATTAINMENT
  (some chart realises exactly a(ℓ−a)+1) — hold over the whole scan.
- CHECK 4: the [2,2,2,2,2] genuine witness, concretely (6 minimisers, max chart = 5, the 6th on another
  branch); the tree UNION of binding divisors = the full minimiser set (tree is complete for binding).
- CHECK 5: ⋃_leaves(t̃=0 binding) == full minimiser set for EVERY core (tree completeness — the
  max-crossing gap is a true INCIDENCE fact, not a missing-chart artifact); the t̃=0 restriction is
  load-bearing (page-22).

## Codex (decorrelated, xhigh; `codex/rho-*.md`)
Fired blind, answer withheld. Independently identified the SAME object:
`ρ = max over charts of #{binding divisors present in the chart}` — "every point lies in some
normal-crossing chart … all binding coordinate hyperplanes in a chart meet at its origin … the naive
total ignores incidence." For [3,3,1,1]: "the two minimizing profiles occur in incompatible charts." It
correctly flagged that a(ℓ−a)+1's exactness needs exactly two leaf-incidence facts — the UPPER bound and
ATTAINMENT — which "do not follow from the number or values of the minimizing lattice profiles," and that
enumeration alone cannot prove them. This is precisely what the tree battery verifies (both directions).

## Structure / ideas for the formaliser (route is the controller's; recorded as data)
- The Lean object already present is `boxedOrder` (per-chart count of min-attaining binding divisors);
  the identity to state is `ρ = max over charts boxedOrder = a(ℓ−a)+1`. `boxedOrder` MUST count only
  terminal (t̃=0) divisors (the page-22 candidate condition) — else it overcounts.
- P6.2 is a MAX-OVER-CHARTS statement, not a lattice cardinality; the naive minimiser count is provably
  the wrong headline (both the degenerate-profile artifact AND the genuine incidence gap). seat-E's
  Tier-1 `bandCount = area + 1` is the arithmetic value; the count-IDENTIFICATION owes the two
  leaf-incidence lemmas: (i) UPPER — no branch carries more than a(ℓ−a)+1 co-crossing t̃=0 minimisers;
  (ii) ATTAINMENT — the eq-(1)/(2) construction (pp.25-26) builds a branch with exactly a(ℓ−a)+1. Both
  are branch/recursion-incidence facts (Lemma 4's envelope+increment characterises which minimisers can
  co-occur on one branch), NOT re-derivable from the minimiser count. (Speculation, register as such:
  the UPPER bound is the harder half — it is the paper's loose per-j band sum done tightly, i.e. the
  max antichain of co-occurring binding profiles on a single root-to-leaf path.)
- The analytic identification (combinatorial max-crossing = zeta pole multiplicity) remains the named
  monument-class deferral (no pole-order operation in Mathlib) — unchanged by this certificate.
