<task>
I am formalising in Lean 4 + Mathlib the Aoyagi (2013) RLCT-order θ for deep linear networks.
GOAL THEOREM (A2b, "named witness" form, approved):
  monomialOrder (achiverK M) (achiverH M) = aoyagiTheta (cAch M) (aTheta M)
where I must DEFINE achiverK, achiverH as explicit closed functions of M.

DEFINITIONS (all exist / are pinned):
- M : Fin (L+1) → ℕ (reduced layer widths, L≥1).
- cAch M = the achiever split-length ℓ* (the LARGEST ℓ∈{1..L} minimising the clean core
  ¼(∑ balancedSplit² − ∑ (ℓ+1 smallest widths)²); = Nat.findGreatest of a "good" predicate).
- P* = Sprefix M (cAch M + 1) = sum of the ℓ*+1 smallest widths.
- aTheta M = P* mod cAch M  (the count of "big" entries in the balanced split).
- balancedSplit P ℓ = a multiset with a := P mod ℓ entries of value ⌈P/ℓ⌉=b+1, and (ℓ−a) of value b=⌊P/ℓ⌋.
- aoyagiTheta ℓ a := a*(ℓ−a)+1.
- axisRatio (h k : ℕ) : ℝ≥0∞ := (h+1)/(2k).
- monomialOrder d k h := card { j : Fin d | axisRatio (h j) (k j) = ⨅ j', axisRatio (h j') (k j') }
  (the number of axes attaining the minimum ratio).

KNOWN COMBINATORIAL FACT (numerically verified, all ground-truth cases):
  θ = a(ℓ−a)+1 = (#big)·(#small) "cross-pairs" + 1 "diagonal".
  Aoyagi: θ = max over charts of Card{ j : (h_j+1)/(2k_j) = λ } — the per-chart count of monomial
  directions TYING the minimum ratio λ = ½·minMval.

THE PROBLEM: I need the EXPLICIT achiever chart (k,h) — a function of M — whose monomialOrder
(tie-count) is exactly a(ℓ−a)+1. The controller REJECTED the trivial all-tied chart
(d = a(ℓ−a)+1, all axes k=1,h=0, every ratio ties) because that free-covers θ trivially without
forcing the genuine achiever geometry. The faithful chart must have axes that DON'T all tie — the
tie-count a(ℓ−a)+1 must emerge as a genuine count over the resolution's axis set.

What I'm unsure of: (1) what the resolution's chart axis-set IS for the achiever balanced split
(the blow-up directions — are they indexed by the L blocks? by ordered pairs of the ℓ blocks? by the
edges of a quiver?), and (2) the explicit (k_j, h_j) on each axis such that exactly the a(ℓ−a) mixed
(big,small) pairs + 1 attain the min ratio.
</task>

<output_contract>
1. RANK the 2-3 most plausible interpretations of "the achiever chart axis-set + (k,h)" that would
   make monomialOrder = a(ℓ−a)+1 a GENUINE (non-trivial) count — for each, state the axis index set,
   the (k_j,h_j) formula, and which axes tie. Prefer the one matching Aoyagi's resolution geometry.
2. For the top interpretation, give the explicit closed-form (achiverK M, achiverH M) — d (axis
   count), k_j, h_j as functions of (cAch M, aTheta M, b=⌊P*/ℓ*⌋) — and SHOW the tie-count = a(ℓ−a)+1
   arithmetic (which axes hit ⨅ axisRatio, why the count is a(ℓ−a)+1).
3. Flag explicitly: is the "+1 diagonal" axis a genuinely-distinct binding direction, or an artefact?
   And is a(ℓ−a) the count of (big,small) ordered or unordered pairs?
4. The single biggest risk that the faithful chart, as you define it, COLLAPSES to the trivial
   all-tied chart (i.e. ALL its axes tie) — and how to avoid it.
</output_contract>

<grounding_rules>
Distinguish what you can derive from the given definitions (mark "DERIVED") vs what you're inferring
about Aoyagi's resolution geometry without the paper (mark "INFERENCE — needs paper check"). Do not
invent a chart construction and present it as Aoyagi's if you're reconstructing it. If the honest
answer is "the faithful axis-set needs the paper's §X resolution and can't be pinned from these
definitions alone", say so — that's a valid and important finding.
</grounding_rules>
