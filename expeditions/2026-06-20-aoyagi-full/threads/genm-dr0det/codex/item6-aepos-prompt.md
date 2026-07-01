<task>
Lean4/Mathlib. Need the CHEAPEST route to a.e.-positivity of the deepRank=0 unit factor, to feed a
NodeAchieverChart bundle's Ubound field. deepRank=0 means Text M (tach M) 2 = 0.

The unit: eDeepRank0Unit ha ... x := VvalGen (x eBlockPivot) M (tach M) (genBlkFlatEfp ... x) hle.
VvalGen u B hle := ∑ i, ∑ j, (HrGen u B hle i j)^2  (a sum of squares of the telescoped Hmat0 entries;
HrGen is a reindex of the chain's Hmat 0). So eDeepRank0Unit ≥ 0 always (banked VvalGen_nonneg).

GOAL: ∀ᵐ u, 0 < eDeepRank0Unit ... u   (a.e.-positive on Fin N → ℝ, Lebesgue).

BANKED PATTERN (the LEAF leg, interiorLiveUnit): build a nonzero MvPolynomial UPolyLive with
eval u UPolyLive = interiorLiveUnit u, then MvPolynomial.ae_eval_ne_zero (nonzero poly ⟹ zero set null)
+ nonneg ⟹ a.e. > 0. The nonzero-ness UPolyLive ≠ 0 is shown by exhibiting a point (an admissible T /
"all-ones") where the unit is nonzero. Building UPolyLive requires a POLYNOMIAL decoder genBlkFlatLiveGen
+ Xvec + sqSumHmat0 + chainOfMt_map naturality (~100 lines of machinery), all keyed to the LEAF chart
(interiorLiveUnit, which needs 0 < Text 2 — FALSE at deepRank=0, so NOT reusable).

deepRank=0 STRUCTURE that might simplify: at Text 2 = 0, the chain is short. The loss factorization
routeMCore(φ x) = (x eBlockPivot)^2 · V (banked rate). The chart φ at radial u=x_p is
paramsEquivFlat(chartParamsGen (x_p) (genBlkFlatEfp x)). At deepRank=0 the K/X/N blocks vanish; A0 = the
E-block (with pivot (0,0) pinned to 1), A1 = the W-block. So the product prod M (chartParams) = A0 · A1,
and V = ‖Hmat0‖² where u • Hmat0 = prod (the u-scaled telescoped product). Since the pivot E-entry is
pinned to 1 and the radial u = x_p, at least ONE entry of the product is guaranteed nonzero when x_p ≠ 0
and the W-block is generic.

QUESTIONS:
1. Is there a route to ∀ᵐ u, 0 < V that AVOIDS building the full polynomial decoder (genBlkFlatEfpGen)?
   Options to rank:
   (a) VvalGen IS already ∑(Hmat0)²; if I can show the map u ↦ Hmat0(genBlkFlatEfp u) is itself given by
       eval of a matrix of MvPolynomials (each entry a polynomial in u), then ∑(entry)² is a polynomial,
       and nonzero at one point ⟹ nonzero poly ⟹ ae. Is the CLEANEST to build ONE polynomial
       "some specific Hmat0 entry" (not the whole decoder) and show IT is a nonzero poly, then
       V ≥ (that entry)² and {V=0} ⊆ {that entry = 0} which is null?
   (b) Since A0 = E has the pinned pivot (0,0)=1, is there a SINGLE product entry (prod M chartParams) i j
       that equals a MONOMIAL like (x_p)·(product of W entries) + ... that is manifestly a nonzero
       polynomial? If prod's (0,0) entry (or some entry) is x_p · (something) + lower, exhibit it.
   (c) Reuse an existing GENERIC brick: is there a banked lemma "VvalGen (genBlk...) is eval of a nonzero
       poly when the decoder is nonzero at a point" that is NOT tied to the leaf chart? (e.g. a
       Core.MeasureTheory.PolynomialZeroSet helper, or a sqSumHmat0-based generic.)
2. For the chosen route, the KEY lemma chain (3-5 steps) + the hardest sub-lemma.
3. Is the "V ≥ (single entry)^2, {V=0} ⊆ {entry=0}, entry a nonzero poly ⟹ ae" route (option a) sound and
   cheap? What is the single entry to pick at deepRank=0 to make its nonzero-poly-ness trivial? (Ideally an
   entry whose polynomial is a single monomial in x_p times a W-coordinate, nonzero at all-ones.)
4. Biggest risk / wall.
</task>

<output_contract>
Q1: rank (a)/(b)/(c) with 1-line rationale. Q2: lemma chain for the winner + hardest sub-lemma.
Q3: yes/no on the single-entry route + the concrete entry to pick. Q4: the wall.
End VERDICT (2 lines): the route + the first lemma to prove.
</output_contract>

<grounding_rules>
Distinguish banked-fact from inference. Flag guesses about the exact form of prod/Hmat0 at deepRank=0
(I did not give the full chain def). Prefer the route needing the FEWEST new Lean definitions.
