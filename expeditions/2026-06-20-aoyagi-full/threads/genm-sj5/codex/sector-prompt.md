<task>
An exact finiteness/covering question in a resolution-of-singularities computation for deep linear
networks. Adjudicate adversarially — I need to know whether a "sector" reduction can cover the whole
domain or whether a degenerate stratum forces a genuinely different estimate. HUNT the obstruction; do
not reassure.

SETUP. Front factor A₀ : m×r (integrated over the box [−1,1]^{m×r}); deeper matrix P : r×n (fixed,
varying over its own box). Front loss frobSq(A₀·P) = ‖A₀P‖_F². Let λ₁≤λ₂≤…≤λ_r be the eigenvalues of the
Gram G = P·Pᵀ (so √λ₁ = σ_min(P) is the smallest singular value). In the Gram spectral basis U,
  frobSq(A₀·P) = Σ_{j=1}^r λ_j · ‖(A₀U)_{·j}‖²   (each column of A₀U is a free ℝ^m vector).
Define g(P) = ∫_{A₀ box} frobSq(A₀·P)^{−c'} dA₀.

THE PROPOSED "SECTOR" REDUCTION. Fix κ>0. The sector predicate is
  sjSector(κ,P): "every non-minimal Gram eigenvalue is ≥ κ²", i.e. λ_j ≥ κ² for all j ≠ argmin.
On the sector one has the TWO-BLOCK lower bound
  frobSq(A₀P) ≥ λ₁·‖(A₀U)_{·argmin}‖² + κ²·Σ_{j≠argmin}‖(A₀U)_{·j}‖²   (v-block dim m, u-block dim m(r−1)),
hence (two-block radial) g(P) ≤ C_κ · λ₁^{−α}·... with α = max{0, 2c'−m(r−1)}, i.e. g(P) ≤ C·σ_min^{−α}.
The claim under scrutiny: by choosing a region (a measurable subset of P-box) and a κ, one covers the
P-box by finitely many such sectors so that ∫_{P-box} g(P) dP < ∞ for c' < ½·minAdm.

KNOWN RED FLAG (F2): the sector does NOT follow from "dominant-minor / σ_min control": e.g. P=diag(1,2),
A₀=(0 1), κ=3 gives the FALSE 9 ≤ 4 (the second eigenvalue 4 < κ²=9). And on the codim-2 stratum
(σ_{r−1}→0 as well as σ_r→0) the second-smallest eigenvalue → 0, so sjSector(κ,·) FAILS for any FIXED κ>0.

Answer, exactly (r=3, m=3, n=4 is the concrete case; minAdm=7, ½minAdm=7/2):

Q1. Exact radial scaling of g(P) on the codim-k stratum (k smallest singular values ≍ σ→0, the rest ≍1):
    g(P) ≍ σ^{−β_k}, β_k = max{0, 2c'−m(r−k)}. Confirm β_1 = 2c'−m(r−1) and β_2 = 2c'−m(r−2), and that the
    codim-1 majorant σ_min^{−β_1} is EXCEEDED by the true g on codim-2 (β_2 > β_1). Give β_1, β_2 for m=r=3.

Q2. THE CRUX. Can a choice of region + κ make the single two-block sjSector cover the whole P-box (so that
    the box integral closes via a finite sector cover), OR does the codim-2 stratum force a genuinely
    DIFFERENT estimate? Consider: (a) fixed κ — fails on codim-2 (σ_{r−1}→0); (b) varying κ=σ_{r−1}(P) —
    does the u-block weight κ²→0 then destroy the bound? Is there ANY single-two-block-sector cover that
    closes, or is a MULTI-COLLAPSE (q-block: q collapsing directions in the v-block, coupled) estimate
    forced on the codim-q≥2 strata? If forced, exhibit why (the q=2 coupled corner).

Q3. The corank-2 coupled estimate: on {σ₂,σ₃→0, σ₁≍1}, is the correct local model the SUM
    u₀²·U₀ + u₁²·U₁ (measure |u₀|³|u₁|²) giving threshold 7/2, versus treating the two collapsing
    directions as INDEPENDENT divisors (which gives min(4/2, 3/2)=3/2, an undershoot)? Confirm the coupled
    corner gives 7/2 and the independent split undershoots.

Q4. Measurability: is the codim-1 sector {σ_{r−1} ≥ κ} (and the corank-q cells) measurable via minor
    conditions {max over (r−q)×(r−q) minors of |det| ≥ κ'} (polynomial, Cauchy–Binet-equivalent to a
    singular-value band)? Any obstruction to a measurable rank-stratified cover?
</task>

<output_contract>
For each Q1-Q4: PROVEN/DERIVED exact statement (mark inference vs fact). β_1, β_2 for m=r=3. A clear
YES/NO on whether a single-two-block-sector region→cover closes the box (and if NO, the exhibited
codim-2 obstruction + the forced multi-collapse estimate). The 7/2-vs-3/2 coupled-vs-independent verdict.
Measurability yes/no.
</output_contract>

<grounding_rules>
Exact algebra (radial/Beta integration, Cauchy–Binet). MC only to guide. For g's scaling, integrate the
transverse block explicitly. Do NOT read my expectation into the answer — I have not said whether I think
the single sector covers; hunt for where it fails.
</grounding_rules>
