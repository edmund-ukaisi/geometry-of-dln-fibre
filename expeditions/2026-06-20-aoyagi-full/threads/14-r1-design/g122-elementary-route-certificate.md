# D1≥ (a)-split — ELEMENTARY route, no Mathlib-scale constant-rank (pp-hall, 2026-06-21, task #122)

**Controller's question (low-priority, D1 roadmapped meanwhile).** a114e07e found Mathlib v4.29 LACKS
the general constant-rank / Morse theorem that the #117 `LocalHomogeneousResidualSplitAt` (a)-split
requires → #119 became Mathlib-contribution-scale. Is the constant-rank theorem GENUINELY ESSENTIAL for
D1≥ at arbitrary `v`, or is there an ELEMENTARY family-specific route avoiding it? (Informs whether D1 is
cheaply revivable.)

**Verdict: ELEMENTARY ROUTE EXISTS. D1≥ is cheaply revivable — NOT gated on a Mathlib-scale constant-rank
build.** Two decorrelated legs converged (pp-hall exact L=2+L=3 + Codex xhigh).

## Why the general constant-rank theorem is NOT essential
The constant-rank theorem is needed when the ONLY datum is "the Jacobian has locally constant rank q" and
coordinates must be manufactured ABSTRACTLY. The DLN family supplies the coordinates EXPLICITLY:
1. **Gauge to a rank-r identity corner** (`block_elimination` #5 DONE for B; the per-layer version is
   `deepestPoint_exists`'s construction, also done — both are finite matrix factorizations, NO
   constant-rank). At the block-normal `v`, the regular block is the rank-r IDENTITY corner; its linear
   perturbation has IDENTITY (unit-diagonal) linear part; the residual core has NO linear part.
2. **Triangular unit-pivot elimination.** After the gauge, ordering the `q = Mval(t)` regular generators
   gives a TRIANGULAR system `g_i = u_i·z_i + h_i`, `u_i(0)=1` (unit pivot), `h_i` in already-controlled
   variables. Solve `z_i = −h_i/u_i` by DIVISION BY A UNIT (analytic, unit denominator), iterated. NO
   general implicit-function/constant-rank machinery — just unit-division + finite triangular induction.

Verified exactly: at the L=3 (2,2,2,2) intermediate fibre point `v∈S(1,0,0)` (the non-empty-core case
that the L=2 artifact would have hidden), solving the 2 regular generators gave explicit RATIONAL
functions with UNIT denominators (`w0+1`, `w0·w8+w0+w8+1`, both units near 0) — analytic, no general IFT
(`g122_L3_elementary.py`). And the block-normal `v` has identity-corner unit pivots making the linear
system triangular by construction (`g122_triangular_always.py`).

## The triangularity catch (the one place constant-rank could be forced — it isn't)
The general theorem's extra content over triangular elimination = the NON-triangular case (rank locally
constant but no separable triangular pivot system). **This does NOT arise for the DLN family:** the chain
product is MULTILINEAR ⟹ each chosen pivot variable occurs LINEARLY; the gauge supplies identity paths;
the regular generators can be ordered so each pivot has a unit coefficient. So the hard constant-rank case
never appears. (Both legs independently confirm this.)

## What Lean actually needs (much lighter than constant-rank)
- Local **unit-division** for analytic/smooth functions: `f(0)≠0 ⟹ 1/f` analytic/smooth locally; closure
  under product/composition/quotient-by-units.
- **Finite triangular induction** over the pivot-solve order.
- A 1-variable nonzero-derivative implicit/inverse-function step SUFFICES, but the explicit
  unit-denominator rational construction may avoid even that.
- Mathlib v4.29 plausibly has the smooth version (`HasFDerivAt` / inverse-function-theorem for invertible
  fderiv / `ContDiff`). Less certain it has a fully-packaged real-analytic implicit theorem — but the
  explicit unit-denominator construction sidesteps that. Proving "unit denominator ⟹ analytic local
  function" is MUCH lighter than proving general constant-rank.

## The ONE lemma to prove uniformly (the DLN-specific gauge/combinatorial fact)
> For every fibre point `v`, there is an explicit gauge + pivot order such that the `q` regular generators
> form a TRIANGULAR UNIT-PIVOT system.

Once this is in place, no fibre point forces the general constant-rank theorem. This lemma is the
block-normal-form gauge (block_elimination / deepestPoint_exists, done) + the identity-corner
triangularity (verified structural). It is a self-contained, provable rung — NOT Mathlib-scale.

## Net for the roadmap
- **D1≥ is cheaply revivable** via the elementary triangular route, off the Mathlib-scale constant-rank
  dependency. The re-scoped headline (rlctAt(deepest) = aoyagiLambda via L2+R1, no constant-rank) stands
  for now, but **D1's ⨅-over-fibre monotonicity does NOT require the Mathlib-scale build** the way #119's
  attempt assumed — it can use the gauge + triangular unit-pivot elimination + unit-division.
- **Recommendation:** if/when D1 is revived, build it on (gauge to identity corner + triangular
  unit-pivot elimination via unit-division), NOT the general constant-rank theorem. The `(a)`-split
  `LocalHomogeneousResidualSplitAt` is then a self-contained rung, not a Mathlib contribution.
- Honest scope: this rests on the gauge + identity-corner triangularity (verified L=2+L=3, structural
  argument for general). The DLN-specific gauge/pivot-order lemma is the thing to prove uniformly; it is
  in reach (block_elimination is done), not open math.

Decorrelation: pp-hall exact (4 scripts `g122-scripts/`: the GL-gauge route, the L=3 unit-denominator
solve, the triangular-unit-pivot characterization, the identity-corner-always-triangularizes argument) +
Codex xhigh (independent: ELEMENTARY route exists, same `g_i=u_i·z_i+h_i` triangular form, same
unit-division ingredient, same "multilinear ⟹ no non-triangular case", same "cheaply revivable").
Converged. Consult `codex/g122-elementary-route-{prompt,answer}.md`.
