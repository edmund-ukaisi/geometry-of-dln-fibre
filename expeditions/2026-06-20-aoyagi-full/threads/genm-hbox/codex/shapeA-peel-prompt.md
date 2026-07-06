# Consult: is the Shape-A arity-descent peel for a box-integral finiteness buildable? Go/no-go on (2,2,2,2).

You are a decorrelated second model reviewing an analytic-formalisation design. Answer the concrete
question; do not defer to the framing. State a clear GO / NO-GO with the precise obstruction if NO-GO.

## The target (a pure box-integral finiteness — no RLCT machinery in the statement)

Fix a width vector `M = (M_0, M_1, ..., M_L)` of positive integers (L+1 widths, L matrices). Layer `s`
(0 ≤ s < L) is a real matrix `A^s` of size `M_s × M_{s+1}`. The product `P(A) = A^0 A^1 ... A^{L-1}` is
`M_0 × M_L`. `frobSq(P) = sum of squares of entries of P`.

TARGET (call it `hbox(M)`): for every real `c'` with `0 < c' < (1/2)·minAdm(M)`,
    I_M(c') := ∫_{A : all entries of every A^s in [-1,1]} frobSq(P(A))^{-c'} dA  <  ∞.

Here `minAdm(M)` is a known nonneg integer defined by a PROVEN layer-peeling recursion (call it minAdmRec):
- L=1 (two widths): minAdm(M_0,M_1) = M_0·M_1.
- L≥2: minAdm(M_0,...,M_L) = min_{0 ≤ t ≤ min(M_0,M_1)} [ (M_0 − t)(M_1 − t) + minAdm(t, M_2, ..., M_L) ].
The reduced chain `redChain t M = (t, M_2, ..., M_L)` has ONE FEWER matrix. (This recursion = the brute-force
`min over admissible strata of the Ext-codimension`; it is fully proven in Lean, `minAdmRec_eq_minAdm`.)

Examples (proven): minAdm(2,2,2)=3; minAdm(1,2,2)=2; minAdm(2,2,2,2)=3 (achieved at t=1 AND t=2).

## What is already BUILT (banked, sorry-free) and what is OPEN

BUILT: the L=2 base case `hbox((m,n,p))` for ALL m,n,p — via a reshape to the two-matrix box
∫_{A0 ∈ [-1,1]^{m×n}} ∫_{A1 ∈ [-1,1]^{n×p}} frobSq(A0·A1)^{-c'}, then a CORANK recursion on `min(m,n)`:
each step is either (cap-B) a radial-Δ pivot-minor cover of the front matrix — `mn` charts, chart =
(radial pivot axis |y|^{mn-1-2c'}, finite for c' < mn/2) × (angular residual, finite for c' < p/2, via a
Schur minor-pivot split `frobSq(R·S) ≍ c0·(‖row0‖² + ‖Sc·S_bot‖²)` + a Morse dominator) — with NO recursion;
or (cap-A) an interior carve recursing on the Schur complement `Sc` (an (m-1)×(n-1) core). This is a corank
recursion on ONE square factor.

OPEN: `hbox(M)` for general L. A prior de-risk proved the corank scaffold WALLS at L≥3 (its measure is the
corank of one square factor; the sum-threshold needs ≥2 boundaries).

## The proposed route (Shape A — arity-L weighted descent mirroring minAdmRec)

Induction on the ARITY L. Base L=2 = the built two-matrix corank recursion. Step: peel the FRONT matrix
`A^0` (M_0×M_1) by its rank `t`; on the pivot chart where a chosen t×t minor is invertible, a monomial
change-of-variables blows up the transverse `(M_0−t)(M_1−t)` directions (the Schur complement block),
producing a Jacobian monomial whose radial integral is finite iff the exponent stays below
`(1/2)(M_0−t)(M_1−t)`, times a REDUCED box integral for the chain `redChain t M = (t, M_2, ..., M_L)`
(one fewer matrix) at a SHIFTED exponent `c' − (M_0−t)(M_1−t)/2`. WellFounded on L; bottoms out at L=2.

The proposed induction statement is a WEIGHTED integral carrying the accumulated Jacobian monomial:
    I_σ(c') = ∫_{U_σ} w_σ(u)·F_σ(u)^{−c'} du,  per step  F_σ∘φ = m(u)²·F_τ(v)·U(u,v)  (a ≤ U ≤ b bounded),
    |Jac φ| ≤ C·n(u),  Tonelli ⟹  I_σ(c') ≤ C·(∏_new-vars ∫₀¹ t^{a−2c'b} dt)·I_τ(c').

## THE DECISIVE GO/NO-GO (please verify concretely, then rule on the general case)

On `M = (2,2,2,2)` (minAdm=3, so threshold c' < 3/2), take the front matrix `A^0` (2×2) and its t=1
rank stratum. Codim of the rank-≤1 locus of a 2×2 matrix is (2−1)(2−1)=1 (the determinant hypersurface).

Q1. Write `A^0 = [[a,b],[c,d]]`. In the chart a≠0, apply the shear/Schur split so that
`A^0 = L·diag(a, s)·R` with s = det(A^0)/a the Schur complement, L,R unipotent. The full product is then
`A^0·A^1·A^2`. Does `frobSq(A^0 A^1 A^2)` on this chart factor (after absorbing L,R into measure-preserving
coordinate changes on A^1) as a BOUNDED-UNIT multiple of a reduced-core `frobSq` for the (1,2,2) chain,
times the pivot/Schur monomial — i.e. does the identity
   frobSq(A^0 A^1 A^2) = m(u)²·frobSq(reduced (1,2,2)-product)·U,   a ≤ U ≤ b > 0
hold on the chart, with m the pivot·Schur monomial and the reduced product being that of `redChain 1 M =
(1,2,2)`? Show the concrete factorization or exhibit the obstruction. **Watch the coupling**: is the reduced
(1,2,2)-product's argument a FREE variable ranging over a box (so I_τ is genuinely `hbox((1,2,2))`), or is it
constrained/coupled to the pivot coordinates in a way that breaks the Tonelli split?

Q2. Does the exponent bookkeeping close: codim-1 monomial gives radial factor finite for c'−(shift) with
shift = 1/2, reduced (1,2,2) box needs c'−1/2 < (1/2)minAdm(1,2,2) = 1, i.e. c' < 3/2. ✓ arithmetic — but
does the ANALYTIC factorization actually deliver this, for BOTH achieving strata (t=1 and t=2), AND for the
non-achieving t=0? (Finiteness needs the WHOLE box covered — every t-chart finite for c' < 3/2, not just the
min-achieving one.)

Q3. The generalization risk (the real question): for a general chain, when the front factor `A^0` is WIDE
(M_0 < M_1) the rank-t stratification of a wide matrix, and the "reduced product is a free box variable"
claim, may fail — the reduced first matrix is `V·A^1` where V is a t×M_1 slice of A^0's factorization, and
`V·A^1` ranging over t×M_2 matrices is a PUSHFORWARD, not a uniform box. Does this break the Tonelli
recursion (the child integral is not literally `hbox(redChain t M)` over a box)? Is there a clean fix
(e.g. dominate the pushforward measure by a box measure with bounded density), or is this the obstruction
that forces the fuller Aoyagi (S,J) blow-up (Shape B)?

Q4. Overall verdict: is `hbox(M)` ∀-L a BOUNDED proof-engineering build (detail-at-scale, ~1000-2000 lines
of Lean given Mathlib's change-of-variables + the banked L=2 base + minAdmRec), or does some step hide a
genuine research obstruction (a monument to cite, not build)? If bounded, name the 2-3 load-bearing lemmas
and the single most likely failure point. If it hides a monument, name it precisely.

Be concrete and quantitative. Prefer exhibiting the (2,2,2,2) t=1 factorization explicitly (even a
schematic with the pivot/Schur/reduced blocks named) over generalities.
