<task>
Commutative-algebra / algebraic-geometry adjudication (exact, characteristic 0, algebraically
closed field k). We need an INDEPENDENT verdict + a clean proof mechanism on one sharp question
arising in a Lean 4 + Mathlib formalisation of Lehalleur–Rimányi "Geometry of the fibers of the
multiplication map of deep linear networks."

## The object

Fix integers d_0, d_1, ..., d_N ≥ 1 (a dimension vector, N ≥ 1 factors). The representation space is
  Rep = { (A_1, ..., A_N) : A_i ∈ Mat_{d_i × d_{i-1}}(k) },  with coordinate ring
  P = k[ entries of all A_i ]   (a polynomial ring; "factor entries").
The multiplication map is
  mult(A_1,...,A_N) = A_N · A_{N-1} · ... · A_1  ∈ Mat_{d_N × d_0}(k).
Each entry of mult is a polynomial of degree N in the factor-entry variables.

Fix a target matrix E ∈ Mat_{d_N × d_0}(k) of rank exactly r (the "endpoint normal form": in the
intended use E = the r×r-pivot normal form, e.g. for d_N = d_0 = 2, r = 1, E = diag(1,0); but treat
general E of rank r). The FIBRE IDEAL is
  I_E := ( mult(A) − E )  ⊆ P     (the d_N·d_0 entry-equations  (A_N···A_1)_{ij} − E_{ij} = 0 ),
and the FIBRE RING is
  F_E := P / I_E   =  k[A_1,...,A_N] / (mult(A) − E).
Scheme-theoretically F_E = O(mult^{-1}(E)) with its NATURAL (possibly non-reduced) structure.

## THE QUESTION (the single load-bearing truth-value)

  Is the ideal I_E RADICAL?  Equivalently, is the scheme-theoretic fibre  mult^{-1}(E)  REDUCED?

This is load-bearing because a downstream "trivialization" S ≅ R ⊗_k F_E (R a regular base ring,
the localized rank-≤r chart) is being identified with a REDUCED chart ring (built as a vanishing
ideal / radical); if F_E is non-reduced the identification has a hole.

We want: (1) a verdict — radical / not radical — stated at its TRUE scope (for which (N, d_•, r, E)
does it hold? does it need E of full rank r? generic E? a smoothness hypothesis?); (2) the cleanest
PROOF MECHANISM (a named criterion: orbit/homogeneous-space structure, Jacobian/smoothness, a
flatness/CI argument, generic-smoothness + no-embedded-primes, etc.) — ideally one that is
"formalisation-friendly" (reduces to a finite exact check or a clean structural theorem rather than
a global primary decomposition); (3) the failure modes — where (if anywhere) does I_E acquire
nilpotents or embedded primes?

## Facts already established (exact, by us)

- Anchor (N=2, d=(2,2,2), r=1, E=diag(1,0)): I = ( (A_2 A_1) − diag(1,0) ), 4 equations in 8 vars.
  Singular `primdecGTZ` + `radical` over QQ returns:
    * I IS radical (radical(I) ⊆ I confirmed by GB reduction).
    * dim I = 4 (codim 4 in the 8-dim Rep); 2 primary components, BOTH dim 4, BOTH with
      primary = associated prime (no embedded / no nilpotent primes).
    * The two primes: P_1 = {second ROW of A_2 = 0, ...}, P_2 = {second COLUMN of A_1 = 0, ...};
      i.e. the two ways the rank-1 product factors through a 1-dim space. They meet in a dim-3 locus.
  - The variety is SINGULAR at the point A_1 = A_2 = diag(1,0): the Jacobian of the 4 equations
    drops from rank 4 (generic) to rank 3 there. (Singular variety, but the anchor ideal is still
    radical — the singularity is the crossing of the 2 components, not non-reducedness.)

- Context: mult is degree N in the factor entries (NOT linear), so the equations are genuinely
  high-degree; the fibre is NOT a complete intersection in general (codim 4 here is cut by 4
  equations, so the anchor happens to be a set-theoretic complete intersection of the right codim,
  but for larger N / d the equation count d_N·d_0 may exceed the codim).

## What we want from YOU

A fresh, independent derivation. Two distinct angles we want you to weigh:
  (A) The fibre mult^{-1}(E) as a quotient / orbit space: the group  G = GL_{d_1} × ... × GL_{d_{N-1}}
      (change of basis in the INTERMEDIATE spaces) acts on Rep preserving mult; for E of rank r the
      fibre may be a homogeneous space or a finite union of orbit-closures. Does an
      orbit / homogeneous-space structure (each component an orbit closure of a reductive group)
      give reducedness, and under what hypotheses?
  (B) A direct smoothness / generic-reducedness argument: is mult^{-1}(E) generically smooth on each
      component (hence generically reduced), and does it have no embedded primes (e.g. because it is
      Cohen–Macaulay / equidimensional)? generically-reduced + no-embedded-primes ⟹ reduced.

Be explicit about whether the answer DEPENDS on E being exactly rank r / on the pivot normal form, on
char 0, on N, or holds in full generality. If there is a known reference (e.g. fibres of matrix
multiplication, quiver-variety / type-A orbit structure, determinantal varieties being reduced/CM),
name it.

<output_contract>
Five sections, terse, object-level (no preamble, no pep talk):

1. VERDICT: radical / not radical / radical-only-under-hypotheses-X. One line, then 2–4 sentences
   stating the TRUE scope (which N, d_•, r, E).

2. MECHANISM: the single cleanest proof that I_E is radical (or the precise nilpotent witness if not).
   Name the criterion. Say which of angle (A) orbit-structure or (B) smoothness+no-embedded is the
   load-bearing one, and why.

3. THE COMPONENTS (general N, d_•, r): what are the irreducible components of mult^{-1}(E), how many,
   what is the geometric description (the anchor's "2 components = 2 factorization patterns" — does it
   generalize to a count, e.g. by where rank drops along the chain)? Is the fibre equidimensional?

4. FORMALISATION-FRIENDLY HANDLE: if radical, the structural theorem a prover could target that does
   NOT require computing a primary decomposition — e.g. "F_E is a tensor/product of reduced pieces",
   "mult^{-1}(E) is a fibre bundle over a flag/Grassmann locus with reduced fibre", "the cut ideal is
   prime after a further localization on the open chart where pivot ≠ 0". Be concrete.

5. THE FAILURE MODE / ONE CAVEAT: where (if anywhere) does this break — a larger d / N / smaller-rank
   E where I_E is non-reduced, or where our framing is most likely wrong.
</output_contract>

<grounding_rules>
- Distinguish FACT (provable / standard theorem you can name) from CONJECTURE (your inference).
  Label inferences as such.
- Do not assume our anchor computation generalizes — derive the general case yourself; if you think
  it does NOT generalize, say so and give the smallest counterexample to check.
- Exact algebra only. Numerics/Monte-Carlo are not a proof.
</grounding_rules>
</task>
