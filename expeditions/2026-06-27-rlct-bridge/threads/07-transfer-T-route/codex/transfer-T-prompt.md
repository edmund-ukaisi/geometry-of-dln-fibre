<task>
I am adjudicating whether one specific statement ("T") is provable inside Lean 4 + Mathlib v4.29
(pin: lean-toolchain v4.29.0, Mathlib v4.29.0) with a bounded effort, or whether it must be left as
an explicitly-cited external fact. I want your INDEPENDENT proof-route analysis. Do NOT rubber-stamp;
construct the route yourself from scratch.

## The mathematical setup (exact)

Fix N ≥ 1 and a dimension vector d : Fin(N+1) → ℕ. A "tuple" is A = (A_1,…,A_N) with A_i a
(d_i × d_{i-1}) matrix over a field. The multiplication map is mult(A) = A_N ⋯ A_1, a (d_N × d_0)
matrix. For a target matrix B (rank r ≤ min(d_0,d_N)), the FIBRE is
  fibre(k, d, B) = { A : tuple over k | mult(A) = B } ⊆ (affine space of all entries).
The ambient affine space has `card` = Σ_i d_i·d_{i-1} coordinates (one per matrix entry); `card` is
the SAME integer regardless of the field.

The "geometric codimension" of a subset Z of this affine space is defined as
  codim(k, Z) := Ideal.height (vanishingIdeal_k (image of Z in coordinate space))
i.e. the Krull height of the vanishing ideal of Z's Zariski closure in the polynomial ring
MvPolynomial (coords) k.

Now fix:
- ℝ (the real field),
- K a field with [Field K] [IsAlgClosed K] [CharZero K] (think: the algebraic closure of ℝ, i.e. ℂ),
- ι : ℝ →+* K the inclusion ring hom,
- B a rank-r real matrix; B.map ι is the same matrix viewed over K.

## The statement T (exact)

  T :  codim(ℝ, fibre(ℝ, d, B))  =  codim(K, fibre(K, d, B.map ι)).

In words: the geometric codimension of the REAL fibre (height of its real vanishing ideal) equals the
geometric codimension of the COMPLEX fibre (height of its complex vanishing ideal). The fibre over K
is the base-change of the fibre over ℝ along ι.

## Facts I have ESTABLISHED (you may rely on these; they are proved or in Mathlib v4.29)

F1. There is a proven, FIELD-GENERIC catenary identity in the codebase:
    for any field k and any nonempty subset Z of the affine space whose closure is the variety,
      codim(k, Z) + varietyDim(k, closure of Z) = card,
    where varietyDim(k, W) = Krull dimension of MvPolynomial(coords) k ⧸ vanishingIdeal_k(W).
    This rests only on: MvPolynomial over a field is catenary / has Krull dim = card, the per-prime
    catenary `height p + dim(R⧸p) = card`, and a chain squeeze. NO algebraic-closedness needed; it
    holds verbatim over ℝ and over K. (So codim and varietyDim are dual: codim = card − dim.)

F2. The entire computation that gives codim(K, fibre(K,d,B')) = C + δ (a concrete combinatorial
    integer; C = a quadratic form on a Kostant partition, δ = r(d_N+d_0−r)) is proven ONLY over an
    algebraically closed field K of char 0. It uses generic smoothness of finitely-presented domains
    over a perfect/alg-closed field (`Scheme.Hom.dense_smoothLocus_of_perfectField`), orbit-closure /
    quiver machinery, Nullstellensatz (vanishingIdeal is radical needs alg-closed), etc. NONE of this
    is available over ℝ.

F3. There is a distinguished RATIONAL point in each top-dimensional minimising component of the
    rank-locus: the "realizer" is a direct sum of 0/1 interval blocks (all entries 0 or 1), hence
    defined over ℚ ⊆ ℝ ⊆ K. It realises the target rank r. (So the real fibre is nonempty whenever the
    complex one is, and the real points are not empty.)

F4. Mathlib v4.29 INVENTORY (I have grepped the pinned tree):
    - HAS: `trdeg R A` (transcendence degree), `IsTranscendenceBasis`, `AlgebraicIndependent` +
      `restrictScalars`/`extendScalars` (algebraic independence under field extension), the catenary
      identity `height p + ringKrullDim(R⧸p) = card`, `MvPolynomial.ringKrullDim_of_isNoetherianRing`,
      `ringKrullDim_quotient_comap_ringEquiv`, `RingEquiv.height_comap`.
    - DOES NOT HAVE (confirmed absent at this pin): any `ringKrullDim` base-change / tensor-product
      lemma; any `height` base-change under a field extension; any theorem `ringKrullDim = trdeg` for
      a finitely-generated algebra (the algebraic-geometry "dimension theorem"); any semialgebraic
      dimension theory; any real Nullstellensatz; any `vanishingIdeal` base-change lemma.

## What I want from you (output contract)

1. CONSTRUCT the most elementary viable proof route for T inside Lean+Mathlib v4.29, OR argue it is
   out of reach at this pin. Adjudicate concretely among (and beyond) these candidate routes:
   (a) reduce T to a statement about Krull dimension / transcendence degree, then pin the relevant
       quantity equal across ℝ and K using a field-independent invariant;
   (b) a direct chain-of-primes argument in the two polynomial rings, exploiting the explicit rational
       realizer point;
   (c) base-change the vanishing ideal / its height directly along ι via comap/map.
   For each, say precisely WHICH step has no Mathlib lemma and would be a from-scratch build, and how
   large that build is (one lemma? a multi-file real-algebraic-geometry theory?).

2. The KEY subtlety to address head-on: is it even TRUE that the height of the REAL vanishing ideal of
   the real fibre equals the height of the COMPLEX vanishing ideal of the complex fibre? Real algebraic
   sets can have real dimension < complex dimension (e.g. x²+y²=0 over ℝ is a point, dim 0, but over ℂ
   is two lines, dim 1). Under what hypotheses on the real fibre does real-codim = complex-codim hold,
   and does the DLN fibre (with its rational realizer in every top component) satisfy them? Be exact
   about what is needed (a smooth real point of full local dimension in each top complex component?
   Zariski-density of real points? something weaker?).

3. FEASIBILITY VERDICT, one of:
   (i)   provable in a bounded Lean tide — give the explicit lemma ladder (each rung a named Mathlib
         lemma or a clearly-bounded new lemma);
   (ii)  needs a substantial real-algebraic-geometry build — scope it (what theory, roughly how big);
   (iii) genuinely beyond Mathlib v4.29 ⟹ T must stay an explicitly-cited external fact.

<grounding_rules>
- Work at the pin: Lean 4 / Mathlib v4.29. Do not assume lemmas that landed in later Mathlib.
- Distinguish FACT (a lemma you can name / a theorem you can state precisely) from INFERENCE (your
  expectation). Mark each.
- The x²+y²=0 phenomenon is the crux — engage it directly; do not assume real-dim = complex-dim.
- Be concrete about the realizer: it is a single rational point; a single rational point does not by
  itself pin the local dimension of a real algebraic set. Say what extra structure is needed.
- I am withholding my own tentative conclusion deliberately. Give me YOUR route and YOUR verdict.
</grounding_rules>
</task>
