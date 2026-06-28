<task>
We are formalizing in Lean 4 + Mathlib a linear-algebra structural fact about products of
real matrices. I want an INDEPENDENT determination of the cleanest mechanism and the cleanest
Lean-targetable statement. Do NOT assume my framing is correct; tell me what the right
mechanism actually is.

SETTING. Fix a layer-width tuple M = (M_0, M_1, ..., M_L) of positive naturals (L >= 2). For
each layer k in {0,...,L-1} a generic matrix A^k of shape (M_k x M_{k+1}). Define the FRONT
PRODUCT
    P = A^0 * A^1 * ... * A^{L-2}    (shape M_0 x M_{L-1}).
(The last layer A^{L-1} is NOT part of P.) Write m0 = M_0, m1 = M_{L-1}.

THE REGIME. We restrict to tuples in which the FRONT-WIDTH MINIMUM equals 1:
    min(M_0, M_1, ..., M_{L-1}) = 1.
Equivalently, at least one of the widths along the path M_0,...,M_{L-1} is exactly 1. This is
a verified property of a finite family of 34 concrete tuples we must cover (the "(1,1)
family"), with L in {2,3,4}. Within this family BOTH of the following occur:
  - cases where M_0 = 1 (so P is a single ROW, shape 1 x m1), and
  - cases where M_0 > 1 but some INNER width M_k = 1 (1 <= k <= L-1).

THE TARGET STRUCTURAL FACT. We want: every column of P is a scalar multiple of column 0 of P.
Concretely, there exist c0 : Fin m0 -> R (a vector) and mu : Fin m1 -> R (per-column scalars)
with
    P i j = mu j * c0 i    for all i, j,    and    c0 = column 0 of P    (so mu 0 = 1).
This feeds a downstream cancellation lemma that needs exactly the "rank-one columns" form plus
||c0||^2 != 0.

SUB-QUESTIONS (answer each decisively):
(1) MECHANISM. Is the right way to obtain "every column of P is a scalar multiple of column 0"
    (a) a LITERAL outer-product factorization P = U * V where U has shape (m0 x 1) and V has
        shape (1 x m1) -- i.e. P factors through a Fin 1 INNER dimension, obtained by
        associativity of the chain product split at a width-1 layer -- so columns of P =
        V-entry-scaled copies of the single column U, with NO rank theory at all; OR
    (b) a genuine rank argument (rank(P) <= 1 via rank(A*B) <= min(rank A, rank B), then
        "rank <= 1 ==> columns proportional")?
    Consider BOTH sub-cases (M_0 = 1 vs inner width-1) and say whether ONE uniform mechanism
    covers both, or whether they genuinely need different treatments. In particular: when M_0 = 1
    there may be NO inner width-1 layer -- does mechanism (a) still apply, and how (what are U, V)?
(2) THE SPLIT POINT. If (a): the chain A^0...A^{L-2} must be split at a position p* where the
    running width is 1. Over a path M_0,...,M_{L-1} with min = 1, what is the clean choice of p*
    (first index where M_{p*} = 1?), and does the factorization P = (A^0...A^{p*-1}) *
    (A^{p*}...A^{L-2}) always have left-factor with exactly 1 column and right-factor with
    exactly 1 row? Handle p* = 0 (the M_0 = 1 case) cleanly.
(3) LEAN STATEMENT + ROUTE (Mathlib v4.29). Give the cleanest Lean-targetable bridge lemma
    SIGNATURE for "P has rank-one columns" specialized to a product that factors through Fin 1,
    and the key Mathlib lemmas you would reach for (Matrix.mul over Fin 1, Matrix.mul_apply,
    Fin.sum_univ_one, associativity of a dependent-width chain product). Is the Fin-1
    factorization the cleanest Lean target, or is there something cleaner? Note the chain
    product here is a LEFT-associated dependent-width fold prod/prodAux over Fin (M_k) types
    (dependent widths), so associativity reassociation through a Fin 1 inner dim has cast
    overhead -- flag whether that's the real cost.
</task>

<output_contract>
- For (1): a DECISIVE verdict (a) or (b), with the reason, and an explicit statement of whether
  one uniform mechanism covers both sub-cases.
- For (2): the clean split-point choice and the shape claims, with the p*=0 corner handled.
- For (3): a concrete Lean lemma signature (pseudo-Lean is fine) + the Mathlib lemma names +
  an honest flag of where the cast/associativity cost lives.
- Mark anything you are INFERRING vs asserting as FACT.
</output_contract>

<grounding_rules>
- This is pure finite-dimensional linear algebra over R. No probability, no measure theory.
- "rank-one columns" means: all columns lie in the span of a single column (column 0). It does
  NOT require the matrix to be nonzero; but the downstream consumer additionally needs
  ||c0||^2 != 0 (col 0 nonzero), supplied separately off a pole.
- Be concrete about the Fin 1 inner dimension: a matrix product X * Y where Y : Matrix (Fin a)
  (Fin 1) R and Z : Matrix (Fin 1) (Fin b) R gives (Y*Z) i j = (Y i 0) * (Z 0 j), a literal
  outer product. State whether THIS is the load-bearing identity.
</grounding_rules>
