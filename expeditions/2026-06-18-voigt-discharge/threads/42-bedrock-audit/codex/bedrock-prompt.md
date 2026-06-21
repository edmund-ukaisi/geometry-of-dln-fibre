You are a decorrelated second-model reviewer (Codex) auditing a Lean 4 + Mathlib formalisation
capstone for BEDROCK + PRECISION (conceptual slop, not technical — the build is green and axiom-clean
already: only [propext, Classical.choice, Quot.sound]).

CONTEXT. The paper (Lehalleur–Rimányi 2024) studies fibres of matrix multiplication for deep linear
networks via type-A quiver orbits. The expedition discharged "Voigt's lemma" hVoigt: the GEOMETRIC
codimension of the orbit closure (rank locus) equals the EXPECTED (tangent-space) codimension =
dim Ext^1(M,M). This is a CODIMENSION equality — NOT the RLCT = ½·codim payoff (that is a separate
Cited analytic bound, Aoyagi/Watanabe, to live later in DLNFibre.DLN).

The two headline theorems, hypotheses [Field k] [IsAlgClosed k] [CharZero k]:

1. codimRep_orbitRankLocus_eq_orbitLinearCodim (M : Tuple d) :
     codimRep (canonicalCoord d) (orbitRankLocus M) = (orbitLinearCodim M : ℕ∞)
   Proof: squeeze varietyDim Z_M = finrank(range δ⁰) from A4 submersion bound (≤, char 0) and A6.1
   reverse inequality (≥, char-free), then cancel finite r from two additive identities
   codimRep + r = card  and  orbitLinearCodim + r = card.

2. codimRepCanonical_orbitRankLocus_eq_multSum_unconditional (L : List (Fin(N+1)×Fin(N+1))) :
     ((codimRepCanonical (orbitRankLocus (intervalDirectSum L))).toNat : ℤ)
       = Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}     (m = multiplicityArray L)

Definitions:
- orbitLinearCodim M := finrank C¹ − finrank(range δ⁰)   (the linear/tangent codim = dim Ext¹)
- codimRep coord Z := Ideal.height (vanishingIdeal (coord '' Z))   (geometric codim)
- varietyDim Z := (ringKrullDim (MvPoly ⧸ vanishingIdeal Z)).unbotD 0
- codimRepCanonical Z := codimRep (canonicalCoord d) Z

JUDGE these as a taste/precision reviewer (argue each):

(1) NAME = CONTENT. Does any name overclaim? Specifically: the recurring trap in this project is an
"rlct_…"-style name secretly claiming an unproved analytic interface. Here the discharge proves a
CODIMENSION equality. Does any name/docstring imply rlct or = ½·codim? Is "Voigt's lemma" the honest
name for codimRep = orbitLinearCodim? Is "unconditional" honest given [IsAlgClosed][CharZero] remain?

(2) HYPOTHESES. Is [CharZero k] load-bearing and honest? (A char-p counterexample is claimed to make
the geometric-codim reading FALSE in char p — via failure of differential-independence/separability in
the A4 submersion bound.) Is [IsAlgClosed k] genuinely needed (smooth point M3 / primeness L1 /
residue field = k)? Are these the weakest honest hypotheses, or is something decorative?

(3) THE .toNat COERCION. Headline 2 states ((codimRepCanonical …).toNat : ℤ) = Σ. codimRepCanonical is
ℕ∞-valued (Ideal.height). The .toNat sends ⊤ ↦ 0. Could this silently make the claim vacuously/wrongly
true at an edge case (e.g. if height were ⊤, or if the locus were empty / varietyDim = ⊥)? Is the RHS
Σ always the honest value, i.e. is the ℕ∞ height provably finite here so .toNat is lossless? Headline 1
is in ℕ∞ directly (no toNat) — is that the cleaner statement, and does headline 2 lose information?

(4) IS THIS THE RIGHT OBJECT / THE WAY? The squeeze proves varietyDim = finrank(range δ⁰), i.e. the
orbit closure is smooth of the expected dimension. Then L7 cancels r. Is cancelling a finite r in ℕ∞
sound (ℕ∞ is not cancellative at ⊤ — is r provably finite)? Is the capstone built so the RLCT payoff
can stand on it without reopening? Any subtle mis-scope: e.g. does codimRep at canonicalCoord truly
equal the geometric codimension, or is the coordinatisation-dependence a hidden gap?

Be terse, adversarial, concrete. Separate INFERENCE from FACT. Flag the single most important
bedrock/precision concern if any. Do not write code.
