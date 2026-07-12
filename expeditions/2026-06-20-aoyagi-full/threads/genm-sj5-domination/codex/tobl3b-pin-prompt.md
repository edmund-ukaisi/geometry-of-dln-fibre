<task>
Measure-theoretic / linear-algebra red-team of ONE change-of-variables lemma in an RLCT
(real-log-canonical-threshold) codimension proof for deep linear networks. NO Lean; exact analysis.

SETTING (a fully-worked anchor). A deep-linear-network loss integral, after a "front peel" at a
binding cut t* of a layer-width chain M=(3,3,3), reduces to an OFF-SECTOR integral of the form
(this is a LANDED, proven lemma; take it as given):

  I(Z) := ∫_{A ∈ box(b×M2)} ∫_{Γ ∈ sΓ (a×b)} ( w(Z) + ‖Ccross + Γ·(A·Z)‖_F^2 )^{-c'} dΓ dA
        ≤  Cresid · Wenn(Z) · w(Z)^{-(c' - ab/2)} ,     valid for FIXED full-rank Z,

with, at the anchor:  a=2, b=2, M2=3;  Z is the deeper product, an M2×n = 3×3 matrix ranging over a
box;  A (=A_cor) is a free b×M2 = 2×3 corank block;  Γ is the freed a×b = 2×2 corner;  Ccross is a
fixed 2×3 matrix;  w(Z)=‖Γ'·Z‖_F^2 is the "pivot energy" (Γ' a reduced front block);  and
  Wenn(Z) := ∫_{A ∈ box(2×3)} det( (A·Z)(A·Z)^T )^{-a/2} dA .

FACTS (established, take as given):
 F1. Wenn(Z) < ∞ for full-rank Z iff a < M2 - b + 1 (a "convergent regime"). At the anchor
     a=2, M2-b+1=2, so a = M2-b+1: BORDERLINE, Wenn is LOG-divergent even for full-rank Z; handled
     by a θ<1 interpolation (a separate, already-banked lemma).
 F2. sup over full-rank Z of Wenn(Z) = ∞: Wenn(Z) → ∞ as σ_min(Z) → 0. So the per-fixed-Z bound does
     NOT integrate over the OUTER Z-box uniformly. This is the sole remaining soundness surface.
 F3. minAdm is a QIP codimension: minAdm(3,3,3)=7; carrierThreshold(M)=½·minAdm(M)=7/2. The proof
     hypothesis is c' < 7/2. Deeper "reduced comparators" redChain(t,M)=(t,M2): minAdm(1,3)=3,
     minAdm(2,3)=6, minAdm(3,3)=9. A comparator on redChain(t*+j,M) is an admissible decoration
     whose finiteness for exponent < ½·minAdm(redChain(t*+j)) is GIVEN by an induction hypothesis
     (IH) on network depth/arity (arity of (2,3) < arity of (3,3,3)).
 F4. The proposed resolution of F2 is to STRATIFY the outer Z-box by SINGULAR-VALUE SHELLS of Z:
     shell j = {σ_{M2-j}(Z) ≥ ε_j > σ_{M2-j+1}(Z)}, j=0,…,r with r=min(a,b)=2 (saturating shell
     j=r lumps all ≥r small singular values). On shell j, PEEL AT THE DEEPER CUT t*+j: the freed
     corner shrinks to (a-j)×(b-j), and the residual is to be handed to the arity-(L+1) IH on the
     comparator redChain(t*+j,M). Charge C_j := (a-j)(b-j)+minAdm(redChain(t*+j,M)); verified
     C_j ≥ minAdm(M) for all j at all 3161 binding cuts swept (tight when t*+j is also binding).
     Anchor: C_0=4+3=7, C_1=1+6=7, C_2=0+9=9.
 F5. On shell j the elimination of the j WEAK singular directions of Z is done by a
     rank-revealing COORDINATE-MINOR chart: since σ_{M2-j}(Z) ≥ ε_j, Cauchy–Binet gives an
     (M2-j)×(M2-j) minor of Z with |det| ≥ ε_j^{M2-j} (up to a dimensional constant). This minor
     provides the change-of-variables Jacobian.

THE OWED LEMMA ("T-Obl3b", the one place a hidden non-uniformity could bite). For each shell j≥1:
   ∫_{Z ∈ shell_j} I(Z) dZ  is to be bounded by  [uniform const] · (comparator integrand on
   redChain(t*+j,M) at exponent c' - ½(a-j)(b-j)), which the IH then closes.

THE QUESTIONS (answer each, exact analysis; the anchor a=b=2, M2=3, j=1 is the worked case):

 Q1 (Jacobian uniformity / no hidden non-uniformity). Is the coordinate-minor CoV Jacobian on
    shell j UNIFORMLY bounded above AND below on the shell interior by constants depending on ε_j
    but NOT on the weak singular values (σ_{M2-j+1},…,σ_{M2}) which → 0? Or is there a shell-interior
    point (or a shell-boundary approach) where the Jacobian degenerates or blows up in a way that
    depends on the vanishing weak σ's? State the exact ε_j-scaling of the Jacobian.

 Q2 (the reduced weight after the CoV). After eliminating the j weak directions via the minor, the
    leftover det-Gram weight is over (b-j) rows in the (M2-j)-strong subspace with exponent (a-j)/2.
    Is this reduced weight FINITE (convergent), and under what condition? Compare to the shell-0
    condition a < M2-b+1. Does the shell-j (j≥1) reduced weight need its own θ-interpolation, or is
    it strictly convergent? Give the exact inequality.

 Q3 (residual identification: exact vs ≤). Is the leftover integrand after the shell-j peel + minor
    CoV EQUAL to the redChain(t*+j,M) comparator integrand, or only ≤ it (a domination)? Note a
    sibling result found that even at j=0 the corner-minimised base is a RATIONAL function of the
    deeper parameters (it carries a Gram-inverse projection) and is NOT literally the polynomial
    comparator loss, so the j=0 reduction is a DOMINATION (drop a nonneg residual + bound a Gram
    divisor by a constant), not an equality. Does the same hold at shells j≥1? Which is it — exact,
    or clean ≤?

 Q4 (adversarial). Try to BREAK the uniform constant: find a shell-interior Z (or a coupling with
    the pivot energy w(Z)=‖Γ'Z‖^2, which ALSO degenerates as Z drops rank) where either the const
    diverges, the residual fails to be dominated by the deeper comparator, or a ≥r-small-singular-
    value degeneracy escapes the saturating shell j=r. If you find one, that is the real obstruction
    — report it loudly. If none, say so.
</task>

<output_contract>
Answer Q1–Q4 in order, each ≤ 12 lines, exact inequalities where relevant. Lead each with a
one-word verdict: Q1 {UNIFORM | NON-UNIFORM}, Q2 {STRICTLY-CONVERGENT | NEEDS-θ | DIVERGENT} + the
inequality, Q3 {EXACT | DOMINATION}, Q4 {NO-BREAK | BREAK: …}. End with one line: does T-Obl3b
close as LABOUR for c' < 7/2, or is there a genuine obstruction?
</output_contract>

<grounding_rules>
Treat F1–F5 as established facts. Do NOT re-derive minAdm. Distinguish what you PROVE (exact
inequality/algebra) from what you INFER/expect; flag inference explicitly. Do not assume my intended
answer — I have deliberately withheld my conclusions. If a question is under-determined by the facts
given, say what extra fact would settle it rather than guessing.
</grounding_rules>
