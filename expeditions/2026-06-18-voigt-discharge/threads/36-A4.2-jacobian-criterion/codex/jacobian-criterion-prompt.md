<task>
I am de-risking one step of a char-0 algebraic-geometry / commutative-algebra argument and want an
independent, rigorous derivation. Please DERIVE the statements and proofs yourself; do not just cite a
textbook name — I need the precise hypotheses and the proof skeleton, because this is going to be
formalised in Lean/Mathlib.

SETTING (all over a field k of characteristic 0; later we may also assume k algebraically closed).
- B is a finitely-generated k-algebra that is a DOMAIN. Concretely B = a localization of a polynomial
  ring k[x_1,...,x_M] (so B is a smooth k-domain; Ω_{B/k} is a free B-module of rank M with basis dx_j,
  and the universal derivation is d, with d(b) recorded by the partials ∂b/∂x_j when b is a polynomial).
- f_1,...,f_n ∈ B. Let A = k[f_1,...,f_n] ⊆ B, the k-subalgebra they generate. A is a f.g. k-domain.
- The "Jacobian" is the n×M matrix J = (∂f_i/∂x_j) with entries in B (or in Frac(B)). Its "generic rank"
  is rank_{Frac(B)} J, i.e. the rank of J over the fraction field of B.

QUESTIONS (please answer each with a proof, flagging exactly where char 0 / separability is used):

Q1. State and PROVE the criterion
        trdeg_k(A) = generic rank of J   (= rank_{Frac B}(df_1,...,df_n) inside Ω_{B/k} ⊗_B Frac(B)).
    I specifically need the direction  trdeg_k(A) ≤ generic rank of J, and the full equality if it is
    not harder. Please make explicit:
      (a) the link "{f_i} algebraically independent over k ⟺ {df_i} linearly independent over Frac(B)",
          and where char 0 (perfect/separable) is essential vs. where it is automatic;
      (b) the role of Ω_{B/k} being free with basis dx_j, and how df_i = Σ_j (∂f_i/∂x_j) dx_j turns the
          differentials into the columns/rows of J;
      (c) whether trdeg = rank holds with equality or only ≤, and under what hypotheses each holds.

Q2. THE SOUNDNESS TRAP. The naive claim "trdeg_k k[f_1,...,f_n] ≤ rank of J at a SINGLE chosen k-point a"
    is FALSE: e.g. n=1, f_1 = x^2, at a=0 the Jacobian (2x) vanishes so pointwise rank 0, but trdeg=1.
    The GENERIC rank (over Frac B) is what equals trdeg, not the rank at an arbitrary special point.
    Now suppose additionally there is an algebraic-group action making things HOMOGENEOUS: a connected
    algebraic group G acts, the map is μ : G → V (an affine space), μ(Q·P) = Q • μ(P) where Q•(−) is a
    LINEAR automorphism of V, and we look at the differential dμ_P : T_P G → V.
      (i) Prove rigorously that rank(dμ_P) is INDEPENDENT of P (constant rank), purely from the
          homogeneity μ(QP)=Q•μ(P) and Q•(−) linear invertible. Where (if anywhere) is char 0 needed
          for THIS step, vs. where homogeneity alone suffices?
      (ii) Conclude that the GENERIC rank of the Jacobian of μ (= rank over Frac of the coordinate ring
           of G) equals the rank at the IDENTITY e, and that the rank at e = rank of the linear map
           dμ_e : Lie(G) = T_e G → V. Be precise about what "generic rank = rank at e" needs: do we need
           e to be a smooth point of G (G is a smooth group, so yes), and do we need char 0 / a
           generic-smoothness theorem to say "generic differential rank = dim image = trdeg"?
      (iii) Flag clearly: which of the two facts (trdeg = generic Jacobian rank) and (generic rank = rank
            at e by homogeneity) is the char-0-essential one, and which would hold in char p too.

Q3. FORMALISATION SIZING. If you were decomposing Q1+Q2 into the smallest set of independently-provable
    Mathlib lemmas (Mathlib has: Ω_{MvPolynomial}/kahler differentials with mvPolynomialBasis, pderiv,
    Algebra.trdeg as a Cardinal, IsTranscendenceBasis, AlgebraicIndependent, trdeg_add_eq tower,
    trdeg_le_of_injective, KaehlerDifferential.finite; it does NOT have any lemma connecting
    AlgebraicIndependent/trdeg with pderiv/Jacobian rank, nor "rank Ω_{L/k} = trdeg L" for field
    extensions): how many genuinely-distinct lemmas is this, what is the single hardest one, and does the
    "trdeg ≤ generic Jacobian rank" criterion SECRETLY require first proving the field-extension fact
    "dim_L Ω_{L/k} = trdeg_k L" (a structure theorem Mathlib lacks)? I want an honest answer on whether
    this is a 1-lemma job or whether it pulls in a chunk of differential-of-field-extensions theory.
</task>

<output_contract>
Four sections, in order, terse and proof-shaped (not prose essays):
  A1 — the criterion + proof of trdeg ≤ generic rank (and = if cheap), char-0 usage pinpointed.
  A2 — constant-rank lemma proof (i), the "generic rank = rank at e" conclusion (ii), and the
       char-0-essential-vs-homogeneity split (iii).
  A3 — lemma decomposition + honest count + the single hardest + the "does it secretly need rank Ω =
       trdeg for fields?" verdict.
  A4 — one-paragraph bottom line: is the trdeg ≤ rank δ⁰ bound sound as I've framed it, and what is the
       most likely thing that breaks a naive formalisation.
</output_contract>

<grounding_rules>
- Derive; do not hand-wave with "this is standard, see Hartshorne". I need the proof structure.
- When you assert a fact holds in char 0 but not char p, give the mechanism (separability / Frobenius),
  not just the label.
- Distinguish clearly: a fact you are PROVING vs. a fact you are ASSUMING from Mathlib's existing API.
- If any step I framed is actually FALSE or needs an extra hypothesis I omitted, say so explicitly.
</grounding_rules>
