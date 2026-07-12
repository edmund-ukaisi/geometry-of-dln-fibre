<task>
I am assembling a measure-theoretic finiteness proof (a decorated recursive integrability step).
I need a decorrelated adversarial check on ONE crux: a Z-uniformity / non-uniform-constant issue in
the final assembly. Judge whether the assembly CLOSES, and if so what the cleanest sound mechanism is,
or whether there is a genuine obstruction. Please reason from the objects; do not defer to me.

SETUP (all exact, no approximation).
- A "reduced comparator" integral, the induction hypothesis (IH), is FINITE:
    D'.integral(e) := ∫_{Z ∈ boxZ} ∫_{Γ' ∈ boxΓ'} ∫_{u} monomial(u) · frobSq(Γ' · Z)^{-e} < ∞
  for every exponent e < carrierThreshold(redChain) = (1/2)·minAdm(redChain). Here:
    * Z is the "deeper product": a matrix M₂ × m, itself = product of deeper layer-matrices ranging over a
      fixed bounded box (so rank(Z) ranges over 0..M₂; full rank M₂ is generic/open-dense).
    * Γ' is a t★ × M₂ free front block; w := frobSq(Γ'·Z) is the comparator loss (the pivot energy).
    * minAdm(·) is an integer "codimension budget"; it EXACTLY charges the codimension of the locus where
      prod(redChain) = Γ'·Z drops rank (including Z's own rank-drops), so D'.integral is finite over the
      FULL Z-box including near rank-drop loci of Z.
- The PARENT integral I must bound introduces a freed a×b corner Γ (integrated by a Gaussian lemma) and a
  FREE b×M₂ "corank block" A_cor. Let Q_b := A_cor · Z (b × m). I have LANDED, per-fixed-FULL-RANK-Z
  (rank Z = M₂) lemmas of the form:
    ∫_{A_cor ∈ box} ∫_{Γ} (w + ‖Ccross + Γ·Q_b‖²_F)^{-c'} dΓ dA_cor  ≤  C₁(Z) · w^{-(c' - shift)},
  where shift = (1/2)·a·b (or a θ-reduced (1/2)·θ·a·b at a "borderline"), and crucially
    C₁(Z) = Cresid · Wenn(Z),   Wenn(Z) := ∫_{A_cor ∈ box} det(Q_b Q_bᵀ)^{-a/2} dA_cor.
  Wenn(Z) is FINITE for full-rank Z when a < M₂ − b + 1, but Wenn(Z) → ∞ as σ_min(Z) → 0 (Z drops rank);
  there is NO finite sup over all full-rank Z. So the per-Z bound does not integrate over Z uniformly.
- BANKED exact combinatorial fact (verified 3161 cases, 0 exceptions), from a convexity of minAdm:
  define the "flag charge" C_j := (a−j)(b−j) + minAdm(redChain@(t★+j)), for j = 0..min(a,b), where
  redChain@(t★+j) is the reduced chain when j MORE pivot columns are absorbed (peel at the deeper cut
  t★+j; the freed corner shrinks to (a−j)×(b−j)). Then C_j ≥ C_0 = minAdm(M) for ALL j, TIGHT at j=0
  (binding identity minAdm(M) = ab + minAdm(redChain@t★)). Each redChain@(t★+j) is a chain ONE node shorter
  than M, so DecoratedBoxThresholdFinite for its comparators is given DIRECTLY by the IH.
- The target: prove the PARENT integral < ∞ for every c' < carrierThreshold(M) = (1/2)·minAdm(M).
- A prior thread already established a caution: a NAIVE "recurse into the rank-drop stratum {corank Z ≥ q+1}"
  is UNSOUND (it can miss 2nd-order degeneration points, e.g. Z = a·b scalar where σ_min = |ab| is 2nd
  order on the diagonal). The known-sound well-founded variable is chain-arity (network depth), decreasing.

QUESTIONS (answer each explicitly).
Q1. The Wenn(Z) non-uniformity. To integrate the per-Z parent bound over the Z-box, how should the Z-domain
    be decomposed so the bound integrates to something finite? Is a stratification by SINGULAR-VALUE SHELLS
    of Z — {σ_min ≥ ε} (all M₂ sv's ≥ ε) as shell 0, and {σ_{M₂-j+1} < ε ≤ σ_{M₂-j}} (exactly j small sv's)
    as shell j — the right decomposition? Is it FINITE (finitely many shells) and does each shell's
    contribution reduce to a comparator the IH closes?
Q2. On shell 0 {σ_min(Z) ≥ ε}: is Wenn(Z) UNIFORMLY bounded? I claim det(A_cor Z (A_cor Z)ᵀ) ≥ ε^{2b}·det(A_cor A_corᵀ)
    when ZZᵀ ⪰ ε²·I (PSD determinant monotonicity), hence Wenn(Z) ≤ ε^{-ab}·Wenn(I). Correct? Any hole?
Q3. On shell j (j small singular values of Z): is the correct move to peel at the DEEPER cut t★+j, so the
    freed corner is (a−j)×(b−j) [charge (1/2)(a−j)(b−j)] and the remainder is a comparator on redChain@(t★+j)
    at exponent c' − (1/2)(a−j)(b−j), which the IH closes because c' < carrierThreshold(M) ≤ (1/2)C_j gives
    c' − (1/2)(a−j)(b−j) < (1/2)minAdm(redChain@(t★+j)) = carrierThreshold(redChain@(t★+j))? Does the "charge
    add" (C_j ≥ minAdm(M)) genuinely make every shell close? Is there any j where it fails?
Q4. INFINITE REGRESS CHECK. On shell j the deeper comparator ALSO involves a freed (a−j)×(b−j) corner and its
    own corank block, hence its OWN Wenn-type factor at the deeper level. Does the argument recurse without
    termination (a hidden non-uniformity pushed one level down each time), or is it genuinely finite? What
    makes it bottom out? (Consider: the flag j is bounded by min(a,b); the deepest shell j=min(a,b) has a
    zero-width freed corner; the IH gives the deeper comparator's finiteness OUTRIGHT without re-stratifying.)
Q5. Is this Z-uniformity issue a genuine OBSTRUCTION (the charges don't add, or the regress doesn't
    terminate, or a degenerate Z is missed), or is it FORMALISATION LABOUR (sound mechanism, residual =
    the per-shell uniform-constant / adapted-chart measure assembly)? If labour, name the single place a
    hidden non-uniformity is most likely to actually bite.
</task>

<output_contract>
Answer Q1–Q5 in order, each 3–8 sentences. For Q2 give an explicit yes/no on the determinant-monotonicity
bound with any correction. For Q5 give a one-line verdict: OBSTRUCTION or LABOUR, and if LABOUR the single
riskiest spot. Be concrete and adversarial; if any step is wrong, say exactly where. Do not restate the
setup back to me.
</output_contract>

<grounding_rules>
Reason from the stated objects and exact algebra. If you need a fact I did not state, state the assumption
you are making. Distinguish what you can prove from what you conjecture. Exact rationals / codimension
counts, not floats.
</grounding_rules>
