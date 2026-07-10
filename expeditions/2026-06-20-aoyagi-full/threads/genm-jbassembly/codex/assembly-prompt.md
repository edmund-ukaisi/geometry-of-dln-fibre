<task>
You are a decorrelated design partner on a resolution-of-singularities / real-log-canonical-threshold
(RLCT) formalisation. I want your independent construction, not a rubber stamp. I will give you the
setup, a banked endpoint lemma, and two sharp sub-questions. Please DERIVE your own answer; I am
deliberately withholding my tentative conclusion.

## SETUP (deep linear network loss, Aoyagi's construction)

Widths M = (M_0, M_1, ..., M_L), a chain of matrices A_k : M_k x M_{k+1}, k=0..L-1. Box = every entry
in [-1,1]. Loss F(A) = frobSq(A_0 A_1 ... A_{L-1}) = squared Frobenius norm of the product (an
M_0 x M_L matrix). GOAL: prove the box integral ∫_box F(A)^{-c'} dA < ∞ for every c' < minAdm(M)/2,
where minAdm(M) is a combinatorial "minimum admissible codimension" = min over rank-flag branches T of
Mval(M,T), and Mval decomposes ADDITIVELY over the boundaries as a sum of per-boundary charges
(M_0-t_0)(M_1-t_0) + (t_0-t_1)(M_2-t_1) + ... . For example minAdm(3,3,3,4)=7 with a binding branch
T=(1,0,0) giving per-boundary charges [4,3,0], sum 7.

This is a genuine resolution-of-singularities problem: F vanishes to high order on the deep locus where
the product drops rank, and we resolve by iterated blow-ups to a normal-crossing/monomial form, then
apply the monomial integrability criterion.

## BANKED ENDPOINT (already proved in Lean, the target the construction must land on)

corner_block_lintegral: Let g : R^n -> R be measurable and degree-2-homogeneous (g(r·x) = r²·g(x)),
with a lower bound "a ≤ g(ω) for all ω on the unit sphere" for some constant a > 0. Then for every
c' < n/2:  ∫_{[-1,1]^n} g(z)^{-c'} dz < ∞.

Proof idea (single polar blow-up): z = r·ω, Jacobian r^{n-1}, loss r²·g(ω), so integrand
r^{n-1}·(r²·g(ω))^{-c'} ≤ a^{-c'}·r^{n-1-2c'}, radial-integrable iff n-1-2c' > -1 iff c' < n/2; sphere
has finite measure. This packages the whole corner (all n codimensions ADDING at one point) into ONE
polar coordinate. The caller must supply the joint block g of dimension n = minAdm, disjoint-sum shape,
with the uniform positive sphere lower bound.

## THE PIVOT PEEL (banked exact matrix identity)

On a chart where the top-left t×t block A of the front factor A_0 = [[A,B],[C,D]] is invertible ("the
pivot"), with the tail product Q = A_1...A_{L-1} split by rows into Q_p (pivot rows) and Q_b (rest):

  frobSq(A_0 · Q) = frobSq(A · Qtil_p) + frobSq(C · Qtil_p + Γ · Q_b),
  Qtil_p = Q_p + A⁻¹ B Q_b,  Γ = D − C A⁻¹ B  (the Schur complement = the corank block).

The bottom block is CROSS-COUPLED: it is C·Qtil_p + Γ·Q_b, NOT the clean Γ·Q_b. The corank block Γ has
dimension (M_0−t)(M_1−t) = the boundary-0 charge.

## WHAT A VERTICAL-SLICE COMPUTATION FOUND (on (3,3,3,4), t=1 pivot)

Writing the sheared layer-1 matrix A_1^# = U·A_1 (U unipotent, det 1) as rows [v ; W] (v = pivot row),
the loss becomes, exactly:
  F = a²·frobSq(v·A_2) + frobSq((C·v + Γ·W)·A_2).
Then the slice "drops the left det-1 unit L = [[1,0],[C/a, I]]" (since [[a·v];[C·v+Γ·W]] = L·[[a·v];[Γ·W]])
to obtain a DISJOINT model g = a²·frobSq(v·A_2) + frobSq(Γ·W·A_2), claimed to have the joint block (Γ, v)
of dimension 4+3 = 7 = minAdm, and fed to the endpoint.

## FACTS I HAVE ALREADY NOTICED (please account for these; do not just repeat them)

1. "Dropping L" is NOT frobSq-preserving pointwise: L is not orthogonal, so frobSq(L·X·A_2) ≠
   frobSq(X·A_2). A two-sided operator-norm domination frobSq(L·M) ≍ frobSq(M) needs ‖L‖,‖L⁻¹‖ bounded,
   but L = [[1,0],[C/a,I]] has entries C/a that blow up as the pivot a → 0.
2. In the disjoint model, the v-block core is a²·frobSq(v·A_2) — its coefficient a² → 0 as the pivot
   a → 0. So the endpoint's uniform sphere lower bound "a_const ≤ g(ω)" DEGRADES as the pivot value
   a → 0 (at the sphere point Γ=0, ‖v‖=1, g = a²·frobSq(v·A_2)).
3. The chart CoV Γ = D − C·a⁻¹·B maps the fixed box D∈[-1,1] to a SHIFTED, unbounded-as-a→0 domain for
   Γ, not a fixed cube [-1,1]^n. So "the joint block ranges over [-1,1]^n" is not automatic.
4. frobSq is degree-2-homog jointly in (Γ,v) but NOT in (a,v) together (a²frobSq(v) scales as r⁴ under
   (a,v)↦(ra,rv)); the pivot a and the corank/boundary blocks have different homogeneity weights.

## THE TWO SUB-QUESTIONS

### Q1 (the L-recursion structure)
Give the cleanest recursion over the L layers that lands ALL boundary charges into ONE joint block of
dimension minAdm fed to the single endpoint. Specifically:
  (a) Does the depth reduction frobSq(A_0 A_1 A_2) = frobSq(H·A_2) (collapsing the front two layers into
      one H) recurse cleanly, and what is the induction variable (chain arity L? rank-flag profile? total
      width)?
  (b) How do the per-boundary corank blocks Γ_0, Γ_1, ..., and the terminal boundary rows, combine into
      ONE disjoint-sum degree-2-homog g of dimension = Σ charges = minAdm — given the cross-coupling and
      the differing homogeneity weights (fact 4)? Is a single joint block even the right target, or should
      the recursion instead peel one boundary and hand a REDUCED chain to an inductive hypothesis (and if
      so, how is the "codimensions ADD / sum-not-min" coupling through the shared deep factor A_L
      preserved across the recursion — a naive Fubini split of corank-block × reduced-chain gives the
      WRONG "min" threshold, not the "sum")?

### Q2 (the pivot degradation, facts 1–3)
Is the disjoint-block reduction (dropping cross-terms, feeding a single fixed-cube joint block to the
endpoint) actually ACHIEVABLE width-general, given the pivot a→0 degradation? Concretely:
  (a) How is the pivot direction a (and its a² coefficient / the L-unit blow-up as a→0) handled so the
      endpoint's uniform sphere lower bound survives? Is a resolved as its own exceptional divisor
      (a radial blow-up of the pivot), or absorbed into a reduced-chain recursion, or something else?
  (b) Does the shifted/unbounded chart domain (fact 3) break the "[-1,1]^n cube" hypothesis of the
      endpoint, and if so what domain-control step fixes it (domination by a fixed ball? a different
      chart cover that keeps a bounded below)?

### Q3 (the deep-factor rank-drop branch)
The endpoint needs g(ω) ≥ a_const > 0 on the whole joint sphere. But g = Σ_j frobSq(X_j · A_L) VANISHES
at a sphere point when every resolved row/block X_j lands in the LEFT-kernel of the deep factor A_L
(i.e. A_L itself is rank-deficient, or the X_j all hit ker). How should this A_L-rank-drop locus be
routed? Is it a genuinely separate, deeper stratum of the resolution (a further corank in the flag) whose
own threshold is ≥ the next codimension (hence non-binding / dominated), and does that recursion
terminate? Or does it reopen the whole construction?

<output_contract>
Four sections, terse, construction-first (show the algebra / the recursion, not prose):
  Q1 — the L-recursion (state the induction variable + how boundary charges assemble into g; explicitly
       resolve whether it is one joint block or a reduced-chain recursion, and how "sum-not-min" survives).
  Q2 — the pivot handling (state exactly how a→0 is resolved; whether disjoint-block is achievable
       width-general or fails; the domain-control step).
  Q3 — the A_L-rank-drop branch (separate stratum? threshold bound? termination?).
  VERDICT — one paragraph: is a single-joint-block-to-the-endpoint route sound width-general, or does the
       right route peel boundary-by-boundary with a carefully-coupled inductive hypothesis? Name the
       single most likely failure mode.
Mark every INFERENCE vs every DERIVED FACT. If a step needs a determinant inverse in a Jacobian, flag it.
</output_contract>

<grounding_rules>
Reason from the setup + the banked endpoint + the facts given. This is exact real-algebraic /
measure-theoretic reasoning — no Monte Carlo. If you assert a threshold or a codimension, show the
arithmetic. Distinguish clearly what you can PROVE from what you conjecture. Do not assume the vertical
slice's "drop L" step is valid — adjudicate it.
</grounding_rules>
</task>
