<task>
Design the induction that CLOSES a finiteness proof, and identify the single hardest / genuinely-new
brick. Work independently; I have withheld my own proposed construction on purpose. If the construction
has a step that does NOT close, say exactly which.
</task>

<setup>
Chains M=(M0,...,ML) of positive ints. minAdm(M0,M1)=M0*M1; minAdm(M)=min_{0≤t≤min(M0,M1)}[(M0-t)(M1-t)+minAdm(t,M2,...,ML)].
Box integral Box(M,c')=∫_{[-1,1]^params} ‖A0·A1···A_{L-1}‖_F^{-2c'}. GOAL: Box(M,c')<∞ for all c'<minAdm(M)/2, by induction on arity.
A "boundary-0 peel" at cut t (via a pivot chart + Schur block-elimination + integrating out the corank
block Γ=(M0-t)×(M1-t)) reduces the step to finiteness of an OUTER integral of the per-chart residual
    R = det(Q_b Q_bᵀ)^{-(M0-t)/2} · (‖A·Q̃_p‖² + ‖C·Q̃_p·(I−P_{Q_b})‖²)^{-(c'-a/2)},   a=(M0-t)(M1-t),
over (A,B,C = the other front-factor blocks; A' = the tail params). Here Q=A1···A_{L-1} (M1×ML),
Q_b = its non-pivot (M1-t) rows, Q_p its pivot t rows, Q̃_p=Q_p+A⁻¹B·Q_b, P_{Q_b}=row-projection.
The factor det(Q_b Q_bᵀ)^{-(M0-t)/2} is a Gram determinant of rows of the tail PRODUCT.
</setup>

<facts_established>
1. VALUE is certified (3 methods + independent model + a cited RRR anchor): the RLCT of the resolved
   core equals ½·minAdm(M), realized as ½·min over rank-profiles t of the terminal-divisor exponent
   Mval(t) = (M1-t1)(M2-t1) + Σ_{j≥2}(t_{j-1}-t_j)(M_{j+1}-t_j); and EVERY admissible branch has
   Mval(t) ≥ minAdm (min attained at the binding branch). [verified exhaustively here]
2. A BLACK-BOX shorter-chain IH is INSUFFICIENT: at the binding cut minAdm(M)=a+minAdm(redChain t*),
   so the residual exponent (c'-a/2)→½minAdm(redChain) as c'→½minAdm(M) — the reduced-chain budget is
   fully consumed, leaving nothing for the Gram-determinant coupling factor; Hölder needs a conjugate
   r→1 (impossible). [verified 0/4000]
3. At L≥3 the Gram divisor {det(Q_b Q_bᵀ)=0} and the reduced-core divisor SHARE the deeper product
   Z=A2···A_{L-1}. At L=2 the tail is a single free matrix and they decouple.
4. A SHARING obstruction (exact, toric RLCT formula rlct(∑x^α)=min_{w>0}(Σw)/(min_α⟨w,α⟩)):
   ⟨δx,δy⟩ (=δ²x²+δ²y², one SHARED δ) has rlct=½, but ⟨δ1x,δ2y⟩ (SEPARATE δ1,δ2) has rlct=1 —
   identical "residual-width + per-row-weight" data, different value. So any invariant that records only
   thresholds/multiplicities (not WHICH exceptional variables are shared across generators) is
   insufficient at corank ≥ 2. Paradigm DLN binder: (3,3,4) t=(1,0), corank 2×2, coupled value 4,
   threshold-only 3.
</facts_established>

<the_questions>
Q1. STRENGTHEN THE INDUCTION. What is the strongest reasonably-clean inductive statement (a class of
   integrals, closed under the boundary-0 peel step, that specializes to Box) whose IH IS strong enough
   to absorb the Gram-determinant coupling factor — i.e. what auxiliary data must the inductive object
   carry beyond "a shorter chain + an exponent"? Give the object, the induction variable (and why it is
   well-founded / strictly decreasing), and the base case.
Q2. THE EXPONENT ACCOUNTING. Show precisely how, in your strengthened induction, the coupling factor's
   order is paid — i.e. why c'<½minAdm(M) keeps EVERY divisor/term strictly below threshold, recovering
   the budget the black-box Hölder route lost. Work the binding branch of M=(3,3,3,3) (charges [1,2,3],
   Mval=6) explicitly.
Q3. THE HARDEST BRICK. Which single step is genuinely NEW (not standard measure theory / not a banked
   change of variables) and is the place this could still fail to close as a clean formalization? In
   particular: how does your object handle the corank-≥2 sharing (fact 4) — does it CLOSE there, and if
   so by what mechanism (be concrete about how det(Q_b Q_bᵀ)^{-(M0-t)/2}, a Gram determinant of a matrix
   PRODUCT, gets resolved into something with a controlled order)?
</the_questions>

<grounding_rules>
- Distinguish PROVE / conjecture / heuristic. The value ½minAdm is not in question — the finiteness
  MECHANISM and its hardest formalization brick are.
- Prefer a construction that stays measure-theoretic (change of variables + Fubini + a monomial/Morse
  endpoint) if one exists; if the only sound route needs an algebraic-geometry resolution of
  singularities with symbolic divisor bookkeeping, say so and say why the measure-theoretic route fails.
- Do NOT assume my intended answer.
</grounding_rules>

<output_contract>
1. The strengthened inductive object + induction variable + base case (Q1).
2. The (3,3,3,3) binding-branch exponent accounting, explicit (Q2).
3. The single hardest/genuinely-new brick, and whether the corank-≥2 sharing CLOSES or is a residual
   gap — with the concrete mechanism resolving the Gram determinant of the product (Q3).
4. The one step most likely to be where a formalization stalls.
</output_contract>
