<task>
Lean 4 / Mathlib formalisation design review. I am formalising "Piece 3" (a boundary-0 pivot
peel) of Aoyagi's (S,J) resolution for deep-linear-network RLCT. I need the CLEANEST FAITHFUL
Lean design for one definition and one theorem, and a sharp verdict on whether the intended
target signature is honestly reachable or should change.

## Objects (real Lean signatures, DLNFibre repo, Mathlib v4.29)

- frobSq (M : Fin p -> Fin n -> R) : R := sum i, sum j, (M i j)^2.
- rmatMul (X : Fin p -> Fin n -> R) (Y : Fin n -> Fin q -> R) : Fin p -> Fin q -> R := fun i j => sum k, X i k * Y k j.
- matBox p n T : Set (Fin p -> Fin n -> R) := {X | forall i k, X i k in Icc (-T) T}  (a closed cube).
- Params M = layer-matrix tuples; paramsBoxM M 1 the entrywise [-1,1] box; prod M A the layer product.
- tailChain M : Fin (L+2) -> N := fun i => M i.succ (drop leading width M0, keep M1..M_L).
- redChain t M : Fin (L+2) -> N := Fin.cons t (fun i => M i.succ.succ) (install pivot t, drop M0,M1).
- minAdm M : N (Aoyagi's minimal admissible codim).

## Already PROVEN and banked (I reuse these, do not re-derive)

1. routeMLayerBoxIntegral_front_split:
   routeMLayerBoxIntegral M c' 1 = INT A' in paramsBoxM (tailChain M) 1, INT A0 in matBox (M 0) (M 1) 1,
        ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c')).
   So the box integral is (outer) over tail params A', (inner) over the FULL front factor A0 in its box,
   integrand frobSq(A0 . Q)^{-c'} with Q := prod (tailChain M) A' (an M1xn matrix).

2. pivotChartCover_lintegral_le_sum {m n} (t) (f : Matrix (Fin m) (Fin n) R -> ENNReal) :
   INT A in {A | t <= A.rank}, f A <= SUM rho : Fin t -> Fin m (embedding), SUM kappa : Fin t -> Fin n (embedding), INT A in pivotChart rho kappa, f A.
   pivotChart rho kappa := {A | IsUnit (A.submatrix rho kappa)} (the (rho,kappa) txt minor invertible).

3. schur_cov (A B C D) [Invertible A] : schurLeft A C * fromBlocks A B C D * schurRight A B = fromBlocks A 0 0 (D - C*Ainv*B). (det schurLeft = det schurRight = 1.)

4. measurePreserving_shearSub {alpha beta} [...] {K : alpha -> beta} (hK : Measurable K) :
   MeasurePreserving (fun p : alpha x beta => (p.1, p.2 - K p.1)) volume volume.
   (The block shear (x,D) |-> (x, D - K x) is measure-preserving; instantiated K = C.Ainv.B exposes Gamma = D - K.)

## The EXACT post-shear block identity (numerically verified to 1e-10, cross-coupled -- NOT a norm split)

Split columns of A0 (= rows of Q) into t pivot + (M1-t) non-pivot, rows of A0 into t pivot + (M0-t):
A0 = [[A,B],[C,D]], Q = [Q_p ; Q_b]. Then (pure block-multiply + substitute D = Gamma + C Ainv B):
    frobSq(A0.Q) = norm(A.Qtilde_p)^2 + norm(C.Qtilde_p + Gamma.Q_b)^2,   Qtilde_p := Q_p + AinvB.Q_b,   Gamma := D - C Ainv B.
The corank Gamma is CROSS-COUPLED with C.Qtilde_p (a prior design that used (norm(A.Qtilde_p)^2 + norm(Gamma.Q_b)^2) DROPPED
the C.Qtilde_p term and was WRONG -- do not reintroduce that error).

## The target (what I must deliver, sorry-free)

- Redefine gammaPeelIntegral M t c' : ENNReal to carry the TRUE integrand (Gamma an integration variable at
  UNSHIFTED exponent -c'; A,B,C also integration variables since they appear in the integrand).
- sjBoundaryPeel M c' (hc' : c' < minAdm M / 2) : EXISTS C != top, routeMLayerBoxIntegral M c' 1 <=
     SUM t in Finset.range (min (M 0) (M 1) + 1), C * gammaPeelIntegral M t c'.
  NO exponent shift, NO atom (those are the deferred finiteness lemma sjJointResolution : gammaPeelIntegral M t c' < top).
- Intended lemma schurShear_chart_lintegral: on a pivot chart, MP (shearSub) + schur_cov rewrite the
  per-chart integral so the integrand is the TRUE (norm(A.Qtilde_p)^2+norm(C.Qtilde_p+Gamma.Q_b)^2)^{-c'} (Jacobian 1).

## The two design problems I need adjudicated

(P1) CHART DEPENDENCE. The target sum is over t only, one gammaPeelIntegral M t c' per t, with C
absorbing the finite chart count. But a general chart (rho,kappa) selects an ARBITRARY t-subset of columns as
pivots, so after schur its Q_p / Q_b are the kappa-selected / complement ROWS of Q -- a row-PERMUTED Q, giving
a DIFFERENT integral per kappa. They are not all equal to a single canonical (first-t) gammaPeelIntegral. How
should gammaPeelIntegral M t c' be defined so the sum-over-t signature is honest? Options I see:
   (a) define it per-chart and change the signature to SUM over (t,rho,kappa);
   (b) canonicalize to the first-t chart and bound each (rho,kappa) chart by it via a frobSq-preserving
       row/col permutation MP argument (extra work -- is it worth it? is it even true, given Q is fixed?);
   (c) something cleaner.

(P2) THE t=0 TRIVIALITY. At t=0: A is 0x0, B is 0xM1, C is M0x0, Qtilde_p empty, so the integrand collapses to
frobSq(Gamma.Q)^{-c'} with Gamma ranging over matBox(M0)(M1) = the SAME box as A0. Hence
gammaPeelIntegral M 0 c' = routeMLayerBoxIntegral M c' 1 = box EXACTLY. So sjBoundaryPeel is TRIVIALLY
true with C=1 by dropping all t>=1 terms -- WITHOUT using the cover or schur at all. Is proving sjBoundaryPeel
via this t=0 identity an acceptable, faithful "plumbing" result (given gammaPeelIntegral's DEFINITION still
faithfully captures the peeled object for all t, and the real work is deferred to sjJointResolution finiteness)?
Or is it laundering / vacuous, such that I MUST route through the genuine cover+schur for t>=1 (and if so,
how, given (P1))?

## What I've established about soundness of the skeleton

sjJointResolution M t c' (hc' : c' < minAdm M / 2) : gammaPeelIntegral M t c' < top is claimed for ALL
t in 0..min. Since minAdm is the MIN over cuts of (M0-t)(M1-t)+minAdm(redChain t M), every t's own
threshold is >= minAdm M, so c' < minAdm M/2 is within every cut's threshold -- the per-t finiteness is
consistent. At t=0 it equals box < top (the goal itself). So the peel's t=0 term is circular-for-finiteness
but the t>=1 terms are genuine reductions; the deferred sorry absorbs all of them.
</task>

<output_contract>
Respond in EXACTLY these four sections, terse:

1. VERDICT on (P2): is the t=0-identity proof of sjBoundaryPeel faithful plumbing or laundering? One
   paragraph + a one-line recommendation (take t=0 route / must do genuine cover+schur).

2. VERDICT on (P1): the cleanest honest gammaPeelIntegral definition + whether the sum-over-t signature
   survives. If (a)/(b)/(c): say which, and give the definition shape in Lean-ish pseudocode (domains of
   A,B,C,Gamma,A'; is A over invertible matrices or the box; is it per-chart or canonical).

3. If you recommend the genuine cover+schur route: the 3-5 load-bearing sub-lemmas in dependency order,
   flagging which is the hardest (the matBox block-reindex-to-product MP? the permutation-to-canonical?),
   and a realistic reachability call (bounded plumbing vs a genuine multi-hundred-line wall) for a single tide.

4. The single biggest correctness trap in this construction (beyond the already-caught cross-coupling drop).

Do NOT write Lean tactic code. Design + reachability only.
</output_contract>

<grounding_rules>
Distinguish what you can DERIVE (the block identity, the t=0 collapse -- these are checkable algebra) from
what is a JUDGEMENT call (reachability, laundering-vs-faithful). Flag any step where you are guessing about
Mathlib API availability. If the t=0 collapse or the chart-dependence claim is WRONG, say so explicitly.
</grounding_rules>
