<task>
You are adjudicating a Lean-formalisation design question about a CARRIED LOOP INVARIANT
in an inductive proof of finiteness of a family of integrals. NO Lean; pure math/logic.

SETUP (a recursion over "arity" L = chain length).
- A "chain" is a tuple M = (M_0, M_1, ..., M_L) of positive integers (matrix dimensions).
  "width-2" = L=1 (one matrix layer); "width-3" = L=2 (two layers A_1, A_2), etc.
- A "decoration" D over M carries: an exceptional-coordinate count d >= 0; a deeper
  parameter space Z which is measure-isomorphic to Params(M) = the tuple of layer matrices
  (A_1,...,A_L); a chart domain dom subset Z equal (via the iso e) to the box [-1,1] on all
  layer entries; a carrier with generators indexed by iota, each generator i having a
  "residual" res_i(z) = a linear form in active variables, and a monomial "support"
  supp : iota -> Fin d -> N.
- An admissibility predicate `adm` is a loop invariant CARRIED at every arity, CONSUMED at
  the width-2 base (call this step #4), and PRESERVED across one peel L -> L-1 (step #5).
  The peel #5 reduces M=(M0,M1,M2,...,M_L) to a reduced chain (t, M2,...,M_L) with ONE fewer
  layer; well-founded on arity, bottoms out at width-2.

THE d>=1 DISJUNCT of `adm` (call it gamma') currently (in a prior "fixed-Z" version) reads,
for some a, n, Dt in N and a FIXED matrix Z : Matrix (Fin n) (Fin Dt):
  exists a n Dt (Z : Matrix (Fin n)(Fin Dt)) (c : R)
    (eGamma : Z_space ~= (Fin a -> Fin n -> R))          -- SINGLE free block, all of Z_space
    (rho : iota ~= Fin a x Fin Dt),
      0 < c  AND  (Z * Z^T - c . I).PosSemidef            -- (*) "UNITS BOUND"
      AND MeasurePreserving eGamma AND dom = eGamma^{-1}(box)
      AND minAdm(M) <= a*n
      AND forall z i, res_i(z) = (eGamma z * Z)_{rho i}    -- provenance, FIXED Z

KNOWN FACTS (established elsewhere, take as given):
1. A separate #5 soundness cert fixed a CARRIABILITY CRITERION: "a clause may be carried in
   the loop invariant `adm` IFF it is z-INDEPENDENT, i.e. holds on ALL of dom (it is a
   structural/combinatorial/arithmetic property of supp, dims, jac, or the fixed parametrizing
   iso, NOT a pointwise fact that can fail at some z in dom)." adm must hold on the WHOLE domain.
2. The "fixed-Z" gamma' above is UNPRESERVABLE across a peel at intermediate arity, for two
   reasons: (i) a SINGLE free block eGamma onto (Fin a -> Fin n -> R) forgets the tail layers
   (Params(M) has >=2 layers at intermediate arity); (ii) a FIXED matrix Z cannot equal the
   deeper product A_2...A_L, which is MULTILINEAR (varies with z). The agreed fix is a
   Gamma x R SPLIT: eGamma : Z_space ~= (Fin a -> Fin n -> R) x R, with a z-dependent tail
   family Z_tail : R -> Matrix (Fin n)(Fin Dt), and provenance res_i(z) = (Gamma(z) * Z_tail(r))_{rho i}
   where (Gamma(z), r) = eGamma z.
3. At the width-2 base the tail is EMPTY: the reduced tail product is the identity, so
   R = Unit and Z_tail = I (the n x n identity), Dt = n.
4. The tail family Z_tail : R -> Matrix ranges over a box in R (the reduced layer params),
   which INCLUDES r = 0 (the box is centred at 0), giving Z_tail(0) = 0 (the zero matrix),
   and more generally rank-deficient members; this rank-deficient sublocus lies INSIDE dom.
5. #5 (the peel) operates by a SECTOR COVER: it restricts to a units sector
   {sigma_min(Z_tail) >= eps} where a Rayleigh bound c.||Gamma||^2 <= ||Gamma Z_tail||^2 holds
   (an eigenvalue-free "units bridge" lemma supplies exists c>0 with Z_tail Z_tail^T >= c.I from
   full-row-rank of Z_tail); the complement {sigma_min < eps} RECURSES as a deeper stratum.

THE QUESTION I want your INDEPENDENT verdict on (do not assume my preferred answer):

(a) UNITS-DROP SOUNDNESS. Under the Gamma x R split, should the UNITS BOUND (*)
    "0 < c AND (Z_tail(r) Z_tail(r)^T - c.I).PosSemidef" be CARRIED in the loop invariant adm
    (quantified how? for the fixed base c? for all r?), or DROPPED entirely from the carried
    invariant? If dropped, is it sound for (A) step #4 to DERIVE it at the width-2 base, and
    (B) step #5 to RE-SUPPLY it per-peel on the units sector? Reason from FACT 1 (carriability
    criterion) and FACTS 3-5. Identify any subtle unsoundness in dropping it OR in keeping it.

(b) WIDTH-3 WITNESS. Consider M = (2,2,2) (width-3, intermediate arity), minAdm(2,2,2)=3,
    binding cut t*=1 so the corank widths a_cut=b_cut=1 (both nonzero, so the d>=1 gamma' disjunct
    is genuinely REQUIRED, not the a=0-or-b=0 escape). Proposed concrete witness of the
    UNITS-DROPPED gamma' (all data exact):
      - d = 1; iota = nu = Fin 2 x Fin 2 (4 generators = 4 product-entry slots);
      - carrier.supp i 0 = 1 for ALL i (uniform support = 1);  carrier.coeff () i v = [v = i];
      - jac 0 = 3;
      - Z_space = Params(2,2,2) = Matrix(2,2) x Matrix(2,2) (layers A_1, A_2), e = identity,
        dom = box; ctx z = ((), entries of (A_1 A_2)); so res_i(z) = (A_1 A_2)_i.
      - gamma' data: a=2, n=2, Dt=2; eGamma(A_1,A_2) = (A_1 as (Fin2->Fin2->R), A_2);
        R = Matrix(2,2); Z_tail(r) = r; rho = identity : Fin2xFin2 ~= Fin2xFin2.
    Independently CHECK each carried clause on this witness and say whether it inhabits the
    units-dropped gamma' at intermediate arity:
      - provenance: res_i(z) =? (rmatMul (Gamma z) (Z_tail r))_{rho i}, rmatMul X Y i j = sum_k X i k Y k j;
      - minAdm(M) <= a*n;
      - alpha: exists i0 with supp i0 <= supp j at every divisor (pSimultaneous);
      - delta-0: supp uniform (supp i l = sharedDivisorExp l for all i,l);
      - beta: minAdm(M)/2 <= monomialThreshold, where for d=1 monomialThreshold = axisRatio(jac 0, k 0)
        with k 0 = sharedDivisorExp 0, and axisRatio(h,k) = (h+1)/(2k);
      - would the UNITS BOUND (*) hold on this witness for-all r in the R-box? (Check r=0.)
    Flag any clause that FAILS, any hidden vacuity, or any reason this is not a legitimate
    intermediate-arity inhabitant.
</task>

<output_contract>
Two sections, (a) and (b), matching the questions. In (a): give a single verdict
CARRY-(how) / DROP, then the soundness of derive-at-base + re-supply-per-peel, then any
subtlety. In (b): a per-clause PASS/FAIL table with the one-line exact-arithmetic reason for
each, then a single verdict INHABITED / VACUOUS / ILL-FORMED. Be terse. Flag inference vs
checkable fact.
</output_contract>

<grounding_rules>
State explicitly which of your conclusions are DERIVED from the given facts/arithmetic
(checkable) vs your own INFERENCE/opinion. Do not invent Lean lemma names. If a clause check
needs an assumption not given, say so rather than guessing. You may disagree with the proposed
resolution; if you think the units bound MUST be carried, say so loudly and give the exact
failure mode of dropping it.
</grounding_rules>
