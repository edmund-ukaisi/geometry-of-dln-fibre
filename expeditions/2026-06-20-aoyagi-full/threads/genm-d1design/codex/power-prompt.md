<task>
Derive the exact per-stratum change-of-variables (blow-up chart + Jacobian + exponents) for ONE integral
arising in a Lean formalisation (Lehalleur–Rimanyi DLN). I withhold my tentative view. WITHHOLD nothing.

SETUP. `frobSq(X) = Σ entries²`. A "chain" `(n0,n1,...,n_last)` has box-integral finiteness
  RouteMBoxThresholdFinite: for c' < minAdm/2, INT_{all layer matrices A_i in [-1,1]-box} frobSq(prod A)^{-c'} < inf,
proved by induction; we ASSUME `hIH` = this finiteness for every SHORTER chain (fewer layers).
minAdm recursion: minAdm(M) = min_{t=0..min(n0,n1)} (n0-t)(n1-t) + minAdm(redChain t M), redChain t M = (t, n2, ...)
(collapses the first TWO widths into one width-t layer). Cut-soundness proved.

THE INTEGRAL (the "a=0 wide wing", POWER regime). Widths M=(M0,M1,M2,...,M_last), M0 < M1 (wide front),
M2 >= M1-M0+2 (POWER). The front factor is F = [P | B12], an M0 x M1 matrix with the leading M0 x M0 block P
INVERTIBLE (so F has full row rank M0 ALWAYS), all entries in [-1,1]. Let A1 be the next layer (M1 x M2, box),
Zdeep = product of the deeper layers (M2 x q). The integral is
  I(c') = INT_{F wingbox} INT_{A1 box} INT_{deep box} frobSq( F · A1 · Zdeep )^{-c'}.
Write W = F·A1 (M0 x M2). The known facts (exact-integer, verified):
  - min over s in [0,M0] of [ (M0-s)(M1-s) + minAdm(redChain s M) ] = minAdm(M)   (the front rank-sector).
  - For the BOUNDED regime M2 <= M1-M0 the density of W is bounded and I(c') reduces to
    [ INT_F det(FF^T)^{-M2/2} = qbox, converges M2<=M1-M0 ] × [ hIH(redChain M0 M) ].  (This is BANKED.)
  - In POWER (M2 >= M1-M0+2) that qbox DIVERGES; the reduction must go via a per-stratum blow-up, each stratum
    s reducing to hIH(redChain s M) at "charge" (M0-s)(M1-s).
  - The binding stratum s* is often INTERIOR (0 < s* < M0). Smallest interior template: M=(2,3,3, n_last),
    binding s*=1, charge (2-1)(3-1)=2, redChain 1 M = (1,3,n_last,...).

KEY SUBTLETY (verified): the charge (M0-s)(M1-s) is NOT the naive determinantal codim of {rank W = s} in the
M0 x M2 matrix space, which is (M0-s)(M2-s) — they differ when M1 != M2 (e.g. M=(1,2,3): charge (1)(2)=2 vs
Wrank-codim (1)(3)=3). Also, for FIXED full-row-rank F the map A1 |-> W=F·A1 is a submersion, so the fixed-F
pushforward density is SMOOTH (no rank-drop singularity); the density singularity of W over (F,A1) comes from
INTEGRATING F as F becomes ill-conditioned (σ_min(F)->0, det(FF^T)->0), coupled to W's rank drop.

DERIVE, for the smallest interior template M=(2,3,3,n_last), stratum s=1 (charge 2, target hIH((1,3,n_last,...))):
(a) THE SECTOR / CHART. What is the correct source-incidence chart that resolves the s=1 stratum? Which SOURCE
    variables (entries/combinations of F and A1) are the exceptional coordinates z_j that vanish on the stratum,
    and which are the "unit"/transverse directions? (Recall F=[P|B12], P invertible 2x2, B12 2x1; A1 3x3.)
(b) THE JACOBIAN. Give |det DΦ| as u(ξ)·∏_j |z_j|^{ν_j - 1} (0 < c ≤ u(ξ) ≤ C on the chart) — the exact
    exceptional exponents ν_j — for this s=1 chart.
(c) THE REDUCTION. After the chart + Jacobian, does the stratum integral factor as [an explicit convergent
    exceptional-radial integral, giving the charge 2] × [ hIH((1,3,n_last,...)) at the shifted exponent
    c' - charge/2 = c' - 1 ]? Show the charge 2 emerges (reconcile with the fact that it is NOT (M0-s)(M2-s)).
(d) GENERAL PATTERN. State the general interior-stratum s chart/Jacobian/exponents for general wide POWER
    M=(M0,M1,M2,...), and confirm the charge is (M0-s)(M1-s) (peelCharge), the reduction is to hIH(redChain s M),
    and whether the M2 (the reduced leading width) is what stays inside the reduced chain (so the "excess"
    (M0-s)(M2-s) - (M0-s)(M1-s) = (M0-s)(M2-M1) is accounted by the reduced chain's own leading (s,M2) layer,
    NOT the charge).
(e) Is each interior stratum a GENUINELY-NEW determinantal blow-up (not reducible to the banked "fixed-F CoV +
    det(FF^T)-qbox + hIH", which only closes the TOP submersive sector s=M0)? Or is there a banked-only route?
</task>

<output_contract>
  Sections (a)-(e). For (a)/(b) be fully concrete for M=(2,3,3,n_last), s=1: name the exceptional coordinates
  and the exact ν_j. For (c) show the charge-2 radial integral explicitly. For (d) the general formula. For
  (e) a one-line verdict {NEW-BLOWUP / BANKED-ONLY}. PROVEN/ARGUED/GUESS per claim. If the charge-vs-codim
  reconciliation reveals the stratification is on a DIFFERENT object than {rank W = s}, say what object. End
  with the single cheapest numerical check that would confirm the exponents. Concrete; no hedging.
</output_contract>

<grounding_rules>
  hIH is plain (undecorated) box-finiteness of shorter chains. A weight det(product-Gram)^{-w} left on the
  reduced box is NOT absorbable by plain hIH. The blow-up is "clean" only if the exceptional Jacobian is a pure
  monomial × bounded unit and each stratum reduces to an unweighted shorter-chain box integral. State inference
  vs fact; do not rubber-stamp — if the interior stratum needs content beyond a determinantal blow-up, say so.
</grounding_rules>
