<task>
Red-team a claimed convergence/soundness structure in an RLCT (real-log-canonical-threshold)
codimension proof for deep linear networks. I have a specific corner I want you to independently
adjudicate: does it CLOSE (finite integral, charge sufficient) or is there a genuine divergence /
under-charge? I am WITHHOLDING my own conclusion. Give your own verdict from the facts.
</task>

<background_facts>
We integrate, over bounded boxes, a loss-power integrand arising from peeling a "binding cut" t*
off a layer chain M = (M0, M1, M2, ...). At a binding cut:
  a := M0 - t*   (rows of a "freed corner" Gamma, a x b)
  b := M1 - t*   (corank rows: A_cor is b x M2, and Q_b := A_cor . Z is b x m)
  r := min(a,b)
  Z is the deep product, M2 x m, ranging in a bounded box; rank Z can drop.

BANKED (proven) facts I give you as ground truth:
F1. Freed-corner Gaussian peel (atom brick): integrating a p x b corner Gamma against a
    full-row-rank b x m matrix Q gives  ∫ (w + ||C + Gamma.Q||_F^2)^{-c'} dGamma
      = const · det(Q Q^T)^{-p/2} · (tail)^{-(c' - p*b/2)},
    i.e. the Gram-divisor exponent is p/2 where p = number of FREED (peeled) rows.
    (I verified the exponent p/2 by the exact scaling law I(lambda Q)/I(Q) = lambda^{-p b};
     at p = 0 the corner is empty and the integrand is just (tail)^{-c'}, no det weight.)
F2. Singular-value SHELL stratification of Z by a SINGLE threshold eps: shell S_j = {exactly j
    singular values of Z < eps}, j = 0..r, with S_r = {>= r small singular values} the lumping
    "saturated" shell. On shell j (j < r) an adapted (M2-j)-minor change-of-variables eliminates
    the j weak directions, leaving a reduced det-Gram weight over (b-j) corank rows in the
    (M2-j)-strong subspace with exponent (a-j)/2, STRICTLY convergent iff a-j < M2-b+1.
F3. Charge at shell j:  C_j = (a-j)(b-j) + minAdm(redChain(t*+j) M),  where redChain(t) M =
    (t, M2, M3, ...) and minAdm is the Aoyagi layer-peel minimum (minAdm of a 2-width leaf (n,m)
    is n*m). Banked convexity (minAdm_redChain_succ_ge) telescopes to  C_j >= minAdm(M)  for all j,
    with equality (tight) at j=0. carrierThreshold(M) := minAdm(M)/2; the hypothesis is
    c' < carrierThreshold(M). The reduced comparator at shell j is invoked at exponent
    e_j = c' - (1/2)(a-j)(b-j), and the recursion's inductive hypothesis (IH) supplies its
    finiteness provided e_j < carrierThreshold(redChain(t*+j) M) = minAdm(redChain(t*+j) M)/2.
F4. There is a LANDED sorry-free sibling ("OnePeel334") proving a Morse codim-rescue: an integral
    ∫_box (sum of squares)^{-w c'} over a deep block is FINITE near the origin (the {Z->0} tube)
    exactly when the block's codimension is large enough (finite <=> w c' < (deep dim)/2). This is
    the mechanism that closes the {rank Z drops} degeneracy WITHOUT any change of variables.

THE SPECIFIC CORNER (a != b). Take M = (3,4,4). Binding cuts t* = 1 (a=2,b=3) and t* = 2 (a=1,b=2);
both give minAdm(M) = 10, carrierThreshold = 5. Focus on t* = 1: a=2, b=3, r = min = 2, so a < b
and b - a = 1 "surviving" corank row. At the SATURATED shell j = r = 2:
  - freed corner is (a-r) x (b-r) = 0 x 1  (zero rows, so by F1 the Gram-divisor exponent is
    (a-r)/2 = 0);
  - the deeper cut is t*+r = 3 = min(M0,M1) (the MAXIMAL legal cut; t*+j for j>r would exceed
    min(M0,M1));
  - redChain(3) M = (3,4), minAdm = 12, so C_r = 0 + 12 = 12;
  - the reduced comparator is invoked at e_r = c' - 0 = c', and carrierThreshold((3,4)) = 6.
Contrast the a=b anchor (3,3,3)@t*=1 (a=b=2, r=2): there the saturated freed corner is 0 x 0 and
there are NO surviving corank rows -- everything "absorbs". The a != b case leaves b-a=1 corank rows
that the minor CoV (which is exhausted at saturation) cannot reach.
</background_facts>

<questions>
Q1. THE SATURATED-SHELL INTEGRAND (a != b). At j = r with a < b, the minor CoV is exhausted. Write
    what you believe the leftover integrand is over the b-a surviving corank rows plus the collapsed
    strong block. In particular: what is the exponent of the det-Gram weight carried by the b-a
    surviving corank rows, and is that weight integrable over a bounded box in EVERY configuration
    (including Z -> 0 / genuine rank drop)? Could that weight ever diverge?

Q2. DOES THE MORSE RESCUE CLOSE IT? Given F4 (the deep Morse codim-rescue closes {Z->0}) and the
    charge C_r = 12 with the comparator invoked at e_r = c' < 5 < 6 = carrierThreshold((3,4)):
    does the saturated shell at a != b close by "surviving-corank weight x deeper comparator IH",
    or does the presence of the b-a unabsorbed corank rows break the identification / the charge?

Q3. CHARGE SUFFICIENCY at a != b. At saturation the freed corner contributes 0 to the charge, so
    ALL of C_r must come from minAdm(redChain(t*+r) M). Is C_r >= minAdm(M) still guaranteed when
    a != b (freed corner exactly 0), or can the "0 freed corner" cause an undershoot that the a=b
    case hides? Reason from the convexity telescoping in F3.

Q4. ADVERSARIAL. Construct, if you can, a surviving-corank configuration (at this or any a != b
    binding cut) where EITHER the surviving-row box integral diverges OR the saturated charge C_r
    undershoots minAdm(M). If you can, that is a real obstruction -- state it plainly. If you cannot,
    say why the corner is sound.

Q5. Is the saturation boundary j = r = min(a,b) the correct cutoff (are cuts t*+j for j>r genuinely
    illegal), and does (3,4,4) bottom out cleanly there?
</questions>

<output_contract>
For each of Q1-Q5: a direct verdict (CLOSES / OBSTRUCTION / UNCERTAIN) + the load-bearing reason.
Distinguish what you can prove from the given facts vs what you infer. If you think the corner has
a genuine hole at a != b, say so loudly and pinpoint it. Do not rubber-stamp; I want your independent
reconstruction of the saturated-shell integrand and its finiteness.
</output_contract>

<grounding_rules>
Ground strictly in the facts above. F1-F4 are proven; treat them as ground truth. Everything about
the a != b saturated shell is what you are adjudicating. It is fine to reach a "CLOSES" verdict if
the facts warrant it, but show the reconstruction. If a fact is insufficient to decide, say UNCERTAIN
and name what is missing.
</grounding_rules>
