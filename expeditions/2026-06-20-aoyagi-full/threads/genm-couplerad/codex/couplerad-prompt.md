<task>
Adjudicate, by exact real-analysis reasoning, whether a specific monomial/blow-up RESOLUTION of a
COUPLED (biquadratic, non-separable) integrand is (i) COMPLETE (its charts cover the domain), (ii) SOUND
(every chart's radial convergence exponent is at least a stated FLOOR), with the change-of-variables
Jacobian carried at every step. Reason it out from scratch and DECIDE. Do not assume my framing is right.
</task>

<grounding_facts>
Setting (a local model from a deep-linear-network RLCT computation; all exact, no numerics needed):

Fix integers u >= 1, and deep widths (M2, ..., M_last) with rho = min(M2,...,M_last), n = M_last,
exc = |M2 - n|. Fix a "front cut" giving a = M0-u >= 1, b = M1-u >= 1 with a+b <= rho-1.

The object to integrate, over a neighborhood of the singular locus, is (schematically) the deep integral
partitioned into strata k = 1..rho by the rank drop of a deep matrix product Z (an M2 x n matrix whose
generic rank is rho). On the stratum {rank Z = rho - k}, after a Schur/pivot reduction of Z into a
surviving (rho-k)-block and a "lost" k-block, the local model is:

  LOSS (COUPLED, biquadratic):   |y|^2  +  sum_{i=1}^k  sigma_i^2 |W_i|^2
        y in R^{u(rho-k)}  (front weights hitting the surviving block; order-1 directions),
        W_i in R^u          (front weights hitting the i-th lost direction),
        sigma_1 >= ... >= sigma_k >= 0   (the k "lost" singular values of Z's normal slice).
  MEASURE:   dy . dW .  [ prod_{i<j} |sigma_i^2 - sigma_j^2| ] . [ prod_i sigma_i^{p-k} ] dsigma,
        where p = k + exc  (the normal slice is p x k).
  CHARGE (a NEGATIVE determinantal power, can blow up):  det(Q_b Q_b^T)^{-a/2}, where Q_b is the b x n
        bottom block of Z (b = M1-u rows). On a monomial ray sigma_i = tau^{e_i} (ordered e_1<=...<=e_k),
        the charge contributes tau^{-gamma(e)} with gamma(e) = max_{h in [max(0,b-s), b]} [ a(e_1+..+e_h) - h(s-b+h) ],  s = rho-k.
  We want finiteness of   integral  (LOSS)^{-q} . CHARGE . MEASURE   for  2q < FLOOR.

The FLOOR is the reduced-rank-regression codimension of the sub-chain (u, M2, ..., M_last):
  FLOOR = minAdm((u, M2, ..., M_last)),  where minAdm is the recursion
     minAdm(x0,x1) = x0*x1 ;  minAdm(x0,x1,rest...) = min_{t=0..min(x0,x1)} (x0-t)(x1-t) + minAdm(t, rest...).

Facts I have already established by exact rational computation (you may use or challenge them):
 - On a monomial ray sigma_i=tau^{e_i}, y=tau^f, W_i=tau^{g_i}, in the OPEN ORDERED sector the Vandermonde
   prod_{i<j}|sigma_i^2-sigma_j^2| becomes the exact monomial prod_i sigma_i^{2(k-i)}, so each sigma_i
   carries measure exponent beta_i - 1 with beta_i = (p-k+1) + 2(k-i).
 - Each pair (sigma_i, W_i) forms a PRODUCT term sigma_i^2 |W_i|^2 whose (-q) power FACTORS as
   sigma_i^{-2q} |W_i|^{-2q} (a product, not a sum).
 - The available FINITENESS ATOMS in the target formal system are exactly:
    (A) a "residual-power / Morse peel":  integral_{[-T,T]^m} (sum_j P_j^2 + w)^{-c} dP <= C . w^{-(c - m/2)}
        for c > m/2, w>0  (peels an m-dim Morse block, shifts the exponent down by m/2, leaves a residual
        power of the remaining loss w);
    (B) a "bilinear fibre peel":  integral_X frobSq(X.Y)^{-c} dX <= C . frobSq(Y)^{-c}  for c < p'/2,
        where X is p' x (something) and the bound is EXPONENT-PRESERVING (same c on frobSq(Y)); it uses
        only ONE column of Y (does not see Y's rank);
    (C) a "corank recursion" for a SQUARE-first-factor bilinear  integral integral frobSq(Delta . S)^{-c}
        (Delta is r x r SQUARE, S is r x p') which reaches c < minAdm(r,r,p')/2 by an iterated Schur /
        minor-pivot split with a SHIFTED exponent -- but ONLY when the first factor is square.
   The diagonalizing SINGULAR VALUE DECOMPOSITION (producing the sigma_i explicitly) is available in
   principle but is EXPENSIVE / hostile in the target formal system (spectral eigen-terms cause
   unification blowups), so a resolution that AVOIDS producing individual sigma_i is strongly preferred.
</grounding_facts>

<questions>
1. Compute the honest per-stratum convergence codimension of the coupled integrand above (the min over
   all monomial rays of 2 * numerator/denominator, numerator = sum_i e_i beta_i + u(rho-k) f + u sum g_i
   - gamma(e), denominator = min(2f, min_i 2(e_i+g_i)) normalized to 1). Give a CLOSED FORM in terms of
   u, rho, k, p, and state whether it is >= FLOOR for every stratum k. Does the CHARGE gamma(e) ever
   lower the min below FLOOR?

2. Is the coupled integrand's codimension ADDITIVE over the disjoint variable groups (y), (sigma_1,W_1),
   ..., (sigma_k,W_k)? If so, can atoms (A)+(B)+(C) be composed to realize that additive codimension
   WITHOUT diagonalizing (without producing individual sigma_i) -- i.e. by peeling front weights with (B),
   the surviving block with (A), and the lost k-block by a raw-coordinate Schur/pivot recursion (C)? Where
   does the requirement in (C) that the first factor be SQUARE bite, and for which (u, M2, n) does the
   reduced lost-block bilinear FAIL to be square-first-factor?

3. Is a monomial resolution that reaches the FLOOR per-stratum GENUINELY POSSIBLE natively (a real
   obstruction would be: the honest exponent is < FLOOR for some stratum, OR the only route needs the
   exact rlct = codim/2 equality rather than just the codim lower bound), or is it a CONSTRUCTION problem
   (charts + Jacobian bookkeeping)? Flag any place where carrying the Jacobian |det J| wrong (dropping the
   Vandermonde or the sigma^{p-k} measure or the (B)/(A) Jacobians) would spuriously make it fail.

4. The charge det(Q_b Q_b^T)^{-a/2}: in a RAW-coordinate (non-SVD) resolution, Q_b Q_b^T can degenerate
   (Q_b loses row rank). Does carrying the charge through the raw Schur complement keep the exponent >=
   FLOOR, or does the charge force an SVD (spectral) treatment? Is the charge's contribution dominated?
</questions>

<output_contract>
- A crisp verdict for each of the 4 questions (YES/NO + the exact reason).
- The closed-form per-stratum codimension and whether it dominates FLOOR (with the charge).
- The precise condition under which the raw (SVD-free) atom composition reaches the floor, and the exact
  sub-case (if any) where it does NOT and a genuinely new step is needed.
- Distinguish clearly PROVED-by-your-reasoning from CONJECTURED. Show the key inequality for additivity.
- Be concrete with small worked numbers: use (M0,M1,M2,M3) = (4,4,4,4), u=3 (a=b=1, rho=4, exc=0, FLOOR=10)
  and (3,4,5,4), u=2 (a=1,b=2,rho=4,exc=1,FLOOR=8).
</output_contract>
