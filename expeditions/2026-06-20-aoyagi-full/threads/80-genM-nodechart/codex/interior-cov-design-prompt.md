<task>
Lean 4 + Mathlib formalisation. I must discharge the `cov` field of an "interior achiever chart"
for a deep-linear-network RLCT lower bound, over OPAQUE widths (general M). I need a decorrelated
opinion on the cleanest design route. Here are the EXACT facts (all verified by reading the code).

THE CONTRACT (already landed, sorry-free) requires a chart `phi : (Fin N → ℝ) → (Fin N → ℝ)`
(N = routeMAmbient M opaque) and an exponent vector `leafH : Fin N → ℕ`, with a change-of-variables:
  cov:  ∫⁻ x in phi '' (V \ {x_p=0}), g  =  ∫⁻ u in V \ {x_p=0}, ofReal(∏_j |u_j|^{leafH j}) · g(phi u)
i.e. the Jacobian |det Dφ(u)| must equal the MONOMIAL ∏_j |u_j|^{leafH j}.

The contract hard-wires phi := achieverPhi M := phiFlatStructV M (tach M) ha hN, where
  phiFlatStructV x := phiGen (x p) M t (genBlkFlatStruct M t ha x) hle.

KEY FACT 1 (the obstruction): genBlkFlatStruct reads each per-boundary Schur K-core block DIRECTLY
as a FREE matrix coordinate (`readK ... i j = x[slot(i,j)]`). The frame Jacobian per boundary s is
|det K_s|^{r_s + c_s}, so the chart's total |det Dφ| = (radial pivot)^a · ∏_s |det K_s|^{r_s+c_s}.
For a t×t K-core with t ≥ 2, det K_s is a degree-t POLYNOMIAL in the free coords (e.g. at the
(3,3,3,3) node the 2×2 core gives det = z1·z4 − z2·z3), NOT a monomial. Hence the FREE-K chart
phiFlatStructV CANNOT have a monomial Jacobian. The contract's cov field as written (phi = phiFlatStructV)
appears UNSATISFIABLE with the monomial RHS.

KEY FACT 2 (the worked instances): The only worked monomial-det instance with a t≥2 K-core is the
hand-built (3,3,3,3) chart phi3333 = paramsEquivFlat ∘ Frame3333 ∘ Kparam3333. Here Kparam3333 is an
explicit LDU reparametrization: it maps free coords (x1,x2,x3,x4) to K-core entries
[x1, x1·x2, x1·x3, x1·x2·x3 + x4] — an LDU lens whose det is the MONOMIAL (x1)^2. So phi3333 reads K
through an LDU lens; its Jacobian IS a monomial. phi3333 is NOT genBlkFlatStruct — it is a DIFFERENT
decoder (an LDU-coordinatized one). The (2,2,2) det leg uses yet another bespoke decoder B_det222
(but at (2,2,2) the K-cores are 1×1 so det is trivially a monomial — LDU is not exercised there).

KEY FACT 3 (the rate is decoder-agnostic): The rate identity routeMCore(phiGen(u) (B) ...) = u²·VvalGen(...)
holds for ANY GenBlk decoder B with a normalized identity boundary (it consumes only hC0 : C 0 · suffix = suffix).
So a DIFFERENT decoder B' that reads K through an LDU lens STILL satisfies the rate identity. But:
  - the banked interior witness `exists_achieverUfun_ne_zero_interior` (the Ubound a.e.-positivity input)
    is proven specifically for genBlkFlatStruct (free-K), using readK_wInt = identity-matrix reader.
  - the landed contract `routeMCore_box_diverges_interiorContract` is stated with phi = phiFlatStructV (free-K).

THE BANKED REUSABLE MACHINERY (all general-width, sorry-free):
  - ChartFactor N + composeFold (foldr ∘) + composeFold_abs_det (telescope of per-factor |det|).
  - radialFactor (det |u_p|^{card−1}), schurChartFactor E (det |K.det|^{r+c}), lduChartFactor E
    (det ∏|q_i|^{2(t−1−i)}, the LDU monomial), chainChartFactor (det 1) — each conjugated by an abstract
    CLE E : (Fin N → ℝ) ≃L[ℝ] Block × R.
  - phiTarget_abs_det_of_factored: GIVEN a map equality `composeFold fs = phi` + per-factor det bookkeeping,
    delivers |det Dφ| = ∏|u_j|^{leafH j}.
  - Worked (4,4,2,2): phi4422 = composeFold [linearFactor Q, radialFactor {0,1,2,3} 0] (pure radial, no LDU);
    the map-equality is a 5-line `funext` + `change` + rfl-chain.
</task>

<output_contract>
Answer in 4 short sections, ranked, concrete:

1. VERDICT on the obstruction: Is my conclusion correct that the contract's cov field with
   phi = phiFlatStructV (free-K) is unsatisfiable with a monomial Jacobian for t≥2 K-cores? Yes/No + one-line why.

2. The CLEANEST route (rank 2-3 options). Candidate routes I see:
   (A) Build a NEW LDU-coordinatized decoder genBlkFlatLDU (reads K via an LDU lens like Kparam3333 generalized),
       prove (a) its rate via the decoder-agnostic engine [cheap], (b) re-derive the interior witness for it
       [moderate — re-run the witness inductions on the LDU reader], (c) a NEW contract on phiFlatLDU, (d) the
       monomial cov via composeFold fs = phiFlatLDU.
   (B) Keep phiFlatStructV but POST/PRE-compose an LDU change-of-coords map ψ so that φ∘ψ (or the
       integrand pullback) has monomial det, absorbing the polynomial det K via a measure-preserving-on-pieces
       reparametrization. (Does this even change the |det| to a monomial? det(φ∘ψ) = det φ · det ψ; need det ψ
       to KILL the polynomial det K and leave a monomial — i.e. ψ is itself the LDU lens. So is (B) just (A)
       in disguise?)
   (C) Something I'm missing.
   For each: the genuine cost (which banked bricks fire vs which need new math), and the single biggest risk.

3. The DESIGN of the composeFold factor list `fs` for the general interior chart over opaque widths:
   what is the right ORDER (radial, then per-boundary {LDU-core, schur-frame, chain}, descending)? And the
   single hardest dependent-Fin-cast hazard in proving `composeFold fs = phi` (the item-3 map equality) over
   opaque Wext/Text widths — where does the (3,3,3,3) pattern fail to generalize?

4. Is there a route that AVOIDS the map equality entirely (define φ AS composeFold fs, get the monomial det
   for free, and transfer the rate by a SEPARATE map equality only at the rate level, not the det level)?
   The rate is decoder-agnostic — can I exploit that to sidestep the hard det-side map equality?
</output_contract>

<grounding_rules>
You have NOT seen the code, only my summary. Flag any step where your recommendation depends on a fact
I have NOT stated (mark it "ASSUMPTION: ..."). Distinguish "this banked brick clearly suffices" (from my
summary) vs "you'd need to verify X exists". Do NOT emit Lean code blocks longer than ~5 lines; I want the
DIAGNOSIS and the route ranking, not an implementation.
</grounding_rules>
