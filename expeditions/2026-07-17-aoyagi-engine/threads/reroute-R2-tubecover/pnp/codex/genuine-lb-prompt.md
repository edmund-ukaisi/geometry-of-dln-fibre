<task>
RED-TEAM a genuine RLCT lower-bound argument for over-vanishing resolution charts (DLN (3,3,4)).

Setting: on a resolution chart with local coords u0..u20, the pulled-back loss is
    loss(u) = sum_{k} g_k(u)^2 ,   g_k = vm * vf_k ,   vm = the monomial GCD of all g_k (a monomial),
so loss = vm^2 * sum_k vf_k^2.  The chart Jacobian is |det| = u^kappa (a monomial; kappa integer >=0).
The per-chart RLCT contribution is the lambda controlling convergence of  INT u^kappa * loss(u)^{-lambda} du
near 0.  We use the standard facts: (i) RLCT is monotone: f >= h >= 0 near 0 => rlct(f) >= rlct(h);
(ii) rlct is invariant under an analytic change of coords with Jacobian a unit at 0.

For an "over-vanishing" chart every vf_k(0)=0 (no unit survivor).  CONCRETE DATA for one such chart:
  vm = u1*u5*u20 ,  kappa nonzero ONLY on {u1:10, u5:7, u20:8} (all OTHER coords have kappa=0).
  Residual factors vf_k (the 12 generators; sample):
    vf_0 = u0 ,  vf_3 = u2 ,  vf_6 = u3 ,  vf_9 = u4                         (pure monomials, degree 1)
    vf_1 = u0*u10 + u1*u12 + u16                                            (linear part = u16)
    vf_4 = u1*u13 + u10*u2 + u17                                            (linear part = u17)
    vf_7 = u1*u14 + u10*u3 + u18                                            (linear part = u18)
    vf_10= u1*u15 + u10*u4 + u19                                            (linear part = u19)
    vf_2, vf_5, vf_8, vf_11 : degree-2/3, ignore.
So among the vf_k, EIGHT have differentials at 0 equal to the eight distinct coordinate 1-forms
du0,du2,du3,du4,du16,du17,du18,du19 -- all on kappa=0 coords, disjoint from supp(vm)={u1,u5,u20}.

CLAIMED genuine lower bound (the thing to red-team):
  Step 1 (subset): loss = vm^2 * sum_k vf_k^2 >= vm^2 * sum_{k in S} vf_k^2, S = the 8 above (drop the rest, all >=0).
  Step 2 (purify): the map Phi = (u0,u2,u3,u4,u16,u17,u18,u19) |-> (vf_0,vf_3,vf_6,vf_9,vf_1,vf_4,vf_7,vf_10)
     has Jacobian = identity at 0 (triangular, det 1), touching ONLY the 8 kappa=0 coords (u1,u5,u20
     untouched), so it is a unit-Jacobian analytic change; in the new coords z_1..z_8, vf_k|_{k in S} = z_i.
     Hence loss (in new coords) >= vm^2 * (z_1^2+...+z_8^2), with vm depending only on {u1,u5,u20}
     (disjoint from the z's), and the z's have kappa=0.
  Step 3 (product of disjoint blocks): for f = vm(x)^2 * (sum_{i=1}^r z_i^2), x-vars and z-vars disjoint,
     jac = x^{kappa_x} (kappa=0 on z), by Fubini the integral factors, giving
        rlct(f) = min( threshold(vm^2),  r/2 ),   threshold(vm^2) = min_{t in supp vm} (kappa_t+1)/(2 vm_t).
  Conclusion: rlct(loss) >= min( threshold(vm^2), 8/2 ) = min( min(11/2,8/2,9/2), 4 ) = min(4,4) = 4.

Also asserted, as the reason a cruder bound fails and the toric LP can't be used for the lower bound:
  (a) the single-term bound loss >= (vm*vf_0)^2 = (u0*u1*u5*u20)^2 gives only threshold 1/2 (the u0 factor
      has kappa=0), useless;
  (b) the "toric LP" min_{w>=0}(kappa+1).w s.t. w.m>=1 over all monomials m of all g_k computes the rlct
      of the MONOMIAL ideal <all monomials>, which CONTAINS <g_k>, hence is an UPPER bound on the true
      rlct -- so it cannot certify a lower bound for over-vanishing charts.
</task>

<output_contract>
Four sections, terse:
1. STEP-BY-STEP AUDIT: for each of Steps 1,2,3 state VALID or FLAWED with the precise reason. In
   particular scrutinize: Step 2's claim that Phi is a genuine unit-Jacobian change touching only the
   kappa=0 coords (note vf_1 CONTAINS u1, a supp(vm) coord, at degree 2 -- does that break "touches
   only kappa=0 coords" or the disjointness needed in Step 3?); and Step 3's product/Fubini rlct = min.
2. TORIC DIRECTION: confirm or refute (b) -- is the toric LP an upper or a lower bound on the true rlct,
   and does that invalidate using it (or the rational-dual certificate of LP_min>=8) to prove rlct>=4
   for OVER-VANISHING charts? State it crisply (it does NOT affect survivor/normal-crossing charts -- say why).
3. HOLES: the single most likely error or missing hypothesis in the claimed >=4 bound, and whether the
   conclusion rlct>=4 survives it. If the bound is sound, say so plainly.
4. GENERALITY: the argument must hold for all 16 over-vanishing leaf-types (each has r=8 such coords and
   threshold(vm^2) in {4, 9/2}). What is the minimal general hypothesis that makes "rlct>=4" a theorem
   for the whole family (state it as: r>=8 regular-seq jac-0 coords disjoint from vm, AND threshold(vm^2)>=4)?
</output_contract>

<grounding_rules>
- Reason from the algebra + the two RLCT facts given; do not invoke heavy machinery you can't state.
- Separate provable fact from plausible inference. If a step is correct, say so; do not manufacture doubt.
- No code. If you need one more computed quantity, name it exactly.
</grounding_rules>
