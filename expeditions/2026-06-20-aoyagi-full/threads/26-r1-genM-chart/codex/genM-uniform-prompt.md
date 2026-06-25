<task>
Build a UNIFORM closed-form change-of-variables chart for a deep-linear-network achiever divergence,
parametric in the width vector. You earlier gave an explicit chart for M=(3,3,3,3) (reproduced below);
I verified it EXACTLY. I now need the GENERAL strictly-decreasing-kept-rank construction (a single
recipe for arbitrary L and arbitrary strictly-decreasing achiever path), not a per-case chart.

SETUP. Widths M=(M_0,...,M_L), factors A^(s) of shape M_s x M_{s+1} (s=0..L-1), loss
F = ||A^(0) A^(1) ... A^(L-1)||_F^2, near A=0. Descent/achiever path T*=(t_1,...,t_{L-1}), with
t_0:=M_0, t_L:=0, STRICTLY DECREASING: M_0 = t_0 > t_1 > t_2 > ... > t_{L-1} > t_L = 0.
Kept ranks p_s = t_s. Block sizes d_s = (t_{s-1}-t_s)(M_s - t_s),  sum_s d_s = minAdm(M).
Want a polynomial diffeo Phi : R^N -> R^N (N = sum_s M_s M_{s+1} = flatDim) with:
  (G1) F(Phi(u)) = u_p^2 * V(u), V a polynomial bounded in (c0, B) on a positive-measure box
       (so the achiever RATE is u_p^2 -- min u_p-degree of F is exactly 2, no u_p^0 term);
  (G2) V|_{u_p=0} not identically 0, > 0 at an explicit sector point;
  (G3) |det D Phi| = |u_p|^{minAdm-1} * (spectator monomial in the k=0 frame coords), det != 0 off
       {u_p=0}.  The single binding axis u_p has (loss-base k, Jacobian h)=(1, minAdm-1), threshold
       (minAdm-1+1)/2 = minAdm/2.

YOUR VERIFIED (3,3,3,3) CHART (for reference, path (2,1,0), blocks (1,2,3)):
  K=[[a, a*alpha],[gamma*a, gamma*a*alpha+delta]];  m=(m1,m2)^T; lambda=(lam1,lam2);
  A = [[I2],[lambda]] K [I2 | m] + u E_{33};
  w=(1,n1,n2); p=(1,ell)^T; Y=[[0,0,0],[0,eta1,eta2]];  D = p b w + u Y;
  r free 1x3;  B = [[D - m r],[r]]  (so (I2|m) B = D);
  h1,h2,zeta free 1x3;  C = [[u zeta - n1 h1 - n2 h2],[h1],[h2]]  (so w C = u zeta);
  Then ABC = u H,  F = u^2 ||H||^2,  |det DPhi| = |u|^5 |a|^4 |delta|^2 |b|^3.

WHAT I FOUND (the obstruction to a NAIVE uniform recipe). A per-boundary local Schur frame
(scale only the drop-row x drop-col residual by u, keep the beta/gamma shears O(1)) does NOT compose:
the inter-factor coupling produces a u^0 term (rate broken) and the wrong det exponent. Your (3,3,3,3)
chart works because of GLOBAL chaining (the "B = [[D-mr],[r]]" makes the kept projection land exactly,
and "C row = u zeta - sum n_i h_i" makes the kept combination = u zeta). I need the GENERAL version of
this chaining: a closed recipe for the frames {G_s}, the residual placement, and the chaining inverses,
for arbitrary strictly-decreasing kept ranks, such that (G1)-(G3) hold.

THE QUESTIONS:
  (1) Give the general construction: for each factor A^(s), the explicit frame + residual + chaining,
      as a function of M and the path, so that the product telescopes to u*H with F=u^2*V (no u^0),
      |det| = u^{minAdm-1} * spectator.  Ideally a telescoping form A^(s) = (frame_s)(core_s(u))(frame_{s+1}^{-1})
      or your B/C-style chaining generalised to L factors.
  (2) Confirm (or correct) the Jacobian exponent: that scaling exactly the d_s residual blocks by ONE
      common radial u, with the rest free frames, gives det u-exponent minAdm-1 (one radial absorbed),
      with a spectator monomial in the pivot-determinant coords (like |a|^4|delta|^2|b|^3 for (3,3,3,3)).
  (3) The codim-0 case: a block d_s=0 occurs when t_{s-1}=t_s (kept rank STAYS, e.g. M=(2,3,4,2) path
      (1,1,0)) OR when M_s=t_s (e.g. M=(5,4,3,2) path (4,2,0), block 0). Does your construction handle
      d_s=0 boundaries cleanly (no residual to scale there, just a frame pass-through), or do they need
      special handling?  Give the recipe for a d_s=0 boundary.
</task>

<output_contract>
1. The general strictly-decreasing construction (frames + residual + chaining), closed-form in M and
   the path. Explicit enough to verify symbolically (I will).
2. The Jacobian-exponent confirmation/correction (minAdm-1 + spectator), with the spectator monomial's
   form in general.
3. The d_s=0 (codim-0) boundary recipe.
4. Distinguish derived vs conjectured; flag any step you are unsure of. Exact algebra for G1-G3.
</output_contract>

<grounding_rules>
- F(Phi) = u^2 V must be an exact polynomial identity (min u-degree exactly 2). State it as such.
- |det| computation must be exact. The spectator monomial sits on k=0 (loss-base-0) axes so it does
  not change the binding-axis threshold minAdm/2.
- The threshold of the product monomial prod x_i^{2 k_i} with Jacobian weight prod x_i^{h_i} is
  min_{k_i != 0} (h_i+1)/(2 k_i).
- I am withholding my tentative telescoping idea. Reason from the (3,3,3,3) chart's structure.
