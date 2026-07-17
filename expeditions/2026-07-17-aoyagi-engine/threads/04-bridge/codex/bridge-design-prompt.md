<task>
Setting (exact, no ML). Fix integers M = (M^(1),...,M^(L+1)). C^(s) is a free real M^(s) x M^(s+1)
matrix (entries are coordinates); F(C) = ||C^(1)...C^(L)||_Frobenius^2, homogeneous of degree 2L. We
must prove a Lebesgue-integral finiteness:
    routeMLayerBoxIntegral(M, c') = integral over [-1,1]^N of F(C)^{-c'} dC  <  infinity,
for every c' < (1/2) minAdm(M).  A resolution tree gives a finite family of "leaf" charts.

The BUG we are fixing. The current Lean obligation `region_glue` takes
   (hcov : ChartsCover M t)   -- says: the zero locus is covered by a neighborhood inside the union
                                 of the leaves' `chartDom : Set (Params M)` (chartDom an ABSTRACT set)
   (hrat : for all terminal divisor exponents e, c' < e/2)
and concludes the box integral is finite. This is UNPROVABLE as stated: nothing ties `chartDom` to any
chart MAP or to the loss, so `chartDom = univ` satisfies ChartsCover vacuously and the divExp are
decoupled from the actual monomialisation. (Confirmed by an exact counterexample: a fake all-univ
atlas with divExp={4} satisfies both hyps at c'=8/5 for M=(2,2,2) while the true integral diverges,
since true 1/2 minAdm = 3/2.)

What I have verified EXACTLY (sympy) on real resolution charts:
 - (2,2,2) delta-chart: with chart map phi (incidence A=alpha[[1,a],[b,ab+delta]],
   B=[[delta u'-a r, delta v'-a s],[r,s]]), the pullback is
       F o phi = alpha^2 * delta^2 * R,   R a NONDEGENERATE (Morse) residual (Hessian rank 5, != 0),
       |det D phi| = alpha^3 * delta^2   (a PURE monomial in the divisors; the "unit" factor is a
       positive constant),
   and the chart threshold min((3+1)/2, (2+1)/2, 5/2) = 3/2 = 1/2 minAdm.  BINDING.
 - (2,2,2) u-chart: F o phi = alpha^2 u^2 * (bounded unit >0), |det Dphi| = alpha^3 u^2, threshold 3/2.
 - (3,3,4) corank-2 chart: a shared divisor delta divides EVERY product generator (the coupling),
   F o phi = delta^2 * (Morse rank 8), |det Dphi| = delta^3, threshold 2 = 1/2 minAdm(2,2,4).

Two structural facts I found: (i) the leaf integrand is (product of divisor monomials) TIMES a
RESIDUAL that is EITHER a bounded unit OR a nondegenerate (Morse) core of some rank rho -- it is NOT
a pure monomial; a per-leaf pure-monomial integrand omits the residual factor. (ii) the Jacobian is a
pure monomial in the divisors (times a bounded factor).

Banked tools available (name = Lean lemma): CoreShearMP.measurePreserving_coreShear (shear CoV, unit
Jacobian); S1NonMPTransport.weightedThreshold_transport (change-of-variables at the RLCT/threshold
level, with a general Jacobian Dpi) and rlctAtOn_boundedUnit_localHomeomorph (strip a bounded-unit
factor); RouteMSJRadialPolar / RadialInt (integral of ||x||^{-2c'} over a ball < infinity iff c' <
rank/2 -- the Morse/radial read; and lintegral_Ioc_rpow_lt_top for a single monomial axis). There is
NO banked elementary blow-up change-of-variables (monomial, non-unit Jacobian) at the Lebesgue-integral
level.

My questions:
 (Q1) What is the MINIMAL set of per-leaf data + hypotheses region_glue must gain so that it is
      provable (ties chartDom to the loss)? Give the fields and the two identities precisely.
 (Q2) The residual factor (bounded-unit OR Morse rank rho): how should it enter the finiteness
      threshold and the leaf-integrand definition? Is a per-leaf "residual rank" field the right
      encoding, or should the Morse residual be resolved into more divisors first?
 (Q3) For the per-chart change-of-variables (box integral = integral over source box of (F o phi)^{-c'}
      |det Dphi|), which is the cleaner route: (a) a direct Lebesgue Jacobian CoV per chart, or
      (b) route through the RLCT (rlctAtOn) using the banked transport + a compactness/scaling bridge
      to the box integral? Name the load-bearing missing lemma either way.
 (Q4) Does adding this bridge to the resolution bundle FORCE any new field on the tree/leaf carrier
      beyond a chart map + the two identities? What is most likely to be WRONG or incomplete in this
      bridge design, and the smallest instance that would expose it?
</task>

<output_contract>
  Answer Q1-Q4 in order, each a tight paragraph. For Q1 list the exact fields + the two identities
  (pullback, Jacobian) with their quantifiers/bounds. For Q3 pick (a) or (b) and name the missing
  lemma. For Q4 give ONE sharpest failure mode + the smallest concrete instance. Flag every claim as
  [proof-sketch you can defend] vs [heuristic/inference]. Do not write Lean. Be concrete.
</output_contract>

<grounding_rules>
  Reason from the setup; do not assume access to any paper. If you need a fact not given, mark it
  [assumed]. Distinguish proof from conjecture. If a question hides a false presupposition, say so.
  Disagreeing with the framing is useful.
</grounding_rules>
