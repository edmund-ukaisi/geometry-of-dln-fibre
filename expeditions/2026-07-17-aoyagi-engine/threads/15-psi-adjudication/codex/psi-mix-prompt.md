<task>
Independent geometry derivation. NO web/lookup; reason from the given structure only.

SETUP (Aoyagi 2023, DLN monomialization, a single blow-up node). We blow up a coordinate
subspace (the "center") of an affine space. The center coordinates at a "Case-1" node are:
  - a d-block of matrix entries d_ij  (i in 1..J1 rows, j in 1..(N) cols), AND
  - one extra existing divisor variable u.
So the center has codim  d_center = J1*N + 1  (the "+1" is u).

The blow-up is covered by its affine "pivot" charts, one per center coordinate. The pivot-p chart
covers the max-modulus sector { |x_k| <= |x_p| for all center coords k } and blows up:
x_p stays, every other center coord x_k = x_p * (ratio_k), |ratio_k| <= 1.

Aoyagi treats two chart TYPES differently (this is verbatim from pp.16-18):
  - Chart 1(1) = pivot on u:  every d_ij = u * d'_ij. No further coordinate change is applied.
  - Chart 1(2) = pivot on a d-entry (corner d_11 becomes a unit): after the blow-up, Aoyagi applies
    an upper-unitriangular matrix Q (clears the pivot's row) and a lower-unitriangular P (clears the
    pivot's column). Net effect on the residual block: the Schur-complement update
    d_ij  ->  d_ij - d_i1 * d_1j / d_pivot  (ratios fixed), i.e. a det-1 unipotent gauge; call it G_p.
    Different pivots p give DIFFERENT (conjugate) G_p; G_p != identity when the residual is >= 2x2.

We are formalizing the node cover in Lean. The current lemma writes each edge's local chart as
  localSub_e(w) = PSI( pivotChart_e(w) )
with ONE shared post-composition PSI (a homeomorphism of the ambient center-coord space), applied
AFTER each edge's own pivotChart, and states the cover as  cube ⊆ ⋃_e localSub_e(domain_e).

FACTS ALREADY ESTABLISHED (by exact rational/symbolic computation, do not re-derive, just use):
  - The PURE pivot family (all charts = pivotChart_e, no gauge) tiles the cube exactly.
  - Q,P give the Schur complement update above; it is det-1 unipotent; identity for the u-pivot.

ANSWER THESE FOUR, each from first principles, exact reasoning, small examples allowed:
  Q1. Consider the sector where u is the strict max modulus (all |d_ij| < |u|, u != 0), e.g. the
      u-axis {all d_ij = 0, u != 0}. Which pivot chart(s) cover it? Is chart 1(1) (u-pivot) required,
      or do the d-entry charts already cover this sector?
  Q2. Can a SINGLE ambient post-composition PSI reproduce every edge's actual local chart
      simultaneously (u-edge actual chart = pure blow-up; d-edges actual chart = G_p o blow-up)?
      Give the obstruction precisely, or exhibit the PSI.
  Q3. Suppose instead we allow a PER-EDGE gauge and model each chart as G_e o pivotChart_e (the gauge
      as a post-composition / target displacement), with G_u = identity and G_d = Schur. Does
      ⋃_e G_e(sector_e) still cover the whole cube, or can it leave a GAP? If a gap, give one explicit
      point (rationals) at a smallest node (take J1=2, N=2 so the d-block is 2x2, plus u) that lies in
      the cube but in none of the G_e(sector_e). Show it is interior (not on the cube boundary).
  Q4. There are two places the det-1 gauge can be attached: (a) as a target/ambient post-composition
      after the blow-up, or (b) as a reparameterization of the chart's SOURCE domain (so the chart is
      blow-up o alpha_e^{-1}, leaving the ambient IMAGE equal to the pure blow-up image). For each of
      {the cover being a clean tiling, the |det| Jacobian, the monomial exponents}, say which
      placement is correct/cleaner and why.
</task>

<output_contract>
  Four numbered answers (Q1-Q4). For Q3, an explicit rational point + the check that no G_e(sector_e)
  contains it. Keep each answer tight (a few sentences + the needed algebra). State any assumption you
  make. End with one line: the single place the det-1 gauge should live so the node cover is a clean
  tiling.
</output_contract>

<grounding_rules>
  Reason only from the structure above. Do not appeal to "the paper says it works" — derive whether
  the STATED Lean model (single shared PSI as target post-composition) is faithful, and where a gap
  would appear. Distinguish fact (your algebra) from conjecture. Small exact examples over prose.
</grounding_rules>
