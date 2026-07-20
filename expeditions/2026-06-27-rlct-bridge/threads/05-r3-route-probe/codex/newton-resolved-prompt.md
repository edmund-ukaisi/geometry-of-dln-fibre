<task>
A deep linear network loss at the deepest (origin) stratum is
    K(A1,...,AN) = || A_N A_{N-1} ... A_1 ||_Frobenius^2,
each A_i a real matrix (composable widths d_0,...,d_N), a sum of squares of the entries of the
matrix product. We want the REAL log canonical threshold (RLCT / learning coefficient) at the
origin, and specifically: which RESOLUTION-OF-SINGULARITIES strategy is needed to PROVE the lower
bound lct(K) >= c (equivalently rlct >= c/... ), where c is the known value.

ESTABLISHED FACTS (do not re-derive, but you may use):
1. K in the STANDARD coordinates is Newton-DEGENERATE: its homogeneous Newton face vanishes on the
   real torus (explicit all-nonzero point with A_N...A_1 = 0 exists), so the naive Newton-polyhedron
   (Kushnirenko-Varchenko) bound is NOT tight. A single Saito-Varchenko/Kushnirenko theorem applied
   in the ORIGINAL coordinates fails.
2. After an SVD/rank change of coordinates (write each A_i = rho_i U_i; radial threshold is
   non-binding), the singularity is governed by an ANGULAR model at the rank-bottleneck stratum.
3. For the all-width-2 chain (d = (2,2,2,2,2), composite = 0), the deepest local model, after
   eliminating Morse directions, is  w1^2 + w2^2 + delta^2*(s^2 + v^2)  -- a MONOMIAL sum of squares
   (monomials delta*s, delta*v), local rlct 3/2.
4. A 2-layer reduced-rank core ||Delta * S||^2 with Delta free 2x2, S free 2x4 (the "(2,2,4) core",
   which appears as a residual when a layer drops rank by 2 with both ambient dims >= 3) is ALSO
   Newton-degenerate in its own entry coordinates, but becomes a monomial sum of squares
   ||P||^2 + e^2 ||Q||^2 only AFTER a radial blow-up Delta = a*Mhat PLUS a nonlinear SHEAR coordinate
   e = w - v*u (Mhat = [[1,u],[v,w]]).

THE QUESTIONS:
Q1. For the all-width-2 chain (2,2,2,2,2) at the origin: is the resolution achievable as a sequence
    of L-1 = 4 STANDARD monomial/incidence blow-ups (one per layer), each leaving a residual that is
    Newton-NONDEGENERATE (so a single citable monomial/toric RLCT theorem discharges each step) --
    OR does even this all-width-2 case require a bespoke recursive blow-up with accumulated divisor
    bookkeeping?
Q2. For GENERAL composable widths (allowing d_i >= 3, so a layer can drop rank by >= 2 with both
    ambient dims >= 2 -- a genuine PARTIAL corank>=2 drop, e.g. inside a (3,3,4) chain): can the
    SAME uniform "monomial-blow-up-per-layer" scheme work, or does the corank>=2 partial-drop residual
    ||Delta*S||^2 force a chart-dependent nonlinear (shear) coordinate change whose monomial support
    depends on which exceptional variable multiplies which generator (a "diag(b)"-type accumulated
    invariant)?
Q3. NET: can the lower bound lct(K) >= c for general DLN widths be discharged by ONE citable
    theorem (e.g. Newton-nondegeneracy in a single uniformly-described resolved chart, or a clean
    per-layer monomial induction), or does it genuinely require Aoyagi's bespoke recursive real
    blow-up (case split on the rank-drop pattern, accumulated divisor exponents)?
</task>

<output_contract>
1. FIRST: a direct verdict on Q1 (all-width-2): VIABLE-as-uniform-monomial-tower vs NEEDS-bespoke.
2. Then Q2 (general widths >= 3, partial corank>=2): does the uniform scheme survive, and if not,
   pinpoint the exact obstruction (what makes the corank>=2 residual not monomially nondegenerate in
   any uniform chart).
3. Then Q3 NET verdict + the single most load-bearing reason.
4. If a per-divisor inequality structure exists (multiplicities (k_j,h_j), inequality h_j+1 >= c*k_j),
   state it; if instead it reduces to a combinatorial min over rank profiles, say so.
5. Confidence + the single most likely way the verdict is wrong.
</output_contract>

<grounding_rules>
- Exact algebra reasoning only. If you assert nondegeneracy or degeneracy, give the torus-critical-point
  reasoning (Kushnirenko-Varchenko face condition), not a hand-wave.
- A "sum of squares of monomials" is Newton-nondegenerate; a "sum of squares of forms sharing a rank
  degeneracy" is typically Newton-degenerate. Use this.
- Distinguish: (a) one chart with a nondegenerate Newton polyhedron; (b) a tower of clean monomial
  blow-ups, one citable theorem per step; (c) a bespoke recursive blow-up with accumulated/coupled
  divisor data. These are three different answers.
- Do NOT assume a target verdict; derive it. Read-only sandbox: reason analytically, do not run code.
</grounding_rules>
