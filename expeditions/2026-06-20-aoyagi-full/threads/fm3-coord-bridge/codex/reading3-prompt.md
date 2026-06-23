<task>
Lean formaliser, DLN-RLCT formalisation. I am discharging a pinned interface `hnode` for a per-node
RLCT (real log canonical threshold) recursion. I found a subtlety that flips my earlier STOP and I
need you to red-team the NEW conclusion (not the old one).

SETUP. 2-factor square loss `L(A,B) = ‖A·B‖²_F`, A,B 2×2, deepest point A=B=0. A blow-up chart at
A-pivot a00: the flat coords y=(y0..y7) with A = [[y0, y0·y1],[y0·y2, y0·y3]] (the literal pivot
blow-up: a00=y0, a01=y0·y1, a10=y0·y2, a11=y0·y3), B=[[b00,b01],[b10,b11]] passes through.

The toolkit's `hnode` (the per-node "Schur presentation") wants, on a nbhd of 0, a coordinate split
(Fin nReg → ℝ) × Y and functions bcol, SΓ with:
  (1) flatCore w = (∑_j w.1_j²) + ∑_{i,j} (bcol_i · w.1_j + SΓ_{ij})²
  (2) G(w.2)² = ∑_{i,j} SΓ_{ij}²
  (3) ∑_i bcol_i² ≤ T²
and the toolkit then concludes  rlctAtOn(flatCore)(0) = nReg/2 + rlctAtOn(G²)(0)  via a "smooth block"
lemma: ∑_j w.1_j² over nReg coords contributes exactly nReg/2 (each regular squared coordinate = 1/2).

THE FINDING (sympy-verified, exact):
- Take w.1 := the literal blown-up PIVOT ROW Erow = row-0 of A·B = (y0(b00+y1·b10), y0(b01+y1·b11)).
  bcol := y2, SΓ := (y0(y3−y1y2)b10, y0(y3−y1y2)b11). Then conjunct (1) holds EXACTLY:
  L(blowup(y)) = Erow0² + Erow1² + (y2·Erow0 + SΓ0)² + (y2·Erow1 + SΓ1)². No leftover scalar factor.
  So as a BARE FUNCTIONAL EQUALITY, hnode conjunct 1 IS dischargeable for the full pulled-back loss.
- BUT Erow = (E0,E1) with E0 = y0(b00+y1·b10): each E vanishes to order ≥2 at the deepest point
  (product of y0 and a b-linear term). The Jacobian of (E0,E1) wrt the 8 ambient coords at 0 is the
  ZERO matrix (rank 0). So ∑_j w.1_j² = E0²+E1² is NOT a sum of nReg=2 independent regular squared
  coordinates near 0 — it is a sum of squares of degree-≥2 functions.

MY NEW CLAIM: The toolkit's "smooth block ⟹ nReg/2" step is UNSOUND when applied with this w.1,
because it assumes ∑_j w.1_j² is the regular form (RLCT nReg/2 = 1, here), but ∑(degree-2 funcs)²
has a LARGER RLCT-codimension contribution (the functions are not submersive). The known correct
answer for (2,2,2) three-layer is RLCT 3/2; a "conserve nReg/2 per node with regular blocks" recursion
that treats E0²+E1² as 2 regular coords would overcount the regular part / undercount the singular
part. Concretely: rlctAtOn(E0²+E1²)(0) ≠ 2/2 = 1 because (E0,E1) is not a submersion at 0.

THE QUESTION FOR YOU:
A. Is my new claim correct — that conjunct 1 holds as a bare equality BUT the downstream "nReg/2 from
   the smooth block" is unsound because w.1 := Erow is not a regular (submersive) coordinate system at
   the deepest point? Decide from the algebra.
B. Is there a DIFFERENT honest choice of the coordinate split (Fin nReg → ℝ) × Y near 0 — i.e. w.1 a
   genuine regular coordinate system (submersive, Jacobian full rank at 0) — for which conjunct 1
   holds for L∘blowup? Or does homogeneity (L is degree-2 in A, the blow-up makes the whole A-row a
   multiple of y0) FORCE any conjunct-1 split to use non-regular w.1?
C. Compute / bound rlctAtOn(E0²+E1²)(0) for E0=y0(b00+y1 b10), E1=y0(b01+y1 b11) to confirm it is NOT
   1 (= 2·(1/2)). A heuristic Newton-polytope / weighted-homogeneity estimate is fine; flag it as an
   estimate.
</task>

<output_contract>
3 sections A, B, C. Terse. For A: YES/NO + the one-line reason from the algebra. For B: the explicit
alternative split if one exists, else "FORCED non-regular by homogeneity, here's why". For C: a number
or bound for rlctAtOn(E0²+E1²)(0) with the method named, flagged estimate-vs-exact.
</output_contract>

<grounding_rules>
You do NOT have the repo. Reason from the algebra given. Flag INFERENCE vs algebra-forced. Do not
invent toolkit internals beyond the "smooth block ⟹ nReg/2" semantics stated. If C needs a fact you
can't derive, name it.
</grounding_rules>
