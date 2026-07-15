<task>
I am formalising, in Lean 4 + Mathlib, a measure-theoretic DOMINATION inequality (call it SD-7) that arises
in an RLCT/codimension computation for deep linear networks. I need a decorrelated judgement on the SINGLE
decisive analytic question below: does the required finite constant `C` exist by a clean argument from the
banked pieces, or is there a hidden exponent-matching obstruction that would force new analysis?

BACKGROUND (all real-analysis; I have stripped the Lean).

Fix integers: u ≥ 1 (pivot rank), M0, M1 (with u = min(M0,M1) at the "saturated" cut, so a := M0−u and
b := M1−u satisfy min(a,b) = 0, i.e. a=0 OR b=0), M2, and a deep-tail matrix
  Z := deep-tail layer product, an M2 × N matrix, N = last width; Z depends on deep params.
Notation frobSq(X) = sum of squares of entries of X. c' is a real exponent with c' > (a·b)/2 = 0, so c' > 0.

THE INTEGRAND. Over the parameter A' of a chain (M1, M2, …, N) (a "tailChain"), write
  prod(tailChain A') = (A'_0) · Z',  where A'_0 is M1 × M2 and Z' is the shared deep tail M2 × N.
Pick u rows of prod(tailChain A') via an injection κ : Fin u ↪ Fin M1; call this u×N matrix Q_p (the "pivot
rows"). The block "freedSchurLoss" of the outer chart variables x = (P, B12, C) and a corank block Γ is:
  L(x,Γ,Q) = frobSq(P·(Q_p + P⁻¹·B12·Q_b)) + frobSq(C·(Q_p + P⁻¹·B12·Q_b) + Γ·Q_b),
where P is u×u (a UNIT, entries in [−1,1] box), B12 is u×b, C is a×u, Γ is a×b, and Q_b is the b corank rows.
At b=0: Q_b has 0 rows, so L = frobSq(P·Q_p) + frobSq(C·Q_p); Γ is a singleton (Fin a → Fin 0).
At a=0: C, Γ have 0 rows, so L = frobSq(P·Q_p) (only the pivot term).

THE LHS (shellSpineIntegrand) is:  ∫ over A' in [−1,1]-box ∩ {shell condition} ∫ over x=(P,B12,C) in
[−1,1]-box with P a unit ∫ over Γ in a shifted box  of  L(x,Γ,Q_p)^(−c').

THE RHS (target) is  C · comparatorIntegral, where
  comparatorIntegral = ∫ over z in [−1,1]-box (z parametrises a reduced chain (u, M2, …, N), with leading
  layer z_0 an u×M2 matrix and shared deep tail Z') ∫ over v in [0,1]  of
      |v|^(m−1) · ( v² · frobSq(prod(redChain z)) )^(−c'),   where prod(redChain z) = z_0 · Z' (u×N),
  and m := minAdm(redChain) is a specific nonnegative integer (the "reduced codimension"); m satisfies
  m ≤ u·M2 (a leading-dimension bound) but that is the only cheap bound I have; I do NOT have m ≤ u².

I MUST prove  LHS ≤ C · comparatorIntegral  with 0 < C < ∞, and I am told to use NONE of the "pivot
admissibility" hypotheses (in the general non-degenerate case one has a hypothesis hpiv: m ≤ u·(tail width);
here at min(a,b)=0 I am asserted to not need it).

BANKED, PROVED tools I can use:
 (T1) A radial polar blow-up: for a u×w block W and fixed w×N matrix Q, and measurable φ,
      ∫_{W ∈ ℝ^{u×w}} φ(frobSq(W·Q)) dW = ∫_{ω ∈ unit sphere S^{uw−1}} ∫_{r>0} r^(uw−1) · φ(r²·frobSq(Ŵ·Q)) dr dσ(ω),
      where Ŵ = reshape(ω). (Whole-space blow-up over ALL of ℝ^{u×w}; the box/unit constraints are NOT built in.)
 (T2) freedSchurLoss ≥ frobSq(P·Q_p)  (drop nonneg terms), giving  L^(−c') ≤ frobSq(P·Q_p)^(−c')  since c'>0.
 (T3) The deep tail Z' is SHARED between tailChain and redChain (dropHead identical).
 (T4) Enlarging a domain increases a nonneg integral (drop the shell restriction, drop C/B12 boxes to volume
      constants); box volumes are finite.

MY PLAN sketch: drop the shell + C-term (T2,T4) ⇒ LHS ≤ ∫_{A'-box}∫_{P-box, unit} frobSq(P·Q_p)^(−c') ·
(finite box-vol const). Then note P·Q_p = P·(κ-rows of A'_0)·Z' = W·Z' with W := P·(κ-rows of A'_0) an u×M2
matrix; and the comparator's core is frobSq(z_0·Z')^(−c'). So I want to change variables so W plays the role
of z_0 and pick up the radial v. My worry: the blow-up (T1) is over the FULL u×w block on ALL of ℝ^{u×w}
with weight r^(uw−1) and r over (0,∞); the comparator has weight |v|^(m−1) with v over [0,1] and z_0 over a
BOX. The exponents uw−1 vs m−1, the radial ranges (0,∞) vs [0,1], and the domains (unit-constrained boxed P
times boxed A'_0, vs boxed z_0) do NOT obviously line up. This is exactly where the general non-degenerate
proof needs hpiv (m ≤ u·tailwidth). I do not see why a FINITE C exists here without such an exponent bound.
</task>

<output_contract>
Answer in four short sections, decision-first:
 1. VERDICT (one line): Is `LHS ≤ C·comparatorIntegral` with finite C provable from the banked tools at
    min(a,b)=0, u≥1, WITHOUT any m-vs-exponent admissibility hypothesis? YES / NO / NEEDS-EXTRA-HYP.
 2. THE FINITE-C MECHANISM (or the obstruction): give the actual argument if YES — precisely how W = P·(κ-rows
    of A'_0) maps to (z_0, v), what change of variables realises it, and how the finite constant arises with
    the weight |v|^(m−1); OR if NO/NEEDS-EXTRA-HYP, exhibit the exponent inequality that must hold and argue
    whether it can fail at min(a,b)=0 (give a concrete (u,M1,M2,N,m) if it can fail).
 3. If YES: is the finite C independent of z, or does it require the comparator's own decLoss = v²·frobSq to
    ABSORB the pivot energy pointwise (i.e. is it a genuine CoV to the comparator, not a crude bound)? Name
    the cleanest sequence of the banked tools.
 4. LEAN-COST estimate: rough line-count band (e.g. 50 / 150 / 400) and the single hardest sub-step.
Be terse. Flag any step where you are INFERRING vs. certain.
</output_contract>

<grounding_rules>
This is pure real analysis; reason from the stated facts only. If a claim needs a fact I did NOT state
(e.g. a relation between m and u, M2), say so explicitly and mark it as a REQUIRED-BUT-UNSTATED assumption.
Do not assume I have any admissibility/finiteness hypothesis beyond m ≤ u·M2. Distinguish "this is forced"
from "this is plausible".
</grounding_rules>
