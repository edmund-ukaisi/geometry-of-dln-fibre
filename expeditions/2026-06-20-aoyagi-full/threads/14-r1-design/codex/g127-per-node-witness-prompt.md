<task>
Adjudicate ONE truth-value (a WITNESS or OBSTRUCTION) with exact reasoning. Do NOT run code.

SETTING. The R1 resolution of the matrix-chain zero-core dlnLoss M 0 = ||prod(C)||^2 recurses: each
PER-NODE chart blows up a rank-stratum center (making a pivot a HARD constant 1), then STRAIGHTENS via a
Schur transvection, then recurses on a smaller zero-core. fm-2's `schur_straighten_exists` (the crux) is
the per-node straighten. The question: does the (u_i, ψ_i) adapted-basis transvection straighten work AT
A REDUCED CHAIN's node (not just the outer/top chain), with the hard-1 pivot supplied by the blow-up?

FACTS I established by EXACT computation, WITNESSED on a reduced node of (3,3,3):
- Top (3,3,3) zero-core ||A1 A2||^2 at origin: all generators bilinear, Jacobian rank 0 (no regular
  block, no unit pivot) — so the straighten cannot run at the raw origin; a blow-up is needed first.
- Blow up {A1=0}: A1 = x·Â, Â = [[1,p,q],[r,s,t],[u,v,w]] with Â[0,0] = 1 a HARD constant. F = x²·||Â A2||^2.
  This ||Â A2||^2 (Â[0,0]=1 hard) is the REDUCED NODE's input.
- The (u_i,ψ_i) adapted basis at this reduced node = the hard-pivot row/col TRANSVECTIONS:
  L = [[1,0,0],[-r,1,0],[-u,0,1]] (clear col 0), R = [[1,-p,-q],[0,1,0],[0,0,1]] (clear row 0). Both
  det = 1 (TRANSVECTIONS, measure-preserving) — because the pivot is a HARD 1 (no division).
  L·Â·R = blockdiag[1, S], S = [[s-pr, t-qr],[v-pu, w-qu]] the reduced 2x2 Schur chain factor.
- The LOSS-level identity, witnessed (diff = 0 exact): ||Â A2||^2 straighten = [regular pivot row,
  the 3 entries of row 0 of Â A2] + ||S · A2red||^2, where A2red = rows 1,2 of A2 and S·A2red is a
  genuine smaller zero-core (a (2,*,3)-shaped reduced chain) — the next recursion node.
- So the per-node interface is: [blow-up supplies hard-1 pivot] → [transvection straighten, det=1, MP] →
  [regular pivot row + smaller zero-core ||S·A2red||²] → recurse. Witnessed on (3,3,3)'s reduced node,
  matching the (2,2,2) anchor's step1Residual_eq_resolvedForm pattern.
</task>

<sub_question>
1. Is the per-node (u_i,ψ_i) adapted-basis transvection straighten a WITNESS (works at a reduced chain's
   node, hard-1 pivot from the blow-up → det=1 transvection → regular + smaller zero-core) — confirmed on
   the (3,3,3) reduced node above — or is there an OBSTRUCTION at some reduced node (a node where the
   hard-1 pivot is NOT available, or the straighten is not a transvection, or the residual is not a
   smaller zero-core)?
2. The hard-1-pivot interface: does the blow-up ALWAYS supply a hard-1 pivot at every reduced node (so
   the straighten is always a det=1 transvection, never a unit-Jacobian division), or can a reduced node
   arise where no rank-stratum blow-up gives a hard pivot? (Consider: at a reduced node the chain is
   smaller but still a zero-product core; its origin again has all-bilinear generators, so the same
   blow-up-first applies. Confirm this recurses uniformly.)
3. Is the residual ||S·A2red||^2 genuinely the SAME class (a smaller matrix-chain zero-core dlnLoss M' 0)
   so the recursion closes, with ΣM' < ΣM? (The witness shows S·A2red is a (2,*,3) chain product = a
   smaller zero-core.)
4. Verdict for fm-2's schur_straighten_exists: WITNESS (the per-node adapted-basis transvection straighten
   is exhibited + uniform across reduced nodes, hard-1 from the blow-up, det=1 MP, smaller-zero-core
   residual) or OBSTRUCTION (with the specific reduced node where it breaks).
</sub_question>

<output_contract>
- Verdict: WITNESS (per-node adapted-basis transvection straighten works at reduced nodes) or OBSTRUCTION.
- Confirm/refute the hard-1-pivot interface (blow-up always supplies it; straighten always a det=1 transvection).
- Confirm/refute the residual is a smaller zero-core (recursion closes, ΣM'<ΣM).
- FACT vs INFERENCE labels.
</output_contract>

<grounding_rules>
- Ground in the facts above + standard resolution / linear algebra (Schur complement, transvections,
  blow-up of a coordinate-subspace rank stratum). Reason on paper ONLY; do NOT read files or run code.
- A "transvection" = an elementary row/col op x_i += λ x_j, det = 1, measure-preserving. A hard-1 pivot
  means the pivot entry is the constant 1 (so clearing its row/col needs no division).
- Preserve FACT vs INFERENCE. Name any hypothesis a claim needs.
</grounding_rules>

<important>
You have NO file, shell, or code access. Do not call any tool. Produce only the reasoned adjudication.
</important>
