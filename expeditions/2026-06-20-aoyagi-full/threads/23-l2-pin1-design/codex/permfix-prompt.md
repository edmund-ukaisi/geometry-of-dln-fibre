<task>
Adjudicate (independently, from scratch) whether a proposed "pivot-aligned permutation" fix makes a
specific linear map F invertible, and what the genuine fix is if it does not. Work the exact algebra.
Do NOT trust the framing's hints; derive F and its invertibility yourself.
</task>

<context>
A formalisation (Lean) of deep-linear-network loss geometry needs a local diffeomorphism at a "deepest"
critical point. The crux: a constant linear map F (the strict derivative at 0 of a "regular-slice"
residual map) must be an invertible continuous-linear-equivalence on R^nReg.

SETUP (verified facts):
- L layers (L >= 2). Hidden dims H_0,...,H_L. Rank r, with r <= H_s for all s. Target matrix B is
  H_0 x H_L of rank exactly r.
- The "deepest point" has, per layer s, a rank-exactly-r matrix; interior layers equal the corner
  corM = diag(I_r, 0); the FIRST layer's tail columns vanish (so it = U·projM, U full col rank), the
  LAST layer's tail rows vanish (so it = embM·V, V full row rank), where B = U·V is the rank-r factor.
- A per-layer frame (P_s, Q_s) (constant, invertible) carries each deepest layer to corM:
  P_s · (layer_s) · Q_s = corM. For L>=2 the boundary frames satisfy Q_first = I and P_last = I.
- Write A := reindex(P_first) and B := reindex(Q_last) in r ⊕ (·-r) block form:
  A = [[A11,A12],[A21,A22]], B = [[B11,B12],[B21,B22]].  A is invertible (P_first is a unit).
- The residual map's reg-slice derivative, after the genuine quadratic cross-terms are killed
  (their strict derivative at 0 is 0), has been computed to the LINEAR block map, in residual-block
  order (P11-I, P12, P21), as a function of the gauge linear coordinates (X : r×r, Y : r×(H_L−r),
  Z : (H_0−r)×r):
      F(X,Y,Z) = ( A11·X + A12·Z + B21·Y ,   B22·Y ,   A21·X + A22·Z ).
  [You should re-derive / sanity check this block structure yourself from the corner-sandwich product
   of a first-layer X/Z deviation and a last-layer Y deviation, frame-conjugated; interior layers are
   the idempotent corner.]
- The last-layer frame Q_last is whatever the "right-only rank normal form" lemma produces: it is SOME
  invertible Q with (embM·V)·Q = corM. We do NOT get to pick it; the construction picks one.

THE PROPOSED FIX (to adjudicate, NOT to assume correct):
"A B-determined pivot-aligned PERMUTATION of the residual pack's output coordinates: permute so that
B's ACTUAL pivot columns align with the pack structure, giving B22 = I (or invertible), hence F
invertible. Claimed measure-preserving + RLCT-preserving (just a coordinate permutation)."

There are KNOWN refuted prior fixes (do not re-propose): (1) strengthening the right-only normal-form
lemma to force B22 invertible is impossible (counterexample r=1, last layer = [0,1]); (2) requiring the
last layer's first r columns independent silently restricts the target B (forces B's first r columns
independent, excluding valid rank-r B like r=1, B=[0,b]).
</context>

<questions>
(a) Compute / confirm: for which A, B is F (as a linear map R^nReg → R^nReg, domain (X,Y,Z), codomain
    the three residual blocks) invertible? Express the determinant/rank condition exactly.
(b) Is a PERMUTATION of F's OUTPUT coordinates (a permutation matrix acting on the residual-block
    entries the loss sums) able to change whether F is invertible? Give the exact reason.
(c) The fix says "permute so B's pivot columns align". Identify precisely WHICH object the permutation
    must act on for it to be non-inert (F's outputs? the column-split of the last interface that
    defines the r⊕(H_L−r) block decomposition of B? the frame choice?). For each candidate, state
    whether it can make B22 invertible AND whether it changes F's invertibility.
(d) If the permutation must act on the column-split of the last interface (relabel which columns are
    "pivot"): does that propagate through the WHOLE telescoping matrix product and the corner corM, and
    does it interact with a separate requirement that the TARGET B itself gauge-normalize as
    reindex(P0·B·QL) = diag(I_r,0) with the SAME first-r pivot? Could a B-determined column permutation
    be inconsistent between the last-layer frame and the target-B normalization?
(e) Net: does the proposed permutation fix actually make F invertible for ALL rank-r targets B without
    restriction, or is there a residual obstruction? If it works, give the explicit permutation and the
    invertibility argument. If it does not, identify the genuine minimal fix.
</questions>

<output_contract>
- Lead with a one-line verdict for (b) and (e): does an output permutation work? does the column-split
  permutation work for all B?
- Show the exact algebra for (a) (the determinant of F).
- Be explicit about the distinction between permuting outputs vs. permuting the column-split.
- Mark each statement Fact (you derived it) vs Inference (plausible but unverified).
- If you identify a genuine fix, give it concretely (the map + why F becomes invertible).
</output_contract>

<grounding_rules>
- Exact algebra only. Symbolic / block-matrix reasoning. No floating point.
- Re-derive F yourself; don't take the given block form on faith — confirm or correct it.
- Do not assume the proposed fix is correct. Adjudicate it.
</grounding_rules>
