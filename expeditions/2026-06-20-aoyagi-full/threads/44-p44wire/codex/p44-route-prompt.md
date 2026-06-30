<task>
I am formalising in Lean 4 / Mathlib a result about the real log-canonical threshold (RLCT) of the
loss of deep linear networks. I need a decorrelated soundness check on a PROOF-ROUTING decision before
I sink effort. This is a pure mathematics + proof-architecture question; no Lean syntax needed.

SETUP (the objects, stated mathematically):
- Fix layer widths H : {0,...,L} → ℕ and a rank r ≤ H_s for all s. L = 2 (depth-2).
- B is an (H_0 × H_L) real matrix of rank exactly r (the "target" of the multiplication map).
- "Params H" = the space of weight tuples (A_1, ..., A_L), A_s an (H_{s-1} × H_s) matrix.
  The "product map" prod : Params H → (H_0 × H_L matrices) sends (A_s) ↦ A_1···A_L.
- dlnLoss H B (A) = ‖prod(A) − B‖²_Frobenius (the square loss). It is ≥ 0, a polynomial in the entries.
- rlctAt H (dlnLoss H B) w = the LOCAL RLCT (real log canonical threshold) of the loss germ at the
  point w ∈ Params H. This is a LOCAL invariant of the function germ at the single point w.
- "deepestPoint H r B" is a SPECIFIC point of Params H defined as Classical.choice of an existence
  proof: it is SOME tuple with every layer A_s of rank EXACTLY r and prod = B. It is an arbitrary
  witness of the predicate "IsDeepLayers" (all layers rank exactly r, product = B). Crucially it is
  NOT a canonical/natural function of B — it is an arbitrary choice.

THE TARGET (a per-B pointwise statement, call it NF(B)):
    rlctAt H (dlnLoss H B) (deepestPoint H r B) = nReg/2 + lambdaCore(M)
  where nReg = r(H_0 + H_L − r), M_s = H_s − r (reduced widths), and lambdaCore(M) is a closed-form
  rational depending only on M (NOT on B). The RHS is permutation-invariant in B (does not see which
  columns/rows of B are pivots).

WHAT I HAVE BANKED (proven, sorry-free):
(A) A "gauge chart construction" that PROVES NF(B) — BUT only under two extra hypotheses on B:
    - hJfront: B's r pivot COLUMNS are the FIRST r columns (the B-determined pivot embedding equals
      the front embedding k ↦ k).
    - htop: B's top r ROWS have full rank r (the leading r×r-ish block is nonsingular).
    Call a B satisfying both "front-aligned". For a front-aligned B, NF(B) is PROVEN.
(B) A PERMUTATION machinery: for any column permutation P and row permutation R, with
    Bpr = B.submatrix R P (i.e. B with rows permuted by R and columns by P), there is a HOMEOMORPHISM
    τ of Params H (a relabelling of the weight tuples induced by R,P) such that:
       dlnLoss H Bpr (τ w) = dlnLoss H B w   for ALL w ∈ Params H   (loss invariance), and hence
       rlctAt H (dlnLoss H Bpr) (τ w) = rlctAt H (dlnLoss H B) w    for ALL w   (pointwise RLCT transfer).
    [This pointwise transfer is REAL and proven (it is the inner step of an infimum-WLOG lemma).]
(C) An existence: for any rank-r B there EXIST permutations P, R making Bpr front-aligned (so NF(Bpr)
    holds by (A)).

THE ROUTING I WANT TO CHECK:
  Goal: prove NF(B) for an ARBITRARY rank-r B (no front-alignment assumption).
  Proposed chain:
    1. Pick P,R from (C) so Bpr is front-aligned.
    2. NF(Bpr) holds by (A):  rlctAt H (dlnLoss H Bpr) (deepestPoint H r Bpr) = nReg/2 + lambdaCore(M).
       [note nReg, M are permutation-invariant, identical for B and Bpr.]
    3. From (B): rlctAt H (dlnLoss H Bpr) (τ (deepestPoint H r B)) = rlctAt H (dlnLoss H B) (deepestPoint H r B).
    4. Want to conclude rlctAt H (dlnLoss H B) (deepestPoint H r B) = nReg/2 + lambdaCore(M).

THE GAP I SEE:
  Step 3 gives the value of rlctAt(dlnLoss Bpr) at the point τ(deepestPoint B). Step 2 gives the value
  at the point deepestPoint(Bpr). To stitch them I need
       rlctAt H (dlnLoss H Bpr) (τ(deepestPoint H r B)) = rlctAt H (dlnLoss H Bpr) (deepestPoint H r Bpr),
  i.e. the RLCT of the SAME loss (dlnLoss Bpr) is the same at the two points τ(deepestPoint B) and
  deepestPoint(Bpr). Both points are deepest-layers points for Bpr (τ carries a deepest point of B to
  a deepest point of Bpr since τ is a relabelling preserving the all-rank-r condition; and
  deepestPoint Bpr is one by construction). But they are DIFFERENT points in general (deepestPoint is
  an arbitrary Classical.choice). So I need: the local RLCT of dlnLoss Bpr is CONSTANT across all
  deepest-layers points (a GL×GL gauge-orbit invariance of the local RLCT).
</task>

<output_contract>
Answer these, in order, terse:

1. Is the GAP I identified real and load-bearing — i.e., is the proposed chain INCOMPLETE without a
   "local RLCT is constant across all deepest-layers points" lemma (gauge-orbit invariance of the
   local RLCT at the deepest stratum)? Yes/No + one-sentence why.

2. Is that gauge-orbit-invariance lemma TRUE mathematically (RLCT constant on the GL_{H_0}×···×GL_{H_L}
   gauge orbit, and all deepest-layers points lie in one orbit)? Give the mathematical reason
   (group action by analytic isomorphisms preserving the loss up to a diffeomorphism ⟹ RLCT invariant),
   and flag any condition under which it could FAIL.

3. Is there a CHEAPER route that AVOIDS proving gauge-orbit invariance? Specifically: can I instead
   prove NF for the SPECIFIC point τ(deepestPoint B) directly — i.e., re-state/should the target NF be
   keyed to "the point τ(deepestPoint B)" rather than "deepestPoint Bpr"? Or alternatively, is the
   honest minimal move to state NF only for front-aligned B (a scoped theorem) and let the
   permutation-WLOG be applied by the DOWNSTREAM consumer at the infimum (⨅ over the optimal set) level,
   where a BijOn-congruence already handles the point-matching without needing orbit invariance at a
   single point?

4. Bottom line: is "prove NF(B) for arbitrary B at its own arbitrary deepestPoint" WIRING-BOUNDED given
   what I have (A,B,C), or does it REQUIRE new mathematics (the gauge-orbit invariance of the local
   RLCT, which is not in A/B/C)? One word (WIRING / NEW-MATH) + 2 sentences.
</output_contract>

<grounding_rules>
- Distinguish clearly: claims you can justify mathematically vs. inferences about my Lean setup you
  cannot verify. I only need the mathematics + proof-architecture judgement.
- Do NOT assume deepestPoint is natural in B; treat it as an arbitrary Classical.choice witness.
- If the answer to (4) is NEW-MATH, say so plainly — do not soften it.
</grounding_rules>
