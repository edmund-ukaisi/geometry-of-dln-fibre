<task>
Adjudicate whether an "iterated-fibre" upper-bound method reaches the sharp RLCT threshold for a
deep-linear-net loss, or only a weaker bound. This decides a Lean proof route.

SETUP. F = ‖A^(0)·A^(1)·…·A^(L-1)‖_F² (product of matrices, A^(s) is M_s × M_{s+1}), near A=0,
flat box (−1,1)^N. Want, for c' < rlct(F), ∫_box F^{−c'} < ∞ (the upper bound). rlct(F) = ½·minAdm(M)
where minAdm(M)=min over admissible paths T of Σ_j (t_{j−1}−t_j)(M_{j+1}−t_j), t_0=M_0, t_L=0.

THE ITERATED-FIBRE METHOD (just built, S2-free). A reusable per-layer "fibre" bound:
  FIBRE LEMMA: for fixed Y (n×q), ∫_{X∈box (p×n)} frobSq(X·Y)^{−c'} dX ≤ const(p,n,q) · frobSq(Y)^{−c'},
  FINITE iff c' < p/2 (p = #rows of the LEFT factor X). [Proof: frobSq(X·Y) ≥ (Y_{ℓj})²·Σ_i u_i² for
  the max-abs entry (ℓ,j) of Y and the per-row shear u_i (det-1 MP in X); (Y_{ℓj})² ≥ frobSq(Y)/(nq);
  the u-fibre is a p-dim Morse, ∫ (Σu_i²)^{−c'} < ∞ iff c' < p/2 (radial). So the X-integral is bounded
  by a Y-independent const times frobSq(Y)^{−c'}, threshold p/2.]
  ITERATE outside-in: ∫_{A0}∫_{A1}…∫_{A_{L-1}} F^{−c'} ≤ C0·C1·…·∫_{A_{L-1}} frobSq(A_{L-1})^{−c'},
  peeling A0 (X=A0, Y=A1…A_{L-1}, threshold M_0/2), then A1 (threshold M_1/2), …, terminal A_{L-1}
  is a Morse block frobSq over M_{L-1}·M_L entries (threshold M_{L-1}·M_L/2).
  So the method's GUARANTEED finiteness threshold is  iterfibre(M) = min( min_{s=0}^{L-2} M_s/2 ,
  M_{L-1}·M_L/2 ).

MY EXACT FINDING. iterfibre(M) vs ½·minAdm(M):
  (4,4,2,2): both 2 (MATCH); (2,1,2): both 1 (MATCH).
  (2,2,2): iterfibre 1 vs ½·minAdm 3/2 (WEAKER); (2,2,4): 1 vs 2; (3,3,4): 3/2 vs 4; (3,3,3): 3/2 vs 7/2;
  (3,3,3,3): 3/2 vs 3; (4,4,4): 2 vs 6; (5,3,4): 5/2 vs 11/2. ALL WEAKER except the two MATCH cases.
So the naive iterated-fibre gives min_s M_s/2 (the smallest left-factor row count over 2), which is
generically STRICTLY BELOW ½·minAdm. It matches only when min_s M_s/2 happens to equal ½·minAdm
(e.g. (4,4,2,2): the leaf 2×2 binds at 2 = both).

QUESTIONS:
  (1) Is my threshold accounting for the iterated-fibre method correct — is the per-peel threshold
      really M_s/2 (the left-factor row count), independent of the rank/structure of the residual Y?
      The fibre lemma uses only ONE max column of Y and the per-row shear; it does NOT see Y's rank.
  (2) Can the iterated-fibre method be REFINED to reach ½·minAdm — e.g. by (a) choosing the peel order
      differently, (b) peeling COLUMNS not rows (transpose), (c) a smarter fibre bound that sees more
      than one column of Y, (d) interleaving with rank-stratification on Y — or is min_s M_s/2 a
      genuine CEILING of the single-column-shear fibre method?
  (3) Net: does iterated-fibre GENERALIZE to ½·minAdm for all M (if so, how), or is it strictly weaker
      at the corank-≥2 binding (where the true rlct = ½·minAdm exceeds min_s M_s/2)? If weaker,
      characterize exactly the M-class where iterfibre(M) = ½·minAdm (so it suffices there) vs where it
      undershoots (needing the rank-stratified coupled resolution).
</task>

<output_contract>
1. Confirm/correct the per-peel threshold M_s/2 and the iterfibre(M) = min(M_s/2, terminal) formula.
2. Can it be refined to ½·minAdm (which refinement), or is min_s M_s/2 the ceiling of the method?
3. The M-class where iterfibre = ½·minAdm (suffices) vs undershoots (needs rank-stratified). Derived
   vs conjectured.
</output_contract>

<grounding_rules>
- The fibre lemma threshold p/2 is the u-fibre Morse dimension (p rows), exact.
- ½·minAdm is the true rlct (literature/Aoyagi). iterfibre ≤ rlct always (it's an upper bound on the
  integral via a lower bound on F, so a valid but possibly-loose finiteness threshold).
- A WEAKER finiteness threshold (iterfibre < ½·minAdm) means the method proves ∫F^{−c'}<∞ only for
  c' < iterfibre, NOT up to ½·minAdm — so it does NOT prove rlct ≥ ½·minAdm. That's the failure mode.
- Reason adversarially; I want to know if the clean iterated-fibre route actually suffices.
</grounding_rules>
