<task>
I am adjudicating whether one remaining gap in a Lean formalisation is (A) a bounded
structural generalisation of an already-completed special case, or (B) an intrinsic
new-mathematics wall. I want an INDEPENDENT judgement + any counterexample you can find.
Answer the mathematical question; do not assume my framing is right.

SETTING (deep linear network RLCT, at the "deepest point" of a fibre).
- Chain of L square-ish "layer" matrices C_0,...,C_{L-1}. Each C_s is block 2x2 in blocks
  (r) + (M_s):   C_s = [[ I_r + X_s , Y_s ],[ Z_s , T_s ]].
- At the "deepest point" ALL blocks vanish: X_s=Y_s=Z_s=T_s=0, so C_s(0)=blockdiag[I_r,0].
- Per-layer Schur core:  S_s := T_s - Z_s (I_r+X_s)^{-1} Y_s   (so S_s(0)=0).
- Global object: Rcore := Schur complement of the (1,1)-block of the product P := C_0 C_1 ... C_{L-1},
    Rcore = P_22 - P_21 (P_11)^{-1} P_12.   (P_11(0)=I_r invertible near 0.)
- Two candidate "core" functions on the parameter space near 0:
    Score(w)  := ||Rcore||_F^2                (global Schur, Frobenius sq)
    corePhi(w):= ||S_0 S_1 ... S_{L-1}||_F^2   (Frobenius sq of the PRODUCT of per-layer Schur cores)
- RLCT (real log canonical threshold) is a LOCAL invariant at 0; it is invariant under an
  analytic/smooth LOCAL DIFFEOMORPHISM of the coordinates (change of variables), and under
  multiplication of the function by a strictly-positive analytic unit.

WHAT IS ALREADY DONE (L=2, and general-L loss side):
- For L=2 the identity Rcore = S_0 (I - K) S_1 with K = Z_1 (P_11)^{-1} Y_0 is proven, and the
  RLCT bridge  rlctAtOn(Sreg + Score) = rlctAtOn(Sreg + corePhi)  is proven at 0, via a LOCAL
  diffeomorphism Psi: S_1 |-> (I-K) S_1 (holding a separate "regular" term Sreg fixed) plus a
  local-diffeo RLCT-invariance lemma. Here K depends only on the "regular" blocks (X,Y,Z), NOT on
  the cores, at L=2.
- For GENERAL L the loss-side sandwich  c1(Sreg+Score) <= loss <= c2(Sreg+Score)  is ALREADY proven
  (sorry-free). So the ONLY remaining general-L gap on this line is the RLCT-equality bridge
      (GOAL)   rlctAtOn(Sreg + Score) = rlctAtOn(Sreg + corePhi)   at 0, for all L >= 3.

FACTS I HAVE ESTABLISHED (exact symbolic + exact-rational checks; please independently sanity-check
the logic, and probe for holes):
(F1) Recursive 2-factor Schur LDU: Schur(A*B) = Schur(A) * (I - K) * Schur(B),
     with K = B_21 (AB)_11^{-1} A_12,  and (I-K)(0)=I.   [verified r,M in {1,2}, random near-0 rationals]
(F2) Iterating F1 over the chain gives
       Rcore = S_0 (I-K_1) S_1 (I-K_2) S_2 ... (I-K_{L-1}) S_{L-1},
     where K_k = (C_k)_21 (P_k)_11^{-1} (P_{k-1})_12,  each analytic near 0, each (I-K_k)(0)=I.
     [verified matrix, non-commutative, L=3,4, r,M in {1,2}]
(F3) For k>=2, K_k DOES depend on the cores T_j (j<k), because off-diagonal blocks of partial
     products carry core factors, e.g. (C_0 C_1)_21 = Z_0(I+X_1) + T_0 Z_1. So the L=2 fact
     "K is core-independent" does NOT lift.
(F4) Define the coordinate map on the core block:  Psi(S_0,...,S_{L-1}) := (S_0, (I-K_1)S_1, ...,
     (I-K_{L-1})S_{L-1}), holding regular/spectator coords fixed. Then Rcore = product of Psi's
     components, so  Score = corePhi ∘ Psi.
(F5) The Jacobian of Psi at 0 is the IDENTITY. I computed d(Psi_i)/dS_j (0) = delta_ij and the
     derivative in every regular direction = 0, EVEN THOUGH K_k depends on cores — because every
     cross term carries a factor S_i(0)=0. [verified symbolically, L=3, scalar r=M=1, expressing
     cores through the chart coords.]
</task>

<output_contract>
Answer these, each with an explicit label PROOF / STRONG-ARGUMENT / HEURISTIC / COUNTEREXAMPLE /
UNSURE, and keep fact vs. inference separate:
1. Is F1 (the 2-factor Schur-product LDU with that specific K) a correct matrix identity? Give the
   cleanest reason or a counterexample.
2. Given F2+F4+F5, does the GOAL rlctAtOn(Sreg+Score)=rlctAtOn(Sreg+corePhi) at 0 follow for all L,
   PURELY by "Psi is a local diffeo at 0 (dPsi(0)=I) => RLCT-invariance"? State precisely what must
   still be checked for Psi to be a genuine local C^∞ diffeomorphism on a neighbourhood of 0 in the
   FULL coordinate space (not just dPsi(0)=I): smoothness of the (P_k)_11^{-1} factors, whether the
   core-dependence of K_k threatens invertibility off 0, domain issues, the Sreg term staying fixed.
3. Is there any obstruction that appears ONLY at L>=3 and has NO analogue at L=2 — i.e. something
   that makes this a genuinely new construction rather than "same local-diffeo mechanism applied to
   a recursively-defined Psi"? Consider especially: non-commutativity of the interspersed units,
   nested inverses (P_k)_11^{-1}, the coupling K_k depending on cores.
4. Net verdict: is closing the GOAL for all L a BOUNDED structural generalisation of the L=2
   construction (reusing local-diffeo RLCT-invariance + a recursive LDU induction), or does it
   require genuinely new mathematics with no L=2 template? If bounded, name the 2-4 concrete
   sub-lemmas. If a wall, name the precise obstruction.
</output_contract>

<grounding_rules>
- Reason from the definitions given. RLCT here = real log canonical threshold / learning coefficient
  (Watanabe), a local analytic invariant at the point; local-diffeo invariance and positive-unit
  invariance are the two tools in play.
- If you think one of F1-F5 is FALSE, that is the most valuable output — give the explicit
  counterexample (small matrices, exact numbers).
- Do NOT rubber-stamp. If the local-diffeo argument has a gap (e.g. Psi not globally invertible on a
  neighbourhood, or Score = corePhi ∘ Psi only holding where P_11 is invertible), say so precisely.
- Distinguish "true and easy to formalise" from "true but a large block-matrix induction".
</grounding_rules>
