<task>
A pure matrix-algebra "germ order" question. I need an INDEPENDENT derivation of the
leading order (in a small deviation parameter ε) of a scalar gap, and the domain
hypotheses it requires. Set it up yourself from the definitions; do not assume my
framing is complete.
</task>

<setup>
L=2 deep linear network, reduced rank r, widths H0,H1,H2; reduced widths M_s = H_s - r.
All matrices real. Work on the block grid (r ⊕ M_s) per layer.

Two block-decomposed layers, each a deviation ε from the "deepest point" (rank-normal
corner = fromBlocks(I_r, 0, 0, 0)):
  C0 = fromBlocks(A0, Y0, Z0, T0)  : (r⊕M0) x (r⊕M1)
  C1 = fromBlocks(A1, Y1, Z1, T1)  : (r⊕M1) x (r⊕M2)
with  A_s = I_r + ε·X_s,   Y_s = ε·Y_s^,  Z_s = ε·Z_s^,  T_s = ε·T_s^   (hatted = O(1) dirs).

The "framed reindexed deviation" Mw is identified (after endpoint-frame stripping) with the
two-layer block product:
  Mw = C0·C1 = fromBlocks( A0A1+Y0Z1 , A0Y1+Y0T1 , Z0A1+T0Z1 , Z0Y1+T0T1 ).
Define the CORNER-SHIFTED pivot block:
  P00 = A0A1 + Y0Z1     (note: → I_r as ε→0),
  P01 = A0Y1 + Y0T1,  P10 = Z0A1 + T0Z1,  P11 = Z0Y1 + T0T1.

Objects:
  (1) Rcore = P11 − P10·P00^{-1}·P01     (the (1,1)-Schur complement, with the +I pivot).
  (2) Sreg  = ‖P00 − I‖_F² + ‖P01‖_F² + ‖P10‖_F²   (three "regular-block" energies).
  (3) coreΦ = ‖S'_0 · S'_1‖_F²  where the per-layer "frame-free Schur cores" are
        S'_s = T_s − Z_s·(I + X_s·ε... )^{-1}·Y_s,  i.e. pivot is (I + (A_s − I)) = A_s.
      (So S'_s = T_s − Z_s·A_s^{-1}·Y_s.)

Known exact ring identity (block-LDU): Rcore = S0·(I − K)·S1 with the SAME per-layer cores
S_s = T_s − Z_s·A_s^{-1}·Y_s (so S_s = S'_s), and K = Z1·P00^{-1}·Y0.
</setup>

<questions>
1. Derive the leading order in ε of:
   - Sreg
   - the gap G := | ‖Rcore‖_F² − coreΦ |  =  | ‖Rcore‖_F² − ‖S0·S1‖_F² |
   Give the exponent p such that G = Θ(ε^p) generically, and Sreg = Θ(ε^q).
2. Hence: G = Θ(Sreg^?) — is the gap O(Sreg), O(Sreg²), O(Sreg³), or something else?
   Show the order of K, of D := Rcore − S0·S1 = −S0·K·S1, of frobSq(D), and of the
   cross term ⟨S0·S1, D⟩, separately.
3. The claimed downstream bound is |‖Rcore‖_F² − coreΦ| ≤ Ccore·Sreg UNIFORMLY on a
   neighbourhood of the deepest point intersected with the domain { cond(P00) ≤ M }
   (P00 invertible, bounded inverse). Does the order you derive make this bound hold,
   and is { cond(P00) ≤ M } (bounded P00^{-1}) SUFFICIENT, or is a stronger hypothesis
   needed (e.g. that the endpoint frames clean the corner so the deviation's (1,1) block
   really is P00 − I with P00 → I and NO O(ε) constant term)?
4. Adversarial: can you construct a direction (choice of hatted dirs, or a frame that
   does NOT clean the corner so that the deviation's (1,1) block has an O(ε) part that
   is NOT folded into Sreg) where G/Sreg does NOT go to 0 as ε→0 — i.e. the gap is
   genuinely Θ(Sreg)? State precisely what breaks the higher order.
</questions>

<output_contract>
- Separate FACT (exact algebra you can show) from INFERENCE (order heuristics).
- Give the order exponents explicitly. State whether the ≤ Ccore·Sreg bound holds and
  under which domain hypothesis (bounded P00^{-1} alone, vs. also corner-clean).
- If you can give the smallest sufficient domain, do.
</output_contract>

<grounding_rules>
- This is generic (the hatted dirs are generic O(1)); ignore measure-zero coincidences
  unless they reveal a real domain restriction.
- "Corner-clean" means: the (1,1) block of the framed deviation equals exactly P00 − I
  with P00 = I + O(ε) and no surviving O(ε^0) or un-Sreg-charged O(ε) piece.
- Do not write code unless it helps you; if you do, state the result, do not assume I'll run it.
</grounding_rules>
