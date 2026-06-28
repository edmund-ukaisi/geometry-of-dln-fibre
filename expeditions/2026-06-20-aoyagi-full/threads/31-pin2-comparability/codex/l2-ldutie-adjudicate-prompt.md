<task>
A two-layer (L=2) matrix-algebra adjudication, exact algebra. Decide independently which product a
"framed global Schur complement" equals, and whether a frame-free per-layer product can equal it.

SETUP (r = 1, scalar blocks; generalize mentally to block r).  Fix a block split of each 2x2 matrix
into r (+) (.-r) = 1 (+) 1.  We have:
  - Two boundary frames: P0 block-LOWER invertible = [[a,0],[c,d]] (a,d != 0);
                         QL block-UPPER invertible = [[e,f],[0,g]] (e,g != 0).
  - corM = [[1,0],[0,0]]  (the rank-r corner).
  - Two perturbed "layers" reconstructed as (this is the EXACT object, frames applied as products):
        A0 = corM + P0 * dev0,        dev0 = [[X0,Y0],[Z0,T0]]
        A1 = corM + dev1 * QL,        dev1 = [[X1,Y1],[Z1,T1]]
    (the deepest point is dev=0, giving A0=A1=corM, product = corM = "B").
  - The "Score-integrand" is the global Schur complement of  Mw = P0*A0*A1*QL - corM
    over its (1,1)-block-PLUS-ONE pivot:   Score = Mw22 - Mw21 * (Mw11 + 1)^{-1} * Mw12.

  - A candidate "bare core" is the FRAME-FREE per-layer Schur product:
        S0_bare = T0 - Z0 (1+X0)^{-1} Y0,   S1_bare = T1 - Z1 (1+X1)^{-1} Y1,
        bareCore = S0_bare * S1_bare      (no a,c,d,e,f,g anywhere).
</task>

<output_contract>
1. Compute the Score-integrand symbolically (exact).  Does it depend on the frame entries a,c,d,e,f,g?
2. Determine what two-factor product the Score is the global Schur complement of.  Specifically: is
   Mw + corM = (P0*A0)*(A1*QL)?  Name the two factors G0, G1 whose product is Mw+corM, and read off
   their per-factor (1,1)-pivot blocks A0hat, A1hat and Schur cores S0hat, S1hat.
3. Is  Score == S0hat * (1 - K) * S1hat  with K = Z1hat * (A0hat*A1hat + Y0hat*Z1hat)^{-1} * Y0hat
   (the block-LDU of the two factors G0, G1)?  (yes/no, exact)
4. Is  Score == bareCore (the frame-free per-layer product)?  (yes/no, exact)  If no, exhibit the
   difference and say WHY (what does the frame-free product miss?).
5. If one wanted a per-layer "dictionary" core that EQUALS the Score, what must the per-layer reads be
   (frame-conjugated or frame-free)?  State the corrected pivot/core dictionary.
</output_contract>

<grounding_rules>
- Use sympy or pen-and-paper exact algebra; show the key intermediate expressions.
- A numeric match at one point is NOT a proof; require symbolic identity (or random-rational confirmation
  at >=2 independent points as a sanity guard).
- Do not assume the frames cancel; verify.  Report inference vs. computed fact distinctly.
- This is about WHICH product the framed Schur equals; do not opine on downstream Lean wiring.
</grounding_rules>
