<task>
Lean 4 + Mathlib v4.29 (toolchain lean v4.29.0). I need the cleanest tactic-level proof
of one strict natural-number inequality, plus the cleanest overall structure for an iff.

THE STRICT INEQUALITY (the genuine content):
  For ell a : ℕ with `2 ≤ a` and `2 ≤ ell - a` (equivalently `a ≤ ell` and `min a (ell-a) ≥ 2`,
  so ell ≥ 4), prove
      a * (ell - a) + 1 < Nat.choose ell a.
  (`-` is truncated nat subtraction but a ≤ ell here so ell - a is genuine.)

  Numerically verified true for all ell ≤ 39. The boundary case a = 2 gives
  Nat.choose ell 2 - (2*ell - 3) = (ell-2)*(ell-3)/2 > 0 for ell ≥ 4.

THE FULL IFF I am formalizing (capstone 2):
  For a ≤ ell:  Nat.choose ell a = a*(ell-a)+1  ↔  min a (ell - a) ≤ 1.
  The ⟸ direction is the four edge cases a ∈ {0,1,ell-1,ell}: both sides are 1,ell,ell,1
  (using Nat.choose_zero_right, choose_one_right, choose_self, choose_symm / choose_succ_self...).
  The ⟹ direction is the contrapositive of the strict inequality above (min ≥ 2 ⟹ LHS ≠ RHS
  because choose is strictly bigger).

CONSTRAINTS / available facts in Mathlib v4.29 (confirmed present):
  - Nat.choose_two_right : choose n 2 = n*(n-1)/2
  - Nat.choose_symm : k ≤ n → choose n (n-k) = choose n k
  - Nat.choose_le_choose (c) : a ≤ b → choose a c ≤ choose b c   (monotone in n)
  - Nat.succ_mul_choose_eq : succ n * choose n k = choose (succ n) (succ k) * succ k
  - Nat.choose_mono, Nat.choose_pos, Nat.choose_symm_diff, descFactorial lemmas
  - Nat.choose_le_descFactorial / choose_lt_descFactorial (hk : 2≤k) (hkn: k≤n): choose n k < descFactorial n k
  - pow_le_choose (r n) : (n+1-r)^r / r! ≤ choose n r   (integer division)
  STYLE: must avoid native_decide (decide +kernel only, but ell is a free variable here so
  decide is NOT available). Prefer omega / nlinarith / induction / a short calc.

What I am unsure about: the cleanest induction variable / monotonicity stepping stone.
Two candidate routes I see:
  (R-mono) Reduce to the boundary a=2 by a unimodality/monotonicity argument:
     for fixed ell, choose ell a is ≥ choose ell 2 when 2 ≤ a ≤ ell-2? FALSE direction to use
     directly since a*(ell-a) also grows. So I'd need choose ell a - (a*(ell-a)+1) monotone,
     which is not a clean Mathlib lemma. Likely a dead end.
  (R-product) Use a closed lower bound: choose ell a ≥ choose ell 2 * choose (ell-2) (a-2)?? via
     a Vandermonde / column-recursion identity, or the "two extra factors" descFactorial bound
     choose ell a ≥ (ell)(ell-1)/(a(a-1)) * choose (ell-2)(a-2) ... messy with nat division.
  (R-induction-on-ell) Fix the gap g = ell - a ≥ 2, induct on a ≥ 2 (so ell = a+g). Pascal:
     choose (a+g) a = choose (a+g-1) (a-1) + choose (a+g-1) a. Does an induction on a with g≥2
     fixed close cleanly with omega on the arithmetic? Base a=2: choose (2+g) 2 = (g+2)(g+1)/2
     vs 2g+1, need (g+2)(g+1)/2 > 2g+1 ⟺ g^2+3g+2 > 4g+2 ⟺ g^2 > g ⟺ g≥2 ✓.

<output_contract>
1. Pick ONE route and justify in 2-3 sentences why it is the cleanest in Lean (least new
   infrastructure, friendliest to omega/nlinarith). Name the exact Mathlib lemmas it uses.
2. Give a concrete Lean proof SKELETON (statement + tactic structure, the key `have`s with their
   types). It does not have to compile verbatim but the lemma names and the induction/case
   structure must be real. Flag any lemma name you are not >80% sure exists in v4.29.
3. Note the single most likely failure point (where omega/nlinarith will choke on nat subtraction
   or division) and how to pre-empt it (e.g. cast to ℤ, or clear the /2 with Nat.choose_two_right
   then a *2 multiply).
</output_contract>

<grounding_rules>
Distinguish "I am confident this Mathlib lemma exists at v4.29 with this signature" from
"this is the shape, verify the name". Do not invent lemma names; if unsure say so.
</grounding_rules>
