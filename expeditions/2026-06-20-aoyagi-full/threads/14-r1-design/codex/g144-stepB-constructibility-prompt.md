<task>
Adjudicate THE open sub-obligation of a resolution-of-singularities construction (RLCT of a deep-linear
network loss). Exact algebra; I have a candidate resolution — RED-TEAM it, don't rubber-stamp.

SETUP. The loss core at a node is `F = ‖C_L···C_1‖²` (a matrix-chain product, Frobenius-norm-squared) at
its origin (all C_i = 0 is the deepest singular point). The resolution recursion at a node:
1. BLOW UP the active factor's pivot: `pivotBlowupOn` makes a chosen pivot coordinate a HARD UNIT (=1).
   After it, `F ∘ blowup = x_p² · Q` (x_p the pivot, Q the residual — a PRODUCT, monomial Jacobian).
2. The residual Q = ‖Ĉ·A2‖², Ĉ the hard-pivot factor [[1,a],[b,D]], A2 the rest. By the EXACT row split
   (Frobenius norm splits by rows): Q = ‖row0‖² + ‖lower‖², where row0 = pivot-row product E = β + a·Γ,
   lower = b·E + S·Γ (S = D − b·a the Schur complement, Γ = A2's non-pivot rows). [verified exact, sympy]

THE CONTROLLER'S WORRY (the open question): for the recursion to DROP the chain-size measure ΣM and
terminate, is an EXACT det-±1 change-of-variables needed taking Q to a CLEAN "(regular squares) +
‖S·A2red‖²" (a smaller chain core, ΣM−2)? Clearing the `b·E` coupling in `lower` to decouple row0 from
the S-core would need S⁻¹, which FAILS at the deepest point (S → 0, S rank-deficient there). So either
(a) some exact det-±1 c-o-v decouples it without S⁻¹ (the (2,2,2) `lemma2Fwd` generalizes), or
(b) it obstructs and the recursion must descend on the COUPLED residual — does ΣM still drop?

MY FINDING (red-team this):
- In (2,2,2), `lemma2Fwd` does NOT decouple to (regular)+(clean S-core). Its output `resolvedForm =
  E² + F0² + (q·E+δ·G)² + (q·F0+δ·H)²` is STILL COUPLED (q·E cross-terms). The decoupling is done by the
  NEXT blow-up (of the coupled vertex {E=F0=δ=0}), NOT by lemma2Fwd. So no clean-decoupling c-o-v exists
  even in (2,2,2). Option (a) is FALSE as stated.
- BUT a clean ΣM−2 c-o-v is NOT NEEDED. The ΣM-drop is COMBINATORIAL: the reduced core ‖S·Γ‖² (S = D−ba,
  the pivot row+col removed) IS a smaller matrix-chain core — e.g. (3,2,3) ΣM=8 → reduced (2,1,3) ΣM=6,
  drop 2 — regardless of S being rank-deficient at 0. S rank-deficient just means ‖S·Γ‖² is itself
  singular, which the recursion handles by descending on it (the (2,1,3) node, which has a width-1 inner
  ⟹ a C4 Fubini pinch / further blow-up).
- The `b·E` coupling does NOT block termination because this is the MONOMIAL route, not a smooth-block
  split: the cover (`argmaxCellOn` chart-locality) splits the chart where the row0/E pivot is nonzero from
  the chart where the S·Γ block is nonzero; each is blown up + recursed separately. No exact decoupling
  c-o-v, no S⁻¹.
- So the answer is (c): no clean c-o-v exists AND none is needed; the recursion descends on the smaller
  (combinatorially-reduced) coupled core, terminating by the lex(depth, ΣM, ncDefect) measure.

THE PRECISE QUESTION FOR YOU:
Does the recursion TERMINATE on the coupled residual without a clean exact c-o-v? Specifically: is there a
case where, after blow-up, NO further pivot is available to recurse on (a STALL) — or does every
nonterminal node always present a fresh hard pivot (post its own blow-up) so the lex measure strictly
drops? Find a stall if one exists (that would be a real obstruction); otherwise confirm termination.
</task>

<output_contract>
  1. Is MY finding correct that NO clean-decoupling exact c-o-v exists (even (2,2,2) stays coupled, the
     next blow-up decouples)? (yes/no + why).
  2. Is the ΣM-drop genuinely COMBINATORIAL (pivot row+col removal, S⁻¹-free), so the reduced core ‖S·Γ‖²
     is a bona-fide smaller matrix-chain core even when S is rank-deficient at 0? (yes/no + why).
  3. THE CRUX: does the recursion TERMINATE on the coupled residual — is there any STALL (a nonterminal
     node with no available pivot / where lex(depth,ΣM,ncDefect) does NOT strictly drop)? Try to BREAK it
     with a specific M (the controller suggested rank-deficient-S cases like (2,3,2)/(3,2,3); also try
     multi-drop / all-equal-width). If you find a stall, that's the real obstruction — report it.
  4. Overall verdict: is the fully-monomial blow-up+recurse construction SOUND on this sub-obligation
     (terminates, no clean-c-o-v needed), or is there a genuine open obstruction?
  Under ~500 words. Mark inference vs. fact. Exact algebra; don't invent lemma names.
</output_contract>

<grounding_rules>
  The row split Q = ‖row0‖² + ‖lower‖², lower = b·E + S·Γ, S = D−ba is FACT (sympy-verified). The
  monomial route's cover (argmaxCellOn) splitting charts is the established mechanism. Distinguish "this
  terminates" (provable) from "this looks fine but I can't rule out a stall". If you find a concrete
  stall M, that overrides everything — report it loudly.
</grounding_rules>
