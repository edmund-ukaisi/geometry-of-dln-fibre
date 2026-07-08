1. **VERDICT: GATE FAIL as stated.**

2. **Strongest attack:** Aoyagi Case 1(2) itself forces a cross-support row mix. In the displayed step, after the partial-run blow-up, the clearing matrix has entries
`P_{i,J+1} = -(b'_i / b'_{J+1}) d''_{i,J+1}` for rows `i > J+1`, including rows beyond the equal run. Thus a row with support `supp(b'_i)` is updated using the pivot row with support `supp(b'_{J+1})`.

Concrete schematic instance:
`b'_{J+1}=u b`, `b'_{J+2}=u b v`. Then
`g'_{J+2} = g_{J+2} - v d''_{J+2,J+1} g_{J+1}`.
This closes because the coefficient `v` raises the pivot term to the target support, not because the two generators had constant support. So a pure “row-mix only inside constant-support blocks” invariant is too weak.

3. **Mismatch:** Your block-split isolation is not literally Aoyagi’s `(S,J)` Case-1 recursion. Aoyagi’s mechanism is subtler: the `diag(b)` divisibility chain makes the quotients `b'_i/b'_{J+1}` regular, and the `P`-clear uses those quotients. Closure is by **support-compatible monomial-coefficient row mix**, not by avoiding all different-support mixing. A Frobenius-loss-only variant that splits pivot/corank before clearing may still be viable, but it is then a replacement proof obligation, not the source-faithful Aoyagi step.

4. **Confidence that GATE PASS is correct:** `0.35`.

Most likely way my fail verdict is wrong: your intended Lean gate already includes a generator-level row-mix lemma allowing monomial support quotients like `b_i/b_pivot`; then the native Aoyagi ledger can close. But that is not the constant-support block-split argument you stated.