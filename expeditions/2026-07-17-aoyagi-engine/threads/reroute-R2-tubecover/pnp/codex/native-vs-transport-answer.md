### 1. NATIVE-vs-TRANSPORT

Conditionally **(A), native**. For every reachable state \(S\), native status requires
\[
p(\sigma S)=\sigma p(S),\qquad C(\sigma S)=\sigma C(S),
\]
and the resulting successor state must equal \(\sigma\) applied to the canonical successor.

The stated rule satisfies this when dominance is unique and \(G\) preserves the row/column incidence defining the cross: support sizes permute, the dominant position becomes \(\sigma(p)\), and
\[
\operatorname{Cross}(\sigma p)=\sigma(\operatorname{Cross}(p)).
\]
Thus the native atom is exactly \(\operatorname{bb}(\sigma C,\sigma p)\).

It can fail through non-equivariant tie-breaking, ordered direction conventions, non-equivariant shear/normalisation choices, or an inner node where \(\sigma\) does not carry the canonical centre/state to the native one. In those cases \(g_c\) remains a valid transported chart but is not proved native.

### 2. VERIFICATION-SOUNDNESS

Yes, provided the 288 charts are the complete native leaf set and “divisorMin” ranges over precisely the survivor coordinate divisors. Then Jacobian exponent \(\ge7\) gives discrepancy \(\ge8\) on every survivor, hence divisorMin \(\ge8\).

The exact global toric LP catches an RLCT optimum off the survivor axes; the symbolic survivor check catches a non-single survivor. However, RLCT equality with the canonical chart does not itself prove divisorMin, and an axes-only Jacobian check would miss non-coordinate toric rays if those count as candidate divisors. Extra native leaves created by ties or different inner centres would also lie outside the 288 checks.

### 3. RESIDUAL RISK

The likeliest overclaim is that the 288 conjugated charts were assumed, rather than proved, to equal the native leaf set.

The cheapest exact closure test is an equivariance audit on every reachable state, checking for generators of \(G\):
\[
\texttt{stepUpdate}(\sigma S)
 =\sigma\bigl(\texttt{stepUpdate}(S)\bigr)
\]
including pivot, direction set, and successor state. Then compare the resulting native leaf signatures with the 288 conjugated signatures.