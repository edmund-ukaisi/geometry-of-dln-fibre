1. VERDICT: CONFIRMED-WITH-CAVEAT

Established fact: Transposition gives a linear isomorphism
\[
(A_1,\ldots,A_p)\longmapsto(A_p^{T},\ldots,A_1^{T})
\]
between the parameter spaces for \((v_0,\ldots,v_p)\) and \((v_p,\ldots,v_0)\), carrying \(P\) to \(P^T\). Hence the geometric locus and its codimension are reversal-invariant.

Inference: Head-peeling a chain is, term by term and recursively, last-peeling its reversal. Since the geometric argument in part 2 validates head-peeling—and transposition validates the mirrored last-peeling—both recursions equal the geometric codimension and therefore equal each other for all chains and all \(s\).

Caveat: Agreement of two abstract recursions alone would not establish their geometric interpretation; they could share the same erroneous dimension rule. One must also extend the geometric definition harmlessly to zero widths, since the terms \(t=0\) and \(r=0\) create reduced chains containing a zero-dimensional space.

2. VERDICT: CONFIRMED

Established fact: Let \(S_t\) be the exact-rank-\(t\) stratum for \(A_1:\mathbb R^{v_0}\to\mathbb R^{v_1}\). It has codimension
\[
(v_0-t)(v_1-t).
\]
For \(A_1\in S_t\), put \(I=\operatorname{im}(A_1)\). Because \(A_1\) surjects onto \(I\),
\[
\operatorname{rank}(A_p\cdots A_2A_1)
=\operatorname{rank}\bigl((A_p\cdots A_2)|_I\bigr).
\]
After locally choosing \(\mathbb R^{v_1}=I\oplus I'\), the restriction \(A_2|_I\), together with \(A_3,\ldots,A_p\), is precisely the reduced chain \((t,v_2,\ldots,v_p)\); \(A_2|_{I'}\) is an unconstrained affine factor.

Inference: Over \(S_t\), the constrained family is locally a product of the reduced composite-rank locus with an affine space. Thus its ambient codimension is exactly
\[
(v_0-t)(v_1-t)+CR((t,v_2,\ldots,v_p),s).
\]
No transversality is being assumed. Finally, the full locus is the finite union over \(t\), so its dimension is the maximum of the stratum dimensions and its codimension is the minimum of these expressions. Closures and possible non-equidimensionality do not invalidate this global-codimension calculation.

3. VERDICT: CONFIRMED

Established fact: For a \(v_1\times v_0\) matrix, the rank-\(\le s\) determinantal locus has codimension
\[
(v_0-s)(v_1-s)
\]
when \(s<\min(v_0,v_1)\), and is the whole matrix space when \(s\ge\min(v_0,v_1)\).

Inference: The uniform formula is therefore
\[
(v_0-s)_+(v_1-s)_+.
\]
If \(s\ge\min(v_0,v_1)\), at least one truncated factor is zero; if \(s>\max(v_0,v_1)\), both are zero. Thus natural-number subtraction gives the correct value for every \(s\ge0\).

Most likely uncaught failure: a semantic mismatch in “codimension.” The recursion computes the global ambient codimension determined by the top-dimensional components of the rank-\(\le s\) locus. If the intended invariant were instead a local codimension, an every-component codimension, or a scheme-theoretic multiplicity-sensitive quantity, both recursions and every numerical comparison could agree while identifying the wrong geometric invariant.