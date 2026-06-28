# Review - A2 Case 2 source-readback factor provenance

Reviewer: xhigh read-only checker `Bacon`.

Verdict: PASS.

The theorem family is sound and useful.  The fixed-base source edge family
built from the endpoint-transported explicit Case 2 datum is realized back as
that datum's `edgeMatrix`, and `sourceReadback_edgeMatrix_eq` recovers the
datum from that edge matrix under the datum's determinant-chart proof.

The two adjacent factor theorems then rewrite the readback to the transported
datum and apply the endpoint-transported `C 1` and `C 0` factor-display
theorems.  This proves source-readback factor provenance, not another
residual-product wrapper.

Dependencies checked:

- fixed-base source-family edge realization;
- source-readback inverse on `data.edgeMatrix`;
- endpoint-transported Case 2 determinant-chart theorem;
- endpoint-transported `C 1` and `C 0` displayed factor theorems.

Nonclaims checked: no construction of `tau`, no proof of `hTau`, no
label-preserving endpoint provenance, no arbitrary `ofTopologyTuple`
alignment, no source-prior transport, no Jacobian comparison, no normal
crossings, no pole order, and no RLCT.
