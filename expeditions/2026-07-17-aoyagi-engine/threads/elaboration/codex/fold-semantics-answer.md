### (1) Start convention

As transcribed, \(M(0)\) is undefined because it is a minimum over an empty index set. Two readings are consistent:

1. The \(S=0\) statement is a separate empty-prefix convention, so none of \(M(0),D_0,\operatorname{diag}(b_i)\) is instantiated.
2. The natural literal extension sets
\[
M(0)=M^{(1)},\qquad b_i=1,\qquad
\operatorname{diag}(b_1,\ldots,b_{M^{(1)}})=I_{M^{(1)}},
\]
with \(E_0\) the \(0\times0\) identity, empty off-diagonal blocks, and
\[
D_0=I_{M^{(1)}}\quad(M^{(1)}\times M^{(1)}).
\]
Then the RHS is literally \(I\,I\,C^{(1)}\cdots C^{(L)}\).

This \(D_0\) is only the \(S=0\) auxiliary identity. At \((S,J)=(1,0)\), the residual called \(D_0\) is \(C^{(1)}\), of size \(M^{(1)}\times M^{(2)}\); that is where the first genuine blow-up acts. Taking \(D_0=C^{(1)}\) already at \(S=0\) would be dimensionally wrong and would duplicate \(C^{(1)}\).

CONFIDENCE: high — dimensions and literal multiplication force the identity extension.

### (2) Case 1(2) versus Case 1(1)

Let the partial block be \(J+1,\ldots,J+J_1\). The necessary reading is that \(u_{s,k}\) is a boundary factor first entering the recurrence at \(b_{J+J_1+1}\), namely \(\tilde t_{s,k}=J+J_1\). Thus it occurs in every later \(b_i\), but not in the equal partial block.

In Case 1(1), \(u_{s,k}\) itself is the exceptional coordinate. Only the centered rows satisfy
\[
d_{ij}=u_{s,k}d'_{ij},
\]
so only \(b_{J+1},\ldots,b_{J+J_1}\) acquire a new recorded factor. Later \(b_i\) already contained \(u_{s,k}\).

In Case 1(2), \(u_{S,J+1}\) is exceptional. The centered \(d\)-rows acquire it through \(d_{ij}=u_{S,J+1}d'_{ij}\), while every later row acquires it through
\[
u_{s,k}=u_{S,J+1}u'_{s,k}
\]
inside its existing \(b_i\). Hence the whole tail receives one common factor.

The transcribed center omits \(\tilde t_{s,k}=J+J_1\); without that condition, the whole-tail update is not forced.

CONFIDENCE: medium — the recurrence explains the display exactly, but the decisive index condition is omitted.

### (3) The \(Q\)- and \(P\)-clearings

\(Q\) reads only \(d'_{J+1,c}\) for \(c>J+1\). Right multiplication writes
\[
d''_{i,J+1}=d'_{i,J+1},\qquad
d''_{i,c}=d'_{i,c}-d'_{i,J+1}d'_{J+1,c}.
\]
Thus the pivot row becomes \((1,0,\ldots,0)\). The residual \(D_{J+1}\), on rows \(J+2,\ldots,M(S)\) and columns \(J+2,\ldots,M^{(S+1)}\), is precisely the rectangular Schur complement of the \(1\times1\) pivot \(d'_{J+1,J+1}=1\).

The compensation \(C'^{(S+1)}_J=Q^{-1}C^{(S+1)}_J\) writes only the corresponding pivot row of \(C^{(S+1)}_J\); \(C^{(S+2)},\ldots,C^{(L)}\) are unchanged.

For each \(i>J+1\), \(P\) reads \(d''_{i,J+1}\) and \(b'_i/b'_{J+1}\), then clears that pivot-column entry in the weighted row. It leaves the Schur-complement entries unchanged. The ratio is polynomial because the recurrence gives the divisibility chain \(b'_{J+1}\mid b'_i\), preserved by the chart updates—subject to the boundary-factor reading in (2).

CONFIDENCE: high — direct matrix multiplication gives every stated read and write.

SHARPEST DISAGREEMENT-RISK: confusing the \(S=0\) identity \(D_0\) with the \(S=1\) residual \(D_0=C^{(1)}\).