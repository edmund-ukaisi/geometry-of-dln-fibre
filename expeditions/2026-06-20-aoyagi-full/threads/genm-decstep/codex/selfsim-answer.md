### Q1. The coupling remainder is droppable — PROVEN

Write \(z\) for the Mellin exponent, reserving \(c=n-t^*\) for the corank. On a chart where the last deeper matrix has rank \(k\) and \(Q_b\) has rank \(r\), the dropped-coupling threshold is

\[
T_{k,r}
=\frac12\Bigl((n-k)^2+t^*k+(b-r)(k-r)+ar\Bigr).
\]

The terms are respectively:

\[
\operatorname{codim}\{\operatorname{rank}W=k\},\quad
\operatorname{codim}\{B_0=0\},\quad
\operatorname{codim}\{\operatorname{rank}Q_b=r\},\quad
\text{active }\Gamma\text{-directions}.
\]

This is the SVD/rank-stratified form of the exact Wishart condition

\[
\int_{[-1,1]^{m\times q}}\det(XX^{T})^{-s}\,dX<\infty
\iff 2s<q-m+1.
\]

For an effective \(b\times k\) Gram matrix, \(s=a/2\), so full row rank is integrable precisely when

\[
a<k-b+1.
\]

When this fails, the lower-rank \(r<b\) terms in \(T_{k,r}\) supply the missing strata.

For \(n=4\),

\[
t^*=2,\qquad a=b=c=2,\qquad q=4,
\]

and

\[
2T_{k,r}=(4-k)^2+2k+(2-r)(k-r)+2r.
\]

Minimizing first over \(k\) for each rank \(r\):

| \(r=\operatorname{rank}Q_b\) | Binding \(k\) | \(2T\) | Threshold |
|---:|---:|---:|---:|
| \(0\) | \(2\) | \(4+4+4=12\) | \(6\) |
| \(1\) | \(2\) or \(3\) | \(4+4+1+2=11\) | \(11/2\) |
| \(2\) | \(3\) | \(1+6+0+4=11\) | \(11/2\) |

Hence

\[
\min_{r,k}T_{k,r}
=\min\left\{6,\frac{11}{2},\frac{11}{2}\right\}
=\frac{11}{2}.
\]

At \(k=3\), the Wishart inequality is critical:

\[
a<k-b+1\iff 2<2,
\]

so ranks \(r=1\) and \(r=2\) tie. This produces a logarithmic boundary phenomenon, not a smaller threshold. Thus \(J_{\rm drop}(z)\) is finite for every \(z<11/2\); divergence at equality is compatible with RLCT \(11/2\).

More generally, for \(a=b=c=\lceil n/3\rceil\),

\[
2\Lambda_{\rm drop}
=\min_{k,r}\bigl((n-k)^2+t^*k+(c-r)(k-r)+cr\bigr).
\]

Putting \(x=n-k\) and \(y=k-r\) turns this into the balanced integer minimum

\[
x^2+xy+y^2+nr,\qquad x+y+r=n,\quad r\le c.
\]

Its balanced minimizer has \(r=c\) or a tied adjacent rank, giving

\[
\Lambda_{\rm drop}
=\frac{c^2}{2}+\frac12\minAdm(t^*,n,n)
=\lambda_n.
\]

Therefore

\[
\bigl(\|B_0\|^2+\|C'B_0\Pi\|^2\bigr)^{-p}
\le \|B_0\|^{-2p}
\]

does not lose threshold. The coupling remainder is not load-bearing.

### Q2. The weighted induction bottoms out — structural INFERENCE

The rank-\(r\) chart leaves a smaller determinantal block indexed by the rank defect \(b-r\). Thus a lexicographic complexity measure such as

\[
(\text{chain arity},\,b)
\]

strictly decreases: an outer peel shortens the chain, while internal rank resolution decreases the Gram size. It reaches the two-width leaf, where there is no deeper shared product and the remaining Gram integral is settled directly by the Wishart criterion.

For \(c\ge2\), one radial coordinate is insufficient: it resolves only the origin, while the rank-\(1,\ldots,c-1\) determinantal strata remain. A full multi-singular-value/determinantal resolution is required.

That resolution is finite for every fixed peel because there are finitely many ranks. Its size is not uniform in \(n\), since \(c=\lceil n/3\rceil\) grows, but it is bounded in the sense requested: finitely many internal blow-ups per peel.

### Q3. The option-(b) citation is not needed

The premise of option (b) is false. No independent coupled corank-Gram incidence theorem is required: the coupled integral is bounded by the uncoupled Gram-weighted integral already handled above.

If one declined to build the determinantal rank recursion, the missing result would instead be the uncoupled Gram-weighted reduced-chain finiteness theorem—not a theorem requiring the projector coupling.

### Q4. Net verdict

**PROVEN threshold verdict:** option (a), SELF-SIMILAR.  
**INFERENCE about construction:** it terminates through a finite determinantal resolution for each fixed chain.

**SELF-SIMILAR-BOUNDED**