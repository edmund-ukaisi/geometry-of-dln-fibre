## 1. VERDICT

**Yes**—within a fixed chart branch, every \(u_{s,k}\) remains in one immutable flat slot for its entire lifetime.

Write
\[
\sigma_S(i,j):=(S,i,j),\qquad p_{S,J}:=\sigma_S(J+1,J+1).
\]

## 2. PER-TRANSITION

| Transition | Flat-slot substitution | Effect on \(u\)-slots |
|---|---|---|
| Case-1(1) | For \(J<i\le J+J_1,\ J<j\le M^{(S+1)}\), \(d_{ij}^{\rm old}=u_{s,k}d'_{ij}\). Each ratio \(d'_{ij}\) remains in \(\sigma_S(i,j)\). | The pivot \(u_{s,k}\) remains in its existing carrier slot. Updating \(\widetilde t_{s,k}\) and \(M_{s,k}\), then dropping primes, is bookkeeping—not relocation. |
| Case-1(2) | At \(p=p_{S,J}\), \(d_{J+1,J+1}^{\rm old}=u_{S,J+1}\). For every other centered \(d\)-slot \(q\), \(d_q^{\rm old}=u_{S,J+1}d'_q\), with \(d'_q\) remaining at \(q\). | If the old divisor occupies \(r\), then \(u_{s,k}^{\rm old}=u_{S,J+1}u'_{s,k}\), and \(u'_{s,k}\) occupies the same \(r\). After \(u'_{s,k}\mapsto u_{s,k}\), the old divisor is still at \(r\); the new divisor is at \(p\). |
| Case-2 | For the full residual block, the pivot slot \(p_{S,J}\) becomes \(u_{S,J+1}\); every nonpivot \(d\)-slot retains its own ratio coordinate. | New divisor at \(p_{S,J}\); all earlier \(u\)-slots are untouched. |
| Rollover | No substitution. The active symbol \(D\) is reused for the residual entries of layer \(S+1\), hence for slots \(\sigma_{S+1}(i,j)\). | No \(u\) is moved or renamed to another slot. |
| \(Q\) | With the trailing block \(A=\begin{psmallmatrix}1&\alpha\\ \beta&C\end{psmallmatrix}\), take \(Q=\begin{psmallmatrix}1&-\alpha\\0&I\end{psmallmatrix}\). Lower-right slots are changed in place to \(C-\beta\alpha\). When \(S<L\), \(C^{(S+1)}\mapsto Q^{-1}C^{(S+1)}\) changes in place the slots \((S+1,J+1,c)\). The \(\alpha\)-coordinates remain spectators in their original first-row slots. | No \(u\)-carrier is reassigned. |
| \(P\) | \(P=\begin{psmallmatrix}1&0\\-\beta&I\end{psmallmatrix}\) makes the displayed first column below the pivot zero. The \(\beta_i\) remain spectator coordinates in slots \(\sigma_S(i,J+1)\). | No \(u\)-carrier is reassigned. |

The supplied description does not specify a companion source-coordinate substitution for \(P\). If \(P\) is more than a left row operation on the displayed generators, its explicit page formula would be needed to list additional non-\(u\) slots. This does not affect the \(u\)-slot conclusion.

## 3. NEW-DIVISOR SLOT

At birth node \((S,J)\),
\[
\boxed{\operatorname{slot}(u_{S,J+1})=(S,J+1,J+1).}
\]

Subsequent factoring of \(u_{S,J+1}\) into \(b_i\) does not remove it from that carrier slot.

## 4. RECONSTRUCTIBILITY

No: the slot is not a function of \((T,M)\) alone.

Take
\[
(M^{(1)},M^{(2)},M^{(3)})=(2,3,2),\qquad L=2.
\]

At \((S,J)=(1,1)\), Case-2 blows up the two-coordinate residual row and creates
\[
u_{1,2}\quad\text{at}\quad(1,2,2).
\]
The center has codimension \(2\), so
\[
M_{1,2}=2-1=1.
\]

After rollover, at \((S,J)=(2,0)\),
\[
b_1\ne b_2,\qquad J_1=1,
\]
and the Case-1 center is
\[
\{d_{11}=d_{12}=u_{1,2}=0\}.
\]

- Case-1(1): \(d_{1j}=u_{1,2}d'_{1j}\). Thus
  \[
  T_{1,2}=(1,0),\qquad M'_{1,2}=1+2=3,
  \]
  while its slot remains \((1,2,2)\).

- Case-1(2): put
  \[
  d_{11}=u_{2,1},\qquad d_{12}=u_{2,1}d'_{12},\qquad
  u_{1,2}=u_{2,1}u'_{1,2}.
  \]
  The new divisor satisfies
  \[
  T_{2,1}=(1,0),\qquad M_{2,1}=1+2=3,
  \]
  but occupies \((2,1,1)\).

Hence identical \((T,M)=((1,0),3)\) occurs in different leaves at different slots. These are branch-local equations for the same blow-up exceptional component. In either immediate leaf there is only one such record; this example is an across-leaf ambiguity. The supplied fragment lacks the complete \(T\)-initialization and rollover rules needed to decide same-leaf injectivity in full generality.

## 5. CARRIER FIELD

A single immutable per-divisor carrier field is sufficient within each branch. Set it to \((S,J+1,J+1)\) at birth; preserve it through Case-1(1), preserve the old carrier and create a new one in Case-1(2), and leave all carriers unchanged under rollover and \(Q/P\). No dynamic slot-update rule is needed.