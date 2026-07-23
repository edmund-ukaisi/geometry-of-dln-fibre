Verdict: the APPEND identity is false for the stated raw child, so it cannot be recovered by ideal manipulation. However, the proposed claim that no determinant-one change of variables can relate raw and cleared is also false: this witness admits an explicit polynomial volume-preserving straightening, but it moves the blow-up center and therefore does not repair the original child edge.

### Q1 — APPEND for the fixed child

**FACT.** Set
\[
x=u_{010},\quad y=u_{001},\quad z=u_{011}=u_{e_2},
\]
\[
b_0=u_{100},\ b_1=u_{101},\ d_0=u_{110},\ d_1=u_{111}.
\]
For output row \(q\), let
\[
S_q=u_{2,q,0}b_0+u_{2,q,1}d_0,\qquad
T_q=u_{2,q,0}b_1+u_{2,q,1}d_1.
\]
Then the two output-column slots are
\[
F_{q0}=S_q+2xT_q,\qquad F_{q1}=yS_q+zT_q,
\]
while the source-cleared residual is
\[
C_{q0}=S_q,\qquad C_{q1}=yS_q+zT_q.
\]

The center ideal is \(I=(z,b_0,d_0)\). Under its blow-up \(B\), \(S_q\mapsto zS_q\), while the spectator term \(xT_q\) is unchanged. For the quotient map \(Q\), \(z\mapsto1\). Hence
\[
(F\circ B)_{q0}-z(F\circ Q)_{q0}
   =2x(1-z)T_q,
\]
\[
(F\circ B)_{q1}-z(F\circ Q)_{q1}=0.
\]

Since \(1-z\) is a unit in the local ring at the origin and \(xT_q\neq0\), the first defect is a nonzero polynomial germ. It also remains nonzero on \(V(I)\). Therefore:

- the stated APPEND identity for raw `foldResid` is false;
- no polynomial, ideal, radical, integral-closure, or continuous-span argument can prove it;
- localizing at \(z\) would only discard the exceptional divisor \(z=0\), where the proof is needed.

**FACT.** There are algebraic repairs, but they change the child. For example, enlarging the center to \(I+(x)\) makes every raw slot degree-one supported. Alternatively, after a coordinate change below, raw is supported on
\[
J=(z-2xy,\ b_0+2xb_1,\ d_0+2xd_1).
\]
Neither is the original case11 center \(I\).

### Q2 — A determinant-one change does exist

**FACT.** The proposed dimension obstruction is false for this witness. Define the polynomial automorphism
\[
\psi:\quad
b_0\mapsto b_0-2xb_1,\quad
d_0\mapsto d_0-2xd_1,\quad
z\mapsto z+2xy,
\]
fixing every other coordinate. Direct substitution gives
\[
F\circ\psi=C.
\]
Its Jacobian determinant is \(1\), and its polynomial inverse uses the opposite signs.

Thus a visibly \(x\)-dependent map can become \(x\)-independent after an invertible full-space change: raw has the nonvanishing flat vector field
\[
V=\partial_x-2b_1\partial_{b_0}-2d_1\partial_{d_0}
  +2y\partial_z,
\qquad V(F_j)=0,\quad Vx=1.
\]

This does not contradict the Gröbner calculations: the ideals are unequal in the original coordinates but are automorphically equivalent,
\[
\psi^*\langle F_j\rangle=\langle C_j\rangle.
\]

**FACT.** This change cannot repair the same child edge because it moves both center and pivot:
\[
I\longmapsto
J=(z-2xy,\ b_0+2xb_1,\ d_0+2xd_1).
\]
Indeed, any automorphism mapping \(F\) to \(C\) while preserving \(I\) would imply \(F_j\in I\) from \(C_j\in I\), contradicting the exact nonmembership. It only transports APPEND to the conjugated blow-up with pivot \(z-2xy\), not to the original \(z\)-edge.

### Q3 — Precise RLCT condition

**FACT.** A clean sufficient condition for fixing \(x=0\) to preserve the RLCT is a regular local fibre trivialization: there must be an analytic diffeomorphism
\[
\Psi:(x,v)\longmapsto\theta
\]
with nonvanishing Jacobian and constants \(0<c<C<\infty\) such that
\[
c\,K(0,v)\le K(\Psi(x,v))\le C\,K(0,v)
\]
uniformly near the origin, and the measure marginalized along \(x\) must remain bounded above and below by a positive smooth density on the slice. Exact fibre invariance \(K\circ\Psi=K(0,v)\) is the strongest version.

Then integrating over \(x\) contributes only a finite positive factor, so the full and sliced RLCTs agree. Without such flatness, restriction generically changes RLCT: \(K=x^2+v^2\) has RLCT \(1\), whereas \(K|_{x=0}=v^2\) has RLCT \(1/2\).

**FACT.** For the displayed parent residual with ordinary smooth positive measure, the explicit \(\psi\) proves
\[
\operatorname{RLCT}\!\left(\sum_jF_j^2\right)
=
\operatorname{RLCT}\!\left(\sum_jC_j^2\right)
=
\operatorname{RLCT}\!\left(\left.\sum_jF_j^2\right|_{x=0}\right).
\]
If a resolution chart already carries a vanishing monomial Jacobian weight, one must additionally verify that its fibre-marginal after \(\psi\) has the same singular order; \(\det D\psi=1\) alone does not preserve an independently specified vanishing weight.

**FACT.** Merely saying that \(x\) belongs to an input \(GL_{d_0}\)-orbit is insufficient. Under
\[
A_0\mapsto A_0G,\qquad P\mapsto PG,
\]
\[
\|PG\|_F^2=\operatorname{tr}(G^\mathsf TP^\mathsf TPG)
\]
is not generally equal to \(\|P\|_F^2\). A bounded local \(G\) can nevertheless be sufficient because
\[
\sigma_{\min}(G)^2\|P\|_F^2
\le \|PG\|_F^2
\le \sigma_{\max}(G)^2\|P\|_F^2,
\]
but this requires uniform bounds, a transverse slice, and a nondegenerate measure Jacobian.

A genuine product-fibre gauge, such as the paired internal action
\[
A_0\mapsto HA_0,\qquad A_1\mapsto A_1H^{-1},
\]
keeps \(P\) fixed. Even then, freeness/transversality and a nonvanishing gauge-fixing Jacobian must be checked; invariance merely on the zero fibre \(P=0\) is not enough for an RLCT, which probes a full neighborhood.

**INFERENCE.** Whether this straightening is admissible in the intended resolution depends on whether the proof may conjugate the subsequent center and whether the accumulated chart measure remains compatible.

### Q4 — Bottom line

For the fixed case11 edge there is no ideal-level APPEND bridge, while replacing raw by cleared requires an RLCT/gauge justification—explicitly realizable here by a determinant-one polynomial straightening, but only after moving/conjugating the center rather than preserving the original child.