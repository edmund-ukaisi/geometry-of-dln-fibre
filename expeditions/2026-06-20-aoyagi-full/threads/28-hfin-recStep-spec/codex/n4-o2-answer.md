Let \(n=r-1\), \(x=M_{12}\in[-1,1]^n\), \(y=M_{21}\in[-1,1]^n\), \(Z=M_{22}\), and \(C=\mathrm{Sc}=Z-yx^T\).

**Q1: PROVEN.**  
The map
\[
(x,y,Z)\mapsto (x,y,C=Z-yx^T)
\]
is triangular in the variables \((x,y,Z)\), with \(C\) depending on \(Z\) by translation. Hence its Jacobian determinant is \(1\). For fixed spectators \((x,y)\),
\[
Z\in[-1,1]^{n^2}
\quad\Longleftrightarrow\quad
C\in \prod_{a,b}[-1-y_ax_b,\,1-y_ax_b].
\]
Since \(|y_ax_b|\le 1\), this translated box is contained in the fixed box \([-2,2]^{n^2}\), independently of \(x,y\).

**Q2: PROVEN, with the standard top-shear care.**  
For any measurable \(g\ge 0\),
\[
\int_{Z\in[-1,1]^{n^2}} g(Z-yx^T)\,dZ
=
\int_{C\in[-1,1]^{n^2}-yx^T} g(C)\,dC
\le
\int_{[-2,2]^{n^2}}g(C)\,dC.
\]
Thus the Schur-complement part has a spectator-independent domination.

For the actual target, write \(S=(U,V)\), where \(U=S_{\mathrm{top}}\in[-T,T]^p\) and \(V=S_{\mathrm{bot}}\in[-T,T]^{np}\). In the \(j=1\) chart,
\[
D=\|U+xV\|^2+\|CV\|^2.
\]
Use the measure-preserving shear \(W=U+xV\). Since \(|x_i|\le1\), the sheared \(W\)-domain is contained in \([ -rT,rT]^p\). Therefore
\[
\int_R\int_S D^{-c'}\,dS\,dR
\le
2^{2n}
\int_{C\in[-2,2]^{n^2}}
\int_{V\in[-T,T]^{np}}
\int_{W\in[-rT,rT]^p}
(\|W\|^2+\|CV\|^2)^{-c'}\,dW\,dV\,dC.
\]
Here \(2^{2n}\) is exactly the spectator-box volume.

**Q3: PROVEN.**  
The argument preserves the additive threshold. The \(p/2\) contribution enters through the integrated Morse variables \(W\). We are not applying the corank-\((r-1)\) estimate pointwise in \(C\); we apply the free-box joint integral in \((W,V,C)\):
\[
\|W\|^2+\|CV\|^2.
\]
By the stated IH, this is finite for
\[
c'<p/2+\lambda_{r-1,p}.
\]
If one froze \(W=0\), the estimate would indeed undershoot to the core threshold. That is not the argument used here.

**Q4: PROVEN for \(j=1\); NEEDS-CARE for \(j\ge2\).**  
For \(j=1\), the loci \(\det C=0\) and \(C=0\) are already inside the free \(C\)-box handled by IH. They may make the fixed-\(C\) inner \(S\)-integral infinite for some \(c'\ge p/2\), especially at \(C=0\), but those are measure-zero \(C\)-loci. The joint \((C,S)\)-integral is the relevant object and is finite below the IH threshold.

For \(j\ge2\), the same \(M_{22}\mapsto\mathrm{Sc}\) translation has Jacobian \(1\) at fixed \(M_{11},M_{12},M_{21}\). The argument remains sound if the chart gives uniform bounds on \(M_{11}^{-1}\), so that \(M_{21}M_{11}^{-1}M_{12}\) lies in a fixed box and the top shear has uniformly bounded Jacobian/domain enlargement. Without such bounds, constants can blow up.

**Q5: VERDICT.**  
O2 is sound for the \(j=1\) chart. There is no concentration obstruction: the \(M_{22}\to\mathrm{Sc}\) map is a volume-preserving translation, and its image is contained in a fixed spectator-independent box. The clean domination is the displayed bound above by the free corank-\((r-1)\) joint core over \(C\in[-2,2]^{(r-1)^2}\), multiplied by the spectator volume. The right viewpoint for finiteness is upper domination of the pushforward measure, or equivalently fixing spectators, translating \(M_{22}\) to \(C\), and then applying the joint IH. A lower-density framing \(dR\ge\rho\,dC\) is not needed for this finiteness step.