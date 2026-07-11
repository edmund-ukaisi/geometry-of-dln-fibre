The supplied reduced-chain oracle is insufficient to certify either anchor. It gives the vanishing order of \(R\) relative to the reduced Jacobian, but not those of \(H_1,H_2\). Those missing orders decide the mixed \(u,v\)-reduced rays.

## 1. The two integrations

Put \(d=ab\). Exactly,
\[
I_u=\int_0^1u^{d-1}(R^2+u^2H^2)^{-c'}\,du
 =R^{d-2c'}H^{-d}
 \int_0^{H/R}x^{d-1}(1+x^2)^{-c'}\,dx .
\]

Hence
\[
I_u\asymp
\begin{cases}
R^{-2c'},&H\le R,\\
R^{d-2c'}H^{-d},&R\le H,\ c'>d/2,\\
H^{-d}\bigl(1+\log(H/R)\bigr),&R\le H,\ c'=d/2,\\
H^{-2c'},&R\le H,\ c'<d/2.
\end{cases}
\]

Thus the prompt’s general expression
\[
R^{2ab-2c'}H^{-2ab}
\]
has doubled exponents. The correct expression is
\[
R^{ab-2c'}H^{-ab}.
\]
For \(a=b=2\), this is indeed \(R^{4-2c'}H^{-4}\).

For the \(v\)-integral, writing \(A=H_1\), \(B=H_2\),
\[
\begin{aligned}
I_v
&=\int_0^1(A^2+v^2B^2)^{-2}\,dv\\
&=A^{-3}B^{-1}
 \left[
 \frac12\arctan(B/A)
 +\frac{AB}{2(A^2+B^2)}
 \right].
\end{aligned}
\]
Therefore
\[
I_v\asymp
\begin{cases}
A^{-4},&B\le A,\\
A^{-3}B^{-1},&A\le B,
\end{cases}
\qquad
I_v\asymp A^{-3}(A+B)^{-1}.
\]

So \(H_1^{-3}H_2^{-1}\) is comparable only on \(H_1\lesssim H_2\). Globally it is merely an overestimate and becomes useless when \(H_2=0\), although the original integral then equals \(H_1^{-4}\).

Moreover, on the region \(R\le H(v)\), the \(v\)-domain itself depends on \(v\). Removing that indicator gives an upper bound, not an asymptotic equivalence.

## 2. Exact combined-ray formula

On a reduced normal-crossings chart, let a reduced ray \(\eta\) have
\[
r=\nu_\eta(R),\qquad
p=\nu_\eta(H_1),\qquad
q=\nu_\eta(H_2),
\]
and let
\[
K=\ord_\eta(\Jac_{\rm red})+1.
\]

For a primitive combined ray
\[
w=(x,y;\eta),
\]
where \(x=\nu_w(u)\), \(y=\nu_w(v)\), the three generator orders are
\[
r,\qquad x+p,\qquad x+y+q.
\]
Consequently
\[
\boxed{\ord_w(f)=2\min(r,x+p,x+y+q)}
\]
and, for \(d=ab\),
\[
\boxed{\ord_w(\Jac)+1=dx+y+K}.
\]
Thus
\[
\boxed{\lambda(w)=
\frac{dx+y+K}
 {2\min(r,x+p,x+y+q)}}.
\]

The universally determined rays are:

| ray | \(\ord f\) | \(\ord\Jac\) | ratio |
|---|---:|---:|---:|
| \(u\)-ray \((1,0;0)\) | \(0\) | \(d-1\) | \(+\infty\) |
| \(v\)-ray \((0,1;0)\) | \(0\) | \(0\) | \(+\infty\) |
| pure reduced \((0,0;\eta)\) | \(2\min(r,p,q)\) | \(K-1\) | \(\frac K{2\min(r,p,q)}\) |
| mixed \((x,y;\eta)\) | \(2\min(r,x+p,x+y+q)\) | \(dx+y+K-1\) | formula above |

The actual primitive mixed rays are the vertices of
\[
\min\{dx+y+Kt:
rt\ge1,\ x+pt\ge1,\ x+y+qt\ge1,\ x,y,t\ge0\},
\]
after clearing denominators. They cannot be enumerated until \((r,p,q,K)\) are supplied.

The plain reduced oracle gives only
\[
K\ge C_{\rm red}\,r,
\]
with equality on some critical reduced ray. It says nothing about \(p,q\).

## 3. Anchor (A): \((3,3,3,4)\)

Here \(d=4\), \(C_{\rm red}=3\), and the target is
\[
\frac{d+C_{\rm red}}2=\frac72.
\]

Let \(\eta\) be a critical reduced ray, so \(K=3r\). If \(p>0\), define
\[
x=(r-p)_+,\qquad
y=(r-q-x)_+.
\]
Then all three generator orders are at least \(r\), with minimum \(r\), while
\[
4x+y<4r.
\]
Hence
\[
\lambda(x,y;\eta)
=\frac{4x+y+3r}{2r}<\frac72.
\]
This is an explicit offending ray if the actual critical reduced divisor has \(\nu_\eta(H_1)>0\).

Conversely, if \(p=0\) on every relevant reduced ray, then
\[
m:=\min(r,x,x+y+q)\le r,\quad m\le x,
\]
so
\[
4x+y+K\ge4m+3m=7m.
\]
Every combined ray then has ratio at least \(7/2\).

Two oracle-compatible models demonstrate the underdetermination:

| model | minimizing ray | \(\ord f\) | \(\ord\Jac\) | minimum |
|---|---|---:|---:|---:|
| \(R=z,\ H_1=H_2=1,\ d\mu=|z|^2dz\) | \((u,z)=(1,1)\) | \(2\) | \(6\) | \(7/2\) |
| \(R=H_1=H_2=z,\ d\mu=|z|^2dz\) | pure \(z\)-ray | \(2\) | \(2\) | \(3/2\) |

Both have plain reduced RLCT \(3/2\).

Verdict for (A): **not certified**. No actual offending ray can be asserted without \(p,q\), but an offending ray is fully compatible with the stated oracle.

## 4. Anchor (B): \((4,4,4,4)\)

### Cut \(t=2\)

Here \(d=4\), \(C_{\rm red}=7\), target \(11/2\). On a critical reduced ray \(K=7r\), the same construction gives
\[
p>0
\quad\Longrightarrow\quad
\lambda(x,y;\eta)
=\frac{4x+y+7r}{2r}<\frac{11}{2}.
\]

Oracle-compatible extremes are:

| model | minimizing ray | \(\ord f\) | \(\ord\Jac\) | minimum |
|---|---|---:|---:|---:|
| \(H_1,H_2\) units | \((1,0,1)\) | \(2\) | \(10\) | \(11/2\) |
| \(R=H_1=H_2=z\) | pure reduced ray | \(2\) | \(6\) | \(7/2\) |

The divisor \(v=0\) alone has \(\ord f=0\). It becomes relevant only through mixed rays with \(y>0\). The assertion that this mixed locus is exactly the \(t=3\) branch does not provide its Jacobian and vanishing orders.

### Cut \(t=3\)

For the \(1\times1\) peel, write
\[
f=R^2+u^2H^2.
\]
Here \(d=1\), \(C_{\rm red}=10\), and
\[
\ord_w(f)=2\min(r,x+p),\qquad
\ord_w(\Jac)+1=x+K.
\]

On a critical ray \(K=10r\), if \(p>0\), take \(x=(r-p)_+\). Then
\[
\lambda=\frac{x+10r}{2r}<\frac{11}{2}.
\]

Again:

| model | minimizing ray | \(\ord f\) | \(\ord\Jac\) | minimum |
|---|---|---:|---:|---:|
| \(H\) unit | \((u,z)=(1,1)\) | \(2\) | \(10\) | \(11/2\) |
| \(R=H=z\) | pure \(z\)-ray | \(2\) | \(9\) | \(5\) |

Verdict for (B): **not certified**, including the \(v=0\) overlap. The two scalar reduced RLCTs do not determine the transition valuations between the \(t=2\) and \(t=3\) charts.

## 5. The decorated residual integral

For the stated residual
\[
R^{4-2c'}H_1^{-3}H_2^{-1}\,d\mu_{\rm red},
\]
a reduced ray \(\eta\) is integrable precisely when
\[
K+(4-2c')r-3p-q>0.
\]

Thus finiteness for every \(c'<L\) requires, at \(r>0\),

- anchor (A), \(L=7/2\):
  \[
  K-3r-3p-q\ge0;
  \]

- anchor (B), \(t=2\), \(L=11/2\):
  \[
  K-7r-3p-q\ge0.
  \]

On a critical reduced divisor these reduce to
\[
3p+q=0,
\]
so the stated decorated majorant requires both \(H_1\) and \(H_2\) to be units there.

For the correct \(v\)-integrated factor
\[
H_1^{-3}(H_1+H_2)^{-1},
\]
replace \(3p+q\) by
\[
3p+\min(p,q).
\]
At a critical ray this requires only \(p=0\). Hence the claimed \(H_1^{-3}H_2^{-1}\) residual can create an artificial divergence when \(H_1\) is a unit but \(H_2\) vanishes.

## Final verdict

Neither anchor is certified from the supplied data. There is no proven genuine finiteness obstruction in the actual DLN model, but neither can one conclude “only a construction/labour gap”: oracle-compatible offending rays exist.

The cheapest decisive check is to compute
\[
(K_\eta,r_\eta,p_\eta,q_\eta)
=
\bigl(\ord_\eta\Jac_{\rm red}+1,\,
\nu_\eta(R),\nu_\eta(H_1),\nu_\eta(H_2)\bigr)
\]
on the critical reduced divisors and their angular refinements. In particular, finding \(p_\eta>0\) on a critical divisor immediately produces the explicit offending ray above; a full no-obstruction certificate requires running the displayed finite Newton linear programs for the complete valuation table.